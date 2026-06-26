// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2020 ETH Zurich.

package viper.gobra.backend

import viper.gobra.backend.ViperBackends.{CarbonBackend => Carbon}
import viper.gobra.frontend.{Config, PackageInfo}
import viper.gobra.reporting.BackTranslator.BackTrackInfo
import viper.gobra.reporting.{BackTranslator, BacktranslatingReporter, ChoppedProgressMessage}
import viper.gobra.tryfold.TryFoldTranslationMetadata
import viper.gobra.util.{ChopperUtil, GobraExecutionContext}
import viper.silicon.interfaces.state.GeneralChunk
import viper.silicon.interfaces.SiliconDebuggingFailureContext
import viper.silicon.resources.PredicateID
import viper.silver
import viper.silver.ast
import viper.silver.verifier.VerificationResult
import viper.silver.{ast => vpr}

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import scala.concurrent.Future

object BackendVerifier {

  case class Task(
                   program: vpr.Program,
                   backtrack: BackTranslator.BackTrackInfo,
                   tryFoldMetadata: Option[TryFoldTranslationMetadata] = None,
                 )

  case class FailureStateStoreEntry(
                                     variable: String,
                                     term: String,
                                     expression: Option[String]
                                   )

  case class FailureStateSnapshot(
                                   errorId: String,
                                   errorReadableMessage: String,
                                   sourceLocation: Option[String],
                                   errorIndex: Int,
                                   contextIndex: Int,
                                   memberName: Option[String],
                                   branchConditions: Vector[String],
                                   failedAssertion: Option[String],
                                   failedAssertionExp: Option[String],
                                   store: Vector[FailureStateStoreEntry],
                                   heapChunks: Vector[String],
                                   predicateOnlyHeapChunks: Vector[String],
                                   oldHeapChunks: Map[String, Vector[String]],
                                   predicateOnlyOldHeapChunks: Map[String, Vector[String]],
                                   sourcePermissions: Vector[TryFoldSourcePermissionExtractor.SourcePermissionEntry],
                                 )

  sealed trait Result
  case object Success extends Result
  case class Failure(
                    errors: Vector[silver.verifier.VerificationError],
                    backtrack: BackTranslator.BackTrackInfo,
                    extractedFailureStates: Vector[FailureStateSnapshot]
                    ) extends Result

  def verify(task: Task, pkgInfo: PackageInfo)(config: Config)(implicit executor: GobraExecutionContext): Future[Result] = {

    var exePaths: Vector[String] = Vector.empty

    config.z3Exe match {
      case Some(z3Exe) =>
        exePaths ++= Vector("--z3Exe", z3Exe)
      case _ =>
    }

    (config.backendOrDefault, config.boogieExe) match {
      case (Carbon, Some(boogieExe)) =>
        exePaths ++= Vector("--boogieExe", boogieExe)
      case _ =>
    }

    val verificationResults: Future[VerificationResult] =  {
      val verifier = config.backendOrDefault.create(exePaths, config)
      val reporter = BacktranslatingReporter(config.reporter, task.backtrack, config)

      if (!config.shouldChop) {
        verifier.verify(config.taskName, reporter, task.program)(executor)
      } else {

        val programs = ChopperUtil.computeChoppedPrograms(task, pkgInfo)(config)
        val num = programs.size
        var counter = 0 // verification progress counter

        // Starts verifying all chopped programs in parallel
        val partialVerificationResults = Future.traverse(programs.zipWithIndex) { case (program, idx) =>
          val programID = s"${config.taskName}_$idx"
          verifier.verify(programID, reporter, program)(executor).andThen { _ =>
            // this block ensures that progress messages are printed in order
            this.synchronized { counter += 1; config.reporter report ChoppedProgressMessage(counter, num, idx) }
          }
        }

        partialVerificationResults map { partialRes =>
          partialRes.foldLeft[VerificationResult](silver.verifier.Success) {
            case (acc, silver.verifier.Success) => acc
            case (silver.verifier.Success, res) => res
            case (silver.verifier.Failure(l), silver.verifier.Failure(r)) => silver.verifier.Failure(l ++ r)
          }
        }
      }
    }

    verificationResults.map(convertVerificationResult(_, task.backtrack, extractFailureStates = config.tryFold))
      .map { result =>
        maybeExportFailureStates(config, result)
        result
      }
  }

  /**
    * Takes a Viper VerificationResult and converts it to a Gobra Result using the provided backtracking information
    */
  def convertVerificationResult(
                                 result: VerificationResult,
                                 backTrackInfo: BackTrackInfo,
                                 extractFailureStates: Boolean = false
                               ): Result =
    result match {
      case silver.verifier.Success => Success
      case failure: silver.verifier.Failure =>
        val (verificationError, otherError) = failure.errors
          .partition(_.isInstanceOf[silver.verifier.VerificationError])
          .asInstanceOf[(Seq[silver.verifier.VerificationError], Seq[silver.verifier.AbstractError])]

        checkAbstractViperErrors(otherError)

        val extractedStates =
          if (extractFailureStates) {
            extractDebuggingFailureStates(verificationError)
          } else {
            Vector.empty
          }

        Failure(verificationError.toVector, backTrackInfo, extractedStates)
    }

  private[backend] def extractDebuggingFailureStates(
                                                      errors: Seq[silver.verifier.VerificationError]
                                                    ): Vector[FailureStateSnapshot] = {
    errors.zipWithIndex.flatMap { case (error, errorIndex) =>
      error.failureContexts.zipWithIndex.collect {
        case (context: SiliconDebuggingFailureContext, contextIndex) if context.state.isDefined =>
          val state = context.state.get
          val storeEntries = state.g.values.toVector
            .sortBy(_._1.name)
            .map { case (variable, (term, expression)) =>
              FailureStateStoreEntry(
                variable = variable.name,
                term = safeRender(term),
                expression = expression.map(safeRender)
              )
            }
          val heapChunks = state.h.values.toVector.map(safeRender)
          val predicateOnlyHeapChunks = state.h.values.toVector.collect {
            case chunk: GeneralChunk if chunk.resourceID == PredicateID => safeRender(chunk)
          }
          val oldHeapChunks = state.oldHeaps.toVector.sortBy(_._1).map {
            case (label, heap) => label -> heap.values.toVector.map(safeRender)
          }.toMap
          val predicateOnlyOldHeapChunks = state.oldHeaps.toVector.sortBy(_._1).map {
            case (label, heap) =>
              label -> heap.values.toVector.collect {
                case chunk: GeneralChunk if chunk.resourceID == PredicateID => safeRender(chunk)
              }
          }.toMap
          val sourcePermissions = TryFoldSourcePermissionExtractor.extractFromState(
            state = state,
            counterexample = context.counterExample,
          )
          FailureStateSnapshot(
            errorId = error.fullId,
            errorReadableMessage = error.readableMessage(withId = true, withPosition = true),
            sourceLocation = positionToString(error.pos),
            errorIndex = errorIndex,
            contextIndex = contextIndex,
            memberName = state.currentMember.map(_.name),
            branchConditions = context.branchConditions.toVector.map(safeRender),
            failedAssertion = Option(context.failedAssertion).map(safeRender),
            failedAssertionExp = Option(context.failedAssertionExp).map(safeRender),
            store = storeEntries,
            heapChunks = heapChunks,
            predicateOnlyHeapChunks = predicateOnlyHeapChunks,
            oldHeapChunks = oldHeapChunks,
            predicateOnlyOldHeapChunks = predicateOnlyOldHeapChunks,
            sourcePermissions = sourcePermissions,
          )
      }
    }.toVector
  }

  private def safeRender(value: Any): String =
    try {
      String.valueOf(value)
    } catch {
      case throwable: Throwable => s"<rendering failed: ${throwable.getClass.getSimpleName}>"
    }

  private def positionToString(position: ast.Position): Option[String] =
    if (position == ast.NoPosition) None
    else Some(safeRender(position))

  private def maybeExportFailureStates(config: Config, result: Result): Unit = {
    if (config.tryFold) {
      config.tryFoldStateOut.foreach { outputPath =>
        val json = renderFailureStateReportJson(config.taskName, result)
        val parent = outputPath.getParent
        if (parent != null) {
          Files.createDirectories(parent)
        }
        Files.write(outputPath, json.getBytes(StandardCharsets.UTF_8))
      }
    }
  }

  private def renderFailureStateReportJson(taskName: String, result: Result): String = {
    val (resultTag, snapshots) = result match {
      case Success => ("success", Vector.empty[FailureStateSnapshot])
      case Failure(_, _, extractedFailureStates) => ("failure", extractedFailureStates)
    }
    val payload = jsonObject(Seq(
      "taskName" -> jsonString(taskName),
      "verificationResult" -> jsonString(resultTag),
      "stateCount" -> snapshots.size.toString,
      "states" -> jsonArray(snapshots.map(snapshotToJson))
    ))
    prettyJson(payload)
  }

  private def snapshotToJson(snapshot: FailureStateSnapshot): String =
    jsonObject(Seq(
      "errorId" -> jsonString(snapshot.errorId),
      "errorReadableMessage" -> jsonString(snapshot.errorReadableMessage),
      "sourceLocation" -> jsonOption(snapshot.sourceLocation),
      "errorIndex" -> snapshot.errorIndex.toString,
      "contextIndex" -> snapshot.contextIndex.toString,
      "memberName" -> jsonOption(snapshot.memberName),
      "branchConditions" -> jsonArray(snapshot.branchConditions.map(jsonString)),
      "failedAssertion" -> jsonOption(snapshot.failedAssertion),
      "failedAssertionExp" -> jsonOption(snapshot.failedAssertionExp),
      "store" -> jsonArray(snapshot.store.map(storeEntryToJson)),
      "heapChunks" -> jsonArray(snapshot.heapChunks.map(jsonString)),
      "predicateOnlyHeapChunks" -> jsonArray(snapshot.predicateOnlyHeapChunks.map(jsonString)),
      "oldHeapChunks" -> jsonObject(snapshot.oldHeapChunks.toVector.sortBy(_._1).map {
        case (label, chunks) => label -> jsonArray(chunks.map(jsonString))
      }),
      "predicateOnlyOldHeapChunks" -> jsonObject(snapshot.predicateOnlyOldHeapChunks.toVector.sortBy(_._1).map {
        case (label, chunks) => label -> jsonArray(chunks.map(jsonString))
      }),
      "sourcePermissions" -> jsonArray(snapshot.sourcePermissions.map(sourcePermissionToJson)),
    ))

  private def storeEntryToJson(entry: FailureStateStoreEntry): String =
    jsonObject(Seq(
      "variable" -> jsonString(entry.variable),
      "term" -> jsonString(entry.term),
      "expression" -> jsonOption(entry.expression)
    ))

  private def sourcePermissionToJson(entry: TryFoldSourcePermissionExtractor.SourcePermissionEntry): String =
    jsonObject(Seq(
      "index" -> entry.index.toString,
      "nodeKind" -> jsonString(entry.nodeKind),
      "nodeName" -> jsonString(entry.nodeName),
      "nodeId" -> jsonString(entry.nodeId),
      "chunkKind" -> jsonString(entry.chunkKind),
      "chunk" -> jsonString(entry.chunk),
      "permissionTerm" -> jsonString(entry.permissionTerm),
      "bodyPermissionTerm" -> jsonOption(entry.bodyPermissionTerm),
      "conditionTerm" -> jsonOption(entry.conditionTerm),
      "conditionEvaluation" -> jsonBooleanOption(entry.conditionEvaluation),
      "evaluatedPermission" -> jsonPermissionAmountOption(entry.evaluatedPermission),
      "evaluatedBodyPermission" -> jsonPermissionAmountOption(entry.evaluatedBodyPermission),
      "evaluationKind" -> jsonString(entry.evaluationKind),
      "arguments" -> jsonArray(entry.arguments.map(jsonString)),
      "argumentsExp" -> jsonArray(entry.argumentsExp.getOrElse(Vector.empty).map(v => jsonString(safeRender(v)))),
      "singletonArguments" -> jsonArray(entry.singletonArguments.map(jsonString)),
      "singletonArgumentsExp" -> jsonArray(entry.singletonArgumentsExp.getOrElse(Vector.empty).map(v => jsonString(safeRender(v)))),
    ))

  private def jsonPermissionAmountOption(value: Option[TryFoldSourcePermissionExtractor.PermissionAmount]): String =
    value match {
      case Some(amount) =>
        jsonObject(Seq(
          "rational" -> jsonString(amount.rational),
          "decimal" -> jsonString(amount.decimal),
        ))
      case None =>
        "null"
    }

  private def jsonBooleanOption(value: Option[Boolean]): String =
    value match {
      case Some(v) => v.toString
      case None => "null"
    }

  private def jsonOption(value: Option[String]): String =
    value match {
      case Some(v) => jsonString(v)
      case None => "null"
    }

  private def jsonArray(values: Seq[String]): String =
    values.mkString("[", ",", "]")

  private def jsonObject(fields: Seq[(String, String)]): String =
    fields.map { case (key, value) => s"${jsonString(key)}:$value" }.mkString("{", ",", "}")

  private def jsonString(value: String): String =
    "\"" + escapeJson(value) + "\""

  private def escapeJson(value: String): String = {
    val out = new StringBuilder(value.length + 8)
    value.foreach {
      case '"' => out.append("\\\"")
      case '\\' => out.append("\\\\")
      case '\b' => out.append("\\b")
      case '\f' => out.append("\\f")
      case '\n' => out.append("\\n")
      case '\r' => out.append("\\r")
      case '\t' => out.append("\\t")
      case c if c < ' ' => out.append(f"\\u${c.toInt}%04x")
      case c => out.append(c)
    }
    out.toString()
  }

  private def prettyJson(minifiedJson: String): String = {
    val out = new StringBuilder(minifiedJson.length + 32)
    var indentation = 0
    var inString = false
    var escaping = false

    def appendIndent(): Unit = {
      var i = 0
      while (i < indentation) {
        out.append("  ")
        i += 1
      }
    }

    minifiedJson.foreach { ch =>
      if (inString) {
        out.append(ch)
        if (escaping) {
          escaping = false
        } else if (ch == '\\') {
          escaping = true
        } else if (ch == '"') {
          inString = false
        }
      } else {
        ch match {
          case '{' | '[' =>
            out.append(ch).append('\n')
            indentation += 1
            appendIndent()
          case '}' | ']' =>
            out.append('\n')
            indentation -= 1
            appendIndent()
            out.append(ch)
          case ',' =>
            out.append(ch).append('\n')
            appendIndent()
          case ':' =>
            out.append(": ")
          case '"' =>
            inString = true
            out.append(ch)
          case _ =>
            out.append(ch)
        }
      }
    }
    out.append('\n')
    out.toString()
  }

  @scala.annotation.elidable(scala.annotation.elidable.ASSERTION)
  private def checkAbstractViperErrors(errors: Seq[silver.verifier.AbstractError]): Unit = {
    if (errors.nonEmpty) {
      var messages: Vector[String] = Vector.empty
      messages ++= Vector("Found non-verification-failures")
      messages ++= errors map (_.readableMessage)

      val completeMessage = messages.mkString("\n")
      throw new java.lang.IllegalStateException(completeMessage)
    }
  }

}
