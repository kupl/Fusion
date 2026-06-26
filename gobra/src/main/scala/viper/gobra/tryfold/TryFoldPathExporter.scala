package viper.gobra.tryfold

import viper.gobra.backend.BackendVerifier
import viper.gobra.frontend.Config
import viper.gobra.frontend.TryFoldCandidateMode
import viper.gobra.tryfold.TryFoldWorklistEngine.{DeferFoldAnnotation, FoldAnnotation, UnfoldAnnotation}
import viper.silver.ast

import java.nio.charset.StandardCharsets
import java.nio.file.Files

object TryFoldPathExporter {

  private[tryfold] final case class PathExportMetadata(
                                                         taskName: String,
                                                         attempt: Int,
                                                         workItemId: Long,
                                                         workItemDepth: Int,
                                                         firstErrorId: Option[String],
                                                         firstErrorReadableMessage: Option[String],
                                                         firstErrorSourceLocation: Option[String],
                                                       )

  private final case class ResolvedInsertionTarget(
                                                    kind: String,
                                                    targetFile: Option[String],
                                                    insertBeforeLine: Option[Int],
                                                    insertBeforeColumn: Option[Int],
                                                  )

  def maybeExport(
                   config: Config,
                   attempt: Int,
                   workItemId: Long,
                   workItemDepth: Int,
                   failure: BackendVerifier.Failure,
                   candidateMode: TryFoldCandidateMode.Mode,
                   endpoints: Option[TryFoldFailureContextExtractor.FailureEndpoints],
                   graphPaths: Vector[TryFoldPathExplorer.Path],
                   selectedPaths: Vector[TryFoldPathExplorer.Path],
                   dynamicPathDecisions: Vector[TryFoldDynamicAlternativeFilter.PathDecision] = Vector.empty,
                   rawSequences: Vector[TryFoldWorklistEngine.AnnotationSequence],
                   selectedSequences: Vector[TryFoldInsertionPlanner.PlannedAnnotationSequence],
                   materializationDrops: Vector[TryFoldAnnotationCandidateBuilder.MaterializationDrop],
                   materializationStats: TryFoldAnnotationCandidateBuilder.MaterializationStats,
                   planning: TryFoldInsertionPlanner.PlanningResult,
                   gobraRender: Option[TryFoldGobraAnnotationBacktranslator.BatchRenderResult] = None,
                 ): Unit = {
    config.tryFoldPathOut.foreach { outputPath =>
      val firstError = failure.errors.headOption
      val metadata = PathExportMetadata(
        taskName = config.taskName,
        attempt = attempt,
        workItemId = workItemId,
        workItemDepth = workItemDepth,
        firstErrorId = firstError.map(_.fullId),
        firstErrorReadableMessage = firstError.map(_.readableMessage(withId = true, withPosition = true)),
        firstErrorSourceLocation = firstError.flatMap(err => positionToString(err.pos)),
      )
      val json = renderPathReportJson(
        metadata = metadata,
        candidateMode = candidateMode,
        endpoints = endpoints,
        graphPaths = graphPaths,
        selectedPaths = selectedPaths,
        dynamicPathDecisions = dynamicPathDecisions,
        rawSequences = rawSequences,
        selectedSequences = selectedSequences,
        materializationDrops = materializationDrops,
        materializationStats = materializationStats,
        planning = planning,
        gobraRender = gobraRender,
      )
      val parent = outputPath.getParent
      if (parent != null) {
        Files.createDirectories(parent)
      }
      Files.write(outputPath, json.getBytes(StandardCharsets.UTF_8))
    }
  }

  private[tryfold] def renderPathReportJson(
                                              metadata: PathExportMetadata,
                                              candidateMode: TryFoldCandidateMode.Mode,
                                              endpoints: Option[TryFoldFailureContextExtractor.FailureEndpoints],
                                              graphPaths: Vector[TryFoldPathExplorer.Path],
                                              selectedPaths: Vector[TryFoldPathExplorer.Path],
                                              dynamicPathDecisions: Vector[TryFoldDynamicAlternativeFilter.PathDecision] = Vector.empty,
                                              rawSequences: Vector[TryFoldWorklistEngine.AnnotationSequence],
                                              selectedSequences: Vector[TryFoldInsertionPlanner.PlannedAnnotationSequence],
                                              materializationDrops: Vector[TryFoldAnnotationCandidateBuilder.MaterializationDrop],
                                              materializationStats: TryFoldAnnotationCandidateBuilder.MaterializationStats,
                                              planning: TryFoldInsertionPlanner.PlanningResult,
                                              gobraRender: Option[TryFoldGobraAnnotationBacktranslator.BatchRenderResult] = None,
                                            ): String = {
    val insertionTarget = resolveInsertionTarget(planning.insertionAnchor)
    val singleStepCandidates = selectedSequences.zipWithIndex.map { case (sequence, idx) =>
      singleStepCandidateToJson(idx, sequence)
    }
    val gobraSucceeded = gobraRender.map(_.succeeded).getOrElse(Vector.empty)
    val gobraFailed = gobraRender.map(_.failed).getOrElse(Vector.empty)
    val (gobraInternalTokenRejected, gobraOtherFailures) = gobraFailed.partition(isInternalTokenFailure)
    val payload = jsonObject(Seq(
      "taskName" -> jsonString(metadata.taskName),
      "candidateMode" -> jsonString(candidateMode.cliValue),
      "graphMode" -> jsonString("ours"),
      "attempt" -> metadata.attempt.toString,
      "workItemId" -> metadata.workItemId.toString,
      "workItemDepth" -> metadata.workItemDepth.toString,
      "firstErrorId" -> jsonOption(metadata.firstErrorId),
      "firstErrorReadableMessage" -> jsonOption(metadata.firstErrorReadableMessage),
      "firstErrorSourceLocation" -> jsonOption(metadata.firstErrorSourceLocation),
      "failureEndpoints" -> endpointsToJson(endpoints),
      "graphPathCount" -> graphPaths.size.toString,
      "selectedPathCount" -> selectedPaths.size.toString,
      "graphPaths" -> jsonArray(graphPaths.map(pathToJson)),
      "selectedPaths" -> jsonArray(selectedPaths.map(pathToJson)),
      "dynamicPathDecisionCount" -> dynamicPathDecisions.size.toString,
      "dynamicPathDecisions" -> jsonArray(dynamicPathDecisions.map(dynamicPathDecisionToJson)),
      "isPostconditionFailure" -> planning.isPostconditionFailure.toString,
      "insertionAnchor" -> insertionAnchorToJson(planning.insertionAnchor),
      "insertionTarget" -> insertionTargetToJson(insertionTarget),
      "rawConcreteCandidateCount" -> rawSequences.size.toString,
      "rawConcreteCandidates" -> jsonArray(rawSequences.map(rawSequenceToJson)),
      "selectedConcreteCandidateCount" -> selectedSequences.size.toString,
      "selectedConcreteCandidates" -> jsonArray(selectedSequences.map(plannedSequenceToJson)),
      "materializationStats" -> materializationStatsToJson(materializationStats),
      "materializationDropCount" -> materializationDrops.size.toString,
      "materializationDrops" -> jsonArray(materializationDrops.map(materializationDropToJson)),
      "singleStepCandidateCount" -> singleStepCandidates.size.toString,
      "singleStepCandidates" -> jsonArray(singleStepCandidates),
      "gobraCandidateSuccessCount" -> gobraSucceeded.size.toString,
      "gobraCandidateFailureCount" -> gobraFailed.size.toString,
      "gobraCandidatesSucceeded" -> jsonArray(gobraSucceeded.map(gobraSuccessToJson)),
      "gobraCandidatesFailed" -> jsonArray(gobraFailed.map(gobraFailureToJson)),
      "gobraInternalTokenRejectedCount" -> gobraInternalTokenRejected.size.toString,
      "gobraInternalTokenRejected" -> jsonArray(gobraInternalTokenRejected.map(gobraFailureToJson)),
      "gobraOtherFailureCount" -> gobraOtherFailures.size.toString,
      "gobraOtherFailures" -> jsonArray(gobraOtherFailures.map(gobraFailureToJson)),
    ))
    prettyJson(payload)
  }

  private def endpointsToJson(endpoints: Option[TryFoldFailureContextExtractor.FailureEndpoints]): String =
    endpoints match {
      case Some(value) =>
        val sortedSources = value.sources.toVector.sortBy(_.id)
        jsonObject(Seq(
          "sourceCount" -> sortedSources.size.toString,
          "sources" -> jsonArray(sortedSources.map(nodeToJson)),
          "target" -> nodeToJson(value.target),
          "sourcePermissions" -> jsonArray(value.sourcePermissions.map(sourcePermissionToJson)),
          "targetPermissionCount" -> value.targetPermissions.size.toString,
          "targetPermissions" -> jsonArray(value.targetPermissions.map(targetPermissionToJson)),
        ))
      case None =>
        "null"
    }

  private def pathToJson(path: TryFoldPathExplorer.Path): String = {
    val annotationSequence = path.steps.map(step => annotationDirectiveToJson(step.directive))
    val steps = path.steps.map(pathStepToJson)
    jsonObject(Seq(
      "source" -> nodeToJson(path.source),
      "target" -> nodeToJson(path.target),
      "stepCount" -> path.steps.size.toString,
      "annotationSequence" -> jsonArray(annotationSequence),
      "steps" -> jsonArray(steps),
    ))
  }

  private def rawSequenceToJson(sequence: TryFoldWorklistEngine.AnnotationSequence): String =
    jsonObject(Seq(
      "stepCount" -> sequence.steps.size.toString,
      "steps" -> jsonArray(sequence.steps.map(annotationDirectiveToJson)),
    ))

  private def plannedSequenceToJson(sequence: TryFoldInsertionPlanner.PlannedAnnotationSequence): String =
    {
      val resolvedTarget = resolveInsertionTarget(sequence.insertionAnchor)
      val lines = annotationLines(sequence.plannedSequence)
      jsonObject(Seq(
        "isPostconditionFailure" -> sequence.isPostconditionFailure.toString,
        "foldToDeferRewriteApplied" -> sequence.foldToDeferRewriteApplied.toString,
        "insertionAnchor" -> insertionAnchorToJson(sequence.insertionAnchor),
        "insertionTarget" -> insertionTargetToJson(resolvedTarget),
        "annotationLines" -> jsonArray(lines.map(jsonString)),
        "annotationLinesWithPrefix" -> jsonArray(lines.map(line => jsonString(s"//@ $line"))),
        "original" -> rawSequenceToJson(sequence.originalSequence),
        "planned" -> rawSequenceToJson(sequence.plannedSequence),
      ))
    }

  private def singleStepCandidateToJson(
                                         candidateId: Int,
                                         sequence: TryFoldInsertionPlanner.PlannedAnnotationSequence,
                                       ): String = {
    val resolvedTarget = resolveInsertionTarget(sequence.insertionAnchor)
    val lines = annotationLines(sequence.plannedSequence)
    jsonObject(Seq(
      "candidateId" -> candidateId.toString,
      "isPostconditionFailure" -> sequence.isPostconditionFailure.toString,
      "foldToDeferRewriteApplied" -> sequence.foldToDeferRewriteApplied.toString,
      "insertionTarget" -> insertionTargetToJson(resolvedTarget),
      "annotationLines" -> jsonArray(lines.map(jsonString)),
      "annotationLinesWithPrefix" -> jsonArray(lines.map(line => jsonString(s"//@ $line"))),
      "renderStatus" -> jsonString("bestEffort"),
    ))
  }

  private def insertionTargetToJson(target: ResolvedInsertionTarget): String =
    jsonObject(Seq(
      "kind" -> jsonString(target.kind),
      "targetFile" -> jsonOption(target.targetFile),
      "insertBeforeLine" -> jsonIntOption(target.insertBeforeLine),
      "insertBeforeColumn" -> jsonIntOption(target.insertBeforeColumn),
    ))

  private def insertionAnchorToJson(anchor: TryFoldInsertionPlanner.InsertionAnchor): String =
    jsonObject(Seq(
      "kind" -> jsonString(anchor.kind.asString),
      "sourceFile" -> jsonOption(anchor.sourceFile),
      "sourceLine" -> jsonIntOption(anchor.sourceLine),
      "sourceColumn" -> jsonIntOption(anchor.sourceColumn),
      "sourceLocation" -> jsonOption(anchor.sourceLocation),
      "returnMarkerLabel" -> jsonOption(anchor.returnMarkerLabel),
      "returnLine" -> jsonIntOption(anchor.returnLine),
      "returnColumn" -> jsonIntOption(anchor.returnColumn),
    ))

  private def resolveInsertionTarget(anchor: TryFoldInsertionPlanner.InsertionAnchor): ResolvedInsertionTarget = {
    val (line, col) =
      if (anchor.kind == TryFoldInsertionPlanner.ReturnMarkerAnchor) {
        anchor.returnLine -> anchor.returnColumn
      } else {
        anchor.sourceLine -> anchor.sourceColumn
      }
    ResolvedInsertionTarget(
      kind = anchor.kind.asString,
      targetFile = anchor.sourceFile,
      insertBeforeLine = line,
      insertBeforeColumn = col,
    )
  }

  private def pathStepToJson(step: TryFoldPathExplorer.PathStep): String = {
    val labels = step.edge.labels.toVector.sortBy(labelSortKey)
    val templates = step.edge.templates.toVector.sortBy(templateSortKey)
    jsonObject(Seq(
      "from" -> nodeToJson(step.from),
      "to" -> nodeToJson(step.to),
      "directive" -> annotationDirectiveToJson(step.directive),
      "edgeKind" -> jsonString(step.edge.kind.asString),
      "edgeLabels" -> jsonArray(labels.map(labelToJson)),
      "edgeTemplates" -> jsonArray(templates.map(templateToJson)),
    ))
  }

  private def dynamicPathDecisionToJson(decision: TryFoldDynamicAlternativeFilter.PathDecision): String = {
    val mismatchJson = decision.mismatch match {
      case Some(mismatch) =>
        jsonObject(Seq(
          "stepIndex" -> mismatch.stepIndex.toString,
          "nodeId" -> jsonString(mismatch.nodeId),
          "nodeName" -> jsonString(mismatch.nodeName),
          "requiredTypeKeys" -> jsonArray(mismatch.requiredTypeKeys.map(jsonString)),
          "resolvedTypeKeys" -> jsonArray(mismatch.resolvedTypeKeys.map(jsonString)),
        ))
      case None =>
        "null"
    }
    jsonObject(Seq(
      "pathIndex" -> decision.pathIndex.toString,
      "kept" -> decision.keep.toString,
      "requiredAlternatives" -> jsonArray(decision.requiredAlternatives.map { required =>
        jsonObject(Seq(
          "stepIndex" -> required.stepIndex.toString,
          "nodeId" -> jsonString(required.nodeId),
          "nodeName" -> jsonString(required.nodeName),
          "typeKey" -> jsonString(required.typeKey),
        ))
      }),
      "resolvedTypeFacts" -> jsonArray(decision.resolvedTypeFacts.map { fact =>
        jsonObject(Seq(
          "nodeId" -> jsonString(fact.nodeId),
          "nodeName" -> jsonString(fact.nodeName),
          "typeKeys" -> jsonArray(fact.typeKeys.map(jsonString)),
          "evidenceSources" -> jsonArray(fact.evidenceSources.map(jsonString)),
        ))
      }),
      "mismatch" -> mismatchJson,
    ))
  }

  private def annotationDirectiveToJson(directive: TryFoldWorklistEngine.AnnotationDirective): String =
    jsonObject(Seq(
      "action" -> jsonString(annotationActionAsString(directive.action)),
      "predicateName" -> jsonString(directive.predicateName),
      "arguments" -> jsonArray(directive.args.map(jsonString)),
      "argumentsExp" -> jsonArray(directive.argsExp.getOrElse(Vector.empty).map(v => jsonString(safeRender(v)))),
      "permission" -> jsonPermissionAmountOption(directive.permission),
      "permissionIsWildcard" -> directive.permissionIsWildcard.toString,
      "permissionSymbolicTerm" -> jsonOption(directive.permissionSymbolicTerm),
      "permissionOrigin" -> jsonOption(directive.permissionOrigin),
    ))

  private def annotationLines(sequence: TryFoldWorklistEngine.AnnotationSequence): Vector[String] =
    sequence.steps.map(renderSilverAnnotationLine)

  private[tryfold] def renderSilverAnnotationLine(directive: TryFoldWorklistEngine.AnnotationDirective): String = {
    val action = annotationActionAsString(directive.action) match {
      case "deferFold" => "defer fold"
      case other => other
    }
    val predicateCall =
      if (directive.args.nonEmpty) s"${directive.predicateName}(${directive.args.mkString(", ")})"
      else s"${directive.predicateName}()"
    val permissionArg =
      if (directive.permissionIsWildcard) ", _"
      else directive.permission.map(perm => s", ${perm.rational}").getOrElse("")
    s"$action acc($predicateCall$permissionArg)"
  }

  private def sourcePermissionToJson(entry: viper.gobra.backend.TryFoldSourcePermissionExtractor.SourcePermissionEntry): String =
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

  private def gobraSuccessToJson(entry: TryFoldGobraAnnotationBacktranslator.CandidateSuccess): String =
    jsonObject(Seq(
      "candidateId" -> entry.candidateId.toString,
      "directiveCount" -> entry.directives.size.toString,
      "annotationLines" -> jsonArray(entry.annotationLines.map(jsonString)),
      "annotationLinesWithPrefix" -> jsonArray(entry.annotationLinesWithPrefix.map(jsonString)),
      "warnings" -> jsonArray(entry.warnings.map(jsonString)),
      "directives" -> jsonArray(entry.directives.map(gobraDirectiveToJson)),
      "backtranslationTrace" -> jsonArray(entry.backtranslationTrace.map(directiveBacktranslationTraceToJson)),
    ))

  private def materializationStatsToJson(stats: TryFoldAnnotationCandidateBuilder.MaterializationStats): String =
    jsonObject(Seq(
      "pathCount" -> stats.pathCount.toString,
      "pathsWithConcreteCandidates" -> stats.pathsWithConcreteCandidates.toString,
      "droppedPathCount" -> stats.droppedPathCount.toString,
      "totalRawConcreteCandidates" -> stats.totalRawConcreteCandidates.toString,
      "totalDrops" -> stats.totalDrops.toString,
      "dropReasonCounts" -> jsonObject(
        stats.dropReasonCounts.toVector.sortBy(_._1).map { case (reason, count) =>
          reason -> count.toString
        }
      ),
    ))

  private def materializationDropToJson(drop: TryFoldAnnotationCandidateBuilder.MaterializationDrop): String =
    jsonObject(Seq(
      "pathIndex" -> drop.pathIndex.toString,
      "reason" -> jsonString(drop.reason),
      "stepIndex" -> jsonIntOption(drop.stepIndex),
      "fromNodeId" -> jsonOption(drop.fromNodeId),
      "fromNodeName" -> jsonOption(drop.fromNodeName),
      "details" -> jsonOption(drop.details),
    ))

  private def gobraDirectiveToJson(entry: TryFoldGobraAnnotationBacktranslator.DirectiveRender): String =
    jsonObject(Seq(
      "action" -> jsonString(annotationActionAsString(entry.action)),
      "gobraPredicateCall" -> jsonString(entry.gobraPredicateCall),
      "permissionRational" -> jsonOption(entry.permissionRational),
      "permissionIsWildcard" -> entry.permissionIsWildcard.toString,
      "permissionSymbolicTerm" -> jsonOption(entry.permissionSymbolicTerm),
      "annotationLine" -> jsonString(entry.annotationLine),
    ))

  private def gobraFailureToJson(entry: TryFoldGobraAnnotationBacktranslator.CandidateFailure): String =
    jsonObject(Seq(
      "candidateId" -> entry.candidateId.toString,
      "reason" -> jsonString(entry.reason),
      "failureStage" -> jsonString(entry.failureStage),
      "failedDirectiveIndex" -> entry.failedDirectiveIndex.map(_.toString).getOrElse("null"),
      "failedPredicateName" -> jsonOption(entry.failedPredicateName),
      "silverAnnotationLines" -> jsonArray(entry.silverAnnotationLines.map(jsonString)),
      "silverAnnotationLinesWithPrefix" -> jsonArray(entry.silverAnnotationLines.map(line => jsonString(s"//@ $line"))),
      "backtranslationTrace" -> jsonArray(entry.backtranslationTrace.map(directiveBacktranslationTraceToJson)),
    ))

  private def directiveBacktranslationTraceToJson(entry: TryFoldGobraAnnotationBacktranslator.DirectiveBacktranslationTrace): String =
    jsonObject(Seq(
      "directiveIndex" -> entry.directiveIndex.toString,
      "predicateName" -> jsonString(entry.predicateName),
      "rawArgsExp" -> jsonArray(entry.rawArgsExp.map(jsonString)),
      "afterReturnSubstitutionExp" -> jsonArray(entry.afterReturnSubstitutionExp.map(jsonString)),
      "afterNormalizationExp" -> jsonArray(entry.afterNormalizationExp.map(jsonString)),
      "afterAliasResolutionExp" -> jsonArray(entry.afterAliasResolutionExp.map(jsonString)),
      "afterPostAliasReturnSubstitutionExp" -> jsonArray(entry.afterPostAliasReturnSubstitutionExp.map(jsonString)),
      "renderedArgs" -> jsonArray(entry.renderedArgs.map(jsonString)),
      "notes" -> jsonArray(entry.notes.map(jsonString)),
    ))

  private def isInternalTokenFailure(entry: TryFoldGobraAnnotationBacktranslator.CandidateFailure): Boolean = {
    val stage = Option(entry.failureStage).getOrElse("")
    val reason = Option(entry.reason).getOrElse("")
    stage == "internalTokenValidation" || reason.contains("internal encoding token")
  }

  private def targetPermissionToJson(entry: TryFoldTargetPermissionExtractor.TargetPermissionEntry): String =
    jsonObject(Seq(
      "index" -> entry.index.toString,
      "nodeKind" -> jsonString(entry.nodeKind),
      "nodeName" -> jsonString(entry.nodeName),
      "nodeId" -> jsonString(entry.nodeId),
      "arguments" -> jsonArray(entry.arguments.map(jsonString)),
      "argumentsExp" -> jsonArray(entry.argumentsExp.getOrElse(Vector.empty).map(v => jsonString(safeRender(v)))),
      "access" -> jsonString(entry.access),
      "permissionTerm" -> jsonOption(entry.permissionTerm),
      "evaluatedPermission" -> jsonPermissionAmountOption(entry.evaluatedPermission),
      "evaluationKind" -> jsonString(entry.evaluationKind),
      "extractionSource" -> jsonString(entry.extractionSource),
      "matchesReasonLocation" -> entry.matchesReasonLocation.toString,
    ))

  private def jsonPermissionAmountOption(value: Option[viper.gobra.backend.TryFoldSourcePermissionExtractor.PermissionAmount]): String =
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

  private def jsonIntOption(value: Option[Int]): String =
    value.map(_.toString).getOrElse("null")

  private def annotationActionAsString(action: TryFoldWorklistEngine.AnnotationAction): String =
    action match {
      case FoldAnnotation => "fold"
      case UnfoldAnnotation => "unfold"
      case DeferFoldAnnotation => "deferFold"
    }

  private def nodeToJson(node: DependencyNode): String =
    node match {
      case PredicateNode(name) =>
        jsonObject(Seq(
          "id" -> jsonString(node.id),
          "kind" -> jsonString("predicate"),
          "name" -> jsonString(name),
        ))
      case FieldNode(name) =>
        jsonObject(Seq(
          "id" -> jsonString(node.id),
          "kind" -> jsonString("field"),
          "name" -> jsonString(name),
        ))
      case BoolLiteralNode(value) =>
        jsonObject(Seq(
          "id" -> jsonString(node.id),
          "kind" -> jsonString("boolLiteral"),
          "name" -> jsonString(value.toString),
          "value" -> value.toString,
        ))
    }

  private def labelToJson(label: DependencyEdgeLabel): String =
    label match {
      case UnlabeledEdge =>
        jsonObject(Seq("kind" -> jsonString("unlabeled")))
      case DynamicAlternativeLabel(typeKey) =>
        jsonObject(Seq(
          "kind" -> jsonString("dynamicAlternative"),
          "typeKey" -> jsonString(typeKey),
        ))
    }

  private def labelSortKey(label: DependencyEdgeLabel): String =
    label match {
      case UnlabeledEdge => "0:unlabeled"
      case DynamicAlternativeLabel(typeKey) => s"1:$typeKey"
    }

  private def templateToJson(template: EdgeCallsiteTemplate): String =
    jsonObject(Seq(
      "ownerFormalParams" -> jsonArray(template.ownerFormalParams.map(jsonString)),
      "calleeArgTemplates" -> jsonArray(template.calleeArgTemplates.map(jsonString)),
      "ownerFormalParamsExp" -> jsonArray(template.ownerFormalParamsExp.map(v => jsonString(safeRender(v)))),
      "calleeArgTemplatesExp" -> jsonArray(template.calleeArgTemplatesExp.map(v => jsonString(safeRender(v)))),
    ))

  private def templateSortKey(template: EdgeCallsiteTemplate): String =
    s"${template.ownerFormalParams.mkString(",")}=>${template.calleeArgTemplates.mkString(",")}"

  private def positionToString(position: ast.Position): Option[String] =
    if (position == ast.NoPosition) None
    else Some(safeRender(position))

  private def safeRender(value: Any): String =
    try {
      String.valueOf(value)
    } catch {
      case throwable: Throwable => s"<rendering failed: ${throwable.getClass.getSimpleName}>"
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
}
