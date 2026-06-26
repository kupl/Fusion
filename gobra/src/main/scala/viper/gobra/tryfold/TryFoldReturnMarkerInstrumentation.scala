package viper.gobra.tryfold

import viper.gobra.ast.{internal => in}
import viper.gobra.reporting.Source
import viper.gobra.translator.Names

object TryFoldReturnMarkerInstrumentation {

  private[tryfold] final case class ReturnMarker(
                                                   labelName: String,
                                                   methodName: String,
                                                   methodHash: String,
                                                   returnIndex: Int,
                                                   line: Option[Int],
                                                   column: Option[Int],
                                                 )

  private[tryfold] final case class InstrumentationResult(
                                                            program: in.Program,
                                                            markers: Vector[ReturnMarker],
                                                          )

  private[tryfold] final case class ParsedReturnMarker(
                                                         methodHash: String,
                                                         returnIndex: Int,
                                                         line: Int,
                                                         column: Int,
                                                         labelName: String,
                                                       )

  private val ReturnMarkerRegex = "^tryfold_ret_m([0-9a-fA-F]+)_i([0-9]+)_l([0-9]+)_c([0-9]+)$".r

  def instrumentProgram(program: in.Program): InstrumentationResult = {
    val markerBuffer = Vector.newBuilder[ReturnMarker]

    val newMembers = program.members.map {
      case method: in.Method =>
        method.body match {
          case Some(body) =>
            val (updatedBody, methodMarkers) = instrumentMethodBody(method, body)
            markerBuffer ++= methodMarkers
            method.copy(body = Some(updatedBody))(method.info)
          case None =>
            method
        }
      case function: in.Function =>
        function.body match {
          case Some(body) =>
            val (updatedBody, functionMarkers) = instrumentFunctionBody(function, body)
            markerBuffer ++= functionMarkers
            function.copy(body = Some(updatedBody))(function.info)
          case None =>
            function
        }
      case member => member
    }

    InstrumentationResult(
      program = program.copy(members = newMembers)(program.info),
      markers = markerBuffer.result(),
    )
  }

  def parseMarker(labelName: String): Option[ParsedReturnMarker] =
    labelName match {
      case ReturnMarkerRegex(methodHash, idx, line, col) =>
        Some(
          ParsedReturnMarker(
            methodHash = methodHash,
            returnIndex = toIntOrZero(idx),
            line = toIntOrZero(line),
            column = toIntOrZero(col),
            labelName = labelName,
          )
        )
      case _ =>
        None
    }

  private def instrumentMethodBody(method: in.Method, body: in.MethodBody): (in.MethodBody, Vector[ReturnMarker]) = {
    val methodHash = Names.hash(method.name.uniqueName)
    val methodName = method.name.uniqueName
    val methodInstrumenter = new MethodInstrumenter(methodName = methodName, methodHash = methodHash)
    val rewrittenStmt = methodInstrumenter.rewriteSingle(body.seqn)
    val rewrittenSeqn = rewrittenStmt match {
      case seqn: in.MethodBodySeqn => seqn
      case other => in.MethodBodySeqn(Vector(other))(other.info)
    }
    (
      body.copy(seqn = rewrittenSeqn)(body.info),
      methodInstrumenter.markers,
    )
  }

  private def instrumentFunctionBody(function: in.Function, body: in.MethodBody): (in.MethodBody, Vector[ReturnMarker]) = {
    val functionHash = Names.hash(function.name.name)
    val functionName = function.name.name
    val functionInstrumenter = new MethodInstrumenter(methodName = functionName, methodHash = functionHash)
    val rewrittenStmt = functionInstrumenter.rewriteSingle(body.seqn)
    val rewrittenSeqn = rewrittenStmt match {
      case seqn: in.MethodBodySeqn => seqn
      case other => in.MethodBodySeqn(Vector(other))(other.info)
    }
    (
      body.copy(seqn = rewrittenSeqn)(body.info),
      functionInstrumenter.markers,
    )
  }

  private final class MethodInstrumenter(methodName: String, methodHash: String) {

    private var nextReturnIndex: Int = 0
    private val markerBuffer = Vector.newBuilder[ReturnMarker]

    def markers: Vector[ReturnMarker] = markerBuffer.result()

    def rewriteSingle(stmt: in.Stmt): in.Stmt = {
      val expanded = rewrite(stmt)
      val withImplicitReturnMarker = appendImplicitReturnMarker(expanded, stmt.info)
      if (withImplicitReturnMarker.size == 1) withImplicitReturnMarker.head
      else in.Seqn(withImplicitReturnMarker)(stmt.info)
    }

    private def rewrite(stmt: in.Stmt): Vector[in.Stmt] =
      stmt match {
        case ret: in.Return =>
          val marker = freshMarker(ret.info)
          val labelStmt = in.Label(in.LabelProxy(marker.labelName)(ret.info))(ret.info)
          Vector(labelStmt, ret)

        case seqn: in.Seqn =>
          Vector(seqn.copy(stmts = seqn.stmts.flatMap(rewrite))(seqn.info))

        case seqn: in.MethodBodySeqn =>
          Vector(seqn.copy(stmts = seqn.stmts.flatMap(rewrite))(seqn.info))

        case block: in.Block =>
          Vector(block.copy(stmts = block.stmts.flatMap(rewrite))(block.info))

        case ifStmt: in.If =>
          Vector(ifStmt.copy(thn = rewriteSingle(ifStmt.thn), els = rewriteSingle(ifStmt.els))(ifStmt.info))

        case whileStmt: in.While =>
          Vector(whileStmt.copy(body = rewriteSingle(whileStmt.body))(whileStmt.info))

        case matchStmt: in.PatternMatchStmt =>
          val rewrittenCases = matchStmt.cases.map { caseStmt =>
            caseStmt.copy(body = rewriteSingle(caseStmt.body))(caseStmt.info)
          }
          Vector(matchStmt.copy(cases = rewrittenCases)(matchStmt.info))

        case pkg: in.PackageWand =>
          val rewrittenBlock = pkg.block.map(rewriteSingle)
          Vector(pkg.copy(block = rewrittenBlock)(pkg.info))

        case outline: in.Outline =>
          Vector(outline.copy(body = rewriteSingle(outline.body))(outline.info))

        case other =>
          Vector(other)
      }

    private def appendImplicitReturnMarker(stmts: Vector[in.Stmt], fallbackInfo: Source.Parser.Info): Vector[in.Stmt] = {
      val (anchorInfo, syntheticLine) = lastExecutableAnchor(stmts, fallbackInfo)
      val marker = freshMarker(anchorInfo, lineOverride = syntheticLine, columnOverride = Some(1))
      val labelStmt = in.Label(in.LabelProxy(marker.labelName)(anchorInfo))(anchorInfo)
      stmts :+ labelStmt
    }

    private def lastExecutableAnchor(
                                      stmts: Vector[in.Stmt],
                                      fallbackInfo: Source.Parser.Info,
                                    ): (Source.Parser.Info, Option[Int]) = {
      val best = stmts
        .flatMap(collectLineInfos)
        .sortBy { case (line, col, _) => (line, col) }
        .lastOption
      best match {
        case Some((line, _, info)) => info -> Some(line + 1)
        case None =>
          val (lineOpt, _) = infoToLineColumn(fallbackInfo)
          fallbackInfo -> lineOpt.map(_ + 1)
      }
    }

    private def collectLineInfos(stmt: in.Stmt): Vector[(Int, Int, Source.Parser.Info)] = {
      val self = infoToLineColumn(stmt.info) match {
        case (Some(line), Some(col)) => Vector((line, col, stmt.info))
        case (Some(line), None) => Vector((line, 0, stmt.info))
        case _ => Vector.empty
      }
      val children: Vector[in.Stmt] = stmt match {
        case seqn: in.Seqn => seqn.stmts
        case seqn: in.MethodBodySeqn => seqn.stmts
        case block: in.Block => block.stmts
        case ifStmt: in.If => Vector(ifStmt.thn, ifStmt.els)
        case whileStmt: in.While => Vector(whileStmt.body)
        case matchStmt: in.PatternMatchStmt => matchStmt.cases.map(_.body).toVector
        case pkg: in.PackageWand => pkg.block.toVector
        case outline: in.Outline => Vector(outline.body)
        case _ => Vector.empty
      }
      self ++ children.flatMap(collectLineInfos)
    }

    private def freshMarker(
                             info: Source.Parser.Info,
                             lineOverride: Option[Int] = None,
                             columnOverride: Option[Int] = None,
                           ): ReturnMarker = {
      val index = nextReturnIndex
      nextReturnIndex += 1

      val (lineOpt, colOpt) = infoToLineColumn(info)
      val markerLineOpt = lineOverride.orElse(lineOpt)
      val markerColOpt = columnOverride.orElse(colOpt)
      val line = markerLineOpt.getOrElse(0)
      val col = markerColOpt.getOrElse(0)
      val labelName = s"tryfold_ret_m${methodHash}_i${index}_l${line}_c${col}"

      val marker = ReturnMarker(
        labelName = labelName,
        methodName = methodName,
        methodHash = methodHash,
        returnIndex = index,
        line = markerLineOpt,
        column = markerColOpt,
      )
      markerBuffer += marker
      marker
    }
  }

  private def infoToLineColumn(info: Source.Parser.Info): (Option[Int], Option[Int]) =
    info match {
      case Source.Parser.Single(_, origin) =>
        Some(origin.pos.line) -> Some(origin.pos.column)
      case _ =>
        None -> None
    }

  private def toIntOrZero(value: String): Int =
    try {
      value.toInt
    } catch {
      case _: NumberFormatException => 0
    }
}
