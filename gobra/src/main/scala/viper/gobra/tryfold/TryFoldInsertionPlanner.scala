package viper.gobra.tryfold

import viper.gobra.backend.BackendVerifier
import viper.gobra.tryfold.TryFoldWorklistEngine.{AnnotationSequence, DeferFoldAnnotation, FoldAnnotation, UnfoldAnnotation}
import viper.silicon.interfaces.SiliconDebuggingFailureContext
import viper.silver.ast
import viper.silver.verifier.VerificationError
import viper.silver.verifier.errors.PostconditionViolated

object TryFoldInsertionPlanner {

  private[tryfold] sealed trait InsertionAnchorKind {
    def asString: String
  }

  private[tryfold] case object ErrorLocationAnchor extends InsertionAnchorKind {
    override val asString: String = "errorLocation"
  }

  private[tryfold] case object ReturnMarkerAnchor extends InsertionAnchorKind {
    override val asString: String = "returnMarker"
  }

  private[tryfold] final case class InsertionAnchor(
                                                      kind: InsertionAnchorKind,
                                                      sourceFile: Option[String],
                                                      sourceLine: Option[Int],
                                                      sourceColumn: Option[Int],
                                                      sourceLocation: Option[String],
                                                      returnMarkerLabel: Option[String],
                                                      returnLine: Option[Int],
                                                      returnColumn: Option[Int],
                                                    )

  private[tryfold] final case class PlannedAnnotationSequence(
                                                                originalSequence: AnnotationSequence,
                                                                plannedSequence: AnnotationSequence,
                                                                insertionAnchor: InsertionAnchor,
                                                                isPostconditionFailure: Boolean,
                                                                foldToDeferRewriteApplied: Boolean,
                                                              )

  private[tryfold] final case class PlanningResult(
                                                     firstErrorId: Option[String],
                                                     firstErrorReadableMessage: Option[String],
                                                     isPostconditionFailure: Boolean,
                                                     insertionAnchor: InsertionAnchor,
                                                     plannedSequences: Vector[PlannedAnnotationSequence],
                                                   )

  def plan(
            failure: BackendVerifier.Failure,
            sequences: Vector[AnnotationSequence],
          ): PlanningResult = {
    val firstError = failure.errors.headOption
    val firstContext = TryFoldFailureContextExtractor.extractFirstDebuggingContext(failure)

    val isPost = firstError.exists(isPostconditionFailure)
    val anchor = chooseInsertionAnchor(firstError, firstContext, isPost)

    val plannedSequences = sequences.map { sequence =>
      val rewritten =
        if (isPost) rewriteForPostcondition(sequence)
        else sequence
      PlannedAnnotationSequence(
        originalSequence = sequence,
        plannedSequence = rewritten,
        insertionAnchor = anchor,
        isPostconditionFailure = isPost,
        foldToDeferRewriteApplied = rewritten != sequence,
      )
    }

    PlanningResult(
      firstErrorId = firstError.map(_.fullId),
      firstErrorReadableMessage = firstError.map(_.readableMessage(withId = true, withPosition = true)),
      isPostconditionFailure = isPost,
      insertionAnchor = anchor,
      plannedSequences = plannedSequences,
    )
  }

  private def isPostconditionFailure(error: VerificationError): Boolean =
    error match {
      case _: PostconditionViolated => true
      case _ =>
        val id = Option(error.id).getOrElse("")
        id == "postcondition.violated"
    }

  private def chooseInsertionAnchor(
                                      firstError: Option[VerificationError],
                                      firstContext: Option[SiliconDebuggingFailureContext],
                                      isPostcondition: Boolean,
                                    ): InsertionAnchor = {
    val firstPositionParts = firstError.flatMap(error => positionParts(error.pos))
    if (isPostcondition) {
      val returnMarker = firstContext.flatMap(pickLastReturnMarker)
      returnMarker match {
        case Some(marker) =>
          InsertionAnchor(
            kind = ReturnMarkerAnchor,
            sourceFile = firstPositionParts.flatMap(_.file),
            sourceLine = firstPositionParts.flatMap(_.line),
            sourceColumn = firstPositionParts.flatMap(_.column),
            sourceLocation = firstError.flatMap(errorLocationString),
            returnMarkerLabel = Some(marker.labelName),
            returnLine = Some(marker.line),
            returnColumn = Some(marker.column),
          )
        case None =>
          InsertionAnchor(
            kind = ErrorLocationAnchor,
            sourceFile = firstPositionParts.flatMap(_.file),
            sourceLine = firstPositionParts.flatMap(_.line),
            sourceColumn = firstPositionParts.flatMap(_.column),
            sourceLocation = firstError.flatMap(errorLocationString),
            returnMarkerLabel = None,
            returnLine = None,
            returnColumn = None,
          )
      }
    } else {
      InsertionAnchor(
        kind = ErrorLocationAnchor,
        sourceFile = firstPositionParts.flatMap(_.file),
        sourceLine = firstPositionParts.flatMap(_.line),
        sourceColumn = firstPositionParts.flatMap(_.column),
        sourceLocation = firstError.flatMap(errorLocationString),
        returnMarkerLabel = None,
        returnLine = None,
        returnColumn = None,
      )
    }
  }

  private[tryfold] def pickLastReturnMarker(context: SiliconDebuggingFailureContext): Option[TryFoldReturnMarkerInstrumentation.ParsedReturnMarker] = {
    val fromState = context.state.toVector.flatMap(_.oldHeaps.keys)
    val fromCounterexample = context.counterExample.toVector.collect {
      case native: viper.silicon.interfaces.SiliconNativeCounterexample => native.oldHeaps.keys
    }.flatten

    val parsed = (fromState ++ fromCounterexample)
      .flatMap(TryFoldReturnMarkerInstrumentation.parseMarker)
      .distinct

    parsed.sortBy(marker => (marker.returnIndex, marker.line, marker.column)).lastOption
  }

  private[tryfold] def rewriteForPostcondition(sequence: AnnotationSequence): AnnotationSequence = {
    val unfolds = sequence.steps.filter(_.action == UnfoldAnnotation)
    val folds = sequence.steps.filter(_.action == FoldAnnotation)
    val deferFoldsAlready = sequence.steps.filter(_.action == DeferFoldAnnotation)

    val rewrittenFolds = folds.reverse.map(step => step.copy(action = DeferFoldAnnotation))
    val rewrittenSteps = unfolds ++ deferFoldsAlready ++ rewrittenFolds

    sequence.copy(steps = rewrittenSteps)
  }

  private def errorLocationString(error: VerificationError): Option[String] =
    positionString(error.pos)

  private final case class PositionParts(
                                          file: Option[String],
                                          line: Option[Int],
                                          column: Option[Int],
                                        )

  private def positionParts(position: ast.Position): Option[PositionParts] =
    position match {
      case sp: ast.AbstractSourcePosition =>
        Some(
          PositionParts(
            file = Option(sp.file).map(_.toString),
            line = Some(sp.line),
            column = Some(sp.column),
          )
        )
      case _ =>
        None
    }

  private def positionString(position: ast.Position): Option[String] =
    if (position == ast.NoPosition) None
    else Some(safeRender(position))

  private def safeRender(value: Any): String =
    try {
      String.valueOf(value)
    } catch {
      case throwable: Throwable => s"<rendering failed: ${throwable.getClass.getSimpleName}>"
    }
}
