package viper.gobra.tryfold

import viper.gobra.ast.{frontend => fe, internal => in}
import viper.gobra.reporting.Source
import viper.gobra.reporting.{Source => ReportSource}
import viper.gobra.translator.Names
import viper.gobra.tryfold.TryFoldWorklistEngine.{AnnotationAction, DeferFoldAnnotation, FoldAnnotation, UnfoldAnnotation}
import viper.gobra.util.Algorithms
import viper.silver.{ast => vpr}
import viper.silver.ast.utility.Simplifier

import java.nio.file.{Path, Paths}
import scala.io.{Source => IoSource}
import scala.collection.mutable
import scala.collection.SortedSet
import scala.util.matching.Regex

object TryFoldGobraAnnotationBacktranslator {

  sealed trait PredicateKind {
    def asString: String
  }

  case object MethodPredicateKind extends PredicateKind {
    override val asString: String = "method"
  }

  case object FunctionPredicateKind extends PredicateKind {
    override val asString: String = "function"
  }

  final case class PredicateDescriptor(
                                        silverName: String,
                                        gobraName: String,
                                        kind: PredicateKind,
                                        source: String,
                                        packageViperId: Option[String] = None,
                                        packageName: Option[String] = None,
                                        pointerArgIndices: Set[Int] = Set.empty,
                                      )

  final case class DirectiveRender(
                                    action: AnnotationAction,
                                    gobraPredicateCall: String,
                                    permissionRational: Option[String],
                                    permissionIsWildcard: Boolean,
                                    permissionSymbolicTerm: Option[String],
                                    annotationLine: String,
                                  )

  final case class CandidateSuccess(
                                     candidateId: Int,
                                     directives: Vector[DirectiveRender],
                                     annotationLines: Vector[String],
                                     annotationLinesWithPrefix: Vector[String],
                                     warnings: Vector[String],
                                     backtranslationTrace: Vector[DirectiveBacktranslationTrace] = Vector.empty,
                                   )

  final case class CandidateFailure(
                                     candidateId: Int,
                                     reason: String,
                                     failureStage: String,
                                     failedDirectiveIndex: Option[Int],
                                     failedPredicateName: Option[String],
                                     silverAnnotationLines: Vector[String],
                                     backtranslationTrace: Vector[DirectiveBacktranslationTrace] = Vector.empty,
                                   )

  final case class BatchRenderResult(
                                      succeeded: Vector[CandidateSuccess],
                                      failed: Vector[CandidateFailure],
                                    )

  final case class DirectiveBacktranslationTrace(
                                                  directiveIndex: Int,
                                                  predicateName: String,
                                                  rawArgsExp: Vector[String],
                                                  afterReturnSubstitutionExp: Vector[String],
                                                  afterNormalizationExp: Vector[String],
                                                  afterAliasResolutionExp: Vector[String],
                                                  afterPostAliasReturnSubstitutionExp: Vector[String],
                                                  renderedArgs: Vector[String],
                                                  notes: Vector[String],
                                                )

  private final case class RenderContext(
                                          methodPredicates: Map[String, PredicateDescriptor],
                                          functionPredicates: Map[String, PredicateDescriptor],
                                          dynamicPredicates: Map[String, PredicateDescriptor],
                                        )

  final case class RenderEnvironment(
                                      packageNameByViperId: Map[String, String],
                                    )

  object RenderEnvironment {
    val empty: RenderEnvironment = RenderEnvironment(packageNameByViperId = Map.empty)
  }

  private final case class FileRenderContext(
                                              targetFile: Option[String],
                                              packageName: Option[String],
                                              importAliasByPackageName: Map[String, String],
                                              sourceLines: Vector[String],
                                            )

  private final case class ScopeContext(
                                         visibleIdentifiers: Set[String],
                                       )

  private final case class RenderError(
                                        reason: String,
                                        stage: String,
                                        directiveIndex: Option[Int] = None,
                                        predicateName: Option[String] = None,
                                        trace: Option[DirectiveBacktranslationTrace] = None,
                                      )

  private final case class ReturnSubstitutionContext(
                                                      primaryByLocalName: Map[String, vpr.Exp],
                                                      sourceFallbackByLocalName: Map[String, vpr.Exp],
                                                      aliasAssignmentsByLocal: Map[String, vpr.Exp],
                                                      contextKind: String,
                                                    )

  private object ReturnSubstitutionContext {
    val empty: ReturnSubstitutionContext = ReturnSubstitutionContext(
      primaryByLocalName = Map.empty,
      sourceFallbackByLocalName = Map.empty,
      aliasAssignmentsByLocal = Map.empty,
      contextKind = "empty",
    )
  }

  private final case class MarkerContext(
                                          method: vpr.Method,
                                          container: vpr.Seqn,
                                          labelIndex: Int,
                                          pathPrefix: Vector[vpr.Stmt],
                                        )

  private final case class AssignmentRecord(
                                             lhsName: String,
                                             rhs: vpr.Exp,
                                             line: Option[Int],
                                             column: Option[Int],
                                             order: Int,
                                           )

  private final case class RenderDirectiveResult(
                                                  render: DirectiveRender,
                                                  trace: DirectiveBacktranslationTrace,
                                                  alternativeSortKey: (Int, Int, Int, Int, String),
                                                )

  private val MaxAliasAlternativesPerArg = 3
  private val MaxDirectiveAlternativeCombinations = 64
  private val MaxRenderedDirectiveAlternatives = 3
  private val MaxRenderedCandidatesPerPlannedSequence = 3

  def renderBatch(
                   plannedSequences: Vector[TryFoldInsertionPlanner.PlannedAnnotationSequence],
                   rootProgram: in.Program,
                   translatedProgram: vpr.Program,
                   renderEnvironment: RenderEnvironment = RenderEnvironment.empty,
                   translationMetadata: Option[TryFoldTranslationMetadata] = None,
                   symbolicStoreByLocal: Map[String, vpr.Exp] = Map.empty,
                   symbolicStoreEntries: Vector[TryFoldFailureContextExtractor.StoreBindingEntry] = Vector.empty,
                 ): BatchRenderResult = {
    val context = buildContext(rootProgram, translationMetadata)
    val fileContextCache = mutable.Map.empty[String, FileRenderContext]
    val scopeContextCache = mutable.Map.empty[String, ScopeContext]
    val succeededBuf = mutable.ArrayBuffer.empty[CandidateSuccess]
    val failedBuf = mutable.ArrayBuffer.empty[CandidateFailure]

    plannedSequences.zipWithIndex.foreach { case (planned, candidateId) =>
      val fileContext = planned.insertionAnchor.sourceFile
        .map(normalizePathString)
        .map(path => fileContextCache.getOrElseUpdate(path, buildFileRenderContext(path)))
        .getOrElse(FileRenderContext(None, None, Map.empty, Vector.empty))
      val insertionLine = planned.insertionAnchor.kind match {
        case TryFoldInsertionPlanner.ReturnMarkerAnchor => planned.insertionAnchor.returnLine
        case _ => planned.insertionAnchor.sourceLine
      }
      val scopeContext = fileContext.targetFile.map { path =>
        val scopeKey = s"$path:${insertionLine.getOrElse(-1)}"
        scopeContextCache.getOrElseUpdate(scopeKey, buildScopeContext(fileContext, insertionLine))
      }
      val returnSubstitutionContexts = buildReturnSubstitutionContexts(
        planned = planned,
        translatedProgram = translatedProgram,
        fileContext = fileContext,
        scopeContext = scopeContext,
        symbolicStoreByLocal = symbolicStoreByLocal,
      )
      val silverLines = planned.plannedSequence.steps.map(TryFoldPathExporter.renderSilverAnnotationLine)
      val renderAttempts = returnSubstitutionContexts.map { substitutionContext =>
        substitutionContext -> renderCandidate(
          candidateId = candidateId,
          planned = planned,
          context = context,
          fileContext = fileContext,
          scopeContext = scopeContext,
          renderEnvironment = renderEnvironment,
          returnSubstitutionContext = substitutionContext,
          symbolicStoreEntries = symbolicStoreEntries,
        )
      }

      val successfulAttempts = renderAttempts.collect {
        case (substitutionContext, Right(successes)) =>
          successes.map(success => substitutionContext -> success)
      }.flatten

      if (successfulAttempts.nonEmpty) {
        val strongestContextPriority = successfulAttempts
          .map { case (substitutionContext, _) =>
            substitutionContextKindPriority(substitutionContext.contextKind)
          }
          .min
        val selectedSuccesses = successfulAttempts
          .filter { case (substitutionContext, _) =>
            substitutionContextKindPriority(substitutionContext.contextKind) == strongestContextPriority
          }
          .sortBy { case (substitutionContext, success) =>
            successSelectionSortKey(substitutionContext, success, scopeContext)
          }
          .map(_._2)
          .foldLeft(Vector.empty[CandidateSuccess]) { (acc, success) =>
            if (acc.exists(existing => existing.annotationLines == success.annotationLines)) acc else acc :+ success
          }
          .take(MaxRenderedCandidatesPerPlannedSequence)
        succeededBuf ++= selectedSuccesses
      } else {
        val orderedErrors = renderAttempts.collect {
          case (substitutionContext, Left(err)) => substitutionContext -> err
        }.sortBy { case (substitutionContext, err) =>
          val priority = substitutionContextKindPriority(substitutionContext.contextKind)
          val stagePenalty = if (err.stage == "scopeValidation") 0 else 1
          (priority, stagePenalty, err.stage, err.reason)
        }
        val firstError = orderedErrors.headOption.map(_._2).getOrElse(
          RenderError(
            reason = "Unknown backtranslation failure (no render attempts produced diagnostics).",
            stage = "renderCandidate",
          )
        )
        failedBuf += CandidateFailure(
          candidateId = candidateId,
          reason = firstError.reason,
          failureStage = firstError.stage,
          failedDirectiveIndex = firstError.directiveIndex,
          failedPredicateName = firstError.predicateName,
          silverAnnotationLines = silverLines,
          backtranslationTrace = firstError.trace.toVector,
        )
      }
    }

    BatchRenderResult(
      succeeded = succeededBuf.toVector,
      failed = failedBuf.toVector,
    )
  }

  private def renderCandidate(
                               candidateId: Int,
                               planned: TryFoldInsertionPlanner.PlannedAnnotationSequence,
                               context: RenderContext,
                               fileContext: FileRenderContext,
                               scopeContext: Option[ScopeContext],
                               renderEnvironment: RenderEnvironment,
                               returnSubstitutionContext: ReturnSubstitutionContext,
                               symbolicStoreEntries: Vector[TryFoldFailureContextExtractor.StoreBindingEntry],
                             ): Either[RenderError, Vector[CandidateSuccess]] = {
    final case class PartialCandidate(
                                       directives: Vector[DirectiveRender],
                                       traces: Vector[DirectiveBacktranslationTrace],
                                       score: (Int, Int, Int, Int, String),
                                     )

    val init = Vector(PartialCandidate(Vector.empty, Vector.empty, (0, 0, 0, 0, "")))
    val accumulated: Either[RenderError, Vector[PartialCandidate]] =
      planned.plannedSequence.steps.zipWithIndex.foldLeft[Either[RenderError, Vector[PartialCandidate]]](Right(init)) {
        case (Right(partials), (directive, idx)) =>
          renderDirectiveAlternatives(
            directiveIndex = idx,
            directive = directive,
            context = context,
            fileContext = fileContext,
            scopeContext = scopeContext,
            renderEnvironment = renderEnvironment,
            returnSubstitutionContext = returnSubstitutionContext,
            symbolicStoreEntries = symbolicStoreEntries,
          ).map { alternatives =>
            val expanded = for {
              partial <- partials
              alt <- alternatives
            } yield PartialCandidate(
              directives = partial.directives :+ alt.render,
              traces = partial.traces :+ alt.trace,
              score = addScore(partial.score, alt.alternativeSortKey),
            )
            expanded
              .foldLeft(Vector.empty[PartialCandidate]) { (acc, candidate) =>
                if (acc.exists(existing => existing.directives.map(_.annotationLine) == candidate.directives.map(_.annotationLine))) acc
                else acc :+ candidate
              }
              .sortBy(c => (c.score, c.directives.map(_.annotationLine).mkString("|")))
              .take(MaxRenderedCandidatesPerPlannedSequence)
          }.left.map(_.copy(directiveIndex = Some(idx)))
        case (left@Left(_), _) => left
      }

    accumulated.flatMap { candidates =>
      val successes = candidates.flatMap { candidate =>
        val lines = candidate.directives.map(_.annotationLine)
        val warnings = collectInternalEncodingWarnings(lines)
        if (warnings.nonEmpty) {
          None
        } else {
          Some(
            CandidateSuccess(
              candidateId = candidateId,
              directives = candidate.directives,
              annotationLines = lines,
              annotationLinesWithPrefix = lines.map(line => s"//@ $line"),
              warnings = warnings,
              backtranslationTrace = candidate.traces,
            )
          )
        }
      }
      if (successes.nonEmpty) Right(successes.take(MaxRenderedCandidatesPerPlannedSequence))
      else {
        val trace = candidates.lastOption.flatMap(_.traces.lastOption)
        Left(
          RenderError(
            reason = "All rendered candidate variants were rejected by hard filters.",
            stage = "renderCandidateVariantsRejected",
            trace = trace,
          )
        )
      }
    }
  }

  private def renderDirectiveAlternatives(
                               directiveIndex: Int,
                               directive: TryFoldWorklistEngine.AnnotationDirective,
                               context: RenderContext,
                               fileContext: FileRenderContext,
                               scopeContext: Option[ScopeContext],
                               renderEnvironment: RenderEnvironment,
                               returnSubstitutionContext: ReturnSubstitutionContext,
                               symbolicStoreEntries: Vector[TryFoldFailureContextExtractor.StoreBindingEntry],
                             ): Either[RenderError, Vector[RenderDirectiveResult]] = {
    val renderedArgsFromAstAndTrace: Option[Vector[(Vector[(String, vpr.Exp)], DirectiveBacktranslationTrace, (Int, Int, Int, Int, String))]] = directive.argsExp.map { args =>
      val rawArgsExp = args.map(safeRender)
      val substitutedArgsExp = args.map(arg => applyPrimaryReturnSubstitution(arg, returnSubstitutionContext))
      val substitutedArgsExpRendered = substitutedArgsExp.map(safeRender)
      val typedStoreSubstitutionPerArg = substitutedArgsExp.map { arg =>
        applyTypedStoreTupleProjectionSubstitution(
          exp = arg,
          symbolicStoreEntries = symbolicStoreEntries,
        )
      }
      val typedStoreSubstitutedArgsExp = typedStoreSubstitutionPerArg.map(_.exp)
      val normalizedPerArg = typedStoreSubstitutedArgsExp.map(arg => normalizeAndSimplify(arg))
      val normalizedArgsExp = normalizedPerArg.map(_.exp)
      val normalizedArgsExpRendered = normalizedArgsExp.map(safeRender)

      val aliasMap = aliasAssignmentsForContext(returnSubstitutionContext)
      val reverseAliasIndex = buildReverseStoreAliasIndex(aliasMap)
      val aliasResolutionPerArg = normalizedArgsExp.map { arg =>
        resolveAliases(
          exp = arg,
          assignmentsByLocal = aliasMap,
        )
      }
      val aliasedArgsExp = aliasResolutionPerArg.map(_.resolved)
      val aliasedArgsExpRendered = aliasedArgsExp.map(safeRender)
      val selectedPostAliasAlternativesPerArg = aliasedArgsExp.map { arg =>
        selectPostAliasExpressions(
          aliasedExp = arg,
          reverseAliasIndex = reverseAliasIndex,
          substitutionContext = returnSubstitutionContext,
          scopeContext = scopeContext,
          topK = MaxAliasAlternativesPerArg,
        )
      }
      val selectedAlternativeCombos = cartesianProductLimited(
        selectedPostAliasAlternativesPerArg,
        MaxDirectiveAlternativeCombinations,
      )
      selectedAlternativeCombos.zipWithIndex.map { case (selectedPostAliasPerArg, comboIdx) =>
        val postAliasSubstitutedPerArg = selectedPostAliasPerArg.map(_.selectedPostAliasExp)
        val postAliasNormalizedPerArg = postAliasSubstitutedPerArg.map(arg => normalizeAndSimplify(arg))
        val postAliasNormalizedArgsExp = postAliasNormalizedPerArg.map(_.exp)
        val postAliasNormalizedArgsExpRendered = postAliasNormalizedArgsExp.map(safeRender)
        val renderedArgs = postAliasNormalizedArgsExp.map(arg => translateExpToGobraExpr(arg))
        val score = selectedPostAliasPerArg.map(_.score).foldLeft((0, 0, 0, 0, ""))(addScore)
        val notes = normalizedPerArg.flatMap(_.notes) ++
          typedStoreSubstitutionPerArg.flatMap(_.notes) ++
          aliasResolutionPerArg.flatMap(_.notes) ++
          selectedPostAliasPerArg.flatMap(_.notes) ++
          postAliasNormalizedPerArg.flatMap(_.notes) ++
          Vector(
            s"returnSubstitution.contextKind=${returnSubstitutionContext.contextKind}",
            s"reverseAlias.comboIndex=$comboIdx",
            s"reverseAlias.comboScore=$score",
          )

        val trace = DirectiveBacktranslationTrace(
          directiveIndex = directiveIndex,
          predicateName = directive.predicateName,
          rawArgsExp = rawArgsExp,
          afterReturnSubstitutionExp = substitutedArgsExpRendered,
          afterNormalizationExp = normalizedArgsExpRendered,
          afterAliasResolutionExp = aliasedArgsExpRendered,
          afterPostAliasReturnSubstitutionExp = postAliasNormalizedArgsExpRendered,
          renderedArgs = renderedArgs,
          notes = notes,
        )
        (renderedArgs.zip(postAliasNormalizedArgsExp), trace, score)
      }
        .sortBy { case (renderedArgs, _, score) =>
          (score, renderedArgs.map(_._1).mkString(","))
        }
        .take(MaxDirectiveAlternativeCombinations)
    }
    val fallbackTrace = DirectiveBacktranslationTrace(
      directiveIndex = directiveIndex,
      predicateName = directive.predicateName,
      rawArgsExp = Vector.empty,
      afterReturnSubstitutionExp = Vector.empty,
      afterNormalizationExp = Vector.empty,
      afterAliasResolutionExp = Vector.empty,
      afterPostAliasReturnSubstitutionExp = Vector.empty,
      renderedArgs = directive.args,
      notes = Vector("legacy-string-args-fallback"),
    )
    resolveDescriptor(directive.predicateName, context).flatMap { descriptor =>
      val rawAttempts: Vector[(Option[Vector[(String, vpr.Exp)]], DirectiveBacktranslationTrace, (Int, Int, Int, Int, String))] =
        renderedArgsFromAstAndTrace match {
          case Some(v) =>
            v.map { case (argsFromAst, trace, score) => (Some(argsFromAst), trace, score) }
          case None if directive.args.isEmpty =>
            Vector((None, fallbackTrace, (0, 0, 0, 0, "")))
          case None if directive.args.nonEmpty =>
            Vector((None, fallbackTrace, (0, 0, 0, 0, "")))
          case None =>
            Vector((None, fallbackTrace, (0, 0, 0, 0, "")))
        }

      val renderErrors = mutable.ArrayBuffer.empty[RenderError]
      val renderedResults = rawAttempts.flatMap { case (argsFromAstOpt, trace, score) =>
        val renderedCall = argsFromAstOpt match {
          case Some(argsFromAst) =>
            renderPredicateCallFromArgs(
              descriptor = descriptor,
              renderedArgs = argsFromAst.map(_._1),
              renderedArgsExp = Some(argsFromAst.map(_._2)),
              fileContext = fileContext,
              renderEnvironment = renderEnvironment,
            )
          case None if directive.args.isEmpty =>
            renderPredicateCallFromArgs(
              descriptor = descriptor,
              renderedArgs = Vector.empty,
              renderedArgsExp = None,
              fileContext = fileContext,
              renderEnvironment = renderEnvironment,
            )
          case None if directive.args.nonEmpty =>
            renderPredicateCallFromArgs(
              descriptor = descriptor,
              renderedArgs = directive.args,
              renderedArgsExp = None,
              fileContext = fileContext,
              renderEnvironment = renderEnvironment,
            )
          case None =>
            Left(
              RenderError(
                reason = s"AST-only backtranslation requires non-empty argsExp for predicate '${directive.predicateName}', but none were provided.",
                stage = "astArgsMissing",
                predicateName = Some(directive.predicateName),
                trace = Some(trace),
              )
            )
        }
        renderedCall match {
          case Left(err) =>
            renderErrors += err.copy(trace = Some(trace))
            None
          case Right(predicateCall) =>
            if (scopeContext.exists(sc => !expressionIdentifiersInScope(predicateCall, sc.visibleIdentifiers))) {
              renderErrors += RenderError(
                reason = s"Rendered predicate call '$predicateCall' references identifiers that are out of scope at insertion location.",
                stage = "scopeValidation",
                predicateName = Some(directive.predicateName),
                trace = Some(trace),
              )
              None
            } else {
              val action = actionAsString(directive.action)
              val permissionSuffix =
                if (directive.permissionIsWildcard) ", _"
                else directive.permission.map(p => s", ${p.rational}").getOrElse("")
              val line = s"$action acc($predicateCall$permissionSuffix)"
              findUnsupportedEncodingToken(line) match {
                case Some(token) =>
                  renderErrors += RenderError(
                    reason = s"Rendered line still contains internal encoding token '$token'.",
                    stage = "internalTokenValidation",
                    predicateName = Some(directive.predicateName),
                    trace = Some(trace),
                  )
                  None
                case None =>
                  val directiveRender = DirectiveRender(
                    action = directive.action,
                    gobraPredicateCall = predicateCall,
                    permissionRational = directive.permission.map(_.rational),
                    permissionIsWildcard = directive.permissionIsWildcard,
                    permissionSymbolicTerm = directive.permissionSymbolicTerm,
                    annotationLine = line,
                  )
                  Some(RenderDirectiveResult(render = directiveRender, trace = trace, alternativeSortKey = score))
              }
            }
        }
      }

      val deduplicated = renderedResults
        .foldLeft(Vector.empty[RenderDirectiveResult]) { (acc, next) =>
          if (acc.exists(existing => existing.render.annotationLine == next.render.annotationLine)) acc else acc :+ next
        }
        .sortBy(result => (result.alternativeSortKey, result.render.annotationLine))
        .take(MaxRenderedDirectiveAlternatives)

      if (deduplicated.nonEmpty) {
        Right(deduplicated)
      } else {
        val firstError = renderErrors.sortBy(err => (if (err.stage == "scopeValidation") 0 else 1, err.stage, err.reason)).headOption.getOrElse(
          RenderError(
            reason = s"No renderable directive alternatives remained for predicate '${directive.predicateName}'.",
            stage = "renderDirectiveAlternatives",
            predicateName = Some(directive.predicateName),
            trace = Some(fallbackTrace),
          )
        )
        Left(firstError)
      }
    }
  }

  private def buildReturnSubstitutionContexts(
                                               planned: TryFoldInsertionPlanner.PlannedAnnotationSequence,
                                               translatedProgram: vpr.Program,
                                               fileContext: FileRenderContext,
                                               scopeContext: Option[ScopeContext],
                                               symbolicStoreByLocal: Map[String, vpr.Exp],
                                             ): Vector[ReturnSubstitutionContext] = {
    val labelOpt = planned.insertionAnchor.returnMarkerLabel
    val markerContextOpt = labelOpt.flatMap(label => findMarkerContext(translatedProgram, label))
    val markerMethodFallbackOpt = labelOpt
      .flatMap(TryFoldReturnMarkerInstrumentation.parseMarker)
      .flatMap(parsed => findMethodByHash(translatedProgram, parsed.methodHash))

    val methodBySourceLocationOpt = planned.insertionAnchor.sourceFile.flatMap { file =>
      planned.insertionAnchor.sourceLine.flatMap { line =>
        findMethodBySourceLocation(
          program = translatedProgram,
          sourceFile = file,
          sourceLine = line,
        )
      }
    }

    val aliasAssignments = markerContextOpt.map { markerContext =>
      collectAssignmentsLatest(markerContext.pathPrefix)
    }.orElse {
      markerMethodFallbackOpt.map(collectRootLevelAssignmentsLatest)
    }.orElse {
      methodBySourceLocationOpt.map(collectRootLevelAssignmentsLatest)
    }.getOrElse(Map.empty[String, vpr.Exp])

    val aliasAssignmentVariants = buildAliasAssignmentVariants(
      aliasAssignments = aliasAssignments,
      symbolicStoreByLocal = symbolicStoreByLocal,
    )
    val methodContextOpt = markerContextOpt.map(_.method)
      .orElse(markerMethodFallbackOpt)
      .orElse(methodBySourceLocationOpt)

    val observedSubstitutionKeys = collectObservedSubstitutionKeys(
      aliasAssignments = aliasAssignments,
      symbolicStoreByLocal = symbolicStoreByLocal,
      methodContextOpt = methodContextOpt,
    )

    val substitutionContexts: Vector[(Map[String, vpr.Exp], Map[String, vpr.Exp], String)] =
      if (!planned.isPostconditionFailure || planned.insertionAnchor.kind != TryFoldInsertionPlanner.ReturnMarkerAnchor) {
        val nonPostFallback = methodContextOpt
          .flatMap(method => buildNearestReturnFallbackMapFromMethod(method, planned, fileContext))
          .filter(_.nonEmpty)
          .getOrElse(Map.empty[String, vpr.Exp])
        val withFallback =
          if (nonPostFallback.nonEmpty) {
            Vector(
              (nonPostFallback, Map.empty[String, vpr.Exp], "non_post_return_primary"),
              (Map.empty[String, vpr.Exp], nonPostFallback, "non_post_source_fallback"),
              (Map.empty[String, vpr.Exp], Map.empty[String, vpr.Exp], "non_post_identity"),
            )
          } else {
            Vector((Map.empty[String, vpr.Exp], Map.empty[String, vpr.Exp], "non_post_identity"))
          }
        withFallback
      } else {
        val fallbackMap = markerContextOpt
          .map(mc => buildSingleReturnFallbackMap(mc, planned, fileContext))
          .orElse(markerMethodFallbackOpt.map(method => buildSingleReturnFallbackMapFromMethod(method, planned, fileContext)))
          .orElse(methodBySourceLocationOpt.map(method => buildSingleReturnFallbackMapFromMethod(method, planned, fileContext)))
          .getOrElse(Map.empty[String, vpr.Exp])

        val returnAlternatives: Vector[Map[String, vpr.Exp]] = markerContextOpt match {
          case Some(markerContext) =>
            buildFormalReturnSubstitutionMaps(
              markerContext = markerContext,
              planned = planned,
              symbolicStoreByLocal = symbolicStoreByLocal,
            )
          case _ =>
            Vector.empty
        }

        if (returnAlternatives.nonEmpty) {
          val primaryContexts = returnAlternatives.map { primary =>
            val missingFallback = fallbackMap.filter { case (k, _) => !primary.contains(k) }
            (primary, missingFallback, "post_return_primary")
          }
          val fallbackOnly = if (fallbackMap.nonEmpty)
            Vector((Map.empty[String, vpr.Exp], fallbackMap, "post_return_fallback_only"))
          else Vector.empty
          primaryContexts ++ fallbackOnly
        } else if (fallbackMap.nonEmpty) {
          Vector((Map.empty[String, vpr.Exp], fallbackMap, "post_return_fallback_only"))
        } else {
          Vector((Map.empty[String, vpr.Exp], Map.empty[String, vpr.Exp], "post_return_identity"))
        }
      }

    val rawContexts: Vector[ReturnSubstitutionContext] =
      for {
        (primaryMapRaw, sourceFallbackMapRaw, contextKind) <- substitutionContexts
        primaryMap = expandSubstitutionMapAliases(
          enrichPrimaryMapWithObservedAliases(
            map = primaryMapRaw,
            observedKeys = observedSubstitutionKeys,
          )
        )
        sourceFallbackMap = expandSubstitutionMapAliases(sourceFallbackMapRaw)
        aliasMap <- aliasAssignmentVariants
      } yield ReturnSubstitutionContext(
        primaryByLocalName = primaryMap,
        sourceFallbackByLocalName = sourceFallbackMap,
        aliasAssignmentsByLocal = aliasMap,
        contextKind = contextKind,
      )

    rankAndDeduplicateSubstitutionContexts(rawContexts, scopeContext)
  }

  private def buildAliasAssignmentVariants(
                                          aliasAssignments: Map[String, vpr.Exp],
                                          symbolicStoreByLocal: Map[String, vpr.Exp],
                                        ): Vector[Map[String, vpr.Exp]] = {
    val variants = Vector(
      expandSubstitutionMapAliases(aliasAssignments ++ symbolicStoreByLocal),
    )
    deduplicateSubstitutionMaps(variants)
  }

  private def deduplicateSubstitutionMaps(
                                           maps: Vector[Map[String, vpr.Exp]]
                                         ): Vector[Map[String, vpr.Exp]] = {
    val seen = mutable.LinkedHashSet.empty[String]
    maps.foldLeft(Vector.empty[Map[String, vpr.Exp]]) { (acc, current) =>
      val signature = substitutionMapSignature(current)
      if (seen.contains(signature)) acc
      else {
        seen += signature
        acc :+ current
      }
    }
  }

  private def expandSubstitutionMapAliases(map: Map[String, vpr.Exp]): Map[String, vpr.Exp] = {
    val expanded = mutable.LinkedHashMap.empty[String, vpr.Exp]
    map.foreach { case (key, value) =>
      val noAt = key.replaceAll("@\\d+", "")
      val aliases = Vector(
        key,
        noAt,
        stripVarSuffix(noAt),
        stripVarSuffix(key),
      ).filter(_.nonEmpty).distinct
      aliases.foreach { alias =>
        if (!expanded.contains(alias)) {
          expanded += alias -> value
        }
      }
    }
    expanded.toMap
  }

  private def enrichPrimaryMapWithObservedAliases(
                                                   map: Map[String, vpr.Exp],
                                                   observedKeys: Set[String],
                                                 ): Map[String, vpr.Exp] = {
    if (map.isEmpty || observedKeys.isEmpty) {
      map
    } else {
      val enriched = mutable.LinkedHashMap.empty[String, vpr.Exp] ++ map
      map.foreach { case (key, value) =>
        val keyBase = stripVarSuffix(key.replaceAll("@\\d+", ""))
        observedKeys.foreach { observed =>
          val observedBase = stripVarSuffix(observed.replaceAll("@\\d+", ""))
          if (keyBase.nonEmpty && observedBase == keyBase && !enriched.contains(observed)) {
            enriched += observed -> value
          }
        }
      }
      enriched.toMap
    }
  }

  private def collectObservedSubstitutionKeys(
                                               aliasAssignments: Map[String, vpr.Exp],
                                               symbolicStoreByLocal: Map[String, vpr.Exp],
                                               methodContextOpt: Option[vpr.Method],
                                             ): Set[String] = {
    val fromMethod = methodContextOpt.toVector.flatMap { method =>
      collectRootLevelAssignmentRecords(method).map(_.lhsName)
    }
    (aliasAssignments.keySet ++ symbolicStoreByLocal.keySet ++ fromMethod).filter(_.nonEmpty)
  }

  private def findMethodByHash(program: vpr.Program, methodHash: String): Option[vpr.Method] =
    program.methods.find(method => Names.hash(method.name) == methodHash)

  private def findMethodBySourceLocation(
                                          program: vpr.Program,
                                          sourceFile: String,
                                          sourceLine: Int,
                                        ): Option[vpr.Method] = {
    val normalizedFile = normalizePathString(sourceFile)

    final case class Candidate(method: vpr.Method, kind: Int, distance: Int)

    val candidates = program.methods.toVector.flatMap { method =>
      method.body.toVector.flatMap { body =>
        val linesInFile = collectSourceLinesForFile(body, normalizedFile)
        if (linesInFile.isEmpty) Vector.empty
        else {
          val minLine = linesInFile.min
          val maxLine = linesInFile.max
          if (linesInFile.contains(sourceLine)) {
            Vector(Candidate(method, kind = 0, distance = 0))
          } else if (sourceLine >= minLine && sourceLine <= maxLine) {
            val midpoint = (minLine + maxLine) / 2
            Vector(Candidate(method, kind = 1, distance = math.abs(sourceLine - midpoint)))
          } else {
            val distance = math.min(math.abs(sourceLine - minLine), math.abs(sourceLine - maxLine))
            Vector(Candidate(method, kind = 2, distance = distance))
          }
        }
      }
    }

    candidates.sortBy(c => (c.kind, c.distance, c.method.name)).headOption.map(_.method)
  }

  private def collectSourceLinesForFile(node: vpr.Node, normalizedFile: String): Vector[Int] = {
    val self = nodeSourceFileAndLine(node).toVector.collect {
      case (file, line) if file == normalizedFile => line
    }
    val children = node.subnodes.toVector.collect { case child: vpr.Node => child }
      .flatMap(child => collectSourceLinesForFile(child, normalizedFile))
    self ++ children
  }

  private def nodeSourceFileAndLine(node: vpr.Node): Option[(String, Int)] =
    try {
      Source.unapply(node).flatMap { info =>
        Option(info.origin.pos).flatMap { pos =>
          val file = Option(pos.file).map(_.toString)
          val line = Option(pos.line)
          for {
            f <- file
            l <- line
          } yield (normalizePathString(f), l)
        }
      }
    } catch {
      case _: Throwable => None
    }

  private def buildSingleReturnFallbackMap(
                                            markerContext: MarkerContext,
                                            planned: TryFoldInsertionPlanner.PlannedAnnotationSequence,
                                            fileContext: FileRenderContext,
                                          ): Map[String, vpr.Exp] = {
    buildSingleReturnFallbackMapFromMethod(markerContext.method, planned, fileContext)
  }

  private def buildSingleReturnFallbackMapFromMethod(
                                                      method: vpr.Method,
                                                      planned: TryFoldInsertionPlanner.PlannedAnnotationSequence,
                                                      fileContext: FileRenderContext,
                                                    ): Map[String, vpr.Exp] = {
    val returnExprs = planned.insertionAnchor.returnLine
      .flatMap(line => extractReturnExpressions(fileContext.sourceLines, line))
      .getOrElse(Vector.empty)

    val formals = method.formalReturns.toVector
    if (formals.isEmpty || returnExprs.isEmpty) Map.empty
    else {
      formals
        .zipAll(returnExprs, null, "")
        .flatMap {
          case (formal, exprText) if formal != null =>
            parseFallbackReturnExpr(exprText, formal.typ).map(exp => formal.name -> exp)
          case _ =>
            None
        }
        .toMap
    }
  }

  private def buildNearestReturnFallbackMapFromMethod(
                                                       method: vpr.Method,
                                                       planned: TryFoldInsertionPlanner.PlannedAnnotationSequence,
                                                       fileContext: FileRenderContext,
                                                     ): Option[Map[String, vpr.Exp]] = {
    val sourceLines = fileContext.sourceLines
    if (sourceLines.isEmpty) {
      None
    } else {
      val insertionLineOpt = insertionLineFor(planned)
      val methodLineRangeOpt = for {
        normalizedFile <- fileContext.targetFile.map(normalizePathString)
        body <- method.body
        lines = collectSourceLinesForFile(body, normalizedFile)
        if lines.nonEmpty
      } yield (lines.min, lines.max)

      val lowerBound = methodLineRangeOpt.map(_._1).getOrElse(1)
      val upperBound = methodLineRangeOpt.map(_._2).getOrElse(sourceLines.size)
      val startLine = insertionLineOpt.map(line => math.max(line, lowerBound)).getOrElse(lowerBound)
      val endLine = math.min(upperBound, sourceLines.size)

      if (startLine > endLine) {
        None
      } else {
        val returnLineOpt = (startLine to endLine).find(line => extractReturnExpressions(sourceLines, line).exists(_.nonEmpty))
        returnLineOpt.flatMap { returnLine =>
          val returnExprs = extractReturnExpressions(sourceLines, returnLine).getOrElse(Vector.empty)
          val formals = method.formalReturns.toVector
          val map =
            if (formals.isEmpty || returnExprs.isEmpty) Map.empty[String, vpr.Exp]
            else {
              formals
                .zipAll(returnExprs, null, "")
                .flatMap {
                  case (formal, exprText) if formal != null =>
                    parseFallbackReturnExpr(exprText, formal.typ).map(exp => formal.name -> exp)
                  case _ =>
                    None
                }
                .toMap
            }
          Option.when(map.nonEmpty)(map)
        }
      }
    }
  }

  private def insertionLineFor(planned: TryFoldInsertionPlanner.PlannedAnnotationSequence): Option[Int] =
    planned.insertionAnchor.kind match {
      case TryFoldInsertionPlanner.ReturnMarkerAnchor =>
        planned.insertionAnchor.returnLine.orElse(planned.insertionAnchor.sourceLine)
      case _ =>
        planned.insertionAnchor.sourceLine.orElse(planned.insertionAnchor.returnLine)
    }

  private val ReturnPrefixPattern: Regex = "^return\\s+(.*)$".r
  private val IdentifierPattern: Regex = "^[A-Za-z_][A-Za-z0-9_]*$".r

  private def extractReturnExpressions(sourceLines: Vector[String], returnLine1Based: Int): Option[Vector[String]] = {
    if (returnLine1Based <= 0 || returnLine1Based > sourceLines.size) None
    else {
      val raw = sourceLines(returnLine1Based - 1)
      val noLineComment = stripLineCommentAwareLiterals(raw).trim
      noLineComment match {
        case ReturnPrefixPattern(exprs) =>
          val parts = splitTopLevelComma(exprs)
          val normalized = parts.map(_.trim).filter(_.nonEmpty)
          if (normalized.nonEmpty) Some(normalized) else None
        case _ => None
      }
    }
  }

  private def parseFallbackReturnExpr(expr: String, typ: vpr.Type): Option[vpr.Exp] = {
    val trimmed = expr.trim
    trimmed match {
      case IdentifierPattern() =>
        Some(vpr.LocalVar(trimmed, typ)())
      case _ =>
        None
    }
  }

  private def splitTopLevelComma(exprs: String): Vector[String] = {
    val builder = Vector.newBuilder[String]
    val current = new StringBuilder
    var parenDepth = 0
    var bracketDepth = 0
    var braceDepth = 0
    var inSingleQuote = false
    var inDoubleQuote = false
    var inBacktick = false
    var escaped = false

    def flushCurrent(): Unit = {
      builder += current.result()
      current.clear()
    }

    exprs.foreach { ch =>
      if (escaped) {
        current.append(ch)
        escaped = false
      } else if ((inSingleQuote || inDoubleQuote) && ch == '\\') {
        current.append(ch)
        escaped = true
      } else if (inBacktick) {
        current.append(ch)
        if (ch == '`') inBacktick = false
      } else if (inSingleQuote) {
        current.append(ch)
        if (ch == '\'') inSingleQuote = false
      } else if (inDoubleQuote) {
        current.append(ch)
        if (ch == '"') inDoubleQuote = false
      } else {
        ch match {
          case '`' =>
            inBacktick = true
            current.append(ch)
          case '\'' =>
            inSingleQuote = true
            current.append(ch)
          case '"' =>
            inDoubleQuote = true
            current.append(ch)
          case '(' =>
            parenDepth += 1
            current.append(ch)
          case ')' =>
            parenDepth = math.max(0, parenDepth - 1)
            current.append(ch)
          case '[' =>
            bracketDepth += 1
            current.append(ch)
          case ']' =>
            bracketDepth = math.max(0, bracketDepth - 1)
            current.append(ch)
          case '{' =>
            braceDepth += 1
            current.append(ch)
          case '}' =>
            braceDepth = math.max(0, braceDepth - 1)
            current.append(ch)
          case ',' if parenDepth == 0 && bracketDepth == 0 && braceDepth == 0 =>
            flushCurrent()
          case _ =>
            current.append(ch)
        }
      }
    }
    flushCurrent()
    builder.result()
  }

  private def stripLineCommentAwareLiterals(raw: String): String = {
    val out = new StringBuilder
    var i = 0
    var inSingleQuote = false
    var inDoubleQuote = false
    var inBacktick = false
    var escaped = false
    while (i < raw.length) {
      val ch = raw.charAt(i)
      if (escaped) {
        out.append(ch)
        escaped = false
      } else if ((inSingleQuote || inDoubleQuote) && ch == '\\') {
        out.append(ch)
        escaped = true
      } else if (inBacktick) {
        out.append(ch)
        if (ch == '`') inBacktick = false
      } else if (inSingleQuote) {
        out.append(ch)
        if (ch == '\'') inSingleQuote = false
      } else if (inDoubleQuote) {
        out.append(ch)
        if (ch == '"') inDoubleQuote = false
      } else if (ch == '/' && (i + 1) < raw.length && raw.charAt(i + 1) == '/') {
        return out.result()
      } else {
        ch match {
          case '`' => inBacktick = true
          case '\'' => inSingleQuote = true
          case '"' => inDoubleQuote = true
          case _ =>
        }
        out.append(ch)
      }
      i += 1
    }
    out.result()
  }

  private def findMarkerContext(program: vpr.Program, labelName: String): Option[MarkerContext] =
    program.methods.iterator.flatMap { method =>
      method.body.toVector.iterator.flatMap { body =>
        findMarkerContextInStmt(
          method = method,
          stmt = body,
          labelName = labelName,
          prefix = Vector.empty,
        )
      }
    }.toVector.headOption

  private def findMarkerContextInStmt(
                                       method: vpr.Method,
                                       stmt: vpr.Stmt,
                                       labelName: String,
                                       prefix: Vector[vpr.Stmt],
                                     ): Option[MarkerContext] =
    stmt match {
      case seqn: vpr.Seqn =>
        val statements = seqn.ss.toVector
        var idx = 0
        while (idx < statements.size) {
          val current = statements(idx)
          current match {
            case vpr.Label(name, _) if name == labelName =>
              return Some(
                MarkerContext(
                  method = method,
                  container = seqn,
                  labelIndex = idx,
                  pathPrefix = prefix ++ statements.take(idx),
                )
              )
            case _ =>
          }

          val nestedPrefix = prefix ++ statements.take(idx)
          findMarkerContextInStmt(
            method = method,
            stmt = current,
            labelName = labelName,
            prefix = nestedPrefix,
          ) match {
            case some@Some(_) => return some
            case None =>
          }
          idx += 1
        }
        None

      case iff: vpr.If =>
        findMarkerContextInStmt(method, iff.thn, labelName, prefix)
          .orElse(findMarkerContextInStmt(method, iff.els, labelName, prefix))

      case loop: vpr.While =>
        findMarkerContextInStmt(method, loop.body, labelName, prefix)

      case _ =>
        None
    }

  private def buildFormalReturnSubstitutionMaps(
                                                 markerContext: MarkerContext,
                                                 planned: TryFoldInsertionPlanner.PlannedAnnotationSequence,
                                                 symbolicStoreByLocal: Map[String, vpr.Exp],
                                               ): Vector[Map[String, vpr.Exp]] = {
    val formalReturns = markerContext.method.formalReturns.toVector
    if (formalReturns.isEmpty) {
      Vector.empty
    } else {
      val returnCutoff = planned.insertionAnchor.returnLine.map(line => (line, planned.insertionAnchor.returnColumn))
      val prefixAssignments = collectAssignmentsWithPos(markerContext.pathPrefix)
      val rootAssignments = collectRootLevelAssignmentRecords(markerContext.method)
      val bridgeAssignments = collectRootLevelFormalReturnAssignmentRecords(markerContext.method)
      val combinedAssignments = rootAssignments ++ prefixAssignments ++ bridgeAssignments
      val reverseAliasIndex = buildReverseStoreAliasIndex(symbolicStoreByLocal)

      val replacementAxes = formalReturns.map { formal =>
        val occurrence = vpr.LocalVar(formal.name, formal.typ)()
        val base = stripVarSuffix(formal.name)
        val seedNames = (Seq(formal.name) ++
          combinedAssignments.map(_.lhsName).filter(n => stripVarSuffix(n) == base)).distinct

        val chainResolved = seedNames.flatMap { seed =>
          resolveAssignmentChainAll(
            varName = seed,
            assignments = combinedAssignments,
            returnCutoff = returnCutoff,
            visited = Set.empty,
            depth = 0,
            maxDepth = 24,
          )
        }

        val reverseAliasResolved = chainResolved.flatMap {
          case lv: vpr.AbstractLocalVar =>
            lookupReverseAliases(lv.name, reverseAliasIndex).map(alias => vpr.LocalVar(alias, formal.typ)(): vpr.Exp)
          case _ =>
            Vector.empty
        }

        val normalized = deduplicateExpByRender(
          (chainResolved ++ reverseAliasResolved).map(decodeAndSimplify)
        ).filterNot {
          case lv: vpr.AbstractLocalVar =>
            stripVarSuffix(lv.name) == stripVarSuffix(formal.name)
          case _ =>
            false
        }

        val axis = deduplicateExpByRender(Vector(occurrence: vpr.Exp) ++ normalized)
        formal.name -> axis
      }

      val alternatives = cartesianProduct(replacementAxes.map(_._2))
      val replacementNames = replacementAxes.map(_._1)
      val rawMaps = alternatives.map { combo =>
        replacementNames.zip(combo).toMap
      }
      rawMaps
        .filter(map => map.exists { case (formalName, exp) => !isIdentityReplacement(formalName, exp) })
        .map(pruneFormalIdentityMappings)
        .filter(_.nonEmpty)
        .map(normalizeSubstitutionMap)
        .distinctBy(substitutionMapSignature)
    }
  }

  private def collectRootLevelFormalReturnAssignmentRecords(method: vpr.Method): Vector[AssignmentRecord] = {
    val formalNames = method.formalReturns.map(_.name).toSet
    method.body match {
      case Some(root) =>
        collectAssignmentsWithPos(Vector(root)).filter(record => formalNames.contains(record.lhsName))
      case None =>
        Vector.empty
    }
  }

  private def collectRootLevelAssignmentRecords(method: vpr.Method): Vector[AssignmentRecord] =
    method.body match {
      case Some(root) => collectAssignmentsWithPos(Vector(root))
      case None => Vector.empty
    }

  private def collectRootLevelAssignmentsLatest(method: vpr.Method): Map[String, vpr.Exp] =
    assignmentRecordsToLatestMap(collectRootLevelAssignmentRecords(method))

  private def collectAssignmentsLatest(stmts: Vector[vpr.Stmt]): Map[String, vpr.Exp] =
    assignmentRecordsToLatestMap(collectAssignmentsWithPos(stmts))

  private def assignmentRecordsToLatestMap(records: Vector[AssignmentRecord]): Map[String, vpr.Exp] = {
    val latest = mutable.LinkedHashMap.empty[String, vpr.Exp]
    records.foreach(record => latest.update(record.lhsName, record.rhs))
    latest.toMap
  }

  private def collectAssignmentsWithPos(stmts: Vector[vpr.Stmt]): Vector[AssignmentRecord] = {
    val records = mutable.ArrayBuffer.empty[AssignmentRecord]
    var order = 0

    def sourceLineCol(node: vpr.Node): (Option[Int], Option[Int]) =
      try {
        Source.unapply(node)
          .flatMap(info => Option(info.origin.pos))
          .map(pos => (Option(pos.line), Option(pos.column)))
          .getOrElse((None, None))
      } catch {
        case _: Throwable => (None, None)
      }

    def visit(stmt: vpr.Stmt): Unit =
      stmt match {
        case vpr.LocalVarAssign(lhs, rhs) =>
          val (lineOpt, colOpt) = sourceLineCol(stmt)
          records += AssignmentRecord(
            lhsName = lhs.name,
            rhs = rhs,
            line = lineOpt,
            column = colOpt,
            order = order,
          )
          order += 1
        case seqn: vpr.Seqn =>
          seqn.ss.foreach(visit)
        case iff: vpr.If =>
          visit(iff.thn)
          visit(iff.els)
        case loop: vpr.While =>
          visit(loop.body)
        case _ =>
      }

    stmts.foreach(visit)
    records.toVector
  }

  private def selectAssignmentsForVar(
                                       varName: String,
                                       assignments: Vector[AssignmentRecord],
                                       returnCutoff: Option[(Int, Option[Int])],
                                     ): Vector[AssignmentRecord] = {
    val assigns = assignments.filter(_.lhsName == varName)
    if (assigns.isEmpty) {
      Vector.empty
    } else {
      returnCutoff match {
        case Some((retLine, retColOpt)) =>
          val cutoffCol = retColOpt.getOrElse(Int.MaxValue)
          val withPos = assigns.flatMap { a =>
            a.line.map(line => (a, (line, a.column.getOrElse(0))))
          }
          if (withPos.isEmpty) {
            assigns
          } else {
            val notAfter = withPos.filter { case (_, (line, col)) =>
              line < retLine || (line == retLine && col <= cutoffCol)
            }
            val base = if (notAfter.nonEmpty) notAfter else withPos
            val best = base.map(_._2).maxBy { case (line, col) => (line, col) }
            base.collect { case (record, lc) if lc == best => record }
          }
        case None =>
          assigns
      }
    }
  }

  private def resolveAssignmentChainAll(
                                         varName: String,
                                         assignments: Vector[AssignmentRecord],
                                         returnCutoff: Option[(Int, Option[Int])],
                                         visited: Set[String],
                                         depth: Int,
                                         maxDepth: Int,
                                       ): Vector[vpr.Exp] = {
    if (depth >= maxDepth || visited.contains(varName)) {
      Vector.empty
    } else {
      val currentAssignments = selectAssignmentsForVar(varName, assignments, returnCutoff)
      if (currentAssignments.isEmpty) {
        Vector.empty
      } else {
        val nextVisited = visited + varName
        deduplicateExpByRender(currentAssignments.flatMap { assignment =>
          assignment.rhs match {
            case rhsLocal: vpr.AbstractLocalVar =>
              val deeper = resolveAssignmentChainAll(
                varName = rhsLocal.name,
                assignments = assignments,
                returnCutoff = returnCutoff,
                visited = nextVisited,
                depth = depth + 1,
                maxDepth = maxDepth,
              )
              if (deeper.nonEmpty) deeper else Vector(rhsLocal: vpr.Exp)
            case other =>
              Vector(other)
          }
        })
      }
    }
  }

  private def buildReverseStoreAliasIndex(
                                           symbolicStoreByLocal: Map[String, vpr.Exp]
                                         ): Map[String, Vector[String]] = {
    val buf = mutable.LinkedHashMap.empty[String, mutable.LinkedHashSet[String]]
    symbolicStoreByLocal.foreach { case (lhsName, rhsExp) =>
      rhsExp match {
        case rhsLocal: vpr.AbstractLocalVar =>
          val keys = Set(rhsLocal.name, stripVarSuffix(rhsLocal.name))
          keys.foreach { key =>
            val set = buf.getOrElseUpdate(key, mutable.LinkedHashSet.empty[String])
            set += lhsName
          }
        case _ =>
      }
    }
    buf.view.mapValues(_.toVector).toMap
  }

  private def lookupReverseAliases(
                                    localName: String,
                                    reverseAliasIndex: Map[String, Vector[String]]
                                  ): Vector[String] = {
    val keys = Vector(localName, stripVarSuffix(localName)).distinct
    keys.flatMap(key => reverseAliasIndex.getOrElse(key, Vector.empty)).distinct
  }

  private def deduplicateExpByRender(exps: Seq[vpr.Exp]): Vector[vpr.Exp] = {
    val seen = mutable.LinkedHashSet.empty[String]
    val ordered = mutable.ArrayBuffer.empty[vpr.Exp]
    exps.foreach { exp =>
      val key = safeRender(exp)
      if (!seen.contains(key)) {
        seen += key
        ordered += exp
      }
    }
    ordered.toVector
  }

  private def isIdentityReplacement(formalName: String, exp: vpr.Exp): Boolean =
    exp match {
      case lv: vpr.AbstractLocalVar =>
        stripVarSuffix(lv.name) == stripVarSuffix(formalName)
      case _ =>
        false
    }

  private def pruneFormalIdentityMappings(map: Map[String, vpr.Exp]): Map[String, vpr.Exp] =
    map.filterNot { case (formalName, exp) => isIdentityReplacement(formalName, exp) }

  private def normalizeSubstitutionMap(map: Map[String, vpr.Exp]): Map[String, vpr.Exp] =
    map.view.mapValues(decodeAndSimplify).toMap

  private def substitutionMapSignature(map: Map[String, vpr.Exp]): String =
    map.toVector.sortBy(_._1).map { case (k, v) => s"$k=${safeRender(v)}" }.mkString("|")

  private def cartesianProduct[A](axes: Vector[Vector[A]]): Vector[Vector[A]] =
    axes.foldLeft(Vector(Vector.empty[A])) { (acc, axis) =>
      for {
        prefix <- acc
        value <- axis
      } yield prefix :+ value
    }

  private def cartesianProductLimited[A](axes: Vector[Vector[A]], limit: Int): Vector[Vector[A]] = {
    if (limit <= 0) {
      Vector.empty
    } else if (axes.isEmpty) {
      Vector(Vector.empty[A])
    } else {
      val out = mutable.ArrayBuffer.empty[Vector[A]]
      val buffer = new Array[Any](axes.size)

      def dfs(depth: Int): Unit = {
        if (out.size >= limit) return
        if (depth == axes.size) {
          out += buffer.toVector.asInstanceOf[Vector[A]]
          return
        }
        val axis = axes(depth)
        var idx = 0
        while (idx < axis.size && out.size < limit) {
          buffer(depth) = axis(idx)
          dfs(depth + 1)
          idx += 1
        }
      }

      dfs(0)
      out.toVector
    }
  }

  private def addScore(
                        left: (Int, Int, Int, Int, String),
                        right: (Int, Int, Int, Int, String),
                      ): (Int, Int, Int, Int, String) =
    (
      left._1 + right._1,
      left._2 + right._2,
      left._3 + right._3,
      left._4 + right._4,
      s"${left._5}|${right._5}",
    )

  private def rankAndDeduplicateSubstitutionContexts(
                                                      contexts: Vector[ReturnSubstitutionContext],
                                                      scopeContext: Option[ScopeContext],
                                                    ): Vector[ReturnSubstitutionContext] = {
    val deduped = {
      val seen = mutable.LinkedHashSet.empty[String]
      contexts.foldLeft(Vector.empty[ReturnSubstitutionContext]) { (acc, ctx) =>
        val signature =
          s"${ctx.contextKind}##${substitutionMapSignature(ctx.primaryByLocalName)}##${substitutionMapSignature(ctx.sourceFallbackByLocalName)}##${substitutionMapSignature(ctx.aliasAssignmentsByLocal)}"
        if (seen.contains(signature)) acc
        else {
          seen += signature
          acc :+ ctx
        }
      }
    }

    deduped.sortBy { ctx =>
      val locals = (ctx.primaryByLocalName.values.toVector ++ ctx.sourceFallbackByLocalName.values.toVector)
        .flatMap(extractLocalNames)
        .map(stripVarSuffix)
        .distinct
      val outOfScopeCount = scopeContext match {
        case Some(sc) if sc.visibleIdentifiers.nonEmpty =>
          locals.count(name => !sc.visibleIdentifiers.contains(name))
        case _ =>
          0
      }
      val internalCount = locals.count(isInternalAliasName)
      val unresolvedCount = locals.count(name => name.contains("$") || name.contains("@"))
      val primaryMappingBias = -ctx.primaryByLocalName.size
      val sourceFallbackPenalty = if (ctx.sourceFallbackByLocalName.nonEmpty) 1 else 0
      val contextKindPriority = substitutionContextKindPriority(ctx.contextKind)
      (outOfScopeCount, internalCount, unresolvedCount, contextKindPriority, sourceFallbackPenalty, primaryMappingBias)
    }
  }

  private def substitutionContextKindPriority(contextKind: String): Int =
    contextKind match {
      case "post_return_primary" => 0
      case "non_post_return_primary" => 0
      case "post_return_fallback_only" => 1
      case "non_post_source_fallback" => 1
      case "non_post_identity" => 2
      case _ => 3
    }

  private def successSelectionSortKey(
                                       substitutionContext: ReturnSubstitutionContext,
                                       success: CandidateSuccess,
                                       scopeContext: Option[ScopeContext],
                                     ): (Int, Int, Int, Int, String) = {
    val contextPriority = substitutionContextKindPriority(substitutionContext.contextKind)
    val unresolvedTokenCount = success.annotationLines.count(line => findUnsupportedEncodingToken(line).nonEmpty)
    val outOfScopeCount = scopeContext match {
      case Some(sc) if sc.visibleIdentifiers.nonEmpty =>
        success.directives.count(d => !expressionIdentifiersInScope(d.gobraPredicateCall, sc.visibleIdentifiers))
      case _ =>
        0
    }
    val directiveCount = success.directives.size
    val signature = success.annotationLines.mkString("|")
    (contextPriority, unresolvedTokenCount, outOfScopeCount, directiveCount, signature)
  }

  private def extractLocalNames(exp: vpr.Exp): Vector[String] = {
    val names = mutable.ArrayBuffer.empty[String]
    def visit(node: vpr.Node): Unit = node match {
      case lv: vpr.AbstractLocalVar =>
        names += lv.name
      case other =>
        other.subnodes.foreach(visit)
    }
    visit(exp)
    names.toVector
  }

  private def isInternalAliasName(name: String): Boolean = {
    val stripped = stripVarSuffix(name)
    stripped.startsWith("fn$$") ||
      stripped.startsWith("$t") ||
      stripped.startsWith("$k") ||
      stripped.matches("^N\\d+$")
  }

  private def applyPrimaryReturnSubstitution(
                                              exp: vpr.Exp,
                                              substitutionContext: ReturnSubstitutionContext,
                                            ): vpr.Exp = {
    if (substitutionContext.primaryByLocalName.isEmpty) exp
    else {
      exp.transform(
        {
          case lv: vpr.AbstractLocalVar =>
            lookupSubstitution(lv.name, substitutionContext.primaryByLocalName).getOrElse(lv)
        }: PartialFunction[vpr.Node, vpr.Node],
        viper.silver.ast.utility.rewriter.Traverse.BottomUp,
      ).asInstanceOf[vpr.Exp]
    }
  }

  private def applySourceFallbackSubstitution(
                                               exp: vpr.Exp,
                                               substitutionContext: ReturnSubstitutionContext,
                                             ): vpr.Exp = {
    if (substitutionContext.sourceFallbackByLocalName.isEmpty) exp
    else {
      exp.transform(
        {
          case lv: vpr.AbstractLocalVar =>
            lookupSubstitution(lv.name, substitutionContext.sourceFallbackByLocalName).getOrElse(lv)
        }: PartialFunction[vpr.Node, vpr.Node],
        viper.silver.ast.utility.rewriter.Traverse.BottomUp,
      ).asInstanceOf[vpr.Exp]
    }
  }

  private def lookupSubstitution(
                                  name: String,
                                  substitutions: Map[String, vpr.Exp],
                                ): Option[vpr.Exp] = {
    val noAt = name.replaceAll("@\\d+", "")
    val strippedNoAt = stripVarSuffix(noAt)
    val stripped = stripVarSuffix(name)
    val directKeys = Vector(name, noAt, strippedNoAt, stripped).distinct
    directKeys.iterator.flatMap(substitutions.get).toVector.headOption.orElse {
      val normalizedName = stripVarSuffix(noAt)
      substitutions.iterator.collectFirst {
        case (key, value)
          if stripVarSuffix(key.replaceAll("@\\d+", "")) == normalizedName =>
          value
      }
    }
  }

  private def resolveDescriptor(predicateName: String, context: RenderContext): Either[RenderError, PredicateDescriptor] = {
    context.dynamicPredicates.get(predicateName)
      .orElse(context.methodPredicates.get(predicateName))
      .orElse(context.functionPredicates.get(predicateName))
      .toRight(
        RenderError(
          reason = s"No Gobra-level predicate mapping found for '$predicateName'.",
          stage = "resolvePredicate",
          predicateName = Some(predicateName),
        )
      )
  }

  private def renderPredicateCallFromArgs(
                                           descriptor: PredicateDescriptor,
                                           renderedArgs: Vector[String],
                                           renderedArgsExp: Option[Vector[vpr.Exp]],
                                         fileContext: FileRenderContext,
                                         renderEnvironment: RenderEnvironment,
                                       ): Either[RenderError, String] = {
    descriptor.kind match {
      case MethodPredicateKind =>
        if (renderedArgs.isEmpty) {
          Left(
            RenderError(
              reason = s"Method predicate '${descriptor.silverName}' has no receiver argument.",
              stage = "renderPredicateCall",
              predicateName = Some(descriptor.silverName),
            )
          )
        } else {
          val recv =
            if (descriptor.silverName.startsWith(Names.dynamicPredicate)) {
              renderedArgsExp
                .flatMap(_.headOption)
                .map(decodeDynamicReceiverExp)
                .map(translateExpToGobraExpr)
                .getOrElse(renderedArgs.head)
            } else renderedArgs.head
          val callArgs = renderedArgs.tail
          val call = if (callArgs.nonEmpty) s"$recv.${descriptor.gobraName}(${callArgs.mkString(", ")})" else s"$recv.${descriptor.gobraName}()"
          Right(call)
        }

      case FunctionPredicateKind =>
        qualifyFunctionPredicate(descriptor, fileContext, renderEnvironment).map { qualifiedName =>
          val addressedArgs = restoreAddressOfForFunctionPredicate(descriptor, renderedArgs, renderedArgsExp)
          s"$qualifiedName(${addressedArgs.mkString(", ")})"
        }
    }
  }

  private def restoreAddressOfForFunctionPredicate(
                                                    descriptor: PredicateDescriptor,
                                                    args: Vector[String],
                                                    argsExp: Option[Vector[vpr.Exp]],
                                                  ): Vector[String] = {
    if (descriptor.pointerArgIndices.isEmpty || args.isEmpty) args
    else {
      args.zipWithIndex.map { case (arg, idx) =>
        val alreadyAddressed = arg.trim.startsWith("&")
        val pointerFormal = descriptor.pointerArgIndices.contains(idx)
        val needsAddress = argsExp.exists { exps =>
          exps.lift(idx).exists(shouldPrefixAddressOfArg)
        }
        if (!alreadyAddressed && pointerFormal && needsAddress) s"&$arg" else arg
      }
    }
  }

  private def shouldPrefixAddressOfArg(exp: vpr.Exp): Boolean =
    exp match {
      case dfa: vpr.DomainFuncApp if dfa.funcname.startsWith("ShStructget") || dfa.funcname.startsWith("ShStructrev") =>
        exp.typ != vpr.Ref
      case _: vpr.FieldAccess =>
        exp.typ != vpr.Ref
      case _ =>
        false
    }

  private final case class ExpNormalizationOutcome(
                                                    exp: vpr.Exp,
                                                    notes: Vector[String],
                                                  )

  private final case class AliasResolutionOutcome(
                                                   resolved: vpr.Exp,
                                                   notes: Vector[String],
                                                 )

  private final case class ReverseAliasSelectionOutcome(
                                                         selectedPostAliasExp: vpr.Exp,
                                                         rendered: String,
                                                         score: (Int, Int, Int, Int, String),
                                                         rank: Int,
                                                         notes: Vector[String],
                                                       )

  private final case class TypedStoreSubstitutionOutcome(
                                                          exp: vpr.Exp,
                                                          notes: Vector[String],
                                                        )

  private final case class LocalVarTypedKey(
                                             name: String,
                                             typRepr: String,
                                           )

  private val TupleProjectionNamePattern: Regex = "^get\\d+of\\d+$".r

  private def aliasAssignmentsForContext(
                                          substitutionContext: ReturnSubstitutionContext
                                        ): Map[String, vpr.Exp] = {
    if (!substitutionContext.contextKind.startsWith("post_return")) {
      substitutionContext.aliasAssignmentsByLocal
    } else {
      substitutionContext.aliasAssignmentsByLocal.filter {
        case (lhs, rhs) =>
          isInternalAliasName(lhs) || !isInternalLocalAliasExp(rhs)
      }
    }
  }

  private def applyTypedStoreTupleProjectionSubstitution(
                                                          exp: vpr.Exp,
                                                          symbolicStoreEntries: Vector[TryFoldFailureContextExtractor.StoreBindingEntry],
                                                        ): TypedStoreSubstitutionOutcome = {
    if (symbolicStoreEntries.isEmpty) {
      TypedStoreSubstitutionOutcome(exp = exp, notes = Vector("typedAlias.entries=0"))
    } else {
      val tupleProjectionLocals = collectTupleProjectionLocalVars(exp)
      if (tupleProjectionLocals.isEmpty) {
        TypedStoreSubstitutionOutcome(exp = exp, notes = Vector("typedAlias.occurrences=0"))
      } else {
        val notes = mutable.ArrayBuffer.empty[String]
        val replacements = mutable.LinkedHashMap.empty[LocalVarTypedKey, vpr.Exp]

        tupleProjectionLocals.foreach { localVar =>
          val key = LocalVarTypedKey(localVar.name, safeRender(localVar.typ))
          if (!replacements.contains(key)) {
            val matchedEntries = symbolicStoreEntries.filter { entry =>
              entry.name == localVar.name && areTypesCompatible(entry.typ, localVar.typ, entry.typRepr)
            }
            val uniqueMatchedExps = deduplicateExpByRender(matchedEntries.map(_.exp))
            notes += s"typedAlias.key=${key.name}:${key.typRepr}"
            notes += s"typedAlias.candidates=${uniqueMatchedExps.size}"
            uniqueMatchedExps match {
              case Vector(single) if safeRender(single) != safeRender(localVar) =>
                replacements += key -> single
                notes += s"typedAlias.applied=${safeRender(single)}"
              case Vector(single) =>
                notes += s"typedAlias.skipped=identity:${safeRender(single)}"
              case Vector() =>
                notes += "typedAlias.skipped=no_match"
              case _ =>
                notes += "typedAlias.skipped=ambiguous"
            }
          }
        }

        if (replacements.isEmpty) {
          TypedStoreSubstitutionOutcome(exp = exp, notes = notes.toVector)
        } else {
          val substituted = replaceLocalVarsByTypedKey(exp, replacements.toMap)
          TypedStoreSubstitutionOutcome(exp = substituted, notes = notes.toVector)
        }
      }
    }
  }

  private def collectTupleProjectionLocalVars(exp: vpr.Exp): Vector[vpr.AbstractLocalVar] = {
    val occurrences = mutable.ArrayBuffer.empty[vpr.AbstractLocalVar]
    def visit(node: vpr.Node): Unit = node match {
      case dfa: vpr.DomainFuncApp if isTupleProjectionCall(dfa.funcname) && dfa.args.size == 1 =>
        dfa.args.head match {
          case lv: vpr.AbstractLocalVar => occurrences += lv
          case other => visit(other)
        }
      case fa: vpr.FuncApp if isTupleProjectionCall(fa.funcname) && fa.args.size == 1 =>
        fa.args.head match {
          case lv: vpr.AbstractLocalVar => occurrences += lv
          case other => visit(other)
        }
      case other =>
        other.subnodes.foreach(visit)
    }
    visit(exp)
    occurrences.toVector
  }

  private def replaceLocalVarsByTypedKey(
                                          exp: vpr.Exp,
                                          replacements: Map[LocalVarTypedKey, vpr.Exp],
                                        ): vpr.Exp =
    if (replacements.isEmpty) exp
    else {
      exp.transform(
        {
          case lv: vpr.AbstractLocalVar
            if replacements.contains(LocalVarTypedKey(lv.name, safeRender(lv.typ))) =>
            replacements(LocalVarTypedKey(lv.name, safeRender(lv.typ)))
        }: PartialFunction[vpr.Node, vpr.Node],
        viper.silver.ast.utility.rewriter.Traverse.BottomUp,
      ).asInstanceOf[vpr.Exp]
    }

  private def areTypesCompatible(
                                  entryType: vpr.Type,
                                  targetType: vpr.Type,
                                  entryTypeRepr: String,
                                ): Boolean =
    entryType == targetType || entryTypeRepr == safeRender(targetType)

  private def preferredAvoidedLocalNames(
                                          substitutionContext: ReturnSubstitutionContext
                                        ): Set[String] =
    substitutionContext.primaryByLocalName.flatMap {
      case (key, lv: vpr.AbstractLocalVar) =>
        val lhs = stripVarSuffix(key)
        val rhs = stripVarSuffix(lv.name)
        if (lhs.nonEmpty && rhs.nonEmpty && lhs != rhs) Some(lhs) else None
      case _ =>
        None
    }.toSet

  private def selectPostAliasExpressions(
                                          aliasedExp: vpr.Exp,
                                          reverseAliasIndex: Map[String, Vector[String]],
                                          substitutionContext: ReturnSubstitutionContext,
                                          scopeContext: Option[ScopeContext],
                                          topK: Int,
                                        ): Vector[ReverseAliasSelectionOutcome] = {
    val alternatives = expandReverseAliasAlternatives(aliasedExp, reverseAliasIndex)
    val avoidedNames = preferredAvoidedLocalNames(substitutionContext)

    final case class EvaluatedAlternative(
                                           postAliasExp: vpr.Exp,
                                           rendered: String,
                                           score: (Int, Int, Int, Int, String),
                                         )

    def evaluate(candidate: vpr.Exp): EvaluatedAlternative = {
      val withPrimary = applyPrimaryReturnSubstitution(candidate, substitutionContext)
      val withFallback = applySourceFallbackSubstitution(withPrimary, substitutionContext)
      val normalized = normalizeAndSimplify(withFallback).exp
      val rendered = translateExpToGobraExpr(normalized)
      val localNames = extractLocalNames(normalized).map(stripVarSuffix).filter(_.nonEmpty)
      val outOfScopeCount = scopeContext match {
        case Some(sc) if sc.visibleIdentifiers.nonEmpty =>
          localNames.count(name => !sc.visibleIdentifiers.contains(name))
        case _ =>
          0
      }
      val internalAliasCount = localNames.count(isInternalAliasName)
      val avoidedNameCount = localNames.count(avoidedNames.contains)
      val unresolvedEncodingPenalty = if (findUnsupportedEncodingToken(rendered).nonEmpty) 1 else 0
      EvaluatedAlternative(
        postAliasExp = withFallback,
        rendered = rendered,
        score = (unresolvedEncodingPenalty, outOfScopeCount, internalAliasCount, avoidedNameCount, rendered),
      )
    }

    val evaluated = alternatives.map(evaluate).sortBy(_.score)
    val selected = evaluated
      .foldLeft(Vector.empty[EvaluatedAlternative]) { (acc, next) =>
        if (acc.exists(existing => existing.rendered == next.rendered)) acc else acc :+ next
      }
      .take(math.max(1, topK))

    selected.zipWithIndex.map { case (entry, idx) =>
      val notes =
        if (evaluated.size <= 1) Vector("reverseAlias.alternatives=1")
        else Vector(
          s"reverseAlias.alternatives=${evaluated.size}",
          s"reverseAlias.selectedRank=${idx + 1}",
          s"reverseAlias.selectedScore=${entry.score}",
          s"reverseAlias.selectedRendered=${entry.rendered}",
        )
      ReverseAliasSelectionOutcome(
        selectedPostAliasExp = entry.postAliasExp,
        rendered = entry.rendered,
        score = entry.score,
        rank = idx,
        notes = notes,
      )
    }
  }

  private def expandReverseAliasAlternatives(
                                              exp: vpr.Exp,
                                              reverseAliasIndex: Map[String, Vector[String]],
                                            ): Vector[vpr.Exp] = {
    val localOccurrences = collectLocalVarOccurrences(exp)
      .groupBy(_.name)
      .values
      .flatMap(_.headOption)
      .toVector
      .sortBy(_.name)

    val replacementAxes: Vector[(String, Vector[vpr.Exp])] = localOccurrences.flatMap { occ =>
      if (!isInternalAliasName(occ.name)) {
        None
      } else {
        val aliases = lookupReverseAliases(occ.name, reverseAliasIndex)
          .filterNot(_ == occ.name)
          .filter(_.nonEmpty)
          .distinct
        if (aliases.isEmpty) None
        else {
          val choices = deduplicateExpByRender(
            Vector(occ: vpr.Exp) ++ aliases.map(name => vpr.LocalVar(name, occ.typ)(): vpr.Exp)
          )
          Some(occ.name -> choices)
        }
      }
    }

    if (replacementAxes.isEmpty) {
      Vector(exp)
    } else {
      val maxAlternatives = 48
      val replacementNames = replacementAxes.map(_._1)
      val replacementChoices = replacementAxes.map(_._2)
      val combinations = cartesianProduct(replacementChoices)
      val replaced = combinations.iterator.map { combo =>
        val replacementMap = replacementNames.zip(combo).toMap
        replaceLocalVarsInExp(exp, replacementMap)
      }.toVector
      deduplicateExpByRender(Vector(exp) ++ replaced)
        .take(maxAlternatives)
        .map(decodeAndSimplify)
    }
  }

  private def collectLocalVarOccurrences(exp: vpr.Exp): Vector[vpr.AbstractLocalVar] = {
    val occurrences = mutable.ArrayBuffer.empty[vpr.AbstractLocalVar]
    def visit(node: vpr.Node): Unit = node match {
      case lv: vpr.AbstractLocalVar =>
        occurrences += lv
      case other =>
        other.subnodes.foreach(visit)
    }
    visit(exp)
    occurrences.toVector
  }

  private def replaceLocalVarsInExp(
                                     exp: vpr.Exp,
                                     replacements: Map[String, vpr.Exp],
                                   ): vpr.Exp =
    if (replacements.isEmpty) exp
    else {
      exp.transform(
        {
          case lv: vpr.AbstractLocalVar if replacements.contains(lv.name) =>
            replacements(lv.name)
        }: PartialFunction[vpr.Node, vpr.Node],
        viper.silver.ast.utility.rewriter.Traverse.BottomUp,
      ).asInstanceOf[vpr.Exp]
    }

  private def isInternalLocalAliasExp(exp: vpr.Exp): Boolean =
    exp match {
      case lv: vpr.AbstractLocalVar =>
        isInternalAliasName(lv.name)
      case _ =>
        false
    }

  private def decodeAndSimplify(exp: vpr.Exp): vpr.Exp = {
    val decoded = TryFoldExpNormalizer.normalize(exp).normalized
    try Simplifier.simplify(decoded)
    catch {
      case _: Throwable => decoded
    }
  }

  private def normalizeAndSimplify(exp: vpr.Exp): ExpNormalizationOutcome = {
    val normalized = TryFoldExpNormalizer.normalize(exp)
    val simplified = try Simplifier.simplify(normalized.normalized)
    catch {
      case _: Throwable => normalized.normalized
    }
    val notes = normalized.steps.map { step =>
      s"${step.pass}: ${step.before} => ${step.after}"
    } ++ Vector(
      s"normalizer.iterations=${normalized.iterations}",
      s"normalizer.converged=${normalized.converged}",
    )
    ExpNormalizationOutcome(
      exp = simplified,
      notes = notes,
    )
  }

  private def resolveAliases(
                              exp: vpr.Exp,
                              assignmentsByLocal: Map[String, vpr.Exp],
                            ): AliasResolutionOutcome = {
    val outcome = TryFoldAliasResolver.resolve(
      exp = exp,
      assignmentsByLocal = assignmentsByLocal,
      maxIterations = 24,
    )
    val notes = outcome.steps.map { step =>
      s"alias.iter${step.iteration}: ${step.before} => ${step.afterSubstitution} => ${step.afterNormalization}"
    } ++ Vector(
      s"alias.terminatedBy=${outcome.terminatedBy}",
      s"alias.iterations=${outcome.iterations}",
    )
    AliasResolutionOutcome(
      resolved = outcome.resolved,
      notes = notes,
    )
  }

  private def translateExpToGobraExpr(exp: vpr.Exp): String =
    exp match {
      case vpr.IntLit(n) => n.toString
      case vpr.BoolLit(v) => v.toString
      case vpr.NullLit() => "nil"
      case local: vpr.AbstractLocalVar =>
        stripVarSuffix(local.name)
      case fa: vpr.FuncApp if fa.funcname == "slen" && fa.args.size == 1 =>
        s"len(${translateExpToGobraExpr(fa.args.head)})"
      case fa: vpr.FuncApp if fa.funcname == "sadd" && fa.args.size == 2 =>
        s"${translateExpToGobraExpr(fa.args.head)} + ${translateExpToGobraExpr(fa.args(1))}"
      case fa: vpr.FuncApp if canonicalCallName(fa.funcname).startsWith("box_Poly") && fa.args.size == 1 =>
        translateExpToGobraExpr(fa.args.head)
      case fa: vpr.FuncApp if canonicalCallName(fa.funcname).startsWith("unbox_Poly") && fa.args.size == 1 =>
        translateExpToGobraExpr(fa.args.head)
      case dfa: vpr.DomainFuncApp if dfa.funcname == "ShArrayloc" && dfa.args.size == 2 =>
        s"${translateExpToGobraExpr(dfa.args.head)}[${translateExpToGobraExpr(dfa.args(1))}]"
      case dfa: vpr.DomainFuncApp if dfa.funcname.startsWith("ShStructget") && dfa.args.size == 1 =>
        tryRenderSelectorChain(dfa).getOrElse {
          extractGoFieldName(dfa) match {
            case Some(field) => s"${translateExpToGobraExpr(dfa.args.head)}.$field"
            case None => s"${translateExpToGobraExpr(dfa.args.head)}.${dfa.funcname}"
          }
        }
      case dfa: vpr.DomainFuncApp if dfa.funcname == "sarray" && dfa.args.size == 1 =>
        translateExpToGobraExpr(dfa.args.head)
      case dfa: vpr.DomainFuncApp if dfa.funcname == "slen" && dfa.args.size == 1 =>
        s"len(${translateExpToGobraExpr(dfa.args.head)})"
      case dfa: vpr.DomainFuncApp if dfa.funcname == "soffset" && dfa.args.size == 1 =>
        s"soffset(${translateExpToGobraExpr(dfa.args.head)})"
      case dfa: vpr.DomainFuncApp if dfa.funcname == "scap" && dfa.args.size == 1 =>
        s"cap(${translateExpToGobraExpr(dfa.args.head)})"
      case dfa: vpr.DomainFuncApp if dfa.funcname == "ShArraylen" && dfa.args.size == 1 =>
        s"len(${translateExpToGobraExpr(dfa.args.head)})"
      case dfa: vpr.DomainFuncApp if canonicalCallName(dfa.funcname).startsWith("box_Poly") && dfa.args.size == 1 =>
        translateExpToGobraExpr(dfa.args.head)
      case dfa: vpr.DomainFuncApp if canonicalCallName(dfa.funcname).startsWith("unbox_Poly") && dfa.args.size == 1 =>
        translateExpToGobraExpr(dfa.args.head)
      case dfa: vpr.DomainFuncApp if dfa.funcname.startsWith("get") && dfa.args.nonEmpty =>
        safeRender(dfa).trim
      case dfa: vpr.DomainFuncApp =>
        val args = dfa.args.map(translateExpToGobraExpr).mkString(", ")
        s"${dfa.funcname}($args)"
      case fa: vpr.FieldAccess =>
        tryRenderSelectorChain(fa).getOrElse {
          extractGoFieldName(fa) match {
            case Some(fieldName) =>
              s"${translateExpToGobraExpr(fa.rcv)}.$fieldName"
            case None =>
              if (fa.field.name.contains("$$$")) translateExpToGobraExpr(fa.rcv)
              else s"${translateExpToGobraExpr(fa.rcv)}.${fa.field.name}"
          }
        }
      case vpr.Add(l, r) => s"${translateExpToGobraExpr(l)} + ${translateExpToGobraExpr(r)}"
      case vpr.Sub(l, r) => s"${translateExpToGobraExpr(l)} - ${translateExpToGobraExpr(r)}"
      case vpr.Mul(l, r) => s"${translateExpToGobraExpr(l)} * ${translateExpToGobraExpr(r)}"
      case other => safeRender(other).trim
    }

  private final case class SelectorStep(
                                         fieldName: String,
                                         sourceKey: Option[String],
                                       )

  private def tryRenderSelectorChain(exp: vpr.Exp): Option[String] =
    decomposeSelectorChain(exp).map { case (base, rawSteps) =>
      val steps = collapseDuplicateSelectorSteps(rawSteps)
      val renderedBase = translateExpToGobraExpr(base)
      steps.foldLeft(renderedBase) { case (acc, step) => s"$acc.${step.fieldName}" }
    }

  private def decomposeSelectorChain(exp: vpr.Exp): Option[(vpr.Exp, Vector[SelectorStep])] =
    exp match {
      case fa: vpr.FieldAccess =>
        extractGoFieldName(fa).map { fieldName =>
          val step = SelectorStep(fieldName, sourceLocationKey(fa))
          decomposeSelectorChain(fa.rcv) match {
            case Some((base, steps)) => (base, steps :+ step)
            case None => (fa.rcv, Vector(step))
          }
        }
      case dfa: vpr.DomainFuncApp if dfa.funcname.startsWith("ShStructget") && dfa.args.size == 1 =>
        extractGoFieldName(dfa).map { fieldName =>
          val step = SelectorStep(fieldName, sourceLocationKey(dfa))
          decomposeSelectorChain(dfa.args.head) match {
            case Some((base, steps)) => (base, steps :+ step)
            case None => (dfa.args.head, Vector(step))
          }
        }
      case _ =>
        None
    }

  private def collapseDuplicateSelectorSteps(steps: Vector[SelectorStep]): Vector[SelectorStep] =
    steps.foldLeft(Vector.empty[SelectorStep]) { (acc, current) =>
      acc.lastOption match {
        case Some(prev)
          if prev.fieldName == current.fieldName && prev.sourceKey.nonEmpty && prev.sourceKey == current.sourceKey =>
          acc
        case _ =>
          acc :+ current
      }
    }

  private def sourceLocationKey(node: vpr.Node): Option[String] =
    try {
      Source.unapply(node).map(info => safeRender(info.origin.pos))
    } catch {
      case _: Throwable => None
    }

  private def extractGoFieldName(node: vpr.Node): Option[String] =
    try {
      Source.unapply(node).flatMap { info =>
        info.pnode match {
          case dot: fe.PDot => Some(dot.id.name)
          case fd: fe.PFieldDecl => Some(fd.id.name)
          case ed: fe.PEmbeddedDecl => Some(ed.id.name)
          case _ => None
        }
      }
    } catch {
      case _: Throwable => None
    }

  private val VarVersionSuffixPattern: Regex = "^([A-Za-z_][A-Za-z0-9_]*)_V\\d+(?:_CN\\d+)?$".r
  private def stripVarSuffix(name: String): String =
    name.replaceAll("@\\d+", "") match {
      case VarVersionSuffixPattern(base) => base
      case other => other
    }

  private def safeRender(value: Any): String =
    try {
      String.valueOf(value)
    } catch {
      case throwable: Throwable => s"<rendering failed: ${throwable.getClass.getSimpleName}>"
    }

  private def buildContext(
                            rootProgram: in.Program,
                            translationMetadata: Option[TryFoldTranslationMetadata],
                          ): RenderContext = {
    val methodMap = buildMethodPredicateMap(rootProgram)
    val functionMap = buildFunctionPredicateMap(rootProgram)
    val dynamicMapFromMetadata = buildDynamicPredicateMapFromMetadata(translationMetadata)
    val dynamicMap =
      if (dynamicMapFromMetadata.nonEmpty) dynamicMapFromMetadata
      else safeBuildDynamicPredicateMap(rootProgram)

    RenderContext(
      methodPredicates = methodMap,
      functionPredicates = functionMap,
      dynamicPredicates = dynamicMap,
    )
  }

  private def buildMethodPredicateMap(rootProgram: in.Program): Map[String, PredicateDescriptor] =
    rootProgram.table.getMPredicates.map(_.name).map { proxy =>
      proxy.uniqueName -> PredicateDescriptor(
        silverName = proxy.uniqueName,
        gobraName = proxy.name,
        kind = MethodPredicateKind,
        source = "lookupTable.methodPredicate",
      )
    }.toMap

  private def buildFunctionPredicateMap(rootProgram: in.Program): Map[String, PredicateDescriptor] =
    {
      val packageNameCache = mutable.Map.empty[String, Option[String]]
      def packageNameFromDeclFile(path: String): Option[String] =
        packageNameCache.getOrElseUpdate(path, {
          val p = Paths.get(path)
          if (!p.toFile.exists()) None
          else parsePackageName(readLines(p))
        })

      def packageNameForProxy(proxy: in.FPredicateProxy): Option[String] =
        try {
          rootProgram.table.lookup(proxy).info match {
            case ReportSource.Parser.Single(_, origin) =>
              val normalized = normalizePathString(origin.pos.file.toString)
              packageNameFromDeclFile(normalized)
            case _ =>
              None
          }
        } catch {
          case _: Throwable => None
        }

      def pointerArgIndicesForProxy(proxy: in.FPredicateProxy): Set[Int] =
        try {
          rootProgram.table.lookup(proxy) match {
            case fp: in.FPredicate =>
              fp.args.zipWithIndex.collect {
                case (arg, idx) if arg.typ.isInstanceOf[in.PointerT] => idx
              }.toSet
            case builtIn: in.BuiltInFPredicate =>
              builtIn.argsT.zipWithIndex.collect {
                case (argT, idx) if argT.isInstanceOf[in.PointerT] => idx
              }.toSet
            case _ =>
              Set.empty
          }
        } catch {
          case _: Throwable => Set.empty
        }

    rootProgram.table.getFPredicates.map(_.name).map { proxy =>
      val (sourceName, packageViperId) = demangleFunctionPredicateName(proxy.name)
      proxy.name -> PredicateDescriptor(
        silverName = proxy.name,
        gobraName = sourceName,
        kind = FunctionPredicateKind,
        source = "lookupTable.functionPredicate",
        packageViperId = packageViperId,
        packageName = packageNameForProxy(proxy),
        pointerArgIndices = pointerArgIndicesForProxy(proxy),
      )
    }.toMap
    }

  private def buildDynamicPredicateMapFromMetadata(
                                                    translationMetadata: Option[TryFoldTranslationMetadata]
                                                  ): Map[String, PredicateDescriptor] =
    translationMetadata.toVector.flatMap(_.dynamicPredicateMap).map { case (silverName, gobraName) =>
      silverName -> PredicateDescriptor(
        silverName = silverName,
        gobraName = gobraName,
        kind = MethodPredicateKind,
        source = "translationTimeDynamicPredicateFamily",
      )
    }.toMap

  private def safeBuildDynamicPredicateMap(rootProgram: in.Program): Map[String, PredicateDescriptor] =
    try {
      buildDynamicPredicateMap(rootProgram)
    } catch {
      case _: Throwable => Map.empty
    }

  private def buildDynamicPredicateMap(rootProgram: in.Program): Map[String, PredicateDescriptor] = {
    val table = rootProgram.table

    val itfNodes: Vector[(in.MPredicateProxy, in.InterfaceT, SortedSet[in.Type])] =
      table.getImplementations.toVector.flatMap { case (itf, impls) =>
        table.lookupMembers(itf)
          .collect { case m: in.MPredicateProxy => m }
          .toVector
          .map(proxy => (proxy, itf, impls))
      }

    val edges: Vector[(in.PredicateProxy, in.PredicateProxy)] =
      itfNodes.flatMap { case (itfProxy, itf, impls) =>
        impls.toVector.flatMap { impl =>
          table.lookupImplementationPredicate(impl, itf, itfProxy.name).toVector.map { implProxy =>
            (itfProxy: in.PredicateProxy, implProxy)
          }
        }
      }

    val nodes = itfNodes.map(_._1: in.PredicateProxy) ++ edges.map(_._2)
    val graphEdges = edges.flatMap { case (l, r) => Set((l, r), (r, l)) }

    val nodeIds = if (nodes.nonEmpty) {
      Algorithms.connected(nodes, graphEdges.toSet)._1
    } else Map.empty[in.PredicateProxy, Int]

    val signatures = itfNodes.map {
      case (itfProxy, _, _) =>
        nodeIds.get(itfProxy).map { id =>
          id -> itfProxy.name
        }
    }.flatten.toMap

    signatures.map { case (id, sigName) =>
      val silverName = s"${Names.dynamicPredicate}_$id"
      silverName -> PredicateDescriptor(
        silverName = silverName,
        gobraName = sigName,
        kind = MethodPredicateKind,
        source = "interfaceDynamicPredicateFamily",
      )
    }
  }

  private val DesugarSuffixPattern: Regex = "^(.+?)_[0-9a-f]{6,}_(?:F|M[A-Za-z0-9_]*|S[A-Za-z0-9_]*|P?M[A-Za-z0-9_]*)$".r
  private val FunctionPredicateWithHashPattern: Regex = "^(.+?)_([0-9a-f]{6,})_F$".r

  private def demanglePredicateName(name: String): String =
    name match {
      case DesugarSuffixPattern(base) => base
      case other => other
    }

  private def demangleFunctionPredicateName(name: String): (String, Option[String]) =
    name match {
      case FunctionPredicateWithHashPattern(base, hash) => (base, Some(hash))
      case _ => (demanglePredicateName(name), None)
    }

  private def decodeDynamicReceiverExp(exp: vpr.Exp): vpr.Exp =
    exp match {
      case fa: vpr.FuncApp if isTupleConstructor(fa.funcname) && fa.args.nonEmpty =>
        decodeAndSimplify(fa.args.head)
      case dfa: vpr.DomainFuncApp if isTupleConstructor(dfa.funcname) && dfa.args.nonEmpty =>
        decodeAndSimplify(dfa.args.head)
      case other =>
        decodeAndSimplify(other)
    }

  private def qualifyFunctionPredicate(
                                        descriptor: PredicateDescriptor,
                                        fileContext: FileRenderContext,
                                        renderEnvironment: RenderEnvironment,
                                      ): Either[RenderError, String] = {
    val packageNameOpt = descriptor.packageName.orElse(descriptor.packageViperId.flatMap(renderEnvironment.packageNameByViperId.get))
    packageNameOpt match {
      case None =>
        Right(descriptor.gobraName)

      case Some(pkgName) =>
        if (fileContext.packageName.contains(pkgName)) {
          Right(descriptor.gobraName)
        } else {
          fileContext.importAliasByPackageName.get(pkgName) match {
            case Some("_") =>
              Left(
                RenderError(
                  reason = s"Package '$pkgName' is imported with blank identifier '_' in target file; cannot qualify predicate '${descriptor.silverName}'.",
                  stage = "resolveQualifier",
                  predicateName = Some(descriptor.silverName),
                )
              )
            case Some(".") =>
              Right(descriptor.gobraName)
            case Some(alias) =>
              Right(s"$alias.${descriptor.gobraName}")
            case None =>
              Left(
                RenderError(
                  reason = s"Could not find import alias for package '$pkgName' while rendering predicate '${descriptor.silverName}'.",
                  stage = "resolveQualifier",
                  predicateName = Some(descriptor.silverName),
                )
              )
          }
        }
    }
  }

  private def buildFileRenderContext(sourceFile: String): FileRenderContext = {
    val path = Paths.get(sourceFile)
    if (!path.toFile.exists()) {
      FileRenderContext(
        targetFile = Some(sourceFile),
        packageName = None,
        importAliasByPackageName = Map.empty,
        sourceLines = Vector.empty,
      )
    } else {
      val lines = readLines(path)
      FileRenderContext(
        targetFile = Some(sourceFile),
        packageName = parsePackageName(lines),
        importAliasByPackageName = parseImportAliases(lines),
        sourceLines = lines,
      )
    }
  }

  private def readLines(path: Path): Vector[String] = {
    val src = IoSource.fromFile(path.toFile, "UTF-8")
    try src.getLines().toVector
    finally src.close()
  }

  private val PackageDeclPattern: Regex = "^\\s*package\\s+([A-Za-z_][A-Za-z0-9_]*)\\b.*$".r
  private val ImportSpecPattern: Regex = "^\\s*(?:(\\.|_|[A-Za-z_][A-Za-z0-9_]*)\\s+)?\"([^\"]+)\".*$".r

  private def parsePackageName(lines: Vector[String]): Option[String] =
    lines.collectFirst {
      case PackageDeclPattern(name) => name
    }

  private def parseImportAliases(lines: Vector[String]): Map[String, String] = {
    val specs = Vector.newBuilder[(String, String)]
    var inImportBlock = false

    lines.foreach { rawLine =>
      val line = rawLine.trim

      if (inImportBlock) {
        if (line.startsWith(")")) {
          inImportBlock = false
        } else {
          parseImportSpecLine(line).foreach(specs += _)
        }
      } else if (line.startsWith("import")) {
        val rest = line.stripPrefix("import").trim
        if (rest.startsWith("(")) {
          inImportBlock = true
        } else {
          parseImportSpecLine(rest).foreach(specs += _)
        }
      }

      parseGhostImportSpecLine(line).foreach(specs += _)
    }

    val grouped = specs.result().groupBy(_._1).view.mapValues(_.map(_._2).distinct).toMap
    grouped.flatMap { case (pkgName, aliases) =>
      aliases.filterNot(_ == "_") match {
        case Vector() => None
        case Vector(single) => Some(pkgName -> single)
        case many if many.distinct.size == 1 => Some(pkgName -> many.head)
        case _ => None
      }
    }
  }

  private def parseImportSpecLine(value: String): Option[(String, String)] =
    value match {
      case ImportSpecPattern(aliasRaw, importPath) =>
        val pkgName = packageNameFromImportPath(importPath)
        val alias = Option(aliasRaw).getOrElse(pkgName)
        Some(pkgName -> alias)
      case _ =>
        None
    }

  private def parseGhostImportSpecLine(value: String): Option[(String, String)] = {
    val normalized = if (value.startsWith("//@")) value.stripPrefix("//@").trim
    else if (value.startsWith("// @")) value.stripPrefix("// @").trim
    else return None
    parseImportSpecLine(normalized)
  }

  private def packageNameFromImportPath(path: String): String =
    path.split('/').lastOption.getOrElse(path)

  private def normalizePathString(path: String): String =
    Paths.get(path).toAbsolutePath.normalize.toString

  private val ScopeBuiltinIdentifiers: Set[String] = Set(
    "nil", "true", "false", "len", "cap", "append", "copy", "make", "new",
    "acc", "perm", "old", "result",
  )
  private val ScopeKeywordIdentifiers: Set[String] = Set(
    "func", "var", "const", "type", "return", "if", "else", "for", "range", "switch", "case", "default",
    "go", "defer", "break", "continue", "fallthrough", "select", "package", "import", "map", "chan", "struct",
    "interface", "assert", "assume", "fold", "unfold",
  )
  private val ScopeTokenPattern: Regex = "[$A-Za-z_][A-Za-z0-9_$]*(?:@\\d+)*".r

  private def buildScopeContext(fileContext: FileRenderContext, insertionLine: Option[Int]): ScopeContext = {
    val imports = fileContext.importAliasByPackageName.values.filter(alias => alias.nonEmpty && alias != "_" && alias != ".").toSet
    val fromFunction = insertionLine.toVector.flatMap(line => collectFunctionScopeIdentifiers(fileContext.sourceLines, line)).toSet
    ScopeContext(visibleIdentifiers = imports ++ ScopeBuiltinIdentifiers ++ fromFunction)
  }

  private def collectFunctionScopeIdentifiers(lines: Vector[String], insertionLine: Int): Set[String] = {
    if (lines.isEmpty || insertionLine <= 0) return Set.empty
    findEnclosingFunction(lines, insertionLine) match {
      case None => Set.empty
      case Some((signatureStartLine, bodyStartLine)) =>
        val cappedInsertion = math.min(insertionLine, lines.size)
        val signatureText = lines.slice(signatureStartLine - 1, bodyStartLine).mkString(" ")
        val signatureIds = extractScopeIdentifiersFromText(signatureText)
        val bodyIds = extractScopeIdentifiersFromBody(lines, bodyStartLine + 1, math.max(bodyStartLine + 1, cappedInsertion - 1))
        signatureIds ++ bodyIds
    }
  }

  private def findEnclosingFunction(lines: Vector[String], insertionLine: Int): Option[(Int, Int)] = {
    val cappedInsertion = math.min(insertionLine, lines.size)
    var result: Option[(Int, Int)] = None
    var line = 1
    while (line <= cappedInsertion) {
      val raw = lines(line - 1)
      if (raw.trim.startsWith("func ")) {
        val bodyStart = findFunctionBodyStartLine(lines, line, cappedInsertion)
        bodyStart.foreach { startLine =>
          val endLine = findFunctionBodyEndLine(lines, startLine)
          if (startLine <= cappedInsertion && endLine >= cappedInsertion) {
            result = Some((line, startLine))
          }
        }
      }
      line += 1
    }
    result
  }

  private def findFunctionBodyStartLine(lines: Vector[String], startLine: Int, cappedInsertion: Int): Option[Int] = {
    var line = startLine
    while (line <= lines.size && line <= math.max(cappedInsertion, startLine + 200)) {
      val sanitized = sanitizeForBraceScanning(lines(line - 1))
      if (sanitized.contains("{")) return Some(line)
      line += 1
    }
    None
  }

  private def findFunctionBodyEndLine(lines: Vector[String], bodyStartLine: Int): Int = {
    var depth = 0
    var line = bodyStartLine
    while (line <= lines.size) {
      val sanitized = sanitizeForBraceScanning(lines(line - 1))
      sanitized.foreach {
        case '{' => depth += 1
        case '}' => depth -= 1
        case _ =>
      }
      if (depth <= 0 && line > bodyStartLine) return line
      line += 1
    }
    lines.size
  }

  private def sanitizeForBraceScanning(raw: String): String = {
    val withoutLineComment = stripLineComment(raw)
    val stringSanitized = new StringBuilder
    var idx = 0
    var inDouble = false
    var inSingle = false
    while (idx < withoutLineComment.length) {
      val ch = withoutLineComment.charAt(idx)
      if (!inSingle && ch == '"' && (idx == 0 || withoutLineComment.charAt(idx - 1) != '\\')) {
        inDouble = !inDouble
        stringSanitized.append(' ')
      } else if (!inDouble && ch == '\'' && (idx == 0 || withoutLineComment.charAt(idx - 1) != '\\')) {
        inSingle = !inSingle
        stringSanitized.append(' ')
      } else if (inDouble || inSingle) {
        stringSanitized.append(' ')
      } else {
        stringSanitized.append(ch)
      }
      idx += 1
    }
    stringSanitized.toString()
  }

  private def stripLineComment(raw: String): String = {
    val idx = raw.indexOf("//")
    if (idx >= 0) raw.substring(0, idx) else raw
  }

  private def extractScopeIdentifiersFromText(text: String): Set[String] =
    ScopeTokenPattern.findAllMatchIn(text).map(_.matched.replaceFirst("(?:@\\d+)+$", "")).filter(isScopeIdentifierCandidate).toSet

  private def extractScopeIdentifiersFromBody(lines: Vector[String], startLine: Int, endLine: Int): Set[String] = {
    if (endLine < startLine) return Set.empty
    val result = mutable.LinkedHashSet.empty[String]
    var inVarBlock = false

    var line = startLine
    while (line <= endLine && line <= lines.size) {
      val sanitized = stripLineComment(lines(line - 1)).trim
      if (inVarBlock) {
        if (sanitized.startsWith(")")) inVarBlock = false
        else {
          extractLeadingIdentifiers(sanitized).foreach(result += _)
        }
      } else {
        if (sanitized.startsWith("var (")) {
          inVarBlock = true
        } else if (sanitized.startsWith("var ")) {
          val afterVar = sanitized.stripPrefix("var").trim
          extractLeadingIdentifiers(afterVar).foreach(result += _)
        }
        val shortDeclIdx = sanitized.indexOf(":=")
        if (shortDeclIdx >= 0) {
          val left = sanitized.substring(0, shortDeclIdx)
          extractLeadingIdentifiers(left).foreach(result += _)
        }
      }
      line += 1
    }
    result.toSet
  }

  private def extractLeadingIdentifiers(text: String): Vector[String] =
    text.split(",").toVector.flatMap { chunk =>
      val trimmed = chunk.trim
      if (trimmed.isEmpty) Vector.empty
      else {
        val first = ScopeTokenPattern.findFirstIn(trimmed).map(_.replaceFirst("(?:@\\d+)+$", ""))
        first.filter(isScopeIdentifierCandidate).toVector
      }
    }

  private def isScopeIdentifierCandidate(token: String): Boolean = {
    val normalized = token.trim
    normalized.nonEmpty &&
      normalized != "_" &&
      normalized.headOption.exists(ch => ch.isLower || ch == '$' || ch == '_') &&
      !ScopeKeywordIdentifiers.contains(normalized)
  }

  private def expressionIdentifiersInScope(expr: String, visibleIdentifiers: Set[String]): Boolean = {
    scopeRelevantIdentifierMatches(expr).forall { case (token, _) => visibleIdentifiers.contains(token) }
  }

  private def scopeRelevantIdentifierMatches(expr: String): Vector[(String, Int)] =
    ScopeTokenPattern.findAllMatchIn(expr).toVector.flatMap { m =>
      val token = m.matched.replaceFirst("(?:@\\d+)+$", "")
      val idx = m.start
      val precededBySelector = idx > 0 && expr.charAt(idx - 1) == '.'
      val scopeCandidate = isScopeIdentifierCandidate(token) || isInternalAliasName(token)
      if (precededBySelector || !scopeCandidate) None
      else Some(token -> idx)
    }

  private def canonicalCallName(name: String): String =
    callBaseName(name).getOrElse(name.trim)

  private def callBaseName(rawName: String): Option[String] = {
    val name = rawName.trim
    if (name.isEmpty) return None

    var idx = 0
    if (!isIdentifierStart(name.charAt(0))) return None
    idx += 1
    while (idx < name.length && isIdentifierPart(name.charAt(idx))) idx += 1

    val base = name.substring(0, idx)
    if (base.isEmpty) return None

    var rest = name.substring(idx).trim
    while (rest.nonEmpty) {
      if (rest.head != '[') return None
      matchingBracketIndex(rest, 0, '[', ']') match {
        case Some(closeIdx) =>
          rest = rest.substring(closeIdx + 1).trim
        case None =>
          return None
      }
    }

    Some(base)
  }

  private def isIdentifierStart(ch: Char): Boolean =
    ch.isLetter || ch == '_'

  private def isIdentifierPart(ch: Char): Boolean =
    ch.isLetterOrDigit || ch == '_' || ch == '$'

  private def matchingBracketIndex(value: String, startIdx: Int, open: Char, close: Char): Option[Int] = {
    if (startIdx < 0 || startIdx >= value.length || value.charAt(startIdx) != open) return None
    var depth = 0
    var idx = startIdx
    while (idx < value.length) {
      val ch = value.charAt(idx)
      if (ch == open) depth += 1
      else if (ch == close) {
        depth -= 1
        if (depth == 0) return Some(idx)
        if (depth < 0) return None
      }
      idx += 1
    }
    None
  }

  private def isTupleConstructor(name: String): Boolean = {
    val canonical = canonicalCallName(name)
    val base = if (canonical.endsWith("()")) canonical.dropRight(2) else canonical
    base == "tuple" || (base.startsWith("tuple") && base.drop("tuple".length).forall(_.isDigit))
  }

  private def isTupleProjectionCall(name: String): Boolean =
    canonicalCallName(name) match {
      case TupleProjectionNamePattern() => true
      case _ => false
    }

  private def actionAsString(action: AnnotationAction): String =
    action match {
      case FoldAnnotation => "fold"
      case UnfoldAnnotation => "unfold"
      case DeferFoldAnnotation => "defer fold"
    }

  private val InternalEncodingTokenPattern: Regex =
    "(dynamic_pred_\\d+|get\\d+of\\d+|tuple\\d*|box_Poly|unbox_Poly|ShArrayloc|sarray|soffset|sadd|ShStructget\\d+of\\d+|ShStructrev\\d+of\\d+|First\\s*:|Second\\s*:|\\$[A-Za-z_][A-Za-z0-9_]*|fn\\$\\$\\d+|\\bN\\d+(?:@\\d+)*\\b)".r

  private def findUnsupportedEncodingToken(line: String): Option[String] =
    InternalEncodingTokenPattern.findFirstIn(line)

  private def collectInternalEncodingWarnings(lines: Vector[String]): Vector[String] =
    lines.zipWithIndex.flatMap { case (line, idx) =>
      findUnsupportedEncodingToken(line).map { token =>
        s"Rendered line #${idx + 1} still contains internal encoding token '$token'."
      }
    }.distinct
}
