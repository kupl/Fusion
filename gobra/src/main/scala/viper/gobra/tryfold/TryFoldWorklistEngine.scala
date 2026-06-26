package viper.gobra.tryfold

import viper.gobra.ast.{internal => in}
import viper.gobra.backend.TryFoldSourcePermissionExtractor.PermissionAmount
import viper.gobra.backend.BackendVerifier
import viper.gobra.frontend.{Config, PackageInfo}
import viper.gobra.frontend.TryFoldCandidateMode
import viper.gobra.reporting.{BackTranslator, VerifierError, VerifierResult}
import viper.gobra.translator.Translator
import viper.gobra.util.GobraExecutionContext
import viper.silver.{ast => vpr}

import scala.concurrent.Future

object TryFoldWorklistEngine {

  sealed trait AnnotationAction {
    def priority: Int
  }
  case object FoldAnnotation extends AnnotationAction {
    override val priority: Int = 1
  }
  case object UnfoldAnnotation extends AnnotationAction {
    override val priority: Int = 0
  }
  case object DeferFoldAnnotation extends AnnotationAction {
    override val priority: Int = 2
  }

  final case class AnnotationDirective(
                                        action: AnnotationAction,
                                        predicateName: String,
                                        args: Vector[String] = Vector.empty,
                                        argsExp: Option[Vector[vpr.Exp]] = None,
                                        permission: Option[PermissionAmount] = None,
                                        permissionIsWildcard: Boolean = false,
                                        permissionSymbolicTerm: Option[String] = None,
                                        permissionOrigin: Option[String] = None,
                                      )

  final case class AnnotationSequence(steps: Vector[AnnotationDirective])

  private final case class CandidatePathEnumeration(
                                                     candidateMode: TryFoldCandidateMode.Mode,
                                                     endpoints: Option[TryFoldFailureContextExtractor.FailureEndpoints],
                                                     graphPaths: Vector[TryFoldPathExplorer.Path],
                                                     selectedPaths: Vector[TryFoldPathExplorer.Path],
                                                     dynamicPathDecisions: Vector[TryFoldDynamicAlternativeFilter.PathDecision],
                                                     rawSequences: Vector[AnnotationSequence],
                                                     plannedSequences: Vector[TryFoldInsertionPlanner.PlannedAnnotationSequence],
                                                     materializationDrops: Vector[TryFoldAnnotationCandidateBuilder.MaterializationDrop],
                                                     materializationStats: TryFoldAnnotationCandidateBuilder.MaterializationStats,
                                                     insertionPlanning: TryFoldInsertionPlanner.PlanningResult,
                                                   )

  def verify(rootProgram: in.Program, pkgInfo: PackageInfo, config: Config)(implicit executor: GobraExecutionContext): Future[VerifierResult] = {
    val instrumented = TryFoldReturnMarkerInstrumentation.instrumentProgram(rootProgram)
    translate(instrumented.program, pkgInfo, config) match {
      case Left(errors) =>
        Future.successful(VerifierResult.Failure(errors))
      case Right(task) =>
        verifyTask(task, pkgInfo, config).map {
          case BackendVerifier.Success =>
            VerifierResult.Success
          case failure: BackendVerifier.Failure =>
            val graph = buildPredicateDependencyGraph(task.program, task.tryFoldMetadata)
            maybeExportPredicateDependencyGraph(
              config = config,
              graph = graph,
              attempt = 1,
              failure = failure,
            )
            val enumeration = enumerateCandidateAnnotationSequences(graph, failure, config, task.program, task.tryFoldMetadata)
            val renderEnvironment = buildRenderEnvironment(config)
            val symbolicStoreByLocal = TryFoldFailureContextExtractor.extractFirstStoreBindings(failure)
            val symbolicStoreEntries = TryFoldFailureContextExtractor.extractFirstStoreBindingEntries(failure)
            val gobraRender = TryFoldGobraAnnotationBacktranslator.renderBatch(
              plannedSequences = enumeration.plannedSequences,
              rootProgram = instrumented.program,
              translatedProgram = task.program,
              renderEnvironment = renderEnvironment,
              translationMetadata = task.tryFoldMetadata,
              symbolicStoreByLocal = symbolicStoreByLocal,
              symbolicStoreEntries = symbolicStoreEntries,
            )
            maybeExportCandidatePaths(
              config = config,
              attempt = 1,
              failure = failure,
              enumeration = enumeration,
              gobraRender = gobraRender,
            )
            BackTranslator.backTranslate(failure)(config)
        }
    }
  }

  private def translate(program: in.Program, pkgInfo: PackageInfo, config: Config): Either[Vector[VerifierError], BackendVerifier.Task] =
    Translator.translate(program, pkgInfo)(config)

  private def verifyTask(task: BackendVerifier.Task, pkgInfo: PackageInfo, config: Config)(implicit executor: GobraExecutionContext): Future[BackendVerifier.Result] =
    if (config.noVerify || !config.shouldVerify) Future.successful(BackendVerifier.Success)
    else BackendVerifier.verify(task, pkgInfo)(config)

  private def buildPredicateDependencyGraph(
                                            program: vpr.Program,
                                            translationMetadata: Option[TryFoldTranslationMetadata],
                                          ): PredicateDependencyGraph =
    PredicateDependencyGraphBuilder.build(
      program = program,
      translationMetadata = translationMetadata.getOrElse(TryFoldTranslationMetadata.empty),
    )

  private def maybeExportPredicateDependencyGraph(
                                                   config: Config,
                                                   graph: PredicateDependencyGraph,
                                                   attempt: Int,
                                                   failure: BackendVerifier.Failure,
                                                 ): Unit =
    PredicateDependencyGraphExporter.maybeExport(
      config = config,
      graph = graph,
      attempt = attempt,
      workItemId = 0L,
      workItemDepth = 0,
      failure = failure,
    )

  private def maybeExportCandidatePaths(
                                         config: Config,
                                         attempt: Int,
                                         failure: BackendVerifier.Failure,
                                         enumeration: CandidatePathEnumeration,
                                         gobraRender: TryFoldGobraAnnotationBacktranslator.BatchRenderResult,
                                       ): Unit =
    TryFoldPathExporter.maybeExport(
      config = config,
      attempt = attempt,
      workItemId = 0L,
      workItemDepth = 0,
      failure = failure,
      endpoints = enumeration.endpoints,
      candidateMode = enumeration.candidateMode,
      graphPaths = enumeration.graphPaths,
      selectedPaths = enumeration.selectedPaths,
      dynamicPathDecisions = enumeration.dynamicPathDecisions,
      rawSequences = enumeration.rawSequences,
      selectedSequences = enumeration.plannedSequences,
      materializationDrops = enumeration.materializationDrops,
      materializationStats = enumeration.materializationStats,
      planning = enumeration.insertionPlanning,
      gobraRender = Some(gobraRender),
    )

  private def enumerateCandidateAnnotationSequences(
                                                     graph: PredicateDependencyGraph,
                                                     failure: BackendVerifier.Failure,
                                                     config: Config,
                                                     translatedProgram: vpr.Program,
                                                     translationMetadata: Option[TryFoldTranslationMetadata],
                                                   ): CandidatePathEnumeration = {
    val endpointOpt = TryFoldFailureContextExtractor.extractFirstFailureEndpoints(failure)
      .map(augmentSourcesWithLiteralNodes(graph, _, config.tryFoldPathMaxDepth))
    val storeBindings = TryFoldFailureContextExtractor.extractFirstStoreBindings(failure)
    val (graphPaths, filteredPaths, dynamicPathDecisions, rawSequences, materializationDrops, materializationStats) =
      config.tryFoldCandidateMode match {
        case TryFoldCandidateMode.Ours =>
          val paths = endpointOpt.toVector.flatMap { endpoints =>
            enumerateOursPaths(graph, endpoints, config.tryFoldPathMaxDepth)
          }
          val pathDecisions = endpointOpt.toVector.flatMap { endpoints =>
            paths.zipWithIndex.map { case (path, pathIndex) =>
              TryFoldDynamicAlternativeFilter.analyzePath(
                pathIndex = pathIndex,
                path = path,
                endpoints = endpoints,
                translationMetadata = translationMetadata.getOrElse(TryFoldTranslationMetadata.empty),
                storeBindings = storeBindings,
                translatedProgram = Some(translatedProgram),
                failure = Some(failure),
              )
            }
          }
          val selectedPaths = pathDecisions.collect { case decision if decision.keep => decision.path }
          val materializationOutcomes = endpointOpt.toVector.flatMap { endpoints =>
            selectedPaths.zipWithIndex.map { case (path, pathIndex) =>
              TryFoldAnnotationCandidateBuilder.materializeWithDiagnosticsForPath(
                path = path,
                pathIndex = pathIndex,
                endpoints = endpoints,
                maxConcreteCandidatesPerPath = config.tryFoldMaxConcreteCandidatesPerPath,
              )
            }
          }
          val sequences = materializationOutcomes.flatMap(_.sequences)
          val drops = materializationOutcomes.flatMap(_.drops)
          val stats = TryFoldAnnotationCandidateBuilder.summarizeMaterializationOutcomes(
            pathCount = selectedPaths.size,
            outcomes = materializationOutcomes,
          )
          (paths, selectedPaths, pathDecisions, sequences, drops, stats)

        case TryFoldCandidateMode.Baseline =>
          val sequences = endpointOpt.toVector.flatMap(TryFoldEnumerativeBaselineCandidateBuilder.enumerate)
          (
            Vector.empty,
            Vector.empty,
            Vector.empty,
            sequences,
            Vector.empty,
            TryFoldAnnotationCandidateBuilder.MaterializationStats(
              pathCount = 0,
              pathsWithConcreteCandidates = 0,
              droppedPathCount = 0,
              totalRawConcreteCandidates = 0,
              totalDrops = 0,
              dropReasonCounts = Map.empty,
            ),
          )
      }
    val sequences = rawSequences
      .groupBy(sequenceSignature)
      .values
      .map(_.head)
      .toVector
      .sortBy(sequenceSortKey)
    val planning = TryFoldInsertionPlanner.plan(
      failure = failure,
      sequences = sequences.take(config.tryFoldMaxChildrenPerFailure),
    )
    CandidatePathEnumeration(
      candidateMode = config.tryFoldCandidateMode,
      endpoints = endpointOpt,
      graphPaths = graphPaths,
      selectedPaths = filteredPaths,
      dynamicPathDecisions = dynamicPathDecisions,
      rawSequences = sequences,
      plannedSequences = planning.plannedSequences,
      materializationDrops = materializationDrops,
      materializationStats = materializationStats,
      insertionPlanning = planning,
    )
  }

  private def augmentSourcesWithLiteralNodes(
                                              graph: PredicateDependencyGraph,
                                              endpoints: TryFoldFailureContextExtractor.FailureEndpoints,
                                              maxDepth: Int,
                                            ): TryFoldFailureContextExtractor.FailureEndpoints = {
    val trueLiteralNodes = graph.nodes.collect { case literal@BoolLiteralNode(true) => literal }.toVector
    if (trueLiteralNodes.isEmpty || maxDepth <= 0) endpoints
    else endpoints.copy(sources = endpoints.sources ++ trueLiteralNodes)
  }

  private def enumerateOursPaths(
                                  graph: PredicateDependencyGraph,
                                  endpoints: TryFoldFailureContextExtractor.FailureEndpoints,
                                  maxDepth: Int,
                                ): Vector[TryFoldPathExplorer.Path] =
    TryFoldPathExplorer.enumerateOursPaths(
      graph = graph,
      sources = endpoints.sources,
      target = endpoints.target,
      maxDepth = maxDepth,
    )

  private def buildRenderEnvironment(config: Config): TryFoldGobraAnnotationBacktranslator.RenderEnvironment = {
    val packageNameByViperId = config.packageInfoInputMap.keys.map { pkg =>
      pkg.viperId -> pkg.name
    }.toMap
    TryFoldGobraAnnotationBacktranslator.RenderEnvironment(packageNameByViperId)
  }

  private def sequenceSignature(sequence: AnnotationSequence): String =
    sequence.steps.map { step =>
      val args = step.args.mkString(",")
      val perm =
        if (step.permissionIsWildcard) "_"
        else step.permission.map(_.rational).getOrElse("?")
      val origin = step.permissionOrigin.getOrElse("?")
      s"${step.action.priority}:${step.predicateName}($args)@$perm@$origin"
    }.mkString("|")

  private def sequenceSortKey(sequence: AnnotationSequence): (Int, String) =
    (sequence.steps.size, sequenceSignature(sequence))
}
