package viper.gobra.tryfold

import viper.gobra.tryfold.TryFoldWorklistEngine.{AnnotationDirective, FoldAnnotation, UnfoldAnnotation}

import scala.collection.immutable.Queue

object TryFoldPathExplorer {

  final case class PathStep(
                             from: DependencyNode,
                             to: DependencyNode,
                             directive: AnnotationDirective,
                             edge: DependencyEdge,
                           )

  final case class Path(
                         source: DependencyNode,
                         target: DependencyNode,
                         steps: Vector[PathStep],
                       ) {
    lazy val annotationSequence: TryFoldWorklistEngine.AnnotationSequence =
      TryFoldWorklistEngine.AnnotationSequence(steps.map(_.directive))
  }

  private final case class ExplorationState(
                                             source: DependencyNode,
                                             nodes: Vector[DependencyNode],
                                             steps: Vector[PathStep],
                                           ) {
    def current: DependencyNode = nodes.last
    def previous: Option[DependencyNode] =
      if (nodes.lengthCompare(2) >= 0) Some(nodes(nodes.size - 2)) else None
  }

  private final case class Move(
                                 to: DependencyNode,
                                 directive: AnnotationDirective,
                                 edge: DependencyEdge,
                               )

  def enumerateOursPaths(
                          graph: PredicateDependencyGraph,
                          sources: Set[DependencyNode],
                          target: DependencyNode,
                          maxDepth: Int,
                        ): Vector[Path] = {
    if (sources.isEmpty || maxDepth <= 0) {
      Vector.empty
    } else {
      var queue = Queue.from(sources.toVector.sortBy(_.id).map(source => ExplorationState(source, Vector(source), Vector.empty)))
      var discovered = Vector.empty[Path]

      while (queue.nonEmpty) {
        val (state, tailQueue) = queue.dequeue
        queue = tailQueue

        if (state.steps.nonEmpty && state.current == target) {
          discovered :+= Path(
            source = state.source,
            target = target,
            steps = state.steps,
          )
        }

        if ((state.current != target || state.steps.isEmpty) && state.steps.size < maxDepth) {
          val moves = oursMoves(graph, state.current)
            .filter(move => !isImmediateBacktrack(state, move))
            .sortBy(move => (move.directive.action.priority, move.directive.predicateName, move.to.id))

          moves.foreach { move =>
            val step = PathStep(
              from = state.current,
              to = move.to,
              directive = move.directive,
              edge = move.edge,
            )
            queue = queue.enqueue(
              ExplorationState(
                source = state.source,
                nodes = state.nodes :+ move.to,
                steps = state.steps :+ step,
              )
            )
          }
        }
      }

      deduplicateAndSort(discovered)
    }
  }

  private def oursMoves(graph: PredicateDependencyGraph, current: DependencyNode): Vector[Move] = {
    val forwardMoves = graph.edgesFrom(current).filterNot(_.kind == LiteralDependency).map { edge =>
      Move(
        to = edge.to,
        directive = AnnotationDirective(UnfoldAnnotation, edge.from.name),
        edge = edge,
      )
    }
    val reverseMoves = graph.edgesTo(current).map { edge =>
      Move(
        to = edge.from,
        directive = AnnotationDirective(FoldAnnotation, edge.from.name),
        edge = edge,
      )
    }
    forwardMoves ++ reverseMoves
  }

  private def isImmediateBacktrack(state: ExplorationState, move: Move): Boolean =
    state.previous.exists(previousNode => move.to == previousNode && move.to != state.current)

  private def deduplicateAndSort(paths: Vector[Path]): Vector[Path] = {
    val deduplicated = paths
      .groupBy(pathSignature)
      .values
      .map(_.head)
      .toVector

    deduplicated.sortBy(pathSortKey)
  }

  private def pathSignature(path: Path): String = {
    val sourceKey = path.source.id
    val targetKey = path.target.id
    val stepKeys = path.steps.map { step =>
      s"${step.from.id}->${step.to.id}:${step.directive.action.priority}:${step.directive.predicateName}"
    }.mkString("|")
    s"$sourceKey=>$targetKey#$stepKeys"
  }

  private def pathSortKey(path: Path): (Int, String) = {
    val stepKeys = path.steps.map { step =>
      s"${step.directive.action.priority}:${step.directive.predicateName}:${step.from.id}->${step.to.id}"
    }.mkString("|")
    (path.steps.size, s"${path.source.id}|${path.target.id}|$stepKeys")
  }
}
