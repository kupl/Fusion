package viper.gobra.tryfold

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import viper.gobra.frontend.TryFoldCandidateMode

class TryFoldPathExporterTests extends AnyFunSuite with Matchers {

  private def pred(name: String): PredicateNode = PredicateNode(name)

  private def graph(edges: Vector[DependencyEdge]): PredicateDependencyGraph = {
    val nodes = edges.flatMap(edge => Vector(edge.from: DependencyNode, edge.to)).toSet
    val outgoingBase = edges.groupBy(_.from).map { case (from, groupedEdges) => (from: DependencyNode) -> groupedEdges }
    val incomingBase = edges.groupBy(_.to)
    val outgoing = nodes.map(node => node -> outgoingBase.getOrElse(node, Vector.empty)).toMap
    val incoming = nodes.map(node => node -> incomingBase.getOrElse(node, Vector.empty)).toMap
    PredicateDependencyGraph(
      nodes = nodes,
      edges = edges,
      outgoing = outgoing,
      incoming = incoming,
    )
  }

  test("rendered path json contains endpoints and selected path steps") {
    val g = graph(
      edges = Vector(
        DependencyEdge(
          from = pred("A"),
          to = pred("B"),
          kind = PredicateDependency,
          labels = Set(UnlabeledEdge),
        )
      )
    )

    val paths = TryFoldPathExplorer.enumerateOursPaths(
      graph = g,
      sources = Set(pred("A")),
      target = pred("B"),
      maxDepth = 1,
    )

    val metadata = TryFoldPathExporter.PathExportMetadata(
      taskName = "task",
      attempt = 2,
      workItemId = 7L,
      workItemDepth = 1,
      firstErrorId = Some("call.precondition:insufficient.permission"),
      firstErrorReadableMessage = Some("insufficient permission"),
      firstErrorSourceLocation = Some("host.go@216.1--216.40"),
    )

    val json = TryFoldPathExporter.renderPathReportJson(
      metadata = metadata,
      candidateMode = TryFoldCandidateMode.Ours,
      endpoints = Some(TryFoldFailureContextExtractor.FailureEndpoints(Set(pred("A")), pred("B"))),
      graphPaths = paths,
      selectedPaths = paths,
      rawSequences = paths.map(_.annotationSequence),
      selectedSequences = paths.map { seq =>
        TryFoldInsertionPlanner.PlannedAnnotationSequence(
          originalSequence = seq.annotationSequence,
          plannedSequence = seq.annotationSequence,
          insertionAnchor = TryFoldInsertionPlanner.InsertionAnchor(
            kind = TryFoldInsertionPlanner.ErrorLocationAnchor,
            sourceFile = Some("/tmp/host.go"),
            sourceLine = Some(216),
            sourceColumn = Some(1),
            sourceLocation = Some("host.go@216.1"),
            returnMarkerLabel = None,
            returnLine = None,
            returnColumn = None,
          ),
          isPostconditionFailure = false,
          foldToDeferRewriteApplied = false,
        )
      },
      materializationDrops = Vector.empty,
      materializationStats = TryFoldAnnotationCandidateBuilder.MaterializationStats(
        pathCount = paths.size,
        pathsWithConcreteCandidates = paths.size,
        droppedPathCount = 0,
        totalRawConcreteCandidates = paths.size,
        totalDrops = 0,
        dropReasonCounts = Map.empty,
      ),
      planning = TryFoldInsertionPlanner.PlanningResult(
        firstErrorId = Some("call.precondition:insufficient.permission"),
        firstErrorReadableMessage = Some("insufficient permission"),
        isPostconditionFailure = false,
        insertionAnchor = TryFoldInsertionPlanner.InsertionAnchor(
          kind = TryFoldInsertionPlanner.ErrorLocationAnchor,
          sourceFile = Some("/tmp/host.go"),
          sourceLine = Some(216),
          sourceColumn = Some(1),
          sourceLocation = Some("host.go@216.1"),
          returnMarkerLabel = None,
          returnLine = None,
          returnColumn = None,
        ),
        plannedSequences = paths.map { seq =>
          TryFoldInsertionPlanner.PlannedAnnotationSequence(
            originalSequence = seq.annotationSequence,
            plannedSequence = seq.annotationSequence,
            insertionAnchor = TryFoldInsertionPlanner.InsertionAnchor(
              kind = TryFoldInsertionPlanner.ErrorLocationAnchor,
              sourceFile = Some("/tmp/host.go"),
              sourceLine = Some(216),
              sourceColumn = Some(1),
              sourceLocation = Some("host.go@216.1"),
              returnMarkerLabel = None,
              returnLine = None,
              returnColumn = None,
            ),
            isPostconditionFailure = false,
            foldToDeferRewriteApplied = false,
          )
        },
      ),
    )

    json should include ("\"graphMode\": \"ours\"")
    json should include ("\"candidateMode\": \"ours\"")
    json should include ("\"graphPathCount\": 1")
    json should include ("\"selectedPathCount\": 1")
    json should include ("\"selectedConcreteCandidateCount\": 1")
    json should include ("\"rawConcreteCandidateCount\": 1")
    json should include ("\"singleStepCandidateCount\": 1")
    json should include ("\"gobraCandidateSuccessCount\": 0")
    json should include ("\"gobraCandidateFailureCount\": 0")
    json should include ("\"sourceCount\": 1")
    json should include ("\"sourcePermissions\"")
    json should include ("\"insertionTarget\"")
    json should include ("\"annotationLinesWithPrefix\"")
    json should include ("\"sourceFile\"")
    json should include ("\"sourceLine\"")
    json should include ("\"sourceColumn\"")
    json should include ("\"action\": \"unfold\"")
    json should include ("\"predicateName\": \"A\"")
    json should include ("\"name\": \"B\"")
  }

  test("rendered path json for baseline contains local candidates without graph paths") {
    val metadata = TryFoldPathExporter.PathExportMetadata(
      taskName = "baseline-task",
      attempt = 1,
      workItemId = 0L,
      workItemDepth = 0,
      firstErrorId = Some("postcondition.violated"),
      firstErrorReadableMessage = Some("postcondition might not hold"),
      firstErrorSourceLocation = Some("host.go@216.1--216.40"),
    )

    val rawSequence = TryFoldWorklistEngine.AnnotationSequence(
      Vector(
        TryFoldWorklistEngine.AnnotationDirective(
          action = TryFoldWorklistEngine.FoldAnnotation,
          predicateName = "A",
          args = Vector("z"),
        )
      )
    )

    val planned = TryFoldInsertionPlanner.PlannedAnnotationSequence(
      originalSequence = rawSequence,
      plannedSequence = TryFoldInsertionPlanner.rewriteForPostcondition(rawSequence),
      insertionAnchor = TryFoldInsertionPlanner.InsertionAnchor(
        kind = TryFoldInsertionPlanner.ReturnMarkerAnchor,
        sourceFile = Some("/tmp/host.go"),
        sourceLine = Some(216),
        sourceColumn = Some(1),
        sourceLocation = Some("host.go@216.1"),
        returnMarkerLabel = Some("ret0"),
        returnLine = Some(220),
        returnColumn = Some(3),
      ),
      isPostconditionFailure = true,
      foldToDeferRewriteApplied = true,
    )

    val json = TryFoldPathExporter.renderPathReportJson(
      metadata = metadata,
      candidateMode = TryFoldCandidateMode.Baseline,
      endpoints = Some(TryFoldFailureContextExtractor.FailureEndpoints(Set(pred("A")), pred("A"))),
      graphPaths = Vector.empty,
      selectedPaths = Vector.empty,
      rawSequences = Vector(rawSequence),
      selectedSequences = Vector(planned),
      materializationDrops = Vector.empty,
      materializationStats = TryFoldAnnotationCandidateBuilder.MaterializationStats(
        pathCount = 0,
        pathsWithConcreteCandidates = 0,
        droppedPathCount = 0,
        totalRawConcreteCandidates = 0,
        totalDrops = 0,
        dropReasonCounts = Map.empty,
      ),
      planning = TryFoldInsertionPlanner.PlanningResult(
        firstErrorId = Some("postcondition.violated"),
        firstErrorReadableMessage = Some("postcondition might not hold"),
        isPostconditionFailure = true,
        insertionAnchor = planned.insertionAnchor,
        plannedSequences = Vector(planned),
      ),
    )

    val compactJson = json.replaceAll("\\s+", "")
    compactJson should include ("\"candidateMode\":\"baseline\"")
    compactJson should include ("\"graphPathCount\":0")
    compactJson should include ("\"graphPaths\":[]")
    compactJson should include ("\"selectedPathCount\":0")
    compactJson should include ("\"selectedConcreteCandidateCount\":1")
    compactJson should include ("\"singleStepCandidateCount\":1")
    compactJson should include ("\"annotationLinesWithPrefix\"")
  }
}
