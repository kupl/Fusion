package viper.gobra.tryfold

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import viper.gobra.backend.TryFoldSourcePermissionExtractor.{PermissionAmount, SourcePermissionEntry}
import viper.gobra.tryfold.TryFoldAnnotationCandidateBuilder.PermissionEvidenceRole
import viper.gobra.tryfold.TryFoldTargetPermissionExtractor.TargetPermissionEntry

class TryFoldAnnotationCandidateBuilderTests extends AnyFunSuite with Matchers {

  private def pred(name: String): PredicateNode = PredicateNode(name)
  private def field(name: String): FieldNode = FieldNode(name)
  private def bool(value: Boolean): BoolLiteralNode = BoolLiteralNode(value)

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

  private def sourceEntry(
                           nodeName: String,
                           args: Vector[String],
                           permission: Option[PermissionAmount],
                           nodeKind: String = "predicate",
                         ): SourcePermissionEntry =
    SourcePermissionEntry(
      index = 0,
      nodeKind = nodeKind,
      nodeName = nodeName,
      nodeId = if (nodeKind == "field") s"field:$nodeName" else s"predicate:$nodeName",
      chunkKind = "BasicChunk",
      chunk = s"$nodeName(${args.mkString(",")})",
      permissionTerm = permission.map(_.rational).getOrElse(""),
      bodyPermissionTerm = permission.map(_.rational),
      conditionTerm = None,
      conditionEvaluation = None,
      evaluatedPermission = permission,
      evaluatedBodyPermission = permission,
      evaluationKind = permission.map(_ => "exact").getOrElse("symbolic"),
      arguments = args,
      argumentsExp = None,
      singletonArguments = Vector.empty,
      singletonArgumentsExp = None,
    )

  private def targetEntry(
                           index: Int = 0,
                           nodeKind: String = "predicate",
                           nodeName: String,
                           args: Vector[String],
                           permission: Option[PermissionAmount],
                           permissionTerm: Option[String],
                           evaluationKind: String,
                         ): TargetPermissionEntry =
    TargetPermissionEntry(
      index = index,
      nodeKind = nodeKind,
      nodeName = nodeName,
      nodeId = if (nodeKind == "field") s"field:$nodeName" else s"pred:$nodeName",
      arguments = args,
      argumentsExp = None,
      access = s"$nodeName(${args.mkString(",")})",
      permissionTerm = permissionTerm,
      evaluatedPermission = permission,
      evaluationKind = evaluationKind,
      extractionSource = "test",
      matchesReasonLocation = false,
    )

  private def endpoints(
                         sourceEntries: Vector[SourcePermissionEntry],
                         target: DependencyNode,
                         sources: Set[DependencyNode] = Set.empty,
                         targetPermissions: Vector[TargetPermissionEntry] = Vector.empty,
                       ): TryFoldFailureContextExtractor.FailureEndpoints =
    TryFoldFailureContextExtractor.FailureEndpoints(
      sources = if (sources.nonEmpty) sources else sourceEntries.map { entry =>
        if (entry.nodeKind == "field") field(entry.nodeName): DependencyNode
        else pred(entry.nodeName): DependencyNode
      }.toSet,
      target = target,
      sourcePermissions = sourceEntries,
      targetPermissions = targetPermissions,
    )

  test("materializes unfold candidates with concrete source arguments") {
    val edge = DependencyEdge(
      from = pred("A"),
      to = pred("B"),
      kind = PredicateDependency,
      labels = Set(UnlabeledEdge),
      templates = Vector(EdgeCallsiteTemplate(Vector("x"), Vector("x"))),
    )
    val g = graph(Vector(edge))
    val path = TryFoldPathExplorer.enumerateOursPaths(
      graph = g,
      sources = Set(pred("A")),
      target = pred("B"),
      maxDepth = 1,
    ).head

    val eps = endpoints(
      sourceEntries = Vector(sourceEntry("A", Vector("h"), Some(PermissionAmount("1/2", "0.5")))),
      target = pred("B"),
    )

    val sequences = TryFoldAnnotationCandidateBuilder.materializeSequencesForPath(
      path = path,
      endpoints = eps,
      maxConcreteCandidatesPerPath = 5,
    )

    sequences should have size 1
    val step = sequences.head.steps.head
    step.action shouldBe TryFoldWorklistEngine.UnfoldAnnotation
    step.predicateName shouldBe "A"
    step.args shouldBe Vector("h")
    step.permission.map(_.rational) shouldBe Some("1/2")
  }

  test("propagates concrete arguments forward across multi-step path") {
    val edgeAB = DependencyEdge(
      from = pred("A"),
      to = pred("B"),
      kind = PredicateDependency,
      labels = Set(UnlabeledEdge),
      templates = Vector(EdgeCallsiteTemplate(Vector("x"), Vector("x"))),
    )
    val edgeBC = DependencyEdge(
      from = pred("B"),
      to = pred("C"),
      kind = PredicateDependency,
      labels = Set(UnlabeledEdge),
      templates = Vector(EdgeCallsiteTemplate(Vector("y"), Vector("f(y)"))),
    )
    val g = graph(Vector(edgeAB, edgeBC))
    val path = TryFoldPathExplorer.enumerateOursPaths(
      graph = g,
      sources = Set(pred("A")),
      target = pred("C"),
      maxDepth = 2,
    ).head

    val eps = endpoints(
      sourceEntries = Vector(sourceEntry("A", Vector("h"), Some(PermissionAmount("1/32768", "0.000030517578125")))),
      target = pred("C"),
    )

    val sequences = TryFoldAnnotationCandidateBuilder.materializeSequencesForPath(
      path = path,
      endpoints = eps,
      maxConcreteCandidatesPerPath = 5,
    )

    sequences should not be empty
    val steps = sequences.head.steps
    steps.map(_.predicateName) shouldBe Vector("A", "B")
    steps.map(_.args) shouldBe Vector(Vector("h"), Vector("h"))
  }

  test("caps concrete candidates per path") {
    val edge = DependencyEdge(
      from = pred("A"),
      to = pred("B"),
      kind = PredicateDependency,
      labels = Set(UnlabeledEdge),
      templates = Vector(EdgeCallsiteTemplate(Vector("x"), Vector("x"))),
    )
    val g = graph(Vector(edge))
    val path = TryFoldPathExplorer.enumerateOursPaths(
      graph = g,
      sources = Set(pred("A")),
      target = pred("B"),
      maxDepth = 1,
    ).head

    val sourceEntries = ('a' to 'f').toVector.map { ch =>
      sourceEntry("A", Vector(ch.toString), Some(PermissionAmount("1/2", "0.5")))
    }
    val eps = endpoints(sourceEntries, pred("B"))

    val sequences = TryFoldAnnotationCandidateBuilder.materializeSequencesForPath(
      path = path,
      endpoints = eps,
      maxConcreteCandidatesPerPath = 5,
    )

    sequences should have size 5
    sequences.foreach(seq => seq.steps should have size 1)
  }

  test("support symbolic binding remains args-only and does not create wildcard permission") {
    val edgeLiteral = DependencyEdge(
      from = pred("B"),
      to = bool(value = true),
      kind = LiteralDependency,
      labels = Set(UnlabeledEdge),
    )
    val edgeBC = DependencyEdge(
      from = pred("B"),
      to = pred("C"),
      kind = PredicateDependency,
      labels = Set(UnlabeledEdge),
      templates = Vector(EdgeCallsiteTemplate(Vector("x"), Vector("x"))),
    )
    val g = graph(Vector(edgeLiteral, edgeBC))
    val path = TryFoldPathExplorer.enumerateOursPaths(
      graph = g,
      sources = Set(bool(value = true)),
      target = pred("C"),
      maxDepth = 2,
    ).find(_.steps.size == 2).get

    val eps = endpoints(
      sourceEntries = Vector.empty,
      target = pred("C"),
      sources = Set(bool(value = true)),
      targetPermissions = Vector(
        targetEntry(
          index = 0,
          nodeName = "B",
          args = Vector("tmp"),
          permission = None,
          permissionTerm = Some("wild_perm"),
          evaluationKind = "symbolic",
        )
      ),
    )

    val sequences = TryFoldAnnotationCandidateBuilder.materializeSequencesForPath(
      path = path,
      endpoints = eps,
      maxConcreteCandidatesPerPath = 5,
    )

    sequences should not be empty
    val steps = sequences.head.steps
    steps.map(_.predicateName) shouldBe Vector("B", "B")
    steps.map(_.args) shouldBe Vector(Vector("tmp"), Vector("tmp"))
    steps.foreach(_.permissionIsWildcard shouldBe false)
    steps.foreach(_.permission shouldBe None)
  }

  test("primary symbolic binding still allows wildcard permission") {
    val entry = targetEntry(
      nodeName = "B",
      args = Vector("tmp"),
      permission = None,
      permissionTerm = Some("wild_perm"),
      evaluationKind = "symbolic",
    )

    val instance = TryFoldAnnotationCandidateBuilder.targetEntryToInstance(
      entry,
      PermissionEvidenceRole.TargetPrimary,
      allowSymbolicWildcard = true,
    ).get

    instance.args shouldBe Vector("tmp")
    instance.permission shouldBe None
    instance.permissionIsWildcard shouldBe true
    instance.permissionSymbolicTerm shouldBe Some("wild_perm")
    instance.permissionEvidenceRole shouldBe PermissionEvidenceRole.TargetPrimary
    instance.wildcardEligible shouldBe true
  }

  test("support exact binding remains usable as concrete permission evidence") {
    val entry = targetEntry(
      nodeName = "B",
      args = Vector("tmp"),
      permission = Some(PermissionAmount("1/4", "0.25")),
      permissionTerm = Some("1/4"),
      evaluationKind = "exact",
    )

    val instance = TryFoldAnnotationCandidateBuilder.targetEntryToInstance(
      entry,
      PermissionEvidenceRole.TargetSupportArgsOnly,
      allowSymbolicWildcard = false,
    ).get

    instance.args shouldBe Vector("tmp")
    instance.permission.map(_.rational) shouldBe Some("1/4")
    instance.permissionIsWildcard shouldBe false
    instance.permissionEvidenceRole shouldBe PermissionEvidenceRole.TargetSupportArgsOnly
    instance.wildcardEligible shouldBe false
  }

  test("fold exact fallback from source remains unchanged") {
    val edge = DependencyEdge(
      from = pred("B"),
      to = field("F"),
      kind = FieldDependency,
      labels = Set(UnlabeledEdge),
      templates = Vector(EdgeCallsiteTemplate(Vector("x"), Vector("x"))),
    )
    val g = graph(Vector(edge))
    val path = TryFoldPathExplorer.enumerateOursPaths(
      graph = g,
      sources = Set(field("F")),
      target = pred("B"),
      maxDepth = 1,
    ).head

    val eps = endpoints(
      sourceEntries = Vector(sourceEntry(nodeKind = "field", nodeName = "F", args = Vector.empty, permission = Some(PermissionAmount("1/4", "0.25")))),
      target = pred("B"),
      sources = Set(field("F")),
      targetPermissions = Vector(
        targetEntry(
          nodeName = "B",
          args = Vector("tmp"),
          permission = None,
          permissionTerm = None,
          evaluationKind = "missing",
        )
      ),
    )

    val sequences = TryFoldAnnotationCandidateBuilder.materializeSequencesForPath(
      path = path,
      endpoints = eps,
      maxConcreteCandidatesPerPath = 5,
    )

    sequences should have size 1
    val step = sequences.head.steps.head
    step.action shouldBe TryFoldWorklistEngine.FoldAnnotation
    step.predicateName shouldBe "B"
    step.args shouldBe Vector("tmp")
    step.permission.map(_.rational) shouldBe Some("1/4")
    step.permissionIsWildcard shouldBe false
    step.permissionOrigin shouldBe Some("fold_from_step_source_unique")
  }
}
