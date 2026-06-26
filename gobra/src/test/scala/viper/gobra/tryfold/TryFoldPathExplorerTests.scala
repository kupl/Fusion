package viper.gobra.tryfold

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import viper.gobra.tryfold.TryFoldWorklistEngine.{FoldAnnotation, UnfoldAnnotation}

class TryFoldPathExplorerTests extends AnyFunSuite with Matchers {

  private def pred(name: String): PredicateNode = PredicateNode(name)
  private def field(name: String): FieldNode = FieldNode(name)

  private def predEdge(from: String, to: String): DependencyEdge =
    DependencyEdge(
      from = pred(from),
      to = pred(to),
      kind = PredicateDependency,
      labels = Set(UnlabeledEdge),
    )

  private def fieldEdge(from: String, toField: String): DependencyEdge =
    DependencyEdge(
      from = pred(from),
      to = field(toField),
      kind = FieldDependency,
      labels = Set(UnlabeledEdge),
    )

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

  test("ours exploration returns shortest unfold path first") {
    val g = graph(Vector(
      predEdge("A", "B"),
      fieldEdge("B", "f"),
    ))
    val paths = TryFoldPathExplorer.enumerateOursPaths(
      graph = g,
      sources = Set(pred("A")),
      target = field("f"),
      maxDepth = 3,
    )

    paths should not be empty
    val first = paths.head
    first.steps.map(_.directive.action) shouldBe Vector(UnfoldAnnotation, UnfoldAnnotation)
    first.steps.map(_.directive.predicateName) shouldBe Vector("A", "B")
    first.steps.map(_.to.id) shouldBe Vector("pred:B", "field:f")
  }

  test("ours exploration uses reverse edges as fold actions") {
    val g = graph(Vector(
      predEdge("A", "B"),
      fieldEdge("B", "f"),
    ))
    val paths = TryFoldPathExplorer.enumerateOursPaths(
      graph = g,
      sources = Set(field("f")),
      target = pred("A"),
      maxDepth = 3,
    )

    paths should not be empty
    val first = paths.head
    first.steps.map(_.directive.action) shouldBe Vector(FoldAnnotation, FoldAnnotation)
    first.steps.map(_.directive.predicateName) shouldBe Vector("B", "A")
    first.steps.map(_.to.id) shouldBe Vector("pred:B", "pred:A")
  }

  test("ours exploration blocks immediate u-v-u backtracking") {
    val g = graph(Vector(predEdge("A", "B")))
    val paths = TryFoldPathExplorer.enumerateOursPaths(
      graph = g,
      sources = Set(pred("A")),
      target = pred("A"),
      maxDepth = 2,
    )

    paths shouldBe Vector.empty
  }

  test("ours exploration allows self-loop paths") {
    val g = graph(Vector(predEdge("A", "A")))
    val paths = TryFoldPathExplorer.enumerateOursPaths(
      graph = g,
      sources = Set(pred("A")),
      target = pred("A"),
      maxDepth = 1,
    )

    paths.map(_.steps.head.directive.action).toSet shouldBe Set(UnfoldAnnotation, FoldAnnotation)
    paths.foreach(path => path.steps.size shouldBe 1)
  }

  test("ours exploration respects max depth") {
    val g = graph(Vector(
      predEdge("A", "B"),
      predEdge("B", "C"),
    ))

    val tooShallow = TryFoldPathExplorer.enumerateOursPaths(
      graph = g,
      sources = Set(pred("A")),
      target = pred("C"),
      maxDepth = 1,
    )
    tooShallow shouldBe Vector.empty

    val deepEnough = TryFoldPathExplorer.enumerateOursPaths(
      graph = g,
      sources = Set(pred("A")),
      target = pred("C"),
      maxDepth = 2,
    )
    deepEnough should not be empty
    deepEnough.head.steps.map(_.directive.action) shouldBe Vector(UnfoldAnnotation, UnfoldAnnotation)
  }
}
