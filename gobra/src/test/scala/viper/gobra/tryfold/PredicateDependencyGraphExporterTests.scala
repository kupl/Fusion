package viper.gobra.tryfold

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
class PredicateDependencyGraphExporterTests extends AnyFunSuite with Matchers {

  private def metadata(taskName: String): PredicateDependencyGraphExporter.GraphExportMetadata =
    PredicateDependencyGraphExporter.GraphExportMetadata(
      taskName = taskName,
      attempt = 1,
      workItemId = 0L,
      workItemDepth = 0,
      firstErrorId = Some("call.precondition:insufficient.permission"),
      firstErrorReadableMessage = Some("insufficient permission"),
      firstErrorSourceLocation = Some("host.go@219.18--219.51"),
    )

  test("rendered graph json preserves ours unlabeled edges") {
    val source = PredicateNode("dynamic_pred_0")
    val graph = PredicateDependencyGraph(
      nodes = Set(source, PredicateNode("B"), PredicateNode("U"), FieldNode("f")),
      edges = Vector(
        DependencyEdge(source, PredicateNode("B"), PredicateDependency, Set(UnlabeledEdge)),
        DependencyEdge(source, FieldNode("f"), FieldDependency, Set(UnlabeledEdge)),
        DependencyEdge(source, PredicateNode("U"), PredicateDependency, Set(UnlabeledEdge)),
      ),
      outgoing = Map.empty,
      incoming = Map.empty,
    )

    val json = PredicateDependencyGraphExporter.renderGraphReportJson(metadata("task-ours"), graph)
    json should include ("\"graphMode\": \"ours\"")
    json should include ("\"kind\": \"unlabeled\"")
    json should not include "\"foldRequirementCount\""
    json should not include "\"foldRequirements\""
    json should not include "\"kind\": \"typeCase\""
    json should not include "\"kind\": \"defaultTypeCase\""
  }
}
