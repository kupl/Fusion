package viper.gobra.tryfold

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import viper.gobra.backend.TryFoldSourcePermissionExtractor.PermissionAmount

class TryFoldInsertionPlannerTests extends AnyFunSuite with Matchers {

  test("postcondition rewrite keeps unfolds, reverses folds, and converts to deferFold") {
    val sequence = TryFoldWorklistEngine.AnnotationSequence(Vector(
      TryFoldWorklistEngine.AnnotationDirective(
        action = TryFoldWorklistEngine.FoldAnnotation,
        predicateName = "A",
        args = Vector("x"),
        permission = Some(PermissionAmount("1/2", "0.5")),
      ),
      TryFoldWorklistEngine.AnnotationDirective(
        action = TryFoldWorklistEngine.UnfoldAnnotation,
        predicateName = "B",
        args = Vector("x"),
      ),
      TryFoldWorklistEngine.AnnotationDirective(
        action = TryFoldWorklistEngine.FoldAnnotation,
        predicateName = "C",
        args = Vector("y"),
      ),
    ))

    val rewritten = TryFoldInsertionPlanner.rewriteForPostcondition(sequence)

    rewritten.steps.map(_.action) shouldBe Vector(
      TryFoldWorklistEngine.UnfoldAnnotation,
      TryFoldWorklistEngine.DeferFoldAnnotation,
      TryFoldWorklistEngine.DeferFoldAnnotation,
    )
    rewritten.steps.map(_.predicateName) shouldBe Vector("B", "C", "A")
    rewritten.steps.last.permission.map(_.rational) shouldBe Some("1/2")
  }
}
