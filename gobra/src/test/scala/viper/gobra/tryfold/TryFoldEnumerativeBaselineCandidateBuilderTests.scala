package viper.gobra.tryfold

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import viper.gobra.backend.TryFoldSourcePermissionExtractor.{PermissionAmount, SourcePermissionEntry}

class TryFoldEnumerativeBaselineCandidateBuilderTests extends AnyFunSuite with Matchers {

  private def pred(name: String): PredicateNode = PredicateNode(name)
  private def field(name: String): FieldNode = FieldNode(name)

  private def sourceEntry(
                           index: Int,
                           nodeKind: String,
                           nodeName: String,
                           args: Vector[String],
                           permission: Option[PermissionAmount],
                         ): SourcePermissionEntry =
    SourcePermissionEntry(
      index = index,
      nodeKind = nodeKind,
      nodeName = nodeName,
      nodeId = s"$nodeKind:$nodeName",
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
                           index: Int,
                           nodeKind: String,
                           nodeName: String,
                           args: Vector[String],
                           permission: Option[PermissionAmount],
                         ): TryFoldTargetPermissionExtractor.TargetPermissionEntry =
    TryFoldTargetPermissionExtractor.TargetPermissionEntry(
      index = index,
      nodeKind = nodeKind,
      nodeName = nodeName,
      nodeId = s"$nodeKind:$nodeName",
      arguments = args,
      argumentsExp = None,
      access = s"$nodeName(${args.mkString(",")})",
      permissionTerm = permission.map(_.rational),
      evaluatedPermission = permission,
      evaluationKind = permission.map(_ => "exact").getOrElse("symbolic"),
      extractionSource = "reason.locationAccess",
      matchesReasonLocation = true,
    )

  test("enumerates unfold candidates from concrete source predicates and fold candidate from concrete target predicate") {
    val endpoints = TryFoldFailureContextExtractor.FailureEndpoints(
      sources = Set(pred("B"), pred("C")),
      target = pred("A"),
      sourcePermissions = Vector(
        sourceEntry(0, "predicate", "B", Vector("x"), Some(PermissionAmount("1/2", "0.5"))),
        sourceEntry(1, "predicate", "C", Vector("y"), Some(PermissionAmount("1/3", "0.3333333333333333"))),
      ),
      targetPermissions = Vector(
        targetEntry(0, "predicate", "A", Vector("z"), Some(PermissionAmount("1/4", "0.25")))
      ),
    )

    val sequences = TryFoldEnumerativeBaselineCandidateBuilder.enumerate(endpoints)

    sequences.map(_.steps.head.action) shouldBe Vector(
      TryFoldWorklistEngine.UnfoldAnnotation,
      TryFoldWorklistEngine.UnfoldAnnotation,
      TryFoldWorklistEngine.FoldAnnotation,
    )
    sequences.map(_.steps.head.predicateName) shouldBe Vector("B", "C", "A")
    sequences.map(_.steps.head.args) shouldBe Vector(Vector("x"), Vector("y"), Vector("z"))
  }

  test("field target failure only emits predicate unfolds and no fold candidate") {
    val endpoints = TryFoldFailureContextExtractor.FailureEndpoints(
      sources = Set(pred("B"), field("f")),
      target = field("missing"),
      sourcePermissions = Vector(
        sourceEntry(0, "predicate", "B", Vector("x"), Some(PermissionAmount("1/2", "0.5"))),
        sourceEntry(1, "field", "f", Vector("obj"), Some(PermissionAmount("1/2", "0.5"))),
      ),
      targetPermissions = Vector(
        targetEntry(0, "field", "missing", Vector("obj"), Some(PermissionAmount("1/4", "0.25")))
      ),
    )

    val sequences = TryFoldEnumerativeBaselineCandidateBuilder.enumerate(endpoints)

    sequences should have size 1
    sequences.head.steps.head.action shouldBe TryFoldWorklistEngine.UnfoldAnnotation
    sequences.head.steps.head.predicateName shouldBe "B"
  }

  test("deduplicates duplicate source and target concrete instances") {
    val endpoints = TryFoldFailureContextExtractor.FailureEndpoints(
      sources = Set(pred("B"), pred("A")),
      target = pred("A"),
      sourcePermissions = Vector(
        sourceEntry(0, "predicate", "B", Vector("x"), Some(PermissionAmount("1/2", "0.5"))),
        sourceEntry(1, "predicate", "B", Vector("x"), Some(PermissionAmount("1/2", "0.5"))),
      ),
      targetPermissions = Vector(
        targetEntry(0, "predicate", "A", Vector("z"), Some(PermissionAmount("1/4", "0.25"))),
        targetEntry(1, "predicate", "A", Vector("z"), Some(PermissionAmount("1/4", "0.25"))),
      ),
    )

    val sequences = TryFoldEnumerativeBaselineCandidateBuilder.enumerate(endpoints)

    sequences should have size 2
    sequences.map(_.steps.head.predicateName) shouldBe Vector("B", "A")
  }

  test("baseline fold candidate rewrites to defer fold on postcondition failure") {
    val endpoints = TryFoldFailureContextExtractor.FailureEndpoints(
      sources = Set.empty,
      target = pred("A"),
      sourcePermissions = Vector.empty,
      targetPermissions = Vector(
        targetEntry(0, "predicate", "A", Vector("z"), Some(PermissionAmount("1/4", "0.25")))
      ),
    )

    val sequence = TryFoldEnumerativeBaselineCandidateBuilder.enumerate(endpoints).head
    val rewritten = TryFoldInsertionPlanner.rewriteForPostcondition(sequence)

    rewritten.steps.map(_.action) shouldBe Vector(TryFoldWorklistEngine.DeferFoldAnnotation)
    rewritten.steps.head.predicateName shouldBe "A"
    rewritten.steps.head.args shouldBe Vector("z")
  }
}
