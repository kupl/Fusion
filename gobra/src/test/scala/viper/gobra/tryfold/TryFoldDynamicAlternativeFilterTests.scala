package viper.gobra.tryfold

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import viper.gobra.backend.TryFoldSourcePermissionExtractor.SourcePermissionEntry
import viper.gobra.translator.library.tuples.TuplesImpl
import viper.silver.{ast => vpr}

class TryFoldDynamicAlternativeFilterTests extends AnyFunSuite with Matchers {

  private val tuples = new TuplesImpl

  private def pred(name: String): PredicateNode = PredicateNode(name)
  private def bool(value: Boolean): BoolLiteralNode = BoolLiteralNode(value)

  private val dynamicFamilyMetadata = DynamicPredicateFamilyMetadata(
    silverName = "dynamic_pred_0",
    gobraName = "Mem",
    alternatives = Vector(
      DynamicPredicateAlternativeMetadata(typeKey = "0", typeExprRepr = "0", trivialBody = true),
      DynamicPredicateAlternativeMetadata(typeKey = "4", typeExprRepr = "4", trivialBody = false),
    ),
  )

  private val translationMetadata = TryFoldTranslationMetadata(
    dynamicPredicateMap = Map("dynamic_pred_0" -> "Mem"),
    dynamicPredicateFamilies = Map("dynamic_pred_0" -> dynamicFamilyMetadata),
  )

  private def boxedInterface(valueName: String, typeTag: BigInt): vpr.Exp =
    tuples.create(Vector(vpr.LocalVar(valueName, vpr.Ref)(), vpr.IntLit(typeTag)()))()

  private def targetEntry(
                           nodeName: String,
                           argExp: Option[vpr.Exp],
                           index: Int = 0,
                         ): TryFoldTargetPermissionExtractor.TargetPermissionEntry =
    TryFoldTargetPermissionExtractor.TargetPermissionEntry(
      index = index,
      nodeKind = "predicate",
      nodeName = nodeName,
      nodeId = s"pred:$nodeName",
      arguments = Vector("arg0"),
      argumentsExp = argExp.map(exp => Vector(exp)),
      access = s"$nodeName(arg0)",
      permissionTerm = None,
      evaluatedPermission = None,
      evaluationKind = "missing",
      extractionSource = "test",
      matchesReasonLocation = false,
    )

  private def sourceEntry(
                           nodeName: String,
                           argExp: Option[vpr.Exp],
                         ): SourcePermissionEntry =
    SourcePermissionEntry(
      index = 0,
      nodeKind = "predicate",
      nodeName = nodeName,
      nodeId = s"predicate:$nodeName",
      chunkKind = "BasicChunk",
      chunk = s"$nodeName(arg0)",
      permissionTerm = "",
      bodyPermissionTerm = None,
      conditionTerm = None,
      conditionEvaluation = None,
      evaluatedPermission = None,
      evaluatedBodyPermission = None,
      evaluationKind = "symbolic",
      arguments = Vector("arg0"),
      argumentsExp = argExp.map(exp => Vector(exp)),
      singletonArguments = Vector.empty,
      singletonArgumentsExp = None,
    )

  private def endpoints(
                         targetPermissions: Vector[TryFoldTargetPermissionExtractor.TargetPermissionEntry] = Vector.empty,
                         sourcePermissions: Vector[SourcePermissionEntry] = Vector.empty,
                       ): TryFoldFailureContextExtractor.FailureEndpoints =
    TryFoldFailureContextExtractor.FailureEndpoints(
      sources = Set(bool(value = true)),
      target = pred("dynamic_pred_0"),
      sourcePermissions = sourcePermissions,
      targetPermissions = targetPermissions,
    )

  private def edge(to: DependencyNode, label: DynamicAlternativeLabel): DependencyEdge =
    DependencyEdge(
      from = pred("dynamic_pred_0"),
      to = to,
      kind = if (to.isInstanceOf[BoolLiteralNode]) LiteralDependency else PredicateDependency,
      labels = Set(label),
    )

  test("prunes true-to-dynamic path when branch-local dynamic type is incompatible") {
    val path = TryFoldPathExplorer.Path(
      source = bool(value = true),
      target = pred("dynamic_pred_0"),
      steps = Vector(
        TryFoldPathExplorer.PathStep(
          from = bool(value = true),
          to = pred("dynamic_pred_0"),
          directive = TryFoldWorklistEngine.AnnotationDirective(
            action = TryFoldWorklistEngine.FoldAnnotation,
            predicateName = "dynamic_pred_0",
          ),
          edge = edge(bool(value = true), DynamicAlternativeLabel("0")),
        )
      ),
    )

    val decision = TryFoldDynamicAlternativeFilter.analyzePath(
      pathIndex = 0,
      path = path,
      endpoints = endpoints(targetPermissions = Vector(targetEntry("dynamic_pred_0", Some(boxedInterface("tmp", 4))))),
      translationMetadata = translationMetadata,
      storeBindings = Map.empty,
    )

    decision.keep shouldBe false
    decision.mismatch.map(_.requiredTypeKeys) shouldBe Some(Vector("0"))
    decision.mismatch.map(_.resolvedTypeKeys) shouldBe Some(Vector("4"))
  }

  test("keeps bytes-to-dynamic path when branch-local dynamic type is compatible") {
    val path = TryFoldPathExplorer.Path(
      source = pred("Bytes"),
      target = pred("dynamic_pred_0"),
      steps = Vector(
        TryFoldPathExplorer.PathStep(
          from = pred("Bytes"),
          to = pred("dynamic_pred_0"),
          directive = TryFoldWorklistEngine.AnnotationDirective(
            action = TryFoldWorklistEngine.FoldAnnotation,
            predicateName = "dynamic_pred_0",
          ),
          edge = edge(pred("Bytes"), DynamicAlternativeLabel("4")),
        )
      ),
    )

    val decision = TryFoldDynamicAlternativeFilter.analyzePath(
      pathIndex = 0,
      path = path,
      endpoints = endpoints(targetPermissions = Vector(targetEntry("dynamic_pred_0", Some(boxedInterface("tmp", 4))))),
      translationMetadata = translationMetadata,
      storeBindings = Map.empty,
    )

    decision.keep shouldBe true
    decision.mismatch shouldBe None
  }

  test("keeps direct true path for HostNone-like branch") {
    val path = TryFoldPathExplorer.Path(
      source = bool(value = true),
      target = pred("dynamic_pred_0"),
      steps = Vector(
        TryFoldPathExplorer.PathStep(
          from = bool(value = true),
          to = pred("dynamic_pred_0"),
          directive = TryFoldWorklistEngine.AnnotationDirective(
            action = TryFoldWorklistEngine.FoldAnnotation,
            predicateName = "dynamic_pred_0",
          ),
          edge = edge(bool(value = true), DynamicAlternativeLabel("0")),
        )
      ),
    )

    val decision = TryFoldDynamicAlternativeFilter.analyzePath(
      pathIndex = 0,
      path = path,
      endpoints = endpoints(targetPermissions = Vector(targetEntry("dynamic_pred_0", Some(boxedInterface("tmp", 0))))),
      translationMetadata = translationMetadata,
      storeBindings = Map.empty,
    )

    decision.keep shouldBe true
  }

  test("does not prune when concrete type extraction is unknown") {
    val path = TryFoldPathExplorer.Path(
      source = bool(value = true),
      target = pred("dynamic_pred_0"),
      steps = Vector(
        TryFoldPathExplorer.PathStep(
          from = bool(value = true),
          to = pred("dynamic_pred_0"),
          directive = TryFoldWorklistEngine.AnnotationDirective(
            action = TryFoldWorklistEngine.FoldAnnotation,
            predicateName = "dynamic_pred_0",
          ),
          edge = edge(bool(value = true), DynamicAlternativeLabel("0")),
        )
      ),
    )

    val decision = TryFoldDynamicAlternativeFilter.analyzePath(
      pathIndex = 0,
      path = path,
      endpoints = endpoints(targetPermissions = Vector(targetEntry("dynamic_pred_0", None))),
      translationMetadata = translationMetadata,
      storeBindings = Map.empty,
    )

    decision.keep shouldBe true
    decision.resolvedTypeFacts shouldBe empty
  }

  test("source permission entries can provide compatible dynamic type facts") {
    val path = TryFoldPathExplorer.Path(
      source = pred("Bytes"),
      target = pred("dynamic_pred_0"),
      steps = Vector(
        TryFoldPathExplorer.PathStep(
          from = pred("Bytes"),
          to = pred("dynamic_pred_0"),
          directive = TryFoldWorklistEngine.AnnotationDirective(
            action = TryFoldWorklistEngine.FoldAnnotation,
            predicateName = "dynamic_pred_0",
          ),
          edge = edge(pred("Bytes"), DynamicAlternativeLabel("4")),
        )
      ),
    )

    val decision = TryFoldDynamicAlternativeFilter.analyzePath(
      pathIndex = 0,
      path = path,
      endpoints = endpoints(sourcePermissions = Vector(sourceEntry("dynamic_pred_0", Some(boxedInterface("tmp", 4))))),
      translationMetadata = translationMetadata,
      storeBindings = Map.empty,
    )

    decision.keep shouldBe true
    decision.resolvedTypeFacts.flatMap(_.typeKeys) shouldBe Vector("4")
  }
}
