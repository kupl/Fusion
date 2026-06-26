package viper.gobra.tryfold

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import viper.gobra.translator.library.tuples.TuplesImpl
import viper.silver.{ast => vpr}

class PredicateDependencyGraphBuilderTests extends AnyFunSuite with Matchers {

  private def predicateAccess(name: String, args: Seq[vpr.Exp]): vpr.PredicateAccessPredicate =
    vpr.PredicateAccessPredicate(vpr.PredicateAccess(args, name)(), Some(vpr.FullPerm()()))()

  private def fieldAccess(field: vpr.Field, receiver: vpr.Exp): vpr.FieldAccessPredicate =
    vpr.FieldAccessPredicate(vpr.FieldAccess(receiver, field)(), Some(vpr.FullPerm()()))()

  test("ours graph collects dynamic predicate dependencies conservatively") {
    val recvDecl = vpr.LocalVarDecl("i", vpr.Ref)()
    val recv = recvDecl.localVar
    val otherDecl = vpr.LocalVarDecl("j", vpr.Ref)()
    val other = otherDecl.localVar
    val f = vpr.Field("f", vpr.Int)()

    val accessToB = predicateAccess("B", Seq(recv))
    val accessToU = predicateAccess("U", Seq(recv))
    val accessToF = fieldAccess(f, recv)

    val condA = vpr.EqCmp(recv, vpr.NullLit()())()
    val condB = vpr.EqCmp(recv, other)()
    val body = vpr.CondExp(
      condA,
      accessToB,
      vpr.CondExp(
        condB,
        vpr.And(accessToB, accessToF)(),
        accessToU
      )()
    )()

    val dynamic = vpr.Predicate("dynamic_pred_0", Seq(recvDecl), Some(body))()
    val b = vpr.Predicate("B", Seq(vpr.LocalVarDecl("x", vpr.Ref)()), None)()
    val u = vpr.Predicate("U", Seq(vpr.LocalVarDecl("x", vpr.Ref)()), None)()

    val program = vpr.Program(
      domains = Seq.empty,
      fields = Seq(f),
      functions = Seq.empty,
      predicates = Seq(dynamic, b, u),
      methods = Seq.empty,
      extensions = Seq.empty
    )()

    val graph = PredicateDependencyGraphBuilder.build(program)

    val edgeToB = graph.findEdge("dynamic_pred_0", "pred:B")
    val edgeToF = graph.findEdge("dynamic_pred_0", "field:f")
    val edgeToU = graph.findEdge("dynamic_pred_0", "pred:U")
    edgeToB.isDefined shouldBe true
    edgeToF.isDefined shouldBe true
    edgeToU.isDefined shouldBe true
    edgeToB.get.labels shouldBe Set(UnlabeledEdge)
    edgeToF.get.labels shouldBe Set(UnlabeledEdge)
    edgeToU.get.labels shouldBe Set(UnlabeledEdge)
    edgeToB.get.templates should not be empty
    edgeToF.get.templates should not be empty
    edgeToU.get.templates should not be empty
  }

  test("graph traversal recursively collects predicate dependencies under quantifiers") {
    val recvDecl = vpr.LocalVarDecl("r", vpr.Ref)()
    val recv = recvDecl.localVar
    val kDecl = vpr.LocalVarDecl("k", vpr.Int)()
    val k = kDecl.localVar

    val cond = vpr.And(vpr.GeCmp(k, vpr.IntLit(0)())(), vpr.LtCmp(k, vpr.IntLit(10)())())()
    val quantifiedBody = vpr.Forall(
      variables = Seq(kDecl),
      triggers = Seq.empty,
      exp = vpr.Implies(cond, predicateAccess("C", Seq(recv)))()
    )()

    val a = vpr.Predicate("A", Seq(recvDecl), Some(vpr.And(predicateAccess("B", Seq(recv)), quantifiedBody)()))()
    val b = vpr.Predicate("B", Seq(vpr.LocalVarDecl("x", vpr.Ref)()), None)()
    val c = vpr.Predicate("C", Seq(vpr.LocalVarDecl("x", vpr.Ref)()), None)()

    val program = vpr.Program(
      domains = Seq.empty,
      fields = Seq.empty,
      functions = Seq.empty,
      predicates = Seq(a, b, c),
      methods = Seq.empty,
      extensions = Seq.empty
    )()

    val graph = PredicateDependencyGraphBuilder.build(program)

    val edgeToB = graph.findEdge("A", "pred:B")
    val edgeToC = graph.findEdge("A", "pred:C")
    edgeToB.isDefined shouldBe true
    edgeToC.isDefined shouldBe true
    edgeToB.get.kind shouldBe PredicateDependency
    edgeToB.get.labels shouldBe Set(UnlabeledEdge)
    edgeToB.get.templates should not be empty
    edgeToC.get.kind shouldBe PredicateDependency
    edgeToC.get.labels shouldBe Set(UnlabeledEdge)
    edgeToC.get.templates should not be empty
  }

  test("graph builder labels dynamic predicate alternatives by concrete type branch") {
    val tuples = new TuplesImpl
    val recvDecl = vpr.LocalVarDecl("i", tuples.typ(Vector(vpr.Ref, vpr.Int)))()
    val recv = recvDecl.localVar
    val dynType = tuples.get(recv, 1, 2)()
    val accessToBytes = predicateAccess("Bytes", Seq(recv))
    val typeNone = vpr.IntLit(0)()
    val typeIPv4 = vpr.IntLit(4)()

    val body = vpr.CondExp(
      vpr.EqCmp(dynType, typeNone)(),
      vpr.TrueLit()(),
      vpr.CondExp(
        vpr.EqCmp(dynType, typeIPv4)(),
        accessToBytes,
        predicateAccess("Unknown", Seq(recv))
      )()
    )()

    val dynamic = vpr.Predicate("dynamic_pred_0", Seq(recvDecl), Some(body))()
    val bytes = vpr.Predicate("Bytes", Seq(vpr.LocalVarDecl("x", recv.typ)()), None)()
    val unknown = vpr.Predicate("Unknown", Seq(vpr.LocalVarDecl("x", recv.typ)()), None)()

    val program = vpr.Program(
      domains = Seq.empty,
      fields = Seq.empty,
      functions = Seq.empty,
      predicates = Seq(dynamic, bytes, unknown),
      methods = Seq.empty,
      extensions = Seq.empty
    )()

    val metadata = TryFoldTranslationMetadata(
      dynamicPredicateMap = Map("dynamic_pred_0" -> "Mem"),
      dynamicPredicateFamilies = Map(
        "dynamic_pred_0" -> DynamicPredicateFamilyMetadata(
          silverName = "dynamic_pred_0",
          gobraName = "Mem",
          alternatives = Vector(
            DynamicPredicateAlternativeMetadata(typeKey = "0", typeExprRepr = "0", trivialBody = true),
            DynamicPredicateAlternativeMetadata(typeKey = "4", typeExprRepr = "4", trivialBody = false),
          ),
        )
      ),
    )

    val graph = PredicateDependencyGraphBuilder.build(program, metadata)

    val edgeToTrue = graph.findEdge("dynamic_pred_0", "bool:true")
    val edgeToBytes = graph.findEdge("dynamic_pred_0", "pred:Bytes")
    val edgeToUnknown = graph.findEdge("dynamic_pred_0", "pred:Unknown")

    edgeToTrue.isDefined shouldBe true
    edgeToBytes.isDefined shouldBe true
    edgeToUnknown.isDefined shouldBe true
    edgeToTrue.get.labels shouldBe Set(DynamicAlternativeLabel("0"))
    edgeToBytes.get.labels shouldBe Set(DynamicAlternativeLabel("4"))
    edgeToUnknown.get.labels shouldBe Set(UnlabeledEdge)
  }

  test("graph builder adds true-edge for pure dynamic alternative without heap dependencies") {
    val tuples = new TuplesImpl
    val recvDecl = vpr.LocalVarDecl("i", tuples.typ(Vector(vpr.Ref, vpr.Int)))()
    val recv = recvDecl.localVar
    val dynType = tuples.get(recv, 1, 2)()
    val pureLenCheck = vpr.EqCmp(vpr.IntLit(0)(), vpr.IntLit(0)())()
    val accessToBytes = predicateAccess("Bytes", Seq(recv))

    val body = vpr.CondExp(
      vpr.EqCmp(dynType, vpr.IntLit(0)())(),
      pureLenCheck,
      vpr.CondExp(
        vpr.EqCmp(dynType, vpr.IntLit(4)())(),
        accessToBytes,
        predicateAccess("Unknown", Seq(recv))
      )()
    )()

    val dynamic = vpr.Predicate("dynamic_pred_0", Seq(recvDecl), Some(body))()
    val bytes = vpr.Predicate("Bytes", Seq(vpr.LocalVarDecl("x", recv.typ)()), None)()
    val unknown = vpr.Predicate("Unknown", Seq(vpr.LocalVarDecl("x", recv.typ)()), None)()

    val program = vpr.Program(
      domains = Seq.empty,
      fields = Seq.empty,
      functions = Seq.empty,
      predicates = Seq(dynamic, bytes, unknown),
      methods = Seq.empty,
      extensions = Seq.empty
    )()

    val metadata = TryFoldTranslationMetadata(
      dynamicPredicateMap = Map("dynamic_pred_0" -> "Mem"),
      dynamicPredicateFamilies = Map(
        "dynamic_pred_0" -> DynamicPredicateFamilyMetadata(
          silverName = "dynamic_pred_0",
          gobraName = "Mem",
          alternatives = Vector(
            DynamicPredicateAlternativeMetadata(typeKey = "0", typeExprRepr = "0", trivialBody = false),
            DynamicPredicateAlternativeMetadata(typeKey = "4", typeExprRepr = "4", trivialBody = false),
          ),
        )
      ),
    )

    val graph = PredicateDependencyGraphBuilder.build(program, metadata)
    val edgeToTrue = graph.findEdge("dynamic_pred_0", "bool:true")

    edgeToTrue.isDefined shouldBe true
    edgeToTrue.get.labels shouldBe Set(DynamicAlternativeLabel("0"))
  }
}
