package viper.gobra.tryfold

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import viper.gobra.ast.{internal => in}
import viper.gobra.backend.TryFoldSourcePermissionExtractor.PermissionAmount
import viper.gobra.reporting.Source
import viper.gobra.theory.Addressability
import viper.gobra.translator.Names
import viper.silver.{ast => vpr}

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import scala.collection.immutable.SortedSet

class TryFoldGobraAnnotationBacktranslatorTests extends AnyFunSuite with Matchers {

  private val srcInfo: Source.Parser.Info = Source.Parser.Internal

  private def tinyProgramForBacktranslation: in.Program = {
    val itf = in.InterfaceT("I", Addressability.Exclusive)
    val impl = in.DefinedT("Host", Addressability.Exclusive)

    val itfPredProxy = in.MPredicateProxy("Mem", "Mem_iface_abcdef_MI")(srcInfo)
    val implPredProxy = in.MPredicateProxy("Mem", "Mem_impl_abcdef_MHost")(srcInfo)

    val itfReceiver = in.Parameter.In("recv", itf)(srcInfo)
    val implReceiver = in.Parameter.In("recv", impl)(srcInfo)

    val mpItf = in.MPredicate(
      receiver = itfReceiver,
      name = itfPredProxy,
      args = Vector.empty,
      body = None,
    )(srcInfo)

    val mpImpl = in.MPredicate(
      receiver = implReceiver,
      name = implPredProxy,
      args = Vector.empty,
      body = None,
    )(srcInfo)

    val fpProxy = in.FPredicateProxy("Bytes_b4eddfca_F")(srcInfo)
    val fpArg = in.Parameter.In("s", in.SliceT(in.BoolT(Addressability.Exclusive), Addressability.Exclusive))(srcInfo)
    val fp = in.FPredicate(
      name = fpProxy,
      args = Vector(fpArg),
      body = None,
    )(srcInfo)

    val table = new in.LookupTable(
      definedMPredicates = Map(
        itfPredProxy -> mpItf,
        implPredProxy -> mpImpl,
      ),
      definedFPredicates = Map(
        fpProxy -> fp,
      ),
      directMemberProxies = Map(
        itf -> SortedSet[in.MemberProxy](itfPredProxy),
        impl -> SortedSet[in.MemberProxy](implPredProxy),
      ),
      directInterfaceImplementations = Map(
        itf -> SortedSet[in.Type](impl),
      ),
    )

    in.Program(
      types = Vector.empty,
      members = Vector(mpItf, mpImpl, fp),
      table = table,
    )(srcInfo)
  }

  private def emptyTranslatedProgram: vpr.Program =
    vpr.Program(
      domains = Seq.empty,
      fields = Seq.empty,
      functions = Seq.empty,
      predicates = Seq.empty,
      methods = Seq.empty,
      extensions = Seq.empty,
    )()

  private def translatedProgramWithReturnMarker(methodName: String, markerLabel: String): vpr.Program = {
    val res = vpr.LocalVarDecl("res_V0", vpr.Ref)()
    val resCn = vpr.LocalVarDecl("res_V0_CN1", vpr.Ref)()
    val tmp = vpr.LocalVarDecl("tmp_V2", vpr.Ref)()

    val boxedTmp = vpr.FuncApp("box_Poly", Seq(tmp.localVar))(vpr.NoPosition, vpr.NoInfo, vpr.Ref, vpr.NoTrafos)
    val tupleExpr = vpr.FuncApp("tuple2", Seq(boxedTmp, vpr.NullLit()()))(vpr.NoPosition, vpr.NoInfo, vpr.Ref, vpr.NoTrafos)

    val method = vpr.Method(
      name = methodName,
      formalArgs = Seq.empty,
      formalReturns = Seq(res),
      pres = Seq.empty,
      posts = Seq.empty,
      body = Some(
        vpr.Seqn(
          Seq(
            vpr.LocalVarAssign(resCn.localVar, tupleExpr)(),
            vpr.Label(markerLabel, Seq.empty)(),
            vpr.LocalVarAssign(res.localVar, resCn.localVar)(),
          ),
          Seq(resCn, tmp),
        )()
      ),
    )()

    vpr.Program(
      domains = Seq.empty,
      fields = Seq.empty,
      functions = Seq.empty,
      predicates = Seq.empty,
      methods = Seq(method),
      extensions = Seq.empty,
    )()
  }

  private def mkFuncApp(name: String, args: Seq[vpr.Exp], typ: vpr.Type): vpr.FuncApp =
    vpr.FuncApp(name, args)(vpr.NoPosition, vpr.NoInfo, typ, vpr.NoTrafos)

  private def mkTuple2(first: vpr.Exp, second: vpr.Exp): vpr.FuncApp =
    mkFuncApp("tuple2", Seq(first, second), vpr.Ref)

  test("renders dynamic and free predicate annotations to Gobra-level strings") {
    val program = tinyProgramForBacktranslation
    val hV0 = vpr.LocalVar("h_V0", vpr.Ref)()
    val boxedH = mkFuncApp("box_Poly", Seq(hV0), vpr.Ref)
    val dynArg = mkTuple2(boxedH, vpr.NullLit()())
    val lenH = mkFuncApp("slen", Seq(hV0), vpr.Int)

    val sequence = TryFoldInsertionPlanner.PlannedAnnotationSequence(
      originalSequence = TryFoldWorklistEngine.AnnotationSequence(Vector.empty),
      plannedSequence = TryFoldWorklistEngine.AnnotationSequence(Vector(
        TryFoldWorklistEngine.AnnotationDirective(
          action = TryFoldWorklistEngine.DeferFoldAnnotation,
          predicateName = "dynamic_pred_0",
          args = Vector("(tuple2((box_Poly(h_V0): Ref), HostIPv4_8e445fc3_T_Types()): Tuple2[Ref, Types])"),
          argsExp = Some(Vector(dynArg)),
          permission = Some(PermissionAmount("1/32768", "0.000030517578125")),
        ),
        TryFoldWorklistEngine.AnnotationDirective(
          action = TryFoldWorklistEngine.DeferFoldAnnotation,
          predicateName = "Bytes_b4eddfca_F",
          args = Vector(
            "(unbox_Poly((get0of2((tuple2((box_Poly(h_V0): Ref), HostIPv4_8e445fc3_T_Types()): Tuple2[Ref, Types])): Ref)): Slice[Ref])",
            "0",
            "(slen((unbox_Poly((get0of2((tuple2((box_Poly(h_V0): Ref), HostIPv4_8e445fc3_T_Types()): Tuple2[Ref, Types])): Ref)): Slice[Ref])): Int)",
          ),
          argsExp = Some(Vector(hV0, vpr.IntLit(0)(), lenH)),
          permission = Some(PermissionAmount("1/32768", "0.000030517578125")),
        ),
      )),
      insertionAnchor = TryFoldInsertionPlanner.InsertionAnchor(
        kind = TryFoldInsertionPlanner.ErrorLocationAnchor,
        sourceFile = None,
        sourceLine = None,
        sourceColumn = None,
        sourceLocation = None,
        returnMarkerLabel = None,
        returnLine = None,
        returnColumn = None,
      ),
      isPostconditionFailure = true,
      foldToDeferRewriteApplied = true,
    )

    val rendered = TryFoldGobraAnnotationBacktranslator.renderBatch(
      plannedSequences = Vector(sequence),
      rootProgram = program,
      translatedProgram = emptyTranslatedProgram,
    )

    rendered.failed shouldBe empty
    rendered.succeeded should have size 1

    val lines = rendered.succeeded.head.annotationLines
    lines should contain("defer fold acc(h.Mem(), 1/32768)")
    lines should contain("defer fold acc(Bytes(h, 0, len(h)), 1/32768)")
  }

  test("prefers translation-time dynamic predicate mappings when provided") {
    val emptyProgram = in.Program(
      types = Vector.empty,
      members = Vector.empty,
      table = new in.LookupTable(),
    )(srcInfo)
    val hV0 = vpr.LocalVar("h_V0", vpr.Ref)()
    val boxedH = mkFuncApp("box_Poly", Seq(hV0), vpr.Ref)
    val dynArg = mkTuple2(boxedH, vpr.NullLit()())

    val sequence = TryFoldInsertionPlanner.PlannedAnnotationSequence(
      originalSequence = TryFoldWorklistEngine.AnnotationSequence(Vector.empty),
      plannedSequence = TryFoldWorklistEngine.AnnotationSequence(Vector(
        TryFoldWorklistEngine.AnnotationDirective(
          action = TryFoldWorklistEngine.UnfoldAnnotation,
          predicateName = "dynamic_pred_0",
          args = Vector("(tuple2((box_Poly(h_V0): Ref), HostIPv4_8e445fc3_T_Types()): Tuple2[Ref, Types])"),
          argsExp = Some(Vector(dynArg)),
          permission = Some(PermissionAmount("1/32768", "0.000030517578125")),
        ),
      )),
      insertionAnchor = TryFoldInsertionPlanner.InsertionAnchor(
        kind = TryFoldInsertionPlanner.ErrorLocationAnchor,
        sourceFile = None,
        sourceLine = None,
        sourceColumn = None,
        sourceLocation = None,
        returnMarkerLabel = None,
        returnLine = None,
        returnColumn = None,
      ),
      isPostconditionFailure = false,
      foldToDeferRewriteApplied = false,
    )

    val rendered = TryFoldGobraAnnotationBacktranslator.renderBatch(
      plannedSequences = Vector(sequence),
      rootProgram = emptyProgram,
      translatedProgram = emptyTranslatedProgram,
      translationMetadata = Some(TryFoldTranslationMetadata(dynamicPredicateMap = Map("dynamic_pred_0" -> "Mem"))),
    )

    rendered.failed shouldBe empty
    rendered.succeeded should have size 1
    rendered.succeeded.head.annotationLines should contain("unfold acc(h.Mem(), 1/32768)")
  }

  test("keeps failures separate when predicate cannot be mapped") {
    val program = tinyProgramForBacktranslation

    val sequence = TryFoldInsertionPlanner.PlannedAnnotationSequence(
      originalSequence = TryFoldWorklistEngine.AnnotationSequence(Vector.empty),
      plannedSequence = TryFoldWorklistEngine.AnnotationSequence(Vector(
        TryFoldWorklistEngine.AnnotationDirective(
          action = TryFoldWorklistEngine.UnfoldAnnotation,
          predicateName = "unknown_predicate_0",
          args = Vector("x"),
          permission = None,
        )
      )),
      insertionAnchor = TryFoldInsertionPlanner.InsertionAnchor(
        kind = TryFoldInsertionPlanner.ErrorLocationAnchor,
        sourceFile = None,
        sourceLine = None,
        sourceColumn = None,
        sourceLocation = None,
        returnMarkerLabel = None,
        returnLine = None,
        returnColumn = None,
      ),
      isPostconditionFailure = false,
      foldToDeferRewriteApplied = false,
    )

    val rendered = TryFoldGobraAnnotationBacktranslator.renderBatch(
      plannedSequences = Vector(sequence),
      rootProgram = program,
      translatedProgram = emptyTranslatedProgram,
    )

    rendered.succeeded shouldBe empty
    rendered.failed should have size 1
    rendered.failed.head.reason should include("No Gobra-level predicate mapping")
    rendered.failed.head.silverAnnotationLines should have size 1
  }

  test("uses return marker context to substitute result variable before expression normalization") {
    val program = tinyProgramForBacktranslation
    val methodName = "HostFromIP_8e445fc3_F"
    val markerLabel = s"tryfold_ret_m${Names.hash(methodName)}_i0_l503_c2"
    val translated = translatedProgramWithReturnMarker(methodName, markerLabel)
    val resLocal = vpr.LocalVar("res_V0", vpr.Ref)()
    val get0Of2 = mkFuncApp("get0of2", Seq(resLocal), vpr.Ref)
    val unboxed = mkFuncApp("unbox_Poly", Seq(get0Of2), vpr.Ref)

    val sequence = TryFoldInsertionPlanner.PlannedAnnotationSequence(
      originalSequence = TryFoldWorklistEngine.AnnotationSequence(Vector.empty),
      plannedSequence = TryFoldWorklistEngine.AnnotationSequence(Vector(
        TryFoldWorklistEngine.AnnotationDirective(
          action = TryFoldWorklistEngine.DeferFoldAnnotation,
          predicateName = "Bytes_b4eddfca_F",
          args = Vector(
            "(unbox_Poly((get0of2((res_V0): Ref)): Ref): Slice[Ref])",
          ),
          argsExp = Some(Vector(unboxed)),
          permission = Some(PermissionAmount("1/32768", "0.000030517578125")),
        ),
      )),
      insertionAnchor = TryFoldInsertionPlanner.InsertionAnchor(
        kind = TryFoldInsertionPlanner.ReturnMarkerAnchor,
        sourceFile = None,
        sourceLine = None,
        sourceColumn = None,
        sourceLocation = None,
        returnMarkerLabel = Some(markerLabel),
        returnLine = Some(503),
        returnColumn = Some(2),
      ),
      isPostconditionFailure = true,
      foldToDeferRewriteApplied = true,
    )

    val rendered = TryFoldGobraAnnotationBacktranslator.renderBatch(
      plannedSequences = Vector(sequence),
      rootProgram = program,
      translatedProgram = translated,
    )

    rendered.failed shouldBe empty
    rendered.succeeded should have size 1
    rendered.succeeded.head.annotationLines should contain("defer fold acc(Bytes(tmp), 1/32768)")
  }

  test("qualifies imported free predicates with source-file import alias when package hash is known") {
    val program = tinyProgramForBacktranslation
    val tmpFile = Files.createTempFile("tryfold-backtranslate-alias-", ".go")
    try {
      val goContent =
        """package addr
          |
          |import (
          |    //@ sl "github.com/scionproto/scion/verification/utils/slices"
          |)
          |
          |func f() {
          |    tmp := nil
          |    _ = tmp
          |}
          |""".stripMargin
      Files.write(tmpFile, goContent.getBytes(StandardCharsets.UTF_8))

      val sequence = TryFoldInsertionPlanner.PlannedAnnotationSequence(
        originalSequence = TryFoldWorklistEngine.AnnotationSequence(Vector.empty),
        plannedSequence = TryFoldWorklistEngine.AnnotationSequence(Vector(
          TryFoldWorklistEngine.AnnotationDirective(
            action = TryFoldWorklistEngine.DeferFoldAnnotation,
            predicateName = "Bytes_b4eddfca_F",
            args = Vector("tmp_V2"),
            argsExp = Some(Vector(vpr.LocalVar("tmp_V2", vpr.Ref)())),
            permission = Some(PermissionAmount("1/32768", "0.000030517578125")),
          ),
        )),
        insertionAnchor = TryFoldInsertionPlanner.InsertionAnchor(
          kind = TryFoldInsertionPlanner.ErrorLocationAnchor,
          sourceFile = Some(tmpFile.toAbsolutePath.normalize.toString),
          sourceLine = Some(7),
          sourceColumn = Some(1),
          sourceLocation = Some("host.go@10.1"),
          returnMarkerLabel = None,
          returnLine = None,
          returnColumn = None,
        ),
        isPostconditionFailure = false,
        foldToDeferRewriteApplied = false,
      )

      val rendered = TryFoldGobraAnnotationBacktranslator.renderBatch(
        plannedSequences = Vector(sequence),
        rootProgram = program,
        translatedProgram = emptyTranslatedProgram,
        renderEnvironment = TryFoldGobraAnnotationBacktranslator.RenderEnvironment(
          packageNameByViperId = Map("b4eddfca" -> "slices")
        ),
      )

      rendered.failed shouldBe empty
      rendered.succeeded should have size 1
      rendered.succeeded.head.annotationLines should contain("defer fold acc(sl.Bytes(tmp), 1/32768)")
    } finally {
      Files.deleteIfExists(tmpFile)
    }
  }

  test("post-return dynamic predicate backtranslation should not re-wrap receiver into nested tuple") {
    val program = tinyProgramForBacktranslation
    val methodName = "HostFromIP_8e445fc3_F"
    val markerLabel = s"tryfold_ret_m${Names.hash(methodName)}_i0_l9_c3"
    val translated = translatedProgramWithReturnMarker(methodName, markerLabel)

    val tmpFile = Files.createTempFile("tryfold-backtranslate-dyn-ret-", ".go")
    try {
      val goContent =
        """package addr
          |
          |func HostFromIP() (res HostAddr) {
          |	if true {
          |		tmp := HostIPv4(nil)
          |		return tmp
          |	}
          |	tmp := HostIPv6(nil)
          |	return tmp
          |}
          |""".stripMargin
      Files.write(tmpFile, goContent.getBytes(StandardCharsets.UTF_8))

      val sequence = TryFoldInsertionPlanner.PlannedAnnotationSequence(
        originalSequence = TryFoldWorklistEngine.AnnotationSequence(Vector.empty),
        plannedSequence = TryFoldWorklistEngine.AnnotationSequence(Vector(
          TryFoldWorklistEngine.AnnotationDirective(
            action = TryFoldWorklistEngine.DeferFoldAnnotation,
            predicateName = "dynamic_pred_0",
            args = Vector("res_V0"),
            argsExp = Some(Vector(vpr.LocalVar("res_V0", vpr.Ref)())),
            permission = Some(PermissionAmount("1/1", "1")),
          ),
        )),
        insertionAnchor = TryFoldInsertionPlanner.InsertionAnchor(
          kind = TryFoldInsertionPlanner.ReturnMarkerAnchor,
          sourceFile = Some(tmpFile.toAbsolutePath.normalize.toString),
          sourceLine = Some(3),
          sourceColumn = Some(1),
          sourceLocation = Some("host.go@3.1--3.20"),
          returnMarkerLabel = Some(markerLabel),
          returnLine = Some(6),
          returnColumn = Some(3),
        ),
        isPostconditionFailure = true,
        foldToDeferRewriteApplied = true,
      )

      // This mimics the symbolic-store aliases observed in HostFromIP@493 traces.
      val symbolicStoreByLocal = Map(
        "tmp_V2" -> vpr.LocalVar("res_V0@21@47", vpr.Ref)(),
        "res_V0" -> vpr.LocalVar("res_V0_CN1@41@47", vpr.Ref)(),
        "res_V0_CN1" -> vpr.LocalVar("res_V0_CN1@41@47", vpr.Ref)(),
      )

      val rendered = TryFoldGobraAnnotationBacktranslator.renderBatch(
        plannedSequences = Vector(sequence),
        rootProgram = program,
        translatedProgram = translated,
        translationMetadata = Some(TryFoldTranslationMetadata(dynamicPredicateMap = Map("dynamic_pred_0" -> "Mem"))),
        symbolicStoreByLocal = symbolicStoreByLocal,
      )

      withClue(s"Backtranslation failures: ${rendered.failed.map(_.reason)}") {
        rendered.failed shouldBe empty
      }
      rendered.succeeded should have size 1
      rendered.succeeded.head.annotationLines should contain("defer fold acc(tmp.Mem(), 1/1)")
    } finally {
      Files.deleteIfExists(tmpFile)
    }
  }

  test("non-post reverse alias expansion should resolve internal temporary to in-scope local") {
    val program = tinyProgramForBacktranslation
    val tmpFile = Files.createTempFile("tryfold-backtranslate-reverse-alias-", ".go")
    try {
      val goContent =
        """package addr
          |
          |func Copy() {
          |	tmp := HostIPv4(nil)
          |	_ = tmp
          |}
          |""".stripMargin
      Files.write(tmpFile, goContent.getBytes(StandardCharsets.UTF_8))

      val sequence = TryFoldInsertionPlanner.PlannedAnnotationSequence(
        originalSequence = TryFoldWorklistEngine.AnnotationSequence(Vector.empty),
        plannedSequence = TryFoldWorklistEngine.AnnotationSequence(Vector(
          TryFoldWorklistEngine.AnnotationDirective(
            action = TryFoldWorklistEngine.FoldAnnotation,
            predicateName = "dynamic_pred_0",
            args = Vector("fn$$1"),
            argsExp = Some(Vector(vpr.LocalVar("fn$$1", vpr.Ref)())),
            permission = Some(PermissionAmount("1/1", "1")),
          ),
        )),
        insertionAnchor = TryFoldInsertionPlanner.InsertionAnchor(
          kind = TryFoldInsertionPlanner.ErrorLocationAnchor,
          sourceFile = Some(tmpFile.toAbsolutePath.normalize.toString),
          sourceLine = Some(5),
          sourceColumn = Some(3),
          sourceLocation = Some("host.go@5.3"),
          returnMarkerLabel = None,
          returnLine = None,
          returnColumn = None,
        ),
        isPostconditionFailure = false,
        foldToDeferRewriteApplied = false,
      )

      val rendered = TryFoldGobraAnnotationBacktranslator.renderBatch(
        plannedSequences = Vector(sequence),
        rootProgram = program,
        translatedProgram = emptyTranslatedProgram,
        translationMetadata = Some(TryFoldTranslationMetadata(dynamicPredicateMap = Map("dynamic_pred_0" -> "Mem"))),
        symbolicStoreByLocal = Map(
          "tmp_V2" -> vpr.LocalVar("fn$$1", vpr.Ref)(),
        ),
      )

      withClue(s"Backtranslation failures: ${rendered.failed.map(_.reason)}") {
        rendered.failed shouldBe empty
      }
      rendered.succeeded should have size 1
      rendered.succeeded.head.annotationLines should contain("fold acc(tmp.Mem(), 1/1)")
    } finally {
      Files.deleteIfExists(tmpFile)
    }
  }

  test("typed store substitution should decode getNofM(i) dynamic receiver to concrete local") {
    val program = tinyProgramForBacktranslation
    val iLocal = vpr.LocalVar("i", vpr.Ref)()
    val get0Of2 = mkFuncApp("get0of2", Seq(iLocal), vpr.Ref)
    val receiverExp = mkFuncApp("unbox_Poly", Seq(get0Of2), vpr.Ref)
    val boxedTmp = mkFuncApp("box_Poly", Seq(vpr.LocalVar("tmp_V3@59", vpr.Ref)()), vpr.Ref)
    val tupleValue = mkTuple2(boxedTmp, vpr.NullLit()())

    val sequence = TryFoldInsertionPlanner.PlannedAnnotationSequence(
      originalSequence = TryFoldWorklistEngine.AnnotationSequence(Vector.empty),
      plannedSequence = TryFoldWorklistEngine.AnnotationSequence(Vector(
        TryFoldWorklistEngine.AnnotationDirective(
          action = TryFoldWorklistEngine.FoldAnnotation,
          predicateName = "dynamic_pred_0",
          args = Vector("unbox_Poly(get0of2(i))"),
          argsExp = Some(Vector(receiverExp)),
          permission = Some(PermissionAmount("1/1", "1")),
        ),
      )),
      insertionAnchor = TryFoldInsertionPlanner.InsertionAnchor(
        kind = TryFoldInsertionPlanner.ErrorLocationAnchor,
        sourceFile = None,
        sourceLine = None,
        sourceColumn = None,
        sourceLocation = None,
        returnMarkerLabel = None,
        returnLine = None,
        returnColumn = None,
      ),
      isPostconditionFailure = false,
      foldToDeferRewriteApplied = false,
    )

    val rendered = TryFoldGobraAnnotationBacktranslator.renderBatch(
      plannedSequences = Vector(sequence),
      rootProgram = program,
      translatedProgram = emptyTranslatedProgram,
      translationMetadata = Some(TryFoldTranslationMetadata(dynamicPredicateMap = Map("dynamic_pred_0" -> "Mem"))),
      symbolicStoreByLocal = Map("i" -> tupleValue),
      symbolicStoreEntries = Vector(
        TryFoldFailureContextExtractor.StoreBindingEntry(
          name = "i",
          typ = vpr.Ref,
          typRepr = "Ref",
          exp = tupleValue,
        )
      ),
    )

    withClue(s"Backtranslation failures: ${rendered.failed.map(_.reason)}") {
      rendered.failed shouldBe empty
    }
    rendered.succeeded should have size 1
    rendered.succeeded.head.annotationLines should contain("fold acc(tmp.Mem(), 1/1)")
  }

  test("post-return aliasing should not rewrite user temporary to different user local") {
    val program = tinyProgramForBacktranslation
    val methodName = "HostFromIP_8e445fc3_F"
    val markerLabel = s"tryfold_ret_m${Names.hash(methodName)}_i0_l503_c2"
    val translated = translatedProgramWithReturnMarker(methodName, markerLabel)

    val sequence = TryFoldInsertionPlanner.PlannedAnnotationSequence(
      originalSequence = TryFoldWorklistEngine.AnnotationSequence(Vector.empty),
      plannedSequence = TryFoldWorklistEngine.AnnotationSequence(Vector(
        TryFoldWorklistEngine.AnnotationDirective(
          action = TryFoldWorklistEngine.DeferFoldAnnotation,
          predicateName = "dynamic_pred_0",
          args = Vector("res_V0"),
          argsExp = Some(Vector(vpr.LocalVar("res_V0", vpr.Ref)())),
          permission = Some(PermissionAmount("1/1", "1")),
        ),
      )),
      insertionAnchor = TryFoldInsertionPlanner.InsertionAnchor(
        kind = TryFoldInsertionPlanner.ReturnMarkerAnchor,
        sourceFile = None,
        sourceLine = None,
        sourceColumn = None,
        sourceLocation = None,
        returnMarkerLabel = Some(markerLabel),
        returnLine = Some(503),
        returnColumn = Some(2),
      ),
      isPostconditionFailure = true,
      foldToDeferRewriteApplied = true,
    )

    val rendered = TryFoldGobraAnnotationBacktranslator.renderBatch(
      plannedSequences = Vector(sequence),
      rootProgram = program,
      translatedProgram = translated,
      translationMetadata = Some(TryFoldTranslationMetadata(dynamicPredicateMap = Map("dynamic_pred_0" -> "Mem"))),
      symbolicStoreByLocal = Map(
        "tmp_V2" -> vpr.LocalVar("ip_V0@2", vpr.Ref)(),
        "res_V0" -> vpr.LocalVar("res_V0_CN1@41@47", vpr.Ref)(),
      ),
    )

    withClue(s"Backtranslation failures: ${rendered.failed.map(_.reason)}") {
      rendered.failed shouldBe empty
    }
    rendered.succeeded should have size 1
    rendered.succeeded.head.annotationLines should contain("defer fold acc(tmp.Mem(), 1/1)")
    rendered.succeeded.head.annotationLines.mkString("\n") should not include "ip.Mem()"
  }

  test("post-return aliasing should not rewrite user temporary to domain function expression") {
    val program = tinyProgramForBacktranslation
    val methodName = "HostFromRaw_8e445fc3_F"
    val markerLabel = s"tryfold_ret_m${Names.hash(methodName)}_i0_l456_c3"
    val translated = translatedProgramWithReturnMarker(methodName, markerLabel)

    val uint16Call = mkFuncApp(
      "Uint16_e2211d10_MbigEndian",
      Seq(vpr.IntLit(0)(), vpr.LocalVar("b_V0@4", vpr.Ref)()),
      vpr.Ref,
    )

    val sequence = TryFoldInsertionPlanner.PlannedAnnotationSequence(
      originalSequence = TryFoldWorklistEngine.AnnotationSequence(Vector.empty),
      plannedSequence = TryFoldWorklistEngine.AnnotationSequence(Vector(
        TryFoldWorklistEngine.AnnotationDirective(
          action = TryFoldWorklistEngine.DeferFoldAnnotation,
          predicateName = "dynamic_pred_0",
          args = Vector("res_V0"),
          argsExp = Some(Vector(vpr.LocalVar("res_V0", vpr.Ref)())),
          permission = Some(PermissionAmount("1/1", "1")),
        ),
      )),
      insertionAnchor = TryFoldInsertionPlanner.InsertionAnchor(
        kind = TryFoldInsertionPlanner.ReturnMarkerAnchor,
        sourceFile = None,
        sourceLine = None,
        sourceColumn = None,
        sourceLocation = None,
        returnMarkerLabel = Some(markerLabel),
        returnLine = Some(456),
        returnColumn = Some(3),
      ),
      isPostconditionFailure = true,
      foldToDeferRewriteApplied = true,
    )

    val rendered = TryFoldGobraAnnotationBacktranslator.renderBatch(
      plannedSequences = Vector(sequence),
      rootProgram = program,
      translatedProgram = translated,
      translationMetadata = Some(TryFoldTranslationMetadata(dynamicPredicateMap = Map("dynamic_pred_0" -> "Mem"))),
      symbolicStoreByLocal = Map(
        "tmp_V2" -> uint16Call,
        "res_V0" -> vpr.LocalVar("res_V0_CN1@41@47", vpr.Ref)(),
      ),
    )

    withClue(s"Backtranslation failures: ${rendered.failed.map(_.reason)}") {
      rendered.failed shouldBe empty
    }
    rendered.succeeded should have size 1
    rendered.succeeded.head.annotationLines should contain("defer fold acc(tmp.Mem(), 1/1)")
    rendered.succeeded.head.annotationLines.mkString("\n") should not include "Uint16_e2211d10_MbigEndian"
  }

  test("non-post stronger return substitution context suppresses weaker identity sibling") {
    val program = tinyProgramForBacktranslation
    val methodName = "f"
    val markerLabel = s"tryfold_ret_m${Names.hash(methodName)}_i0_l5_c2"
    val tmpFile = Files.createTempFile("tryfold-backtranslate-nonpost-priority-", ".go")
    try {
      val goContent =
        """package addr
          |
          |func f() (res []bool) {
          |	tmp := res
          |	_ = tmp
          |	return tmp
          |}
          |""".stripMargin
      Files.write(tmpFile, goContent.getBytes(StandardCharsets.UTF_8))

      val translated = translatedProgramWithReturnMarker(methodName, markerLabel)

      val sequence = TryFoldInsertionPlanner.PlannedAnnotationSequence(
        originalSequence = TryFoldWorklistEngine.AnnotationSequence(Vector.empty),
        plannedSequence = TryFoldWorklistEngine.AnnotationSequence(Vector(
          TryFoldWorklistEngine.AnnotationDirective(
            action = TryFoldWorklistEngine.FoldAnnotation,
            predicateName = "Bytes_b4eddfca_F",
            args = Vector("res_V0"),
            argsExp = Some(Vector(vpr.LocalVar("res_V0", vpr.Ref)())),
            permission = Some(PermissionAmount("1/32768", "0.000030517578125")),
          ),
        )),
        insertionAnchor = TryFoldInsertionPlanner.InsertionAnchor(
          kind = TryFoldInsertionPlanner.ErrorLocationAnchor,
          sourceFile = Some(tmpFile.toAbsolutePath.normalize.toString),
          sourceLine = Some(5),
          sourceColumn = Some(2),
          sourceLocation = Some("host.go@5.2"),
          returnMarkerLabel = Some(markerLabel),
          returnLine = None,
          returnColumn = None,
        ),
        isPostconditionFailure = false,
        foldToDeferRewriteApplied = false,
      )

      val rendered = TryFoldGobraAnnotationBacktranslator.renderBatch(
        plannedSequences = Vector(sequence),
        rootProgram = program,
        translatedProgram = translated,
      )

      withClue(s"Backtranslation failures: ${rendered.failed.map(_.reason)}") {
        rendered.failed shouldBe empty
      }
      rendered.succeeded should have size 1
      rendered.succeeded.head.annotationLines should contain("fold acc(Bytes(tmp), 1/32768)")
      rendered.succeeded.head.annotationLines.mkString("\n") should not include "Bytes(res)"
    } finally {
      Files.deleteIfExists(tmpFile)
    }
  }
}
