package viper.gobra.tryfold

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import viper.gobra.ast.{internal => in}
import viper.gobra.reporting.Source
import viper.gobra.theory.Addressability

class TryFoldReturnMarkerInstrumentationTests extends AnyFunSuite with Matchers {

  private val srcInfo: Source.Parser.Info = Source.Parser.Internal

  private def tinyProgramWithSingleReturn: in.Program = {
    val recv = in.Parameter.In("recv", in.BoolT(Addressability.Exclusive))(srcInfo)
    val method = in.Method(
      receiver = recv,
      name = in.MethodProxy("Copy", "pkg/addr.Host.Copy")(srcInfo),
      args = Vector.empty,
      results = Vector.empty,
      pres = Vector.empty,
      posts = Vector.empty,
      terminationMeasures = Vector.empty,
      backendAnnotations = Vector.empty,
      body = Some(
        in.MethodBody(
          decls = Vector.empty,
          seqn = in.MethodBodySeqn(Vector(in.Return()(srcInfo)))(srcInfo),
          postprocessing = Vector.empty,
        )(srcInfo)
      ),
    )(srcInfo)

    in.Program(
      types = Vector.empty,
      members = Vector(method),
      table = new in.LookupTable(),
    )(srcInfo)
  }

  test("instrumentation inserts return marker label immediately before return") {
    val program = tinyProgramWithSingleReturn
    val result = TryFoldReturnMarkerInstrumentation.instrumentProgram(program)

    result.markers should have size 1

    val method = result.program.members.collectFirst { case m: in.Method => m }.get
    val stmts = method.body.get.seqn.stmts

    stmts should have size 2
    stmts.head shouldBe a[in.Label]
    stmts(1) shouldBe a[in.Return]

    val labelStmt = stmts.head.asInstanceOf[in.Label]
    val parsed = TryFoldReturnMarkerInstrumentation.parseMarker(labelStmt.id.name)
    parsed should not be empty
    parsed.get.returnIndex shouldBe 0
  }
}
