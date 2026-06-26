package viper.gobra.tryfold

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import viper.gobra.backend.{BackendVerifier, ViperBackends}
import viper.gobra.frontend.{Config, PackageInfo}
import viper.gobra.reporting.{BackTranslator, NoopReporter}
import viper.gobra.util.{DefaultGobraExecutionContext, GobraExecutionContext}
import viper.silicon.interfaces.SiliconDebuggingFailureContext
import viper.silver.{ast => vpr}

import scala.concurrent.Await
import scala.concurrent.duration.Duration

class TryFoldTargetPermissionExtractorTests extends AnyFunSuite with Matchers {

  private def programWithPostconditionPermissionFailure: vpr.Program = {
    val field = vpr.Field("f", vpr.Int)()
    val receiver = vpr.LocalVarDecl("x", vpr.Ref)()
    val halfPerm = vpr.FractionalPerm(vpr.IntLit(1)(), vpr.IntLit(2)())()
    val access = vpr.FieldAccess(receiver.localVar, field)()
    val accessPredicate = vpr.FieldAccessPredicate(access, Some(halfPerm))()
    val method = vpr.Method(
      name = "failingTargetPermission",
      formalArgs = Seq(receiver),
      formalReturns = Seq.empty,
      pres = Seq(accessPredicate),
      posts = Seq(accessPredicate),
      body = Some(
        vpr.Seqn(
          Seq(
            vpr.Exhale(accessPredicate)(),
          ),
          Seq.empty,
        )()
      ),
    )()
    vpr.Program(
      domains = Seq.empty,
      fields = Seq(field),
      functions = Seq.empty,
      predicates = Seq.empty,
      methods = Seq(method),
      extensions = Seq.empty,
    )()
  }

  test("tryFold extracts target permission amount for first failing error") {
    implicit val executor: GobraExecutionContext = new DefaultGobraExecutionContext()
    try {
      val task = BackendVerifier.Task(
        program = programWithPostconditionPermissionFailure,
        backtrack = BackTranslator.BackTrackInfo(Seq.empty, Seq.empty),
      )
      val pkgInfo = new PackageInfo("tryfold-tests", "tryfold-tests", isBuiltIn = false)
      val config = Config(
        backend = Some(ViperBackends.SiliconBackend),
        reporter = NoopReporter,
        tryFold = true,
        shouldChop = false,
      )

      val result = Await.result(BackendVerifier.verify(task, pkgInfo)(config), Duration.Inf)

      result match {
        case BackendVerifier.Success =>
          fail("Expected verification to fail")
        case failure: BackendVerifier.Failure =>
          val firstError = failure.errors.head
          val context = firstError.failureContexts.collectFirst {
            case ctx: SiliconDebuggingFailureContext if ctx.state.isDefined => ctx
          }

          val extraction = TryFoldTargetPermissionExtractor.extract(firstError, context)
          extraction.entries should not be empty
          extraction.entries.head.nodeKind shouldBe "field"
          extraction.entries.head.nodeName shouldBe "f"
          extraction.entries.head.evaluatedPermission.map(_.rational) shouldBe Some("1/2")
      }
    } finally {
      executor.terminate()
    }
  }
}
