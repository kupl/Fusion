package viper.gobra.tryfold

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import viper.silver.{ast => vpr}

class TryFoldAliasResolverTests extends AnyFunSuite with Matchers {

  test("resolves internal temporary aliases") {
    val exp = vpr.LocalVar("fn$$1", vpr.Ref)()
    val result = TryFoldAliasResolver.resolve(
      exp = exp,
      assignmentsByLocal = Map(
        "fn$$1" -> vpr.LocalVar("tmp_V2", vpr.Ref)(),
      ),
    )
    result.resolved.toString should include("tmp_V2")
  }

  test("does not rewrite user-visible locals even if alias assignments exist") {
    val exp = vpr.LocalVar("tmp_V2", vpr.Ref)()
    val result = TryFoldAliasResolver.resolve(
      exp = exp,
      assignmentsByLocal = Map(
        "tmp_V2" -> vpr.LocalVar("ip_V0@2", vpr.Ref)(),
      ),
    )
    result.resolved.toString should include("tmp_V2")
    result.resolved.toString should not include "ip_V0"
  }
}

