// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.gobra.frontend

import org.rogach.scallop.exceptions.ValidationFailure
import org.rogach.scallop.exceptions.UnknownOption
import org.rogach.scallop.throwError
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import viper.gobra.backend.{SiliconBasedBackend, ViperVerifier}
import viper.gobra.util.GobraExecutionContext
import java.nio.file.Paths

class TryFoldOptionUnitTests extends AnyFunSuite with Matchers {

  private object ExposedSiliconBackend extends SiliconBasedBackend {
    override def create(exePaths: Vector[String], config: Config)(implicit executor: GobraExecutionContext): ViperVerifier =
      throw new UnsupportedOperationException("not needed in this unit test")

    def options(config: Config): Vector[String] =
      buildOptions(Vector.empty, config)
  }

  test("CLI accepts --tryFold on Silicon and propagates it to frontend config") {
    val parsed = new ScallopGobraConfig(Seq("--backend", "SILICON", "--tryFold"), isInputOptional = true).config
    parsed.isRight shouldBe true
    parsed.toOption.get.tryFold shouldBe true
    parsed.toOption.get.tryFoldStateOut.get.toString should endWith ("output/tryfold_state.json")
    parsed.toOption.get.tryFoldGraphOut.get.toString should endWith ("output/tryfold_graph.json")
    parsed.toOption.get.tryFoldPathOut.get.toString should endWith ("output/tryfold_path.json")
  }

  test("CLI rejects --tryFold on Carbon") {
    val oldThrowError = throwError.value
    throwError.value = true
    try {
      an[ValidationFailure] should be thrownBy {
        new ScallopGobraConfig(Seq("--backend", "CARBON", "--tryFold"), isInputOptional = true)
      }
    } finally {
      throwError.value = oldThrowError
    }
  }

  test("CLI accepts --counterexample only with Silicon and mceMode=on") {
    val parsed = new ScallopGobraConfig(
      Seq("--backend", "SILICON", "--counterexample", "native", "--mceMode", "on"),
      isInputOptional = true
    ).config
    parsed.isRight shouldBe true
    parsed.toOption.get.counterexampleMode shouldBe Some(CounterexampleMode.Native)
  }

  test("CLI rejects --counterexample with mceMode different from on") {
    val oldThrowError = throwError.value
    throwError.value = true
    try {
      an[ValidationFailure] should be thrownBy {
        new ScallopGobraConfig(
          Seq("--backend", "SILICON", "--counterexample", "native", "--mceMode", "od"),
          isInputOptional = true
        )
      }
    } finally {
      throwError.value = oldThrowError
    }
  }

  test("CLI rejects --counterexample on Carbon") {
    val oldThrowError = throwError.value
    throwError.value = true
    try {
      an[ValidationFailure] should be thrownBy {
        new ScallopGobraConfig(
          Seq("--backend", "CARBON", "--counterexample", "native"),
          isInputOptional = true
        )
      }
    } finally {
      throwError.value = oldThrowError
    }
  }

  test("CLI accepts --tryFoldStateOut only together with --tryFold") {
    val parsed = new ScallopGobraConfig(
      Seq("--backend", "SILICON", "--tryFold", "--tryFoldStateOut", "tmp/tryfold-states.json"),
      isInputOptional = true
    ).config
    parsed.isRight shouldBe true
    parsed.toOption.get.tryFoldStateOut shouldBe Some(Paths.get("tmp/tryfold-states.json"))
  }

  test("CLI rejects --tryFoldStateOut without --tryFold") {
    val oldThrowError = throwError.value
    throwError.value = true
    try {
      an[ValidationFailure] should be thrownBy {
        new ScallopGobraConfig(
          Seq("--backend", "SILICON", "--tryFoldStateOut", "tmp/tryfold-states.json"),
          isInputOptional = true
        )
      }
    } finally {
      throwError.value = oldThrowError
    }
  }

  test("CLI accepts tryFold candidate tuning flags and output paths with --tryFold") {
    val parsed = new ScallopGobraConfig(
      Seq(
        "--backend", "SILICON",
        "--tryFold",
        "--tryFoldMaxChildrenPerFailure", "40",
        "--tryFoldMaxConcreteCandidatesPerPath", "5",
        "--tryFoldPathMaxDepth", "5",
        "--tryFoldGraphOut", "tmp/tryfold-graph.json",
        "--tryFoldPathOut", "tmp/tryfold-path.json",
      ),
      isInputOptional = true,
    ).config
    parsed.isRight shouldBe true
    parsed.toOption.get.tryFoldMaxChildrenPerFailure shouldBe 40
    parsed.toOption.get.tryFoldMaxConcreteCandidatesPerPath shouldBe 5
    parsed.toOption.get.tryFoldPathMaxDepth shouldBe 5
    parsed.toOption.get.tryFoldGraphOut shouldBe Some(Paths.get("tmp/tryfold-graph.json"))
    parsed.toOption.get.tryFoldPathOut shouldBe Some(Paths.get("tmp/tryfold-path.json"))
  }

  test("CLI rejects removed --tryFoldWorklist flag") {
    val oldThrowError = throwError.value
    throwError.value = true
    try {
      an[UnknownOption] should be thrownBy {
        new ScallopGobraConfig(
          Seq("--backend", "SILICON", "--tryFold", "--tryFoldWorklist"),
          isInputOptional = true
        )
      }
    } finally {
      throwError.value = oldThrowError
    }
  }

  test("CLI accepts tryFold candidate bounds with --tryFold only") {
    val parsed = new ScallopGobraConfig(
      Seq(
        "--backend", "SILICON",
        "--tryFold",
        "--tryFoldMaxChildrenPerFailure", "7",
        "--tryFoldMaxConcreteCandidatesPerPath", "3",
        "--tryFoldPathMaxDepth", "4",
      ),
      isInputOptional = true
    ).config
    parsed.isRight shouldBe true
    parsed.toOption.get.tryFoldMaxChildrenPerFailure shouldBe 7
    parsed.toOption.get.tryFoldMaxConcreteCandidatesPerPath shouldBe 3
    parsed.toOption.get.tryFoldPathMaxDepth shouldBe 4
  }

  test("CLI rejects removed --tryFoldMaxIterations and --tryFoldMaxQueueSize flags") {
    val oldThrowError = throwError.value
    throwError.value = true
    try {
      an[UnknownOption] should be thrownBy {
        new ScallopGobraConfig(
          Seq("--backend", "SILICON", "--tryFold", "--tryFoldMaxIterations", "10"),
          isInputOptional = true
        )
      }
      an[UnknownOption] should be thrownBy {
        new ScallopGobraConfig(
          Seq("--backend", "SILICON", "--tryFold", "--tryFoldMaxQueueSize", "20"),
          isInputOptional = true
        )
      }
    } finally {
      throwError.value = oldThrowError
    }
  }

  test("CLI accepts --tryFoldGraphOut with --tryFold only") {
    val parsed = new ScallopGobraConfig(
      Seq("--backend", "SILICON", "--tryFold", "--tryFoldGraphOut", "tmp/graph.json"),
      isInputOptional = true
    ).config
    parsed.isRight shouldBe true
    parsed.toOption.get.tryFoldGraphOut shouldBe Some(Paths.get("tmp/graph.json"))
  }

  test("CLI accepts --tryFoldPathOut with --tryFold only") {
    val parsed = new ScallopGobraConfig(
      Seq("--backend", "SILICON", "--tryFold", "--tryFoldPathOut", "tmp/path.json"),
      isInputOptional = true
    ).config
    parsed.isRight shouldBe true
    parsed.toOption.get.tryFoldPathOut shouldBe Some(Paths.get("tmp/path.json"))
  }

  test("CLI rejects non-positive worklist bounds") {
    val oldThrowError = throwError.value
    throwError.value = true
    try {
      an[ValidationFailure] should be thrownBy {
        new ScallopGobraConfig(
          Seq(
            "--backend", "SILICON",
            "--tryFold",
            "--tryFoldPathMaxDepth", "0",
          ),
          isInputOptional = true
        )
      }
    } finally {
      throwError.value = oldThrowError
    }
  }

  test("Config merge keeps tryFold enabled if it is enabled in either config") {
    Config(tryFold = true).merge(Config(tryFold = false)).tryFold shouldBe true
    Config(tryFold = false).merge(Config(tryFold = true)).tryFold shouldBe true
  }

  test("Config merge keeps left-hand tryFoldPathMaxDepth value") {
    Config(tryFoldPathMaxDepth = 4).merge(Config(tryFoldPathMaxDepth = 7)).tryFoldPathMaxDepth shouldBe 4
  }

  test("Config merge keeps left-hand tryFoldMaxConcreteCandidatesPerPath value") {
    Config(tryFoldMaxConcreteCandidatesPerPath = 5).merge(Config(tryFoldMaxConcreteCandidatesPerPath = 9)).tryFoldMaxConcreteCandidatesPerPath shouldBe 5
  }

  test("Config merge keeps first non-empty tryFoldGraphOut") {
    val lhs = Config(tryFoldGraphOut = Some(Paths.get("lhs/graph.json")))
    val rhs = Config(tryFoldGraphOut = Some(Paths.get("rhs/graph.json")))
    lhs.merge(rhs).tryFoldGraphOut shouldBe Some(Paths.get("lhs/graph.json"))
    Config(tryFoldGraphOut = None).merge(rhs).tryFoldGraphOut shouldBe Some(Paths.get("rhs/graph.json"))
  }

  test("Config merge keeps first non-empty tryFoldPathOut") {
    val lhs = Config(tryFoldPathOut = Some(Paths.get("lhs/path.json")))
    val rhs = Config(tryFoldPathOut = Some(Paths.get("rhs/path.json")))
    lhs.merge(rhs).tryFoldPathOut shouldBe Some(Paths.get("lhs/path.json"))
    Config(tryFoldPathOut = None).merge(rhs).tryFoldPathOut shouldBe Some(Paths.get("rhs/path.json"))
  }

  test("Silicon backend enables non-interactive debug state collection in tryFold mode") {
    val withTryFold = ExposedSiliconBackend.options(Config(tryFold = true))
    withTryFold should contain ("--tryFold")
    withTryFold should contain ("--enableDebugging")
    withTryFold should contain ("--disableInteractiveDebugging")

    val withoutTryFold = ExposedSiliconBackend.options(Config(tryFold = false))
    withoutTryFold should not contain "--tryFold"
    withoutTryFold should not contain "--enableDebugging"
    withoutTryFold should not contain "--disableInteractiveDebugging"
  }

  test("Silicon backend forwards --counterexample mode when configured") {
    val withCounterexample = ExposedSiliconBackend.options(Config(counterexampleMode = Some(CounterexampleMode.Native)))
    withCounterexample should contain ("--counterexample")
    withCounterexample should contain ("native")

    val withoutCounterexample = ExposedSiliconBackend.options(Config(counterexampleMode = None))
    withoutCounterexample should not contain "--counterexample"
  }
}
