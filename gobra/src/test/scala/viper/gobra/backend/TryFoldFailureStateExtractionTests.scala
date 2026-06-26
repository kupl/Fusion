// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.gobra.backend

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import viper.gobra.frontend.{Config, CounterexampleMode, MCE, PackageInfo}
import viper.gobra.reporting.{BackTranslator, NoopReporter}
import viper.gobra.util.{DefaultGobraExecutionContext, GobraExecutionContext}
import viper.silver.{ast => vpr}

import scala.concurrent.Await
import scala.concurrent.duration.Duration
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}

class TryFoldFailureStateExtractionTests extends AnyFunSuite with Matchers {

  private def failingProgram: vpr.Program = {
    val argument = vpr.LocalVarDecl("x", vpr.Int)()
    val method = vpr.Method(
      "failing",
      Seq(argument),
      Seq.empty,
      Seq.empty,
      Seq(vpr.FalseLit()()),
      Some(vpr.Seqn(Seq.empty, Seq.empty)()),
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

  private def failingProgramWithFieldPermissionPrecondition: vpr.Program = {
    val field = vpr.Field("f", vpr.Int)()
    val argument = vpr.LocalVarDecl("x", vpr.Ref)()
    val pre = vpr.FieldAccessPredicate(
      vpr.FieldAccess(argument.localVar, field)(),
      Some(vpr.FractionalPerm(vpr.IntLit(1)(), vpr.IntLit(2)())())
    )()
    val method = vpr.Method(
      "failingWithPermissionPrecondition",
      Seq(argument),
      Seq.empty,
      Seq(pre),
      Seq(vpr.FalseLit()()),
      Some(vpr.Seqn(Seq.empty, Seq.empty)()),
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

  private def failingProgramWithConditionalFieldPermissionPrecondition: vpr.Program = {
    val field = vpr.Field("f", vpr.Int)()
    val receiver = vpr.LocalVarDecl("x", vpr.Ref)()
    val guard = vpr.LocalVarDecl("b", vpr.Bool)()
    val conditionalPerm = vpr.CondExp(
      guard.localVar,
      vpr.FractionalPerm(vpr.IntLit(1)(), vpr.IntLit(2)())(),
      vpr.NoPerm()(),
    )()
    val pre = vpr.FieldAccessPredicate(
      vpr.FieldAccess(receiver.localVar, field)(),
      Some(conditionalPerm),
    )()
    val method = vpr.Method(
      "failingWithConditionalPermissionPrecondition",
      Seq(receiver, guard),
      Seq.empty,
      Seq(pre),
      Seq(vpr.FalseLit()()),
      Some(vpr.Seqn(Seq.empty, Seq.empty)()),
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

  test("tryFold extracts debugging failure states while keeping debugger non-interactive") {
    implicit val executor: GobraExecutionContext = new DefaultGobraExecutionContext()
    try {
      val task = BackendVerifier.Task(
        program = failingProgram,
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
        case BackendVerifier.Failure(errors, _, extractedFailureStates) =>
          errors should not be empty
          extractedFailureStates should not be empty
          extractedFailureStates.foreach { snapshot =>
            snapshot.errorReadableMessage should not be empty
            snapshot.sourceLocation should not be null
            snapshot.memberName should not be null
            snapshot.heapChunks should not be null
            snapshot.predicateOnlyHeapChunks should not be null
            snapshot.store should not be null
            snapshot.oldHeapChunks should not be null
            snapshot.predicateOnlyOldHeapChunks should not be null
            snapshot.sourcePermissions should not be null
          }
      }
    } finally {
      executor.terminate()
    }
  }

  test("tryFold exports extracted failure states to JSON file when requested") {
    implicit val executor: GobraExecutionContext = new DefaultGobraExecutionContext()
    val outFile = Files.createTempFile("tryfold-failure-states-", ".json")
    try {
      val task = BackendVerifier.Task(
        program = failingProgram,
        backtrack = BackTranslator.BackTrackInfo(Seq.empty, Seq.empty),
      )
      val pkgInfo = new PackageInfo("tryfold-tests", "tryfold-tests", isBuiltIn = false)
      val config = Config(
        backend = Some(ViperBackends.SiliconBackend),
        reporter = NoopReporter,
        tryFold = true,
        tryFoldStateOut = Some(outFile),
        shouldChop = false,
      )

      val result = Await.result(BackendVerifier.verify(task, pkgInfo)(config), Duration.Inf)
      result shouldBe a[BackendVerifier.Failure]

      val exported = new String(Files.readAllBytes(outFile), StandardCharsets.UTF_8)
      exported should include ("\"verificationResult\": \"failure\"")
      exported should include ("\"states\"")
      exported should include ("\"sourceLocation\"")
      exported should include ("\"memberName\"")
      exported should include ("\"predicateOnlyHeapChunks\"")
      exported should include ("\"sourcePermissions\"")
    } finally {
      executor.terminate()
      Files.deleteIfExists(outFile)
    }
  }

  test("without tryFold, state export file is not written even if output path is configured") {
    implicit val executor: GobraExecutionContext = new DefaultGobraExecutionContext()
    val tmpDir = Files.createTempDirectory("tryfold-no-export-")
    val outFile: Path = tmpDir.resolve("states.json")
    try {
      val task = BackendVerifier.Task(
        program = failingProgram,
        backtrack = BackTranslator.BackTrackInfo(Seq.empty, Seq.empty),
      )
      val pkgInfo = new PackageInfo("tryfold-tests", "tryfold-tests", isBuiltIn = false)
      val config = Config(
        backend = Some(ViperBackends.SiliconBackend),
        reporter = NoopReporter,
        tryFold = false,
        tryFoldStateOut = Some(outFile),
        shouldChop = false,
      )

      val result = Await.result(BackendVerifier.verify(task, pkgInfo)(config), Duration.Inf)
      result shouldBe a[BackendVerifier.Failure]
      Files.exists(outFile) shouldBe false
    } finally {
      executor.terminate()
      Files.deleteIfExists(outFile)
      Files.deleteIfExists(tmpDir)
    }
  }

  test("tryFold source permissions include evaluated permission amount when available") {
    implicit val executor: GobraExecutionContext = new DefaultGobraExecutionContext()
    try {
      val task = BackendVerifier.Task(
        program = failingProgramWithFieldPermissionPrecondition,
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
        case BackendVerifier.Failure(_, _, extractedFailureStates) =>
          extractedFailureStates should not be empty
          val sourcePermissions = extractedFailureStates.flatMap(_.sourcePermissions)
          sourcePermissions should not be empty
          sourcePermissions.exists(_.evaluatedBodyPermission.exists(_.rational == "1/2")) shouldBe true
      }
    } finally {
      executor.terminate()
    }
  }

  test("tryFold source permissions remain available with native counterexample enabled") {
    implicit val executor: GobraExecutionContext = new DefaultGobraExecutionContext()
    try {
      val task = BackendVerifier.Task(
        program = failingProgramWithFieldPermissionPrecondition,
        backtrack = BackTranslator.BackTrackInfo(Seq.empty, Seq.empty),
      )
      val pkgInfo = new PackageInfo("tryfold-tests", "tryfold-tests", isBuiltIn = false)
      val config = Config(
        backend = Some(ViperBackends.SiliconBackend),
        reporter = NoopReporter,
        tryFold = true,
        shouldChop = false,
        counterexampleMode = Some(CounterexampleMode.Native),
        mceMode = MCE.Enabled,
      )

      val result = Await.result(BackendVerifier.verify(task, pkgInfo)(config), Duration.Inf)

      result match {
        case BackendVerifier.Success =>
          fail("Expected verification to fail")
        case BackendVerifier.Failure(_, _, extractedFailureStates) =>
          extractedFailureStates should not be empty
          val sourcePermissions = extractedFailureStates.flatMap(_.sourcePermissions)
          sourcePermissions should not be empty
          sourcePermissions.exists(_.evaluatedBodyPermission.exists(_.rational == "1/2")) shouldBe true
      }
    } finally {
      executor.terminate()
    }
  }

  test("tryFold conditional permissions use non-zero branch heuristic when condition is unresolved") {
    implicit val executor: GobraExecutionContext = new DefaultGobraExecutionContext()
    try {
      val task = BackendVerifier.Task(
        program = failingProgramWithConditionalFieldPermissionPrecondition,
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
        case BackendVerifier.Failure(_, _, extractedFailureStates) =>
          extractedFailureStates should not be empty
          val sourcePermissions = extractedFailureStates.flatMap(_.sourcePermissions)
          sourcePermissions should not be empty
          sourcePermissions.exists { entry =>
            entry.permissionTerm.contains("?") &&
              entry.evaluatedBodyPermission.exists(_.rational == "1/2")
          } shouldBe true
      }
    } finally {
      executor.terminate()
    }
  }
}
