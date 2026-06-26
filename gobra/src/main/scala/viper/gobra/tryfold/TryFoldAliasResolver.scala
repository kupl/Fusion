package viper.gobra.tryfold

import viper.silver.{ast => vpr}
import viper.silver.ast.utility.rewriter.Traverse

import scala.util.matching.Regex

object TryFoldAliasResolver {

  final case class ResolutionStep(
                                   iteration: Int,
                                   before: String,
                                   afterSubstitution: String,
                                   afterNormalization: String,
                                 )

  final case class ResolutionResult(
                                     resolved: vpr.Exp,
                                     steps: Vector[ResolutionStep],
                                     terminatedBy: String,
                                     iterations: Int,
                                   )

  def resolve(
               exp: vpr.Exp,
               assignmentsByLocal: Map[String, vpr.Exp],
               maxIterations: Int = 24,
             ): ResolutionResult = {
    if (assignmentsByLocal.isEmpty) {
      ResolutionResult(
        resolved = exp,
        steps = Vector.empty,
        terminatedBy = "no_assignments",
        iterations = 0,
      )
    } else {
      var current = exp
      var iteration = 0
      var steps = Vector.empty[ResolutionStep]
      var terminatedBy = "fixed_point"
      var keepGoing = true
      var seen = Set(safeRender(current))

      while (keepGoing && iteration < maxIterations) {
        val before = safeRender(current)
        val substituted = substituteLocals(current, assignmentsByLocal)
        val afterSubstitution = safeRender(substituted)
        val normalized = TryFoldExpNormalizer.normalize(substituted, maxIterations = 8).normalized
        val afterNormalization = safeRender(normalized)

        steps :+= ResolutionStep(
          iteration = iteration + 1,
          before = before,
          afterSubstitution = afterSubstitution,
          afterNormalization = afterNormalization,
        )

        if (afterNormalization == before) {
          terminatedBy = "fixed_point"
          keepGoing = false
          current = normalized
        } else if (seen.contains(afterNormalization)) {
          terminatedBy = "cycle_detected"
          keepGoing = false
          current = normalized
        } else {
          seen += afterNormalization
          current = normalized
          iteration += 1
        }
      }

      if (keepGoing) {
        terminatedBy = "max_iterations"
      }

      ResolutionResult(
        resolved = current,
        steps = steps,
        terminatedBy = terminatedBy,
        iterations = steps.size,
      )
    }
  }

  private def substituteLocals(exp: vpr.Exp, assignmentsByLocal: Map[String, vpr.Exp]): vpr.Exp =
    exp.transform(
      {
        case lv: vpr.AbstractLocalVar =>
          if (isAliasResolutionTarget(lv.name)) replacementFor(lv.name, assignmentsByLocal).getOrElse(lv)
          else lv
      }: PartialFunction[vpr.Node, vpr.Node],
      Traverse.BottomUp,
    ).asInstanceOf[vpr.Exp]

  private val VersionSuffixPattern: Regex = "^([A-Za-z_][A-Za-z0-9_]*)_V\\d+(?:_CN\\d+)?$".r

  private def replacementFor(name: String, assignmentsByLocal: Map[String, vpr.Exp]): Option[vpr.Exp] = {
    val stripped = stripVarSuffix(name)
    val noAt = name.replaceAll("@\\d+", "")

    assignmentsByLocal.get(name)
      .orElse(assignmentsByLocal.get(noAt))
      .orElse(assignmentsByLocal.get(stripped))
      .orElse(lookupByBaseName(stripped, assignmentsByLocal))
      .filterNot {
        case lv: vpr.AbstractLocalVar => lv.name == name
        case _ => false
      }
  }

  private def lookupByBaseName(base: String, assignmentsByLocal: Map[String, vpr.Exp]): Option[vpr.Exp] = {
    if (base.isEmpty) return None
    val candidates = assignmentsByLocal.iterator.collect {
      case (key, value)
        if stripVarSuffix(key.replaceAll("@\\d+", "")) == base =>
        value
    }.toVector

    val preferred = candidates.find(exp => !isUserLocalAlias(exp))
      .orElse(candidates.find(exp => isInternalLocalAlias(exp)))
      .orElse(candidates.headOption)
    preferred
  }

  private def isUserLocalAlias(exp: vpr.Exp): Boolean =
    exp match {
      case lv: vpr.AbstractLocalVar =>
        !isInternalLocalAlias(lv)
      case _ =>
        false
    }

  private def isInternalLocalAlias(exp: vpr.Exp): Boolean =
    exp match {
      case lv: vpr.AbstractLocalVar => isInternalLocalAlias(lv)
      case _ => false
    }

  private def isInternalLocalAlias(local: vpr.AbstractLocalVar): Boolean = {
    val stripped = stripVarSuffix(local.name.replaceAll("@\\d+", ""))
    stripped.startsWith("fn$$") ||
      stripped.startsWith("$t") ||
      stripped.startsWith("$k") ||
      stripped.matches("^N\\d+$")
  }

  private def isAliasResolutionTarget(name: String): Boolean = {
    val stripped = stripVarSuffix(name.replaceAll("@\\d+", ""))
    stripped.startsWith("fn$$") ||
      stripped.startsWith("$t") ||
      stripped.startsWith("$k") ||
      stripped.matches("^N\\d+$")
  }

  private def stripVarSuffix(name: String): String =
    name.replaceAll("@\\d+", "") match {
      case VersionSuffixPattern(base) => base
      case other => other
    }

  private def safeRender(value: Any): String =
    try {
      String.valueOf(value)
    } catch {
      case throwable: Throwable => s"<rendering failed: ${throwable.getClass.getSimpleName}>"
    }
}
