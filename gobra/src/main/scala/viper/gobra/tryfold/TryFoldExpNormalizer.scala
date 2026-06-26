package viper.gobra.tryfold

import viper.silver.{ast => vpr}
import viper.silver.ast.utility.rewriter.Traverse

import scala.util.matching.Regex

object TryFoldExpNormalizer {

  final case class NormalizationStep(
                                      pass: String,
                                      before: String,
                                      after: String,
                                    )

  final case class NormalizationResult(
                                        normalized: vpr.Exp,
                                        steps: Vector[NormalizationStep],
                                        converged: Boolean,
                                        iterations: Int,
                                      )

  def normalize(exp: vpr.Exp, maxIterations: Int = 20): NormalizationResult = {
    var current = exp
    var iteration = 0
    var changed = true
    var steps = Vector.empty[NormalizationStep]

    while (changed && iteration < maxIterations) {
      val before = safeRender(current)
      val next = normalizeOnce(current)
      val after = safeRender(next)
      if (before != after) {
        steps :+= NormalizationStep(
          pass = s"decode-pass-${iteration + 1}",
          before = before,
          after = after,
        )
      }
      changed = before != after
      current = next
      iteration += 1
    }

    NormalizationResult(
      normalized = current,
      steps = steps,
      converged = !changed,
      iterations = iteration,
    )
  }

  private def normalizeOnce(exp: vpr.Exp): vpr.Exp =
    exp.transform(
      {
        case dfa: vpr.DomainFuncApp if decodeTupleProjection(dfa).isDefined =>
          decodeTupleProjection(dfa).get
        case fa: vpr.FuncApp if decodeTupleProjection(fa).isDefined =>
          decodeTupleProjection(fa).get
        case vpr.DomainFuncApp(name, Seq(vpr.DomainFuncApp(inner, Seq(value), _)), _)
            if canonicalCallName(name).startsWith("unbox_Poly") && canonicalCallName(inner).startsWith("box_Poly") =>
          value
        case vpr.DomainFuncApp(name, Seq(vpr.DomainFuncApp(inner, Seq(value), _)), _)
            if canonicalCallName(name).startsWith("box_Poly") && canonicalCallName(inner).startsWith("unbox_Poly") =>
          value
        case fa: vpr.FuncApp
            if canonicalCallName(fa.funcname).startsWith("unbox_Poly") &&
              fa.args.size == 1 &&
              fa.args.head.isInstanceOf[vpr.FuncApp] &&
              canonicalCallName(fa.args.head.asInstanceOf[vpr.FuncApp].funcname).startsWith("box_Poly") &&
              fa.args.head.asInstanceOf[vpr.FuncApp].args.size == 1 =>
          fa.args.head.asInstanceOf[vpr.FuncApp].args.head
        case fa: vpr.FuncApp
            if canonicalCallName(fa.funcname).startsWith("box_Poly") &&
              fa.args.size == 1 &&
              fa.args.head.isInstanceOf[vpr.FuncApp] &&
              canonicalCallName(fa.args.head.asInstanceOf[vpr.FuncApp].funcname).startsWith("unbox_Poly") &&
              fa.args.head.asInstanceOf[vpr.FuncApp].args.size == 1 =>
          fa.args.head.asInstanceOf[vpr.FuncApp].args.head
        case vpr.LabelledOld(innerExp, _) =>
          innerExp
        case vpr.DebugLabelledOld(innerExp, _) =>
          innerExp
        case vpr.Old(innerExp) =>
          innerExp
      }: PartialFunction[vpr.Node, vpr.Node],
      Traverse.BottomUp,
    ).asInstanceOf[vpr.Exp]

  private val TupleProjectionPattern: Regex = "^get(\\d+)of(\\d+)$".r

  private def decodeTupleProjection(dfa: vpr.DomainFuncApp): Option[vpr.Exp] = {
    val getterName = canonicalCallName(dfa.funcname)
    decodeTupleProjectionFrom(getterName, dfa.args)
  }

  private def decodeTupleProjection(fa: vpr.FuncApp): Option[vpr.Exp] = {
    val getterName = canonicalCallName(fa.funcname)
    decodeTupleProjectionFrom(getterName, fa.args)
  }

  private def decodeTupleProjectionFrom(getterName: String, args: Seq[vpr.Exp]): Option[vpr.Exp] = {
    val (index, arity) = getterName match {
      case TupleProjectionPattern(i, a) => (i.toInt, a.toInt)
      case _ => return None
    }
    if (args.size != 1 || index < 0 || arity <= 0) return None
    args.head match {
      case vpr.DomainFuncApp(tupleName, tupleArgs, _)
          if isTupleConstructor(tupleName) && tupleArgs.size == arity && index < tupleArgs.size =>
        Some(tupleArgs(index))
      case tuple: vpr.FuncApp
          if isTupleConstructor(tuple.funcname) && tuple.args.size == arity && index < tuple.args.size =>
        Some(tuple.args(index))
      case _ =>
        None
    }
  }

  private def canonicalCallName(name: String): String =
    callBaseName(name).getOrElse(name.trim)

  private def callBaseName(rawName: String): Option[String] = {
    val name = rawName.trim
    if (name.isEmpty) return None

    var idx = 0
    if (!isIdentifierStart(name.charAt(0))) return None
    idx += 1
    while (idx < name.length && isIdentifierPart(name.charAt(idx))) idx += 1

    val base = name.substring(0, idx)
    if (base.isEmpty) return None

    var rest = name.substring(idx).trim
    while (rest.nonEmpty) {
      if (rest.head != '[') return None
      matchingBracketIndex(rest, 0, '[', ']') match {
        case Some(closeIdx) =>
          rest = rest.substring(closeIdx + 1).trim
        case None =>
          return None
      }
    }

    Some(base)
  }

  private def isIdentifierStart(ch: Char): Boolean =
    ch.isLetter || ch == '_'

  private def isIdentifierPart(ch: Char): Boolean =
    ch.isLetterOrDigit || ch == '_' || ch == '$'

  private def matchingBracketIndex(value: String, startIdx: Int, open: Char, close: Char): Option[Int] = {
    if (startIdx < 0 || startIdx >= value.length || value.charAt(startIdx) != open) return None
    var depth = 0
    var idx = startIdx
    while (idx < value.length) {
      val ch = value.charAt(idx)
      if (ch == open) depth += 1
      else if (ch == close) {
        depth -= 1
        if (depth == 0) return Some(idx)
        if (depth < 0) return None
      }
      idx += 1
    }
    None
  }

  private def isTupleConstructor(name: String): Boolean = {
    val canonical = canonicalCallName(name)
    val base = if (canonical.endsWith("()")) canonical.dropRight(2) else canonical
    base == "tuple" || (base.startsWith("tuple") && base.drop("tuple".length).forall(_.isDigit))
  }

  private def safeRender(value: Any): String =
    try {
      String.valueOf(value)
    } catch {
      case throwable: Throwable => s"<rendering failed: ${throwable.getClass.getSimpleName}>"
    }
}
