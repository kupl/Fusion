// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.gobra.backend

import viper.silicon.toMap
import viper.silicon.interfaces.state.GeneralChunk
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silver.{ast => vpr}
import viper.silver.utility.Common.Rational
import viper.silver.verifier.{ApplicationEntry, ConstantEntry, Counterexample, Model, ModelEntry}

object TryFoldSourcePermissionExtractor {

  final case class PermissionAmount(
                                    rational: String,
                                    decimal: String,
                                  )

  final case class SourcePermissionEntry(
                                          index: Int,
                                          nodeKind: String,
                                          nodeName: String,
                                          nodeId: String,
                                          chunkKind: String,
                                          chunk: String,
                                          permissionTerm: String,
                                          bodyPermissionTerm: Option[String],
                                          conditionTerm: Option[String],
                                          conditionEvaluation: Option[Boolean],
                                          evaluatedPermission: Option[PermissionAmount],
                                          evaluatedBodyPermission: Option[PermissionAmount],
                                          evaluationKind: String,
                                          arguments: Vector[String],
                                          argumentsExp: Option[Vector[vpr.Exp]],
                                          singletonArguments: Vector[String],
                                          singletonArgumentsExp: Option[Vector[vpr.Exp]],
                                        )

  def extractFromState(state: State, counterexample: Option[Counterexample]): Vector[SourcePermissionEntry] =
    extractFromChunks(state.h.values.collect { case chunk: GeneralChunk => chunk }, counterexample.map(_.model))

  def extractFromChunks(chunks: Iterable[GeneralChunk], model: Option[Model]): Vector[SourcePermissionEntry] =
    chunks.zipWithIndex.flatMap { case (chunk, index) =>
      toSourcePermissionEntry(chunk, index, model)
    }.toVector

  private def toSourcePermissionEntry(chunk: GeneralChunk, index: Int, model: Option[Model]): Option[SourcePermissionEntry] = {
    nodeForChunk(chunk).map { node =>
      val chunkKind = chunk.getClass.getSimpleName
      val basePermissionTerm = basePermissionForChunk(chunk)
      val conditionTerm = conditionForChunk(chunk)
      val permissionTermStr = safeRender(chunk.perm)
      val bodyPermissionTermStr = if (basePermissionTerm == chunk.perm) None else Some(safeRender(basePermissionTerm))
      val conditionTermStr = conditionTerm.map(safeRender)
      val evaluatedPermission = evaluatePerm(chunk.perm, model).map(toPermissionAmount)
      val evaluatedBodyPermission = evaluatePerm(basePermissionTerm, model).map(toPermissionAmount)
      val kind =
        if (evaluatedBodyPermission.isDefined) "exact"
        else if (conditionTerm.isDefined || basePermissionTerm.isInstanceOf[Ite]) "conditional"
        else "symbolic"
      val singletonArguments = singletonArgumentsForChunk(chunk).map(safeRender).toVector
      val arguments = nonQuantifiedArgumentsForChunk(chunk).map(safeRender).toVector
      val singletonArgumentsExp = singletonArgumentExpsForChunk(chunk).toVector
      val argumentsExp = nonQuantifiedArgumentExpsForChunk(chunk).toVector
      val conditionEvaluation = conditionTerm.flatMap(evaluateBool(_, model))
      SourcePermissionEntry(
        index = index,
        nodeKind = node._1,
        nodeName = node._2,
        nodeId = s"${node._1}:${node._2}",
        chunkKind = chunkKind,
        chunk = safeRender(chunk),
        permissionTerm = permissionTermStr,
        bodyPermissionTerm = bodyPermissionTermStr,
        conditionTerm = conditionTermStr,
        conditionEvaluation = conditionEvaluation,
        evaluatedPermission = evaluatedPermission,
        evaluatedBodyPermission = evaluatedBodyPermission,
        evaluationKind = kind,
        arguments = arguments,
        argumentsExp = if (argumentsExp.nonEmpty) Some(argumentsExp) else None,
        singletonArguments = singletonArguments,
        singletonArgumentsExp = if (singletonArgumentsExp.nonEmpty) Some(singletonArgumentsExp) else None,
      )
    }
  }

  private def nodeForChunk(chunk: GeneralChunk): Option[(String, String)] = {
    val nameOpt = chunk.id match {
      case BasicChunkIdentifier(name) => Some(name)
      case _ => Option(chunk.id).map(_.toString).filter(_.nonEmpty)
    }
    nameOpt.flatMap { name =>
      chunk.resourceID match {
        case PredicateID => Some(("predicate", name))
        case FieldID => Some(("field", name))
        case _ => None
      }
    }
  }

  private def basePermissionForChunk(chunk: GeneralChunk): Term =
    chunk match {
      case qfc: QuantifiedFieldChunk =>
        substituteQuantifiedBindings(qfc.permValue, qfc.quantifiedVars, qfc.singletonArguments)
      case qpc: QuantifiedPredicateChunk =>
        substituteQuantifiedBindings(qpc.permValue, qpc.quantifiedVars, qpc.singletonArguments)
      case other =>
        other.perm
    }

  private def conditionForChunk(chunk: GeneralChunk): Option[Term] =
    chunk match {
      case qfc: QuantifiedFieldChunk =>
        Some(substituteQuantifiedBindings(qfc.condition, qfc.quantifiedVars, qfc.singletonArguments))
      case qpc: QuantifiedPredicateChunk =>
        Some(substituteQuantifiedBindings(qpc.condition, qpc.quantifiedVars, qpc.singletonArguments))
      case _ =>
        chunk.perm match {
          case ite: Ite if ite.t0.sort == sorts.Bool => Some(ite.t0)
          case _ => None
        }
    }

  private def substituteQuantifiedBindings(term: Term, quantifiedVars: Seq[Var], singletonArgs: Option[Seq[Term]]): Term =
    singletonArgs match {
      case Some(args) if args.size == quantifiedVars.size =>
        term.replace[Var](toMap(quantifiedVars.zip(args)))
      case _ =>
        term
    }

  private def singletonArgumentsForChunk(chunk: GeneralChunk): Seq[Term] =
    chunk match {
      case qfc: QuantifiedFieldChunk => qfc.singletonArguments.toSeq.flatten
      case qpc: QuantifiedPredicateChunk => qpc.singletonArguments.getOrElse(Seq.empty)
      case _ => Seq.empty
    }

  private def nonQuantifiedArgumentsForChunk(chunk: GeneralChunk): Seq[Term] =
    chunk match {
      case basic: BasicChunk => basic.args
      case _ => Seq.empty
    }

  private def singletonArgumentExpsForChunk(chunk: GeneralChunk): Seq[vpr.Exp] =
    chunk match {
      case qfc: QuantifiedFieldChunk => qfc.singletonArgumentExps.toSeq.flatten
      case qpc: QuantifiedPredicateChunk => qpc.singletonArgumentExps.toSeq.flatten
      case _ => Seq.empty
    }

  private def nonQuantifiedArgumentExpsForChunk(chunk: GeneralChunk): Seq[vpr.Exp] =
    chunk match {
      case basic: BasicChunk => basic.argsExp.toSeq.flatten
      case _ => Seq.empty
    }

  private def evaluatePerm(term: Term, model: Option[Model]): Option[Rational] =
    term match {
      case NoPerm => Some(Rational.zero)
      case FullPerm => Some(Rational.one)
      case literal: PermLiteral => Some(literal.literal)
      case FractionPerm(n, d) =>
        for {
          numer <- evaluateInt(n, model)
          denom <- evaluateInt(d, model)
          if denom != 0
        } yield Rational(numer, denom)
      case PermTimes(p0, p1) =>
        for {
          left <- evaluatePerm(p0, model)
          right <- evaluatePerm(p1, model)
        } yield left * right
      case IntPermTimes(p0, p1) =>
        for {
          left <- evaluatePerm(p0, model)
          right <- evaluatePerm(p1, model)
        } yield left * right
      case PermIntDiv(p0, p1) =>
        for {
          left <- evaluatePerm(p0, model)
          right <- evaluatePerm(p1, model)
          if right != Rational.zero
        } yield left / right
      case PermPlus(p0, p1) =>
        for {
          left <- evaluatePerm(p0, model)
          right <- evaluatePerm(p1, model)
        } yield left + right
      case PermMinus(p0, p1) =>
        for {
          left <- evaluatePerm(p0, model)
          right <- evaluatePerm(p1, model)
        } yield left - right
      case PermMin(p0, p1) =>
        for {
          left <- evaluatePerm(p0, model)
          right <- evaluatePerm(p1, model)
        } yield if (left <= right) left else right
      case ite: Ite if ite.t0.sort == sorts.Bool =>
        evaluateBool(ite.t0, model).flatMap {
          case true => evaluatePerm(ite.t1, model)
          case false => evaluatePerm(ite.t2, model)
        }.orElse {
          // Heuristic fallback for unresolved conditions:
          // prefer the non-zero branch when exactly one side is no permission;
          // otherwise prefer the then-branch.
          val thenPerm = evaluatePerm(ite.t1, model)
          val elsePerm = evaluatePerm(ite.t2, model)
          val thenNonZero = thenPerm.exists(_ != Rational.zero)
          val elseNonZero = elsePerm.exists(_ != Rational.zero)
          (thenPerm, elsePerm) match {
            case (Some(tp), Some(ep)) =>
              if (thenNonZero && !elseNonZero) Some(tp)
              else if (!thenNonZero && elseNonZero) Some(ep)
              else Some(tp)
            case (Some(tp), None) =>
              Some(tp)
            case (None, Some(ep)) =>
              Some(ep)
            case _ =>
              None
          }
        }
      case variable: Var if variable.sort == sorts.Perm =>
        model.flatMap(m => m.entries.get(variable.toString)).flatMap(parseRationalEntry)
      case _ =>
        None
    }

  private def evaluateInt(term: Term, model: Option[Model]): Option[BigInt] =
    term match {
      case IntLiteral(value) => Some(value)
      case Plus(p0, p1) =>
        for {
          left <- evaluateInt(p0, model)
          right <- evaluateInt(p1, model)
        } yield left + right
      case Minus(p0, p1) =>
        for {
          left <- evaluateInt(p0, model)
          right <- evaluateInt(p1, model)
        } yield left - right
      case Times(p0, p1) =>
        for {
          left <- evaluateInt(p0, model)
          right <- evaluateInt(p1, model)
        } yield left * right
      case Div(p0, p1) =>
        for {
          left <- evaluateInt(p0, model)
          right <- evaluateInt(p1, model)
          if right != 0
        } yield left / right
      case variable: Var if variable.sort == sorts.Int =>
        model.flatMap(m => m.entries.get(variable.toString)).flatMap(parseIntEntry)
      case _ =>
        None
    }

  private def evaluateBool(term: Term, model: Option[Model]): Option[Boolean] =
    term match {
      case True => Some(true)
      case False => Some(false)
      case Not(p) => evaluateBool(p, model).map(!_)
      case and: And =>
        and.ts.foldLeft(Option(true)) { (acc, element) =>
          acc.flatMap(result => evaluateBool(element, model).map(result && _))
        }
      case or: Or =>
        or.ts.foldLeft(Option(false)) { (acc, element) =>
          acc.flatMap(result => evaluateBool(element, model).map(result || _))
        }
      case cmp: Equals =>
        evaluateEquality(cmp.p0, cmp.p1, model)
      case cmp: Less =>
        for {
          left <- evaluateInt(cmp.p0, model)
          right <- evaluateInt(cmp.p1, model)
        } yield left < right
      case cmp: AtMost =>
        for {
          left <- evaluateInt(cmp.p0, model)
          right <- evaluateInt(cmp.p1, model)
        } yield left <= right
      case cmp: Greater =>
        for {
          left <- evaluateInt(cmp.p0, model)
          right <- evaluateInt(cmp.p1, model)
        } yield left > right
      case cmp: AtLeast =>
        for {
          left <- evaluateInt(cmp.p0, model)
          right <- evaluateInt(cmp.p1, model)
        } yield left >= right
      case cmp: PermLess =>
        for {
          left <- evaluatePerm(cmp.p0, model)
          right <- evaluatePerm(cmp.p1, model)
        } yield left < right
      case cmp: PermAtMost =>
        for {
          left <- evaluatePerm(cmp.p0, model)
          right <- evaluatePerm(cmp.p1, model)
        } yield left <= right
      case ite: Ite if ite.t1.sort == sorts.Bool && ite.t2.sort == sorts.Bool =>
        evaluateBool(ite.t0, model).flatMap {
          case true => evaluateBool(ite.t1, model)
          case false => evaluateBool(ite.t2, model)
        }
      case variable: Var if variable.sort == sorts.Bool =>
        model.flatMap(m => m.entries.get(variable.toString)).flatMap(parseBoolEntry)
      case _ =>
        None
    }

  private def evaluateEquality(left: Term, right: Term, model: Option[Model]): Option[Boolean] = {
    if (left == right) {
      Some(true)
    } else {
      val boolCmp = for {
        lhs <- evaluateBool(left, model)
        rhs <- evaluateBool(right, model)
      } yield lhs == rhs
      val intCmp = for {
        lhs <- evaluateInt(left, model)
        rhs <- evaluateInt(right, model)
      } yield lhs == rhs
      val permCmp = for {
        lhs <- evaluatePerm(left, model)
        rhs <- evaluatePerm(right, model)
      } yield lhs == rhs
      boolCmp.orElse(intCmp).orElse(permCmp)
    }
  }

  private def parseBoolEntry(entry: ModelEntry): Option[Boolean] =
    entry match {
      case ConstantEntry("true") => Some(true)
      case ConstantEntry("false") => Some(false)
      case ConstantEntry("1") => Some(true)
      case ConstantEntry("0") => Some(false)
      case ApplicationEntry("not", Seq(value)) => parseBoolEntry(value).map(!_)
      case ApplicationEntry("and", values) =>
        values.foldLeft(Option(true)) { (acc, value) =>
          acc.flatMap(result => parseBoolEntry(value).map(result && _))
        }
      case ApplicationEntry("or", values) =>
        values.foldLeft(Option(false)) { (acc, value) =>
          acc.flatMap(result => parseBoolEntry(value).map(result || _))
        }
      case _ => None
    }

  private def parseIntEntry(entry: ModelEntry): Option[BigInt] =
    entry match {
      case ConstantEntry(value) =>
        parseIntegerLiteral(value)
      case ApplicationEntry("-", Seq(value)) =>
        parseIntEntry(value).map(-_)
      case ApplicationEntry("+", Seq(lhs, rhs)) =>
        for {
          left <- parseIntEntry(lhs)
          right <- parseIntEntry(rhs)
        } yield left + right
      case ApplicationEntry("*", Seq(lhs, rhs)) =>
        for {
          left <- parseIntEntry(lhs)
          right <- parseIntEntry(rhs)
        } yield left * right
      case ApplicationEntry("div", Seq(lhs, rhs)) =>
        for {
          left <- parseIntEntry(lhs)
          right <- parseIntEntry(rhs)
          if right != 0
        } yield left / right
      case _ => None
    }

  private def parseRationalEntry(entry: ModelEntry): Option[Rational] =
    entry match {
      case ConstantEntry(value) => parseRationalLiteral(value)
      case ApplicationEntry("-", Seq(value)) =>
        parseRationalEntry(value).map(-_)
      case ApplicationEntry("/", Seq(lhs, rhs)) =>
        for {
          left <- parseRationalEntry(lhs)
          right <- parseRationalEntry(rhs)
          if right != Rational.zero
        } yield left / right
      case ApplicationEntry("+", Seq(lhs, rhs)) =>
        for {
          left <- parseRationalEntry(lhs)
          right <- parseRationalEntry(rhs)
        } yield left + right
      case ApplicationEntry("*", Seq(lhs, rhs)) =>
        for {
          left <- parseRationalEntry(lhs)
          right <- parseRationalEntry(rhs)
        } yield left * right
      case _ => None
    }

  private val integerLiteralRegex = "^-?[0-9]+$".r
  private val rationalLiteralRegex = "^(-?[0-9]+)/(-?[0-9]+)$".r
  private val decimalLiteralRegex = "^-?[0-9]+\\.[0-9]+$".r

  private def parseIntegerLiteral(value: String): Option[BigInt] =
    value match {
      case integerLiteralRegex() => Some(BigInt(value))
      case _ => None
    }

  private def parseRationalLiteral(value: String): Option[Rational] =
    value match {
      case "W" => Some(Rational.one)
      case "Z" => Some(Rational.zero)
      case integerLiteralRegex() =>
        Some(Rational(BigInt(value), 1))
      case rationalLiteralRegex(numer, denom) if BigInt(denom) != 0 =>
        Some(Rational(BigInt(numer), BigInt(denom)))
      case decimalLiteralRegex() =>
        decimalToRational(value)
      case _ =>
        None
    }

  private def decimalToRational(value: String): Option[Rational] =
    try {
      val decimal = BigDecimal(value)
      val unscaled = BigInt(decimal.bigDecimal.unscaledValue())
      val scale = decimal.bigDecimal.scale()
      if (scale <= 0) {
        Some(Rational(unscaled * BigInt(10).pow(-scale), 1))
      } else {
        Some(Rational(unscaled, BigInt(10).pow(scale)))
      }
    } catch {
      case _: NumberFormatException => None
    }

  private def toPermissionAmount(value: Rational): PermissionAmount =
    PermissionAmount(
      rational = value.toString,
      decimal = rationalToDecimalString(value),
    )

  private def rationalToDecimalString(value: Rational): String = {
    val decimal = BigDecimal(value.numerator) / BigDecimal(value.denominator)
    decimal.bigDecimal.stripTrailingZeros().toPlainString
  }

  private def safeRender(value: Any): String =
    try {
      String.valueOf(value)
    } catch {
      case throwable: Throwable => s"<rendering failed: ${throwable.getClass.getSimpleName}>"
    }
}
