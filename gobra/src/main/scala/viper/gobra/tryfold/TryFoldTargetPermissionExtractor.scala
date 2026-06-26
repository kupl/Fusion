package viper.gobra.tryfold

import viper.gobra.backend.TryFoldSourcePermissionExtractor.PermissionAmount
import viper.silicon.debugger.DebugExp
import viper.silicon.interfaces.SiliconDebuggingFailureContext
import viper.silver.utility.Common.Rational
import viper.silver.verifier.{ApplicationEntry, ConstantEntry, Model, ModelEntry, VerificationError}
import viper.silver.verifier.reasons.InsufficientPermission
import viper.silver.{ast => vpr}

import scala.collection.mutable

object TryFoldTargetPermissionExtractor {

  final case class TargetPermissionEntry(
                                          index: Int,
                                          nodeKind: String,
                                          nodeName: String,
                                          nodeId: String,
                                          arguments: Vector[String],
                                          argumentsExp: Option[Vector[vpr.Exp]],
                                          access: String,
                                          permissionTerm: Option[String],
                                          evaluatedPermission: Option[PermissionAmount],
                                          evaluationKind: String,
                                          extractionSource: String,
                                          matchesReasonLocation: Boolean,
                                        )

  final case class ExtractionResult(
                                     entries: Vector[TargetPermissionEntry],
                                   )

  def extract(error: VerificationError, context: Option[SiliconDebuggingFailureContext]): ExtractionResult = {
    val model = context.flatMap(_.counterExample.map(_.model))
    val reasonLocation = extractReasonLocation(error)

    val accessCandidatesFromError = collectAccessPredicates(error.offendingNode)
      .flatMap { access =>
        access.loc match {
          case loc: vpr.LocationAccess => Some((loc, access.perm, "error.offendingNode"))
          case _ => None
        }
      }
    val accessCandidatesFromFailedAssertion = context.toVector
      .flatMap(ctx => collectAccessPredicatesFromDebugExp(ctx.failedAssertionExp))
      .flatMap { access =>
        access.loc match {
          case loc: vpr.LocationAccess => Some((loc, access.perm, "failedAssertionExp.accessPredicate"))
          case _ => None
        }
      }
    val currentPermCandidates = context.toVector
      .flatMap(ctx => collectCurrentPermRequirements(ctx.failedAssertionExp))
      .map { case (loc, needed) => (loc, needed, "failedAssertionExp.currentPermCmp") }

    val allCandidates = accessCandidatesFromError ++ accessCandidatesFromFailedAssertion ++ currentPermCandidates

    val entries = allCandidates.zipWithIndex.flatMap { case ((loc, permExp, source), idx) =>
      toEntry(
        location = loc,
        permissionExp = Option(permExp),
        source = source,
        index = idx,
        reasonLocation = reasonLocation,
        model = model,
      )
    }

    val locationOnlyFallback = reasonLocation.flatMap { loc =>
      val hasMatchingCandidate = entries.exists(_.matchesReasonLocation)
      if (hasMatchingCandidate) {
        None
      } else {
        toEntry(
          location = loc,
          permissionExp = None,
          source = "reason.locationAccess",
          index = entries.size,
          reasonLocation = reasonLocation,
          model = model,
        )
      }
    }.toVector

    val merged = deduplicate(entries ++ locationOnlyFallback)
    val ordered = prioritize(merged, reasonLocation)
    ExtractionResult(entries = ordered)
  }

  private def extractReasonLocation(error: VerificationError): Option[vpr.LocationAccess] =
    error.reason match {
      case InsufficientPermission(offendingNode) => Some(offendingNode)
      case _ => None
    }

  private def collectAccessPredicatesFromDebugExp(debugExp: DebugExp): Vector[vpr.AccessPredicate] = {
    val visited = mutable.HashSet.empty[Int]
    val expressions = mutable.ArrayBuffer.empty[vpr.Exp]

    def loop(node: DebugExp): Unit = {
      if (!visited.contains(node.id)) {
        visited += node.id
        node.originalExp.foreach(expressions += _)
        node.finalExp.foreach(expressions += _)
        node.children.foreach(loop)
      }
    }

    loop(debugExp)
    expressions.toVector.flatMap(collectAccessPredicates)
  }

  private def collectCurrentPermRequirements(debugExp: DebugExp): Vector[(vpr.LocationAccess, vpr.Exp)] = {
    val visited = mutable.HashSet.empty[Int]
    val expressions = mutable.ArrayBuffer.empty[vpr.Exp]

    def loop(node: DebugExp): Unit = {
      if (!visited.contains(node.id)) {
        visited += node.id
        node.originalExp.foreach(expressions += _)
        node.finalExp.foreach(expressions += _)
        node.children.foreach(loop)
      }
    }

    loop(debugExp)
    expressions.toVector.flatMap(collectCurrentPermRequirementsFromExp)
  }

  private def collectAccessPredicates(node: vpr.Node): Vector[vpr.AccessPredicate] = {
    val current = node match {
      case access: vpr.AccessPredicate => Vector(access)
      case _ => Vector.empty
    }
    val children = node.subnodes.toVector.flatMap(collectAccessPredicates)
    current ++ children
  }

  private def collectCurrentPermRequirementsFromExp(exp: vpr.Exp): Vector[(vpr.LocationAccess, vpr.Exp)] = {
    val current = exp match {
      case vpr.PermLtCmp(vpr.CurrentPerm(loc: vpr.LocationAccess), needed) => Vector(loc -> needed)
      case vpr.PermLeCmp(vpr.CurrentPerm(loc: vpr.LocationAccess), needed) => Vector(loc -> needed)
      case vpr.PermGtCmp(needed, vpr.CurrentPerm(loc: vpr.LocationAccess)) => Vector(loc -> needed)
      case vpr.PermGeCmp(needed, vpr.CurrentPerm(loc: vpr.LocationAccess)) => Vector(loc -> needed)
      case _ => Vector.empty
    }
    val nested = exp.subnodes.toVector.collect { case childExp: vpr.Exp => childExp }
      .flatMap(collectCurrentPermRequirementsFromExp)
    current ++ nested
  }

  private def toEntry(
                       location: vpr.LocationAccess,
                       permissionExp: Option[vpr.Exp],
                       source: String,
                       index: Int,
                       reasonLocation: Option[vpr.LocationAccess],
                       model: Option[Model],
                     ): Option[TargetPermissionEntry] =
    locationToNode(location).map { node =>
      val evaluated = permissionExp.flatMap(exp => evaluatePerm(exp, model).map(toPermissionAmount))
      val evaluationKind =
        if (permissionExp.isEmpty) "missing"
        else if (evaluated.isDefined) "exact"
        else if (permissionExp.exists(_.isInstanceOf[vpr.CondExp])) "conditional"
        else "symbolic"
      TargetPermissionEntry(
        index = index,
        nodeKind = nodeKind(node),
        nodeName = nodeName(node),
        nodeId = node.id,
        arguments = locationArguments(location),
        argumentsExp = locationArgumentsExp(location),
        access = safeRender(location),
        permissionTerm = permissionExp.map(safeRender),
        evaluatedPermission = evaluated,
        evaluationKind = evaluationKind,
        extractionSource = source,
        matchesReasonLocation = reasonLocation.exists(reasonLoc => sameLocation(reasonLoc, location)),
      )
    }

  private def deduplicate(entries: Vector[TargetPermissionEntry]): Vector[TargetPermissionEntry] =
    entries
      .groupBy(entry => s"${entry.nodeId}|${entry.access}|${entry.permissionTerm.getOrElse("")}|${entry.extractionSource}")
      .values
      .map(_.head)
      .toVector
      .sortBy(entry => (entry.index, entry.nodeId, entry.access, entry.extractionSource))

  private def prioritize(entries: Vector[TargetPermissionEntry], reasonLocation: Option[vpr.LocationAccess]): Vector[TargetPermissionEntry] = {
    val reasonNodeId = reasonLocation.flatMap(locationToNode).map(_.id)
    entries.sortBy { entry =>
      val reasonNodePriority = reasonNodeId match {
        case Some(id) if entry.nodeId == id => 0
        case Some(_) => 1
        case None => 0
      }
      val valuePriority = if (entry.evaluatedPermission.isDefined) 0 else if (entry.permissionTerm.isDefined) 1 else 2
      val locationPriority = if (entry.matchesReasonLocation) 0 else 1
      val sourcePriority = entry.extractionSource match {
        case "error.offendingNode" => 0
        case "failedAssertionExp.accessPredicate" => 1
        case "failedAssertionExp.currentPermCmp" => 2
        case "reason.locationAccess" => 3
        case _ => 4
      }
      (reasonNodePriority, valuePriority, locationPriority, sourcePriority, entry.index)
    }
  }

  private def locationToNode(location: vpr.LocationAccess): Option[DependencyNode] =
    location match {
      case predicateAccess: vpr.PredicateAccess => Some(PredicateNode(predicateAccess.predicateName))
      case fieldAccess: vpr.FieldAccess => Some(FieldNode(fieldAccess.field.name))
      case _ => None
    }

  private def nodeKind(node: DependencyNode): String =
    node match {
      case _: PredicateNode => "predicate"
      case _: FieldNode => "field"
      case _: BoolLiteralNode => "boolLiteral"
    }

  private def nodeName(node: DependencyNode): String =
    node match {
      case PredicateNode(name) => name
      case FieldNode(name) => name
      case BoolLiteralNode(value) => value.toString
    }

  private def sameLocation(left: vpr.LocationAccess, right: vpr.LocationAccess): Boolean =
    (left, right) match {
      case (lp: vpr.PredicateAccess, rp: vpr.PredicateAccess) =>
        lp.predicateName == rp.predicateName && safeRender(lp) == safeRender(rp)
      case (lf: vpr.FieldAccess, rf: vpr.FieldAccess) =>
        lf.field.name == rf.field.name && safeRender(lf) == safeRender(rf)
      case _ =>
        false
    }

  private def evaluatePerm(exp: vpr.Exp, model: Option[Model]): Option[Rational] =
    exp match {
      case _: vpr.FullPerm => Some(Rational.one)
      case _: vpr.NoPerm => Some(Rational.zero)
      case vpr.FractionalPerm(numer, denom) =>
        for {
          n <- evaluateInt(numer, model)
          d <- evaluateInt(denom, model)
          if d != 0
        } yield Rational(n, d)
      case vpr.PermDiv(left, right) =>
        for {
          l <- evaluatePerm(left, model)
          r <- evaluateInt(right, model)
          if r != 0
        } yield l / Rational(r, 1)
      case vpr.PermPermDiv(left, right) =>
        for {
          l <- evaluatePerm(left, model)
          r <- evaluatePerm(right, model)
          if r != Rational.zero
        } yield l / r
      case vpr.PermAdd(left, right) =>
        for {
          l <- evaluatePerm(left, model)
          r <- evaluatePerm(right, model)
        } yield l + r
      case vpr.PermSub(left, right) =>
        for {
          l <- evaluatePerm(left, model)
          r <- evaluatePerm(right, model)
        } yield l - r
      case vpr.PermMul(left, right) =>
        for {
          l <- evaluatePerm(left, model)
          r <- evaluatePerm(right, model)
        } yield l * r
      case vpr.IntPermMul(left, right) =>
        for {
          l <- evaluateInt(left, model)
          r <- evaluatePerm(right, model)
        } yield Rational(l, 1) * r
      case vpr.PermMinus(inner) =>
        evaluatePerm(inner, model).map(-_)
      case cond: vpr.CondExp =>
        evaluateBool(cond.cond, model).flatMap {
          case true => evaluatePerm(cond.thn, model)
          case false => evaluatePerm(cond.els, model)
        }.orElse {
          val thenPerm = evaluatePerm(cond.thn, model)
          val elsePerm = evaluatePerm(cond.els, model)
          val thenNonZero = thenPerm.exists(_ != Rational.zero)
          val elseNonZero = elsePerm.exists(_ != Rational.zero)
          (thenPerm, elsePerm) match {
            case (Some(tp), Some(ep)) =>
              if (thenNonZero && !elseNonZero) Some(tp)
              else if (!thenNonZero && elseNonZero) Some(ep)
              else Some(tp)
            case (Some(tp), None) => Some(tp)
            case (None, Some(ep)) => Some(ep)
            case _ => None
          }
        }
      case local: vpr.LocalVar if local.typ == vpr.Perm =>
        model.flatMap(m => m.entries.get(local.name)).flatMap(parseRationalEntry)
      case _ =>
        None
    }

  private def locationArguments(location: vpr.LocationAccess): Vector[String] =
    location match {
      case predicateAccess: vpr.PredicateAccess =>
        predicateAccess.args.toVector.map(safeRender)
      case fieldAccess: vpr.FieldAccess =>
        fieldAccess.getArgs.toVector.map(safeRender)
      case _ =>
        Vector.empty
    }

  private def locationArgumentsExp(location: vpr.LocationAccess): Option[Vector[vpr.Exp]] =
    location match {
      case predicateAccess: vpr.PredicateAccess =>
        Some(predicateAccess.args.toVector)
      case fieldAccess: vpr.FieldAccess =>
        Some(fieldAccess.getArgs.toVector)
      case _ =>
        None
    }

  private def evaluateInt(exp: vpr.Exp, model: Option[Model]): Option[BigInt] =
    exp match {
      case vpr.IntLit(value) => Some(value)
      case vpr.Add(left, right) =>
        for {
          l <- evaluateInt(left, model)
          r <- evaluateInt(right, model)
        } yield l + r
      case vpr.Sub(left, right) =>
        for {
          l <- evaluateInt(left, model)
          r <- evaluateInt(right, model)
        } yield l - r
      case vpr.Mul(left, right) =>
        for {
          l <- evaluateInt(left, model)
          r <- evaluateInt(right, model)
        } yield l * r
      case vpr.Div(left, right) =>
        for {
          l <- evaluateInt(left, model)
          r <- evaluateInt(right, model)
          if r != 0
        } yield l / r
      case vpr.Minus(inner) =>
        evaluateInt(inner, model).map(-_)
      case local: vpr.LocalVar if local.typ == vpr.Int =>
        model.flatMap(m => m.entries.get(local.name)).flatMap(parseIntEntry)
      case _ =>
        None
    }

  private def evaluateBool(exp: vpr.Exp, model: Option[Model]): Option[Boolean] =
    exp match {
      case _: vpr.TrueLit => Some(true)
      case _: vpr.FalseLit => Some(false)
      case vpr.Not(inner) =>
        evaluateBool(inner, model).map(!_ )
      case vpr.And(left, right) =>
        for {
          l <- evaluateBool(left, model)
          r <- evaluateBool(right, model)
        } yield l && r
      case vpr.Or(left, right) =>
        for {
          l <- evaluateBool(left, model)
          r <- evaluateBool(right, model)
        } yield l || r
      case vpr.Implies(left, right) =>
        for {
          l <- evaluateBool(left, model)
          r <- evaluateBool(right, model)
        } yield !l || r
      case vpr.EqCmp(left, right) =>
        evaluateEquality(left, right, model)
      case vpr.NeCmp(left, right) =>
        evaluateEquality(left, right, model).map(!_ )
      case vpr.LtCmp(left, right) =>
        for {
          l <- evaluateInt(left, model)
          r <- evaluateInt(right, model)
        } yield l < r
      case vpr.LeCmp(left, right) =>
        for {
          l <- evaluateInt(left, model)
          r <- evaluateInt(right, model)
        } yield l <= r
      case vpr.GtCmp(left, right) =>
        for {
          l <- evaluateInt(left, model)
          r <- evaluateInt(right, model)
        } yield l > r
      case vpr.GeCmp(left, right) =>
        for {
          l <- evaluateInt(left, model)
          r <- evaluateInt(right, model)
        } yield l >= r
      case vpr.PermLtCmp(left, right) =>
        for {
          l <- evaluatePerm(left, model)
          r <- evaluatePerm(right, model)
        } yield l < r
      case vpr.PermLeCmp(left, right) =>
        for {
          l <- evaluatePerm(left, model)
          r <- evaluatePerm(right, model)
        } yield l <= r
      case vpr.PermGtCmp(left, right) =>
        for {
          l <- evaluatePerm(left, model)
          r <- evaluatePerm(right, model)
        } yield l > r
      case vpr.PermGeCmp(left, right) =>
        for {
          l <- evaluatePerm(left, model)
          r <- evaluatePerm(right, model)
        } yield l >= r
      case cond: vpr.CondExp if cond.typ == vpr.Bool =>
        evaluateBool(cond.cond, model).flatMap {
          case true => evaluateBool(cond.thn, model)
          case false => evaluateBool(cond.els, model)
        }
      case local: vpr.LocalVar if local.typ == vpr.Bool =>
        model.flatMap(m => m.entries.get(local.name)).flatMap(parseBoolEntry)
      case _ =>
        None
    }

  private def evaluateEquality(left: vpr.Exp, right: vpr.Exp, model: Option[Model]): Option[Boolean] = {
    if (left == right) {
      Some(true)
    } else {
      val intEq = for {
        l <- evaluateInt(left, model)
        r <- evaluateInt(right, model)
      } yield l == r
      val boolEq = for {
        l <- evaluateBool(left, model)
        r <- evaluateBool(right, model)
      } yield l == r
      val permEq = for {
        l <- evaluatePerm(left, model)
        r <- evaluatePerm(right, model)
      } yield l == r
      intEq.orElse(boolEq).orElse(permEq)
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
        values.foldLeft(Option(true)) { (acc, value) => acc.flatMap(result => parseBoolEntry(value).map(result && _)) }
      case ApplicationEntry("or", values) =>
        values.foldLeft(Option(false)) { (acc, value) => acc.flatMap(result => parseBoolEntry(value).map(result || _)) }
      case _ =>
        None
    }

  private def parseIntEntry(entry: ModelEntry): Option[BigInt] =
    entry match {
      case ConstantEntry(value) =>
        parseIntegerLiteral(value)
      case ApplicationEntry("-", Seq(value)) =>
        parseIntEntry(value).map(-_)
      case ApplicationEntry("+", Seq(lhs, rhs)) =>
        for {
          l <- parseIntEntry(lhs)
          r <- parseIntEntry(rhs)
        } yield l + r
      case ApplicationEntry("*", Seq(lhs, rhs)) =>
        for {
          l <- parseIntEntry(lhs)
          r <- parseIntEntry(rhs)
        } yield l * r
      case ApplicationEntry("div", Seq(lhs, rhs)) =>
        for {
          l <- parseIntEntry(lhs)
          r <- parseIntEntry(rhs)
          if r != 0
        } yield l / r
      case _ =>
        None
    }

  private def parseRationalEntry(entry: ModelEntry): Option[Rational] =
    entry match {
      case ConstantEntry(value) =>
        parseRationalLiteral(value)
      case ApplicationEntry("-", Seq(value)) =>
        parseRationalEntry(value).map(-_)
      case ApplicationEntry("/", Seq(lhs, rhs)) =>
        for {
          l <- parseRationalEntry(lhs)
          r <- parseRationalEntry(rhs)
          if r != Rational.zero
        } yield l / r
      case ApplicationEntry("+", Seq(lhs, rhs)) =>
        for {
          l <- parseRationalEntry(lhs)
          r <- parseRationalEntry(rhs)
        } yield l + r
      case ApplicationEntry("*", Seq(lhs, rhs)) =>
        for {
          l <- parseRationalEntry(lhs)
          r <- parseRationalEntry(rhs)
        } yield l * r
      case _ =>
        None
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
