package viper.gobra.tryfold

import viper.silver.ast.pretty.FastPrettyPrinter
import viper.silver.{ast => vpr}

import scala.collection.mutable

object PredicateDependencyGraphBuilder {

  def build(
             program: vpr.Program,
             translationMetadata: TryFoldTranslationMetadata = TryFoldTranslationMetadata.empty,
           ): PredicateDependencyGraph = {
    val acc = new MutableAccumulator
    val dynamicFamilies = translationMetadata.dynamicPredicateFamilies

    program.predicates.foreach { predicate =>
      val owner = PredicateNode(predicate.name)
      val ownerFormalParams = predicate.formalArgs.map(_.name).toVector
      val ownerFormalParamsExp = predicate.formalArgs.toVector
      acc.addNode(owner)
      predicate.body.foreach { body =>
        collectNode(owner, ownerFormalParams, ownerFormalParamsExp, body, Set(UnlabeledEdge), acc, dynamicFamilies)
      }
    }

    acc.toGraph()
  }

  private def collectNode(
                          owner: PredicateNode,
                          ownerFormalParams: Vector[String],
                          ownerFormalParamsExp: Vector[vpr.LocalVarDecl],
                          node: vpr.Node,
                          labels: Set[DependencyEdgeLabel],
                          acc: MutableAccumulator,
                          dynamicFamilies: Map[String, DynamicPredicateFamilyMetadata],
                        ): Unit = {
    val effectiveLabels: Set[DependencyEdgeLabel] =
      if (labels.nonEmpty) labels else Set[DependencyEdgeLabel](UnlabeledEdge)

    node match {
      case cond: vpr.CondExp =>
        dynamicAlternativeLabelForCondition(owner, cond, dynamicFamilies) match {
          case Some(label) =>
            val labeledBranch = (effectiveLabels - UnlabeledEdge) + label
            collectNode(owner, ownerFormalParams, ownerFormalParamsExp, cond.thn, labeledBranch, acc, dynamicFamilies)
            if (!acc.hasOutgoingEdgeWithAnyLabel(owner, labeledBranch)) {
              acc.addEdge(
                from = owner,
                to = BoolLiteralNode(value = true),
                kind = LiteralDependency,
                labels = labeledBranch,
                template = None,
              )
            }
            collectNode(owner, ownerFormalParams, ownerFormalParamsExp, cond.els, effectiveLabels, acc, dynamicFamilies)
          case None =>
            cond.subnodes.foreach(child => collectNode(owner, ownerFormalParams, ownerFormalParamsExp, child, effectiveLabels, acc, dynamicFamilies))
        }
      case pap: vpr.PredicateAccessPredicate =>
        acc.addEdge(
          from = owner,
          to = PredicateNode(pap.loc.predicateName),
          kind = PredicateDependency,
          labels = effectiveLabels,
          template = Some(EdgeCallsiteTemplate(
            ownerFormalParams = ownerFormalParams,
            calleeArgTemplates = pap.loc.args.toVector.map(render),
            ownerFormalParamsExp = ownerFormalParamsExp,
            calleeArgTemplatesExp = pap.loc.args.toVector,
          ))
        )
      case pa: vpr.PredicateAccess =>
        acc.addEdge(
          from = owner,
          to = PredicateNode(pa.predicateName),
          kind = PredicateDependency,
          labels = effectiveLabels,
          template = Some(EdgeCallsiteTemplate(
            ownerFormalParams = ownerFormalParams,
            calleeArgTemplates = pa.args.toVector.map(render),
            ownerFormalParamsExp = ownerFormalParamsExp,
            calleeArgTemplatesExp = pa.args.toVector,
          ))
        )
      case fap: vpr.FieldAccessPredicate =>
        acc.addEdge(
          from = owner,
          to = FieldNode(fap.loc.field.name),
          kind = FieldDependency,
          labels = effectiveLabels,
          template = Some(EdgeCallsiteTemplate(
            ownerFormalParams = ownerFormalParams,
            calleeArgTemplates = fap.loc.getArgs.toVector.map(render),
            ownerFormalParamsExp = ownerFormalParamsExp,
            calleeArgTemplatesExp = fap.loc.getArgs.toVector,
          ))
        )
      case fa: vpr.FieldAccess =>
        acc.addEdge(
          from = owner,
          to = FieldNode(fa.field.name),
          kind = FieldDependency,
          labels = effectiveLabels,
          template = Some(EdgeCallsiteTemplate(
            ownerFormalParams = ownerFormalParams,
            calleeArgTemplates = fa.getArgs.toVector.map(render),
            ownerFormalParamsExp = ownerFormalParamsExp,
            calleeArgTemplatesExp = fa.getArgs.toVector,
          ))
        )
      case _: vpr.TrueLit =>
        acc.addEdge(
          from = owner,
          to = BoolLiteralNode(value = true),
          kind = LiteralDependency,
          labels = effectiveLabels,
          template = None
        )
      case _: vpr.FalseLit =>
        acc.addEdge(
          from = owner,
          to = BoolLiteralNode(value = false),
          kind = LiteralDependency,
          labels = effectiveLabels,
          template = None
        )
      case _ =>
    }

    node match {
      case _: vpr.CondExp =>
      case _ =>
        node.subnodes.foreach(child => collectNode(owner, ownerFormalParams, ownerFormalParamsExp, child, effectiveLabels, acc, dynamicFamilies))
    }
  }

  private final case class EdgeKey(from: PredicateNode, to: DependencyNode, kind: DependencyKind)
  private final case class EdgeEntry(
                                      labels: mutable.LinkedHashSet[DependencyEdgeLabel],
                                      templates: mutable.LinkedHashSet[EdgeCallsiteTemplate],
                                    )

  private def render(exp: vpr.Exp): String = FastPrettyPrinter.pretty(exp).trim

  private final class MutableAccumulator {
    private val nodes = mutable.LinkedHashSet.empty[DependencyNode]
    private val edges = mutable.LinkedHashMap.empty[EdgeKey, EdgeEntry]

    def addNode(node: DependencyNode): Unit = {
      nodes += node
    }

    def addEdge(
                 from: PredicateNode,
                 to: DependencyNode,
                 kind: DependencyKind,
                 labels: Set[DependencyEdgeLabel],
                 template: Option[EdgeCallsiteTemplate],
               ): Unit = {
      nodes += from
      nodes += to
      val key = EdgeKey(from, to, kind)
      val entry = edges.getOrElseUpdate(
        key,
        EdgeEntry(
          labels = mutable.LinkedHashSet.empty,
          templates = mutable.LinkedHashSet.empty,
        )
      )
      labels.foreach(entry.labels += _)
      template.foreach(entry.templates += _)
    }

    def hasOutgoingEdgeWithAnyLabel(from: PredicateNode, labels: Set[DependencyEdgeLabel]): Boolean =
      edges.iterator.exists { case (key, entry) =>
        key.from == from && entry.labels.exists(labels.contains)
      }

    def toGraph(): PredicateDependencyGraph = {
      val normalizedEdges = edges.toVector
        .map { case (key, entry) =>
          DependencyEdge(
            from = key.from,
            to = key.to,
            kind = key.kind,
            labels = entry.labels.toSet,
            templates = entry.templates.toVector.sortBy(templateSortKey),
          )
        }
        .sortBy { edge =>
          (
            edge.from.name,
            edge.to.id,
            edge.kind.asString,
            edge.labels.toVector.map(_.repr).sorted.mkString("|"),
            edge.templates.map(templateSortKey).mkString("|"),
          )
        }

      val outgoingBase = normalizedEdges
        .groupBy(_.from)
        .map { case (from, groupedEdges) => (from: DependencyNode) -> groupedEdges }
      val incomingBase = normalizedEdges
        .groupBy(_.to)
        .map { case (to, groupedEdges) => to -> groupedEdges }

      val allNodes = nodes.toSet
      val outgoing = allNodes.map(node => node -> outgoingBase.getOrElse(node, Vector.empty)).toMap
      val incoming = allNodes.map(node => node -> incomingBase.getOrElse(node, Vector.empty)).toMap

      PredicateDependencyGraph(
        nodes = allNodes,
        edges = normalizedEdges,
        outgoing = outgoing,
        incoming = incoming,
      )
    }

    private def templateSortKey(template: EdgeCallsiteTemplate): String = {
      val formals = template.ownerFormalParams.mkString(",")
      val args = template.calleeArgTemplates.mkString(",")
      s"$formals=>$args"
    }
  }

  private def dynamicAlternativeLabelForCondition(
                                                   owner: PredicateNode,
                                                   cond: vpr.CondExp,
                                                   dynamicFamilies: Map[String, DynamicPredicateFamilyMetadata],
                                                 ): Option[DynamicAlternativeLabel] =
    dynamicFamilies.get(owner.name).flatMap { family =>
      cond.cond match {
        case vpr.EqCmp(left: vpr.Exp, right: vpr.Exp) =>
          dynamicAlternativeTypeKey(left, right, family)
            .orElse(dynamicAlternativeTypeKey(right, left, family))
            .map(DynamicAlternativeLabel)
        case _ =>
          None
      }
    }

  private def dynamicAlternativeTypeKey(
                                         maybeTypeSelector: vpr.Exp,
                                         maybeTypeExpr: vpr.Exp,
                                         family: DynamicPredicateFamilyMetadata,
                                       ): Option[String] =
    if (isDynamicReceiverTypeSelector(maybeTypeSelector, family)) {
      family.typeExprToKey.get(render(maybeTypeExpr))
    } else {
      None
    }

  private def isDynamicReceiverTypeSelector(
                                             exp: vpr.Exp,
                                             family: DynamicPredicateFamilyMetadata,
                                           ): Boolean = {
    val expectedGetter = s"get${family.receiverTupleTypeSlot}of${family.receiverTupleArity}"
    exp match {
      case app: vpr.DomainFuncApp if app.funcname == expectedGetter && app.args.size == 1 =>
        app.args.head match {
          case local: vpr.AbstractLocalVar => local.name == family.receiverFormalName
          case _ => false
        }
      case _ =>
        false
    }
  }
}
