package viper.gobra.tryfold

import viper.silver.{ast => vpr}

sealed trait DependencyNode {
  def id: String
}

final case class PredicateNode(name: String) extends DependencyNode {
  override val id: String = s"pred:$name"
}

final case class FieldNode(name: String) extends DependencyNode {
  override val id: String = s"field:$name"
}

final case class BoolLiteralNode(value: Boolean) extends DependencyNode {
  override val id: String = if (value) "bool:true" else "bool:false"
}

sealed trait DependencyKind {
  def asString: String
}

case object PredicateDependency extends DependencyKind {
  override val asString: String = "predicate"
}

case object FieldDependency extends DependencyKind {
  override val asString: String = "field"
}

case object LiteralDependency extends DependencyKind {
  override val asString: String = "literal"
}

sealed trait DependencyEdgeLabel {
  def repr: String
}

case object UnlabeledEdge extends DependencyEdgeLabel {
  override val repr: String = "unlabeled"
}

final case class DynamicAlternativeLabel(typeKey: String) extends DependencyEdgeLabel {
  override val repr: String = s"dynamic:$typeKey"
}

final case class EdgeCallsiteTemplate(
                                       ownerFormalParams: Vector[String],
                                       calleeArgTemplates: Vector[String],
                                       ownerFormalParamsExp: Vector[vpr.LocalVarDecl] = Vector.empty,
                                       calleeArgTemplatesExp: Vector[vpr.Exp] = Vector.empty,
                                     )

final case class DependencyEdge(
                                 from: PredicateNode,
                                 to: DependencyNode,
                                 kind: DependencyKind,
                                 labels: Set[DependencyEdgeLabel],
                                 templates: Vector[EdgeCallsiteTemplate] = Vector.empty,
                               )

final case class PredicateDependencyGraph(
                                           nodes: Set[DependencyNode],
                                           edges: Vector[DependencyEdge],
                                           outgoing: Map[DependencyNode, Vector[DependencyEdge]],
                                           incoming: Map[DependencyNode, Vector[DependencyEdge]],
                                         ) {
  def edgesFrom(node: DependencyNode): Vector[DependencyEdge] =
    outgoing.getOrElse(node, Vector.empty)

  def edgesTo(node: DependencyNode): Vector[DependencyEdge] =
    incoming.getOrElse(node, Vector.empty)

  def findEdge(fromPredicateName: String, toNodeId: String): Option[DependencyEdge] = {
    val from = PredicateNode(fromPredicateName)
    edgesFrom(from).find(_.to.id == toNodeId)
  }
}
