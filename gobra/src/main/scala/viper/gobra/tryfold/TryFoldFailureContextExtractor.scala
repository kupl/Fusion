package viper.gobra.tryfold

import viper.gobra.backend.{BackendVerifier, TryFoldSourcePermissionExtractor}
import viper.silicon.interfaces.SiliconDebuggingFailureContext
import viper.silver.{ast => vpr}
import viper.silver.verifier.VerificationError
import viper.silver.verifier.reasons.InsufficientPermission

object TryFoldFailureContextExtractor {

  final case class StoreBindingEntry(
                                      name: String,
                                      typ: vpr.Type,
                                      typRepr: String,
                                      exp: vpr.Exp,
                                    )

  final case class FailureEndpoints(
                                     sources: Set[DependencyNode],
                                     target: DependencyNode,
                                     sourcePermissions: Vector[TryFoldSourcePermissionExtractor.SourcePermissionEntry] = Vector.empty,
                                     targetPermissions: Vector[TryFoldTargetPermissionExtractor.TargetPermissionEntry] = Vector.empty,
                                   )

  def extractFirstFailureEndpoints(failure: BackendVerifier.Failure): Option[FailureEndpoints] = {
    val firstErrorOpt = failure.errors.headOption
    firstErrorOpt.flatMap { firstError =>
      val context = extractDebuggingContext(firstError)
      val targetPermissions = TryFoldTargetPermissionExtractor.extract(firstError, context)
      extractTarget(firstError, targetPermissions.entries).map { target =>
        val extractedSources = extractSources(context).getOrElse(
          ExtractedSources(
            nodes = Set.empty,
            permissions = Vector.empty,
          )
        )
        FailureEndpoints(
        sources = extractedSources.nodes,
        target = target,
        sourcePermissions = extractedSources.permissions,
        targetPermissions = targetPermissions.entries,
      )
      }
    }
  }

  def extractFirstDebuggingContext(failure: BackendVerifier.Failure): Option[SiliconDebuggingFailureContext] =
    failure.errors.headOption.flatMap(extractDebuggingContext)

  def extractFirstStoreBindingEntries(failure: BackendVerifier.Failure): Vector[StoreBindingEntry] =
    extractFirstDebuggingContext(failure)
      .flatMap(_.state)
      .map { state =>
        state.g.values.collect {
          case (localVar, (_, Some(exp))) =>
            StoreBindingEntry(
              name = localVar.name,
              typ = localVar.typ,
              typRepr = safeRender(localVar.typ),
              exp = exp,
            )
        }.toVector
      }
      .getOrElse(Vector.empty)

  def extractFirstStoreBindings(failure: BackendVerifier.Failure): Map[String, vpr.Exp] =
    extractFirstStoreBindingEntries(failure)
      .foldLeft(scala.collection.mutable.LinkedHashMap.empty[String, vpr.Exp]) { (acc, entry) =>
        if (!acc.contains(entry.name)) acc += (entry.name -> entry.exp)
        acc
      }
      .toMap

  private def extractTarget(error: VerificationError, targetPermissions: Vector[TryFoldTargetPermissionExtractor.TargetPermissionEntry]): Option[DependencyNode] =
    extractTargetFromReason(error)
      .orElse(targetPermissions.headOption.flatMap(targetEntryToNode))

  private final case class ExtractedSources(
                                             nodes: Set[DependencyNode],
                                             permissions: Vector[TryFoldSourcePermissionExtractor.SourcePermissionEntry],
                                           )

  private[tryfold] def extractDebuggingContext(error: VerificationError): Option[SiliconDebuggingFailureContext] =
    error.failureContexts.collectFirst {
      case context: SiliconDebuggingFailureContext if context.state.isDefined => context
    }

  private def extractSources(context: Option[SiliconDebuggingFailureContext]): Option[ExtractedSources] = {
    context.map { ctx =>
      val permissions = TryFoldSourcePermissionExtractor.extractFromState(
        state = ctx.state.get,
        counterexample = ctx.counterExample,
      )
      val nodes = permissions.flatMap(permissionEntryToNode).toSet
      ExtractedSources(nodes = nodes, permissions = permissions)
    }
  }

  private def extractTargetFromReason(error: VerificationError): Option[DependencyNode] =
    error.reason match {
      case InsufficientPermission(offendingNode) =>
        locationAccessToNode(offendingNode)
      case _ =>
        None
    }

  private def targetEntryToNode(entry: TryFoldTargetPermissionExtractor.TargetPermissionEntry): Option[DependencyNode] =
    entry.nodeKind match {
      case "predicate" => Some(PredicateNode(entry.nodeName))
      case "field" => Some(FieldNode(entry.nodeName))
      case _ => None
    }

  private def locationAccessToNode(access: vpr.LocationAccess): Option[DependencyNode] = {
    access match {
      case predicateAccess: vpr.PredicateAccess =>
        Some(PredicateNode(predicateAccess.predicateName))
      case fieldAccess: vpr.FieldAccess =>
        Some(FieldNode(fieldAccess.field.name))
      case _ =>
        None
    }
  }

  private def permissionEntryToNode(entry: TryFoldSourcePermissionExtractor.SourcePermissionEntry): Option[DependencyNode] =
    entry.nodeKind match {
      case "predicate" => Some(PredicateNode(entry.nodeName))
      case "field" => Some(FieldNode(entry.nodeName))
      case _ => None
    }

  private def safeRender(value: Any): String =
    try String.valueOf(value)
    catch {
      case throwable: Throwable => s"<rendering failed: ${throwable.getClass.getSimpleName}>"
    }
}
