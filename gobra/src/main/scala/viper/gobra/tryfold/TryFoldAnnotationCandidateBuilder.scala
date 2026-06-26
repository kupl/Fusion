package viper.gobra.tryfold

import viper.gobra.backend.TryFoldSourcePermissionExtractor.{PermissionAmount, SourcePermissionEntry}
import viper.silver.ast.utility.Expressions
import viper.silver.ast.utility.Nodes
import viper.silver.{ast => vpr}

import java.util.regex.{Matcher, Pattern}
import scala.collection.mutable

object TryFoldAnnotationCandidateBuilder {

  private[tryfold] object PermissionEvidenceRole {
    val SourceHeap: String = "source_heap"
    val TargetPrimary: String = "target_primary"
    val TargetSupportArgsOnly: String = "target_support_args_only"
  }

  private final case class TargetBindingContext(
                                                 primary: Option[TryFoldTargetPermissionExtractor.TargetPermissionEntry],
                                                 support: Vector[TryFoldTargetPermissionExtractor.TargetPermissionEntry],
                                               )

  final case class ConcreteAccessInstance(
                                           nodeId: String,
                                           nodeKind: String,
                                           nodeName: String,
                                           args: Vector[String],
                                           argsExp: Option[Vector[vpr.Exp]],
                                           permission: Option[PermissionAmount],
                                           permissionIsWildcard: Boolean,
                                           permissionSymbolicTerm: Option[String],
                                           origin: String,
                                           evaluationKind: String,
                                           permissionEvidenceRole: String,
                                           wildcardEligible: Boolean,
                                         )

  private final case class InferredPermission(
                                               permission: Option[PermissionAmount],
                                               permissionIsWildcard: Boolean,
                                               permissionSymbolicTerm: Option[String],
                                               permissionOrigin: Option[String],
                                             )

  final case class MaterializationDrop(
                                        pathIndex: Int,
                                        reason: String,
                                        stepIndex: Option[Int],
                                        fromNodeId: Option[String],
                                        fromNodeName: Option[String],
                                        details: Option[String],
                                      )

  final case class MaterializationOutcome(
                                           sequences: Vector[TryFoldWorklistEngine.AnnotationSequence],
                                           drops: Vector[MaterializationDrop],
                                         )

  final case class MaterializationStats(
                                         pathCount: Int,
                                         pathsWithConcreteCandidates: Int,
                                         droppedPathCount: Int,
                                         totalRawConcreteCandidates: Int,
                                         totalDrops: Int,
                                         dropReasonCounts: Map[String, Int],
                                       )

  def materializeSequencesForPath(
                                   path: TryFoldPathExplorer.Path,
                                   endpoints: TryFoldFailureContextExtractor.FailureEndpoints,
                                   maxConcreteCandidatesPerPath: Int,
                                 ): Vector[TryFoldWorklistEngine.AnnotationSequence] = {
    materializeWithDiagnosticsForPath(
      path = path,
      pathIndex = -1,
      endpoints = endpoints,
      maxConcreteCandidatesPerPath = maxConcreteCandidatesPerPath,
    ).sequences
  }

  def materializeWithDiagnosticsForPath(
                                         path: TryFoldPathExplorer.Path,
                                         pathIndex: Int,
                                         endpoints: TryFoldFailureContextExtractor.FailureEndpoints,
                                         maxConcreteCandidatesPerPath: Int,
                                       ): MaterializationOutcome = {
    if (maxConcreteCandidatesPerPath <= 0 || path.steps.isEmpty) {
      MaterializationOutcome(
        sequences = Vector.empty,
        drops = Vector(
          MaterializationDrop(
            pathIndex = pathIndex,
            reason = "skipped_invalid_bound_or_empty_path",
            stepIndex = None,
            fromNodeId = None,
            fromNodeName = None,
            details = Some(s"pathStepCount=${path.steps.size}, maxConcreteCandidatesPerPath=$maxConcreteCandidatesPerPath"),
          )
        ),
      )
    } else {
      val targetBindingContexts = enumerateTargetBindingContextsForPath(path, endpoints)
      val bindingOutcomes = targetBindingContexts.map { bindingContext =>
        val seeded = seedConcreteInstances(
          endpoints = endpoints,
          activeTargetBinding = bindingContext.primary,
          supportTargetBindings = bindingContext.support,
        )
        val propagated = propagateAlongPath(path, seeded)
        buildConcreteSequences(
          path = path,
          pathIndex = pathIndex,
          instancesByNode = propagated,
          endpoints = endpoints,
          maxConcreteCandidatesPerPath = maxConcreteCandidatesPerPath,
          activeTargetBinding = bindingContext.primary,
        )
      }
      val combinedSequences = deduplicateSequences(bindingOutcomes.flatMap(_.sequences).map(_.steps))
        .sortBy(directiveSeqSortKey)
        .take(maxConcreteCandidatesPerPath)
        .map(steps => TryFoldWorklistEngine.AnnotationSequence(steps))
      val combinedDrops =
        if (combinedSequences.nonEmpty) Vector.empty
        else deduplicateDrops(bindingOutcomes.flatMap(_.drops))
      MaterializationOutcome(sequences = combinedSequences, drops = combinedDrops)
    }
  }

  def summarizeMaterializationOutcomes(
                                        pathCount: Int,
                                        outcomes: Vector[MaterializationOutcome],
                                      ): MaterializationStats = {
    val pathsWithConcreteCandidates = outcomes.count(_.sequences.nonEmpty)
    val totalRawConcreteCandidates = outcomes.map(_.sequences.size).sum
    val allDrops = outcomes.flatMap(_.drops)
    val reasonCounts = allDrops
      .groupBy(_.reason)
      .view
      .mapValues(_.size)
      .toMap
    MaterializationStats(
      pathCount = pathCount,
      pathsWithConcreteCandidates = pathsWithConcreteCandidates,
      droppedPathCount = math.max(0, pathCount - pathsWithConcreteCandidates),
      totalRawConcreteCandidates = totalRawConcreteCandidates,
      totalDrops = allDrops.size,
      dropReasonCounts = reasonCounts,
    )
  }

  private def seedConcreteInstances(
                                     endpoints: TryFoldFailureContextExtractor.FailureEndpoints,
                                     activeTargetBinding: Option[TryFoldTargetPermissionExtractor.TargetPermissionEntry],
                                     supportTargetBindings: Vector[TryFoldTargetPermissionExtractor.TargetPermissionEntry],
                                   ): Map[String, Vector[ConcreteAccessInstance]] = {
    val seeds = mutable.LinkedHashMap.empty[String, mutable.LinkedHashMap[String, ConcreteAccessInstance]]

    def add(instance: ConcreteAccessInstance): Unit = {
      val byKey = seeds.getOrElseUpdate(instance.nodeId, mutable.LinkedHashMap.empty[String, ConcreteAccessInstance])
      val key = instanceKey(instance)
      if (!byKey.contains(key)) {
        byKey.put(key, instance)
      }
    }

    endpoints.sourcePermissions.flatMap(sourceEntryToInstance).foreach(add)
    activeTargetBinding
      .flatMap(targetEntryToInstance(_, PermissionEvidenceRole.TargetPrimary, allowSymbolicWildcard = true))
      .foreach(add)
    supportTargetBindings
      .flatMap(targetEntryToInstance(_, PermissionEvidenceRole.TargetSupportArgsOnly, allowSymbolicWildcard = false))
      .foreach(add)

    pruneEmptyArgumentInstancesPerNode(seeds.toVector.map { case (nodeId, byKey) =>
      nodeId -> byKey.values.toVector.sortBy(instanceSortKey)
    }.toMap)
  }

  private[tryfold] def sourceEntryToInstance(entry: SourcePermissionEntry): Option[ConcreteAccessInstance] = {
    if (!isSupportedNodeKind(entry.nodeKind)) {
      None
    } else {
      val args =
        if (entry.singletonArguments.nonEmpty) entry.singletonArguments
        else entry.arguments
      val argsExp =
        if (entry.singletonArgumentsExp.exists(_.nonEmpty)) entry.singletonArgumentsExp
        else entry.argumentsExp
      val symbolicTerm = entry.bodyPermissionTerm.orElse(Option(entry.permissionTerm).filter(_.nonEmpty))
      val wildcard = entry.evaluatedBodyPermission.orElse(entry.evaluatedPermission).isEmpty &&
        isSymbolicOrConditional(entry.evaluationKind) &&
        symbolicTerm.nonEmpty
      Some(
        ConcreteAccessInstance(
          nodeId = canonicalNodeId(entry.nodeKind, entry.nodeName, entry.nodeId),
          nodeKind = entry.nodeKind,
          nodeName = entry.nodeName,
          args = args,
          argsExp = argsExp,
          permission = entry.evaluatedBodyPermission.orElse(entry.evaluatedPermission),
          permissionIsWildcard = wildcard,
          permissionSymbolicTerm = if (wildcard) symbolicTerm else None,
          origin = "source",
          evaluationKind = entry.evaluationKind,
          permissionEvidenceRole = PermissionEvidenceRole.SourceHeap,
          wildcardEligible = wildcard,
        )
      )
    }
  }

  private[tryfold] def targetEntryToInstance(
                                              entry: TryFoldTargetPermissionExtractor.TargetPermissionEntry,
                                              permissionEvidenceRole: String,
                                              allowSymbolicWildcard: Boolean,
                                            ): Option[ConcreteAccessInstance] = {
    if (!isSupportedNodeKind(entry.nodeKind)) {
      None
    } else {
      val symbolicTerm = entry.permissionTerm.filter(_.nonEmpty)
      val wildcard = allowSymbolicWildcard &&
        entry.evaluatedPermission.isEmpty &&
        isSymbolicOrConditional(entry.evaluationKind) &&
        symbolicTerm.nonEmpty
      Some(
        ConcreteAccessInstance(
          nodeId = canonicalNodeId(entry.nodeKind, entry.nodeName, entry.nodeId),
          nodeKind = entry.nodeKind,
          nodeName = entry.nodeName,
          args = entry.arguments,
          argsExp = entry.argumentsExp,
          permission = entry.evaluatedPermission,
          permissionIsWildcard = wildcard,
          permissionSymbolicTerm = if (wildcard) symbolicTerm else None,
          origin = "target",
          evaluationKind = entry.evaluationKind,
          permissionEvidenceRole = permissionEvidenceRole,
          wildcardEligible = wildcard,
        )
      )
    }
  }

  private def enumerateTargetBindingContextsForPath(
                                                     path: TryFoldPathExplorer.Path,
                                                     endpoints: TryFoldFailureContextExtractor.FailureEndpoints,
                                                   ): Vector[TargetBindingContext] = {
    val allDeduplicated = deduplicateTargetEntries(endpoints.targetPermissions)
    val relevantNodeIds = pathRelevantNodeIds(path)
    val primaryBindings = allDeduplicated.filter(entry =>
      canonicalNodeId(entry.nodeKind, entry.nodeName, entry.nodeId) == path.target.id
    )
    val supportBindings = allDeduplicated.filter { entry =>
      val nodeId = canonicalNodeId(entry.nodeKind, entry.nodeName, entry.nodeId)
      nodeId != path.target.id && relevantNodeIds.contains(nodeId)
    }

    if (primaryBindings.nonEmpty) {
      primaryBindings.map(primary => TargetBindingContext(primary = Some(primary), support = supportBindings))
    } else {
      Vector(TargetBindingContext(primary = None, support = supportBindings))
    }
  }

  private def pathRelevantNodeIds(path: TryFoldPathExplorer.Path): Set[String] = {
    val ids = mutable.LinkedHashSet.empty[String]
    ids += path.source.id
    ids += path.target.id
    path.steps.foreach { step =>
      ids += step.edge.from.id
      ids += step.edge.to.id
    }
    ids.toSet
  }

  private[tryfold] def deduplicateTargetEntries(
                                        entries: Vector[TryFoldTargetPermissionExtractor.TargetPermissionEntry]
                                      ): Vector[TryFoldTargetPermissionExtractor.TargetPermissionEntry] =
    entries
      .groupBy(entry => s"${entry.nodeId}|${entry.arguments.mkString(",")}|${entry.permissionTerm.getOrElse("")}|${entry.extractionSource}")
      .values
      .map(_.head)
      .toVector
      .sortBy(entry => entry.index)

  private def propagateAlongPath(
                                  path: TryFoldPathExplorer.Path,
                                  seeded: Map[String, Vector[ConcreteAccessInstance]],
                                ): Map[String, Vector[ConcreteAccessInstance]] = {
    val state = mutable.LinkedHashMap.empty[String, mutable.LinkedHashMap[String, ConcreteAccessInstance]]

    def add(instance: ConcreteAccessInstance): Boolean = {
      val byKey = state.getOrElseUpdate(instance.nodeId, mutable.LinkedHashMap.empty[String, ConcreteAccessInstance])
      val key = instanceKey(instance)
      if (byKey.contains(key)) {
        false
      } else {
        byKey.put(key, instance)
        true
      }
    }

    seeded.valuesIterator.flatten.foreach(add)

    val edges = path.steps.map(_.edge).distinct
    val maxRounds = math.max(1, path.steps.size * 2 + 2)
    var round = 0
    var changed = true

    while (round < maxRounds && changed) {
      changed = false
      edges.foreach { edge =>
        val fromInstances = state.getOrElse(edge.from.id, mutable.LinkedHashMap.empty).values.toVector
        if (fromInstances.nonEmpty) {
          edge.templates.foreach { template =>
            fromInstances.foreach { fromInstance =>
              deriveArguments(template, fromInstance.args).foreach { derivedArgs =>
                val derivedArgsExp = deriveArgumentsExp(template, fromInstance.argsExp)
                val derived = ConcreteAccessInstance(
                  nodeId = edge.to.id,
                  nodeKind = nodeKind(edge.to),
                  nodeName = nodeName(edge.to),
                  args = derivedArgs,
                  argsExp = derivedArgsExp,
                  permission = fromInstance.permission,
                  permissionIsWildcard = fromInstance.permissionIsWildcard,
                  permissionSymbolicTerm = fromInstance.permissionSymbolicTerm,
                  origin = "derived",
                  evaluationKind = fromInstance.evaluationKind,
                  permissionEvidenceRole = fromInstance.permissionEvidenceRole,
                  wildcardEligible = fromInstance.wildcardEligible,
                )
                if (add(derived)) {
                  changed = true
                }
              }
            }
          }
        }

        val toInstances = state.getOrElse(edge.to.id, mutable.LinkedHashMap.empty).values.toVector
        if (toInstances.nonEmpty) {
          edge.templates.foreach { template =>
            toInstances.foreach { toInstance =>
              deriveOwnerArgumentsReverse(template, toInstance).foreach { case (ownerArgs, ownerArgsExp) =>
                val derived = ConcreteAccessInstance(
                  nodeId = edge.from.id,
                  nodeKind = nodeKind(edge.from),
                  nodeName = nodeName(edge.from),
                  args = ownerArgs,
                  argsExp = ownerArgsExp,
                  permission = toInstance.permission,
                  permissionIsWildcard = toInstance.permissionIsWildcard,
                  permissionSymbolicTerm = toInstance.permissionSymbolicTerm,
                  origin = "derived_reverse",
                  evaluationKind = toInstance.evaluationKind,
                  permissionEvidenceRole = toInstance.permissionEvidenceRole,
                  wildcardEligible = toInstance.wildcardEligible,
                )
                if (add(derived)) {
                  changed = true
                }
              }
            }
          }
        }
      }
      round += 1
    }

    pruneEmptyArgumentInstancesPerNode(state.toVector.map { case (nodeId, byKey) =>
      nodeId -> byKey.values.toVector.sortBy(instanceSortKey)
    }.toMap)
  }

  private def deriveArguments(template: EdgeCallsiteTemplate, fromArgs: Vector[String]): Option[Vector[String]] = {
    val ownerFormals = template.ownerFormalParams
    if (ownerFormals.nonEmpty && ownerFormals.size != fromArgs.size) {
      None
    } else {
      val mapping = ownerFormals.zip(fromArgs).toMap
      val substituted = template.calleeArgTemplates.map(argTemplate => substituteFormals(argTemplate, mapping))
      Some(substituted)
    }
  }

  private def deriveOwnerArgumentsReverse(
                                           template: EdgeCallsiteTemplate,
                                           toInstance: ConcreteAccessInstance,
                                         ): Option[(Vector[String], Option[Vector[vpr.Exp]])] = {
    val toArgsExp = toInstance.argsExp.getOrElse(Vector.empty)
    val calleeArgTemplatesExp = template.calleeArgTemplatesExp
    if (toArgsExp.isEmpty || calleeArgTemplatesExp.isEmpty || toArgsExp.size != calleeArgTemplatesExp.size) {
      None
    } else {
      val ownerFormalOrder =
        if (template.ownerFormalParamsExp.nonEmpty) template.ownerFormalParamsExp.map(_.name)
        else template.ownerFormalParams

      if (ownerFormalOrder.isEmpty) {
        None
      } else {
        val placeholderNames = ownerFormalOrder.toSet
        val bindingsOpt = calleeArgTemplatesExp.zip(toArgsExp).foldLeft[Option[Map[String, vpr.Exp]]](Some(Map.empty)) {
          case (Some(env), (patternArg, actualArg)) =>
            unifyExpPattern(patternArg, actualArg, placeholderNames, env)
          case (None, _) =>
            None
        }

        bindingsOpt.flatMap { bindings =>
          val ownerArgsExpOpt = ownerFormalOrder.map(bindings.get)
          if (ownerArgsExpOpt.forall(_.isDefined)) {
            val ownerArgsExp = ownerArgsExpOpt.flatten.toVector
            Some(ownerArgsExp.map(safeRender) -> Some(ownerArgsExp))
          } else {
            None
          }
        }
      }
    }
  }

  private def deriveArgumentsExp(
                                  template: EdgeCallsiteTemplate,
                                  fromArgsExp: Option[Vector[vpr.Exp]],
                                ): Option[Vector[vpr.Exp]] = {
    val ownerFormalsExp = template.ownerFormalParamsExp
    val calleeArgsExp = template.calleeArgTemplatesExp
    fromArgsExp.flatMap { argsExp =>
      if (ownerFormalsExp.nonEmpty && ownerFormalsExp.size != argsExp.size) {
        None
      } else if (calleeArgsExp.isEmpty) {
        Some(Vector.empty)
      } else {
        val variables = ownerFormalsExp
        val values = argsExp
        val substituted = calleeArgsExp.map { argExp =>
          try {
            Expressions.instantiateVariables(argExp, variables, values, Set.empty)
          } catch {
            case _: Throwable =>
              argExp
          }
        }
        Some(substituted)
      }
    }
  }

  private def unifyExpPattern(
                               pattern: vpr.Exp,
                               actual: vpr.Exp,
                               placeholders: Set[String],
                               bindings: Map[String, vpr.Exp],
                             ): Option[Map[String, vpr.Exp]] = {
    pattern match {
      case local: vpr.AbstractLocalVar if placeholders.contains(local.name) =>
        bindings.get(local.name) match {
          case Some(bound) =>
            if (sameExp(bound, actual)) Some(bindings) else None
          case None =>
            Some(bindings + (local.name -> actual))
        }
      case _ =>
        if (pattern.getClass != actual.getClass) {
          None
        } else {
          val (patternChildren, patternOther) = Nodes.children(pattern)
          val (actualChildren, actualOther) = Nodes.children(actual)
          if (patternOther != actualOther || patternChildren.size != actualChildren.size) {
            None
          } else {
            patternChildren.zip(actualChildren).foldLeft[Option[Map[String, vpr.Exp]]](Some(bindings)) {
              case (Some(env), (pExp: vpr.Exp, aExp: vpr.Exp)) =>
                unifyExpPattern(pExp, aExp, placeholders, env)
              case (Some(env), (pOtherNode, aOtherNode)) =>
                if (pOtherNode == aOtherNode) Some(env) else None
              case (None, _) =>
                None
            }
          }
        }
    }
  }

  private def sameExp(left: vpr.Exp, right: vpr.Exp): Boolean =
    left == right || safeRender(left) == safeRender(right)

  private def substituteFormals(template: String, mapping: Map[String, String]): String = {
    mapping.toVector.sortBy { case (formal, _) => -formal.length }.foldLeft(template) { case (acc, (formal, actual)) =>
      val pattern = "(?<![A-Za-z0-9_@$])" + Pattern.quote(formal) + "(?:@\\d+)*(?![A-Za-z0-9_@$])"
      acc.replaceAll(pattern, Matcher.quoteReplacement(actual))
    }
  }

  private def pruneEmptyArgumentInstancesPerNode(
                                                instancesByNode: Map[String, Vector[ConcreteAccessInstance]]
                                              ): Map[String, Vector[ConcreteAccessInstance]] =
    instancesByNode.view.mapValues { instances =>
      val hasNonEmptyArgs = instances.exists(_.args.nonEmpty)
      val filtered =
        if (hasNonEmptyArgs) instances.filter(_.args.nonEmpty)
        else instances
      filtered.distinct.sortBy(instanceSortKey)
    }.toMap

  private def buildConcreteSequences(
                                     path: TryFoldPathExplorer.Path,
                                     pathIndex: Int,
                                     instancesByNode: Map[String, Vector[ConcreteAccessInstance]],
                                     endpoints: TryFoldFailureContextExtractor.FailureEndpoints,
                                     maxConcreteCandidatesPerPath: Int,
                                     activeTargetBinding: Option[TryFoldTargetPermissionExtractor.TargetPermissionEntry],
                                   ): MaterializationOutcome = {
    val stepDirectives = path.steps.map { step =>
      instancesByNode.getOrElse(step.edge.from.id, Vector.empty)
        .map { ownerInstance =>
          val inferred = inferPermissionForStep(
            step = step,
            ownerInstance = ownerInstance,
            endpoints = endpoints,
            instancesByNode = instancesByNode,
            activeTargetBinding = activeTargetBinding,
          )
          TryFoldWorklistEngine.AnnotationDirective(
            action = step.directive.action,
            predicateName = step.directive.predicateName,
            args = ownerInstance.args,
            argsExp = ownerInstance.argsExp,
            permission = inferred.permission,
            permissionIsWildcard = inferred.permissionIsWildcard,
            permissionSymbolicTerm = inferred.permissionSymbolicTerm,
            permissionOrigin = inferred.permissionOrigin,
          )
        }
        .distinct
        .sortBy(directiveSortKey)
    }

    val missingStepDrops = path.steps
      .zip(stepDirectives)
      .zipWithIndex
      .collect {
        case ((step, directives), stepIndex) if directives.isEmpty =>
          MaterializationDrop(
            pathIndex = pathIndex,
            reason = "no_instances_for_from_node",
            stepIndex = Some(stepIndex),
            fromNodeId = Some(step.edge.from.id),
            fromNodeName = Some(step.edge.from.name),
            details = Some("Concretization failed: no propagated concrete instances for edge source node."),
          )
      }

    if (missingStepDrops.nonEmpty) {
      MaterializationOutcome(sequences = Vector.empty, drops = missingStepDrops)
    } else {
      val capped = stepDirectives.foldLeft(Vector(Vector.empty[TryFoldWorklistEngine.AnnotationDirective])) { (partial, currentStepDirectives) =>
        val expanded = partial.flatMap(prefix => currentStepDirectives.map(directive => prefix :+ directive))
        deduplicateSequences(expanded)
          .sortBy(directiveSeqSortKey)
          .take(maxConcreteCandidatesPerPath)
      }
      MaterializationOutcome(
        sequences = capped
          .map(steps => TryFoldWorklistEngine.AnnotationSequence(steps))
          .filter(_.steps.size == path.steps.size),
        drops = Vector.empty,
      )
    }
  }

  private def inferPermissionForStep(
                                      step: TryFoldPathExplorer.PathStep,
                                      ownerInstance: ConcreteAccessInstance,
                                      endpoints: TryFoldFailureContextExtractor.FailureEndpoints,
                                      instancesByNode: Map[String, Vector[ConcreteAccessInstance]],
                                      activeTargetBinding: Option[TryFoldTargetPermissionExtractor.TargetPermissionEntry],
                                    ): InferredPermission = {
    val ownerNodeId = step.edge.from.id
    val ownerArgs = ownerInstance.args
    val base = inferMissingPermission(
      nodeId = ownerNodeId,
      args = ownerArgs,
      currentPermission = ownerInstance.permission,
      endpoints = endpoints,
      instancesByNode = instancesByNode,
      activeTargetBinding = activeTargetBinding,
    )
    if (base.permission.isDefined || base.permissionIsWildcard) {
      base
    } else if (step.directive.action == TryFoldWorklistEngine.FoldAnnotation) {
      uniqueExactPositivePermission(step.from.id, instancesByNode) match {
        case Some(perm) =>
          InferredPermission(
            permission = Some(perm),
            permissionIsWildcard = false,
            permissionSymbolicTerm = None,
            permissionOrigin = Some("fold_from_step_unique"),
          )
        case None =>
          uniqueExactPositivePermissionFromSource(step.from.id, endpoints.sourcePermissions) match {
            case Some(perm) =>
              InferredPermission(
                permission = Some(perm),
                permissionIsWildcard = false,
                permissionSymbolicTerm = None,
                permissionOrigin = Some("fold_from_step_source_unique"),
              )
            case None => base
          }
      }
    } else {
      base
    }
  }

  private def deduplicateSequences(
                                    sequences: Vector[Vector[TryFoldWorklistEngine.AnnotationDirective]]
                                  ): Vector[Vector[TryFoldWorklistEngine.AnnotationDirective]] =
    sequences
      .groupBy(directiveSeqSignature)
      .values
      .map(_.head)
      .toVector

  private def deduplicateDrops(
                                drops: Vector[MaterializationDrop]
                              ): Vector[MaterializationDrop] =
    drops
      .groupBy(drop => s"${drop.pathIndex}|${drop.reason}|${drop.stepIndex.getOrElse(-1)}|${drop.fromNodeId.getOrElse("")}|${drop.fromNodeName.getOrElse("")}|${drop.details.getOrElse("")}")
      .values
      .map(_.head)
      .toVector
      .sortBy(drop => (drop.pathIndex, drop.stepIndex.getOrElse(-1), drop.reason, drop.fromNodeId.getOrElse(""), drop.fromNodeName.getOrElse("")))

  private def directiveSeqSignature(sequence: Vector[TryFoldWorklistEngine.AnnotationDirective]): String =
    sequence.map(directiveSignature).mkString("|")

  private def directiveSeqSortKey(sequence: Vector[TryFoldWorklistEngine.AnnotationDirective]): (Int, String) =
    (sequence.size, directiveSeqSignature(sequence))

  private[tryfold] def directiveSignature(directive: TryFoldWorklistEngine.AnnotationDirective): String = {
    val args = directive.args.mkString(",")
    val perm =
      if (directive.permissionIsWildcard) "_"
      else directive.permission.map(_.rational).getOrElse("?")
    val origin = directive.permissionOrigin.getOrElse("?")
    s"${directive.action.priority}:${directive.predicateName}($args)@$perm@$origin"
  }

  private[tryfold] def directiveSortKey(directive: TryFoldWorklistEngine.AnnotationDirective): (String, Int) =
    (directiveSignature(directive), directive.args.size)

  private def inferMissingPermission(
                                      nodeId: String,
                                      args: Vector[String],
                                      currentPermission: Option[PermissionAmount],
                                      endpoints: TryFoldFailureContextExtractor.FailureEndpoints,
                                      instancesByNode: Map[String, Vector[ConcreteAccessInstance]],
                                      activeTargetBinding: Option[TryFoldTargetPermissionExtractor.TargetPermissionEntry],
                                    ): InferredPermission = {
    currentPermission match {
      case Some(perm) =>
        InferredPermission(
          permission = Some(perm),
          permissionIsWildcard = false,
          permissionSymbolicTerm = None,
          permissionOrigin = Some("instance"),
        )
      case None =>
        val targetBindingExact = activeTargetBinding
          .filter(entry => canonicalNodeId(entry.nodeKind, entry.nodeName, entry.nodeId) == nodeId)
          .filter(entry => argsCompatible(args, entry.arguments))
          .flatMap(_.evaluatedPermission)
          .map { perm =>
            InferredPermission(
              permission = Some(perm),
              permissionIsWildcard = false,
              permissionSymbolicTerm = None,
              permissionOrigin = Some("target_binding"),
            )
          }

        val sourceExact = uniquePermission(
          endpoints.sourcePermissions
            .filter(entry => canonicalNodeId(entry.nodeKind, entry.nodeName, entry.nodeId) == nodeId)
            .flatMap { entry =>
              val entryArgs = if (entry.singletonArguments.nonEmpty) entry.singletonArguments else entry.arguments
              if (argsCompatible(args, entryArgs)) entry.evaluatedBodyPermission.orElse(entry.evaluatedPermission).toVector
              else Vector.empty
            }
        ).map { perm =>
          InferredPermission(
            permission = Some(perm),
            permissionIsWildcard = false,
            permissionSymbolicTerm = None,
            permissionOrigin = Some("source_exact_unique"),
          )
        }

        val nodeUnique = uniquePermission(
          instancesByNode.getOrElse(nodeId, Vector.empty).flatMap(_.permission)
        ).map { perm =>
          InferredPermission(
            permission = Some(perm),
            permissionIsWildcard = false,
            permissionSymbolicTerm = None,
            permissionOrigin = Some("node_unique"),
          )
        }

        val targetBindingWildcard = activeTargetBinding
          .filter(entry => canonicalNodeId(entry.nodeKind, entry.nodeName, entry.nodeId) == nodeId)
          .filter(entry => argsCompatible(args, entry.arguments))
          .filter(entry => isSymbolicOrConditional(entry.evaluationKind))
          .flatMap(_.permissionTerm.filter(_.nonEmpty))
          .headOption
          .map { term =>
            InferredPermission(
              permission = None,
              permissionIsWildcard = true,
              permissionSymbolicTerm = Some(term),
              permissionOrigin = Some("target_binding_wildcard"),
            )
          }

        val sourceWildcard = endpoints.sourcePermissions
          .filter(entry => canonicalNodeId(entry.nodeKind, entry.nodeName, entry.nodeId) == nodeId)
          .filter { entry =>
            val entryArgs = if (entry.singletonArguments.nonEmpty) entry.singletonArguments else entry.arguments
            argsCompatible(args, entryArgs)
          }
          .filter(entry => isSymbolicOrConditional(entry.evaluationKind))
          .flatMap(entry => entry.bodyPermissionTerm.orElse(Option(entry.permissionTerm).filter(_.nonEmpty)))
          .headOption
          .map { term =>
            InferredPermission(
              permission = None,
              permissionIsWildcard = true,
              permissionSymbolicTerm = Some(term),
              permissionOrigin = Some("source_symbolic_wildcard"),
            )
          }

        val nodeWildcard = instancesByNode
          .getOrElse(nodeId, Vector.empty)
          .find(instance => instance.permissionIsWildcard && instance.wildcardEligible)
          .flatMap(_.permissionSymbolicTerm)
          .map { term =>
            InferredPermission(
              permission = None,
              permissionIsWildcard = true,
              permissionSymbolicTerm = Some(term),
              permissionOrigin = Some("node_symbolic_wildcard"),
            )
          }

        targetBindingExact
          .orElse(sourceExact)
          .orElse(nodeUnique)
          .orElse(ownerWildcardCandidate(currentPermission, instancesByNode, nodeId, args))
          .orElse(targetBindingWildcard)
          .orElse(sourceWildcard)
          .orElse(nodeWildcard)
          .getOrElse(
            InferredPermission(
              permission = None,
              permissionIsWildcard = false,
              permissionSymbolicTerm = None,
              permissionOrigin = None,
            )
          )
    }
  }

  private def ownerWildcardCandidate(
                                      currentPermission: Option[PermissionAmount],
                                      instancesByNode: Map[String, Vector[ConcreteAccessInstance]],
                                      nodeId: String,
                                      args: Vector[String],
                                    ): Option[InferredPermission] = {
    if (currentPermission.isDefined) None
    else {
      instancesByNode
        .getOrElse(nodeId, Vector.empty)
        .find(instance =>
          instance.permission.isEmpty &&
            instance.permissionIsWildcard &&
            instance.wildcardEligible &&
            argsCompatible(args, instance.args)
        )
        .flatMap(_.permissionSymbolicTerm)
        .map { term =>
          InferredPermission(
            permission = None,
            permissionIsWildcard = true,
            permissionSymbolicTerm = Some(term),
            permissionOrigin = Some("instance_wildcard"),
          )
        }
    }
  }

  private def uniquePermission(values: Vector[PermissionAmount]): Option[PermissionAmount] = {
    val distinct = values.groupBy(_.rational).values.map(_.head).toVector
    if (distinct.size == 1) distinct.headOption else None
  }

  private def uniqueExactPositivePermission(
                                             nodeId: String,
                                             instancesByNode: Map[String, Vector[ConcreteAccessInstance]],
                                           ): Option[PermissionAmount] = {
    val candidates = instancesByNode
      .getOrElse(nodeId, Vector.empty)
      .filter(_.evaluationKind == "exact")
      .flatMap(_.permission)
      .filter(isPositivePermission)
    uniquePermission(candidates)
  }

  private def uniqueExactPositivePermissionFromSource(
                                                       nodeId: String,
                                                       sourcePermissions: Vector[SourcePermissionEntry],
                                                     ): Option[PermissionAmount] = {
    val candidates = sourcePermissions
      .filter(entry => canonicalNodeId(entry.nodeKind, entry.nodeName, entry.nodeId) == nodeId)
      .flatMap(entry => entry.evaluatedBodyPermission.orElse(entry.evaluatedPermission))
      .filter(isPositivePermission)
    uniquePermission(candidates)
  }

  private def isPositivePermission(perm: PermissionAmount): Boolean =
    parseRationalNumeratorDenominator(perm.rational).exists { case (n, d) =>
      d > 0 && n > 0
    }

  private def parseRationalNumeratorDenominator(text: String): Option[(BigInt, BigInt)] = {
    val trimmed = Option(text).getOrElse("").trim
    if (trimmed.isEmpty) {
      None
    } else {
      val parts = trimmed.split("/", 2).map(_.trim)
      if (parts.length == 1) {
        scala.util.Try(BigInt(parts(0))).toOption.map(n => (n, BigInt(1)))
      } else {
        for {
          n <- scala.util.Try(BigInt(parts(0))).toOption
          d <- scala.util.Try(BigInt(parts(1))).toOption
          if d != 0
        } yield (n, d)
      }
    }
  }

  private def argsCompatible(lhs: Vector[String], rhs: Vector[String]): Boolean =
    lhs == rhs || lhs.isEmpty || rhs.isEmpty

  private[tryfold] def instanceKey(instance: ConcreteAccessInstance): String = {
    val perm =
      if (instance.permissionIsWildcard) "_"
      else instance.permission.map(_.rational).getOrElse("?")
    s"${instance.nodeId}|${instance.args.mkString(",")}|$perm"
  }

  private[tryfold] def instanceSortKey(instance: ConcreteAccessInstance): String = {
    val perm =
      if (instance.permissionIsWildcard) "_"
      else instance.permission.map(_.rational).getOrElse("?")
    s"${instance.nodeId}|${instance.args.mkString(",")}|$perm|${instance.origin}|${instance.evaluationKind}|${instance.permissionEvidenceRole}|${instance.wildcardEligible}"
  }

  private def isSymbolicOrConditional(evaluationKind: String): Boolean =
    evaluationKind == "symbolic" || evaluationKind == "conditional"

  private def isSupportedNodeKind(nodeKind: String): Boolean =
    nodeKind == "predicate" || nodeKind == "field"

  private[tryfold] def canonicalNodeId(nodeKind: String, nodeName: String, fallback: String): String =
    nodeKind match {
      case "predicate" => s"pred:$nodeName"
      case "field" => s"field:$nodeName"
      case _ => fallback
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

  private def safeRender(value: Any): String =
    try {
      String.valueOf(value)
    } catch {
      case throwable: Throwable => s"<rendering failed: ${throwable.getClass.getSimpleName}>"
    }
}
