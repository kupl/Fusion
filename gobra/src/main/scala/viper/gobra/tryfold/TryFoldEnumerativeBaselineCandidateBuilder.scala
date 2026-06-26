package viper.gobra.tryfold

import scala.collection.mutable

object TryFoldEnumerativeBaselineCandidateBuilder {

  def enumerate(
                 endpoints: TryFoldFailureContextExtractor.FailureEndpoints,
               ): Vector[TryFoldWorklistEngine.AnnotationSequence] = {
    val unfoldCandidates = endpoints.sourcePermissions
      .flatMap(TryFoldAnnotationCandidateBuilder.sourceEntryToInstance)
      .filter(_.nodeKind == "predicate")
      .groupBy(instance => TryFoldAnnotationCandidateBuilder.instanceKey(instance))
      .values
      .map(_.head)
      .toVector
      .sortBy(instance => TryFoldAnnotationCandidateBuilder.instanceSortKey(instance))
      .map { instance =>
        TryFoldWorklistEngine.AnnotationSequence(
          Vector(
            TryFoldWorklistEngine.AnnotationDirective(
              action = TryFoldWorklistEngine.UnfoldAnnotation,
              predicateName = instance.nodeName,
              args = instance.args,
              argsExp = instance.argsExp,
              permission = instance.permission,
              permissionIsWildcard = instance.permissionIsWildcard,
              permissionSymbolicTerm = instance.permissionSymbolicTerm,
              permissionOrigin = Some(instance.origin),
            )
          )
        )
      }

    val foldCandidates = endpoints.target match {
      case _: PredicateNode =>
        val targetId = endpoints.target.id
        TryFoldAnnotationCandidateBuilder
          .deduplicateTargetEntries(endpoints.targetPermissions)
          .filter(entry =>
            TryFoldAnnotationCandidateBuilder.canonicalNodeId(entry.nodeKind, entry.nodeName, entry.nodeId) == targetId
          )
          .flatMap(entry =>
            TryFoldAnnotationCandidateBuilder.targetEntryToInstance(
              entry,
              TryFoldAnnotationCandidateBuilder.PermissionEvidenceRole.TargetPrimary,
              allowSymbolicWildcard = true,
            )
          )
          .filter(_.nodeKind == "predicate")
          .groupBy(instance => TryFoldAnnotationCandidateBuilder.instanceKey(instance))
          .values
          .map(_.head)
          .toVector
          .sortBy(instance => TryFoldAnnotationCandidateBuilder.instanceSortKey(instance))
          .map { instance =>
            TryFoldWorklistEngine.AnnotationSequence(
              Vector(
                TryFoldWorklistEngine.AnnotationDirective(
                  action = TryFoldWorklistEngine.FoldAnnotation,
                  predicateName = instance.nodeName,
                  args = instance.args,
                  argsExp = instance.argsExp,
                  permission = instance.permission,
                  permissionIsWildcard = instance.permissionIsWildcard,
                  permissionSymbolicTerm = instance.permissionSymbolicTerm,
                  permissionOrigin = Some(instance.origin),
                )
              )
            )
          }
      case _ =>
        Vector.empty
    }

    val deduplicated = mutable.LinkedHashMap.empty[String, TryFoldWorklistEngine.AnnotationSequence]
    (unfoldCandidates ++ foldCandidates)
      .sortBy(sequenceSortKey)
      .foreach { sequence =>
        val signature = sequence.steps.map(TryFoldAnnotationCandidateBuilder.directiveSignature).mkString("|")
        deduplicated.getOrElseUpdate(signature, sequence)
      }
    deduplicated.values.toVector.sortBy(sequenceSortKey)
  }

  private def sequenceSortKey(
                               sequence: TryFoldWorklistEngine.AnnotationSequence
                             ): (Int, String, String, String, String) = {
    val step = sequence.steps.head
    val permissionKey =
      if (step.permissionIsWildcard) "_"
      else step.permission.map(_.rational).getOrElse("?")
    (
      step.action.priority,
      step.predicateName,
      step.args.mkString(","),
      permissionKey,
      step.permissionOrigin.getOrElse("?"),
    )
  }
}
