package viper.gobra.tryfold

import viper.gobra.backend.BackendVerifier
import viper.gobra.backend.TryFoldSourcePermissionExtractor.SourcePermissionEntry
import viper.gobra.reporting.Source
import viper.silver.ast.pretty.FastPrettyPrinter
import viper.silver.{ast => vpr}

import scala.collection.mutable
import scala.util.matching.Regex

object TryFoldDynamicAlternativeFilter {

  final case class RequiredAlternative(
                                        stepIndex: Int,
                                        nodeId: String,
                                        nodeName: String,
                                        typeKey: String,
                                      )

  final case class ResolvedTypeFact(
                                     nodeId: String,
                                     nodeName: String,
                                     typeKeys: Vector[String],
                                     evidenceSources: Vector[String],
                                   )

  final case class PathMismatch(
                                 stepIndex: Int,
                                 nodeId: String,
                                 nodeName: String,
                                 requiredTypeKeys: Vector[String],
                                 resolvedTypeKeys: Vector[String],
                               )

  final case class PathDecision(
                                 pathIndex: Int,
                                 path: TryFoldPathExplorer.Path,
                                 requiredAlternatives: Vector[RequiredAlternative],
                                 resolvedTypeFacts: Vector[ResolvedTypeFact],
                                 mismatch: Option[PathMismatch],
                               ) {
    def keep: Boolean = mismatch.isEmpty
  }

  private final case class AssignmentRecord(
                                             lhsName: String,
                                             rhs: vpr.Exp,
                                             line: Option[Int],
                                             column: Option[Int],
                                             order: Int,
                                           )

  private final case class MarkerContext(
                                          method: vpr.Method,
                                          container: vpr.Seqn,
                                          labelIndex: Int,
                                          pathPrefix: Vector[vpr.Stmt],
                                        )

  private final case class BranchLocalResolutionContext(
                                                         markerLabel: String,
                                                         returnLine: Int,
                                                         returnColumn: Int,
                                                         assignments: Vector[AssignmentRecord],
                                                       )

  private val VarVersionSuffixPattern: Regex = "^([A-Za-z_][A-Za-z0-9_]*)_V\\d+(?:_CN\\d+)?$".r

  def analyzePath(
                   pathIndex: Int,
                   path: TryFoldPathExplorer.Path,
                   endpoints: TryFoldFailureContextExtractor.FailureEndpoints,
                   translationMetadata: TryFoldTranslationMetadata,
                   storeBindings: Map[String, vpr.Exp],
                   translatedProgram: Option[vpr.Program] = None,
                   failure: Option[BackendVerifier.Failure] = None,
                 ): PathDecision = {
    val requiredAlternatives = collectRequiredAlternatives(path)
    val branchLocalContext = for {
      program <- translatedProgram
      failed <- failure
      context <- buildBranchLocalResolutionContext(program, failed)
    } yield context

    val resolvedFacts = collectResolvedTypeFacts(
      requiredAlternatives = requiredAlternatives,
      endpoints = endpoints,
      translationMetadata = translationMetadata,
      storeBindings = storeBindings,
      branchLocalContext = branchLocalContext,
    )
    val factsByNode = resolvedFacts.map(fact => fact.nodeId -> fact).toMap
    val mismatch = requiredAlternatives
      .groupBy(required => (required.stepIndex, required.nodeId, required.nodeName))
      .toVector
      .sortBy { case ((stepIndex, nodeId, _), _) => (stepIndex, nodeId) }
      .collectFirst {
      case ((stepIndex, nodeId, nodeName), requireds)
          if factsByNode.get(nodeId).exists(fact =>
            fact.typeKeys.nonEmpty && requireds.forall(required => !fact.typeKeys.contains(required.typeKey))
          ) =>
        val fact = factsByNode(nodeId)
        PathMismatch(
          stepIndex = stepIndex,
          nodeId = nodeId,
          nodeName = nodeName,
          requiredTypeKeys = requireds.map(_.typeKey).distinct.sorted,
          resolvedTypeKeys = fact.typeKeys,
        )
    }

    PathDecision(
      pathIndex = pathIndex,
      path = path,
      requiredAlternatives = requiredAlternatives,
      resolvedTypeFacts = resolvedFacts,
      mismatch = mismatch,
    )
  }

  private def collectRequiredAlternatives(
                                           path: TryFoldPathExplorer.Path
                                         ): Vector[RequiredAlternative] =
    path.steps.zipWithIndex.flatMap { case (step, stepIndex) =>
      step.edge.labels.toVector.collect {
        case DynamicAlternativeLabel(typeKey) =>
          RequiredAlternative(
            stepIndex = stepIndex,
            nodeId = step.edge.from.id,
            nodeName = step.edge.from.name,
            typeKey = typeKey,
          )
      }
    }

  private def collectResolvedTypeFacts(
                                         requiredAlternatives: Vector[RequiredAlternative],
                                         endpoints: TryFoldFailureContextExtractor.FailureEndpoints,
                                         translationMetadata: TryFoldTranslationMetadata,
                                         storeBindings: Map[String, vpr.Exp],
                                         branchLocalContext: Option[BranchLocalResolutionContext],
                                       ): Vector[ResolvedTypeFact] = {
    val relevantNodeIds = requiredAlternatives.map(_.nodeId).toSet
    if (relevantNodeIds.isEmpty) {
      Vector.empty
    } else {
      val collected = mutable.LinkedHashMap.empty[String, mutable.LinkedHashMap[String, mutable.LinkedHashSet[String]]]

      def add(nodeId: String, typeKey: String, evidenceSource: String): Unit = {
        val nodeMap = collected.getOrElseUpdate(nodeId, mutable.LinkedHashMap.empty[String, mutable.LinkedHashSet[String]])
        val evidence = nodeMap.getOrElseUpdate(typeKey, mutable.LinkedHashSet.empty[String])
        evidence += evidenceSource
      }

      endpoints.targetPermissions.foreach { entry =>
        val nodeId = TryFoldAnnotationCandidateBuilder.canonicalNodeId(entry.nodeKind, entry.nodeName, entry.nodeId)
        if (relevantNodeIds.contains(nodeId)) {
          extractTypeKeysFromTargetEntry(entry, translationMetadata, storeBindings, branchLocalContext).foreach {
            case (typeKey, evidence) => add(nodeId, typeKey, evidence)
          }
        }
      }

      endpoints.sourcePermissions.foreach { entry =>
        val nodeId = TryFoldAnnotationCandidateBuilder.canonicalNodeId(entry.nodeKind, entry.nodeName, entry.nodeId)
        if (relevantNodeIds.contains(nodeId)) {
          extractTypeKeysFromSourceEntry(entry, translationMetadata, storeBindings, branchLocalContext).foreach {
            case (typeKey, evidence) => add(nodeId, typeKey, evidence)
          }
        }
      }

      relevantNodeIds.toVector.sorted.flatMap { nodeId =>
        val nodeName = requiredAlternatives.find(_.nodeId == nodeId).map(_.nodeName).getOrElse(nodeId)
        collected.get(nodeId).map { byType =>
          val orderedTypes = byType.keys.toVector.sorted
          val evidenceSources = orderedTypes.flatMap(typeKey => byType.getOrElse(typeKey, mutable.LinkedHashSet.empty).toVector.sorted)
          ResolvedTypeFact(
            nodeId = nodeId,
            nodeName = nodeName,
            typeKeys = orderedTypes,
            evidenceSources = evidenceSources,
          )
        }
      }
    }
  }

  private def extractTypeKeysFromTargetEntry(
                                              entry: TryFoldTargetPermissionExtractor.TargetPermissionEntry,
                                              translationMetadata: TryFoldTranslationMetadata,
                                              storeBindings: Map[String, vpr.Exp],
                                              branchLocalContext: Option[BranchLocalResolutionContext],
                                            ): Vector[(String, String)] =
    translationMetadata.dynamicPredicateFamilies.get(entry.nodeName).toVector.flatMap { family =>
      entry.argumentsExp
        .flatMap(_.lift(family.receiverArgumentIndex))
        .toVector
        .flatMap { argExp =>
          resolveDynamicTypeKeysWithEvidence(
            interfaceExp = argExp,
            family = family,
            storeBindings = storeBindings,
            branchLocalContext = branchLocalContext,
            directEvidencePrefix = s"target:${entry.extractionSource}:${entry.index}",
          )
        }
    }

  private def extractTypeKeysFromSourceEntry(
                                              entry: SourcePermissionEntry,
                                              translationMetadata: TryFoldTranslationMetadata,
                                              storeBindings: Map[String, vpr.Exp],
                                              branchLocalContext: Option[BranchLocalResolutionContext],
                                            ): Vector[(String, String)] =
    translationMetadata.dynamicPredicateFamilies.get(entry.nodeName).toVector.flatMap { family =>
      val argsExp =
        if (entry.singletonArgumentsExp.exists(_.nonEmpty)) entry.singletonArgumentsExp
        else entry.argumentsExp
      argsExp
        .flatMap(_.lift(family.receiverArgumentIndex))
        .toVector
        .flatMap { argExp =>
          resolveDynamicTypeKeysWithEvidence(
            interfaceExp = argExp,
            family = family,
            storeBindings = storeBindings,
            branchLocalContext = branchLocalContext,
            directEvidencePrefix = s"source:${entry.index}",
          )
        }
    }

  private def resolveDynamicTypeKeysWithEvidence(
                                                  interfaceExp: vpr.Exp,
                                                  family: DynamicPredicateFamilyMetadata,
                                                  storeBindings: Map[String, vpr.Exp],
                                                  branchLocalContext: Option[BranchLocalResolutionContext],
                                                  directEvidencePrefix: String,
                                                ): Vector[(String, String)] = {
    val direct = resolveDynamicTypeKey(
      interfaceExp = interfaceExp,
      family = family,
      storeBindings = storeBindings,
    ).toVector.map(typeKey => typeKey -> s"$directEvidencePrefix:direct")

    val branchLocal = branchLocalContext.toVector.flatMap { ctx =>
      expandViaBranchLocalAssignments(interfaceExp, ctx).flatMap { expanded =>
        resolveDynamicTypeKey(
          interfaceExp = expanded,
          family = family,
          storeBindings = storeBindings,
        ).map(typeKey => typeKey -> s"$directEvidencePrefix:returnMarker:${ctx.markerLabel}").toVector
      }
    }

    deduplicateTypeEvidence(direct ++ branchLocal)
  }

  private def deduplicateTypeEvidence(entries: Vector[(String, String)]): Vector[(String, String)] = {
    val seen = mutable.LinkedHashSet.empty[(String, String)]
    entries.foldLeft(Vector.empty[(String, String)]) { (acc, entry) =>
      if (seen.contains(entry)) acc
      else {
        seen += entry
        acc :+ entry
      }
    }
  }

  private def resolveDynamicTypeKey(
                                     interfaceExp: vpr.Exp,
                                     family: DynamicPredicateFamilyMetadata,
                                     storeBindings: Map[String, vpr.Exp],
                                     visitedLocals: Set[String] = Set.empty,
                                     depth: Int = 0,
                                   ): Option[String] = {
    if (depth > 8) {
      None
    } else {
      directTypeKey(interfaceExp, family)
        .orElse(extractFromTupleCreate(interfaceExp, family))
        .orElse(resolveViaTupleGetter(interfaceExp, family, storeBindings, visitedLocals, depth))
        .orElse(resolveViaStoreBinding(interfaceExp, family, storeBindings, visitedLocals, depth))
    }
  }

  private def extractFromTupleCreate(
                                      interfaceExp: vpr.Exp,
                                      family: DynamicPredicateFamilyMetadata,
                                    ): Option[String] =
    interfaceExp match {
      case app: vpr.DomainFuncApp
          if app.funcname == tupleConstructorName(family.receiverTupleArity) &&
            app.args.size == family.receiverTupleArity =>
        app.args.lift(family.receiverTupleTypeSlot).flatMap(typeExp => directTypeKey(typeExp, family))
      case _ =>
        None
    }

  private def resolveViaTupleGetter(
                                      interfaceExp: vpr.Exp,
                                      family: DynamicPredicateFamilyMetadata,
                                      storeBindings: Map[String, vpr.Exp],
                                      visitedLocals: Set[String],
                                      depth: Int,
                                    ): Option[String] =
    interfaceExp match {
      case app: vpr.DomainFuncApp
          if app.funcname == tupleGetterName(family.receiverTupleTypeSlot, family.receiverTupleArity) &&
            app.args.size == 1 =>
        directTypeKey(interfaceExp, family)
          .orElse(resolveDynamicTypeKey(app.args.head, family, storeBindings, visitedLocals, depth + 1))
      case _ =>
        None
    }

  private def resolveViaStoreBinding(
                                       interfaceExp: vpr.Exp,
                                       family: DynamicPredicateFamilyMetadata,
                                       storeBindings: Map[String, vpr.Exp],
                                       visitedLocals: Set[String],
                                       depth: Int,
                                     ): Option[String] =
    interfaceExp match {
      case local: vpr.AbstractLocalVar if !visitedLocals.contains(local.name) =>
        lookupStoreBinding(local.name, storeBindings).flatMap(bound =>
          resolveDynamicTypeKey(bound, family, storeBindings, visitedLocals + local.name, depth + 1)
        )
      case _ =>
        None
    }

  private def lookupStoreBinding(name: String, storeBindings: Map[String, vpr.Exp]): Option[vpr.Exp] = {
    val noAt = name.replaceAll("@\\d+", "")
    val strippedNoAt = stripVarSuffix(noAt)
    val stripped = stripVarSuffix(name)
    val directKeys = Vector(name, noAt, strippedNoAt, stripped).filter(_.nonEmpty).distinct
    directKeys.iterator.flatMap(storeBindings.get).toVector.headOption.orElse {
      storeBindings.iterator.collectFirst {
        case (key, value)
          if stripVarSuffix(key.replaceAll("@\\d+", "")) == strippedNoAt =>
          value
      }
    }
  }

  private def directTypeKey(
                             exp: vpr.Exp,
                             family: DynamicPredicateFamilyMetadata,
                           ): Option[String] =
    family.typeExprToKey.get(render(exp))

  private def tupleConstructorName(arity: Int): String = s"tuple$arity"

  private def tupleGetterName(index: Int, arity: Int): String = s"get${index}of$arity"

  private def render(exp: vpr.Exp): String =
    FastPrettyPrinter.pretty(exp).trim

  private def stripVarSuffix(name: String): String =
    name.replaceAll("@\\d+", "") match {
      case VarVersionSuffixPattern(base) => base
      case other => other
    }

  private def buildBranchLocalResolutionContext(
                                                 translatedProgram: vpr.Program,
                                                 failure: BackendVerifier.Failure,
                                               ): Option[BranchLocalResolutionContext] = {
    for {
      firstError <- failure.errors.headOption
      if isPostconditionFailure(firstError)
      debuggingContext <- TryFoldFailureContextExtractor.extractFirstDebuggingContext(failure)
      marker <- TryFoldInsertionPlanner.pickLastReturnMarker(debuggingContext)
      markerContext <- findMarkerContext(translatedProgram, marker.labelName)
    } yield {
      val prefixAssignments = collectAssignmentsWithPos(markerContext.pathPrefix)
      val rootAssignments = collectRootLevelAssignmentRecords(markerContext.method)
      val bridgeAssignments = collectRootLevelFormalReturnAssignmentRecords(markerContext.method)
      BranchLocalResolutionContext(
        markerLabel = marker.labelName,
        returnLine = marker.line,
        returnColumn = marker.column,
        assignments = rootAssignments ++ prefixAssignments ++ bridgeAssignments,
      )
    }
  }

  private def isPostconditionFailure(error: viper.silver.verifier.VerificationError): Boolean =
    error match {
      case _: viper.silver.verifier.errors.PostconditionViolated => true
      case _ =>
        val id = Option(error.id).getOrElse("")
        id == "postcondition.violated"
    }

  private def expandViaBranchLocalAssignments(
                                               exp: vpr.Exp,
                                               branchLocalContext: BranchLocalResolutionContext,
                                             ): Vector[vpr.Exp] =
    exp match {
      case local: vpr.AbstractLocalVar =>
        val base = stripVarSuffix(local.name)
        val seedNames = (Vector(local.name, local.name.replaceAll("@\\d+", ""), base) ++
          branchLocalContext.assignments.map(_.lhsName).filter(lhs => stripVarSuffix(lhs) == base))
          .filter(_.nonEmpty)
          .distinct
        val cutoff = Some(branchLocalContext.returnLine -> Some(branchLocalContext.returnColumn))
        deduplicateExpByRender(seedNames.flatMap { seed =>
          resolveAssignmentChainAll(
            varName = seed,
            assignments = branchLocalContext.assignments,
            returnCutoff = cutoff,
            visited = Set.empty,
            depth = 0,
            maxDepth = 24,
          )
        })
      case _ =>
        Vector.empty
    }

  private def deduplicateExpByRender(exps: Seq[vpr.Exp]): Vector[vpr.Exp] = {
    val seen = mutable.LinkedHashSet.empty[String]
    val ordered = mutable.ArrayBuffer.empty[vpr.Exp]
    exps.foreach { exp =>
      val key = safeRender(exp)
      if (!seen.contains(key)) {
        seen += key
        ordered += exp
      }
    }
    ordered.toVector
  }

  private def resolveAssignmentChainAll(
                                         varName: String,
                                         assignments: Vector[AssignmentRecord],
                                         returnCutoff: Option[(Int, Option[Int])],
                                         visited: Set[String],
                                         depth: Int,
                                         maxDepth: Int,
                                       ): Vector[vpr.Exp] = {
    if (depth >= maxDepth || visited.contains(varName)) {
      Vector.empty
    } else {
      val currentAssignments = selectAssignmentsForVar(varName, assignments, returnCutoff)
      if (currentAssignments.isEmpty) {
        Vector.empty
      } else {
        val nextVisited = visited + varName
        deduplicateExpByRender(currentAssignments.flatMap { assignment =>
          assignment.rhs match {
            case rhsLocal: vpr.AbstractLocalVar =>
              val deeper = resolveAssignmentChainAll(
                varName = rhsLocal.name,
                assignments = assignments,
                returnCutoff = returnCutoff,
                visited = nextVisited,
                depth = depth + 1,
                maxDepth = maxDepth,
              )
              if (deeper.nonEmpty) deeper else Vector(rhsLocal: vpr.Exp)
            case other =>
              Vector(other)
          }
        })
      }
    }
  }

  private def selectAssignmentsForVar(
                                       varName: String,
                                       assignments: Vector[AssignmentRecord],
                                       returnCutoff: Option[(Int, Option[Int])],
                                     ): Vector[AssignmentRecord] = {
    val normalizedTarget = stripVarSuffix(varName)
    val assigns = assignments.filter(record => stripVarSuffix(record.lhsName) == normalizedTarget)
    if (assigns.isEmpty) {
      Vector.empty
    } else {
      returnCutoff match {
        case Some((retLine, retColOpt)) =>
          val cutoffCol = retColOpt.getOrElse(Int.MaxValue)
          val withPos = assigns.flatMap { a =>
            a.line.map(line => (a, (line, a.column.getOrElse(0))))
          }
          if (withPos.isEmpty) {
            assigns
          } else {
            val notAfter = withPos.filter { case (_, (line, col)) =>
              line < retLine || (line == retLine && col <= cutoffCol)
            }
            val base = if (notAfter.nonEmpty) notAfter else withPos
            val best = base.map(_._2).maxBy { case (line, col) => (line, col) }
            base.collect { case (record, lc) if lc == best => record }
          }
        case None =>
          assigns
      }
    }
  }

  private def collectRootLevelFormalReturnAssignmentRecords(method: vpr.Method): Vector[AssignmentRecord] = {
    val formalNames = method.formalReturns.map(ret => stripVarSuffix(ret.name)).toSet
    method.body match {
      case Some(root) =>
        collectAssignmentsWithPos(Vector(root)).filter(record => formalNames.contains(stripVarSuffix(record.lhsName)))
      case None =>
        Vector.empty
    }
  }

  private def collectRootLevelAssignmentRecords(method: vpr.Method): Vector[AssignmentRecord] =
    method.body match {
      case Some(root) => collectAssignmentsWithPos(Vector(root))
      case None => Vector.empty
    }

  private def collectAssignmentsWithPos(stmts: Vector[vpr.Stmt]): Vector[AssignmentRecord] = {
    val records = mutable.ArrayBuffer.empty[AssignmentRecord]
    var order = 0

    def sourceLineCol(node: vpr.Node): (Option[Int], Option[Int]) =
      try {
        Source.unapply(node)
          .flatMap(info => Option(info.origin.pos))
          .map(pos => (Option(pos.line), Option(pos.column)))
          .getOrElse((None, None))
      } catch {
        case _: Throwable => (None, None)
      }

    def visit(stmt: vpr.Stmt): Unit =
      stmt match {
        case vpr.LocalVarAssign(lhs, rhs) =>
          val (lineOpt, colOpt) = sourceLineCol(stmt)
          records += AssignmentRecord(
            lhsName = lhs.name,
            rhs = rhs,
            line = lineOpt,
            column = colOpt,
            order = order,
          )
          order += 1
        case seqn: vpr.Seqn =>
          seqn.ss.foreach(visit)
        case iff: vpr.If =>
          visit(iff.thn)
          visit(iff.els)
        case loop: vpr.While =>
          visit(loop.body)
        case _ =>
      }

    stmts.foreach(visit)
    records.toVector
  }

  private def findMarkerContext(program: vpr.Program, labelName: String): Option[MarkerContext] =
    program.methods.iterator.flatMap { method =>
      method.body.toVector.iterator.flatMap { body =>
        findMarkerContextInStmt(
          method = method,
          stmt = body,
          labelName = labelName,
          prefix = Vector.empty,
        )
      }
    }.toVector.headOption

  private def findMarkerContextInStmt(
                                       method: vpr.Method,
                                       stmt: vpr.Stmt,
                                       labelName: String,
                                       prefix: Vector[vpr.Stmt],
                                     ): Option[MarkerContext] =
    stmt match {
      case seqn: vpr.Seqn =>
        val statements = seqn.ss.toVector
        var idx = 0
        while (idx < statements.size) {
          val current = statements(idx)
          current match {
            case vpr.Label(name, _) if name == labelName =>
              return Some(
                MarkerContext(
                  method = method,
                  container = seqn,
                  labelIndex = idx,
                  pathPrefix = prefix ++ statements.take(idx),
                )
              )
            case _ =>
          }

          val nestedPrefix = prefix ++ statements.take(idx)
          findMarkerContextInStmt(
            method = method,
            stmt = current,
            labelName = labelName,
            prefix = nestedPrefix,
          ) match {
            case some@Some(_) => return some
            case None =>
          }
          idx += 1
        }
        None

      case iff: vpr.If =>
        findMarkerContextInStmt(method, iff.thn, labelName, prefix)
          .orElse(findMarkerContextInStmt(method, iff.els, labelName, prefix))

      case loop: vpr.While =>
        findMarkerContextInStmt(method, loop.body, labelName, prefix)

      case _ =>
        None
    }

  private def safeRender(value: Any): String =
    try {
      String.valueOf(value)
    } catch {
      case throwable: Throwable => s"<rendering failed: ${throwable.getClass.getSimpleName}>"
    }
}
