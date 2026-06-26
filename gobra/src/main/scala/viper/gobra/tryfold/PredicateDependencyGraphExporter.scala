package viper.gobra.tryfold

import viper.gobra.backend.BackendVerifier
import viper.gobra.frontend.Config
import viper.silver.ast

import java.nio.charset.StandardCharsets
import java.nio.file.Files

object PredicateDependencyGraphExporter {

  private[tryfold] final case class GraphExportMetadata(
                                                         taskName: String,
                                                         attempt: Int,
                                                         workItemId: Long,
                                                         workItemDepth: Int,
                                                         firstErrorId: Option[String],
                                                         firstErrorReadableMessage: Option[String],
                                                         firstErrorSourceLocation: Option[String],
                                                       )

  def maybeExport(
                   config: Config,
                   graph: PredicateDependencyGraph,
                   attempt: Int,
                   workItemId: Long,
                   workItemDepth: Int,
                   failure: BackendVerifier.Failure,
                 ): Unit = {
    config.tryFoldGraphOut.foreach { outputPath =>
      val firstError = failure.errors.headOption
      val metadata = GraphExportMetadata(
        taskName = config.taskName,
        attempt = attempt,
        workItemId = workItemId,
        workItemDepth = workItemDepth,
        firstErrorId = firstError.map(_.fullId),
        firstErrorReadableMessage = firstError.map(_.readableMessage(withId = true, withPosition = true)),
        firstErrorSourceLocation = firstError.flatMap(err => positionToString(err.pos)),
      )
      val json = renderGraphReportJson(metadata, graph)
      val parent = outputPath.getParent
      if (parent != null) {
        Files.createDirectories(parent)
      }
      Files.write(outputPath, json.getBytes(StandardCharsets.UTF_8))
    }
  }

  private[tryfold] def renderGraphReportJson(metadata: GraphExportMetadata, graph: PredicateDependencyGraph): String = {
    val nodes = graph.nodes.toVector.sortBy(_.id)
    val edges = graph.edges
      .sortBy { edge =>
        (
          edge.from.id,
          edge.to.id,
          edge.kind.asString,
          edge.labels.toVector.map(labelSortKey).sorted.mkString("|"),
          edge.templates.map(templateSortKey).mkString("|"),
        )
      }
    val payload = jsonObject(Seq(
      "taskName" -> jsonString(metadata.taskName),
      "graphMode" -> jsonString("ours"),
      "attempt" -> metadata.attempt.toString,
      "workItemId" -> metadata.workItemId.toString,
      "workItemDepth" -> metadata.workItemDepth.toString,
      "firstErrorId" -> jsonOption(metadata.firstErrorId),
      "firstErrorReadableMessage" -> jsonOption(metadata.firstErrorReadableMessage),
      "firstErrorSourceLocation" -> jsonOption(metadata.firstErrorSourceLocation),
      "nodeCount" -> nodes.size.toString,
      "edgeCount" -> edges.size.toString,
      "nodes" -> jsonArray(nodes.map(nodeToJson)),
      "edges" -> jsonArray(edges.map(edgeToJson)),
    ))
    prettyJson(payload)
  }

  private def nodeToJson(node: DependencyNode): String =
    node match {
      case PredicateNode(name) =>
        jsonObject(Seq(
          "id" -> jsonString(node.id),
          "kind" -> jsonString("predicate"),
          "name" -> jsonString(name),
        ))
      case FieldNode(name) =>
        jsonObject(Seq(
          "id" -> jsonString(node.id),
          "kind" -> jsonString("field"),
          "name" -> jsonString(name),
        ))
      case BoolLiteralNode(value) =>
        jsonObject(Seq(
          "id" -> jsonString(node.id),
          "kind" -> jsonString("boolLiteral"),
          "name" -> jsonString(value.toString),
          "value" -> value.toString,
        ))
    }

  private def edgeToJson(edge: DependencyEdge): String = {
    val labels = edge.labels.toVector.sortBy(labelSortKey)
    jsonObject(Seq(
      "from" -> jsonString(edge.from.id),
      "to" -> jsonString(edge.to.id),
      "kind" -> jsonString(edge.kind.asString),
      "labelCount" -> labels.size.toString,
      "labels" -> jsonArray(labels.map(labelToJson)),
      "templateCount" -> edge.templates.size.toString,
      "templates" -> jsonArray(edge.templates.toVector.sortBy(templateSortKey).map(templateToJson)),
    ))
  }

  private def labelToJson(label: DependencyEdgeLabel): String =
    label match {
      case UnlabeledEdge =>
        jsonObject(Seq("kind" -> jsonString("unlabeled")))
      case DynamicAlternativeLabel(typeKey) =>
        jsonObject(Seq(
          "kind" -> jsonString("dynamicAlternative"),
          "typeKey" -> jsonString(typeKey),
        ))
    }

  private def labelSortKey(label: DependencyEdgeLabel): String =
    label match {
      case UnlabeledEdge => "0:unlabeled"
      case DynamicAlternativeLabel(typeKey) => s"1:$typeKey"
    }

  private def templateToJson(template: EdgeCallsiteTemplate): String =
    jsonObject(Seq(
      "ownerFormalParams" -> jsonArray(template.ownerFormalParams.map(jsonString)),
      "calleeArgTemplates" -> jsonArray(template.calleeArgTemplates.map(jsonString)),
      "ownerFormalParamsExp" -> jsonArray(template.ownerFormalParamsExp.map(v => jsonString(safeRender(v)))),
      "calleeArgTemplatesExp" -> jsonArray(template.calleeArgTemplatesExp.map(v => jsonString(safeRender(v)))),
    ))

  private def templateSortKey(template: EdgeCallsiteTemplate): String =
    s"${template.ownerFormalParams.mkString(",")}=>${template.calleeArgTemplates.mkString(",")}"

  private def positionToString(position: ast.Position): Option[String] =
    if (position == ast.NoPosition) None
    else Some(safeRender(position))

  private def safeRender(value: Any): String =
    try {
      String.valueOf(value)
    } catch {
      case throwable: Throwable => s"<rendering failed: ${throwable.getClass.getSimpleName}>"
    }

  private def jsonOption(value: Option[String]): String =
    value match {
      case Some(v) => jsonString(v)
      case None => "null"
    }

  private def jsonArray(values: Seq[String]): String =
    values.mkString("[", ",", "]")

  private def jsonObject(fields: Seq[(String, String)]): String =
    fields.map { case (key, value) => s"${jsonString(key)}:$value" }.mkString("{", ",", "}")

  private def jsonString(value: String): String =
    "\"" + escapeJson(value) + "\""

  private def escapeJson(value: String): String = {
    val out = new StringBuilder(value.length + 8)
    value.foreach {
      case '"' => out.append("\\\"")
      case '\\' => out.append("\\\\")
      case '\b' => out.append("\\b")
      case '\f' => out.append("\\f")
      case '\n' => out.append("\\n")
      case '\r' => out.append("\\r")
      case '\t' => out.append("\\t")
      case c if c < ' ' => out.append(f"\\u${c.toInt}%04x")
      case c => out.append(c)
    }
    out.toString()
  }

  private def prettyJson(minifiedJson: String): String = {
    val out = new StringBuilder(minifiedJson.length + 32)
    var indentation = 0
    var inString = false
    var escaping = false

    def appendIndent(): Unit = {
      var i = 0
      while (i < indentation) {
        out.append("  ")
        i += 1
      }
    }

    minifiedJson.foreach { ch =>
      if (inString) {
        out.append(ch)
        if (escaping) {
          escaping = false
        } else if (ch == '\\') {
          escaping = true
        } else if (ch == '"') {
          inString = false
        }
      } else {
        ch match {
          case '{' | '[' =>
            out.append(ch).append('\n')
            indentation += 1
            appendIndent()
          case '}' | ']' =>
            out.append('\n')
            indentation -= 1
            appendIndent()
            out.append(ch)
          case ',' =>
            out.append(ch).append('\n')
            appendIndent()
          case ':' =>
            out.append(": ")
          case '"' =>
            inString = true
            out.append(ch)
          case _ =>
            out.append(ch)
        }
      }
    }
    out.append('\n')
    out.toString()
  }
}
