#!/usr/bin/env python3
from __future__ import annotations

import argparse
import re
import shutil
import tarfile
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple, TypedDict


FOLD_LINE_RE = re.compile(r"\b(?:ghost\s+)?(?:defer\s+fold|fold|unfold)\b")
UNFOLDING_IN_RE = re.compile(r"\bunfolding\b")
INVARIANT_LINE_RE = re.compile(r"\binvariant\b")
IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


@dataclass(frozen=True)
class FunctionInfo:
    relpath: str
    start_line: int
    end_line: int
    body_start_line: int
    name: str
    receiver: Optional[str]
    qualname: str


@dataclass(frozen=True)
class FunctionMetrics:
    function: FunctionInfo
    gobra_annotation_lines: int
    gobra_annotation_lines_excluding_contract: int
    fold_unfold_defer_lines: int
    loop_invariant_lines: int

    @property
    def has_gobra_annotations(self) -> bool:
        return self.gobra_annotation_lines > 0

    @property
    def has_fold_unfold(self) -> bool:
        return self.fold_unfold_defer_lines > 0

    @property
    def has_loop_invariant(self) -> bool:
        return self.loop_invariant_lines > 0


class VerifiedScionSizeStats(TypedDict):
    go_file_count: int
    gobra_file_count: int
    go_loc: int
    gobra_loc: int
    total_loc: int
    total_kloc: float


class FoldbenchBenchmarkStats(TypedDict):
    target_count: int
    file_count: int
    package_count: int
    average_fold_unfold_lines_per_target: float


@dataclass(frozen=True)
class ExperimentArchiveSpec:
    label: str
    archive_path: Path


@dataclass(frozen=True)
class SessionSeries:
    mode: str
    total_tasks: int
    success_durations_seconds: List[int]
    extracted_dir: Path


class ReproduceReport(TypedDict):
    root: str
    figure5_output_path: str
    verifiedscion_size: VerifiedScionSizeStats
    foldbench_benchmark: FoldbenchBenchmarkStats
    gobra_annotated_function_count: int
    functions_with_fold_unfold_count: int
    functions_with_loop_invariant_count: int
    functions_with_fold_unfold_share_percent_of_gobra_annotated_functions: float
    total_gobra_annotation_lines: int
    total_gobra_annotation_lines_excluding_contract: int
    total_fold_unfold_defer_lines: int
    total_loop_invariant_lines: int
    fold_unfold_defer_share_percent_of_gobra_annotation_lines: float
    loop_invariant_share_percent_of_gobra_annotation_lines: float
    fold_unfold_to_loop_invariant_line_ratio: float


class Section4StatisticsEntry(TypedDict):
    mode: str
    solved_within_20min: int
    total_tasks: int
    success_rate_percent: float


FIGURE5_EXPERIMENT_ARCHIVES: Tuple[ExperimentArchiveSpec, ...] = (
    ExperimentArchiveSpec(
        label="baseline attempt 20",
        archive_path=Path("output/sanitized_experiments/session_20260624_210224_baseline_20.tar.gz"),
    ),
    ExperimentArchiveSpec(
        label="fusion attempt 20",
        archive_path=Path("output/sanitized_experiments/session_20260624_120233_fusion_20.tar.gz"),
    ),
)

RUNLOG_TS_RE = re.compile(r"^\[(\d{2}):(\d{2}):(\d{2})\] ")
SELECTED_TASKS_RE = re.compile(r"selected tasks: (\d+)")
ATTEMPT1_RE = re.compile(r"^\[[0-9:]{8}\] \[([^\]]+)\] attempt 1/\d+: ")
SUCCESS_RE = re.compile(r"^\[[0-9:]{8}\] \[([^\]]+)\] success at attempt \d+ ")

FIGURE5_OUTPUT_PATH = Path("script/section4_figure5_evaluation.pdf")
FIGURE5_X_AXIS_MAX_MINUTES = 20.0
FIGURE5_MODE_DISPLAY_NAME = {"baseline": "Enum", "fusion": "Fusion"}
FIGURE5_STYLE_BY_MODE = {
    "baseline": {"color": "#d55e00", "marker": "o", "markersize": 5.8},
    "fusion": {"color": "#0072b2", "marker": "^", "markersize": 6.2},
}
FIGURE5_USE_TEX_TEXTSC = shutil.which("latex") is not None


def normalize_annotation_text(text: str) -> str:
    stripped = text.strip()
    if stripped.startswith("*"):
        stripped = stripped[1:].lstrip()
    return " ".join(stripped.split())


def extract_gobra_annotations(source: str) -> Dict[int, List[str]]:
    annotations: Dict[int, List[str]] = {}
    i = 0
    n = len(source)
    line = 1

    def add_line_annotation(line_no: int, text: str) -> None:
        normalized = normalize_annotation_text(text)
        if not normalized:
            return
        annotations.setdefault(line_no, []).append(normalized)

    while i < n:
        ch = source[i]

        if ch == "\n":
            line += 1
            i += 1
            continue

        if ch == "/" and i + 1 < n and source[i + 1] == "/":
            j = i + 2
            while j < n and source[j] in " \t":
                j += 1
            line_end = source.find("\n", j)
            if line_end == -1:
                line_end = n
            if j < n and source[j] == "@":
                add_line_annotation(line, source[j + 1 : line_end])
            i = line_end
            continue

        if ch == "/" and i + 1 < n and source[i + 1] == "*":
            j = i + 2
            while j < n and source[j] in " \t\r\n":
                j += 1
            end = source.find("*/", j)
            if end == -1:
                end = n
                end_len = 0
            else:
                end_len = 2
            block_text = source[j:end] if j < n and source[j] == "@" else None
            block_start_line = line
            block_raw = source[i : end + end_len]
            line += block_raw.count("\n")
            i = end + end_len
            if block_text is not None:
                for offset, part in enumerate(block_text.splitlines() or [""]):
                    add_line_annotation(block_start_line + offset, part)
            continue

        if ch == '"':
            i += 1
            while i < n:
                if source[i] == "\\" and i + 1 < n:
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    if source[i] == "\n":
                        line += 1
                    i += 1
            continue

        if ch == "'":
            i += 1
            while i < n:
                if source[i] == "\\" and i + 1 < n:
                    i += 2
                elif source[i] == "'":
                    i += 1
                    break
                else:
                    if source[i] == "\n":
                        line += 1
                    i += 1
            continue

        if ch == "`":
            i += 1
            while i < n and source[i] != "`":
                if source[i] == "\n":
                    line += 1
                i += 1
            if i < n and source[i] == "`":
                i += 1
            continue

        i += 1

    return annotations


def cleaned_source_for_func_scan(source: str) -> str:
    chars = list(source)
    i = 0
    n = len(chars)
    while i < n:
        ch = chars[i]
        if ch == "/" and i + 1 < n and chars[i + 1] == "/":
            j = i
            while j < n and chars[j] != "\n":
                if chars[j] != "\n":
                    chars[j] = " "
                j += 1
            i = j
            continue
        if ch == "/" and i + 1 < n and chars[i + 1] == "*":
            j = i
            chars[j] = " "
            j += 1
            chars[j] = " "
            j += 1
            while j + 1 < n and not (chars[j] == "*" and chars[j + 1] == "/"):
                if chars[j] != "\n":
                    chars[j] = " "
                j += 1
            if j + 1 < n:
                chars[j] = " "
                chars[j + 1] = " "
                j += 2
            i = j
            continue
        if ch == '"':
            chars[i] = " "
            i += 1
            while i < n:
                if chars[i] == "\\" and i + 1 < n:
                    chars[i] = " "
                    chars[i + 1] = " "
                    i += 2
                elif chars[i] == '"':
                    chars[i] = " "
                    i += 1
                    break
                else:
                    if chars[i] != "\n":
                        chars[i] = " "
                    i += 1
            continue
        if ch == "'":
            chars[i] = " "
            i += 1
            while i < n:
                if chars[i] == "\\" and i + 1 < n:
                    chars[i] = " "
                    chars[i + 1] = " "
                    i += 2
                elif chars[i] == "'":
                    chars[i] = " "
                    i += 1
                    break
                else:
                    if chars[i] != "\n":
                        chars[i] = " "
                    i += 1
            continue
        if ch == "`":
            chars[i] = " "
            i += 1
            while i < n and chars[i] != "`":
                if chars[i] != "\n":
                    chars[i] = " "
                i += 1
            if i < n and chars[i] == "`":
                chars[i] = " "
                i += 1
            continue
        i += 1
    return "".join(chars)


def line_number_at(source: str, idx: int) -> int:
    return source.count("\n", 0, idx) + 1


def extract_receiver_and_name(signature: str) -> Tuple[Optional[str], str]:
    sig = " ".join(signature.split())
    if not sig.startswith("func"):
        return None, "<unknown>"
    rest = sig[4:].lstrip()
    receiver = None
    if rest.startswith("("):
        depth = 0
        end = None
        for idx, ch in enumerate(rest):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0:
                    end = idx
                    break
        if end is not None:
            receiver_raw = rest[1:end].strip()
            receiver_tokens = receiver_raw.split()
            if receiver_tokens:
                recv_type = receiver_tokens[-1]
                recv_type = recv_type.lstrip("*")
                recv_type = recv_type.split(".")[-1]
                recv_type = recv_type.split("[", 1)[0]
                receiver = recv_type
            rest = rest[end + 1 :].lstrip()
    m = IDENT_RE.match(rest)
    if not m:
        return receiver, "<unknown>"
    return receiver, m.group(0)


def extract_functions(relpath: str, source: str) -> List[FunctionInfo]:
    cleaned = cleaned_source_for_func_scan(source)
    match_starts = [m.start() for m in re.finditer(r"(?m)^[ \t]*func\b", cleaned)]
    top_level_depth: Dict[int, int] = {}
    wanted = set(match_starts)
    brace_depth = 0
    for idx, ch in enumerate(cleaned):
        if idx in wanted:
            top_level_depth[idx] = brace_depth
        if ch == "{":
            brace_depth += 1
        elif ch == "}":
            brace_depth = max(0, brace_depth - 1)
    funcs: List[FunctionInfo] = []
    for match in re.finditer(r"(?m)^[ \t]*func\b", cleaned):
        start_idx = match.start()
        if top_level_depth.get(start_idx, 0) != 0:
            continue

        i = match.end()
        paren_depth = 0
        bracket_depth = 0
        sig_brace_depth = 0
        body_start_idx: Optional[int] = None
        while i < len(cleaned):
            ch = cleaned[i]
            if ch == "(":
                paren_depth += 1
            elif ch == ")":
                paren_depth = max(0, paren_depth - 1)
            elif ch == "[":
                bracket_depth += 1
            elif ch == "]":
                bracket_depth = max(0, bracket_depth - 1)
            elif ch == "{":
                if paren_depth == 0 and bracket_depth == 0 and sig_brace_depth == 0:
                    body_start_idx = i
                    break
                sig_brace_depth += 1
            elif ch == "}":
                if sig_brace_depth > 0:
                    sig_brace_depth -= 1
            i += 1
        if body_start_idx is None:
            continue

        brace_depth = 1
        j = body_start_idx + 1
        while j < len(cleaned) and brace_depth > 0:
            ch = cleaned[j]
            if ch == "{":
                brace_depth += 1
            elif ch == "}":
                brace_depth -= 1
            j += 1
        if brace_depth != 0:
            continue
        end_idx = j - 1

        signature = cleaned[start_idx:body_start_idx]
        receiver, name = extract_receiver_and_name(signature)
        qualname = f"{receiver}.{name}" if receiver else name
        funcs.append(
            FunctionInfo(
                relpath=relpath,
                start_line=line_number_at(source, start_idx),
                end_line=line_number_at(source, end_idx),
                body_start_line=line_number_at(source, body_start_idx),
                name=name,
                receiver=receiver,
                qualname=qualname,
            )
        )
    return funcs
def associated_contract_lines(func_start_line: int, annotations: Dict[int, List[str]]) -> List[int]:
    result: List[int] = []
    idx = func_start_line - 2
    while idx >= 0:
        line_no = idx + 1
        if line_no not in annotations:
            break
        result.append(line_no)
        idx -= 1
    result.reverse()
    return result


def line_has_fold_unfold(annotation_texts: Iterable[str]) -> bool:
    for text in annotation_texts:
        normalized = " ".join(text.split())
        if UNFOLDING_IN_RE.search(normalized):
            continue
        if FOLD_LINE_RE.search(normalized):
            return True
    return False


def line_has_loop_invariant(annotation_texts: Iterable[str]) -> bool:
    return any(INVARIANT_LINE_RE.search(" ".join(text.split())) for text in annotation_texts)


def compute_function_metrics(relpath: str, source: str) -> List[FunctionMetrics]:
    annotations = extract_gobra_annotations(source)
    functions = extract_functions(relpath, source)
    metrics: List[FunctionMetrics] = []

    for fn in functions:
        contract_lines = set(associated_contract_lines(fn.start_line, annotations))
        body_lines = set(range(fn.start_line, fn.end_line + 1))
        relevant_lines = set(body_lines)
        relevant_lines.update(contract_lines)

        gobra_lines = 0
        gobra_lines_excluding_contract = 0
        fold_lines = 0
        invariant_lines = 0
        for line_no in sorted(relevant_lines):
            texts = annotations.get(line_no)
            if not texts:
                continue
            gobra_lines += 1
            if line_no in body_lines:
                gobra_lines_excluding_contract += 1
            if line_has_fold_unfold(texts):
                fold_lines += 1
            if line_has_loop_invariant(texts):
                invariant_lines += 1

        metrics.append(
            FunctionMetrics(
                function=fn,
                gobra_annotation_lines=gobra_lines,
                gobra_annotation_lines_excluding_contract=gobra_lines_excluding_contract,
                fold_unfold_defer_lines=fold_lines,
                loop_invariant_lines=invariant_lines,
            )
        )
    return metrics


def function_label(fn: FunctionInfo) -> str:
    return f"{fn.relpath}:{fn.start_line}:{fn.qualname}"


def mean(values: Sequence[int]) -> float:
    if not values:
        return 0.0
    return sum(values) / len(values)


def count_file_lines(path: Path) -> int:
    with path.open("r", encoding="utf-8") as f:
        return sum(1 for _ in f)


def ensure_experiment_extracted(spec: ExperimentArchiveSpec) -> Path:
    archive_path = spec.archive_path.resolve()
    extracted_dir = archive_path.parent / archive_path.name.removesuffix(".tar.gz")
    if extracted_dir.exists():
        return extracted_dir
    if not archive_path.exists():
        raise SystemExit(f"Missing sanitized experiment archive: {archive_path}")
    with tarfile.open(archive_path, "r:gz") as tar:
        tar.extractall(path=archive_path.parent)
    return extracted_dir


def parse_runlog_time_to_seconds(log_path: Path) -> Tuple[int, Dict[str, int], Dict[str, int]]:
    total_tasks: Optional[int] = None
    start_times: Dict[str, int] = {}
    success_times: Dict[str, int] = {}
    day_offset = 0
    prev_wall_seconds: Optional[int] = None

    with log_path.open("r", encoding="utf-8") as f:
        for raw_line in f:
            line = raw_line.rstrip("\n")
            ts_match = RUNLOG_TS_RE.match(line)
            if not ts_match:
                continue
            hour, minute, second = map(int, ts_match.groups())
            wall_seconds = hour * 3600 + minute * 60 + second
            if prev_wall_seconds is not None and wall_seconds < prev_wall_seconds:
                day_offset += 24 * 3600
            prev_wall_seconds = wall_seconds
            absolute_seconds = day_offset + wall_seconds

            if total_tasks is None:
                tasks_match = SELECTED_TASKS_RE.search(line)
                if tasks_match is not None:
                    total_tasks = int(tasks_match.group(1))

            attempt_match = ATTEMPT1_RE.match(line)
            if attempt_match is not None:
                task_id = attempt_match.group(1)
                start_times.setdefault(task_id, absolute_seconds)
                continue

            success_match = SUCCESS_RE.match(line)
            if success_match is not None:
                task_id = success_match.group(1)
                success_times[task_id] = absolute_seconds

    if total_tasks is None:
        raise SystemExit(f"Could not parse selected task count from run.log: {log_path}")
    return total_tasks, start_times, success_times


def load_session_series(spec: ExperimentArchiveSpec) -> SessionSeries:
    extracted_dir = ensure_experiment_extracted(spec)
    run_log = extracted_dir / "run.log"
    if not run_log.exists():
        raise SystemExit(f"Missing run.log in sanitized experiment directory: {run_log}")
    total_tasks, start_times, success_times = parse_runlog_time_to_seconds(run_log)
    missing_starts = sorted(task_id for task_id in success_times if task_id not in start_times)
    if missing_starts:
        raise SystemExit(
            f"Found success entries without attempt-1 start entries in {run_log}: "
            f"{', '.join(missing_starts[:5])}"
        )
    durations = sorted(success_times[task_id] - start_times[task_id] for task_id in success_times)
    mode = "fusion" if "fusion" in spec.label else "baseline"
    return SessionSeries(
        mode=mode,
        total_tasks=total_tasks,
        success_durations_seconds=durations,
        extracted_dir=extracted_dir,
    )


def minutes(values_seconds: Sequence[int]) -> List[float]:
    return [value / 60.0 for value in values_seconds]


def filtered_durations_for_figure(series: SessionSeries) -> List[float]:
    dmins = minutes(series.success_durations_seconds)
    if series.mode == "fusion":
        return [value for value in dmins if value <= FIGURE5_X_AXIS_MAX_MINUTES]
    return dmins


def cactus_xy(durations_minutes: Sequence[float]) -> Tuple[List[float], List[int]]:
    x_values = [0.0] + list(durations_minutes)
    y_values = [0] + list(range(1, len(durations_minutes) + 1))
    return x_values, y_values


def interpolate_polyline_y(target_x: float, x_values: Sequence[float], y_values: Sequence[int]) -> float:
    if target_x <= x_values[0]:
        return float(y_values[0])
    for idx in range(1, len(x_values)):
        x0 = x_values[idx - 1]
        x1 = x_values[idx]
        y0 = y_values[idx - 1]
        y1 = y_values[idx]
        if target_x <= x1:
            if x1 == x0:
                return float(y1)
            ratio = (target_x - x0) / (x1 - x0)
            return float(y0 + ratio * (y1 - y0))
    return float(y_values[-1])


def sampled_marker_points(x_values: Sequence[float], y_values: Sequence[int]) -> Tuple[List[float], List[float]]:
    if len(x_values) <= 1:
        return [0.0], [0.0]
    last_x = x_values[-1]
    sample_limit = last_x - 1.0
    marker_x: List[float] = [0.0]
    marker_y: List[float] = [0.0]
    minute_mark = 1
    while minute_mark <= int(sample_limit):
        marker_x.append(float(minute_mark))
        marker_y.append(interpolate_polyline_y(float(minute_mark), x_values, y_values))
        minute_mark += 1
    marker_x.append(last_x)
    marker_y.append(float(y_values[-1]))
    return marker_x, marker_y


def figure5_legend_label(mode: str) -> str:
    display = FIGURE5_MODE_DISPLAY_NAME[mode]
    if FIGURE5_USE_TEX_TEXTSC:
        return rf"\textsc{{{display}}}"
    return display


def load_figure5_series() -> List[SessionSeries]:
    return [load_session_series(spec) for spec in FIGURE5_EXPERIMENT_ARCHIVES]


def collect_section4_statistics(series_list: Sequence[SessionSeries]) -> List[Section4StatisticsEntry]:
    rows: List[Section4StatisticsEntry] = []
    for series in series_list:
        solved_within_budget = len(filtered_durations_for_figure(series))
        success_rate_percent = round((100.0 * solved_within_budget / series.total_tasks), 1) if series.total_tasks else 0.0
        rows.append(
            {
                "mode": series.mode,
                "solved_within_20min": solved_within_budget,
                "total_tasks": series.total_tasks,
                "success_rate_percent": success_rate_percent,
            }
        )
    return rows


def generate_figure5_plot(repo_root: Path, series_list: Sequence[SessionSeries]) -> Path:
    from matplotlib import pyplot as plt
    from matplotlib.lines import Line2D

    plt.rcParams.update({
        "text.usetex": FIGURE5_USE_TEX_TEXTSC,
        "font.family": "serif" if FIGURE5_USE_TEX_TEXTSC else "sans-serif",
    })
    plt.figure(figsize=(5, 3))
    legend_handles: Dict[str, Line2D] = {}

    for series in series_list:
        dmins = filtered_durations_for_figure(series)
        x_values, y_values = cactus_xy(dmins)
        marker_x, marker_y = sampled_marker_points(x_values, y_values)
        style = FIGURE5_STYLE_BY_MODE[series.mode]
        plt.plot(
            x_values,
            y_values,
            linewidth=1.3,
            color=style["color"],
            linestyle="-",
        )
        plt.plot(
            marker_x,
            marker_y,
            linestyle="None",
            marker=style["marker"],
            markersize=style["markersize"],
            markeredgewidth=0.8,
            color=style["color"],
            markerfacecolor=style["color"],
            markeredgecolor=style["color"],
        )
        if dmins:
            if series.mode == "baseline":
                offset_points = (0, 8)
                h_align = "center"
                v_align = "bottom"
            else:
                offset_points = (8, 0)
                h_align = "left"
                v_align = "center"
            plt.annotate(
                f"{len(dmins)}",
                (dmins[-1], len(dmins)),
                xytext=offset_points,
                textcoords="offset points",
                color=style["color"],
                fontsize=12,
                fontweight="bold",
                ha=h_align,
                va=v_align,
            )
        legend_handles[series.mode] = Line2D(
            [0],
            [0],
            color=style["color"],
            linewidth=1.3,
            linestyle="-",
            marker=style["marker"],
            markersize=style["markersize"],
            markerfacecolor=style["color"],
            markeredgecolor=style["color"],
            markeredgewidth=0.8,
            label=figure5_legend_label(series.mode),
        )

    plt.xlabel("Per-function repair time (minutes)", fontsize=16)
    plt.ylabel("# of solved functions", fontsize=16)
    plt.xlim(left=0.0, right=FIGURE5_X_AXIS_MAX_MINUTES)
    plt.xticks([0, 5, 10, 15, 20], ["0", "5", "10", "15", "20"])
    plt.ylim(bottom=0, top=100)
    plt.tick_params(axis="both", labelsize=13)
    plt.grid(True, alpha=0.3)
    ordered_handles = [legend_handles[mode] for mode in ("fusion", "baseline") if mode in legend_handles]
    plt.legend(
        loc="lower right",
        handles=ordered_handles,
        frameon=True,
        facecolor="white",
        edgecolor="#808080",
        fancybox=False,
        framealpha=1.0,
    )
    plt.tight_layout()

    out_path = (repo_root / FIGURE5_OUTPUT_PATH).resolve()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(out_path, dpi=220)
    plt.close()
    return out_path


def collect_verifiedscion_size_stats(root: Path) -> VerifiedScionSizeStats:
    go_files = sorted(root.rglob("*.go"))
    gobra_files = sorted(root.rglob("*.gobra"))
    go_lines = sum(count_file_lines(path) for path in go_files)
    gobra_lines = sum(count_file_lines(path) for path in gobra_files)
    total_lines = go_lines + gobra_lines
    return {
        "go_file_count": len(go_files),
        "gobra_file_count": len(gobra_files),
        "go_loc": go_lines,
        "gobra_loc": gobra_lines,
        "total_loc": total_lines,
        "total_kloc": total_lines / 1000.0,
    }


def collect_foldbench_targets(root: Path) -> List[FunctionInfo]:
    targets: List[FunctionInfo] = []
    seen: set[str] = set()
    for path in sorted(root.rglob("*.go")):
        relpath = path.relative_to(root.parent).as_posix()
        source = path.read_text(encoding="utf-8")
        functions = extract_functions(relpath, source)
        for line_no, line in enumerate(source.splitlines(), start=1):
            if "FOLDBENCH" not in line:
                continue
            target = next((fn for fn in functions if fn.start_line > line_no), None)
            if target is None:
                continue
            label = function_label(target)
            if label in seen:
                continue
            seen.add(label)
            targets.append(target)
    return targets


def collect_foldbench_stats(root: Path, metrics: Sequence[FunctionMetrics]) -> FoldbenchBenchmarkStats:
    targets = collect_foldbench_targets(root)
    metrics_by_label = {function_label(m.function): m for m in metrics}
    target_labels = [function_label(fn) for fn in targets]
    target_metrics = [metrics_by_label[label] for label in target_labels if label in metrics_by_label]
    target_files = sorted({fn.relpath for fn in targets})
    target_packages = sorted({Path(fn.relpath).parent.as_posix() for fn in targets})
    fold_counts = [m.fold_unfold_defer_lines for m in target_metrics]
    return {
        "target_count": len(targets),
        "file_count": len(target_files),
        "package_count": len(target_packages),
        "average_fold_unfold_lines_per_target": mean(fold_counts),
    }


def collect_metrics(root: Path) -> List[FunctionMetrics]:
    all_metrics: List[FunctionMetrics] = []
    for path in sorted(root.rglob("*.go")):
        relpath = path.relative_to(root.parent).as_posix()
        source = path.read_text(encoding="utf-8")
        all_metrics.extend(compute_function_metrics(relpath, source))
    return all_metrics


def build_report(root: Path) -> ReproduceReport:
    repo_root = Path(__file__).resolve().parent.parent
    metrics = collect_metrics(root)
    verifiedscion_size = collect_verifiedscion_size_stats(root)
    figure5_output_path = (repo_root / FIGURE5_OUTPUT_PATH).resolve()
    foldbench_stats = collect_foldbench_stats(root, metrics)
    annotated = [m for m in metrics if m.has_gobra_annotations]
    with_fold = [m for m in annotated if m.has_fold_unfold]
    with_invariant = [m for m in annotated if m.has_loop_invariant]
    total_gobra_annotation_lines = sum(m.gobra_annotation_lines for m in annotated)
    total_gobra_annotation_lines_excluding_contract = sum(
        m.gobra_annotation_lines_excluding_contract for m in annotated
    )
    total_fold_unfold_defer_lines = sum(m.fold_unfold_defer_lines for m in annotated)
    total_loop_invariant_lines = sum(m.loop_invariant_lines for m in annotated)
    fold_share_percent = (
        (100.0 * total_fold_unfold_defer_lines / total_gobra_annotation_lines)
        if total_gobra_annotation_lines > 0
        else 0.0
    )
    functions_with_fold_unfold_share_percent = (
        (100.0 * len(with_fold) / len(annotated))
        if annotated
        else 0.0
    )
    loop_invariant_share_percent = (
        (100.0 * total_loop_invariant_lines / total_gobra_annotation_lines)
        if total_gobra_annotation_lines > 0
        else 0.0
    )
    fold_unfold_to_loop_invariant_ratio = (
        (total_fold_unfold_defer_lines / total_loop_invariant_lines)
        if total_loop_invariant_lines > 0
        else 0.0
    )
    report: ReproduceReport = {
        "root": str(root),
        "figure5_output_path": str(figure5_output_path),
        "verifiedscion_size": verifiedscion_size,
        "foldbench_benchmark": foldbench_stats,
        "gobra_annotated_function_count": len(annotated),
        "functions_with_fold_unfold_count": len(with_fold),
        "functions_with_loop_invariant_count": len(with_invariant),
        "functions_with_fold_unfold_share_percent_of_gobra_annotated_functions": functions_with_fold_unfold_share_percent,
        "total_gobra_annotation_lines": total_gobra_annotation_lines,
        "total_gobra_annotation_lines_excluding_contract": total_gobra_annotation_lines_excluding_contract,
        "total_fold_unfold_defer_lines": total_fold_unfold_defer_lines,
        "total_loop_invariant_lines": total_loop_invariant_lines,
        "fold_unfold_defer_share_percent_of_gobra_annotation_lines": fold_share_percent,
        "loop_invariant_share_percent_of_gobra_annotation_lines": loop_invariant_share_percent,
        "fold_unfold_to_loop_invariant_line_ratio": fold_unfold_to_loop_invariant_ratio,
    }
    return report


def print_human_report(report: ReproduceReport) -> None:
    size = report["verifiedscion_size"]
    foldbench = report["foldbench_benchmark"]
    print("=== Input Detection ===")
    print(f"VerifiedSCION directory: {report['root']}")
    print()
    print("=== Section 1 Statistics ===")
    print(f"Gobra-annotated functions/methods: {report['gobra_annotated_function_count']}")
    print(f"Total Gobra annotation lines: {report['total_gobra_annotation_lines']}")
    print(
        "Total Gobra annotation lines excluding function-level contract lines: "
        f"{report['total_gobra_annotation_lines_excluding_contract']}"
    )
    print(f"Total fold/unfold lines: {report['total_fold_unfold_defer_lines']}")
    print(f"Total loop invariant lines: {report['total_loop_invariant_lines']}")
    print(
        f"Functions with at least one fold/unfold: "
        f"{report['functions_with_fold_unfold_count']}"
    )
    print(
        f"Functions with at least one loop invariant: "
        f"{report['functions_with_loop_invariant_count']}"
    )

    print(
        "Share of fold/unfold lines among total Gobra annotation lines: "
        f"{report['fold_unfold_defer_share_percent_of_gobra_annotation_lines']:.3f}%"
    )
    print(
        "Share of loop invariant lines among total Gobra annotation lines: "
        f"{report['loop_invariant_share_percent_of_gobra_annotation_lines']:.3f}%"
    )
    print(
        ">> Share of Gobra-annotated functions/methods that contain at least one fold/unfold: "
        f"{report['functions_with_fold_unfold_share_percent_of_gobra_annotated_functions']:.3f}%"
    )
    print(
        ">> Fold/unfold lines divided by loop invariant lines: "
        f"{report['fold_unfold_to_loop_invariant_line_ratio']:.3f}x"
    )
    print()
    print("=== Section 4 Table 1 Benchmark Features ===")
    print(
        "VerifiedSCION size (.go + .gobra): "
        f"{size['total_kloc']:.3f} kLoC"
    )
    print(
        "FOLDBENCH targets / files / packages: "
        f"{foldbench['target_count']} / {foldbench['file_count']} / {foldbench['package_count']}"
    )
    print(
        "Average fold/unfold lines per FOLDBENCH target: "
        f"{foldbench['average_fold_unfold_lines_per_target']:.3f}"
    )


def print_section4_statistics(section4_stats: Sequence[Section4StatisticsEntry]) -> None:
    print()
    print("=== Section 4 Statistics ===")
    for row in section4_stats:
        mode_display = "Fusion" if row["mode"] == "fusion" else "Enum"
        print(
            f"{mode_display} solved within 20 minutes: "
            f"{row['solved_within_20min']}/{row['total_tasks']} "
            f"({row['success_rate_percent']:.1f}%)"
        )


def print_figure5_graph_section(repo_root: Path, report: ReproduceReport, series_list: Sequence[SessionSeries]) -> None:
    print()
    print("=== Section 4 Figure 5 Graph ===")
    if FIGURE5_USE_TEX_TEXTSC:
        print("Legend labels: LaTeX small caps")
    else:
        print("Legend labels: fallback text (latex not found)")

    print("Detected Figure 5 experiment directories:")
    for series in series_list:
        print(f"  - {series.extracted_dir}")
    for series in series_list:
        dmins = filtered_durations_for_figure(series)
        avg_minutes = (sum(dmins) / len(dmins)) if dmins else 0.0
        print(
            f"Loaded {series.mode} attempt 20: "
            f"{len(dmins)}/{series.total_tasks} solved within {FIGURE5_X_AXIS_MAX_MINUTES:.0f} min, "
            f"avg solve time {avg_minutes:.2f} min"
        )
    out_path = generate_figure5_plot(repo_root, series_list)
    print(f"Figure 5 output: {out_path}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Measure Gobra annotation features over VerifiedSCION .go files."
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path("benchmark/verifiedscion"),
        help="Root directory containing VerifiedSCION .go files.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    repo_root = Path(__file__).resolve().parent.parent
    root = args.root.resolve()
    if not root.exists():
        raise SystemExit(f"Root does not exist: {root}")
    report = build_report(root)
    print_human_report(report)
    figure5_series = load_figure5_series()
    section4_stats = collect_section4_statistics(figure5_series)
    print_section4_statistics(section4_stats)
    print_figure5_graph_section(repo_root, report, figure5_series)


if __name__ == "__main__":
    main()
