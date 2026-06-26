#!/usr/bin/env python3
"""
Source-level BFS experiment engine for Gobra tryFold.

Design:
- Gobra tryFold is used as a single-step candidate generator.
- This script manages source-level candidate states with a BFS worklist.
- For each dequeued state:
  1) write candidate source to target file,
  2) run Gobra with --tryFold and JSON exports,
  3) if verification fails, read tryfold_path.json and enqueue children.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import logging
import os
import re
import shlex
import subprocess
import sys
import traceback
from collections import deque
from dataclasses import dataclass, asdict
from datetime import datetime
from pathlib import Path
from typing import Any, Deque, Dict, Iterable, List, Optional, Sequence, Tuple

FOLDBENCH_MARKER = "// FOLDBENCH"
TARGET_PLACEHOLDER = "__TARGET__"


@dataclass(frozen=True)
class ScriptSpec:
    name: str
    raw_script: str
    tokens: List[str]
    target_file: Optional[Path]
    target_token_index: int
    path_base: Path
    old_root_prefix: Optional[Path]


@dataclass(frozen=True)
class FunctionTask:
    task_id: str
    script_name: str
    target_file: Path
    function_name: str
    function_decl_line: int
    function_signature_line: str
    marker_line: Optional[int]


@dataclass
class CandidatePatch:
    candidate_id: int
    insertion_line: int
    insertion_column: Optional[int]
    insertion_file: Optional[Path]
    annotation_lines: List[str]
    source: str
    metadata: Dict[str, Any]


@dataclass
class WorkItem:
    state_id: int
    parent_state_id: Optional[int]
    depth: int
    content: str
    fingerprint: str
    producer: Optional[Dict[str, Any]]


def setup_logger(session_dir: Path) -> logging.Logger:
    logger = logging.getLogger("tryfold_experiment")
    logger.setLevel(logging.DEBUG)
    logger.handlers.clear()

    fmt = logging.Formatter("[%(asctime)s] %(message)s", datefmt="%H:%M:%S")

    ch = logging.StreamHandler(sys.stdout)
    ch.setLevel(logging.INFO)
    ch.setFormatter(fmt)
    logger.addHandler(ch)

    fh = logging.FileHandler(session_dir / "run.log", encoding="utf-8")
    fh.setLevel(logging.DEBUG)
    fh.setFormatter(fmt)
    logger.addHandler(fh)
    return logger


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="BFS source-level experiment engine using Gobra tryFold outputs."
    )
    default_smoke_exp_list = Path(__file__).resolve().parents[1] / "benchmark" / "smoke_run_exp_list.txt"
    parser.add_argument(
        "--exp-list",
        type=Path,
        default=None,
        help="Path to experiment list file.",
    )
    parser.add_argument(
        "--gobra-config",
        type=Path,
        default=None,
        help="Path to single-target Gobra command config JSON.",
    )
    parser.add_argument(
        "--target",
        type=str,
        default=None,
        help="Single target as '/abs/path/file.go@line'.",
    )
    parser.add_argument(
        "--all-foldbench",
        action="store_true",
        help="Run all // FOLDBENCH functions discovered from exp-list target files.",
    )
    parser.add_argument(
        "--smoke-run",
        action="store_true",
        help="Run a small exp-list-backed smoke experiment over a limited number of FOLDBENCH functions.",
    )
    parser.add_argument(
        "--smoke-file",
        type=Path,
        default=None,
        help="Optional file to restrict smoke-run tasks to, chosen from the active exp-list.",
    )
    parser.add_argument(
        "--smoke-max-functions",
        type=int,
        default=3,
        help="Maximum number of functions to run in smoke-run mode.",
    )
    parser.add_argument(
        "--mode",
        choices=["ours", "baseline"],
        default="ours",
        help="Experiment mode. ours uses graph-based Gobra tryFold; baseline uses local 1-step tryFold enumeration.",
    )
    parser.add_argument(
        "--max-attempts",
        type=int,
        default=20,
        help="Maximum verification attempts per function.",
    )
    parser.add_argument(
        "--path-max-depth",
        type=int,
        default=3,
        help="--tryFoldPathMaxDepth",
    )
    parser.add_argument(
        "--max-children-per-failure",
        type=int,
        default=64,
        help="--tryFoldMaxChildrenPerFailure",
    )
    parser.add_argument(
        "--max-concrete-per-path",
        type=int,
        default=5,
        help="--tryFoldMaxConcreteCandidatesPerPath",
    )
    parser.add_argument(
        "--mce-mode",
        choices=["off", "on", "od"],
        default="od",
        help="mce mode used in Gobra runs.",
    )
    parser.add_argument(
        "--counterexample",
        choices=["off", "native", "variables", "mapped"],
        default="off",
        help="counterexample mode; if not off, mceMode is forced to 'on'.",
    )
    parser.add_argument(
        "--kill-z3-on-task-start",
        choices=["true", "false"],
        default="false",
        help='Whether to run `pkill -f "(^|/)z3($| )"` before each target task starts.',
    )
    parser.add_argument(
        "--timeout-sec",
        type=int,
        default=180,
        help="Per-attempt timeout in seconds.",
    )
    parser.add_argument(
        "--output-root",
        type=Path,
        default=Path(__file__).resolve().parents[1] / "output" / "experiments",
        help="Directory for experiment logs and attempt artifacts.",
    )
    parser.add_argument(
        "--keep-temp-states",
        action="store_true",
        help="Store each child state content snapshot for debugging.",
    )
    args = parser.parse_args()

    has_exp_list = args.exp_list is not None
    has_gobra_config = args.gobra_config is not None
    if args.smoke_run:
        if has_gobra_config:
            parser.error("--smoke-run does not support --gobra-config.")
        if args.target or args.all_foldbench:
            parser.error("--smoke-run is mutually exclusive with --target and --all-foldbench.")
        if not has_exp_list:
            args.exp_list = default_smoke_exp_list
            has_exp_list = True
    else:
        if args.smoke_file is not None:
            parser.error("--smoke-file is only supported with --smoke-run.")
        if has_exp_list == has_gobra_config:
            parser.error("Specify exactly one of --exp-list or --gobra-config.")
        if not args.target and not args.all_foldbench:
            parser.error("Specify either --target or --all-foldbench.")
        if args.target and args.all_foldbench:
            parser.error("--target and --all-foldbench are mutually exclusive.")
        if has_gobra_config and args.all_foldbench:
            parser.error("--all-foldbench is only supported with --exp-list.")
        if has_gobra_config and not args.target:
            parser.error("--gobra-config requires --target.")
    if args.max_attempts <= 0:
        parser.error("--max-attempts must be positive.")
    if args.path_max_depth <= 0:
        parser.error("--path-max-depth must be positive.")
    if args.max_children_per_failure <= 0:
        parser.error("--max-children-per-failure must be positive.")
    if args.max_concrete_per_path <= 0:
        parser.error("--max-concrete-per-path must be positive.")
    if args.smoke_max_functions <= 0:
        parser.error("--smoke-max-functions must be positive.")
    if args.counterexample != "off" and args.mce_mode != "on":
        args.mce_mode = "on"
    args.kill_z3_on_task_start = args.kill_z3_on_task_start == "true"
    return args


def normalize_space(text: str) -> str:
    return " ".join(text.split())


def hash_content(content: str) -> str:
    return hashlib.sha256(content.encode("utf-8")).hexdigest()


def should_preserve_successful_target(args: argparse.Namespace) -> bool:
    return args.target is not None


def ensure_dir(path: Path) -> None:
    path.mkdir(parents=True, exist_ok=True)


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def write_text(path: Path, content: str) -> None:
    path.write_text(content, encoding="utf-8")


def json_dump(path: Path, obj: Any) -> None:
    def _default(value: Any) -> Any:
        if isinstance(value, Path):
            return str(value)
        raise TypeError(
            f"Object of type {value.__class__.__name__} is not JSON serializable"
        )

    with path.open("w", encoding="utf-8") as f:
        json.dump(obj, f, ensure_ascii=False, indent=2, default=_default)


def parse_exp_list(exp_list_path: Path) -> List[Tuple[str, str]]:
    content = read_text(exp_list_path)
    pattern = r"====\s*(.+?)\s*====\s*\n(.*?)\n########"
    matches = re.findall(pattern, content, re.DOTALL)
    return [(name.strip(), script.strip()) for name, script in matches]


def flatten_script_to_tokens(script: str) -> List[str]:
    lines: List[str] = []
    for raw in script.splitlines():
        line = raw.rstrip()
        if not line.strip():
            continue
        if line.endswith("\\"):
            line = line[:-1].strip()
        else:
            line = line.strip()
        if line:
            lines.append(line)
    cmd = " ".join(lines)
    return shlex.split(cmd)


def detect_old_root_prefix(tokens: Sequence[str]) -> Optional[Path]:
    for token in tokens:
        if token.startswith("/") and "/benchmark/" in token:
            return Path(token.split("/benchmark/", 1)[0]).resolve()
    return None


def maybe_rewrite_token_paths(
    tokens: Sequence[str], old_root: Optional[Path], new_root: Path
) -> List[str]:
    if old_root is None:
        return list(tokens)
    old_prefix = str(old_root)
    new_prefix = str(new_root.resolve())

    def rewrite_one(token: str) -> str:
        suffix = ""
        core = token
        if "@" in token:
            left, right = token.rsplit("@", 1)
            if right.isdigit():
                core = left
                suffix = f"@{right}"
        if core.startswith(old_prefix + os.sep):
            core = new_prefix + core[len(old_prefix) :]
        return core + suffix

    return [rewrite_one(token) for token in tokens]


def find_first_input_index(tokens: Sequence[str]) -> int:
    if "-i" not in tokens:
        raise ValueError("No -i option in exp-list script.")
    i = tokens.index("-i")
    if i + 1 >= len(tokens):
        raise ValueError("No input file after -i.")
    return i + 1


def validate_target_placeholder_index(tokens: Sequence[str]) -> int:
    indices = [i for i, tok in enumerate(tokens) if tok == TARGET_PLACEHOLDER]
    if not indices:
        raise ValueError(
            f"Gobra config command must contain {TARGET_PLACEHOLDER} exactly once."
        )
    if len(indices) > 1:
        raise ValueError(
            f"Gobra config command must contain {TARGET_PLACEHOLDER} exactly once."
        )
    idx = indices[0]
    if "-i" not in tokens:
        raise ValueError("Gobra config command must contain -i before target input.")
    i = tokens.index("-i")
    if idx != i + 1:
        raise ValueError(
            f"{TARGET_PLACEHOLDER} must appear immediately after -i in Gobra config command."
        )
    return idx


def strip_line_marker(path_token: str) -> str:
    if "@" in path_token:
        left, right = path_token.rsplit("@", 1)
        if right.isdigit():
            return left
    return path_token


def resolve_script_path(path_token: str, path_base: Path) -> Path:
    raw = strip_line_marker(path_token)
    p = Path(raw)
    if p.is_absolute():
        return p.resolve()
    return (path_base.resolve() / p).resolve()


def parse_scripts(exp_list_path: Path, workspace_root: Path) -> List[ScriptSpec]:
    specs: List[ScriptSpec] = []
    path_base = workspace_root.resolve()
    for name, script in parse_exp_list(exp_list_path):
        tokens = flatten_script_to_tokens(script)
        old_root = detect_old_root_prefix(tokens)
        rewritten = maybe_rewrite_token_paths(tokens, old_root, workspace_root)
        target_token_idx = find_first_input_index(rewritten)
        target_file = resolve_script_path(rewritten[target_token_idx], path_base)
        specs.append(
            ScriptSpec(
                name=name,
                raw_script=script,
                tokens=rewritten,
                target_file=target_file,
                target_token_index=target_token_idx,
                path_base=path_base,
                old_root_prefix=old_root,
            )
        )
    return specs


def load_config_script(config_path: Path, workspace_root: Path) -> ScriptSpec:
    try:
        cfg = json.loads(read_text(config_path))
    except json.JSONDecodeError as exc:
        raise ValueError(f"Malformed Gobra config JSON: {config_path}") from exc
    if not isinstance(cfg, dict):
        raise ValueError(f"Gobra config must be a JSON object: {config_path}")

    command = cfg.get("command")
    if not isinstance(command, str) or not command.strip():
        raise ValueError(f"Missing non-empty 'command' in Gobra config: {config_path}")

    name_raw = cfg.get("name")
    if name_raw is None:
        name = config_path.stem
    elif isinstance(name_raw, str) and name_raw.strip():
        name = name_raw.strip()
    else:
        raise ValueError(f"Invalid 'name' in Gobra config: {config_path}")

    tokens = shlex.split(command)
    target_token_idx = validate_target_placeholder_index(tokens)
    return ScriptSpec(
        name=name,
        raw_script=command,
        tokens=tokens,
        target_file=None,
        target_token_index=target_token_idx,
        path_base=workspace_root.resolve(),
        old_root_prefix=None,
    )


def map_scripts_by_target(specs: Sequence[ScriptSpec]) -> Dict[Path, ScriptSpec]:
    out: Dict[Path, ScriptSpec] = {}
    for s in specs:
        if s.target_file is None:
            continue
        out[s.target_file] = s
    return out


def _find_func_end(lines: Sequence[str], func_start: int) -> int:
    brace_count = 0
    in_function = False
    in_multiline_comment = False

    for i in range(func_start, len(lines)):
        line = lines[i]
        j = 0
        while j < len(line):
            if in_multiline_comment:
                if j + 1 < len(line) and line[j : j + 2] == "*/":
                    in_multiline_comment = False
                    j += 2
                    continue
                j += 1
                continue
            if j + 1 < len(line) and line[j : j + 2] == "/*":
                in_multiline_comment = True
                j += 2
                continue
            if j + 1 < len(line) and line[j : j + 2] == "//":
                break
            if line[j] == '"':
                j += 1
                while j < len(line):
                    if line[j] == "\\" and j + 1 < len(line):
                        j += 2
                        continue
                    if line[j] == '"':
                        j += 1
                        break
                    j += 1
                continue
            if line[j] == "`":
                j += 1
                while j < len(line) and line[j] != "`":
                    j += 1
                if j < len(line):
                    j += 1
                continue
            if line[j] == "'":
                j += 1
                while j < len(line):
                    if line[j] == "\\" and j + 1 < len(line):
                        j += 2
                        continue
                    if line[j] == "'":
                        j += 1
                        break
                    j += 1
                continue
            if line[j] == "{":
                brace_count += 1
                in_function = True
            elif line[j] == "}":
                brace_count -= 1
            j += 1
        if in_function and brace_count == 0:
            return i
    return len(lines) - 1


FUNC_DECL_RE = re.compile(r"^\s*(?:func|pred)\s+(?:\([^)]+\)\s+)?([A-Za-z_]\w*)\b")


def enumerate_functions_with_ranges(content: str) -> List[Tuple[str, int, int, str]]:
    lines = content.splitlines()
    out: List[Tuple[str, int, int, str]] = []
    i = 0
    while i < len(lines):
        m = FUNC_DECL_RE.match(lines[i])
        if m:
            name = m.group(1)
            start = i
            end = _find_func_end(lines, start)
            out.append((name, start + 1, end + 1, lines[i].strip()))
            i = end + 1
        else:
            i += 1
    return out


def find_containing_function(
    content: str, target_line_1: int
) -> Tuple[str, int, int, str]:
    funcs = enumerate_functions_with_ranges(content)
    for name, start, end, sig in funcs:
        if start <= target_line_1 <= end:
            return name, start, end, sig
    raise ValueError(f"No function contains line {target_line_1}.")


def find_foldbench_functions(file_path: Path) -> List[Tuple[str, int, int, str, int]]:
    content = read_text(file_path)
    lines = content.splitlines()
    funcs = enumerate_functions_with_ranges(content)

    marker_lines: List[int] = []
    for i, line in enumerate(lines):
        if FOLDBENCH_MARKER in line:
            marker_lines.append(i + 1)

    result: List[Tuple[str, int, int, str, int]] = []
    for marker in marker_lines:
        for name, start, end, sig in funcs:
            if start >= marker:
                result.append((name, start, end, sig, marker))
                break
    return result


def find_foldbench_marker_for_function(
    lines: Sequence[str],
    funcs: Sequence[Tuple[str, int, int, str]],
    function_start_line_1: int,
) -> Optional[int]:
    prev_end = 0
    for _, start, end, _ in funcs:
        if end < function_start_line_1:
            prev_end = max(prev_end, end)
            continue
        if start == function_start_line_1:
            break

    marker: Optional[int] = None
    for line_no in range(prev_end + 1, function_start_line_1):
        if FOLDBENCH_MARKER in lines[line_no - 1]:
            marker = line_no
    return marker


def extract_function_snapshot(
    content: str,
    signature_line: str,
    fallback_decl_line: int,
    marker_hint_line: Optional[int],
) -> Dict[str, Any]:
    lines = content.splitlines()
    funcs = enumerate_functions_with_ranges(content)
    decl_line = (
        find_function_line_by_signature(content, signature_line) or fallback_decl_line
    )
    name, start, end, sig = find_containing_function(content, decl_line)

    marker_line: Optional[int] = None
    if (
        marker_hint_line is not None
        and 1 <= marker_hint_line <= len(lines)
        and marker_hint_line < start
        and FOLDBENCH_MARKER in lines[marker_hint_line - 1]
    ):
        marker_line = marker_hint_line
    if marker_line is None:
        marker_line = find_foldbench_marker_for_function(lines, funcs, start)

    snapshot_start = marker_line if marker_line is not None else start
    snippet_lines = lines[snapshot_start - 1 : end]
    snippet = "\n".join(snippet_lines)
    if content.endswith("\n"):
        snippet += "\n"

    return {
        "function_name": name,
        "function_signature_line": sig,
        "function_start_line": start,
        "function_end_line": end,
        "marker_line": marker_line,
        "snapshot_start_line": snapshot_start,
        "line_count": len(snippet_lines),
        "content": snippet,
    }


ANNOT_LINE_RE = re.compile(
    r"^\s*//\s*@\s*(?:ghost\s+)?(?:defer\s+fold|fold|unfold)\b", re.IGNORECASE
)


def remove_fold_related_annotations_from_function(
    content: str, function_start_line_1: int
) -> str:
    lines = content.splitlines()
    funcs = enumerate_functions_with_ranges(content)
    target = None
    for _, start, end, _ in funcs:
        if start == function_start_line_1:
            target = (start, end)
            break
    if target is None:
        return content
    start, end = target
    out: List[str] = []
    for i, line in enumerate(lines, start=1):
        if start <= i <= end and ANNOT_LINE_RE.match(line):
            continue
        out.append(line)
    return "\n".join(out) + ("\n" if content.endswith("\n") else "")


def get_verification_unit_input_files(script: ScriptSpec) -> List[Path]:
    tokens = script.tokens
    start = script.target_token_index
    files: List[Path] = []
    i = start
    while i < len(tokens):
        tok = tokens[i]
        if tok.startswith("-"):
            break
        if tok == TARGET_PLACEHOLDER:
            i += 1
            continue
        p = resolve_script_path(tok, script.path_base)
        if p.exists():
            files.append(p)
        i += 1
    return files


def get_include_roots_from_script(script: ScriptSpec) -> List[Path]:
    roots: List[Path] = []
    toks = script.tokens
    i = 0
    while i < len(toks):
        tok = toks[i]
        if tok != "-I":
            i += 1
            continue
        j = i + 1
        while j < len(toks) and not toks[j].startswith("-"):
            p = resolve_script_path(toks[j], script.path_base)
            if p.exists() and p.is_dir():
                roots.append(p)
            j += 1
        i = j
    # de-duplicate while preserving order
    out: List[Path] = []
    seen: set[Path] = set()
    for r in roots:
        if r in seen:
            continue
        seen.add(r)
        out.append(r)
    return out


def collect_go_gobra_files_under_roots(roots: Sequence[Path]) -> List[Path]:
    files: List[Path] = []
    for root in roots:
        if not root.exists() or not root.is_dir():
            continue
        for p in root.rglob("*"):
            if not p.is_file():
                continue
            if p.suffix not in (".go", ".gobra"):
                continue
            files.append(p.resolve())
    out: List[Path] = []
    seen: set[Path] = set()
    for f in files:
        if f in seen:
            continue
        seen.add(f)
        out.append(f)
    return out


def find_function_line_by_signature(content: str, signature_line: str) -> Optional[int]:
    norm = normalize_space(signature_line.strip())
    for i, line in enumerate(content.splitlines(), start=1):
        if normalize_space(line.strip()) == norm:
            return i
    return None


def strip_flag(tokens: Sequence[str], flag: str) -> List[str]:
    out: List[str] = []
    i = 0
    while i < len(tokens):
        t = tokens[i]
        if t == flag:
            i += 1
            continue
        if t.startswith(flag + "="):
            i += 1
            continue
        out.append(t)
        i += 1
    return out


def strip_flag_with_value(tokens: Sequence[str], flag: str) -> List[str]:
    out: List[str] = []
    i = 0
    while i < len(tokens):
        t = tokens[i]
        if t == flag:
            i += 2
            continue
        if t.startswith(flag + "="):
            i += 1
            continue
        out.append(t)
        i += 1
    return out


def build_attempt_command_tokens(
    base_tokens: Sequence[str],
    target_token_index: int,
    target_file: Path,
    line: int,
    args: argparse.Namespace,
    state_out: Path,
    graph_out: Path,
    path_out: Path,
) -> List[str]:
    tokens = list(base_tokens)
    tokens[target_token_index] = f"{str(target_file)}@{line}"

    drop_with_val = [
        "--tryFoldStateOut",
        "--tryFoldGraphOut",
        "--tryFoldPathOut",
        "--tryFoldCandidateMode",
        "--tryFoldGraphMode",
        "--tryFoldPathMaxDepth",
        "--tryFoldMaxChildrenPerFailure",
        "--tryFoldMaxConcreteCandidatesPerPath",
        "--mceMode",
        "--counterexample",
    ]
    drop_no_val = ["--tryFold"]

    for flag in drop_with_val:
        tokens = strip_flag_with_value(tokens, flag)
    for flag in drop_no_val:
        tokens = strip_flag(tokens, flag)

    tokens.append("--tryFold")
    tokens.append(f"--tryFoldCandidateMode={args.mode}")
    tokens.append(f"--tryFoldPathMaxDepth={args.path_max_depth}")
    tokens.append(f"--tryFoldMaxChildrenPerFailure={args.max_children_per_failure}")
    tokens.append(f"--tryFoldMaxConcreteCandidatesPerPath={args.max_concrete_per_path}")
    tokens.append(f"--tryFoldStateOut={state_out}")
    tokens.append(f"--tryFoldGraphOut={graph_out}")
    tokens.append(f"--tryFoldPathOut={path_out}")
    tokens.append(f"--mceMode={args.mce_mode}")
    if args.counterexample != "off":
        tokens.append(f"--counterexample={args.counterexample}")
    return tokens


def build_plain_gobra_command_tokens(
    base_tokens: Sequence[str],
    target_token_index: int,
    target_file: Path,
    line: int,
    args: argparse.Namespace,
) -> List[str]:
    tokens = list(base_tokens)
    tokens[target_token_index] = f"{str(target_file)}@{line}"

    drop_with_val = [
        "--tryFoldStateOut",
        "--tryFoldGraphOut",
        "--tryFoldPathOut",
        "--tryFoldCandidateMode",
        "--tryFoldGraphMode",
        "--tryFoldPathMaxDepth",
        "--tryFoldMaxChildrenPerFailure",
        "--tryFoldMaxConcreteCandidatesPerPath",
        "--counterexample",
        "--mceMode",
    ]
    drop_no_val = ["--tryFold"]

    for flag in drop_with_val:
        tokens = strip_flag_with_value(tokens, flag)
    for flag in drop_no_val:
        tokens = strip_flag(tokens, flag)

    tokens.append(f"--mceMode={args.mce_mode}")
    if args.counterexample != "off":
        tokens.append(f"--counterexample={args.counterexample}")
    return tokens


def run_command(
    tokens: Sequence[str], cwd: Path, timeout_sec: int
) -> Tuple[int, str, str]:
    proc = subprocess.run(
        list(tokens),
        cwd=str(cwd),
        capture_output=True,
        text=True,
        timeout=timeout_sec,
    )
    return proc.returncode, proc.stdout, proc.stderr


def kill_z3_processes(logger: logging.Logger) -> None:
    """
    Best-effort cleanup for stale Z3 processes between target tasks.
    pkill returns rc=1 when no process matched; this is not treated as an error.
    """
    try:
        proc = subprocess.run(
            ["pkill", "-f", r"(^|/)z3($| )"],
            capture_output=True,
            text=True,
            check=False,
        )
    except FileNotFoundError:
        logger.warning("z3 cleanup skipped: `pkill` command not found")
        return
    except Exception as exc:
        logger.warning("z3 cleanup skipped due to unexpected error: %s", exc)
        return

    stdout = proc.stdout.strip()
    stderr = proc.stderr.strip()
    if proc.returncode in (0, 1):
        # 0: killed one or more, 1: no matching process.
        # logger.info("z3 cleanup: pkill rc=%d", proc.returncode)
        if stdout:
            logger.debug("z3 cleanup stdout: %s", stdout)
        if stderr:
            logger.debug("z3 cleanup stderr: %s", stderr)
    else:
        logger.warning("z3 cleanup returned rc=%d", proc.returncode)
        if stdout:
            logger.warning("z3 cleanup stdout: %s", stdout)
        if stderr:
            logger.warning("z3 cleanup stderr: %s", stderr)


def load_json_if_exists(path: Path) -> Optional[Dict[str, Any]]:
    if not path.exists():
        return None
    try:
        with path.open("r", encoding="utf-8") as f:
            return json.load(f)
    except json.JSONDecodeError:
        return None


def detect_success(return_code: int, stdout: str, stderr: str) -> bool:
    if return_code != 0:
        return False
    combined = (stdout + "\n" + stderr).lower()
    if "has found 1 error" in combined:
        return False
    if "error at:" in combined:
        return False
    return True


def parse_first_error(path_json: Optional[Dict[str, Any]]) -> Dict[str, Any]:
    if not path_json:
        return {
            "error_id": None,
            "readable_message": None,
            "source_location": None,
        }
    return {
        "error_id": path_json.get("firstErrorId"),
        "readable_message": path_json.get("firstErrorReadableMessage"),
        "source_location": path_json.get("firstErrorSourceLocation"),
    }


def _safe_int(value: Any, default: int = 0) -> int:
    return value if isinstance(value, int) else default


def _top_counts(items: Dict[str, int], limit: int = 3) -> List[Tuple[str, int]]:
    return sorted(
        [(k, v) for k, v in items.items() if isinstance(v, int)],
        key=lambda kv: (-kv[1], kv[0]),
    )[:limit]


def summarize_candidate_generation(
    path_json: Optional[Dict[str, Any]],
) -> Dict[str, Any]:
    if not path_json:
        return {
            "candidate_mode": "ours",
            "cause": "path_report_missing",
            "raw": 0,
            "selected": 0,
            "gobra_success": 0,
            "gobra_fail": 0,
            "single_step": 0,
            "graph_path_count": 0,
            "selected_path_count": 0,
            "material_drops": 0,
            "top_drop_reasons": [],
            "top_backtranslation_failures": [],
        }

    candidate_mode = str(path_json.get("candidateMode") or "ours")
    raw = _safe_int(path_json.get("rawConcreteCandidateCount"))
    selected = _safe_int(path_json.get("selectedConcreteCandidateCount"))
    gobra_success = _safe_int(path_json.get("gobraCandidateSuccessCount"))
    gobra_fail = _safe_int(path_json.get("gobraCandidateFailureCount"))
    single_step = _safe_int(path_json.get("singleStepCandidateCount"))
    graph_path_count = _safe_int(
        path_json.get(
            "graphPathCount",
            path_json.get("oursPathCount", path_json.get("baselinePathCount")),
        )
    )
    selected_path_count = _safe_int(path_json.get("selectedPathCount"))
    failure_endpoints = path_json.get("failureEndpoints")

    material = path_json.get("materializationStats") or {}
    material_drops = _safe_int(material.get("totalDrops"))
    drop_counts = material.get("dropReasonCounts") or {}
    top_drop_reasons = _top_counts(
        drop_counts if isinstance(drop_counts, dict) else {}, limit=3
    )

    bt_fail_counts: Dict[str, int] = {}
    for entry in path_json.get("gobraCandidatesFailed", []):
        if not isinstance(entry, dict):
            continue
        reason = entry.get("reason")
        stage = entry.get("stage")
        key = str(reason) if reason else "unknown"
        if stage:
            key = f"{key} @ {stage}"
        bt_fail_counts[key] = bt_fail_counts.get(key, 0) + 1
    top_backtranslation_failures = _top_counts(bt_fail_counts, limit=3)

    if raw == 0 and material_drops > 0:
        cause = "materialization_failed"
    elif failure_endpoints is None:
        cause = "failure_endpoints_unavailable"
    elif candidate_mode == "ours" and graph_path_count == 0:
        cause = "no_graph_paths"
    elif candidate_mode == "ours" and selected_path_count == 0:
        cause = "all_paths_filtered"
    elif candidate_mode == "baseline" and raw == 0:
        cause = "no_local_candidates"
    elif selected == 0 and raw > 0:
        cause = "no_selected_sequences_after_dedup_or_planning"
    elif selected > 0 and gobra_success == 0:
        cause = "backtranslation_failed_or_filtered"
    elif gobra_success > 0:
        cause = "candidates_available"
    elif single_step > 0:
        cause = "fallback_candidates_available"
    else:
        cause = "unknown"

    return {
        "candidate_mode": candidate_mode,
        "cause": cause,
        "raw": raw,
        "selected": selected,
        "gobra_success": gobra_success,
        "gobra_fail": gobra_fail,
        "single_step": single_step,
        "graph_path_count": graph_path_count,
        "selected_path_count": selected_path_count,
        "material_drops": material_drops,
        "top_drop_reasons": top_drop_reasons,
        "top_backtranslation_failures": top_backtranslation_failures,
    }


def classify_missing_path_report_cause(
    return_code: int,
    stdout: str,
    stderr: str,
) -> str:
    combined = f"{stdout}\n{stderr}".lower()
    if return_code == -1 and "timed out" in combined:
        return "execution_timeout"
    if "jsondecodeerror" in combined:
        return "path_report_corrupted"
    parse_signals = (
        "no viable alternative",
        "syntax error",
        "mismatched input",
        "unknown identifier",
        "undeclared identifier",
    )
    if any(sig in combined for sig in parse_signals):
        return "candidate_caused_parse_or_type_error"
    if "gobra found" in combined and "error" in combined:
        return "verification_failed_before_path_export"
    return "path_report_missing"


def extract_candidates_from_tryfold_path(
    path_json: Optional[Dict[str, Any]],
    allow_single_step_fallback: bool = False,
) -> List[CandidatePatch]:
    if not path_json:
        return []

    selected = path_json.get("selectedConcreteCandidates", [])
    selected_by_id: Dict[int, Dict[str, Any]] = {}
    for i, entry in enumerate(selected):
        selected_by_id[i] = entry

    patches: List[CandidatePatch] = []
    seen: set[Tuple[int, Tuple[str, ...], Optional[str]]] = set()

    def make_lines(raw: Iterable[str]) -> List[str]:
        out: List[str] = []
        for line in raw:
            s = line.rstrip()
            if not s:
                continue
            out.append(s)
        return out

    # Preferred: Gobra-level successful backtranslation candidates.
    for entry in path_json.get("gobraCandidatesSucceeded", []):
        cid_raw = entry.get("candidateId")
        if not isinstance(cid_raw, int):
            continue
        selected_entry = selected_by_id.get(cid_raw, {})
        target = selected_entry.get("insertionTarget", {}) or {}
        line = target.get("insertBeforeLine")
        if not isinstance(line, int):
            continue
        target_file = target.get("targetFile")
        lines = make_lines(
            entry.get("annotationLinesWithPrefix", [])
            or entry.get("annotationLines", [])
        )
        if not lines:
            continue
        key = (line, tuple(lines), target_file)
        if key in seen:
            continue
        seen.add(key)
        patches.append(
            CandidatePatch(
                candidate_id=cid_raw,
                insertion_line=line,
                insertion_column=target.get("insertBeforeColumn"),
                insertion_file=Path(target_file).resolve() if target_file else None,
                annotation_lines=lines,
                source="gobraCandidatesSucceeded",
                metadata={
                    "directiveCount": entry.get("directiveCount"),
                    "selectedConcreteCandidate": selected_entry,
                },
            )
        )

    # Optional fallback: single-step candidates (best-effort rendering).
    if allow_single_step_fallback and not patches:
        for entry in path_json.get("singleStepCandidates", []):
            cid_raw = entry.get("candidateId")
            if not isinstance(cid_raw, int):
                continue
            target = entry.get("insertionTarget", {}) or {}
            line = target.get("insertBeforeLine")
            if not isinstance(line, int):
                continue
            target_file = target.get("targetFile")
            lines = make_lines(
                entry.get("annotationLinesWithPrefix", [])
                or entry.get("annotationLines", [])
            )
            if not lines:
                continue
            key = (line, tuple(lines), target_file)
            if key in seen:
                continue
            seen.add(key)
            patches.append(
                CandidatePatch(
                    candidate_id=cid_raw,
                    insertion_line=line,
                    insertion_column=target.get("insertBeforeColumn"),
                    insertion_file=Path(target_file).resolve() if target_file else None,
                    annotation_lines=lines,
                    source="singleStepCandidates",
                    metadata={},
                )
            )

    return patches


def normalize_annotation_line(line: str) -> str:
    s = line.strip()
    if s.startswith("//@") or s.startswith("// @"):
        return s.replace("// @", "//@", 1)
    if s.startswith("@"):
        return "//" + s
    return f"//@ {s}"


def detect_indent_for_insert(lines: Sequence[str], idx0: int) -> str:
    if 0 <= idx0 < len(lines):
        probe = lines[idx0]
    elif lines:
        probe = lines[-1]
    else:
        return ""
    m = re.match(r"^\s*", probe)
    return m.group(0) if m else ""


def _annotation_payload(line: str) -> Optional[str]:
    stripped = line.lstrip()
    if stripped.startswith("//@"):
        return stripped[3:].lstrip()
    if stripped.startswith("// @"):
        return stripped[4:].lstrip()
    return None


def _annotation_balance_delta(payload: str) -> int:
    depth = 0
    in_single = False
    in_double = False
    in_backtick = False
    escaped = False
    for ch in payload:
        if escaped:
            escaped = False
            continue
        if (in_single or in_double) and ch == "\\":
            escaped = True
            continue
        if in_backtick:
            if ch == "`":
                in_backtick = False
            continue
        if in_single:
            if ch == "'":
                in_single = False
            continue
        if in_double:
            if ch == '"':
                in_double = False
            continue
        if ch == "`":
            in_backtick = True
            continue
        if ch == "'":
            in_single = True
            continue
        if ch == '"':
            in_double = True
            continue
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
    return depth


_ANNOTATION_CONTINUATION_SUFFIX = re.compile(
    r"(==|!=|<=|>=|&&|\|\||[+\-*/%&|^,.:=<>])\s*$"
)


def _annotation_continues(payload: str) -> bool:
    text = payload.rstrip()
    if not text:
        return False
    if _annotation_balance_delta(text) > 0:
        return True
    return bool(_ANNOTATION_CONTINUATION_SUFFIX.search(text))


def _adjust_insertion_index_for_annotation_blocks(
    lines: Sequence[str], idx: int
) -> int:
    if idx <= 0 or idx >= len(lines):
        return idx
    prev_payload = _annotation_payload(lines[idx - 1])
    if prev_payload is None:
        return idx

    start = idx - 1
    while start > 0:
        upper_payload = _annotation_payload(lines[start - 1])
        if upper_payload is None:
            break
        if not _annotation_continues(upper_payload):
            break
        start -= 1

    end = start + 1
    while end < len(lines):
        cur_payload = _annotation_payload(lines[end - 1])
        if cur_payload is None or not _annotation_continues(cur_payload):
            break
        next_payload = _annotation_payload(lines[end])
        if next_payload is None:
            break
        end += 1

    if start < idx < end:
        return start
    return idx


def apply_candidate_patch(content: str, patch: CandidatePatch) -> str:
    lines = content.splitlines()
    idx = patch.insertion_line - 1
    if idx < 0:
        idx = 0
    if idx > len(lines):
        idx = len(lines)
    idx = _adjust_insertion_index_for_annotation_blocks(lines, idx)

    indent = detect_indent_for_insert(lines, idx if idx < len(lines) else idx - 1)
    inserted: List[str] = [
        indent + normalize_annotation_line(line) for line in patch.annotation_lines
    ]
    out = lines[:idx] + inserted + lines[idx:]

    trailing_newline = content.endswith("\n")
    joined = "\n".join(out)
    if trailing_newline:
        joined += "\n"
    return joined


def sanitize_name(name: str) -> str:
    return re.sub(r"[^A-Za-z0-9._-]+", "_", name)


def select_task_for_target_from_exp_list(
    target: str, scripts_by_file: Dict[Path, ScriptSpec]
) -> FunctionTask:
    if "@" not in target:
        raise ValueError("--target must be '/abs/path/file.go@line'.")
    file_part, line_part = target.rsplit("@", 1)
    if not line_part.isdigit():
        raise ValueError("--target line must be numeric.")
    target_file = Path(file_part).resolve()
    target_line = int(line_part)
    if target_file not in scripts_by_file:
        raise ValueError(f"No exp-list script found for target file: {target_file}")

    content = read_text(target_file)
    func_name, func_start, _, sig = find_containing_function(content, target_line)
    task_id = sanitize_name(f"{target_file.name}_{func_name}_{func_start}")
    return FunctionTask(
        task_id=task_id,
        script_name=scripts_by_file[target_file].name,
        target_file=target_file,
        function_name=func_name,
        function_decl_line=func_start,
        function_signature_line=sig,
        marker_line=None,
    )


def select_task_for_target_from_config(target: str, script: ScriptSpec) -> FunctionTask:
    if "@" not in target:
        raise ValueError("--target must be '/abs/path/file.go@line'.")
    file_part, line_part = target.rsplit("@", 1)
    if not line_part.isdigit():
        raise ValueError("--target line must be numeric.")
    target_file = Path(file_part).resolve()
    target_line = int(line_part)

    content = read_text(target_file)
    func_name, func_start, _, sig = find_containing_function(content, target_line)
    task_id = sanitize_name(f"{target_file.name}_{func_name}_{func_start}")
    return FunctionTask(
        task_id=task_id,
        script_name=script.name,
        target_file=target_file,
        function_name=func_name,
        function_decl_line=func_start,
        function_signature_line=sig,
        marker_line=None,
    )


def select_tasks_all_foldbench(scripts: Sequence[ScriptSpec]) -> List[FunctionTask]:
    tasks: List[FunctionTask] = []
    for script in scripts:
        if script.target_file is None:
            continue
        if not script.target_file.exists():
            continue
        entries = find_foldbench_functions(script.target_file)
        for func_name, start, _, sig, marker in entries:
            task_id = sanitize_name(f"{script.target_file.name}_{func_name}_{start}")
            tasks.append(
                FunctionTask(
                    task_id=task_id,
                    script_name=script.name,
                    target_file=script.target_file,
                    function_name=func_name,
                    function_decl_line=start,
                    function_signature_line=sig,
                    marker_line=marker,
                )
            )
    # Preserve experiment-list order.
    # - scripts are iterated in exp-list block order
    # - functions are emitted in in-file FOLDBENCH marker order
    # This keeps execution order aligned with the user's exp_list file.
    return tasks


def select_tasks_smoke_run(
    scripts: Sequence[ScriptSpec],
    workspace_root: Path,
    smoke_file: Optional[Path],
    max_functions: int,
) -> List[FunctionTask]:
    tasks = select_tasks_all_foldbench(scripts)
    if smoke_file is not None:
        file_path = smoke_file if smoke_file.is_absolute() else (workspace_root / smoke_file)
        smoke_target = file_path.resolve()
        tasks = [task for task in tasks if task.target_file.resolve() == smoke_target]
    return tasks[:max_functions]


def build_session_dir(output_root: Path) -> Path:
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    session_dir = output_root / f"session_{ts}"
    ensure_dir(session_dir)
    return session_dir


def run_one_task(
    task: FunctionTask,
    script: ScriptSpec,
    args: argparse.Namespace,
    workspace_root: Path,
    session_dir: Path,
    logger: logging.Logger,
) -> Dict[str, Any]:
    task_dir = session_dir / task.task_id
    ensure_dir(task_dir)

    logger.info(
        "[%s] start: %s:%d (%s)",
        task.task_id,
        task.target_file,
        task.function_decl_line,
        task.function_name,
    )

    original_content = read_text(task.target_file)
    write_text(task_dir / "original.go.snapshot", original_content)

    stripped_content = remove_fold_related_annotations_from_function(
        original_content, task.function_decl_line
    )
    write_text(task_dir / "initial_stripped.go.snapshot", stripped_content)
    function_snapshots_dir = task_dir / "function_snapshots"
    ensure_dir(function_snapshots_dir)

    next_state_id = 1
    root_item = WorkItem(
        state_id=0,
        parent_state_id=None,
        depth=0,
        content=stripped_content,
        fingerprint=hash_content(stripped_content),
        producer=None,
    )
    queue: Deque[WorkItem] = deque([root_item])
    seen: set[str] = {root_item.fingerprint}

    attempts: List[Dict[str, Any]] = []
    status = "failed"
    success_state_id: Optional[int] = None
    success_attempt: Optional[int] = None
    successful_content: Optional[str] = None
    target_file_final_state = "restored_original"

    try:
        for attempt_no in range(1, args.max_attempts + 1):
            if args.kill_z3_on_task_start:
                # logger.info("[%s] running z3 cleanup before task start", task.task_id)
                kill_z3_processes(logger)

            if not queue:
                logger.info(
                    "[%s] queue exhausted at attempt %d", task.task_id, attempt_no
                )
                break

            item = queue.popleft()
            attempt_dir = task_dir / f"attempt_{attempt_no:04d}_state_{item.state_id}"
            ensure_dir(attempt_dir)

            write_text(task.target_file, item.content)
            write_text(attempt_dir / "state_input.go.snapshot", item.content)

            current_line = find_function_line_by_signature(
                item.content, task.function_signature_line
            )
            if current_line is None:
                current_line = task.function_decl_line

            function_snapshot = extract_function_snapshot(
                content=item.content,
                signature_line=task.function_signature_line,
                fallback_decl_line=task.function_decl_line,
                marker_hint_line=task.marker_line,
            )
            function_snapshot_path = (
                function_snapshots_dir
                / f"attempt_{attempt_no:04d}_state_{item.state_id}_{sanitize_name(task.function_name)}.go.snapshot"
            )
            write_text(function_snapshot_path, function_snapshot["content"])
            json_dump(attempt_dir / "function_snapshot_meta.json", function_snapshot)

            state_json = attempt_dir / "tryfold_state.json"
            graph_json = attempt_dir / "tryfold_graph.json"
            path_json = attempt_dir / "tryfold_path.json"

            cmd_tokens = build_attempt_command_tokens(
                base_tokens=script.tokens,
                target_token_index=script.target_token_index,
                target_file=task.target_file,
                line=current_line,
                args=args,
                state_out=state_json,
                graph_out=graph_json,
                path_out=path_json,
            )
            cmd_line = " ".join(shlex.quote(tok) for tok in cmd_tokens)
            write_text(attempt_dir / "cmd.txt", cmd_line + "\n")

            logger.info(
                "[%s] attempt %d/%d: state=%d depth=%d queue=%d line=%d",
                task.task_id,
                attempt_no,
                args.max_attempts,
                item.state_id,
                item.depth,
                len(queue),
                current_line,
            )

            try:
                rc, stdout, stderr = run_command(
                    cmd_tokens, cwd=workspace_root, timeout_sec=args.timeout_sec
                )
            except subprocess.TimeoutExpired:
                rc, stdout, stderr = -1, "", f"Timed out after {args.timeout_sec}s."
            except Exception as exc:
                rc, stdout, stderr = (
                    -1,
                    "",
                    f"Execution failed: {exc}\n{traceback.format_exc()}",
                )

            write_text(attempt_dir / "stdout.log", stdout)
            write_text(attempt_dir / "stderr.log", stderr)

            path_report = load_json_if_exists(path_json)
            state_report = load_json_if_exists(state_json)
            graph_report = load_json_if_exists(graph_json)
            first_error = parse_first_error(path_report)

            is_success = detect_success(rc, stdout, stderr)
            attempt_record: Dict[str, Any] = {
                "attempt": attempt_no,
                "state_id": item.state_id,
                "parent_state_id": item.parent_state_id,
                "depth": item.depth,
                "fingerprint": item.fingerprint,
                "return_code": rc,
                "success": is_success,
                "current_line_marker": current_line,
                "function_snapshot_path": str(function_snapshot_path),
                "function_snapshot_start_line": function_snapshot.get(
                    "snapshot_start_line"
                ),
                "function_snapshot_end_line": function_snapshot.get(
                    "function_end_line"
                ),
                "function_snapshot_marker_line": function_snapshot.get("marker_line"),
                "first_error": first_error,
                "candidate_count": 0,
                "children_enqueued": [],
                "queue_size_after": None,
            }

            if is_success:
                status = "success"
                success_state_id = item.state_id
                success_attempt = attempt_no
                successful_content = item.content
                attempts.append(attempt_record)
                logger.info(
                    "[%s] success at attempt %d (state=%d)",
                    task.task_id,
                    attempt_no,
                    item.state_id,
                )
                break

            candidates = extract_candidates_from_tryfold_path(path_report)
            attempt_record["candidate_count"] = len(candidates)
            generation_summary = summarize_candidate_generation(path_report)
            if path_report is None:
                generation_summary["cause"] = classify_missing_path_report_cause(
                    return_code=rc,
                    stdout=stdout,
                    stderr=stderr,
                )
            attempt_record["candidate_generation_summary"] = generation_summary
            if not candidates:
                logger.info(
                    "[%s] attempt %d produced no candidates: mode=%s cause=%s graph_paths=%d selected_paths=%d raw=%d selected=%d gobra_success=%d gobra_fail=%d single_step=%d material_drops=%d top_drop_reasons=%s top_backtranslation_failures=%s",
                    task.task_id,
                    attempt_no,
                    generation_summary.get("candidate_mode", "ours"),
                    generation_summary.get("cause", "unknown"),
                    generation_summary.get("graph_path_count", 0),
                    generation_summary.get("selected_path_count", 0),
                    generation_summary.get("raw", 0),
                    generation_summary.get("selected", 0),
                    generation_summary.get("gobra_success", 0),
                    generation_summary.get("gobra_fail", 0),
                    generation_summary.get("single_step", 0),
                    generation_summary.get("material_drops", 0),
                    generation_summary.get("top_drop_reasons", []),
                    generation_summary.get("top_backtranslation_failures", []),
                )
            child_infos: List[Dict[str, Any]] = []
            for cand in candidates:
                if (
                    cand.insertion_file
                    and cand.insertion_file.resolve() != task.target_file.resolve()
                ):
                    child_infos.append(
                        {
                            "candidate_id": cand.candidate_id,
                            "enqueued": False,
                            "reason": "insertion_target_file_mismatch",
                            "target_file": str(cand.insertion_file),
                        }
                    )
                    continue
                try:
                    child_content = apply_candidate_patch(item.content, cand)
                except Exception as exc:
                    child_infos.append(
                        {
                            "candidate_id": cand.candidate_id,
                            "enqueued": False,
                            "reason": f"apply_failed: {exc}",
                        }
                    )
                    continue
                child_fp = hash_content(child_content)
                if child_fp in seen:
                    child_infos.append(
                        {
                            "candidate_id": cand.candidate_id,
                            "enqueued": False,
                            "reason": "duplicate_state",
                        }
                    )
                    continue
                seen.add(child_fp)
                child = WorkItem(
                    state_id=next_state_id,
                    parent_state_id=item.state_id,
                    depth=item.depth + 1,
                    content=child_content,
                    fingerprint=child_fp,
                    producer={
                        "attempt": attempt_no,
                        "candidate_id": cand.candidate_id,
                        "source": cand.source,
                        "insertion_line": cand.insertion_line,
                        "annotation_lines": cand.annotation_lines,
                    },
                )
                next_state_id += 1
                queue.append(child)
                child_info = {
                    "candidate_id": cand.candidate_id,
                    "enqueued": True,
                    "child_state_id": child.state_id,
                    "fingerprint": child_fp,
                    "source": cand.source,
                    "insertion_line": cand.insertion_line,
                    "annotation_lines": cand.annotation_lines,
                }
                child_infos.append(child_info)
                attempt_record["children_enqueued"].append(child_info)

                if args.keep_temp_states:
                    write_text(
                        attempt_dir
                        / f"child_{child.state_id:04d}_from_candidate_{cand.candidate_id}.go.snapshot",
                        child_content,
                    )

            attempt_record["queue_size_after"] = len(queue)
            attempts.append(attempt_record)

            debug_summary = {
                "attempt_record": attempt_record,
                "path_report_present": path_report is not None,
                "state_report_present": state_report is not None,
                "graph_report_present": graph_report is not None,
                "candidate_debug": [asdict(c) for c in candidates],
                "child_infos": child_infos,
            }
            json_dump(attempt_dir / "attempt_debug.json", debug_summary)

        if status != "success":
            logger.info(
                "[%s] failed (attempt budget reached or queue exhausted)", task.task_id
            )

    finally:
        if (
            should_preserve_successful_target(args)
            and status == "success"
            and successful_content is not None
        ):
            write_text(task.target_file, successful_content)
            target_file_final_state = "preserved_success"
            logger.info("[%s] preserved successful file state", task.task_id)
        else:
            write_text(task.target_file, original_content)
            logger.info("[%s] restored original file", task.task_id)

    summary = {
        "task_id": task.task_id,
        "script_name": task.script_name,
        "target_file": str(task.target_file),
        "function_name": task.function_name,
        "function_decl_line": task.function_decl_line,
        "status": status,
        "success_attempt": success_attempt,
        "success_state_id": success_state_id,
        "attempt_count": len(attempts),
        "max_attempts": args.max_attempts,
        "target_file_final_state": target_file_final_state,
        "preserved_successful_target_state": (
            target_file_final_state == "preserved_success"
        ),
        "attempts": attempts,
    }
    json_dump(task_dir / "task_summary.json", summary)
    return summary


def main() -> int:
    args = parse_args()
    workspace_root = Path(__file__).resolve().parents[1]
    session_dir = build_session_dir(args.output_root.resolve())
    logger = setup_logger(session_dir)
    script_source = "exp_list" if args.exp_list is not None else "config"
    script_source_path = (
        args.exp_list.resolve() if args.exp_list is not None else args.gobra_config.resolve()
    )

    logger.info("session dir: %s", session_dir)
    logger.info(
        "config: scriptSource=%s mode=%s maxAttempts=%d pathMaxDepth=%d maxChildren=%d maxConcrete=%d mce=%s counterexample=%s killZ3OnTaskStart=%s timeout=%ds smokeRun=%s smokeFile=%s smokeMaxFunctions=%d",
        script_source,
        args.mode,
        args.max_attempts,
        args.path_max_depth,
        args.max_children_per_failure,
        args.max_concrete_per_path,
        args.mce_mode,
        args.counterexample,
        args.kill_z3_on_task_start,
        args.timeout_sec,
        args.smoke_run,
        str(args.smoke_file) if args.smoke_file is not None else None,
        args.smoke_max_functions,
    )

    scripts_by_file: Dict[Path, ScriptSpec] = {}
    config_script: Optional[ScriptSpec] = None
    if args.exp_list is not None:
        try:
            scripts = parse_scripts(args.exp_list.resolve(), workspace_root)
        except Exception as exc:
            logger.error("failed to parse exp-list: %s", exc)
            return 2
        scripts_by_file = map_scripts_by_target(scripts)
    else:
        try:
            config_script = load_config_script(args.gobra_config.resolve(), workspace_root)
            scripts = [config_script]
        except Exception as exc:
            logger.error("failed to load gobra config: %s", exc)
            return 2

    if args.target:
        try:
            if args.exp_list is not None:
                tasks = [select_task_for_target_from_exp_list(args.target, scripts_by_file)]
            else:
                assert config_script is not None
                tasks = [select_task_for_target_from_config(args.target, config_script)]
        except Exception as exc:
            logger.error("invalid target: %s", exc)
            return 2
    elif args.smoke_run:
        tasks = select_tasks_smoke_run(
            scripts,
            workspace_root,
            args.smoke_file,
            args.smoke_max_functions,
        )
        if not tasks:
            logger.error("no smoke-run functions found.")
            return 2
    else:
        tasks = select_tasks_all_foldbench(scripts)
        if not tasks:
            logger.error("no FOLDBENCH functions found.")
            return 2

    json_dump(
        session_dir / "session_config.json",
        {
            "workspace_root": str(workspace_root),
            "script_source": script_source,
            "script_source_path": str(script_source_path),
            "exp_list": str(args.exp_list.resolve()) if args.exp_list is not None else None,
            "gobra_config": (
                str(args.gobra_config.resolve()) if args.gobra_config is not None else None
            ),
            "target": args.target,
            "all_foldbench": args.all_foldbench,
            "smoke_run": args.smoke_run,
            "smoke_file": str(args.smoke_file.resolve()) if args.smoke_file is not None else None,
            "smoke_max_functions": args.smoke_max_functions,
            "mode": args.mode,
            "max_attempts": args.max_attempts,
            "path_max_depth": args.path_max_depth,
            "max_children_per_failure": args.max_children_per_failure,
            "max_concrete_per_path": args.max_concrete_per_path,
            "mce_mode": args.mce_mode,
            "counterexample": args.counterexample,
            "kill_z3_on_task_start": args.kill_z3_on_task_start,
            "timeout_sec": args.timeout_sec,
            "task_count": len(tasks),
            "tasks": [asdict(t) for t in tasks],
        },
    )

    logger.info("selected tasks: %d", len(tasks))
    for t in tasks:
        logger.info(
            "  - %s: %s:%d (%s)",
            t.task_id,
            t.target_file,
            t.function_decl_line,
            t.function_name,
        )

    summaries: List[Dict[str, Any]] = []
    for task in tasks:
        if args.exp_list is not None:
            script = scripts_by_file.get(task.target_file.resolve())
            if script is None:
                logger.error(
                    "[%s] no script mapping found for %s", task.task_id, task.target_file
                )
                summaries.append(
                    {
                        "task_id": task.task_id,
                        "status": "error",
                        "error": f"missing script for {task.target_file}",
                    }
                )
                continue
        else:
            assert config_script is not None
            script = config_script
        if args.kill_z3_on_task_start:
            # logger.info("[%s] running z3 cleanup before task start", task.task_id)
            kill_z3_processes(logger)
        try:
            summary = run_one_task(
                task=task,
                script=script,
                args=args,
                workspace_root=workspace_root,
                session_dir=session_dir,
                logger=logger,
            )
            summaries.append(summary)
        except Exception as exc:
            logger.error("[%s] task crashed: %s", task.task_id, exc)
            logger.debug(traceback.format_exc())
            summaries.append(
                {
                    "task_id": task.task_id,
                    "status": "error",
                    "error": str(exc),
                }
            )

    success_count = sum(1 for s in summaries if s.get("status") == "success")
    fail_count = sum(1 for s in summaries if s.get("status") == "failed")
    error_count = sum(1 for s in summaries if s.get("status") == "error")

    final_summary = {
        "session_dir": str(session_dir),
        "task_count": len(summaries),
        "success_count": success_count,
        "failed_count": fail_count,
        "error_count": error_count,
        "results": summaries,
    }
    json_dump(session_dir / "session_summary.json", final_summary)

    logger.info(
        "done: success=%d failed=%d error=%d (total=%d)",
        success_count,
        fail_count,
        error_count,
        len(summaries),
    )
    logger.info("session summary: %s", session_dir / "session_summary.json")

    return 0 if error_count == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
