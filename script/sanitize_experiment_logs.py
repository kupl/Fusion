#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import shutil
import tarfile
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


HOME_PATH_RE = re.compile(r"/home/[^/\s\"']+")
MAC_HOME_PATH_RE = re.compile(r"/Users/[^/\s\"']+")


@dataclass(frozen=True)
class SanitizeStats:
    files_copied: int = 0
    text_files_rewritten: int = 0
    binary_files_copied: int = 0
    files_skipped: int = 0


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Copy an experiment session directory and sanitize absolute paths / "
            "user-specific information for artifact submission."
        )
    )
    parser.add_argument(
        "session_dir",
        type=Path,
        help="Path to the original experiment session directory.",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=None,
        help=(
            "Destination directory for the sanitized copy. "
            "Defaults to output/sanitized_experiments/<session-name>."
        ),
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="Repository root used for replacing absolute repo paths.",
    )
    parser.add_argument(
        "--repo-placeholder",
        default="<REPO_ROOT>",
        help="Placeholder used when rewriting absolute repository paths.",
    )
    parser.add_argument(
        "--overwrite",
        action="store_true",
        help="Overwrite the destination if it already exists.",
    )
    return parser.parse_args()


def default_output_dir(session_dir: Path) -> Path:
    return session_dir.parent.parent / "sanitized_experiments" / session_dir.name


def sanitize_text(text: str, repo_root: Path, repo_placeholder: str) -> str:
    repo_root_str = str(repo_root.resolve())
    text = text.replace(repo_root_str, repo_placeholder)
    text = HOME_PATH_RE.sub("/home/<USER>", text)
    text = MAC_HOME_PATH_RE.sub("/Users/<USER>", text)
    return text


def try_read_text(path: Path) -> str | None:
    try:
        return path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return None


def iter_files(root: Path) -> Iterable[Path]:
    for path in sorted(root.rglob("*")):
        if path.is_file():
            yield path


def should_keep_file(rel: Path) -> bool:
    name = rel.name
    if name in {"run.log", "session_config.json", "session_summary.json", "task_summary.json"}:
        return True
    if name in {"original.go.snapshot", "initial_stripped.go.snapshot"}:
        return True
    if "function_snapshots" in rel.parts and name.endswith(".go.snapshot"):
        return True
    return False


def sanitize_session(
    session_dir: Path, output_dir: Path, repo_root: Path, repo_placeholder: str
) -> SanitizeStats:
    stats = SanitizeStats()
    output_dir.mkdir(parents=True, exist_ok=True)
    for src in iter_files(session_dir):
        rel = src.relative_to(session_dir)
        if not should_keep_file(rel):
            stats = SanitizeStats(
                files_copied=stats.files_copied,
                text_files_rewritten=stats.text_files_rewritten,
                binary_files_copied=stats.binary_files_copied,
                files_skipped=stats.files_skipped + 1,
            )
            continue
        dst = output_dir / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        text = try_read_text(src)
        if text is None:
            shutil.copy2(src, dst)
            stats = SanitizeStats(
                files_copied=stats.files_copied + 1,
                text_files_rewritten=stats.text_files_rewritten,
                binary_files_copied=stats.binary_files_copied + 1,
                files_skipped=stats.files_skipped,
            )
            continue
        sanitized = sanitize_text(text, repo_root=repo_root, repo_placeholder=repo_placeholder)
        dst.write_text(sanitized, encoding="utf-8")
        stats = SanitizeStats(
            files_copied=stats.files_copied + 1,
            text_files_rewritten=stats.text_files_rewritten + 1,
            binary_files_copied=stats.binary_files_copied,
            files_skipped=stats.files_skipped,
        )
    return stats


def write_manifest(
    output_dir: Path, session_dir: Path, repo_root: Path, repo_placeholder: str, stats: SanitizeStats
) -> None:
    source_session = sanitize_text(str(session_dir.resolve()), repo_root, repo_placeholder)
    sanitized_session = sanitize_text(str(output_dir.resolve()), repo_root, repo_placeholder)
    manifest = {
        "source_session_dir": source_session,
        "sanitized_session_dir": sanitized_session,
        "repo_root_placeholder": repo_placeholder,
        "files_copied": stats.files_copied,
        "text_files_rewritten": stats.text_files_rewritten,
        "binary_files_copied": stats.binary_files_copied,
        "files_skipped": stats.files_skipped,
        "kept_file_kinds": [
            "run.log",
            "session_config.json",
            "session_summary.json",
            "task_summary.json",
            "original.go.snapshot",
            "initial_stripped.go.snapshot",
            "function_snapshots/*.go.snapshot",
        ],
    }
    (output_dir / "sanitize_manifest.json").write_text(json.dumps(manifest, indent=2), encoding="utf-8")


def create_archive(output_dir: Path) -> Path:
    archive_path = output_dir.with_suffix(".tar.gz")
    if archive_path.exists():
        archive_path.unlink()
    with tarfile.open(archive_path, "w:gz") as tar:
        tar.add(output_dir, arcname=output_dir.name)
    return archive_path


def main() -> None:
    args = parse_args()
    session_dir = args.session_dir.resolve()
    if not session_dir.is_dir():
        raise SystemExit(f"Session directory does not exist: {session_dir}")
    repo_root = args.repo_root.resolve()
    output_dir = args.output_dir.resolve() if args.output_dir else default_output_dir(session_dir).resolve()
    if output_dir.exists():
        if not args.overwrite:
            raise SystemExit(f"Output directory already exists: {output_dir}")
        shutil.rmtree(output_dir)
    stats = sanitize_session(
        session_dir=session_dir,
        output_dir=output_dir,
        repo_root=repo_root,
        repo_placeholder=args.repo_placeholder,
    )
    write_manifest(
        output_dir=output_dir,
        session_dir=session_dir,
        repo_root=repo_root,
        repo_placeholder=args.repo_placeholder,
        stats=stats,
    )
    archive_path = create_archive(output_dir)
    print(f"Sanitized session copied to: {output_dir}")
    print(f"Archive created at: {archive_path}")
    print(f"Files copied: {stats.files_copied}")
    print(f"Text files rewritten: {stats.text_files_rewritten}")
    print(f"Binary files copied unchanged: {stats.binary_files_copied}")
    print(f"Files skipped: {stats.files_skipped}")


if __name__ == "__main__":
    main()
