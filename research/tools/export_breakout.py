#!/usr/bin/env python3
"""Inspect or export minimal transitive OddPerfect.* Lean closures for standalone breakouts."""

from __future__ import annotations

import argparse
import re
import shutil
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
IMPORT_RE = re.compile(r"^(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(\S+)\s*$")
EXTERNAL_PREFIXES = {"Mathlib", "Archive", "Lean", "Std", "Init"}
CERT_PATTERNS = (".Part", ".Primes", ".Seed", "SizeIndex", "SizePrimeBank", "DeficientReplay")


def direct_local_imports(path: Path) -> list[str]:
    imports: list[str] = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.partition("--")[0].strip()
        match = IMPORT_RE.fullmatch(line)
        if not match:
            continue
        mod = match.group(1)
        if mod.split(".")[0] not in EXTERNAL_PREFIXES:
            imports.append(mod)
    return imports


def transitive_closure(roots: list[str], source_root: Path = REPO) -> dict[str, Path]:
    seen: dict[str, Path] = {}
    pending = list(roots)
    while pending:
        mod = pending.pop()
        if mod in seen:
            continue
        rel = Path(*mod.split(".")).with_suffix(".lean")
        src = source_root / rel
        if not src.exists():
            raise FileNotFoundError(f"Missing module {mod} at {src}")
        seen[mod] = rel
        for imp in direct_local_imports(src):
            pending.append(imp)
    return dict(sorted(seen.items()))


def is_cert_chunk(mod: str) -> bool:
    return any(pat in mod for pat in CERT_PATTERNS)


def write_scaffold(output: Path, pkg_name: str, entry_targets: list[str], closure: dict[str, Path]) -> None:
    output.mkdir(parents=True, exist_ok=True)
    for rel in closure.values():
        dst = output / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(REPO / rel, dst)

    for fixed in ("lean-toolchain", "lake-manifest.json"):
        shutil.copy2(REPO / fixed, output / fixed)

    (output / ".gitignore").write_text(
        "/.lake/\n**/__pycache__/\n*.aux\n*.log\n*.out\n*.toc\n*.synctex.gz\n",
        encoding="utf-8",
    )

    targets_toml = ", ".join(f'"{t}"' for t in entry_targets)
    libs_toml = "\n".join(f'[[lean_lib]]\nname = "{t}"\n' for t in entry_targets)
    lakefile = f'''name = "{pkg_name}"
version = "0.1.0"
defaultTargets = [{targets_toml}]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "fc4f59e577feb1a4956671bc04ac18aaaf8cd842"

[[lean_lib]]
name = "OddPerfect"
globs = ["OddPerfect.+"]

{libs_toml}'''
    (output / "lakefile.toml").write_text(lakefile, encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--roots", nargs="+", required=True, help="Root OddPerfect.* module names")
    parser.add_argument("--output", type=Path, help="Destination breakout directory")
    parser.add_argument("--pkg-name", default="breakout_pkg", help="Lake package name")
    parser.add_argument("--entry-targets", nargs="+", default=["MainTheorem"], help="Top-level Lean lib targets")
    parser.add_argument("--dry-run", action="store_true", help="Only print closure statistics and bloat sources")
    args = parser.parse_args()

    closure = transitive_closure(args.roots)
    certs = [m for m in closure if is_cert_chunk(m)]
    structural = [m for m in closure if not is_cert_chunk(m)]

    print(f"Total modules: {len(closure)} ({len(structural)} structural, {len(certs)} cert/bank chunks)")
    if certs:
        # Report which structural modules directly pull in cert/umbrella modules
        print("Modules importing umbrella/cert dependencies:")
        for m in structural:
            imps = direct_local_imports(REPO / closure[m])
            bad = [i for i in imps if is_cert_chunk(i) or "GlobalWave" in i or i in {"OddPerfect.SizeBound300", "OddPerfect.DeficientFourClassification"}]
            if bad:
                print(f"  {m} -> {bad}")

    if args.dry_run or not args.output:
        return

    write_scaffold(args.output, args.pkg_name, args.entry_targets, closure)
    print(f"Exported {len(closure)} modules to {args.output}")


if __name__ == "__main__":
    main()
