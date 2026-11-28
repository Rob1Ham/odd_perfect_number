#!/usr/bin/env python3
"""Validate the headline-theorem registry and regenerate research/CLAIMS.md.

Checks for every entry of research/claims_registry.json:
  * the declaration `theorem|lemma|def <name>` exists in the stated module file;
  * the module is reachable from OddPerfect.lean (i.e. covered by research/Audit.lean);
  * the branch id exists in the machine-readable block of research/BRANCH_MAP.md.

Usage:
  python3 research/tools/claims.py            # validate + write research/CLAIMS.md
  python3 research/tools/claims.py --check    # validate only (exit 1 on any problem)
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys
from collections import deque

REPO_ROOT = pathlib.Path(__file__).resolve().parents[2]
REGISTRY = REPO_ROOT / "research" / "claims_registry.json"
CLAIMS_MD = REPO_ROOT / "research" / "CLAIMS.md"
BRANCH_MAP = REPO_ROOT / "research" / "BRANCH_MAP.md"
ROOT_LEAN = REPO_ROOT / "OddPerfect.lean"
IMPORT_RE = re.compile(r"^(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+)", re.M)
CLASS_ORDER = ["REPLAY", "CANDIDATE-NEW", "REDUCTION", "LIBRARY"]


def mod_path(mod: str) -> pathlib.Path:
    return REPO_ROOT.joinpath(*mod.split(".")).with_suffix(".lean")


def reachable_modules() -> set[str]:
    seen: set[str] = set()
    queue = deque(m for m in IMPORT_RE.findall(ROOT_LEAN.read_text(encoding="utf-8")) if m.startswith("OddPerfect"))
    while queue:
        m = queue.popleft()
        if m in seen:
            continue
        seen.add(m)
        p = mod_path(m)
        if p.exists():
            for d in IMPORT_RE.findall(p.read_text(encoding="utf-8")):
                if d.startswith("OddPerfect") and d not in seen:
                    queue.append(d)
    return seen


def branch_nodes() -> list[dict]:
    if not BRANCH_MAP.exists():
        return []
    m = re.search(r"```json\s*(\{.*?\})\s*```", BRANCH_MAP.read_text(encoding="utf-8"), re.S)
    if not m:
        return []
    return json.loads(m.group(1))["nodes"]


def branch_ids() -> set[str]:
    return {n["id"] for n in branch_nodes()}


def validate_claims() -> tuple[list[dict], list[str], list[tuple[int, str]]]:
    claims = json.loads(REGISTRY.read_text(encoding="utf-8"))["claims"]
    reach = reachable_modules()
    nodes = branch_nodes()
    branches = {n["id"] for n in nodes}
    problems: list[str] = []
    rows: list[tuple[int, str]] = []
    registered_names: set[str] = set()
    for c in claims:
        p = mod_path(c["module"])
        text = p.read_text(encoding="utf-8") if p.exists() else ""
        # Reject `private` declarations; headline claims must be publicly importable.
        decl_pat = rf"^(?:(?:protected|noncomputable)\s+)*(?:theorem|lemma|def)\s+{re.escape(c['name'])}(?:\s|$)"
        priv_pat = rf"^private\s+(?:(?:noncomputable)\s+)*(?:theorem|lemma|def)\s+{re.escape(c['name'])}(?:\s|$)"
        is_private = p.exists() and re.search(priv_pat, text, re.M) is not None
        found = p.exists() and re.search(decl_pat, text, re.M) is not None
        audited = c["module"] in reach
        ns = c.get("namespace")
        ns_ok = True
        if ns:
            ns_ok = re.search(rf"^namespace\s+{re.escape(ns)}(?:\s|$)", text, re.M) is not None
        if is_private and not found:
            problems.append(f"{c['name']}: declaration is private in {p.relative_to(REPO_ROOT)} (headline claims must be public)")
        elif not found:
            problems.append(f"{c['name']}: public declaration not found in {p.relative_to(REPO_ROOT)}")
        if not ns_ok:
            problems.append(f"{c['name']}: declared namespace {ns!r} not found in {p.relative_to(REPO_ROOT)}")
        if not audited:
            problems.append(f"{c['name']}: module {c['module']} not reachable from OddPerfect.lean (unaudited)")
        if branches and c["branch"] not in branches:
            problems.append(f"{c['name']}: unknown branch id {c['branch']}")
        if c["class"] not in CLASS_ORDER:
            problems.append(f"{c['name']}: unknown class {c['class']}")
        rel = p.relative_to(REPO_ROOT).as_posix()
        status = "in public imports" if (found and ns_ok and audited) else "**PROBLEM**"
        statement = c["statement"].replace("|", r"\|")
        display_name = ".".join(filter(None, (ns, c["name"])))
        registered_names.add(c["name"])
        registered_names.add(display_name)
        row = (f"| [`{display_name}`](../{rel}) | {statement} | `{c['branch']}` | {c['class']} | "
               f"{c['literature']} | {status} |")
        rows.append((CLASS_ORDER.index(c["class"]) if c["class"] in CLASS_ORDER else 99, row))

    # Cross-check `lean` citations in research/BRANCH_MAP.md against registered claims
    for n in nodes:
        for ref in n.get("lean", []):
            if ref not in registered_names:
                problems.append(f"BRANCH_MAP node {n['id']}: lean reference {ref!r} not in claims_registry.json")
        if n.get("status") == "CLOSED" and not n.get("lean"):
            problems.append(f"BRANCH_MAP node {n['id']}: CLOSED without any cited lean theorem")
        if n.get("status") == "CONDITIONAL" and not n.get("hypothesis"):
            problems.append(f"BRANCH_MAP node {n['id']}: CONDITIONAL without named hypothesis")

    return claims, problems, rows


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()

    claims, problems, rows = validate_claims()

    for p in problems:
        print(f"PROBLEM: {p}", file=sys.stderr)
    if args.check:
        print(f"{len(claims)} claims checked, {len(problems)} problems")
        return 1 if problems else 0

    counts = {k: sum(1 for c in claims if c["class"] == k) for k in CLASS_ORDER}
    lines = [
        "# Headline claims registry",
        "",
        "Generated by `python3 research/tools/claims.py` from [claims_registry.json](claims_registry.json). Do not edit by hand.",
        "",
        "This is the **only** list of headline results other documents may cite. Other files should link here instead of copying statements and numbers.",
        "",
        "This tool checks public declaration names, namespaces, reachability, and BRANCH_MAP cross-references. Check the linked Lean signature for hypotheses and run the kernel audit separately.",
        "",
        "Classes:",
        "- `REPLAY`: formalizes a published result or a stated consequence.",
        "- `CANDIDATE-NEW`: priority is unresolved. Check the literature before making a novelty claim.",
        "- `REDUCTION`: a conditional or bookkeeping implication.",
        "- `LIBRARY`: true, but changes no node of [BRANCH_MAP.md](BRANCH_MAP.md) and no row of [FLOOR_CEILING.md](FLOOR_CEILING.md).",
        "",
        "Counts: " + ", ".join(f"{k} {v}" for k, v in counts.items()) + f". Problems detected: {len(problems)}.",
        "",
        "| Lean name | Statement | Branch | Class | Closest literature / note | Status |",
        "| --- | --- | --- | --- | --- | --- |",
    ]
    lines += [r for _, r in sorted(rows, key=lambda x: x[0])]
    lines.append("")
    CLAIMS_MD.write_text("\n".join(lines), encoding="utf-8")
    print(f"wrote {CLAIMS_MD.relative_to(REPO_ROOT)} ({len(claims)} claims, {len(problems)} problems)")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
