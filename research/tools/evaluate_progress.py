#!/usr/bin/env python3
"""Progress dashboard for OddPerfect.

Progress metrics (section 0 of the dashboard) are the only numbers that count as progress:
  * BRANCH_MAP node statuses (CLOSED / CONDITIONAL / OPEN) and the active nodes' missing ingredients;
  * count-LP status per branch (research/tools/count_lp.py, gate G2);
  * IDEAS.md pipeline (proposed / gated / survived / killed);
  * CLAIMS registry classes (REPLAY / CANDIDATE-NEW / REDUCTION / LIBRARY);
  * repository integrity: modules imported by OddPerfect.lean that git does not track (must be 0).

Library-health numbers (modules, declarations, certificate share, Mathlib imports) are still
reported, but explicitly as *not progress*. Unintegrated modules are reported as a liability.

Usage:
  python3 research/tools/evaluate_progress.py --dashboard research/PROGRESS_DASHBOARD.md --record
  python3 research/tools/evaluate_progress.py --json
  python3 research/tools/evaluate_progress.py --strict   # exit 1 on hygiene or untracked imports
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sqlite3
import subprocess
import sys
import time
from collections import Counter, deque

REPO_ROOT = pathlib.Path(__file__).resolve().parents[2]
PROJECT_DIR = REPO_ROOT / "OddPerfect"
ROOT_LEAN = REPO_ROOT / "OddPerfect.lean"
OLEAN_ROOT = REPO_ROOT / ".lake" / "build" / "lib" / "lean"
STATE_DIR = REPO_ROOT / "research" / "state"
KB_DB = STATE_DIR / "mathlib_kb.sqlite"
LATEST_JSON = STATE_DIR / "progress_latest.json"
HISTORY_JSONL = STATE_DIR / "progress_history.jsonl"

IMPORT_RE = re.compile(r"^(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+)", re.M)
FORBIDDEN_PATTERNS = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom": re.compile(r"^\s*(?:public\s+|private\s+)?axiom\s+", re.M),
    "unsafe": re.compile(r"^\s*unsafe\s+", re.M),
    "implemented_by": re.compile(r"@\[implemented_by\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
}
CERT_PART_RE = re.compile(r"^(Part\d+|Primes\d*|Seed\d+Part\d+|Seed\d+)$")

# Named unintegrated / active tracks grouping related modules
TRACK_RULES = [
    ("NearPerfectFinite (Tier 0.1 — open-in-journals odd near-perfect finiteness)", re.compile(r"^OddPerfect\.Near(Perfect|Abundant)[A-Za-z0-9_]*(\.|$)")),
    ("IndexBound2379 (Tier 0.2 — Euler index ≥ 2379)", re.compile(r"^OddPerfect\.(IndexBound2379|IndexRange\d*|IndexRangeTables|IndexSieve[A-Za-z0-9_]*)(\.|$)")),
    ("Analytic & Ranked-Prime Bridge (Tier 0.3 — Zelinsky log & b^5 < 2N)", re.compile(r"^OddPerfect\.(PrimeReciprocalLog|ZelinskyReciprocal|SecondLargestPrime|QuasiperfectSupport)(\.|$)")),
    ("EvenIndexExponent256 (Tier 0.4 — prime-power index j ≥ 256)", re.compile(r"^OddPerfect\.EvenIndex[A-Za-z0-9_]*(\.|$)")),
    ("PrimeBoxes / SixthPowers / OrderTables (Tier 0.4)", re.compile(r"^OddPerfect\.(PrimeBoxTree|PrimeCover|PrimeDemand|SixthPowerBounds|OrderTable|PureSigmaOrder|OddPrimePowerSize|DivisorCountValuation)(\.|$)")),
    ("Tier 1 & 2 Stepping Stones / Global Obstructions", re.compile(r"^OddPerfect\.(ParityDichotomy|EvenDeficient|BoundedTwoVal|HarmonicFinite|HarmonicSupportFinite|HarmonicCubeFree|HarmonicBoundedExp|HarmonicTwoThree|PrimePowerObstruction|TripleRepunitObstruction|QuadrupleRepunitObstruction|PrimePowerExponent2308|PrimePowerHigherObstruction|DrisRegime|EulerExceptionalObstruction|ExceptionalBlockSquare|ExceptionalBranchClosure|RestrainedExponents|ZelinskySlope|ZelinskyFullSlope|CyclotomicRootSlope|UniversalCyclotomicRoots|GlobalObstruction|GlobalAbundancyObstruction|GlobalWave4Obstruction|Resolution)[A-Za-z0-9_]*(\.|$)")),
    ("SizeBound300 (Tier 0.5 background — N > 10^300)", re.compile(r"^OddPerfect\.(SizeBound300|SizeIndex300|SizePrimeBank300)(\.|$)")),
    ("DeficientFour & ω(N) ≥ 6 (background — Yang–Togbé / Gradshtein)", re.compile(r"^OddPerfect\.(Deficient(Cuts|FourClassification|Slots|Tree|Replay\d+|PowerReplayGeneral)|PrimeFive|PrimeRank5_\d+)(\.|$)")),
    ("CountBound47 (background — Ω(N) ≥ 47)", re.compile(r"^OddPerfect\.(CountBound47|CountChain45|ChainArithmetic|ChainWitness)(\.|$)")),
    ("HarmonicRange (background — Cohen–Sorli odd harmonic exclusion)", re.compile(r"^OddPerfect\.Harmonic[A-Za-z0-9_]*(\.|$)")),
]

FRONTIER_AXES = [
    {
        "axis": "Absolute Size Bound (N > 10^k)",
        "audited_claim": "N > 10^300 (> 10^740 on all I=ℓt² a>1; > 10^17240 if i=p^j; > 10^3136 if 6th-power-free)",
        "audited_mod": "OddPerfect.SizeBound300",
        "audited_thm": "ten_pow_three_hundred_lt_of_odd_perfect",
        "staged_claim": "N > 10^1500 branch-tree replay",
        "staged_mod": None,
        "published_best": "N > 10^1500 (Ochem–Rao 2012); 10^2200 reported",
    },
    {
        "axis": "Distinct Prime Divisors ω(N)",
        "audited_claim": "ω(N) ≥ 6 (≥ 8 if 3 ∤ N or i=p^(2u); ≥ 443 if 6th-power-free)",
        "audited_mod": "OddPerfect.PrimeFive",
        "audited_thm": "six_le_distinct_prime_factor_count",
        "staged_claim": "ω(N) ≥ 7 / Nielsen ω(N) ≥ 10",
        "staged_mod": None,
        "published_best": "ω(N) ≥ 10 (Nielsen 2015)",
    },
    {
        "axis": "Total Prime Divisors Ω(N)",
        "audited_claim": "Ω(N) ≥ 37. Every candidate has an index with Ω(i_p)+6 ≤ Ω(N). Sixth-power-free gives Ω(N) ≥ 1179.",
        "audited_mod": "OddPerfect.QuarticTargetCapacity",
        "audited_thm": "exists_componentIndex_cardFactors_add_six_le",
        "staged_claim": "Ω(N) ≥ 47",
        "staged_mod": "OddPerfect.CountBound47",
        "published_best": "Ω(N) ≥ 101 (Ochem–Rao 2012)",
    },
    {
        "axis": "Linear / Additive Factor Excess",
        "audited_claim": "21ω ≤ 8Ω+39. At 3∤N, 8ω+4L₂ ≤ 3Ω+7. In the sixth-power-free case more than one sixth of the support is an exact-square prime ≡1 mod 5.",
        "audited_mod": "OddPerfect.ZelinskyFullSlope",
        "audited_thm": "multi_block_slope_above_zelinsky",
        "staged_claim": "Extend Clayton–Hansen and Zelinsky slopes across uncovered residue classes",
        "staged_mod": None,
        "published_best": "Ω ≥ 2ω + 51 (Ochem–Rao). Clayton–Hansen (2023) give 99ω ≤ 37Ω+187 and, for 3∤N, 51ω ≤ 19Ω+46.",
    },
    {
        "axis": "Euler Component Index i_q = σ(m²)/qᵃ",
        "audited_claim": "i_q ≥ 2379. At a>1, I=ℓt² forces N > 10^740 and excludes q ≡ 2,4 mod 7.",
        "audited_mod": "OddPerfect.ExceptionalBranchClosure",
        "audited_thm": "exceptional_index_size_gt_ten_pow_740",
        "staged_claim": "Full closure of I = ℓ t² (Hirakawa 2024)",
        "staged_mod": None,
        "published_best": "Dris / Broughan–Delbourgo–Zhou / Hirakawa (2024)",
    },
    {
        "axis": "Prime-Power Component Index i = p^j",
        "audited_claim": "Only at the Euler prime; even j: ≥ 13 repunit bases, 2u ≥ 1.3·10^16 (floor without ceiling, see FLOOR_CEILING.md)",
        "audited_mod": "OddPerfect.TridecupleRepunitObstruction",
        "audited_thm": "even_prime_power_component_size_gt_ten_pow_353234555955090756",
        "staged_claim": "Paused pending quantitatively incompatible bounds (IDEAS 3)",
        "staged_mod": None,
        "published_best": "Conditional exclusion via Nagell–Ljunggren / Goormaghtigh",
    },
    {
        "axis": "Odd Harmonic Superclass (σ(N) ∣ Nτ(N))",
        "audited_claim": "ω ≥ 3 (≥ 4 if 5th-power-free); HarmonicRange/Smooth; fixed-support/mean finite",
        "audited_mod": "OddPerfect.HarmonicBoundedExp",
        "audited_thm": "odd_oreHarmonic_four_le_primeFactors_of_fifthPowerFree",
        "staged_claim": "HarmonicTauSmooth toward N > 10^24",
        "staged_mod": "OddPerfect.HarmonicTauSmooth",
        "published_best": "N > 10^24 (Cohen–Sorli 2010); Pollack (2014) Subspace finiteness",
    },
    {
        "axis": "Deficient-Perfect / Near-Perfect / Spoof Classes",
        "audited_claim": "The unique four-prime odd deficient-perfect case is (9018009, 819). A coprime divisor-sum split gives the proper factor 19 of its Tóth multiplier.",
        "audited_mod": "OddPerfect.DeficientFourClassification",
        "audited_thm": "odd_deficientPerfect_four_iff",
        "staged_claim": "4-prime odd near-perfect uniqueness (Tang–Ma–Feng)",
        "staged_mod": None,
        "published_best": "Yang–Togbé (2023), Tang–Ma–Feng (2016), BYU signed spoofs",
    },
]


def mod_to_lean(mod: str) -> pathlib.Path:
    return REPO_ROOT.joinpath(*mod.split(".")).with_suffix(".lean")


def mod_to_olean(mod: str) -> pathlib.Path:
    return OLEAN_ROOT.joinpath(*mod.split(".")).with_suffix(".olean")


def strip_lean_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    text = re.sub(r"--[^\n]*", " ", text)
    return text


def olean_status(mod: str) -> str:
    lp = mod_to_lean(mod)
    op = mod_to_olean(mod)
    if not lp.exists():
        return "missing_source"
    if not op.exists():
        return "unbuilt"
    return "fresh" if op.stat().st_mtime >= lp.stat().st_mtime else "stale"


RESEARCH_DIR = REPO_ROOT / "research"
IDEA_STATUSES = ["PROPOSED", "GATED", "SURVIVES", "FORMALIZING", "DONE", "KILLED", "PAUSED"]


def _branch_nodes() -> list[dict]:
    path = RESEARCH_DIR / "BRANCH_MAP.md"
    if not path.exists():
        return []
    m = re.search(r"```json\s*(\{.*?\})\s*```", path.read_text(encoding="utf-8"), re.S)
    return json.loads(m.group(1))["nodes"] if m else []


def _idea_counts() -> dict[str, int]:
    path = RESEARCH_DIR / "IDEAS.md"
    if not path.exists():
        return {}
    counts: Counter = Counter()
    for line in path.read_text(encoding="utf-8").splitlines():
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) >= 4 and cells[0].isdigit() and cells[3] in IDEA_STATUSES:
            counts[cells[3]] += 1
    return dict(counts)


def _claim_counts() -> dict[str, int]:
    path = RESEARCH_DIR / "claims_registry.json"
    if not path.exists():
        return {}
    return dict(Counter(c["class"] for c in json.loads(path.read_text(encoding="utf-8"))["claims"]))


def _count_lp_status() -> dict[str, dict]:
    data_path = RESEARCH_DIR / "count_constraints.json"
    if not data_path.exists():
        return {}
    sys.path.insert(0, str(RESEARCH_DIR / "tools"))
    try:
        import count_lp  # type: ignore
    finally:
        sys.path.pop(0)
    out = {}
    data = json.loads(data_path.read_text(encoding="utf-8"))
    for bid, br in data["branches"].items():
        parsed = [count_lp.parse_constraint(c["expr"]) for c in br["constraints"]]
        obj = br.get("objective", next(iter(br["variables"])))
        res = count_lp.simplex_max(list(br["variables"]), parsed, {obj: count_lp.Fraction(1)})
        entry = {"status": res.status, "objective": obj, "n_constraints": len(parsed)}
        if res.ray:
            entry["ray"] = {k: count_lp.fmt(v) for k, v in res.ray.items() if v != 0}
        if res.value is not None:
            entry["max"] = count_lp.fmt(res.value)
        out[bid] = entry
    return out


def _untracked_imported(reached: set[str]) -> list[str]:
    try:
        res = subprocess.run(
            ["git", "ls-files", "--others", "--exclude-standard", "--", "OddPerfect", "OddPerfect.lean"],
            cwd=REPO_ROOT, capture_output=True, text=True, check=True,
        )
    except (OSError, subprocess.CalledProcessError):
        return ["<git unavailable>"]
    untracked = {
        ".".join(pathlib.Path(p).with_suffix("").parts)
        for p in res.stdout.splitlines() if p.endswith(".lean")
    }
    hits = sorted(m for m in untracked if m in reached)
    if "OddPerfect" in untracked:
        hits.insert(0, "OddPerfect (root file)")
    return hits


def _claims_problems() -> list[str]:
    sys.path.insert(0, str(RESEARCH_DIR / "tools"))
    try:
        import claims  # type: ignore
        _, problems, _ = claims.validate_claims()
        return problems
    finally:
        sys.path.pop(0)


def research_frontier(reached: set[str]) -> dict:
    nodes = _branch_nodes()
    tree_nodes = [n for n in nodes if n.get("parent") is not None or n["id"] == "ROOT"]
    partition_nodes = [n for n in tree_nodes if n.get("kind") == "partition"]
    slice_nodes = [n for n in tree_nodes if n.get("kind") == "slice"]
    return {
        "branch_status": dict(Counter(n["status"] for n in tree_nodes)),
        "partition_status": dict(Counter(n["status"] for n in partition_nodes)),
        "slice_status": dict(Counter(n["status"] for n in slice_nodes)),
        "nodes": [{k: n.get(k) for k in ("id", "kind", "status", "active", "missing", "hypothesis")} for n in nodes],
        "active_nodes": [n for n in nodes if n.get("active")],
        "ideas": _idea_counts(),
        "claims": _claim_counts(),
        "claims_problems": _claims_problems(),
        "count_lp": _count_lp_status(),
        "untracked_imported": _untracked_imported(reached),
    }


def analyze_repo() -> dict:
    all_files = sorted(PROJECT_DIR.rglob("*.lean"))
    all_mods = [".".join(p.relative_to(REPO_ROOT).with_suffix("").parts) for p in all_files]
    mod_set = set(all_mods)

    # Parse imports & check hygiene
    imports_map: dict[str, list[str]] = {}
    mathlib_imports: set[str] = set()
    hygiene_violations: list[dict] = []
    structural_files = 0
    cert_files = 0

    for p, m in zip(all_files, all_mods):
        if CERT_PART_RE.match(p.stem):
            cert_files += 1
        else:
            structural_files += 1
        raw = p.read_text(encoding="utf-8", errors="replace")
        code = strip_lean_comments(raw)
        imps = IMPORT_RE.findall(code)
        imports_map[m] = [i for i in imps if i.startswith("OddPerfect")]
        if not CERT_PART_RE.match(p.stem):
            for i in imps:
                if i.startswith(("Mathlib.", "Archive.")):
                    mathlib_imports.add(i)
        for kind, rx in FORBIDDEN_PATTERNS.items():
            if rx.search(code):
                hygiene_violations.append({"module": m, "path": str(p.relative_to(REPO_ROOT)), "kind": kind})

    # Compute reachability from OddPerfect.lean
    root_code = strip_lean_comments(ROOT_LEAN.read_text(encoding="utf-8", errors="replace"))
    root_imports = [i for i in IMPORT_RE.findall(root_code) if i.startswith("OddPerfect")]

    reached: set[str] = set()
    q = deque(root_imports)
    while q:
        cur = q.popleft()
        if cur in reached or cur not in mod_set:
            continue
        reached.add(cur)
        for nxt in imports_map.get(cur, []):
            if nxt not in reached:
                q.append(nxt)

    unreached = sorted(mod_set - reached)

    # Group unreached into tracks
    tracks = []
    assigned: set[str] = set()
    for label, rx in TRACK_RULES:
        matched = [m for m in unreached if rx.search(m)]
        if matched:
            assigned.update(matched)
            top_mods = [m for m in matched if m.count(".") == 1]
            statuses = [olean_status(m) for m in matched]
            fresh_cnt = statuses.count("fresh")
            stale_cnt = statuses.count("stale")
            unbuilt_cnt = statuses.count("unbuilt")
            tracks.append(
                {
                    "track": label,
                    "total_modules": len(matched),
                    "top_level_modules": top_mods,
                    "fresh_olean": fresh_cnt,
                    "stale_olean": stale_cnt,
                    "unbuilt": unbuilt_cnt,
                    "ready_pct": round(100.0 * fresh_cnt / len(matched), 1),
                }
            )

    other_unreached = [m for m in unreached if m not in assigned]
    if other_unreached:
        statuses = [olean_status(m) for m in other_unreached]
        tracks.append(
            {
                "track": "Other Unintegrated Modules",
                "total_modules": len(other_unreached),
                "top_level_modules": [m for m in other_unreached if m.count(".") == 1],
                "fresh_olean": statuses.count("fresh"),
                "stale_olean": statuses.count("stale"),
                "unbuilt": statuses.count("unbuilt"),
                "ready_pct": round(100.0 * statuses.count("fresh") / len(other_unreached), 1),
            }
        )

    tracks.sort(key=lambda t: (-t["ready_pct"], t["unbuilt"], -t["total_modules"]))

    # Frontier verification
    frontier_report = []
    for ax in FRONTIER_AXES:
        a_mod = ax["audited_mod"]
        s_mod = ax["staged_mod"]
        a_state = "IMPORTED" if a_mod in reached else olean_status(a_mod)
        if s_mod is None:
            s_state = "OPEN"
        elif s_mod in reached:
            s_state = "IMPORTED"
        else:
            s_state = f"STAGED ({olean_status(s_mod)})"
        frontier_report.append({**ax, "audited_status": a_state, "staged_status": s_state})

    # Mathlib KB stats if indexed
    kb_stats = {}
    if KB_DB.exists():
        conn = sqlite3.connect(str(KB_DB))
        try:
            kb_stats["mathlib_declarations"] = conn.execute(
                "SELECT COUNT(*) FROM declarations WHERE scope='mathlib'"
            ).fetchone()[0]
            kb_stats["project_structural_declarations"] = conn.execute(
                "SELECT COUNT(*) FROM declarations WHERE scope='project' AND is_cert_chunk=0"
            ).fetchone()[0]
            kb_stats["project_certificate_declarations"] = conn.execute(
                "SELECT COUNT(*) FROM declarations WHERE scope='project' AND is_cert_chunk=1"
            ).fetchone()[0]
        finally:
            conn.close()

    # Strategic signals & recommended next Neon cohort
    recommendations = []
    if hygiene_violations:
        recommendations.append(
            f"[BLOCKER] Eliminate {len(hygiene_violations)} proof-hygiene violation(s) (`sorry`/`axiom`/`admit`) before any integration."
        )

    frontier = research_frontier(reached)
    if frontier["untracked_imported"]:
        recommendations.append(
            f"[BLOCKER] {len(frontier['untracked_imported'])} module(s) reachable from `OddPerfect.lean` are not tracked by git. Commit and tag before the next round."
        )
    if len(frontier["active_nodes"]) > 3:
        recommendations.append(
            f"[BLOCKER] {len(frontier['active_nodes'])} active nodes in BRANCH_MAP.md (max 3 allowed by AGENTS.md §0)."
        )
    if frontier["claims_problems"]:
        recommendations.append(
            f"[BLOCKER] {len(frontier['claims_problems'])} problem(s) reported by `claims.py --check`. Fix before committing."
        )
    for node in frontier["active_nodes"]:
        recommendations.append(
            f"[ACTIVE {node['id']}] Missing ingredient: {node.get('missing', '(not stated — fill in BRANCH_MAP.md)')}"
        )
    if frontier["ideas"].get("PROPOSED", 0) and not frontier["ideas"].get("GATED", 0):
        recommendations.append(
            "[GATES] Ideas are waiting in IDEAS.md without gate records. Run research/GATES.md G1–G4 and the Skeptic before dispatching any prover."
        )
    if unreached:
        recommendations.append(
            f"[LIABILITY] {len(unreached)} unintegrated modules. Harvest only those on an active branch's critical path; archive the rest."
        )
    recommendations.append(
        "Policy: harvesting, floor-raising and count tightening are not progress unless they change BRANCH_MAP, FLOOR_CEILING or the count-LP status (see NO_GO.md)."
    )

    return {
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "counts": {
            "total_lean_modules": len(all_mods),
            "audited_reached_modules": len(reached),
            "unintegrated_modules": len(unreached),
            "root_direct_imports": len(root_imports),
            "structural_modules": structural_files,
            "certificate_chunk_modules": cert_files,
            "structural_share_pct": round(100.0 * structural_files / max(1, len(all_mods)), 1),
            "distinct_mathlib_imports_in_structural": len(mathlib_imports),
            "hygiene_violations": len(hygiene_violations),
            **kb_stats,
        },
        "hygiene_violations": hygiene_violations,
        "research_frontier": frontier,
        "unintegrated_tracks": tracks,
        "frontier": frontier_report,
        "recommendations": recommendations,
    }


def load_previous_snapshot() -> dict | None:
    if not HISTORY_JSONL.exists():
        return None
    lines = [ln.strip() for ln in HISTORY_JSONL.read_text(encoding="utf-8").splitlines() if ln.strip()]
    if not lines:
        return None
    return json.loads(lines[-1])


def render_dashboard(report: dict, prev: dict | None) -> str:
    c = report["counts"]
    prev_c = prev["counts"] if prev else {}

    def fmt_delta(key: str) -> str:
        val = c.get(key, 0)
        if key not in prev_c:
            return f"`{val:,}`"
        diff = val - prev_c[key]
        if diff == 0:
            return f"`{val:,}` (0)"
        sign = "+" if diff > 0 else ""
        return f"`{val:,}` ({sign}{diff:,})"

    rf = report.get("research_frontier", {})
    lines = [
        "# Odd Perfect Number — Progress Dashboard",
        "",
        f"**Snapshot UTC**: `{report['timestamp']}` · **Hygiene (`sorry`/`axiom`)**: `{c['hygiene_violations']} violations`"
        f" · **Untracked modules imported by `OddPerfect.lean`**: `{len(rf.get('untracked_imported', []))}`",
        "",
        "Generated by `python3 research/tools/evaluate_progress.py`. Do not edit by hand.",
        "",
        "## 0. Progress metrics",
        "",
        "Only this section measures progress toward `¬ existsOddPerfect`. See [BRANCH_MAP.md](BRANCH_MAP.md), [FLOOR_CEILING.md](FLOOR_CEILING.md), [IDEAS.md](IDEAS.md), [CLAIMS.md](CLAIMS.md) and [NO_GO.md](NO_GO.md).",
        "",
        "### Case-tree nodes",
        "",
        "| Node | Kind | Status | Active | Missing ingredient / hypothesis |",
        "| --- | --- | --- | --- | --- |",
    ]
    for n in rf.get("nodes", []):
        extra = (n.get("missing") or n.get("hypothesis") or "").replace("|", r"\|")
        lines.append(f"| `{n['id']}` | {n['kind']} | **{n['status']}** | {'yes' if n.get('active') else ''} | {extra} |")
    ps = rf.get("partition_status", {})
    ss = rf.get("slice_status", {})
    lines += [
        "",
        f"Partitions: CLOSED {ps.get('CLOSED', 0)} · CONDITIONAL {ps.get('CONDITIONAL', 0)} · OPEN {ps.get('OPEN', 0)}  |  "
        f"Slices: CLOSED {ss.get('CLOSED', 0)} · CONDITIONAL {ss.get('CONDITIONAL', 0)} · OPEN {ss.get('OPEN', 0)}.",
        "",
        "Partition closures and slice closures are tracked separately (anti-slice-inflation rule). Totals cannot be interpreted as a fraction of the conjecture resolved.",
        "",
        "### Count-LP gate (G2)",
        "",
        "This table describes the public baseline projection. See the [profile comparison and surviving families](STRATEGY_REVIEW.md#what-survives-the-calculation) for the effect of including the separate target-reuse inequalities.",
        "",
        "| Branch | Constraints | Status | Recession ray / max |",
        "| --- | ---: | --- | --- |",
    ]
    for bid, e in rf.get("count_lp", {}).items():
        detail = ", ".join(f"{k}={v}" for k, v in e.get("ray", {}).items()) or (f"max {e['objective']} = {e['max']}" if "max" in e else "")
        lines.append(f"| `{bid}` | {e['n_constraints']} | **{e['status'].upper()}** | {detail} |")
    ideas = rf.get("ideas", {})
    claims = rf.get("claims", {})
    lines += [
        "",
        "### Idea pipeline and claims",
        "",
        "| Metric | Value |",
        "| --- | --- |",
        "| Ideas (" + " / ".join(IDEA_STATUSES) + ") | " + " / ".join(str(ideas.get(s, 0)) for s in IDEA_STATUSES) + " |",
        "| Claims (REPLAY / CANDIDATE-NEW / REDUCTION / LIBRARY) | "
        + " / ".join(str(claims.get(k, 0)) for k in ("REPLAY", "CANDIDATE-NEW", "REDUCTION", "LIBRARY")) + " |",
        "",
    ]
    lines += [
        "## 1. Library health (not progress)",
        "",
        "These numbers measure the size of the verified library. They do not measure closeness to the goal. See the [research ledger](LEDGER.md) for the last completed Lean build and axiom audit.",
        "",
        "| Metric | Current (Δ vs prior) | Interpretation |",
        "| --- | --- | --- |",
        f"| Modules reachable from `OddPerfect.lean` | {fmt_delta('audited_reached_modules')} | Covered by the public audit when it passes |",
        f"| Unintegrated modules in `OddPerfect/` | {fmt_delta('unintegrated_modules')} | **Liability**: harvest only when on an active node's critical path |",
        f"| Structural modules vs Certificate chunks | `{c['structural_modules']:,}` / `{c['certificate_chunk_modules']:,}` (`{c['structural_share_pct']}%` structural) | Size only |",
        f"| Structural declarations (`OddPerfect/`) | {fmt_delta('project_structural_declarations')} | Size only |",
        f"| Distinct Mathlib modules imported (structural) | {fmt_delta('distinct_mathlib_imports_in_structural')} | Size only |",
        "",
        "## 2. Candidate-set restrictions (`∃ N, Odd N ∧ Nat.Perfect N`)",
        "",
        "| Axis | Imported by `OddPerfect.lean` | Staged / next | Published Frontier |",
        "| --- | --- | --- | --- |",
    ]

    for f in report["frontier"]:
        audited_claim = f["audited_claim"].replace("|", r"\|")
        lines.append(
            f"| **{f['axis']}** | {audited_claim} (`{f['audited_status']}`) | {f['staged_claim']} (`{f['staged_status']}`) | {f['published_best']} |"
        )

    lines.extend(
        [
            "",
            "## 3. Unintegrated modules (liability)",
            "",
            "| Track | Total Files | Fresh `.olean` | Stale `.olean` | Unbuilt | Compiled % | Entry Modules |",
            "| --- | ---: | ---: | ---: | ---: | ---: | --- |",
        ]
    )
    for t in report["unintegrated_tracks"]:
        tops = ", ".join(f"`{m.split('.', 1)[1]}`" for m in t["top_level_modules"][:4])
        if len(t["top_level_modules"]) > 4:
            tops += f" (+{len(t['top_level_modules']) - 4})"
        lines.append(
            f"| {t['track']} | {t['total_modules']} | {t['fresh_olean']} | {t['stale_olean']} | {t['unbuilt']} | {t['ready_pct']}% | {tops} |"
        )

    lines.extend(
        [
            "",
            "## 4. Signals and next actions",
            "",
        ]
    )
    for rec in report["recommendations"]:
        lines.append(f"- {rec}")
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description="Evaluate OddPerfect proof progress and strategic frontier")
    parser.add_argument("--dashboard", default=str(REPO_ROOT / "research" / "PROGRESS_DASHBOARD.md"))
    parser.add_argument("--record", action="store_true", help="Append snapshot to progress_history.jsonl")
    parser.add_argument("--check", action="store_true",
                        help="Read-only mode: do not modify progress_latest.json, progress_history.jsonl, or dashboard")
    parser.add_argument("--json", action="store_true", help="Print JSON report to stdout")
    parser.add_argument("--strict", action="store_true",
                        help="Exit 1 on hygiene violations, untracked imports, >3 active nodes, or claims.py problems")
    args = parser.parse_args()

    prev = load_previous_snapshot()
    report = analyze_repo()
    dash_text = render_dashboard(report, prev)

    if not args.check:
        STATE_DIR.mkdir(parents=True, exist_ok=True)
        LATEST_JSON.write_text(json.dumps(report, indent=2), encoding="utf-8")
        pathlib.Path(args.dashboard).write_text(dash_text, encoding="utf-8")
        if args.record:
            with HISTORY_JSONL.open("a", encoding="utf-8") as fh:
                fh.write(json.dumps(report) + "\n")

    if args.json:
        print(json.dumps(report, indent=2))
    elif not args.check:
        print(dash_text)
    else:
        rf = report["research_frontier"]
        print(
            f"CHECK OK-SUMMARY: hygiene={report['counts']['hygiene_violations']}, "
            f"untracked_imported={len(rf['untracked_imported'])}, "
            f"active_nodes={len(rf['active_nodes'])}/3, "
            f"claims_problems={len(rf['claims_problems'])}"
        )

    if args.strict:
        rf = report["research_frontier"]
        failures = []
        if report["counts"]["hygiene_violations"]:
            failures.append(f"{report['counts']['hygiene_violations']} hygiene violation(s)")
        if rf["untracked_imported"]:
            failures.append(f"{len(rf['untracked_imported'])} untracked imported module(s)")
        if len(rf["active_nodes"]) > 3:
            failures.append(f"{len(rf['active_nodes'])} active nodes (>3)")
        if rf["claims_problems"]:
            failures.append(f"{len(rf['claims_problems'])} claims.py problem(s): " + "; ".join(rf["claims_problems"][:3]))
        if failures:
            print("STRICT FAILURE: " + ", ".join(failures), file=sys.stderr)
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
