#!/usr/bin/env python3
"""Continuous Progress & Strategic Reevaluation Engine for OddPerfect.

Used by the Carbon Coordinator session on every reevaluation cycle to:
1. Measure verified proof coverage reachable from `OddPerfect.lean` vs unintegrated WIP tracks.
2. Check `.olean` compilation status and proof hygiene (`sorry`, `admit`, `axiom`, `unsafe`).
3. Track the 8-axis mathematical candidate-set contraction frontier (Audited vs Staged vs Published).
4. Compute structural-vs-certificate balance and Mathlib leverage metrics.
5. Compare against prior snapshots (`research/state/progress_history.jsonl`) to detect real
   progress vs stagnation/certificate bloat, and recommend the next Neon subagent cohort.

Usage:
  python3 research/tools/evaluate_progress.py --dashboard research/PROGRESS_DASHBOARD.md --record
  python3 research/tools/evaluate_progress.py --json
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sqlite3
import sys
import time
from collections import deque

REPO_ROOT = pathlib.Path(__file__).resolve().parents[2]
PROJECT_DIR = REPO_ROOT / "OddPerfect"
ROOT_LEAN = REPO_ROOT / "OddPerfect.lean"
OLEAN_ROOT = REPO_ROOT / ".lake" / "build" / "lib" / "lean"
STATE_DIR = REPO_ROOT / "research" / "state"
KB_DB = STATE_DIR / "mathlib_kb.sqlite"
LATEST_JSON = STATE_DIR / "progress_latest.json"
HISTORY_JSONL = STATE_DIR / "progress_history.jsonl"

IMPORT_RE = re.compile(r"^(?:public\s+)?import\s+([A-Za-z0-9_.]+)", re.M)
FORBIDDEN_PATTERNS = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom": re.compile(r"^\s*(?:public\s+|private\s+)?axiom\s+", re.M),
    "unsafe": re.compile(r"^\s*unsafe\s+", re.M),
    "implemented_by": re.compile(r"@\[implemented_by\b"),
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
        "audited_claim": "Ω(N) ≥ 37. Every candidate has an index with Ω(i_p)+5 ≤ Ω(N). Sixth-power-free gives Ω(N) ≥ 1179.",
        "audited_mod": "OddPerfect.ComponentIndexDrop",
        "audited_thm": "exists_componentIndex_cardFactors_add_five_le",
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
        "audited_claim": "j ≥ 30028 (≥ 36207 odd); 5 repunits |S₁|≥5; i,N > 10^17240 (> 10^300280 even)",
        "audited_mod": "OddPerfect.PrimePowerHigherObstruction",
        "audited_thm": "component_prime_power_index_exponent_ge_30028",
        "staged_claim": "Unconditional elimination of i = p^(2u) via higher p-adic congruences",
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

    ready_tracks = [t for t in tracks if t["fresh_olean"] > 0 and t["unbuilt"] <= 10]
    if ready_tracks:
        names = ", ".join(f"{t['track']} ({t['fresh_olean']}/{t['total_modules']} built)" for t in ready_tracks[:3])
        recommendations.append(
            f"[HARVEST HIGH-ROI] Dispatch `neon-harvester` + `neon-auditor` to finish & audit nearly-built staged tracks: {names}."
        )

    if len(unreached) > len(reached):
        recommendations.append(
            f"[INTEGRATION DEBT] Unintegrated modules ({len(unreached)}) exceed audited modules ({len(reached)}). Freeze new large certificate-tree generation until top staged theorems are wired into `OddPerfect.lean` and pass `research/Audit.lean`."
        )

    recommendations.append(
        "See [the resolution handoff](RESOLUTION_HANDOFF.md) for the six-factor criterion, Tóth split, exceptional Fermat reduction and the global B3 cap."
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

    lines = [
        "# Odd Perfect Number — Continuous Progress & Reevaluation Dashboard",
        "",
        f"**Snapshot UTC**: `{report['timestamp']}` · **Hygiene (`sorry`/`axiom`)**: `{c['hygiene_violations']} violations`",
        "",
        "## 1. Macro Health & Integration Metrics",
        "",
        "Module totals come from the import graph. See the [research ledger](LEDGER.md) for the last completed Lean build and axiom audit.",
        "",
        "| Metric | Current (Δ vs prior) | Interpretation |",
        "| --- | --- | --- |",
        f"| Modules reachable from `OddPerfect.lean` | {fmt_delta('audited_reached_modules')} | Covered by the public audit when it passes |",
        f"| Unintegrated modules in `OddPerfect/` | {fmt_delta('unintegrated_modules')} | Staged / WIP debt awaiting harvest or pruning |",
        f"| Structural modules vs Certificate chunks | `{c['structural_modules']:,}` / `{c['certificate_chunk_modules']:,}` (`{c['structural_share_pct']}%` structural) | Guards against brute-force tree bloat |",
        f"| Structural declarations (`OddPerfect/`) | {fmt_delta('project_structural_declarations')} | Reusable lemmas & public theorems |",
        f"| Distinct Mathlib modules imported (structural) | {fmt_delta('distinct_mathlib_imports_in_structural')} | Breadth of Mathlib theorem reuse |",
        "",
        "## 2. Candidate-Set Contraction Frontier (`∃ N, Odd N ∧ Nat.Perfect N`)",
        "",
        "| Axis | Imported by `OddPerfect.lean` | Staged in Workspace | Published Frontier |",
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
            "## 3. Unintegrated Work Tracks (Harvest Queue)",
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
            "## 4. Carbon Strategic Signals & Recommended Next Actions",
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
    parser.add_argument("--json", action="store_true", help="Print JSON report to stdout")
    args = parser.parse_args()

    STATE_DIR.mkdir(parents=True, exist_ok=True)
    prev = load_previous_snapshot()
    report = analyze_repo()

    LATEST_JSON.write_text(json.dumps(report, indent=2), encoding="utf-8")
    dash_text = render_dashboard(report, prev)
    pathlib.Path(args.dashboard).write_text(dash_text, encoding="utf-8")

    if args.record:
        with HISTORY_JSONL.open("a", encoding="utf-8") as fh:
            fh.write(json.dumps(report) + "\n")

    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(dash_text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
