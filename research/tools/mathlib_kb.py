#!/usr/bin/env python3
"""Local Mathlib & OddPerfect theorem indexer and knowledge-base CLI.

Indexes all declarations (`theorem`, `lemma`, `def`, `abbrev`, `structure`, `class`)
across the pinned Mathlib checkout (`.lake/packages/mathlib/{Mathlib,Archive}`) and
this project (`OddPerfect/`) into a local SQLite database (`research/state/mathlib_kb.sqlite`)
with FTS5 full-text search when available (and fast LIKE fallback otherwise).

Usage examples:
  python3 research/tools/mathlib_kb.py index
  python3 research/tools/mathlib_kb.py search "cyclotomic orderOf"
  python3 research/tools/mathlib_kb.py search "abundancyIndex" --scope mathlib
  python3 research/tools/mathlib_kb.py search "divisor" --module Mathlib.NumberTheory
  python3 research/tools/mathlib_kb.py overlap
  python3 research/tools/mathlib_kb.py domain-map --out research/MATHLIB_KB.md
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sqlite3
import sys
import time
import tempfile
from collections import Counter
from contextlib import closing

REPO_ROOT = pathlib.Path(__file__).resolve().parents[2]
MATHLIB_ROOT = REPO_ROOT / ".lake" / "packages" / "mathlib"
PROJECT_DIR = REPO_ROOT / "OddPerfect"
STATE_DIR = REPO_ROOT / "research" / "state"
DB_PATH = STATE_DIR / "mathlib_kb.sqlite"

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|public|noncomputable|unsafe|partial|scoped)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class)\s+"
    r"([A-Za-z0-9_'.]+)"
    r"([^\n]*)"
)

NAMESPACE_RE = re.compile(r"^namespace\s+([A-Za-z0-9_.']+)")
END_RE = re.compile(r"^end\s+([A-Za-z0-9_.']+)")
CERT_PART_RE = re.compile(r"^(Part\d+|Primes\d*|Seed\d+Part\d+)$")

CURATED_DOMAINS = [
    {
        "slug": "divisors_perfection",
        "title": "1. Divisors, Perfection, Abundancy & Factorisation Properties",
        "purpose": (
            "Core predicates (`Nat.Perfect`, `Nat.Abundant`, `Nat.Deficient`, "
            "`Nat.Pseudoperfect`, `Nat.abundancyIndex`), proper/antidiagonal divisor sums, "
            "monotonicity of abundancy under divisibility (`Abundant.of_dvd`, "
            "`abundancyIndex_le_of_dvd`), and Euclid-Euler even perfect numbers."
        ),
        "modules": [
            "Mathlib.NumberTheory.Divisors",
            "Mathlib.NumberTheory.FactorisationProperties",
            "Mathlib.Data.Nat.Factorization.Divisors",
            "Archive.Wiedijk100Theorems.PerfectNumbers",
        ],
        "queries": ["Perfect", "Abundant", "abundancyIndex", "properDivisors", "divisors_prime_pow"],
    },
    {
        "slug": "arithmetic_functions",
        "title": "2. Arithmetic Functions (`σ`, `ω`, `Ω`, `ζ`, `μ`) & Multiplicativity",
        "purpose": (
            "Dirichlet ring of arithmetic functions, multiplicativity of `σ k` "
            "(`isMultiplicative_sigma`), prime-power evaluation (`sigma_one_apply_prime_pow`), "
            "factorization expansions (`multiplicative_factorization`), `cardFactors` (`Ω`), "
            "`cardDistinctFactors` (`ω`), and `prodPrimeFactors`."
        ),
        "modules": [
            "Mathlib.NumberTheory.ArithmeticFunction.Misc",
            "Mathlib.NumberTheory.ArithmeticFunction.Defs",
            "Mathlib.NumberTheory.ArithmeticFunction.Zeta",
            "Mathlib.NumberTheory.ArithmeticFunction.Moebius",
            "Mathlib.NumberTheory.ArithmeticFunction.Carmichael",
        ],
        "queries": ["sigma_one_apply", "isMultiplicative_sigma", "cardFactors", "prodPrimeFactors"],
    },
    {
        "slug": "factorization_padic",
        "title": "3. Prime Factorization, Exact Prime Powers (`ordProj` / `ordCompl`) & Valuations",
        "purpose": (
            "Exact component extraction (`ordProj[p] n`, `ordCompl[p] n`), `Nat.factorization`, "
            "`IsPrimePow`, `padicValNat`, coprime splitting (`ordProj_mul_ordCompl_eq_self`), "
            "square characterizations (`Nat.isSquare_iff_even_factorization`), and LCM/GCD valuations."
        ),
        "modules": [
            "Mathlib.Data.Nat.Factorization.Basic",
            "Mathlib.Data.Nat.Factorization.Defs",
            "Mathlib.Data.Nat.Factorization.PrimePow",
            "Mathlib.Data.Nat.Factorization.LCM",
            "Mathlib.Algebra.IsPrimePow",
            "Mathlib.NumberTheory.Padics.PadicVal.Basic",
            "Mathlib.NumberTheory.Multiplicity",
        ],
        "queries": ["ordCompl", "ordProj", "isSquare_iff_even_factorization", "isPrimePow_iff"],
    },
    {
        "slug": "cyclotomic_orders",
        "title": "4. Cyclotomic Polynomials, Geometric Sums & Multiplicative Orders",
        "purpose": (
            "Bang-Zsigmondy / primitive prime divisor machinery, `Polynomial.cyclotomic` roots "
            "modulo `r` (`isRoot_cyclotomic_prime_pow_mul_iff_of_charP`), prime divisors of "
            "`Φ_n(a)`, lower bounds `(b - 1)^φ(d) < |Φ_d(b)|`, `orderOf` in `(ZMod r)ˣ`, and "
            "primes congruent to `1 mod n`."
        ),
        "modules": [
            "Mathlib.RingTheory.Polynomial.Cyclotomic.Basic",
            "Mathlib.RingTheory.Polynomial.Cyclotomic.Eval",
            "Mathlib.RingTheory.Polynomial.Cyclotomic.Expand",
            "Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization",
            "Mathlib.RingTheory.Polynomial.Cyclotomic.Roots",
            "Mathlib.Algebra.Ring.GeomSum",
            "Mathlib.GroupTheory.OrderOfElement",
            "Mathlib.NumberTheory.PrimesCongruentOne",
        ],
        "queries": ["cyclotomic", "geom_sum", "orderOf_dvd", "exists_prime_gt_modEq_one"],
    },
    {
        "slug": "reciprocity_zmod",
        "title": "5. Quadratic Reciprocity, Legendre/Jacobi Symbols & Finite Fields",
        "purpose": (
            "Direction constraints on prime-forcing edges (`3 mod 4` reciprocity), Euler's "
            "criterion, quadratic characters mod `4` and `8`, Jacobi symbol evaluation without "
            "primality, and finite-field multiplicative group structure."
        ),
        "modules": [
            "Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity",
            "Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol",
            "Mathlib.NumberTheory.LegendreSymbol.Basic",
            "Mathlib.FieldTheory.Finite.Basic",
            "Mathlib.Algebra.Field.ZMod",
        ],
        "queries": ["legendreSym", "jacobiSym", "quadraticReciprocity", "isSquare_of_mod_four"],
    },
    {
        "slug": "pell_diophantine",
        "title": "6. Pell Equations, `Zsqrtd`, Squares & Exponential Diophantine Tools",
        "purpose": (
            "Ljunggren / Nagell-Ljunggren reductions, Pell solution groups (`Pell.Solution1`), "
            "norm-one elements in `ℤ[√d]` (also used in Brillhart-Lehmer-Selfridge quadratic "
            "primality certificates), and Lucas-Lehmer / primality proving tactics."
        ),
        "modules": [
            "Mathlib.NumberTheory.Pell",
            "Mathlib.NumberTheory.PellMatiyasevic",
            "Mathlib.NumberTheory.Zsqrtd.Basic",
            "Mathlib.NumberTheory.LucasLehmer",
            "Mathlib.Tactic.Primality",
            "Mathlib.Tactic.NormNum.Prime",
        ],
        "queries": ["Solution1", "Zsqrtd", "lucas_lehmer"],
    },
    {
        "slug": "analytic_bounds",
        "title": "7. Logarithmic, Prime-Reciprocal & Rational Envelope Inequalities",
        "purpose": (
            "Underutilized analytical bridge for formalizing Zelinsky (2025) prime-reciprocal "
            "bounds (`∑ 1/p < log 2 - ...`), subexponential index envelopes `(1 + 1/K)^j`, "
            "and sharp abundancy-product upper bounds via `Real.log`."
        ),
        "modules": [
            "Mathlib.Analysis.SpecialFunctions.Log.Basic",
            "Mathlib.Analysis.SpecialFunctions.Log.Sum",
            "Mathlib.Analysis.SpecialFunctions.Log.Monotone",
            "Mathlib.NumberTheory.SumPrimeReciprocals",
            "Mathlib.NumberTheory.PrimeCounting",
        ],
        "queries": ["log_one_add", "log_prod", "tendsto_sum_prime_inv"],
    },
]


def is_certificate_chunk(path: pathlib.Path) -> bool:
    return bool(CERT_PART_RE.match(path.stem))


def path_to_module(path: pathlib.Path, base: pathlib.Path) -> str:
    rel = path.relative_to(base).with_suffix("")
    return ".".join(rel.parts)


def parse_lean_file(path: pathlib.Path, scope: str, module: str, is_cert: bool) -> list[tuple]:
    """Extract declarations with line numbers, signatures, and preceding `/-- ... -/` docstrings."""
    try:
        lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError:
        return []

    rows: list[tuple] = []
    ns_stack: list[str] = []
    doc_buf: list[str] = []
    in_doc = False
    rel_path = str(path.relative_to(REPO_ROOT))

    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        stripped = line.strip()

        # Track `/-- ... -/` docstrings
        if not in_doc and stripped.startswith("/--"):
            doc_buf = []
            if stripped.endswith("-/") and len(stripped) >= 5:
                doc_buf.append(stripped[3:-2].strip())
            else:
                in_doc = True
                doc_buf.append(stripped[3:].strip())
            i += 1
            continue
        elif in_doc:
            if "-/" in stripped:
                before, _ = stripped.split("-/", 1)
                doc_buf.append(before.strip())
                in_doc = False
            else:
                doc_buf.append(stripped)
            i += 1
            continue

        # Track namespaces lightly for context
        m_ns = NAMESPACE_RE.match(stripped)
        if m_ns:
            ns_stack.extend(m_ns.group(1).split("."))
            doc_buf = []
            i += 1
            continue
        m_end = END_RE.match(stripped)
        if m_end:
            parts = m_end.group(1).split(".")
            for _ in parts:
                if ns_stack:
                    ns_stack.pop()
            doc_buf = []
            i += 1
            continue

        m_decl = DECL_RE.match(line)
        if m_decl:
            kind, raw_name, rest = m_decl.group(1), m_decl.group(2), m_decl.group(3)
            is_private = 1 if re.search(r"\bprivate\b", line[: m_decl.start(1)]) else 0
            sig_lines = [rest.strip()]
            j = i + 1
            # Collect multi-line signature up to `:=` or `where` or blank line (max 8 lines)
            while (
                j < min(n, i + 9)
                and ":=" not in sig_lines[-1]
                and not sig_lines[-1].endswith("where")
                and lines[j].strip()
                and not lines[j].lstrip().startswith(("|", "theorem ", "lemma ", "def ", "/--"))
            ):
                sig_lines.append(lines[j].strip())
                if ":=" in lines[j] or lines[j].strip().endswith("where"):
                    break
                j += 1
            sig = " ".join(s for s in sig_lines if s)
            if ":=" in sig:
                sig = sig.split(":=", 1)[0].strip()
            if sig.endswith("where"):
                sig = sig[:-5].strip()
            sig = sig[:600]

            if raw_name.startswith("_root_."):
                full_name = raw_name[len("_root_.") :]
            elif ns_stack:
                full_name = ".".join(ns_stack) + "." + raw_name
            else:
                full_name = raw_name

            docstring = " ".join(d for d in doc_buf if d)[:600]
            doc_buf = []
            rows.append(
                (
                    scope,
                    module,
                    rel_path,
                    i + 1,
                    kind,
                    raw_name,
                    full_name,
                    sig,
                    docstring,
                    is_private,
                    1 if is_cert else 0,
                )
            )
            i += 1
            continue

        if stripped and not stripped.startswith("@["):
            doc_buf = []
        i += 1

    return rows


def has_fts5(conn: sqlite3.Connection) -> bool:
    try:
        conn.execute("CREATE VIRTUAL TABLE temp._fts5_probe USING fts5(x)")
        conn.execute("DROP TABLE temp._fts5_probe")
        return True
    except sqlite3.OperationalError:
        return False


def build_index(db_path: pathlib.Path = DB_PATH) -> dict:
    # Publish a complete snapshot so a search or a second indexer can keep using
    # the previous database while the new index is being populated.
    db_path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=db_path.parent, prefix=".mathlib-index-") as tmp:
        candidate = pathlib.Path(tmp) / "index.sqlite"
        with closing(sqlite3.connect(candidate)) as conn:
            meta = _populate_index(conn)
        candidate.replace(db_path)
    return meta


def _populate_index(conn: sqlite3.Connection) -> dict:
    t0 = time.time()
    conn.execute("PRAGMA synchronous = NORMAL")
    conn.execute(
        """
        CREATE TABLE declarations (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            scope TEXT NOT NULL,
            module TEXT NOT NULL,
            rel_path TEXT NOT NULL,
            line INTEGER NOT NULL,
            kind TEXT NOT NULL,
            name TEXT NOT NULL,
            full_name TEXT NOT NULL,
            signature TEXT NOT NULL,
            docstring TEXT NOT NULL,
            is_private INTEGER NOT NULL,
            is_cert_chunk INTEGER NOT NULL
        )
        """
    )
    conn.execute("CREATE INDEX idx_decl_scope_mod ON declarations(scope, module)")
    conn.execute("CREATE INDEX idx_decl_name ON declarations(name)")
    conn.execute("CREATE INDEX idx_decl_cert ON declarations(is_cert_chunk)")

    fts_enabled = has_fts5(conn)
    if fts_enabled:
        conn.execute(
            """
            CREATE VIRTUAL TABLE decl_fts USING fts5(
                full_name,
                name,
                module,
                signature,
                docstring,
                content='declarations',
                content_rowid='id',
                tokenize="unicode61 tokenchars '_'"
            )
            """
        )

    batch: list[tuple] = []
    mathlib_files = 0
    project_files = 0

    for sub in ("Mathlib", "Archive"):
        root = MATHLIB_ROOT / sub
        if not root.exists():
            continue
        for p in sorted(root.rglob("*.lean")):
            mathlib_files += 1
            mod = path_to_module(p, MATHLIB_ROOT)
            batch.extend(parse_lean_file(p, "mathlib", mod, False))
            if len(batch) >= 10000:
                conn.executemany(
                    """INSERT INTO declarations
                    (scope, module, rel_path, line, kind, name, full_name, signature, docstring, is_private, is_cert_chunk)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
                    batch,
                )
                batch.clear()

    if PROJECT_DIR.exists():
        for p in sorted(PROJECT_DIR.rglob("*.lean")):
            project_files += 1
            mod = path_to_module(p, REPO_ROOT)
            batch.extend(parse_lean_file(p, "project", mod, is_certificate_chunk(p)))

    if batch:
        conn.executemany(
            """INSERT INTO declarations
            (scope, module, rel_path, line, kind, name, full_name, signature, docstring, is_private, is_cert_chunk)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
            batch,
        )
        batch.clear()

    if fts_enabled:
        conn.execute("INSERT INTO decl_fts(decl_fts) VALUES('rebuild')")

    conn.commit()

    cur = conn.cursor()
    m_cnt = cur.execute("SELECT COUNT(*) FROM declarations WHERE scope='mathlib'").fetchone()[0]
    p_struct = cur.execute(
        "SELECT COUNT(*) FROM declarations WHERE scope='project' AND is_cert_chunk=0"
    ).fetchone()[0]
    p_cert = cur.execute(
        "SELECT COUNT(*) FROM declarations WHERE scope='project' AND is_cert_chunk=1"
    ).fetchone()[0]

    meta = {
        "indexed_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "elapsed_sec": round(time.time() - t0, 2),
        "fts5": fts_enabled,
        "mathlib_files": mathlib_files,
        "mathlib_declarations": m_cnt,
        "project_files": project_files,
        "project_structural_declarations": p_struct,
        "project_certificate_declarations": p_cert,
    }
    conn.execute("CREATE TABLE meta (k TEXT PRIMARY KEY, v TEXT)")
    for k, v in meta.items():
        conn.execute("INSERT INTO meta VALUES (?, ?)", (k, json.dumps(v)))
    conn.commit()
    return meta


def ensure_db() -> sqlite3.Connection:
    if not DB_PATH.exists():
        build_index(DB_PATH)
    conn = sqlite3.connect(str(DB_PATH))
    conn.row_factory = sqlite3.Row
    return conn


def search_declarations(
    conn: sqlite3.Connection,
    query: str,
    scope: str = "all",
    module_prefix: str | None = None,
    kind: str | None = None,
    include_certs: bool = False,
    limit: int = 20,
) -> list[sqlite3.Row]:
    fts_row = conn.execute("SELECT v FROM meta WHERE k='fts5'").fetchone()
    use_fts = bool(fts_row and json.loads(fts_row["v"]))

    filters = ["is_private = 0"]
    params: list = []
    if scope in ("mathlib", "project"):
        filters.append("d.scope = ?")
        params.append(scope)
    if not include_certs:
        filters.append("d.is_cert_chunk = 0")
    if module_prefix:
        filters.append("d.module LIKE ?")
        params.append(f"{module_prefix}%")
    if kind:
        filters.append("d.kind = ?")
        params.append(kind)

    where_extra = " AND ".join(filters)

    if use_fts:
        tokens = [re.sub(r'[^A-Za-z0-9_\']', "", t) for t in query.split()]
        tokens = [t for t in tokens if t]
        if tokens:
            fts_q = " AND ".join(f'"{t}"*' for t in tokens)
            sql = f"""
                SELECT d.*, bm25(decl_fts, 4.0, 6.0, 2.0, 1.5, 1.0) AS score
                FROM decl_fts
                JOIN declarations d ON d.id = decl_fts.rowid
                WHERE decl_fts MATCH ? AND {where_extra}
                ORDER BY score ASC
                LIMIT ?
            """
            rows = conn.execute(sql, [fts_q, *params, limit]).fetchall()
            if rows:
                return rows

    # Fallback substring match across full_name, signature, docstring
    sub_filters = list(filters)
    sub_params = list(params)
    for tok in query.split():
        sub_filters.append(
            "(d.full_name LIKE ? OR d.signature LIKE ? OR d.docstring LIKE ? OR d.module LIKE ?)"
        )
        pat = f"%{tok}%"
        sub_params.extend([pat, pat, pat, pat])

    sql = f"""
        SELECT d.*
        FROM declarations d
        WHERE {" AND ".join(sub_filters)}
        ORDER BY CASE WHEN d.name LIKE ? THEN 0 ELSE 1 END, length(d.name) ASC
        LIMIT ?
    """
    sub_params.extend([f"%{query.split()[0]}%", limit])
    return conn.execute(sql, sub_params).fetchall()


def compute_overlap_and_gaps(conn: sqlite3.Connection) -> dict:
    """Identify Mathlib import usage vs available relevant Mathlib modules & overlapping lemma names."""
    # Count current Mathlib imports across OddPerfect/*.lean (structural modules)
    imp_counter: Counter[str] = Counter()
    imp_re = re.compile(r"^(?:public\s+)?import\s+((?:Mathlib|Archive)\.[A-Za-z0-9_.]+)", re.M)
    for p in PROJECT_DIR.rglob("*.lean"):
        if is_certificate_chunk(p):
            continue
        for m in imp_re.findall(p.read_text(encoding="utf-8", errors="replace")):
            imp_counter[m] += 1

    underused = []
    for dom in CURATED_DOMAINS:
        for mod in dom["modules"]:
            decl_cnt = conn.execute(
                "SELECT COUNT(*) FROM declarations WHERE scope='mathlib' AND module=? AND is_private=0",
                (mod,),
            ).fetchone()[0]
            used_cnt = imp_counter.get(mod, 0)
            if decl_cnt > 0 and used_cnt <= 2:
                underused.append(
                    {
                        "domain": dom["title"],
                        "module": mod,
                        "mathlib_declarations": decl_cnt,
                        "project_imports": used_cnt,
                    }
                )

    # Check exact or near-exact lemma short-name collisions between structural OddPerfect and Mathlib NumberTheory/Algebra
    overlaps = conn.execute(
        """
        SELECT p.full_name AS proj_decl, p.rel_path AS proj_path, p.line AS proj_line, p.signature AS proj_sig,
               m.full_name AS mathlib_decl, m.module AS mathlib_mod, m.signature AS mathlib_sig
        FROM declarations p
        JOIN declarations m ON p.name = m.name
        WHERE p.scope = 'project' AND p.is_cert_chunk = 0 AND p.is_private = 0
          AND m.scope = 'mathlib' AND m.is_private = 0
          AND (m.module LIKE 'Mathlib.NumberTheory%'
               OR m.module LIKE 'Mathlib.Data.Nat%'
               OR m.module LIKE 'Mathlib.Algebra%'
               OR m.module LIKE 'Mathlib.RingTheory.Polynomial.Cyclotomic%')
          AND length(p.name) >= 8
        ORDER BY p.rel_path, p.line
        LIMIT 30
        """
    ).fetchall()

    return {
        "top_imported_mathlib": imp_counter.most_common(20),
        "underused_curated_modules": underused,
        "name_overlaps": [dict(r) for r in overlaps],
    }


def generate_markdown_kb(conn: sqlite3.Connection, out_path: pathlib.Path) -> None:
    meta = {r["k"]: json.loads(r["v"]) for r in conn.execute("SELECT k, v FROM meta").fetchall()}
    overlap = compute_overlap_and_gaps(conn)

    lines = [
        "# Mathlib Knowledge Base for Odd Perfect Numbers",
        "",
        "This knowledge base indexes proven theorems, definitions, and proof tactics in the",
        "repository's pinned Mathlib checkout (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, Lean `v4.36.0`)",
        "and cross-references them against `OddPerfect/`.",
        "",
        "## Quick Lookup Workflow (Carbon & Neon Agents)",
        "",
        "Before proving any general lemma on divisors, valuations, cyclotomics, orders, squares,",
        "or inequalities from scratch, query the local SQLite/FTS5 index:",
        "",
        "```sh",
        "# Search Mathlib declarations by name, type signature, or docstring",
        "python3 research/tools/mathlib_kb.py search \"cyclotomic orderOf\" --scope mathlib",
        "",
        "# Search within Mathlib.NumberTheory specifically",
        "python3 research/tools/mathlib_kb.py search \"abundancyIndex\" --module Mathlib.NumberTheory",
        "",
        "# Search existing project theorems so workers reuse OddPerfect lemmas instead of duplicating",
        "python3 research/tools/mathlib_kb.py search \"component_index\" --scope project",
        "",
        "# Audit underused Mathlib modules & potential duplicate helpers",
        "python3 research/tools/mathlib_kb.py overlap",
        "```",
        "",
        "## Index Snapshot",
        "",
        f"- **Pinned Mathlib files indexed**: `{meta.get('mathlib_files', 0):,}`",
        f"- **Pinned Mathlib declarations indexed**: `{meta.get('mathlib_declarations', 0):,}`",
        f"- **Project structural declarations (`OddPerfect/`)**: `{meta.get('project_structural_declarations', 0):,}`",
        f"- **Project generated certificate declarations**: `{meta.get('project_certificate_declarations', 0):,}`",
        "",
        "---",
        "",
        "## Domain Map of Proven Mathlib Machinery",
        "",
    ]

    for dom in CURATED_DOMAINS:
        lines.append(f"### {dom['title']}")
        lines.append("")
        lines.append(dom["purpose"])
        lines.append("")
        lines.append("| Mathlib Module | Public Decls | `OddPerfect` Imports |")
        lines.append("| --- | ---: | ---: |")
        imp_map = dict(
            overlap["top_imported_mathlib"]
            + [(u["module"], u["project_imports"]) for u in overlap["underused_curated_modules"]]
        )
        for mod in dom["modules"]:
            cnt = conn.execute(
                "SELECT COUNT(*) FROM declarations WHERE scope='mathlib' AND module=? AND is_private=0",
                (mod,),
            ).fetchone()[0]
            # Count exact imports in structural files if not in imp_map
            if mod not in imp_map:
                used = sum(
                    1
                    for p in PROJECT_DIR.rglob("*.lean")
                    if not is_certificate_chunk(p)
                    and re.search(rf"^(?:public\s+)?import\s+{re.escape(mod)}\b", p.read_text(errors="ignore"), re.M)
                )
            else:
                used = imp_map[mod]
            lines.append(f"| `{mod}` | {cnt} | {used} |")
        lines.append("")
        lines.append("**Representative Mathlib declarations:**")
        seen = set()
        shown = 0
        for q in dom["queries"]:
            for mod_pref in dom["modules"]:
                rows = search_declarations(conn, q, scope="mathlib", module_prefix=mod_pref, limit=3)
                for r in rows:
                    if r["full_name"] in seen:
                        continue
                    seen.add(r["full_name"])
                    sig = r["signature"].replace("|", "\\|")
                    if len(sig) > 110:
                        sig = sig[:107] + "..."
                    lines.append(f"- `{r['full_name']}` (`{r['module']}`): `{sig}`")
                    shown += 1
                    if shown >= 8:
                        break
                if shown >= 8:
                    break
            if shown >= 8:
                break
        lines.append("")

    lines.extend(
        [
            "---",
            "",
            "## High-Value Underutilized Mathlib Modules (Strategic Opportunities)",
            "",
            "These modules are already compiled in `.lake/build` on the pinned commit, contain",
            "relevant number-theoretic or analytic lemmas, and currently have **≤ 2** imports across",
            "structural `OddPerfect/` modules:",
            "",
            "| Module | Domain | Public Decls | Current Imports |",
            "| --- | --- | ---: | ---: |",
        ]
    )
    for u in overlap["underused_curated_modules"]:
        lines.append(
            f"| `{u['module']}` | {u['domain']} | {u['mathlib_declarations']} | {u['project_imports']} |"
        )

    lines.extend(
        [
            "",
            "## Lean 4 / Mathlib Proof Automation Checklist for Neon Workers",
            "",
            "- **Arithmetic & linear/integer goals**: `omega`, `lia`, `grind`, `norm_num`, `positivity`, `gcongr`.",
            "- **Ring / field identities**: `ring`, `linear_combination`, `field_simp`.",
            "- **Finite residue / small exponent exhaustion**: `interval_cases`, `fin_cases`, `decide`, `decide +kernel`.",
            "- **Primality certificates**: `norm_num` (`Mathlib.Tactic.NormNum.Prime`), Pratt/Lucas (`Mathlib.Tactic.Primality`), or project Pocklington/BLS checkers (`OddPerfect.LargeOrderPrime`, `OddPerfect.LargeOrderCube`, `OddPerfect.LargeOrderQuadratic`).",
            "- **Interactive lemma discovery inside temporary scratch checks**: `exact?`, `apply?`, `rw?`.",
            "",
        ]
    )

    out_path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Mathlib & OddPerfect Knowledge Base CLI")
    sub = parser.add_subparsers(dest="cmd", required=True)

    sub.add_parser("index", help="Build or rebuild the SQLite/FTS5 declaration index")

    p_search = sub.add_parser("search", help="Search Mathlib and/or project declarations")
    p_search.add_argument("query", help="Keywords from declaration name, signature, or docstring")
    p_search.add_argument("--scope", choices=["all", "mathlib", "project"], default="all")
    p_search.add_argument("--module", default=None, help="Module prefix filter, e.g. Mathlib.NumberTheory")
    p_search.add_argument("--kind", choices=["theorem", "lemma", "def", "abbrev", "structure", "class"], default=None)
    p_search.add_argument("--include-certs", action="store_true", help="Include generated PartNNN/PrimesNN chunks")
    p_search.add_argument("--limit", type=int, default=15)

    sub.add_parser("overlap", help="Report underused Mathlib modules and overlapping helper names")

    p_map = sub.add_parser("domain-map", help="Generate research/MATHLIB_KB.md from live index")
    p_map.add_argument("--out", default=str(REPO_ROOT / "research" / "MATHLIB_KB.md"))

    args = parser.parse_args()

    if args.cmd == "index":
        meta = build_index(DB_PATH)
        print(json.dumps(meta, indent=2))
        return 0

    conn = ensure_db()
    try:
        if args.cmd == "search":
            rows = search_declarations(
                conn,
                query=args.query,
                scope=args.scope,
                module_prefix=args.module,
                kind=args.kind,
                include_certs=args.include_certs,
                limit=args.limit,
            )
            if not rows:
                print(f"No matches for {args.query!r}.")
                return 0
            for r in rows:
                tag = "MATHLIB" if r["scope"] == "mathlib" else "PROJECT"
                print(f"[{tag}] {r['kind']} {r['full_name']}")
                print(f"  import {r['module']}   ({r['rel_path']}:{r['line']})")
                if r["signature"]:
                    print(f"  sig: {r['signature']}")
                if r["docstring"]:
                    print(f"  doc: {r['docstring']}")
                print()
            return 0

        if args.cmd == "overlap":
            info = compute_overlap_and_gaps(conn)
            print("=== Top Imported Mathlib Modules (Structural Files) ===")
            for mod, cnt in info["top_imported_mathlib"]:
                print(f"  {cnt:4d}  {mod}")
            print("\n=== Underused Curated Mathlib Modules (<= 2 imports) ===")
            for u in info["underused_curated_modules"]:
                print(
                    f"  imports={u['project_imports']}  decls={u['mathlib_declarations']:3d}  {u['module']}  ({u['domain']})"
                )
            print("\n=== Exact Short-Name Overlaps (Project vs Mathlib) ===")
            for o in info["name_overlaps"]:
                print(f"  {o['proj_decl']} ({o['proj_path']}:{o['proj_line']}) <-> {o['mathlib_decl']} ({o['mathlib_mod']})")
            return 0

        if args.cmd == "domain-map":
            out = pathlib.Path(args.out)
            generate_markdown_kb(conn, out)
            print(f"Wrote {out}")
            return 0
    finally:
        conn.close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
