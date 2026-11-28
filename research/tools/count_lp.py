#!/usr/bin/env python3
"""Count-polyhedron gate (G2) for OddPerfect research.

Collects the linear count constraints recorded in research/count_constraints.json for a
BRANCH_MAP node, relaxes them to a rational LP over nonnegative variables, and answers:

  * Is the objective (default: omega) bounded above?  If not, print a recession ray —
    the direction along which *every* recorded constraint stays satisfied forever.
    Compare each proposed inequality with named families as well as the solver ray.
  * Do the recorded parametric families (e.g. the 27 Nov assessment family) satisfy
    every constraint for all t >= t_min?

Exact rational arithmetic (fractions.Fraction), two-phase simplex with Bland's rule,
no third-party dependencies.

Usage:
  python3 research/tools/count_lp.py --branch A1_SPF
  python3 research/tools/count_lp.py --branch A1_SPF --add "S51col <= Q13 - 5"
  python3 research/tools/count_lp.py --branch A1_SPF --profile target-reuse
  python3 research/tools/count_lp.py --branch A1_SPF --profile target-reuse --omit-row mod-five
  python3 research/tools/count_lp.py --branch A1_SPF --verified-only
  python3 research/tools/count_lp.py --branch A1_SPF --json
Exit codes: 0 = bounded, 3 = unbounded (ray printed), 2 = infeasible, 1 = error.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys
from fractions import Fraction

REPO_ROOT = pathlib.Path(__file__).resolve().parents[2]
DEFAULT_DATA = REPO_ROOT / "research" / "count_constraints.json"

TOKEN_RE = re.compile(r"\s*(?:(\d+(?:/\d+)?)|([A-Za-z_][A-Za-z0-9_]*)|(<=|>=|=|\+|-|\*))")


# ---------------------------------------------------------------- parsing

def _tokens(s: str) -> list[str]:
    out, pos = [], 0
    s = s.strip()
    while pos < len(s):
        m = TOKEN_RE.match(s, pos)
        if not m or m.end() == pos:
            raise ValueError(f"cannot parse near {s[pos:]!r}")
        out.append(next(g for g in m.groups() if g is not None))
        pos = m.end()
    return out


def parse_linear(side: list[str]) -> tuple[dict[str, Fraction], Fraction]:
    """Parse 'a*X + b - c*Y' into ({X: a, Y: -c}, b)."""
    coeffs: dict[str, Fraction] = {}
    const = Fraction(0)
    sign, i = 1, 0
    if not side:
        raise ValueError("empty expression side")
    while i < len(side):
        tok = side[i]
        if tok in "+-":
            sign = 1 if tok == "+" else -1
            i += 1
            continue
        coef = Fraction(1)
        if re.fullmatch(r"\d+(?:/\d+)?", tok):
            coef = Fraction(tok)
            i += 1
            if i < len(side) and side[i] == "*":
                i += 1
                var = side[i]
                i += 1
                coeffs[var] = coeffs.get(var, Fraction(0)) + sign * coef
            else:
                const += sign * coef
        else:
            var = tok
            i += 1
            coeffs[var] = coeffs.get(var, Fraction(0)) + sign * coef
        sign = 1
    return coeffs, const


def parse_constraint(expr: str) -> tuple[dict[str, Fraction], str, Fraction]:
    """Return (coeffs, op, rhs) meaning sum coeffs*x  op  rhs with op in {'<=','='}."""
    toks = _tokens(expr)
    ops = [i for i, t in enumerate(toks) if t in ("<=", ">=", "=")]
    if len(ops) != 1:
        raise ValueError(f"need exactly one comparison in {expr!r}")
    k = ops[0]
    lc, lk = parse_linear(toks[:k])
    rc, rk = parse_linear(toks[k + 1:])
    coeffs = dict(lc)
    for v, c in rc.items():
        coeffs[v] = coeffs.get(v, Fraction(0)) - c
    rhs = rk - lk
    op = toks[k]
    if op == ">=":
        coeffs = {v: -c for v, c in coeffs.items()}
        rhs = -rhs
        op = "<="
    return {v: c for v, c in coeffs.items() if c != 0}, op, rhs


# ---------------------------------------------------------------- simplex

class LPResult:
    def __init__(self, status: str, value=None, point=None, ray=None):
        self.status, self.value, self.point, self.ray = status, value, point, ray


def simplex_max(variables: list[str], cons: list[tuple[dict, str, Fraction]],
                objective: dict[str, Fraction]) -> LPResult:
    n = len(variables)
    idx = {v: i for i, v in enumerate(variables)}
    rows, rhs, kinds = [], [], []
    for coeffs, op, b in cons:
        row = [Fraction(0)] * n
        for v, c in coeffs.items():
            row[idx[v]] = c
        rows.append(row)
        rhs.append(b)
        kinds.append(op)
    m = len(rows)
    n_slack = sum(1 for k in kinds if k == "<=")
    total = n + n_slack + m  # originals, slacks, artificials
    A = []
    s_col = n
    for i in range(m):
        row = rows[i] + [Fraction(0)] * (n_slack + m)
        if kinds[i] == "<=":
            row[s_col] = Fraction(1)
            s_col += 1
        b = rhs[i]
        if b < 0:
            row = [-x for x in row]
            b = -b
        row[n + n_slack + i] = Fraction(1)
        A.append(row + [b])
    basis = [n + n_slack + i for i in range(m)]
    art = set(basis)

    def pivot(r: int, c: int) -> None:
        pv = A[r][c]
        A[r] = [x / pv for x in A[r]]
        for i in range(m):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        basis[r] = c

    def run(cost: list[Fraction], allowed: set[int]):
        while True:
            # reduced costs for maximization: cost_j - c_B B^-1 A_j
            enter = None
            for j in sorted(allowed):
                if j in basis:
                    continue
                red = cost[j] - sum(cost[basis[i]] * A[i][j] for i in range(m))
                if red > 0:
                    enter = j
                    break  # Bland
            if enter is None:
                return "optimal", None
            best, leave = None, None
            for i in range(m):
                if A[i][enter] > 0:
                    ratio = A[i][-1] / A[i][enter]
                    if best is None or ratio < best or (ratio == best and basis[i] < basis[leave]):
                        best, leave = ratio, i
            if leave is None:
                return "unbounded", enter
            pivot(leave, enter)

    # Phase 1: maximize -sum(artificials)
    cost1 = [Fraction(0)] * total
    for j in art:
        cost1[j] = Fraction(-1)
    run(cost1, set(range(total)))
    if sum(A[i][-1] for i in range(m) if basis[i] in art) != 0:
        return LPResult("infeasible")
    # drive remaining zero-level artificials out of the basis where possible
    for i in range(m):
        if basis[i] in art:
            for j in range(n + n_slack):
                if A[i][j] != 0:
                    pivot(i, j)
                    break
    allowed = set(range(n + n_slack))
    cost2 = [Fraction(0)] * total
    for v, c in objective.items():
        cost2[idx[v]] = c
    status, enter = run(cost2, allowed)
    point = [Fraction(0)] * total
    for i in range(m):
        point[basis[i]] = A[i][-1]
    orig = {variables[j]: point[j] for j in range(n)}
    if status == "unbounded":
        direction = [Fraction(0)] * total
        direction[enter] = Fraction(1)
        for i in range(m):
            direction[basis[i]] = -A[i][enter]
        ray = {variables[j]: direction[j] for j in range(n)}
        return LPResult("unbounded", point=orig, ray=ray)
    value = sum(c * orig[v] for v, c in objective.items())
    return LPResult("bounded", value=value, point=orig)


# ---------------------------------------------------------------- families

def check_family(fam: dict, cons_raw: list[dict], parsed, variables: list[str]) -> list[str]:
    """Check an affine integer assignment for every integer t >= t_min."""
    if set(fam["assignment"]) != set(variables):
        raise ValueError(f"{fam['name']}: assignment must define every model variable exactly once")
    start = fam["t_min"]
    base, slope = {}, {}
    for name, expr in fam["assignment"].items():
        coeffs, const = parse_linear(_tokens(expr))
        if set(coeffs) - {"t"}:
            raise ValueError(f"{name}: unknown parameter in {expr!r}")
        slope[name] = coeffs.get("t", Fraction(0))
        base[name] = const + start * slope[name]
        if base[name].denominator != 1 or slope[name].denominator != 1:
            return [f"{name} is not integer-valued for all t >= {start}"]
        if base[name] < 0 or slope[name] < 0:
            return [f"{name} violates nonnegativity at or after t={start}"]

    failures = []
    for raw, (coeffs, op, rhs) in zip(cons_raw, parsed):
        lhs = sum(c * base[v] for v, c in coeffs.items())
        delta = sum(c * slope[v] for v, c in coeffs.items())
        if lhs > rhs or (op == "=" and lhs != rhs):
            failures.append(f"t={start}: violates {raw['expr']}")
        elif delta > 0 or (op == "=" and delta != 0):
            steps = (rhs - lhs) // delta + 1 if op == "<=" else 1
            failures.append(f"t={start + steps}: violates {raw['expr']}")
    return failures


def ray_tight(ray: dict, parsed, cons_raw) -> list[str]:
    tight = []
    for raw, (coeffs, op, _b) in zip(cons_raw, parsed):
        d = sum(c * ray.get(v, Fraction(0)) for v, c in coeffs.items())
        if d == 0 and any(ray.get(v, 0) != 0 for v in coeffs):
            tight.append(raw["expr"])
    return tight


def fmt(x: Fraction) -> str:
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--data", default=str(DEFAULT_DATA))
    ap.add_argument("--branch", required=True)
    ap.add_argument("--omit-row", help="omit a named row to reproduce an earlier relaxation")
    ap.add_argument("--profile", help="add the constraints from a named research profile")
    ap.add_argument("--add", action="append", default=[], help="candidate inequality to test")
    ap.add_argument("--objective", default=None, help="variable to maximize (default from data)")
    ap.add_argument("--audited-only", "--verified-only", dest="audited_only", action="store_true",
                    help="keep only rows marked kernel_audited: true")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    data = json.loads(pathlib.Path(args.data).read_text(encoding="utf-8"))
    br = data["branches"].get(args.branch)
    if br is None:
        print(f"unknown branch {args.branch}; known: {', '.join(data['branches'])}", file=sys.stderr)
        return 1
    profile = br.get("profiles", {}).get(args.profile, {})
    if args.profile and not profile:
        ap.error(f"unknown profile {args.profile!r} for {args.branch}")
    rows = br["constraints"] + profile.get("constraints", [])
    def is_audited(c: dict) -> bool:
        return bool(c.get("kernel_audited", c.get("verified", False)))
    cons_raw = [c for c in rows if is_audited(c) or not args.audited_only]
    cons_raw += [{"expr": e, "source": "candidate (--add)", "statement_checked": False, "kernel_audited": False} for e in args.add]
    if args.omit_row:
        if not any(c.get("id") == args.omit_row for c in cons_raw):
            ap.error(f"unknown row {args.omit_row!r}")
        cons_raw = [c for c in cons_raw if c.get("id") != args.omit_row]
    n_unaudited = sum(1 for c in cons_raw if not is_audited(c))
    parsed = [parse_constraint(c["expr"]) for c in cons_raw]
    variables = list(br["variables"])
    for coeffs, _, _ in parsed:
        for v in coeffs:
            if v not in variables:
                print(f"unknown variable {v!r} in constraints", file=sys.stderr)
                return 1
    obj_var = args.objective or br.get("objective", variables[0])
    if obj_var not in variables:
        ap.error(f"unknown objective {obj_var!r}")
    res = simplex_max(variables, parsed, {obj_var: Fraction(1)})

    fam_reports = []
    for fam in br.get("known_families", []):
        fails = check_family(fam, cons_raw, parsed, variables)
        fam_reports.append({"family": fam["name"], "survives": not fails, "first_failures": fails[:5]})

    out = {"branch": args.branch, "objective": obj_var, "n_constraints": len(cons_raw),
           "n_unaudited_constraints": n_unaudited,
           "status": res.status, "families": fam_reports}
    if args.omit_row:
        out["omitted_row"] = args.omit_row
    if args.profile:
        out["profile"] = args.profile
        out["profile_source"] = profile["source"]
    if res.status == "bounded":
        out["max"] = fmt(res.value)
        out["argmax"] = {k: fmt(v) for k, v in res.point.items()}
    if res.status == "unbounded":
        out["ray"] = {k: fmt(v) for k, v in res.ray.items() if v != 0}
        out["base_point"] = {k: fmt(v) for k, v in res.point.items() if v != 0}
        out["constraints_parallel_to_ray"] = ray_tight(res.ray, parsed, cons_raw)

    if args.json:
        print(json.dumps(out, indent=2))
    else:
        print(f"# count_lp — branch {args.branch} — maximize {obj_var} over {len(cons_raw)} constraints"
              f"{' (kernel-audited only)' if args.audited_only else ''}"
              f"{f' ({n_unaudited} unaudited)' if n_unaudited else ''}")
        if args.omit_row:
            print(f"row omitted: {args.omit_row}")
        if args.profile:
            print(f"profile: {args.profile} ({profile['source']})")
        print(f"status: {res.status.upper()}")
        if res.status == "bounded":
            print(f"max {obj_var} = {out['max']}  ⇒ combined with a floor above this, the branch closes.")
        elif res.status == "unbounded":
            print("recession ray (every recorded constraint holds along base + s·ray for all s ≥ 0):")
            print("  " + ", ".join(f"{k}={v}" for k, v in out["ray"].items()))
            print("constraints parallel to the ray (a cut must tighten one of these or add a new one):")
            for e in out["constraints_parallel_to_ray"]:
                print(f"  - {e}")
            print("Test both the direction and named affine families. A different solver ray alone does not establish a cut.")
        elif res.status == "infeasible":
            print("constraints are jointly infeasible ⇒ if all are proven, the branch is CLOSED. Verify sources!")
        for fr in fam_reports:
            state = "SURVIVES all constraints" if fr["survives"] else "is cut"
            print(f"family {fr['family']}: {state}")
            for f in fr["first_failures"]:
                print(f"  {f}")
    return {"bounded": 0, "unbounded": 3, "infeasible": 2}[res.status]


if __name__ == "__main__":
    sys.exit(main())
