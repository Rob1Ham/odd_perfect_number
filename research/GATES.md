# Pre-dispatch gates

Every candidate lemma in [IDEAS.md](IDEAS.md) must pass all four gates **before** a Neon prover is dispatched. Record each gate's outcome in the idea's entry. A failing gate is a successful result: move the idea to [NO_GO.md](NO_GO.md) with the evidence.

A task that passes the gates must also carry a one-line **closure argument**: how its result could close a node of [BRANCH_MAP.md](BRANCH_MAP.md). The argument is copied verbatim into the prover prompt and into the module docstring.

---

## G1 — Spoof gate

**Question.** Does the argument still go through if one base is allowed to be composite or negative?

**Test objects** (see the filter bank in [WHITEBOARD.md](WHITEBOARD.md#counterexample-filter-bank)):
- Descartes: `3²·7²·11²·13²·22021` (22021 = 19²·61 treated as a prime base)
- Voight: `3⁴·7²·11²·19²·(−127)`
- The 21 primitive odd spoofs with fewer than seven bases (Andersen et al., *Odd, spoof perfect factorizations*, J. Number Theory)
- Tóth cofactor `(9018009, 819)` and Johnson near-perfect `173369889`

**Verdict.** Test a proposed contradiction against an object satisfying its stated hypotheses. A spoof outside the branch is a control for particular steps. A helper may hold for every spoof and still be useful when combined with an actual-prime or exact-valuation hypothesis. Record where the full argument uses that distinction.

## G2 — Count constraints

Run the public projection, any relevant separate profile, and the trial inequality with `--add`. Keep conjectural rows out of the public baseline. Compare the same affine family or direction before and after adding the row. A changed simplex witness alone does not show that the old direction was removed. For an affine inequality check its slope on the old direction and its value at a feasible starting point. A positive violation in the slope cuts the direction. A change in the constant alone can still exclude an exact arithmetic subcase.

Report whether a consistent family of unbounded rank survives. Rational feasibility describes the relaxation. Bounded rank requires an additional contradiction or a discharged finite residual. An infeasible system proves an exclusion only after each constraint and its hypotheses have been checked against actual candidates. See the reproducible runs in the [strategy review](STRATEGY_REVIEW.md#what-survives-the-calculation).

## G3 — Local solvability

Test the equation together with all conditions encoded in the proposed congruence argument. For the isolated equation `q^d + 1 = 2y²`, the class of (1,1) survives reduction at every modulus. This rules out excluding every class by reducing that equation alone. The integer 1 fails the primality hypothesis on q. Additional equations or valuation information may remove its congruence class.

## G4 — Floor/ceiling gate

**Question.** A new lower bound (floor) on a parameter is useful only if it can meet an upper bound (ceiling) on the same parameter. Which ceiling does this floor approach?

**Procedure.** Look up the parameter in [FLOOR_CEILING.md](FLOOR_CEILING.md).
- **No ceiling exists** → **FREEZE** the floor-raising task. Optionally redirect it into finding a ceiling.
- **A ceiling exists** → state the gap before and after.

---

## Gate record template (paste into the IDEAS entry)

```
G1 spoof:      PASS — first failing step: <step> (fails for Descartes because 22021 composite)
G2 count-LP:   N/A | PASS (ray cut: old <ray>, new <ray>) | LIBRARY
G3 local:      N/A | PASS (no degenerate/local solution because …) | FAIL (witness …)
G4 floor/ceil: N/A | PASS (meets ceiling …) | FREEZE
Skeptic:       SURVIVES | KILL (<reason>) | UNCLEAR
Closure arg:   <one line>
```
