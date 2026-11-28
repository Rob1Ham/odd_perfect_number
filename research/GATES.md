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

**Verdict.**
- If every step survives for some spoof → **KILL**. The argument only uses the multiplicative shape of σ and cannot produce a contradiction.
- Otherwise name the **first step a spoof fails**. That step is the real leverage, usually primality of a base or *closure* (every prime factor of every σ(p^e) lies in the support with exact valuation).

## G2 — Count-polyhedron gate

**Question.** Does a new linear count inequality cut off the unbounded direction of the polyhedron formed by all proven count inequalities on the branch?

**Procedure.**
1. Add the inequality to [count_constraints.json](count_constraints.json) under the branch, with its source.
2. Run `python3 research/tools/count_lp.py --branch <id>`.
3. Read off the result:
   - **Still unbounded with the same recession ray** → the inequality is `LIBRARY`, not progress.
   - **Ray cut, new ray reported** → partial progress. Record the new ray in [FLOOR_CEILING.md](FLOOR_CEILING.md).
   - **Bounded** → combined with an existing floor this may close the branch. Escalate to the Strategist immediately.

## G3 — Local-solvability gate

Applies to Diophantine sub-branches.

**Question.** Does the equation have a global solution, including degenerate ones (e.g. `q = 1`, `y = ±1`, `p = 0`), or a solution modulo every prime power?

**Verdict.** If yes, congruence and residue-class work **cannot** close the branch. Only shrinking density is possible. The task must instead aim at a size, descent, or non-congruence argument, or the branch must be marked `CONDITIONAL` on a named hypothesis.

> Example: `q^d + 1 = 2y²` has `(q, y) = (1, 1)` for every `d`. So the class `q ≡ 1, y ≡ 1` survives every modulus, and primes `q ≡ 1 (mod M)` always exist. → NO_GO §2.

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
