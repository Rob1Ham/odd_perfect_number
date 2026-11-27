---
name: carbon-reevaluation-loop
description: >-
  Runbook for the Carbon Coordinator session to continually evaluate proof progress,
  cross-check Mathlib theorem leverage, dispatch parallel Neon (`Model="flash"`) proof
  and audit subagents, and steer stepping-stone theorems toward full unconditional
  resolution of `OddPerfect.existsOddPerfect`.
---

# Carbon Continuous Reevaluation & Resolution Loop

Use this skill whenever coordinating multi-round research on `odd_perfect_number` from a Carbon (`pro`) session. Operate with full conviction that `OddPerfect.existsOddPerfect` admits an unconditional, axiom-pure Lean 4 proof reachable via our Stepping-Stone $\to$ Global Obstruction architecture (`research/ROADMAP.md`, `research/WHITEBOARD.md`).

## Cycle Architecture (5 Phases per Round)

### Phase 1: Quantitative & Architectural Reevaluation (Carbon)
Run the progress evaluator and inspect `research/ROADMAP.md` and `research/WHITEBOARD.md`:

```sh
python3 research/tools/evaluate_progress.py --dashboard research/PROGRESS_DASHBOARD.md --record
```

Check five strategic gates:
1. **Tier 0 Ready-Harvest Gate**: Any staged structural or stepping-stone track at `≥ 70%` fresh `.olean` (starting with `NearPerfectFinite` and `IndexBound2379`, then `PrimeReciprocalLog`, `ZelinskyReciprocal`, `SecondLargestPrime`, `QuasiperfectSupport`, `EvenIndexExponent256`) gets an immediate `neon-harvester` / `neon-auditor` slot before spawning new work.
2. **Anti-Bloat Gate**: Freeze new `PartNNN.lean` brute-force tree generation unless discharging an explicit finite residual set produced by a structural rank/index cap (`B1`–`B3` on `research/WHITEBOARD.md`). Keep legacy computational harvests (`SizeBound300`, `DeficientFour`) confined to at most one background harvester slot.
3. **Mathlib Leverage Gate**: Run `python3 research/tools/mathlib_kb.py overlap` and search underused Mathlib modules (`Analysis.SpecialFunctions.Log`, `RingTheory.Polynomial.Cyclotomic`, `NumberTheory.Pell`, `NumberTheory.LegendreSymbol.JacobiSymbol`).
4. **Counterexample Filter Gate**: Before dispatching a `neon-prover` on a candidate global lemma, verify on `research/WHITEBOARD.md` that it is not trivially refuted by Descartes's spoof (`198585576189`), Tóth's cofactor (`9018009`), Johnson's near-perfect square (`173369889`), or local valuation cycles (`3→11→7→3`, `7²→19→151→7`), and identify which non-spoofable invariant (`I1`–`I4`) makes it hold for genuine odd perfect numbers.
5. **Bridge Alignment Gate**: Every new Tier 1 / Tier 2 task must advance a specific Stepping Stone (`S1`–`S5` in `research/ROADMAP.md`) or one of the Four Global Bridges (`B0` direct closed-support contradiction, `B1` $\omega(N)$ upper cap, `B2` $i_p$ upper cap, `B3` $\Omega(i_p)$ upper cap).

### Phase 2: Mathlib Reconnaissance (Neon Scout)
Before launching `neon-prover` on a nontrivial structural or open theorem, dispatch `neon-mathlib-scout` (`Model="flash"`) or run `research/workflows/neon_proof_round.py` so the prover receives verified Mathlib imports and exact signatures upfront.

### Phase 3: Parallel Proof & Harvest Execution (Neon Workers)
Keep up to **3–4 concurrent Neon subagents** (`invoke_subagent(..., Model="flash")` or `run_workflow`) on strictly disjoint files:
- **Slot A (Tier 0 Harvest & Integration)**: `neon-harvester` / `neon-auditor` clearing ready staged tracks (`NearPerfectFinite`, `IndexBound2379`, analytic/prime-rank bridge, `EvenIndexExponent256`).
- **Slot B (Tier 1 Open Stepping-Stone Prover)**: `neon-prover` proving an open stepping-stone theorem (`S1` parity dichotomy & bounded-$v_2$ finiteness, `S2` `OreHarmonic` fixed-rank finiteness & $\omega \in \{2,3\}$ exclusion, `S3` unconditional $i \ne p^j$ obstructions via $2(s-1)(s+1)=p\sigma(p^{2u-1})$, `S4` $I \ne \ell t^2$ / Dris regimes, `S5` Zelinsky slope + log-reciprocal pinch).
- **Slot C (Tier 2 Global Obstruction / Adversarial Audit)**: `neon-prover` prototyping a global Bridge `B0`–`B3` lemma from `research/WHITEBOARD.md`, paired with `neon-auditor` challenging hypothesis strength, edge cases, and axiom purity.

### Phase 4: Coordinator Synthesis & Kernel Gate (Carbon)
When Neon workers return:
1. Re-index declarations: `python3 research/tools/mathlib_kb.py index && python3 research/tools/mathlib_kb.py domain-map`
2. Wire `PASS`-audited modules into `OddPerfect.lean`.
3. Run the authoritative gate:
   ```sh
   lake build && lake lean research/Audit.lean
   ```
4. Update `research/ROADMAP.md`, `research/WHITEBOARD.md`, `research/LEDGER.md`, `research/CORPUS.md`, and `research/PROGRESS_DASHBOARD.md`.

### Phase 5: Strategic Pivot Check (Carbon)
- **Advancing Toward Resolution**: Staged stepping stones move to `AUDITED`, new open Tier 1 theorems compile with `0` `sorry`, or a global conservation/reciprocity/slope inequality tightens Bridges `B0`–`B3`.
- **Local Minimum Detected**: Tactic timeouts, splintering subcases, or local edge rules failing on the Counterexample Filter Bank. Record the exact obstruction on `research/WHITEBOARD.md` immediately and pivot to coupling a second global invariant (`I1`–`I4`).
