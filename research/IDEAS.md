# Idea queue (informal proof first, then gates, then Lean)

Every candidate lemma starts here as an **informal** argument. No Neon prover is dispatched until the entry has a passing gate record ([GATES.md](GATES.md)) and a Skeptic verdict of `SURVIVES`.

Statuses: `PROPOSED → GATED → SURVIVES → FORMALIZING → DONE`, or `KILLED` (then move a summary to [NO_GO.md](NO_GO.md)).

| # | Idea | Branch | Status | Owner |
| --- | --- | --- | --- | --- |
| 1 | Target reuse bound for Φ₃/Φ₅ targets | `A1_SPF` | PROPOSED | Strategist |
| 2 | Largest-prime chain down to the least prime | `A1_SPF` | PROPOSED | Strategist |
| 3 | Ceiling u ≤ g(p) from the deficient square s² | `IQ_PRIME_POWER_EVEN` | PROPOSED | Strategist |
| 4 | Descent on the coprime half-successor system | `A1_G1` | PROPOSED | Strategist |
| 5 | Spoof-difference scan of the four ideas above | all active | PROPOSED | Skeptic |

---

## 1. Target reuse bound for Φ₃/Φ₅ targets (`A1_SPF`)

**Setting.** Sixth-power-free N: Euler exponent 1, other exponents 2 (block Φ₃(p) = p²+p+1) or 4 (block Φ₅(p)). Each non-Euler prime t receives total valuation exactly v_t(N) ∈ {2, 4} from all blocks.

**Arithmetic facts to exploit.**
- If t | Φ₃(p) with t ≠ 3, then p mod t is one of the **two** roots of x²+x+1, and these roots sum to −1.
- If t | Φ₅(p) with t ≠ 5, then p mod t is one of **four** roots.
- t | Φ₃(p) implies t ≤ p²+p+1. Large targets need large sources.
- Quartic-chain lemma (27 Nov assessment): Φ₃(Φ₅(w)) has two distinct primes of odd valuation.

**Question.** Do these facts force the number of distinct targets to grow *superlinearly* in the number of sources, or force a linear relation with a better coefficient than the current LP?

**Closure argument.** A new inequality that cuts the LP ray (gate G2), combined with ω ≥ 443, could make the LP bounded below the floor.

**Gates:** not yet run.

## 2. Largest-prime chain (`A1_SPF`)

**Sketch.** The largest prime P of N must be supplied by some block Φ₃(p) or Φ₅(p) with p ≥ P^{1/4}. Iterate downward. Then use Acquaah–Konyagin-type ranked bounds (`SecondLargestPrime`) and the abundancy identity Σ log(σ(p^e)/p^e) = log 2.

**Question.** Does the chain of forced suppliers run out before reaching the least prime, whose floor would be 10⁸ after an FNO replay?

**Closure argument.** A contradiction between the chain length and the least-prime floor.

**Gates:** not yet run. G4 needs the least-prime ceiling (FNO 10¹⁰⁰⁰, not formalized).

## 3. Ceiling u ≤ g(p) (`IQ_PRIME_POWER_EVEN`)

**Setting.** 2(p−1)s² = p^{2u+1} + p − 2 and σ(s²) = p^{2u}. So s² is a deficient odd square with abundancy just below 2 − 2/p, and it has ≥ 13 repunit components σ(r^{2e}) = p^β.

**Question.** Does a Dickson-type prefix-gap argument (as in `Dickson.lean` / `NearPerfectFinite.lean`) bound u in terms of p and ω(s)? If an argument only works for bounded ω(s), what forces ω(s) small?

**Closure argument.** Such a ceiling meets the existing ceilings p < 6^u and p ≤ 8(u+1)·128^{√(2u)} (see FLOOR_CEILING).

**Kill criterion.** If every route needs linear forms in logarithms (Baker), record the branch in NO_GO and freeze it.

**Gates:** not yet run.

## 4. Descent on the coprime half-successor system (`A1_G1`)

**Setting.** u² = W·σ(h²), σ(u²) = W(2h² − 1). Also h₀ + 2 ≤ u₀, W = 1 ↔ ω(u) = 1, and W ≥ 5113 on sixth-power-free N.

**Question.** Does a prime-by-prime analysis of σ(u²) = W(2h²−1) produce a smaller triple (h′, u′, W′) satisfying the same system? Alternatively, do the size relations contradict each other?

**Closure argument.** Infinite descent closes `A1_G1`.

**Gates:** not yet run. G1 is critical: check whether the system has spoof solutions with composite "primes".

## 5. Spoof-difference scan (all active)

For each idea above, find the first step that the Descartes, Voight and BYU spoofs fail. Ideas with no failing step are killed at G1.
