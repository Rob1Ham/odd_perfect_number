# Methods that cannot finish (no-go record)

This file records methods that **cannot** close a branch of [BRANCH_MAP.md](BRANCH_MAP.md), with the reason, so no future round repeats them. It is a research asset: this kind of knowledge rarely appears in the literature.

Each entry gives:
- **Method**: what was tried.
- **Why it cannot finish**: a proof sketch or counterexample.
- **Used in**: which waves or modules.
- **Allowed residual use**: what is still legitimate.

Proven results produced by these methods stay in the library. They are classified `LIBRARY` in [CLAIMS.md](CLAIMS.md) and are not counted as progress.

---

## 1. Finite-residual bridges B1–B3 (rank cap / index cap / index-multiplicity cap)

- **Method.** Prove a uniform cap `K₀`, then discharge
  `hempty : ∀ N ≤ (max 1 (productLabelBound (2K₀) (2K₀) 1))^K₀, ¬(Odd N ∧ N.Perfect)`
  (`not_existsOddPerfect_of_rank_cap`, `…_componentIndex_cap`, `…_componentIndex_multiplicity_cap` in `OddPerfect/GlobalObstruction.lean`).
- **Observed limitation.** Each cap would imply finiteness. The formal reductions separately require an emptiness proof up to the resulting bound. Finiteness permits some odd perfect numbers.
- **When to revisit.** A concrete cap and a plausible certificate or proof covering its residual. A direct contradiction with an existing floor is one way to do this.

## 2. Residue-class sieves on `q^d + 1 = 2y²` (exceptional Euler index `I = ℓt²`, a > 1)

- **Method.** Exclude residue classes of `q` (48 → 148 classes, mod-8/mod-5 refinements, ℤ√2 split/inert prime sieves).
- **Why it cannot finish.** `(q, y) = (1, 1)` solves `q^d + 1 = 2y²` for every `d`. For any modulus `M`, the class `q ≡ 1, y ≡ 1 (mod M)` is therefore never excluded, and Dirichlet supplies primes `q ≡ 1 (mod M)`. No finite congruence table closes the branch (gate G3).
- **What does close it.** Hirakawa Lemma 2.5 uses Ivorra for prime exponent at least 7. Bennett–Skinner Proposition 8.1 also classifies the precise positive-integer equation needed here. The local reduction still takes this input as a hypothesis. [Sources and interface](STRATEGY_REVIEW.md#evidence-and-coverage)
- **Used in.** `ExceptionalFermatCongruences`, `ExceptionalFermatHigherSieve`, `ZsqrtTwo*Sieve*`, `ZsqrtTwoCombinedFirstSecondBlockSieve`, Waves 5–Q.
- **Allowed residual use.** Keep `ExceptionalFermatObstruction` (`OddPerfect/ExceptionalFermatReduction.lean`) as an **explicit named hypothesis**. The branch is `CONDITIONAL` in BRANCH_MAP. Any future work must be a non-congruence argument or a port of the modular input.

## 3. Floor-raising on unbounded parameters without a ceiling

- **Method.** Raise lower bounds on:
  - `j` (36207 → 1.3·10¹⁶);
  - `u` in `i_q = p^{2u}` (u ≥ 6.5·10¹⁵);
  - the Padé constants (`20p` → `10¹²p` → `(10¹⁰⁰⁰)⁶ p < 6^u`);
  - `d` (17 → 73 → 241);
  - minimum prime factors of `l, r, z`;
  - `|S₅₁|`, `|Q₁₃|`, `E`, `W`.
- **Why it cannot finish.** A floor closes a branch only when it meets a ceiling on the same parameter (gate G4). For `i_q = p^{2u}` every ceiling has the form `p < f(u)`, and no incompatible ceiling on u has been established here. For `d`, `l`, `r`, `W`, `|S₅₁|` there is no ceiling at all. Both sides can grow forever.
- **Used in.** Prime-power index series (S3, S7, S12, S14, S15, S18, S19), Padé series (Waves F–O), exceptional parameter floors.
- **Allowed residual use.** Only when [FLOOR_CEILING.md](FLOOR_CEILING.md) names a ceiling and the task states the gap.

## 4. Linear count-inequality tightening without arithmetic input (sixth-power-free branch)

- **Method.** Sharpen linear inequalities among `ω, Ω, |S₅₀|, |S₅₁|, |Q₁₃|, |Q₂₃|, E, M`.
- **Observed limitation.** The Wave K assessment assignment survives the historical baseline projection. The separate target-reuse profile excludes it. A second unbounded direction survives that profile and fails the audited modulo-five inequality. A third survives the combined projection.
- **Scope.** These are limitations of specified constraints. Further linear inequalities with arithmetic content can remove those directions. Reproduce the families and study their residuals in the [strategy review](STRATEGY_REVIEW.md#what-survives-the-calculation).

## 5. Universal identities presented as obstructions

- **Method.** Proving facts true for all `N`, or for all odd `N`, inside "Obstruction" modules.
- **Examples.**
  - `(ζ * id) N = 2N` is σ(N) = 2N restated.
  - `∑ μ(d)σ(N/d) = N` and `∑ μ(d)² = 2^ω` hold for every N.
  - `mersenne p % 4 = 3`.
  - Mathlib-coverage-driven integrations (`LucasLehmerMersenneParityBridge`, `MoebiusInversionAndCyclotomicExpandLaws`).
- **Why it cannot finish.** A statement true for every N cannot distinguish odd perfect numbers from anything.
- **Allowed residual use.** As library helpers with neutral names. The word *Obstruction* is reserved for conclusions that are `False` or that exclude a named BRANCH_MAP node.

## 6. Brute-force certificate trees without a structural residual

- **Method.** Large `PartNNN.lean` factor-chain trees (966 certificate chunks).
- **Why it cannot finish.** Factor chains only exclude bounded prefixes. Without a structural cap they raise floors (see §3).
- **Allowed residual use.** Formal replays of published frontier results (Ochem–Rao, Fletcher–Nielsen–Ochem, Goto–Ohno). These are terminating deliverables listed in [ROADMAP.md](ROADMAP.md) §3.

## 7. Unordered supplier iteration

If a prime target P divides Φ₅(p), the polynomial gives P ≤ Φ₅(p) < (p+1)⁴. The prime value Φ₅(4153) itself exceeds 4153⁴. The proposed stronger lower bound p ≥ P^(1/4) fails. Iterating the weaker bound also needs a strict descent, a termination measure and treatment of Euler supply. The known least-prime interval supplies none of these. [Local control](../OddPerfect/QuarticChainBaselineAndReuse.lean)
