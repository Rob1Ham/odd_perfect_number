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
- **Why it cannot finish.**
  1. Each cap implies there are only finitely many odd perfect numbers (Dickson), itself an open problem of comparable difficulty.
  2. B3 is *stronger* than B1 (`ω ≤ 4K₀ + 4`). By `Ω(i_p) = 1 + Ω(N) − e_p − Ω(σ(p^{e_p}))`, a cap `Ω(i_p) ≤ K₀` forces one prime power to carry almost all prime factors of N. On the sixth-power-free branch (e_p ≤ 4) it is impossible outright.
  3. `hempty` ranges over a doubly-exponential bound and cannot be computed. It can only be discharged by a proven floor above the cap, which makes the bridge a direct contradiction (B0) in disguise.
- **Used in.** Tier 2 framing since Wave 4; `GlobalObstruction`, `GlobalLogSlopePinch`, the drop-conservation modules.
- **Allowed residual use.** As bookkeeping lemmas only. A cap is useful exclusively when it falls **below a formalized floor on the same branch**.

## 2. Residue-class sieves on `q^d + 1 = 2y²` (exceptional Euler index `I = ℓt²`, a > 1)

- **Method.** Exclude residue classes of `q` (48 → 148 classes, mod-8/mod-5 refinements, ℤ√2 split/inert prime sieves).
- **Why it cannot finish.** `(q, y) = (1, 1)` solves `q^d + 1 = 2y²` for every `d`. For any modulus `M`, the class `q ≡ 1, y ≡ 1 (mod M)` is therefore never excluded, and Dirichlet supplies primes `q ≡ 1 (mod M)`. No finite congruence table closes the branch (gate G3).
- **What does close it.** Hirakawa (arXiv 2309.17084) uses results on generalized Fermat equations `x^n + y^n = 2z²` (Bennett–Skinner / Darmon–Merel type). Those rest on modularity and Galois representations, which are absent from the pinned Mathlib.
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
- **Why it cannot finish.** A floor closes a branch only when it meets a ceiling on the same parameter (gate G4). For `i_q = p^{2u}` every ceiling has the form `p < f(u)`, and no ceiling `u ≤ g(p)` exists. For `d`, `l`, `r`, `W`, `|S₅₁|` there is no ceiling at all. Both sides can grow forever.
- **Used in.** Prime-power index series (S3, S7, S12, S14, S15, S18, S19), Padé series (Waves F–O), exceptional parameter floors.
- **Allowed residual use.** Only when [FLOOR_CEILING.md](FLOOR_CEILING.md) names a ceiling and the task states the gap.

## 4. Linear count-inequality tightening without arithmetic input (sixth-power-free branch)

- **Method.** Sharpen linear inequalities among `ω, Ω, |S₅₀|, |S₅₁|, |Q₁₃|, |Q₂₃|, E, M`.
- **Why it cannot finish.** The 27 November assessment exhibited an explicit unbounded family satisfying all the Wave K count constraints. `python3 research/tools/count_lp.py --branch A1_SPF` reproduces this as a recession ray. New inequalities of the same kind do not cut it:
  - S₅₁ = S₅₁_col = t, Q₁₃ = t, others 0;
  - ω = 2t+1, Ω = 6t+1, E = M = 2t.
- **Used in.** S5, S6, S11, S16, S17, Waves G–Q (`SixthPowerFree*Pinch`).
- **Allowed residual use.** Only inequalities that pass gate G2 (they cut the current ray). Expect such cuts to require *arithmetic* information about which primes are targets, not counts alone.

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
