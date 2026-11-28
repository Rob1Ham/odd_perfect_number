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

## 8. Weighted square-source capacity (`IDEAS #7`) and pure multi-degree cyclotomic count-LPs on `ROOT`

- **Method.** Generalize the modulo-five square-source capacity bound to arbitrary exponents (`20S ≤ 14X + 6V + 10U + 2H`), or formulate multi-degree cyclotomic count-LPs (`e ∈ {2, 4, 6, 10}`, Vieta root caps, exact valuation conservation, residue classes mod 3, 4, 5, 7, 11) on `ROOT`.
- **Why it cannot finish.**
  1. `20S ≤ 14X + 6V + 10U + 2H` is completely vacuous when `S = 0` (every non-Euler prime has `e_p ≥ 4`), and strictly weaker than pure Vieta mod 3 (`3S ≤ 2X + V`) whenever `3H + 15U > V - X`.
  2. High-exponent targets `e_t = ℓ - 1` (`ℓ` prime) emit **no** compulsory outgoing multiplicity proportional to `e_t`: concrete primes `t ≡ 13 (mod 15)` (contributing `0` to `H`) have prime `Φ_ℓ(t)` (`Ω = 1`) for every prime `ℓ ∈ [7, 43]`, e.g. `(ℓ=7, t=73)`, `(ℓ=11, t=1213)`, `(ℓ=43, t=163)`. Composite `e_t + 1` also yields `O(1)` multiplicity (`e_t = 24, t = 22699` gives `Ω = 2`).
  3. Exact rational simplex proves multi-degree cyclotomic count-LPs on `ROOT` remain **UNBOUNDED** even with `S = 0` and `B_h = 0`, witnessed by explicit bipartite families `(|Q_4|, |R_6|) = (6k, 4k)` (`ω = 10k + 1`, `Ω = 48k + 1`) and `(|R_6|, |R_{10}|) = (5k, 3k)` (`ω = 8k + 1`, `Ω = 60k + 1`).
- **Used in.** Round 1 Track 2 experiment (`IDEAS #7`).
- **Allowed residual use.** None for closing `ROOT` via pure output-cardinality LPs. Any `ROOT` argument must remain nontrivial at `S = 0` (where `m` is odd powerful on `A1`) or exploit non-cardinality structure.

## 9. Single-shared-prime `g = r` abundancy-ratio contradiction on `A1`

- **Method.** On `N = q m²` with `g = gcd((q+1)/2, i_q) = r` prime and `v_r(m) = 1`, try to contradict `∏_{p | r²+r+1} (1 + 1/p + 1/p²) ≤ σ(u₀²)/u₀² = r(2 r h₀² - 1)/((r²+r+1) σ(h₀²))`.
- **Why it cannot finish.** Across `(r ≤ 500, h₀ < 300)`, `7,604` pairs (`723` with `q = 2 r h₀² - 1` prime) leave positive abundancy headroom, and `0` primes `r < 50,000` saturate `2r²/(r²+r+1)` (max `1.9564 < 1.9998`). Mod-8 residues are also unobstructed for every odd `r mod 8`.
- **Used in.** Round 1 Track 3 experiment.
- **Allowed residual use.** Structural elimination of `r₀ ∣ m_L` (`IDEAS #9`) and `3 ∤ N` exclusion of `(g = r, v_r(m) = 1)` are legitimate structural reductions, but abundancy headroom alone cannot eliminate `(r, h₀)` with `3 ∣ N`.

## 10. Unconditional local/count-LP closure of `IQ_MULTI` (`a > 1`, `|oddVal(I)| ≥ 2`)

- **Method.** Close `IQ_MULTI` (or replace the killed `ROOT` count-LP) via local congruence/abundancy/Jacobi checks on `I = ℓ₁ ℓ₂ t²` (`Subcase B`, `(q^d+1)/2 ≠ □`), or by coupling `WeightedLength.lean` (`d_factors ≤ |oddVal(I)| ≤ ω - 1`) into an `S = 0` multi-degree cyclotomic count-LP.
- **Why it cannot finish.**
  1. In Subcase B (`(q^d+1)/2 ≠ □`), simultaneous `(A_d = ℓ₁ v², B_d = ℓ₂ w²)` is locally unobstructed and survives abundancy and Jacobi checks: e.g. `(q = 17, a = 13, d = 7)` gives `A_7 = 25646167` (prime), `B_7 = 22796593 · 3²` (abundancy `1.4444 < 1.8824`), and `(q = 293, a = 5, d = 3)` gives `A_3 = 86143` (prime), `B_3 = 79 · 399²` (abundancy `1.7961 < 1.9932`), with `5` prime witnesses for `d = 3, y₀ < 3000`.
  2. Coupling `a ≥ 5`, `|oddVal(I)| ≥ 2`, and `d_factors ≤ |oddVal(I)| ≤ ω - 1` into the `S = 0` multi-degree cyclotomic count-LP leaves `ω` and `a` **UNBOUNDED** (exact ray `Q_4 = 4, R_6 = 1, ω = 5, Ω = 22`, even with `|oddVal(I)| = 2, a = 5` fixed).
  3. Subcase A (`(q^d+1)/2 = □`) across prime or composite `d` reduces elementarily (via `AlternatingPell`/`AlternatingBlock`) to every prime `p ∣ d` satisfying `p ≡ 1 (mod 8)`, `p ≥ 17`, `a ≥ 33`, and `x^p + 1 = 2 y²` (`x = q^(d/p) > 1`, `x ≡ 1 mod 16`), which requires external modular methods (Ivorra 2003 / Bennett–Skinner 2004; same barrier as §2).
- **Used in.** Round 1 `IQ_MULTI` scouting experiment.
- **Allowed residual use.** Generalizing `ExceptionalFermatObstruction` to `1 < x` to conditionally close all of Subcase A across `A_GT1`, or proving the elementary `d` prime forcing when `I = ℓ₁ ℓ₂ t²` and `(q^d+1)/2 ≠ □`.

## 11. Standalone quartic-reuse bounds (`5D ≥ 3k − 2` / `5 D_all ≥ 4k − 2`) and Ochem–Zelinsky complete-factorization counting on `A1_SPF`

- **Method.** Close `A1_SPF` (or cut `lower-square-count`) by sharpening the quartic-to-square chain target bound `4 D ≥ 2k − 1` → `5 D ≥ 3k − 2` → `5 D_all ≥ 4k − 2` (with per-residue mod-5/mod-4/mod-20/mod-40 prime-image bounds) or by applying Ochem–Zelinsky's complete-factorization tracking (`arXiv:2607.19746`) inside linear partition-count models.
- **Why it cannot finish.**
  1. `5 D_all ≥ 4k − 2` (`OddPerfect/QuarticChainModFiveTargetReuse.lean`) is sharp in both slope (`max k/D_all = 5/4`) and constant (`+2`, integer mod-40 witness `k = 8 + 20m, D_all = 6 + 16m, q_1 = 1`), yet because `Q₁₃ = k + q_Q + Q₁₃,3 + Q₁₃,5+` already enforces `k ≤ Q₁₃` and `D_all ≤ Q₁₃`, it cannot cut `lower-square-count` (`Q₁₃ = 2m, k ≥ m - 2`) or any `k = 0` family. (Also fails for `D_odd` alone via `A = p r², B = t u²`.)
  2. Even with all 28 fine conservation constraints (`farkas_int_reductions`), fine mod-5/mod-4 complete-factorization patterns, disjoint prime images `(S_p, k_A1, k_B1)`, non-cubeness, and per-residue upward root bounds, **both** `lower-square-count` and a `k = 0` affine family of slope `Ω/ω = 27/10` (`ω = 40t + 1, Ω = 108t + 1, S₅₀ = 0, S₅₁,col = 7t, S₅₁,rep = 19t, Q₁₃ = 14t, Q₂₃ = 0, k = 0`; verified in integers at `t = 12`) survive all constraints.
  3. Ochem–Zelinsky (`arXiv:2607.19746`) forces exponential growth only because restrained OPNs have fixed large-exponent support `|L(N)| = 1` (`rad(σ(s²)) ∣ q n`), whereas on `A1_SPF` the target set `Q₁₃` grows linearly with `ω` (`≥ (7/20) ω` on `27/10`, `ω/3` on `lower-square-count`).
- **Used in.** Round 1 Track 1b quartic-reuse & Ochem–Zelinsky experiment (`IDEAS #10`).
- **Allowed residual use.** `5 D_all ≥ 4k − 2` stands as an audited, sharp standalone quartic-reuse theorem (`OddPerfect/QuarticChainModFiveTargetReuse.lean`), but does not reset `A1_SPF`'s pivot clock. Closing `A1_SPF` requires non-cardinality mechanisms beyond linear partition counts.

## 12. Elementary global mechanisms on `ROOT` at `S = 0` (odd powerful `m`) — `ROOT` frozen

- **Method.** Seek a global non-cardinality obstruction on `ROOT` (`N = q^a m²`) remaining nontrivial when `S = 0` (every non-Euler prime has `e_p ≥ 4`), via abundancy/reciprocal sums (`I3`), cyclotomic primitive-divisor graphs (`Bang`/`Zsigmondy`) + `v_2(σ)` + `mod (3,4,5,7)` + quadratic reciprocity, `τ(N)` / Cohen–Sorli / Ore harmonicity, or `A1` powerful-`m` / powerful-`(q+1)/2` splits.
- **Why it cannot finish.**
  1. Raising `e_p` from `2` to `4` changes local abundancy by `1/p³ + 1/p⁴` (`≤ 6.84×10⁻⁶` for `p ≥ 53`) with no ceiling; exact `I3`-balanced all-`e_p = 4` witnesses exist at arbitrary `ω` (e.g. `ω = 60`, `p ≥ 17`, `∏ σ(p^e)/p^e = 2 - 9.47×10⁻⁵`; `ω = 120`, `p ≥ 29`).
  2. Unlike `e_p = 4` alone, `Φ_7(p)` (`e_p = 6`) hits all nonzero classes `{1, 2, 3, 4} (mod 5)`, and `3 ∣ N` gains ample `3`-adic slack (`σ(3⁴) = 11²`, `σ(3⁶) = 1093`, `σ(3⁸) = 13·757`, local `QR`-antisymmetric cycle `3⁴ → 11⁸ → 7⁸ → 3`). The `S = 0` Zsigmondy + `mod (3,4,5,7)` count-LP stays **UNBOUNDED** (`Q_4 = 6/7, R_6 = 1/7, ω = 1, Ω = 30/7`).
  3. `(e+1)⁴ / p^e ≤ 1` for every `p ≥ 5, e ≥ 4` even, so Cohen–Sorli (`τ⁴ ≤ N`) and Ore harmonicity hold automatically.
  4. On `A1` with `S = 0` (`g_R = 1` forcing `A = (q+1)/2` powerful, or `g = 1` forcing `p⁴ ∣ A`), `106` odd powerful `A ≤ 200,000` yield prime `q = 2A - 1` (`15` with `h₀ < 10,000` powerful), with verified local `q ∥ σ(r₀^{2e₀})` and abundancy-slack witnesses (e.g. `A = 169, q = 337, r₀ = 79, e₀ = 3`; `h₀ = 25, q = 1249, r₀ = 83, e₀ = 6`).
- **Used in.** Round 2 Track 2 (`ROOT`) pivot-checkpoint experiment (`exp_round2_root_s0.py`).
- **Allowed residual use.** Freeze `ROOT` (`active: false`); pursue the top-level split `A1` (`a = 1`) and `A_GT1` (`a > 1`) separately.

## 13. Coupled residue-partition + bipartite log-height LPs on `A1_SPF` — `A1_SPF` frozen

- **Method.** Close `A1_SPF` by coupling all 28 fine conservation rows (`farkas_int_reductions`), non-square cuts (`1 ≤ e_1 + e_3`), exact `Ω ≡ 1 (mod 4)` convex-hull / slot-residue cuts (including `w_{2,2} = 0`), disjoint mod-5 `A/B` prime injections, `HS_1`/`HS_2`, mod-4 parity, `IDEAS #9` (`r₀ ∤ (q+1)/2`), and node-strata bipartite log-height constraints.
- **Why it cannot finish.**
  1. Exact rational LP verification (`exp_track1_a1spf.py`) confirms `Ray_18` (`k = 0`) survives every coupled count, residue, non-square, mod-4, and bipartite log-height constraint, with an explicit verified 364-variable integer witness at `m = 100` (`ω = 1800`) and feasible node-strata log-heights (`min h_q ≈ 2360.15 log 3` vs bulk `1–3 log 3`).
  2. Even with `IDEAS #9` (`r₀ ∤ (q+1)/2`), a 2-step height-amplification loop `(q+1)/2 → s₁² → u₂ → r₀² → q` amplifies log-height by `× 8`, leaving `(7/8) log q` free in `(q+1)/2` to absorb all of `S₅₀`, `Q₂₃`, and `HQ`.
  3. `lower-square-count` (`m = 100`) is infeasible at `k = 0` but survives at `k ≥ m - 2` (`min_k = 98`) under both mod-4 parity and log-heights; general `k > 0` (`3d`) also stays unbounded, and Branch R2 on `A1_SPF` has 17 local prime witnesses (`61 ≤ r₀ < 3000`, all `A`-factors `≥ 53`).
- **Used in.** Round 1–2 Track 1 (`A1_SPF`) experiments (`exp_track1_a1spf.py`, `exp_quartic_5D_3k.py`, `exp_round2_a1.py`).
- **Allowed residual use.** Freeze `A1_SPF` (`active: false`); do not revisit `A1_SPF` without a genuinely non-LP, non-height arithmetic mechanism.
