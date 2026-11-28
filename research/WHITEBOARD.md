# Whiteboard: current mathematics only

Keep this file under about 120 lines. It holds the settled framework and the **current** sketches. Clear finished material every round: proven results go to [CLAIMS.md](CLAIMS.md) and [LEDGER.md](LEDGER.md), dead ideas go to [NO_GO.md](NO_GO.md), candidate ideas live in [IDEAS.md](IDEAS.md). The previous whiteboard, with the Waves 1–Q lock-in list, is archived at [archive/WHITEBOARD_2026-11-27.md](archive/WHITEBOARD_2026-11-27.md).

---

## 1. The closed equation

Write N = q^a ∏_{p∈S∖{q}} p^{e_p} (Euler form, q ≡ a ≡ 1 mod 4, e_p even). Perfection is

$$2\,q^a\!\!\prod_{p\in S\setminus\{q\}}\! p^{e_p} \;=\; \prod_{p\in S}\;\prod_{\substack{d\mid e_p+1\\ d>1}} \Phi_d(p).$$

If r divides Φ_d(p) with d > 2, then either r ≡ 1 (mod d), or r is the largest prime factor of d and r ∥ Φ_d(p).

Component index: i_p = σ(N/p^{e_p})/p^{e_p} = 2N/(p^{e_p}σ(p^{e_p})). Conservation law: Ω(i_p) + e_p + Ω(σ(p^{e_p})) = 1 + Ω(N).

## 2. The non-spoofable properties

A proof must use at least one property that spoofs violate (see gate G1):

- **I1. Primality of the bases.** Spoofs use composite bases (Descartes: 22021 = 19²·61) or negative bases (Voight: −127).
- **I2. Closure with exact valuations.** Every odd prime factor of each σ(p^{e_p}) lies in S. Divide the Euler block by 2. The resulting blocks multiply to N, and their incoming valuations at each r in S sum to e_r. Spoofs leak prime factors outside the base set.
- **I3. Abundancy balance.** ∏ σ(p^e)/p^e = 2, hence ∑ 1/p < log 2 < ∑ 1/(p−1). On its own this is satisfied by spoofs; it is useful only combined with I1/I2.
- **I4. Prefix-gap rigidity.** No proper sub-product of local abundancies hits a forbidden rational target (`Dickson.lean`, `NearPerfectFinite.lean`).

The count models omit some relations between a source and its actual target primes. The modulo-five test uses such a relation and still admits an unbounded count family.

## Counterexample filter bank

Every candidate global lemma is tested against these (gate G1):

1. **Descartes spoof** `198585576189 = 3²·7²·11²·13²·19²·61`, formal base `22021`. It passes Euler form, Touchard, 105 ∤ N and formal balance. It fails primality of 22021, the fourth-power requirement and Ore harmonicity.
2. **Voight negative-base spoof** `3⁴·7²·11²·19²·(−127)`.
3. **BYU primitive odd spoofs.** All 21 with fewer than seven bases, plus the infinite families (Andersen et al., *Odd, spoof perfect factorizations*, J. Number Theory).
4. **Tóth / deficient-perfect cofactor** `(9018009, 819)`, multiplier 22021. At a = 1, m² is odd deficient-perfect with omitted divisor i_q.
5. **Johnson near-perfect** `173369889 = 3⁴·7²·11²·19²`, σ(n) = 2n + 2751903.
6. **Local cycles** `3 → 11 → 7 → 3` and `7² → 19, 19⁴ → 151, 151² → 7`. They cycle locally only because they leak primes (13, 19, …).
7. **Quartic-chain controls** w = 4153 and w = 22639. Both give a prime s = Φ₅(w), and 73 divides s²+s+1 to the first power in both chains. This is local reuse of a target (27 Nov assessment).
8. **Shared Φ₃/Φ₅ target** 31 | Φ₃(191) and 31 | Φ₅(97).

## 3. Known reformulations (not routes)

The bridges B1 (cap on ω), B2 (cap on i_p) and B3 (cap on Ω(i_p)) are correct implications (`not_existsOddPerfect_of_*` in `GlobalObstruction.lean`). Each cap would imply finiteness. The formal reductions separately require an emptiness proof up to the resulting bound. Its feasibility depends on the cap and the method. See NO_GO §1.

## 4. Current sketches

Round 2 completed two audited structural reductions and froze both count-LP/elementary global tracks after exhaustive refutations (see [NO_GO.md](NO_GO.md) §§8–13, [IDEAS.md](IDEAS.md)):
- **`A1` (OPEN, active):** `OddPerfect/LinearEulerRightSourceForcing.lean` eliminates `r₀ ∣ m_L` unconditionally across all `g ≥ 1`, and `OddPerfect/LinearEulerRightBranchStructure.lean` restricts Branch R1 (`r₀ ∣ g_R ⇔ r₀ ∣ (q+1)/2`) to `r₀ ≡ 1 mod 4` (`r₀ = 3 ⇒ q ≡ 1 mod 12`), non-Fermat `4ℓ ∣ q − 1`, `A < r₀^(v_{r₀}(I))`, `k_R ≤ 2b`, and `b = 1 ⇒ k_R = 1`. All 7 remaining local `(R1/R2)×(g_L, g_R)` regimes admit exact-`Fraction` abundancy `< 2` witnesses; closing `A1` requires a genuine non-local Diophantine descent on `(h₀, u₀, g_L, g_R, W_R)`.
- **`A_GT1` (OPEN, active):** `OddPerfect/HighEulerHalfSumReduction.lean` conditionally closes the entire Subcase A (`(q^d + 1)/2 = □`, prime and composite `d`) across `A_GT1` on `PrimePowerFermatObstruction` (externally Ivorra 2003 / Bennett–Skinner 2004 modular forms, absent from pinned Mathlib), and unconditionally forces `d.Prime` on Subcase B (`¬ IsSquare ((q^d + 1)/2)`) of `I = ℓ₁ ℓ₂ t²`. Prime-`d` Subcase B retains local abundancy/Jacobi witnesses `(17, 13, 7)` and `(293, 5, 3)` (`NO_GO §10`).
- **Frozen tracks (`ROOT`, `A1_SPF`):** `ROOT` is frozen (`NO_GO §§8, 12`: `S = 0` powerful-`m` barrier); `A1_SPF` is frozen (`NO_GO §§11, 13`: `Ray_18` 364-var integer + bipartite log-height witness at `ω = 1800` and `lower-square-count` survive every linear count, residue, complete-factorization, and log-height LP).
