module

public import OddPerfect.TothCover
public import OddPerfect.TothIntervals
public import OddPerfect.DeficientPerfect
public import OddPerfect.DeficientFiniteness
public import OddPerfect.ParityDichotomy
public import OddPerfect.Dickson
public import OddPerfect.TothPrimeObstruction
public import OddPerfect.TothSplitExistence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# General Analytical Proof for Tóth Pairs & Deficient-Perfect Cofactors

This entry point collects the **purely analytical and structural** theorems for
Tóth's equation `σ(n) * (x + 1) = 2 * n * x` (`OddPerfect.TothPair n x`) and
deficient-perfect numbers `σ(n) + d = 2 * n` (`OddPerfect.DeficientPerfectWith n d`),
with **zero finite case-enumeration certificates** (`TothTrillion/Part*.lean` are
not imported here).

## Four Analytical Pillars
1. **Square-Cofactor & Deficient-Divisor Reduction** (`odd_toth_square_and_deficient_iff`):
   For odd `n` and odd `x > 1`, `σ(n)(x + 1) = 2nx` forces `n = m²`, `x ≡ 1 (mod 4)`,
   and establishes a bijection with proper deficient divisors `d = 2n - σ(n) = σ(n)/x`.
2. **Rational Abundancy Ceiling & Multiplier Monotonicity Cut**
   (`suffix_abundancy_strict_ceiling`, `analytic_interval_cut`):
   Bounds the unknown square-root suffix rank from `m < a^(k+1)` to prove
   `σ(m²)/m² < (a/(a - 1))^k`, bounds the a priori unbounded multiplier `x` below by
   `nextMultiplier D S`, and closes entire infinite `(m, x)` branches analytically
   via monotonicity of `x / (x + 1)`.
3. **Unbounded Rank-`k` Analytical Size Bound & Finiteness**
   (`unbounded_toth_radical_size_upper`, `finite_odd_toth_pairs_of_bounded_prime_count`,
   `finite_deficientPerfect_of_bounded_rank_and_two_val`):
   Proves `4(k + 1) x³ rad(n)² n ≤ (4(k + 1))^(4^(ω(n) + 1))` unconditionally without
   any `n ≤ 10^12` cap, yielding finiteness of odd `TothPair (n, x)` and
   `DeficientPerfectWith (n, d)` at every fixed prime-factor bound `ω(n) ≤ k` (as well
   as unrestricted-parity finiteness when `v₂(n) ≤ A`).
4. **Coprime Split & Linear-Euler (`N = q m²`) Source Isolation**
   (`proper_factor_and_unsplit_characterization`, `linear_euler_toth_unique_source`):
   Any non-absorbing coprime split `n = a * b` produces a nontrivial factor `gcd(x, σ(a))`
   of `x`; an odd coprime Tóth pair is unsplit iff a unique prime-power component absorbs
   `x`, forcing a unique source prime `r₀ ∣ m` with `q ∥ σ(r₀^(2 v_{r₀}(m)))` and
   `2q < 3 r₀^(2 v_{r₀}(m))` on every linear-Euler odd perfect candidate `N = q m²`.
-/

public section

namespace TothBreakout.Analytic

open OddPerfect ArithmeticFunction Finset

/-- Parity reduction and deficient-divisor equivalence for odd Tóth cofactors. -/
theorem odd_toth_square_and_deficient_iff {n : ℕ} (ho : Odd n) :
    ((∃ x, Odd x ∧ 1 < x ∧ TothPair n x) ↔ ∃ d, DeficientPerfectWith n d) ∧
    ∀ x, Odd x → TothPair n x → IsSquare n ∧ x % 4 = 1 :=
  ⟨(odd_deficientPerfect_iff_toth ho).symm, fun _ hx hp => toth_odd_cofactor_square hp hx⟩

/-- Strict analytical abundancy ceiling `σ(m²) / m² < (a / (a - 1)) ^ k` when every prime
factor of `m > 1` is at least `a` and `m < a ^ (k + 1)`. -/
theorem suffix_abundancy_strict_ceiling {m a k : ℕ} (hm : 1 < m) (ha : 1 < a)
    (hpr : ∀ p ∈ m.primeFactors, a ≤ p) (hk : m < a ^ (k + 1)) :
    (sigma 1 (m ^ 2) : ℚ) / (m ^ 2 : ℕ) < (primeAbundancyLimit a) ^ k :=
  Toth.suffix_strict_limit hm ha hpr hk

/-- Analytical closure of an entire suffix and unbounded-multiplier branch when the
rational abundancy ceiling stays at or below `t / (t + 1)` at `t = nextMultiplier D S`. -/
theorem analytic_interval_cut {B D S a k : ℕ} (ha : 1 < a) (cap : B < D * a ^ (k + 1))
    (empty : Toth.checkPoint D S)
    (cut : (S : ℚ) * (primeAbundancyLimit a) ^ k * ((Toth.nextMultiplier D S : ℚ) + 1) ≤
      2 * (D : ℚ) ^ 2 * (Toth.nextMultiplier D S : ℚ)) :
    Toth.Closed B D S a :=
  Toth.closed_interval ha cap empty cut

/-- Unbounded analytical radical-and-multiplier size bound for every odd `TothPair n x`
with `ω(n) ≤ k` (no `n ≤ 10^12` hypothesis). -/
theorem unbounded_toth_radical_size_upper {n x k : ℕ} (h : TothPair n x) (hx : Odd x)
    (h1 : 1 < x) (hk : n.primeFactors.card ≤ k) :
    (4 * (k + 1)) * x ^ 3 * (n.primeFactors.prod id) ^ 2 * n ≤
      (4 * (k + 1)) ^ (4 ^ (n.primeFactors.card + 1)) :=
  h.radical_size_upper hx h1 hk

/-- General analytical finiteness of nontrivial odd Tóth pairs `(n, x)` with `ω(n) ≤ k`,
bounding both the cofactor `n` and the multiplier `x` explicitly by `(4(k+1))^(4^(k+1))`. -/
theorem finite_odd_toth_pairs_of_bounded_prime_count (k : ℕ) :
    Set.Finite {v : ℕ × ℕ |
      Odd v.1 ∧ Odd v.2 ∧ 1 < v.2 ∧ v.1.primeFactors.card ≤ k ∧ TothPair v.1 v.2} := by
  let B := (4 * (k + 1)) ^ (4 ^ (k + 1))
  apply ((Set.finite_le_nat B).prod (Set.finite_le_nat B)).subset
  rintro ⟨n, x⟩ ⟨_, hx, h1, hk, h⟩
  have hr : 0 < n.primeFactors.prod id :=
    prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  have hpow : (4 * (k + 1)) ^ (4 ^ (n.primeFactors.card + 1)) ≤ B :=
    Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right hk 1))
  have hub : (4 * (k + 1)) * x ^ 3 * (n.primeFactors.prod id) ^ 2 * n ≤ B :=
    (h.radical_size_upper hx h1 hk).trans hpow
  have hx_pos : 0 < x := zero_lt_one.trans h1
  have hn_le : n ≤ B :=
    (Nat.le_mul_of_pos_left n
      (mul_pos (mul_pos (by omega) (pow_pos hx_pos 3)) (pow_pos hr 2))).trans hub
  have hx3 : x ≤ x ^ 3 := by
    calc x = x * 1 := (Nat.mul_one x).symm
         _ ≤ x * x ^ 2 := Nat.mul_le_mul_left x (pow_pos hx_pos 2)
         _ = x ^ 3 := by ring
  have hx3_mul : x ^ 3 ≤ x ^ 3 * ((4 * (k + 1)) * (n.primeFactors.prod id) ^ 2 * n) :=
    Nat.le_mul_of_pos_right (x ^ 3) (mul_pos (mul_pos (by omega) (pow_pos hr 2)) h.1.pos)
  have heq : x ^ 3 * ((4 * (k + 1)) * (n.primeFactors.prod id) ^ 2 * n) =
      (4 * (k + 1)) * x ^ 3 * (n.primeFactors.prod id) ^ 2 * n := by ring
  exact ⟨hn_le, hx3.trans (hx3_mul.trans (heq.symm ▸ hub))⟩

/-- Unrestricted-parity finiteness when both `ω(n) ≤ k` and `v₂(n) ≤ A` are bounded
(sharp against the infinite even family `2^a` in `OddPerfect.pow_two_deficientPerfect`). -/
theorem finite_deficientPerfect_of_bounded_rank_and_two_val (k A : ℕ) :
    Set.Finite {v : ℕ × ℕ | v.1.primeFactors.card ≤ k ∧ v.1.factorization 2 ≤ A ∧
      DeficientPerfectWith v.1 v.2} :=
  finite_deficientPerfect_pairs_of_bounded_prime_count_two_val k A

/-- Coprime-split factor extraction and exact single-absorber characterization for
unsplit odd coprime Tóth pairs. -/
theorem proper_factor_and_unsplit_characterization {n x : ℕ}
    (h : TothPair n x) (hx : Odd x) (h1 : 1 < x) (hc : n.Coprime x) :
    (∀ a b, n = a * b → a.Coprime b →
      ¬ sigma 1 a ∣ sigma 1 n / x → ¬ sigma 1 b ∣ sigma 1 n / x →
      1 < x.gcd (sigma 1 a) ∧ x.gcd (sigma 1 a) < x ∧ x.gcd (sigma 1 a) ∣ x) ∧
    ((∀ a b, n = a * b → a.Coprime b → sigma 1 a ∣ sigma 1 n / x ∨ sigma 1 b ∣ sigma 1 n / x) ↔
      ∃! r₀, r₀ ∈ n.primeFactors ∧ x ∣ sigma 1 (ordProj[r₀] n) ∧
        sigma 1 (ordCompl[r₀] n) ∣ sigma 1 n / x) :=
  ⟨fun _ _ hn hab ha hb => h.proper_factor_of_sigma_split hx h1 hn hab ha hb,
   tothPair_unsplit_iff_single_component_absorbs_multiplier h hx h1 hc⟩

/-- Linear-Euler (`N = q * m²`) transfer to an unsplit coprime Tóth pair `(m², q)`,
isolating the unique prime-power source `r₀^(2 v_{r₀}(m))` of `q` in `σ(m²)`. -/
theorem linear_euler_toth_unique_source {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    TothPair (m ^ 2) q ∧
    (sigma 1 (m ^ 2)).factorization q = 1 ∧
    ∃ r₀ ∈ m.primeFactors,
      q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)) ∧
      (sigma 1 (r₀ ^ (2 * m.factorization r₀))).factorization q = 1 ∧
      sigma 1 (ordCompl[r₀] (m ^ 2)) ∣ sigma 1 (m ^ 2) / q ∧
      2 * q < 3 * r₀ ^ (2 * m.factorization r₀) ∧
      ∀ r₁ ∈ m.primeFactors, q ∣ sigma 1 (r₁ ^ (2 * m.factorization r₁)) → r₁ = r₀ := by
  have hm2odd : Odd (m ^ 2) := ho.of_dvd_nat (hform ▸ dvd_mul_left (m ^ 2) q)
  have hc : (m ^ 2).Coprime q :=
    (hq.coprime_iff_not_dvd.mpr fun h => hqm (hq.dvd_of_dvd_pow h)).symm
  have hperf : (m ^ 2 * q).Perfect := by rwa [mul_comm, ← hform]
  exact ⟨tothPair_of_linear_euler hm2odd hq hc hperf,
    linear_euler_unique_q_source_and_bound ho hN hq hqm hform⟩

end TothBreakout.Analytic
