module

public import OddPerfect.IndexBound2379
public import OddPerfect.FermatIndexObstruction
public import OddPerfect.EulerExceptionalObstruction
public import OddPerfect.ExceptionalBlockSquare
public import OddPerfect.ExceptionalBranchClosure
public import OddPerfect.HirakawaClosure
public import OddPerfect.ExceptionalFermatCongruences
public import OddPerfect.ExceptionalFermatHigherSieve
public import OddPerfect.ZsqrtTwoFermatDescent

/-!
# Lower Bounds, Non-Fermat Support, and `ℤ√2` Descent for the Euler Index

Standalone public entry point for `euler-index-breakout`, packaging:
1. `euler_index_ge_2379`:
   Sharpens Broughan, Delbourgo, and Zhou's (2013) unconditional bound
   `σ(m²) / q^a ≥ 315` by `7.5×` to `2379 ≤ σ(m²) / q^a` and `2379 * q^a < 2 * m²`.
2. `odd_component_index_has_nonfermat_prime` & `euler_index_odd_valuation_escape`:
   Proves every odd component index (hence every Euler index across all `a ≥ 1`
   and arbitrary multiplicities) is divisible by a non-Fermat prime (`∀ k, p - 1 ≠ 2^k`),
   and for `a > 1` admits an odd-valuation prime `p ∤ q - 1`.
3. `hirakawa_exceptional_branch_size_and_sieve` & `hirakawa_second_block_pell_fundamental`:
   On Hirakawa's (2024) prime-times-square Euler-index branch `I = l * t²` (`a > 1`),
   proves `10 ^ 740 < N` unconditionally across all `a > 1`, excludes `148` prime-modulus
   Fermat residue classes (including `q % 7 ∈ {2, 4}` and `q % 5 = 3`), proves
   `¬ 3 ∣ N ∧ ¬ 5 ∣ N → 241 ≤ d ∧ 481 ≤ a`, and verifies `Pell.IsFundamental` in `ℤ[√(2q)]`.
4. `hirakawa_zsqrtTwo_frobenius_descent`:
   Establishes `EuclideanDomain (ℤ√2)`, full unit classification `±(1 + √2)^n`,
   reduced `d`-th power descent `1 + y√2 = (1 + √2)^k * α^d` with `1 ≤ |k| ≤ (d - 1)/2`,
   and mod-`d` Frobenius congruence `α ≡ (1 + √2)^(-k) [ZMOD d]`.
-/

public section

namespace EulerIndexBounds

open OddPerfect ArithmeticFunction

/-- **Unconditional Euler Component Index Lower Bound `2,379`**:
For every odd perfect number `N = q ^ a * m ^ 2` in Euler form,
`2379 * q ^ a < 2 * m ^ 2` and `2379 ≤ σ(m ^ 2) / q ^ a`. -/
theorem euler_index_ge_2379 {N q a m : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2) :
    2379 * q ^ a < 2 * m ^ 2 ∧ 2379 ≤ sigma 1 (m ^ 2) / q ^ a :=
  OddPerfect.euler_component_index_ge_2379 hN ho hq hq4 ha4 hqm hform

/-- **Non-Fermat Prime Support of Every Odd Component Index**:
Every odd component index `i` (including every Euler component index `σ(m²) / q^a`)
has at least one prime divisor `p` such that `p - 1` is not a power of two. -/
theorem odd_component_index_has_nonfermat_prime {N q a b i : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hio : Odd i) :
    ∃ p ∈ i.primeFactors, ∀ k : ℕ, p - 1 ≠ 2 ^ k :=
  OddPerfect.exists_nonfermat_prime_of_odd_component_index hN ho hq ha hform hqb hl hr hio

/-- **Odd-Valuation Predecessor Escape Above Euler Exponent One**:
When `a > 1`, some prime `p` with odd valuation in `i` does not divide `q - 1`. -/
theorem euler_index_odd_valuation_escape {q a m i : ℕ}
    (hq : q.Prime) (hq4 : q % 4 = 1) (ha4 : a % 4 = 1) (ha : 1 < a) (hm : 0 < m)
    (hright : sigma 1 (q ^ a) * i = 2 * m ^ 2) :
    ∃ p : ℕ, p.Prime ∧ Odd (i.factorization p) ∧ ¬ p ∣ q - 1 :=
  OddPerfect.odd_valuation_index_prime_not_dvd_euler_pred hq hq4 ha4 ha hm hright

/-- **Fundamental Second-Block Pell Minimality in `ℤ[√(2q)]`**:
On the simultaneous Hirakawa block equations `q + 1 = 2 * d * w ^ 2` and
`q ^ d + 1 = 2 * (d * w * z) ^ 2`, `hirakawaSecondBlockPell` is fundamental. -/
theorem hirakawa_second_block_pell_fundamental {q d w z : ℕ}
    (hq : q.Prime) (hq5 : 5 ≤ q) (hd : d.Prime) (hd_odd : Odd d)
    (hq1 : q + 1 = 2 * d * w ^ 2) (hqd1 : q ^ d + 1 = 2 * (d * w * z) ^ 2) :
    Pell.IsFundamental (OddPerfect.hirakawaSecondBlockPell hd_odd hqd1) :=
  OddPerfect.hirakawa_pell_second_block_is_fundamental hq hq5 hd hd_odd hq1 hqd1

/-- **Hirakawa Exceptional Branch (`I = l * t²`, `a > 1`) Unconditional `10^740` & Higher Sieve**:
Across all `a > 1` on `σ(m²) / q^a = l * t²` (`l.Prime`), `10 ^ 740 < N`, `q % 5 ≠ 3`,
`¬ ExcludedFermatResidue q`, `¬ HigherExcludedFermatResidue q`, and whenever
`¬ 3 ∣ N` and `¬ 5 ∣ N`, `d := (a + 1) / 2` satisfies `241 ≤ d` and `481 ≤ a`. -/
theorem hirakawa_exceptional_branch_size_and_sieve {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    10 ^ 740 < N ∧
    q % 5 ≠ 3 ∧
    ¬ ExcludedFermatResidue q ∧
    ¬ HigherExcludedFermatResidue q ∧
    (¬ 3 ∣ N → ¬ 5 ∣ N → 241 ≤ (a + 1) / 2 ∧ 481 ≤ a) := by
  refine ⟨OddPerfect.exceptional_index_size_gt_ten_pow_740 hN ho hq hq4 ha4 ha hqm hform hl hi,
    fun hq5 => OddPerfect.euler_index_ne_prime_mul_square_of_mod_five_eq_three
      hN ho hq hq4 ha4 ha hqm hform (Or.inr hl) hq5 hi,
    fun hres => OddPerfect.euler_index_ne_prime_mul_square_of_excluded_residue
      hN ho hq hq4 ha4 ha hqm hform (Or.inr hl) hres hi,
    fun hres => OddPerfect.euler_index_ne_prime_mul_square_of_higher_excluded_residue
      hN ho hq hq4 ha4 ha hqm hform (Or.inr hl) hres hi,
    fun h3 h5 => ?_⟩
  obtain ⟨_, _, _, hd241, ha481⟩ :=
    OddPerfect.exceptional_euler_of_not_three_or_five_dvd hN ho hq hq4 ha4 ha hqm hform hl hi h3 h5
  exact ⟨hd241, ha481⟩

/-- **Euclidean `ℤ√2` Unit Classification & Frobenius Descent on `I = l * t²` (`a > 1`)**:
Every unit of `ℤ√2` has the form `±(1 + √2)^n`, and on `σ(m²) / q^a = l * t²` (`a > 1`, `l.Prime`)
with `d := (a + 1) / 2`, there exist `y > 0`, `k ∈ ℤ` (`1 ≤ |k| ≤ (d - 1)/2`), and `α ∈ ℤ√2`
satisfying `q ^ d + 1 = 2 * y ^ 2`, `1 + y√2 = (1 + √2)^k * α^d`, `α.norm = ±q`, and
`α ≡ (1 + √2)^(-k) [ZMOD d]`. -/
theorem hirakawa_zsqrtTwo_frobenius_descent {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    (∀ u : (ℤ√2)ˣ, ∃ n : ℤ, u = silverUnit ^ n ∨ u = -silverUnit ^ n) ∧
    let d := (a + 1) / 2
    ∃ (y : ℕ) (k : ℤ) (α : ℤ√2),
      0 < y ∧ d ∣ y ∧ q ^ d + 1 = 2 * y ^ 2 ∧
      1 ≤ |k| ∧ 2 * |k| ≤ (d : ℤ) - 1 ∧
      (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d ∧
      α.norm = (if Even k then -(q : ℤ) else (q : ℤ)) ∧
      α.re ≡ ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2).re [ZMOD (d : ℤ)] ∧
      α.im ≡ ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2).im [ZMOD (d : ℤ)] :=
  ⟨OddPerfect.zsqrtTwo_unit_eq_silverUnit_zpow,
   OddPerfect.exceptional_euler_zsqrtTwo_frobenius_descent hN ho hq hq4 ha4 ha hqm hform hl hi⟩

end EulerIndexBounds
