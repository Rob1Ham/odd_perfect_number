module

public import OddPerfect.PrimePowerObstruction
public import OddPerfect.PrimePowerHigherObstruction
public import OddPerfect.EvenIndexSubexponential
public import OddPerfect.ComponentIndexMatrix
public import OddPerfect.TridecupleRepunitObstruction
public import OddPerfect.EvenIndexPrimorialObstruction
public import OddPerfect.PadicEvenIndexObstruction
public import OddPerfect.GaussSumCyclotomicForms
public import OddPerfect.FermatIndexObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Unconditional `p`-adic and Repunit Obstructions to Prime-Power Component Indices

Standalone public entry point for `prime-power-index-breakout`, packaging the
unconditional obstructions to `componentIndex N r = p ^ j` (`p.Prime`, `0 < j`)
across all prime divisors `r ∈ N.primeFactors` of an odd perfect number `N`:

1. `prime_power_index_euler_only_and_nonfermat`:
   Eliminates all non-Euler prime-power component indices (`r ≠ q`), proving
   `r = q`, `Odd p`, `p ≠ q`, `30028 ≤ j`, `10 ^ 17240 < componentIndex N q`,
   `10 ^ 17240 < N`, and `∀ k, p - 1 ≠ 2 ^ k` (no Fermat prime base).
2. `even_prime_power_tridecuple_repunit_and_size_bounds`:
   Eliminates `|S₁| ∈ {0, 1, ..., 12}` unconditionally (including the pure
   Nagell–Ljunggren branch `|S₁| = 0`), proving `HasThirteenOddPrimeRepunits p`,
   `16 ≤ ω(N)`, `13082761331670028 ≤ 2 * u`, and `10 ^ 353234555955090756 < i, N`
   alongside the subexponential base cap `p ≤ 8 * (u + 1) * 128 ^ Nat.sqrt (2 * u)`.
3. `even_prime_power_primorial_padic_and_gauss_reciprocity`:
   Couples all-`k` primorial confinement (`min S₁ ∈ {3, 5, 7, 11, 13}`),
   Gauss-sum cyclotomic quadratic reciprocity `IsSquare ((-1) ^ (l / 2) * l : ZMod p)`,
   fourth-order congruence `128 * (s - 1) ≡ 32 * p + 28 * p ^ 2 + 25 * p ^ 3 [MOD p ^ 4]`,
   and exact `p`-adic Hensel root distance `‖(s : ℤ_[p]) - σ_p‖ = p ^ (-(2 * u + 1))`.
-/

public section

namespace PrimePowerIndex

open OddPerfect ArithmeticFunction Finset

/-- Every prime-power component index `componentIndex N r = p ^ j` (`p.Prime`, `0 < j`)
must occur at the Euler prime `r = q`, with `Odd p`, `p ≠ q`, `30028 ≤ j`,
`10 ^ 17240 < componentIndex N q`, `10 ^ 17240 < N`, and non-Fermat base `∀ k, p - 1 ≠ 2 ^ k`. -/
theorem prime_power_index_euler_only_and_nonfermat {N q r p j : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ s : ℕ, s ≠ q → Even (N.factorization s))
    (hr : r ∈ N.primeFactors) (hp : p.Prime) (hj : 0 < j)
    (hci_eq : componentIndex N r = p ^ j) :
    r = q ∧ Odd p ∧ p ≠ q ∧
    30028 ≤ j ∧ 10 ^ 17240 < componentIndex N q ∧ 10 ^ 17240 < N ∧
    (∀ k : ℕ, p - 1 ≠ 2 ^ k) := by
  have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr
  have ha_pos : 0 < N.factorization r := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
  have hNb : N = r ^ N.factorization r * ordCompl[r] N :=
    (Nat.ordProj_mul_ordCompl_eq_self N r).symm
  have hrb : ¬ r ∣ ordCompl[r] N := Nat.not_dvd_ordCompl hr_prime hN.2.ne'
  obtain ⟨i, _, hleft, hright, _⟩ := exists_component_index hN hr_prime hNb hrb
  have hci : componentIndex N r = i := by
    rw [componentIndex, hleft]
    exact Nat.mul_div_cancel_left i (pow_pos hr_prime.pos _)
  have hi_eq : i = p ^ j := hci.symm.trans hci_eq
  obtain ⟨hj30028, hi17240, hN17240, _⟩ :=
    component_prime_power_index_exponent_ge_30028
      hN ho hr_prime ha_pos hNb hrb hleft hright hp hj hi_eq
  have hdich := componentIndex_two_valuation_dichotomy ho hN hq hq4 he hev hr
  have hr_eq_q : r = q := by
    by_contra hr_ne_q
    obtain ⟨_, hci_even, hci_ndvd4⟩ := hdich.2 hr_ne_q
    rw [hci_eq] at hci_even hci_ndvd4
    have h2_dvd_pj : 2 ∣ p ^ j := Nat.dvd_of_mod_eq_zero (Nat.even_iff.mp hci_even)
    have h2_dvd_p : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow h2_dvd_pj
    have hp2 : p = 2 := (((Nat.dvd_prime hp).mp h2_dvd_p).resolve_left (by decide)).symm
    rw [hp2] at hci_ndvd4
    exact hci_ndvd4 (pow_dvd_pow 2 (by omega : 2 ≤ j))
  subst r
  have hci_odd : Odd (componentIndex N q) := (hdich.1 rfl).2
  have hp_odd : Odd p := by
    by_contra hp_not_odd
    have hp2 : p = 2 := by
      have := hp.two_le
      have hmod : p % 2 = 0 := by
        by_contra h1
        exact hp_not_odd (Nat.odd_iff.mpr (by omega))
      exact (((Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero hmod)).resolve_left (by decide)).symm
    have h2_dvd : 2 ∣ componentIndex N q := by
      rw [hci_eq, hp2]
      exact dvd_pow_self 2 hj.ne'
    exact hci_odd.not_two_dvd_nat h2_dvd
  have hp_ne_q : p ≠ q := by
    rintro rfl
    exact componentIndex_not_dvd_self ho hN hq (hci_eq ▸ dvd_pow_self p hj.ne')
  have hnf : ∀ k : ℕ, p - 1 ≠ 2 ^ k := fun k hk =>
    component_index_ne_fermat_prime_power
      hN ho hr_prime ha_pos hNb hrb hleft hright hp hj hk hi_eq
  exact ⟨rfl, hp_odd, hp_ne_q, hj30028, hci.symm ▸ hi17240, hN17240, hnf⟩

/-- **Tridecuple Goormaghtigh Repunits, Subexponential Base Cap, & `10^353234555955090756` Bound**:
For any even prime-power component index `i = p ^ (2 * u)`, `p` simultaneously admits
at least 13 odd-prime repunit representations, `16 ≤ ω(N)`, `p ≤ 8(u+1)128^√(2u)`,
`13082761331670028 ≤ 2 * u`, and `10 ^ 353234555955090756 < i < N`. -/
theorem even_prime_power_tridecuple_repunit_and_size_bounds
    {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    HasThirteenOddPrimeRepunits p ∧
    16 ≤ N.primeFactors.card ∧
    p ≤ 8 * (u + 1) * 128 ^ Nat.sqrt (2 * u) ∧
    13082761331670028 ≤ 2 * u ∧
    10 ^ 353234555955090756 < i ∧
    10 ^ 353234555955090756 < N := by
  obtain ⟨h13, h16⟩ :=
    even_prime_power_component_forces_thirteen_repunits_and_sixteen_primes
      hN ho hq ha hform hqb hl hr hp hu hi
  have hsub :=
    (even_prime_power_component_subexponential_bounds hN ho hq ha hform hqb hl hr hp hu hi).1
  obtain ⟨hj, hi_gt, hN_gt⟩ :=
    even_prime_power_component_size_gt_ten_pow_353234555955090756
      hN ho hq ha hform hqb hl hr hp (by omega : 0 < 2 * u) ⟨u, by ring⟩ hi
  exact ⟨h13, h16, hsub, hj, hi_gt, hN_gt⟩

/-- **Unified Primorial Confinement, Gauss-Sum Reciprocity, Mod-`p^4` & `p`-Adic Hensel Profile**:
On any even prime-power component index `i = p ^ (2 * u)`:
1. `N` is divisible by `r ^ 2` for some `r ∈ {3, 5, 7, 11, 13}` with `geometricBlock r l = p`
   (`l` odd prime) and `IsSquare ((-1 : ZMod p) ^ (l / 2) * (l : ZMod p))`;
2. The cofactor `s` (`q + 1 = 2 * s ^ 2`) satisfies
   `2 * (p - 1) * s ^ 2 = (p - 2) + p ^ (2 * u + 1)`,
   `32 * (s - 1) ≡ 8 * p + 7 * p ^ 2 [MOD p ^ 3]`,
   `128 * (s - 1) ≡ 32 * p + 28 * p ^ 2 + 25 * p ^ 3 [MOD p ^ 4]`,
   and lies at exact `p`-adic distance `p ^ (-(2 * u + 1))` from the Hensel root `σ_p ∈ ℤ_[p]`. -/
theorem even_prime_power_primorial_padic_and_gauss_reciprocity
    {N q a b i p u : ℕ} [Fact p.Prime]
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    (∃ r ∈ ({3, 5, 7, 11, 13} : Finset ℕ),
      r ^ 2 ∣ N ∧ ∃ l : ℕ, l.Prime ∧ 2 < l ∧ geometricBlock r l = p ∧
        IsSquare ((-1 : ZMod p) ^ (l / 2) * (l : ZMod p))) ∧
    ∃ s : ℕ, Odd s ∧
      2 * (p - 1) * s ^ 2 = (p - 2) + p ^ (2 * u + 1) ∧
      32 * (s - 1) ≡ 8 * p + 7 * p ^ 2 [MOD p ^ 3] ∧
      128 * (s - 1) ≡ 32 * p + 28 * p ^ 2 + 25 * p ^ 3 [MOD p ^ 4] ∧
      ∃ σ_p : ℤ_[p],
        2 * ((p : ℤ_[p]) - 1) * σ_p ^ 2 = (p : ℤ_[p]) - 2 ∧
        ‖(s : ℤ_[p]) - σ_p‖ = (p : ℝ) ^ (-(2 * u + 1 : ℤ)) ∧
        ((s : ℤ_[p]) - σ_p).valuation = 2 * u + 1 := by
  obtain ⟨⟨r, hr5, hr2N, l, hlp, hl2, hgb⟩, _⟩ :=
    even_prime_power_component_forces_small_repunit_base hN ho hq ha hform hqb hl hr hp hu hi
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b _)
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h4 : 4 ∣ 2 * b := hr ▸ hi ▸ (pow_dvd_pow 2 (by omega : 2 ≤ 2 * u)).trans (dvd_mul_left _ _)
    have := hbo.not_two_dvd_nat
    omega
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hl_ne2 : l ≠ 2 := by omega
  have hr_ge1 : 1 ≤ r := by
    have hpos : ∀ x ∈ ({3, 5, 7, 11, 13} : Finset ℕ), 1 ≤ x := by decide
    exact hpos r hr5
  have hp_gt_l : l < p := by
    rw [← hgb]
    calc
      l = ∑ _j ∈ Finset.range l, 1 := by simp
      _ < ∑ j ∈ Finset.range l, r ^ j := by
        refine Finset.sum_lt_sum (fun j _ => Nat.one_le_pow j r hr_ge1) ?_
        have hr_gt1 : 1 < r := by
          have hpos : ∀ x ∈ ({3, 5, 7, 11, 13} : Finset ℕ), 1 < x := by decide
          exact hpos r hr5
        exact ⟨1, Finset.mem_range.mpr (by omega), by simpa using hr_gt1⟩
  have hpl : p ≠ l := (ne_of_lt hp_gt_l).symm
  have hdvd_gb : p ∣ geometricBlock r l := hgb ▸ dvd_rfl
  have hgauss :=
    (signed_prime_isSquare_of_dvd_geometricBlock hlp hl_ne2 hp hp2 hpl hr_ge1 hdvd_gb).2.1
  obtain ⟨ha1, hσq⟩ :=
    even_prime_power_index_eq_selected_sigma hN ho hq ha hform hqb hl hr hp hu hi
  obtain ⟨m, _, _, _, rfl⟩ :=
    euler_form_of_odd_component_index hN ho hq ha hform hqb hl hr (hi ▸ hpo.pow)
  have hmo := ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _)
  rw [ha1, pow_one] at hform hl hr
  rw [hi] at hl hr
  obtain ⟨s, hso, _, _, _, hplus, hσs⟩ := even_prime_power_cofactor_split hq hp hmo hpo hu hl hr
  have hclosed := even_index_twice_pred_mul_cofactor_sq hp hσq hplus
  obtain ⟨hmod3, hmod4⟩ := even_index_cofactor_mod_p_cube_and_fourth hp hpo hso hu hσq hplus hσs
  obtain ⟨σ_p, hroot, _, _, hnorm, hval, _, _⟩ :=
    even_index_cofactor_padic_distance_to_hensel_root hp hpo hso hu hσq hplus hσs
  exact ⟨⟨r, hr5, hr2N, l, hlp, hl2, hgb, hgauss⟩,
    ⟨s, hso, hclosed, hmod3, hmod4, σ_p, hroot, hnorm, hval⟩⟩

end PrimePowerIndex
