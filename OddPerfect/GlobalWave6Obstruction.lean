module

public import OddPerfect.GlobalWave5Obstruction
public import OddPerfect.LinearEulerCofactor
public import OddPerfect.SeptupleRepunitObstruction
public import OddPerfect.RestrainedThreeFreeObstruction
public import OddPerfect.ComponentIndexMatrix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Wave 6 Global Obstruction Synthesis (`OddPerfect.GlobalWave6Obstruction`)

Tier 2 global synthesis unifying the four Wave 6 structural pillars:
1. `OddPerfect.ComponentIndexMatrix` + `OddPerfect.SeptupleRepunitObstruction`:
   - **Non-Euler Prime-Power Component-Index Exclusion**: `componentIndex_two_valuation_dichotomy`
     (`v_2(i_r) = 1` for `r ≠ q`) combined with `36207 ≤ j` proves that **no non-Euler prime
     `r ≠ q` can ever have a prime-power component index `componentIndex N r = p ^ j` (`p.Prime`,
     `0 < j`)**! Only the Euler prime `r = q` (with `Odd p` and `p ≠ q`) can have a prime-power
     index, and for even `j` it requires `HasSevenOddPrimeRepunits p`, `10 ≤ ω(N)`, `9699688 ≤ j`,
     and `10 ^ 145495320 < i_q < N`.
2. `OddPerfect.LinearEulerCofactor`:
   - Exact quotient and divisibility decomposition on `N = q * m ^ 2` (`c₀ ∣ B`, `i_q = c₀ * σ(B)`,
     `(q + 1) * c₀ * σ(B) = 2 * r₀ ^ (2 * e₀) * B`, pure-prime `c₀ = 1` split) and unconditional
     `q % 12 = 1 ∧ 13 ≤ q` across all `3`-free odd perfect numbers.
3. `OddPerfect.RestrainedThreeFreeObstruction`:
   - Doubly-exponential telescoping abundancy elimination of `¬ (q % 3 = 1 ∧ r₀ % 3 = 1)`
     restrained three-free candidates, forcing `q % 12 = 1`, `r₀ % 3 = 1`, `13 ≤ q`, `7 ≤ r₀`,
     `N.factorization r₀ % 3 ≠ 2`, and `16 ≤ N.factorization r₀` when `a = 1`.
4. `sixth_power_free_complete_euler_profile` and `odd_perfect_wave6_master_profile`:
   - Unified Wave 6 global obstruction profile across every odd perfect number `N`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- **Non-Euler Prime-Power Component-Index Exclusion & Wave 6 Repunit Lift**:
If `r ∈ N.primeFactors` has a prime-power component index `componentIndex N r = p ^ j` (`p.Prime`,
`0 < j`), then `r` **must** be the Euler prime `q` (every non-Euler prime `r ≠ q` has singly-even
`componentIndex N r`, incompatible with `36207 ≤ j`), `Odd p`, `p ≠ q`, `36207 ≤ j`,
`10 ^ 17240 < componentIndex N r < N`, `Odd j → ¬ ExcludedFermatResidue q`, and for `Even j`:
`N.factorization q = 1`, `HasSevenOddPrimeRepunits p`, `10 ≤ ω(N)`, `9699688 ≤ j`, and
`10 ^ 145495320 < componentIndex N q < N`. -/
theorem component_prime_power_index_euler_only_and_septuple_lift {N q r p j : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ s : ℕ, s ≠ q → Even (N.factorization s))
    (hr : r ∈ N.primeFactors) (hp : p.Prime) (hj : 0 < j)
    (hci_eq : componentIndex N r = p ^ j) :
    r = q ∧ Odd p ∧ p ≠ q ∧
    36207 ≤ j ∧ 10 ^ 17240 < componentIndex N q ∧ 10 ^ 17240 < N ∧
    (Odd j → ¬ ExcludedFermatResidue q) ∧
    (Even j → N.factorization q = 1 ∧ HasSevenOddPrimeRepunits p ∧ 10 ≤ N.primeFactors.card ∧
      9699688 ≤ j ∧ 10 ^ 145495320 < componentIndex N q ∧ 10 ^ 145495320 < N) := by
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
  obtain ⟨hj36207, hi17240, hN17240, _⟩ :=
    component_prime_power_index_exponent_ge_36207
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
  have hp_neq_q : p ≠ q := by
    rintro rfl
    exact componentIndex_not_dvd_self ho hN hq (by rw [hci_eq]; exact dvd_pow_self p hj.ne')
  refine ⟨rfl, hp_odd, hp_neq_q, hj36207, hi17240.trans_eq hci.symm, hN17240, ?_, ?_⟩
  · intro hj_odd hres
    exact componentIndex_ne_odd_prime_power_of_excluded_residue ho hN hq hres hp hj_odd hci_eq
  · intro hj_even
    obtain ⟨hj9699688, hi145, hN145⟩ :=
      even_prime_power_component_size_gt_ten_pow_145495320
        hN ho hr_prime ha_pos hNb hrb hleft hright hp hj hj_even hi_eq
    obtain ⟨u, rfl⟩ := hj_even
    have hu : 0 < u := by omega
    have hi2 : i = p ^ (2 * u) := by
      rw [hi_eq, show u + u = 2 * u by ring]
    obtain ⟨hq1, _⟩ :=
      even_prime_power_index_eq_selected_sigma hN ho hr_prime ha_pos hNb hrb hleft hright hp hu hi2
    obtain ⟨hseven, h10⟩ :=
      even_prime_power_component_forces_seven_repunits_and_ten_primes
        hN ho hr_prime ha_pos hNb hrb hleft hright hp hu hi2
    exact ⟨hq1, hseven, h10, hj9699688, hi145.trans_eq hci.symm, hN145⟩

/-- Complete sixth-power-free Euler-component profile combining `LinearEulerCofactor`,
`ComponentIndexMatrix`, and `GlobalWave5Obstruction`. -/
theorem sixth_power_free_complete_euler_profile {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    N.factorization q = 1 ∧
    q % 12 = 1 ∧
    13 ≤ q ∧
    Odd (componentIndex N q) ∧
    ¬ q ∣ componentIndex N q ∧
    (componentIndex N q).primeFactors.card + 1 +
      ((squareSources N).filter (· % 5 ≠ 1)).card +
      (twoModThreeLargeSources N q).card ≤ N.primeFactors.card ∧
    cardFactors (componentIndex N q) + 1 +
      2 * ((squareSources N).filter (· % 5 ≠ 1)).card +
      4 * (twoModThreeLargeSources N q).card ≤ cardFactors N ∧
    (∀ p ∈ (componentIndex N q).primeFactors, p ≠ q ∧ (p % 5 = 1 ∨ p % 3 = 1)) := by
  have hq1 : N.factorization q = 1 := sixth_power_free_euler_exponent_one ho hN hq he hfree
  obtain ⟨hq12, hq13⟩ := sixth_power_free_euler_prime_mod_twelve_or_twenty ho hN hq hq4 he hev hfree
  have hodd : Odd (componentIndex N q) :=
    ((componentIndex_two_valuation_dichotomy ho hN hq hq4 he hev hq).1 rfl).2
  have hnq : ¬ q ∣ componentIndex N q := componentIndex_not_dvd_self ho hN hq
  have hdist := sixth_power_free_euler_index_distinct_drop ho hN hq hq4 he hev hfree
  obtain ⟨hmult, hsupp⟩ := sixth_power_free_euler_index_drop_and_support ho hN hq hq4 he hev hfree
  refine ⟨hq1, hq12, hq13, hodd, hnq, hdist, hmult, fun p hp => ⟨?_, hsupp p hp⟩⟩
  rintro rfl
  exact hnq (Nat.dvd_of_mem_primeFactors hp)

/-- Unified Wave 6 global obstruction profile across every odd perfect number `N`. -/
theorem odd_perfect_wave6_master_profile {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    (∃ p ∈ N.primeFactors,
      cardFactors (componentIndex N p) + 6 ≤ cardFactors N ∧
      7 ≤ N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) ∧
    (∀ p ∈ N.primeFactors, ¬ p ∣ componentIndex N p ∧
      (componentIndex N p).Coprime (ordProj[p] N)) ∧
    ((∑ p ∈ N.primeFactors, (componentIndex N p).factorization 2) = N.primeFactors.card - 1 ∧
      ∀ r ∈ N.primeFactors,
        (∑ p ∈ N.primeFactors, (componentIndex N p).factorization r) =
          (N.primeFactors.card - 2) * N.factorization r) ∧
    ∃ q a m, q.Prime ∧ q % 4 = 1 ∧ a % 4 = 1 ∧ ¬ q ∣ m ∧ N = q ^ a * m ^ 2 ∧
      q ∈ N.primeFactors ∧ N.factorization q = a ∧
      (∀ r, r ≠ q → Even (N.factorization r)) ∧
      (¬ 3 ∣ N → q % 12 = 1 ∧ 13 ≤ q) ∧
      (∀ r ∈ N.primeFactors, ∀ p j, p.Prime → 0 < j → componentIndex N r = p ^ j →
        r = q ∧ Odd p ∧ p ≠ q ∧ 36207 ≤ j ∧
        10 ^ 17240 < componentIndex N q ∧ 10 ^ 17240 < N ∧
        (Odd j → ¬ ExcludedFermatResidue q) ∧
        (Even j → a = 1 ∧ HasSevenOddPrimeRepunits p ∧ 10 ≤ N.primeFactors.card ∧
          9699688 ≤ j ∧ 10 ^ 145495320 < componentIndex N q ∧ 10 ^ 145495320 < N)) ∧
      (a = 1 →
        ∃ r₀ ∈ m.primeFactors,
          let e₀ := m.factorization r₀
          let B := ordCompl[r₀] (m ^ 2)
          let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
          sigma 1 (r₀ ^ (2 * e₀)) = q * c₀ ∧ ¬ q ∣ c₀ ∧ Odd c₀ ∧
          Nat.Coprime c₀ (r₀ ^ (2 * e₀)) ∧
          sigma 1 (m ^ 2) / q = c₀ * sigma 1 B ∧
          (q + 1) * c₀ * sigma 1 B = 2 * r₀ ^ (2 * e₀) * B ∧
          c₀ ∣ B ∧ r₀ ^ (2 * e₀) ∣ ((q + 1) / 2) * sigma 1 B) ∧
      (¬ 3 ∣ N → (largeSources N q).card ≤ 1 →
        ∃ r₀, largeSources N q = {r₀} ∧ q % 12 = 1 ∧ r₀ % 3 = 1 ∧
          13 ≤ q ∧ 7 ≤ r₀ ∧ N.factorization r₀ % 3 ≠ 2 ∧
          (a = 1 → 16 ≤ N.factorization r₀)) := by
  have hcons := sum_componentIndex_factorization_conservation ho hN
  refine ⟨exists_component_capturing_seven_factors ho hN,
    fun p hp => ⟨componentIndex_not_dvd_self ho hN hp, componentIndex_coprime_ordProj ho hN hp⟩,
    ⟨hcons.2, hcons.1⟩, ?_⟩
  obtain ⟨q, a, m, hq, hq4, ha4, hqm, hform⟩ := euler_form ho hN
  have ha_pos : 0 < a := by omega
  have hm : Odd m := ho.of_dvd_nat
    (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self m (by decide : 2 ≠ 0)) _)
  have hqN : q ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr
      ⟨hq, hform ▸ dvd_mul_of_dvd_left (dvd_pow_self q ha_pos.ne') _, hN.2.ne'⟩
  have hval : N.factorization q = a := by
    rw [hform, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hm.pos.ne'),
      Finsupp.add_apply, hq.factorization_pow, Finsupp.single_eq_same, Nat.factorization_pow,
      Finsupp.smul_apply, Nat.factorization_eq_zero_of_not_dvd hqm, smul_eq_mul, mul_zero,
      add_zero]
  have he4 : N.factorization q % 4 = 1 := by simpa [hval] using ha4
  have hev : ∀ r, r ≠ q → Even (N.factorization r) := by
    intro r hrq
    by_cases hrp : r.Prime
    · have hr_not_q : ¬ r ∣ q := fun hd => hrq ((Nat.prime_dvd_prime_iff_eq hrp hq).mp hd)
      rw [hform, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hm.pos.ne'),
        Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
        Nat.factorization_eq_zero_of_not_dvd hr_not_q, mul_zero, zero_add,
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
      exact ⟨m.factorization r, by ring⟩
    · rw [Nat.factorization_eq_zero_of_not_prime N hrp]
      exact ⟨0, rfl⟩
  refine ⟨q, a, m, hq, hq4, ha4, hqm, hform, hqN, hval, hev, ?_, ?_, ?_, ?_⟩
  · exact three_free_euler_prime_mod_twelve ho hN hqN hq4 he4
  · intro r hr p j hp hj hci_eq
    obtain ⟨hrq, hp_odd, hp_neq, hj36207, hi17, hN17, hodd_j, heven_j⟩ :=
      component_prime_power_index_euler_only_and_septuple_lift
        ho hN hqN hq4 he4 hev hr hp hj hci_eq
    refine ⟨hrq, hp_odd, hp_neq, hj36207, hi17, hN17, hodd_j, fun hje => ?_⟩
    obtain ⟨hq1, hseven, h10, hj9, hi145, hN145⟩ := heven_j hje
    exact ⟨hval.symm.trans hq1, hseven, h10, hj9, hi145, hN145⟩
  · intro ha1
    have hform1 : N = q * m ^ 2 := by simpa [ha1] using hform
    exact linear_euler_cofactor_quotient_structure ho hN hq hqm hform1
  · intro h3 hle
    obtain ⟨r₀, hr₀, hq12, hr₀3, hq13, hr₀7, hmod3⟩ :=
      restrained_three_free_forces_both_one_mod_three ho hN hqN hq4 he4 hev h3 hle
    refine ⟨r₀, hr₀, hq12, hr₀3, hq13, hr₀7, hmod3, fun ha1 => ?_⟩
    have hq_fac1 : N.factorization q = 1 := hval.trans ha1
    exact restrained_three_free_euler_exp_one_forces_sixteenth_power
      ho hN hqN hq4 hq_fac1 hev h3 hr₀

end OddPerfect
