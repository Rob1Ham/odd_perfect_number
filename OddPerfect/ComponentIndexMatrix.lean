module

public import OddPerfect.QuarticTargetCapacity
public import OddPerfect.GlobalObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Global Component-Index Valuation Matrix (`OddPerfect.ComponentIndexMatrix`)

Formalizes the exact global valuation matrix and prime-support saturation laws of
`componentIndex N p` across all `p ∈ N.primeFactors`:

1. `componentIndex_factorization_self_eq_zero`, `componentIndex_not_dvd_self`, and
   `componentIndex_coprime_ordProj`: diagonal zeros of the component-index valuation matrix.
2. `componentIndex_factorization_eq_sub`: off-diagonal conservation
   `v_r(i_p) + v_r(σ(p^{v_p(N)})) = v_r(N)` for `r ≠ p, 2`.
3. `componentIndex_two_valuation_dichotomy`: exact 2-adic dichotomy separating the Euler prime
   (`v_2(i_q) = 0`, `Odd (i_q)`) from all non-Euler primes (`v_2(i_p) = 1`, `Even (i_p)`, `¬ 4 ∣ i_p`).
4. `sum_componentIndex_factorization_conservation`: global column sums across all `p ∈ N.primeFactors`,
   `∑_p v_r(i_p) = (ω(N) - 2) * v_r(N)` and `∑_p v_2(i_p) = ω(N) - 1`.
5. `componentIndex_primeFactors_subset_and_saturation_drop` and
   `sixth_power_free_euler_index_distinct_drop`: prime-support exclusion via saturated targets
   and specialization to the sixth-power-free incoming-source vacuum `S₅₀ ∪ Q₂₃`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- Diagonal vanishing of the component-index valuation matrix: `v_p(componentIndex N p) = 0`. -/
theorem componentIndex_factorization_self_eq_zero {N p : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) :
    (componentIndex N p).factorization p = 0 := by
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp_odd : Odd p := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
  have hp_ne2 : p ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hp_odd)
  have hp_ndvd2 : ¬ p ∣ 2 := fun hd =>
    hp_ne2 (((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left hp_prime.ne_one)
  obtain ⟨hmul, hpos⟩ := componentIndex_mul_eq_two_mul hN hp
  have hord_ne0 : ordProj[p] N ≠ 0 := pow_ne_zero _ hp_prime.ne_zero
  have hsig_ne0 : sigma 1 (ordProj[p] N) ≠ 0 := (sigma_pos 1 _ hord_ne0).ne'
  have hfac := congrArg (fun n => n.factorization p) hmul
  rw [Nat.factorization_mul (mul_ne_zero hpos.ne' hord_ne0) hsig_ne0, Finsupp.add_apply,
    Nat.factorization_mul hpos.ne' hord_ne0, Finsupp.add_apply,
    Nat.factorization_pow_self hp_prime,
    Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) hN.2.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hp_ndvd2, zero_add] at hfac
  omega

/-- No prime `p ∈ N.primeFactors` divides its own `componentIndex N p`. -/
theorem componentIndex_not_dvd_self {N p : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) :
    ¬ p ∣ componentIndex N p := by
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpos : 0 < componentIndex N p := (componentIndex_mul_eq_two_mul hN hp).2
  intro hd
  have h1 : 1 ≤ (componentIndex N p).factorization p :=
    (hp_prime.dvd_iff_one_le_factorization hpos.ne').mp hd
  have h0 : (componentIndex N p).factorization p = 0 :=
    componentIndex_factorization_self_eq_zero ho hN hp
  omega

/-- Each `componentIndex N p` is coprime to the exact prime-power component `ordProj[p] N`. -/
theorem componentIndex_coprime_ordProj {N p : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) :
    (componentIndex N p).Coprime (ordProj[p] N) := by
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  exact ((hp_prime.coprime_iff_not_dvd.mpr
    (componentIndex_not_dvd_self ho hN hp)).pow_left (N.factorization p)).symm

/-- Off-diagonal valuation conservation: for every `r ≠ p, 2`,
`v_r(componentIndex N p) + v_r(σ(p^{v_p(N)})) = v_r(N)`. -/
theorem componentIndex_factorization_eq_sub {N p r : ℕ} (_ho : Odd N) (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) (hr : r ≠ p) (hr2 : r ≠ 2) :
    (componentIndex N p).factorization r + (sigma 1 (ordProj[p] N)).factorization r =
      N.factorization r := by
  by_cases hr_prime : r.Prime
  · have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    obtain ⟨hmul, hpos⟩ := componentIndex_mul_eq_two_mul hN hp
    have hord_ne0 : ordProj[p] N ≠ 0 := pow_ne_zero _ hp_prime.ne_zero
    have hsig_ne0 : sigma 1 (ordProj[p] N) ≠ 0 := (sigma_pos 1 _ hord_ne0).ne'
    have hndvd2 : ¬ r ∣ 2 := fun hd =>
      hr2 (((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left hr_prime.ne_one)
    have hord_fac : (ordProj[p] N).factorization r = 0 := by
      rw [hp_prime.factorization_pow, Finsupp.single_apply, ite_eq_right hr.symm]
    have hfac := congrArg (fun n => n.factorization r) hmul
    rw [Nat.factorization_mul (mul_ne_zero hpos.ne' hord_ne0) hsig_ne0, Finsupp.add_apply,
      Nat.factorization_mul hpos.ne' hord_ne0, Finsupp.add_apply,
      hord_fac, add_zero,
      Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) hN.2.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hndvd2, zero_add] at hfac
    exact hfac
  · rw [Nat.factorization_eq_zero_of_not_prime _ hr_prime,
      Nat.factorization_eq_zero_of_not_prime _ hr_prime,
      Nat.factorization_eq_zero_of_not_prime _ hr_prime,
      zero_add]

/-- Exact 2-adic dichotomy for `componentIndex N p`: the Euler prime has odd index
(`v_2(i_q) = 0`), whereas every non-Euler prime has singly-even index (`v_2(i_p) = 1`, `¬ 4 ∣ i_p`). -/
theorem componentIndex_two_valuation_dichotomy {N q p : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (_hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hp : p ∈ N.primeFactors) :
    (p = q → (componentIndex N p).factorization 2 = 0 ∧ Odd (componentIndex N p)) ∧
    (p ≠ q → (componentIndex N p).factorization 2 = 1 ∧ Even (componentIndex N p) ∧
      ¬ 4 ∣ componentIndex N p) := by
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp_odd : Odd p := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
  have hp_ne2 : p ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hp_odd)
  obtain ⟨hmul, hpos⟩ := componentIndex_mul_eq_two_mul hN hp
  have hord_ne0 : ordProj[p] N ≠ 0 := pow_ne_zero _ hp_prime.ne_zero
  have hsig_ne0 : sigma 1 (ordProj[p] N) ≠ 0 := (sigma_pos 1 _ hord_ne0).ne'
  have hord_fac2 : (ordProj[p] N).factorization 2 = 0 := by
    rw [hp_prime.factorization_pow, Finsupp.single_apply, ite_eq_right hp_ne2]
  have hN_fac2 : N.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd ho.not_two_dvd_nat
  have h2_fac2 : (2 : ℕ).factorization 2 = 1 :=
    Nat.Prime.factorization_self Nat.prime_two
  have hfac2 := congrArg (fun n => n.factorization 2) hmul
  rw [Nat.factorization_mul (mul_ne_zero hpos.ne' hord_ne0) hsig_ne0, Finsupp.add_apply,
    Nat.factorization_mul hpos.ne' hord_ne0, Finsupp.add_apply,
    hord_fac2, add_zero,
    Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) hN.2.ne', Finsupp.add_apply,
    h2_fac2, hN_fac2, add_zero] at hfac2
  constructor
  · intro hpq
    rw [hpq] at hp_prime hpos hsig_ne0 hfac2 ⊢
    have hS4 := sigma_modEq_of_one hp_prime (show q ≡ 1 [MOD 4] from hq4) (N.factorization q)
    change sigma 1 (ordProj[q] N) % 4 = (N.factorization q + 1) % 4 at hS4
    have hS2 : 2 ∣ sigma 1 (ordProj[q] N) := Nat.dvd_of_mod_eq_zero (by omega)
    have hsig_fac2 : 1 ≤ (sigma 1 (ordProj[q] N)).factorization 2 :=
      (Nat.prime_two.dvd_iff_one_le_factorization hsig_ne0).mp hS2
    have hci_fac2 : (componentIndex N q).factorization 2 = 0 := by omega
    have hci_ndvd2 : ¬ 2 ∣ componentIndex N q := by
      intro hd
      have h1 := (Nat.prime_two.dvd_iff_one_le_factorization hpos.ne').mp hd
      omega
    rw [Nat.dvd_iff_mod_eq_zero] at hci_ndvd2
    exact ⟨hci_fac2, Nat.odd_iff.mpr (by omega)⟩
  · intro hpq
    obtain ⟨k, hk⟩ := hev p hpq
    have hord_sq : IsSquare (ordProj[p] N) := ⟨p ^ k, by rw [hk, pow_add]⟩
    have hord_odd : Odd (ordProj[p] N) := ho.of_dvd_nat (Nat.ordProj_dvd N p)
    have hsig_odd : Odd (sigma 1 (ordProj[p] N)) :=
      (odd_sigma_iff_square_of_odd hord_odd).mpr hord_sq
    have hsig_fac2 : (sigma 1 (ordProj[p] N)).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hsig_odd.not_two_dvd_nat
    have hci_fac2 : (componentIndex N p).factorization 2 = 1 := by omega
    have hci_dvd2 : 2 ∣ componentIndex N p :=
      (Nat.prime_two.dvd_iff_one_le_factorization hpos.ne').mpr (by omega)
    have hci_even : Even (componentIndex N p) :=
      Nat.even_iff.mpr (Nat.dvd_iff_mod_eq_zero.mp hci_dvd2)
    have hci_ndvd4 : ¬ 4 ∣ componentIndex N p := by
      intro hd
      have hd2 : 2 ^ 2 ∣ componentIndex N p := hd
      have h2 := (Nat.prime_two.pow_dvd_iff_le_factorization hpos.ne').mp hd2
      omega
    exact ⟨hci_fac2, hci_even, hci_ndvd4⟩

/-- Global column-sum conservation of `componentIndex N p` valuations across `N.primeFactors`:
`∑_p v_r(i_p) = (ω(N) - 2) * v_r(N)` for every `r ∈ N.primeFactors`, and `∑_p v_2(i_p) = ω(N) - 1`. -/
theorem sum_componentIndex_factorization_conservation {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    (∀ r ∈ N.primeFactors,
      (∑ p ∈ N.primeFactors, (componentIndex N p).factorization r) =
        (N.primeFactors.card - 2) * N.factorization r) ∧
    (∑ p ∈ N.primeFactors, (componentIndex N p).factorization 2) = N.primeFactors.card - 1 := by
  have hpos : ∀ p ∈ N.primeFactors, componentIndex N p ≠ 0 :=
    fun p hp => (componentIndex_mul_eq_two_mul hN hp).2.ne'
  have hprod := prod_componentIndex_eq ho hN
  have h_at : ∀ q : ℕ,
      (∑ p ∈ N.primeFactors, (componentIndex N p).factorization q) =
        (N.primeFactors.card - 1) * (2 : ℕ).factorization q +
          (N.primeFactors.card - 2) * N.factorization q := by
    intro q
    have hfac := congrArg (fun n => n.factorization q) hprod
    rw [Nat.factorization_prod_apply hpos,
      Nat.factorization_mul (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)) (pow_ne_zero _ hN.2.ne'),
      Finsupp.add_apply, Nat.factorization_pow, Nat.factorization_pow,
      Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul] at hfac
    exact hfac
  constructor
  · intro r hr
    have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hr_odd : Odd r := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr)
    have hr_ne2 : r ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hr_odd)
    have hr_ndvd2 : ¬ r ∣ 2 := fun hd =>
      hr_ne2 (((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left hr_prime.ne_one)
    have h := h_at r
    rw [Nat.factorization_eq_zero_of_not_dvd hr_ndvd2, mul_zero, zero_add] at h
    exact h
  · have h := h_at 2
    rw [Nat.Prime.factorization_self Nat.prime_two, mul_one,
      Nat.factorization_eq_zero_of_not_dvd ho.not_two_dvd_nat, mul_zero, add_zero] at h
    exact h

/-- Prime-support containment and saturation drop for `componentIndex N p`: every odd prime
dividing `componentIndex N p` lies in `(N.primeFactors.erase p) \ Sat(N, p)`, so when
`Odd (componentIndex N p)`, `ω(componentIndex N p) + 1 + #Sat(N, p) ≤ ω(N)`. -/
theorem componentIndex_primeFactors_subset_and_saturation_drop {N p : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hp : p ∈ N.primeFactors) :
    let sat := (N.primeFactors.erase p).filter
      (fun r => (sigma 1 (ordProj[p] N)).factorization r = N.factorization r)
    (componentIndex N p).primeFactors ⊆ insert 2 (N.primeFactors.erase p \ sat) ∧
    (Odd (componentIndex N p) →
      (componentIndex N p).primeFactors ⊆ N.primeFactors.erase p \ sat ∧
      (componentIndex N p).primeFactors.card + 1 + sat.card ≤ N.primeFactors.card) := by
  intro sat
  have hpos : 0 < componentIndex N p := (componentIndex_mul_eq_two_mul hN hp).2
  have hsub : (componentIndex N p).primeFactors ⊆ insert 2 (N.primeFactors.erase p \ sat) := by
    intro r hr
    have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hr_dvd : r ∣ componentIndex N p := Nat.dvd_of_mem_primeFactors hr
    have hr_fac_pos : 1 ≤ (componentIndex N p).factorization r :=
      (hr_prime.dvd_iff_one_le_factorization hpos.ne').mp hr_dvd
    by_cases hr2 : r = 2
    · rw [hr2]
      exact Finset.mem_insert_self 2 _
    · apply Finset.mem_insert_of_mem
      have hrp : r ≠ p := by
        intro hrp
        rw [hrp] at hr_dvd
        exact componentIndex_not_dvd_self ho hN hp hr_dvd
      have hbal := componentIndex_factorization_eq_sub ho hN hp hrp hr2
      have hrN : r ∈ N.primeFactors :=
        Nat.mem_primeFactors.mpr
          ⟨hr_prime, (hr_prime.dvd_iff_one_le_factorization hN.2.ne').mpr (by omega), hN.2.ne'⟩
      have hr_not_sat : r ∉ sat := by
        intro hrsat
        have heq := (Finset.mem_filter.mp hrsat).2
        omega
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hrp, hrN⟩, hr_not_sat⟩
  refine ⟨hsub, fun hodd => ?_⟩
  have hnot2 : 2 ∉ (componentIndex N p).primeFactors := by
    intro h2
    exact hodd.not_two_dvd_nat (Nat.dvd_of_mem_primeFactors h2)
  have hsub_odd : (componentIndex N p).primeFactors ⊆ N.primeFactors.erase p \ sat := by
    intro r hr
    rcases Finset.mem_insert.mp (hsub hr) with rfl | hmem
    · exact (hnot2 hr).elim
    · exact hmem
  have hle : (componentIndex N p).primeFactors.card ≤ (N.primeFactors.erase p \ sat).card :=
    Finset.card_le_card hsub_odd
  have hsdiff : (N.primeFactors.erase p \ sat).card + sat.card = (N.primeFactors.erase p).card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  have herase : (N.primeFactors.erase p).card + 1 = N.primeFactors.card :=
    Finset.card_erase_add_one hp
  exact ⟨hsub_odd, by omega⟩

/-- On a sixth-power-free odd perfect number `N`, the incoming vacuum `S₅₀ ∪ Q₂₃` saturates in
`σ(q^1)`, forcing the distinct prime-factor drop
`ω(componentIndex N q) + 1 + #S₅₀ + #Q₂₃ ≤ ω(N)`. -/
theorem sixth_power_free_euler_index_distinct_drop {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    (componentIndex N q).primeFactors.card + 1 +
      ((squareSources N).filter (· % 5 ≠ 1)).card +
      (twoModThreeLargeSources N q).card ≤ N.primeFactors.card := by
  let S₅₀ := (squareSources N).filter (· % 5 ≠ 1)
  let Q₂₃ := twoModThreeLargeSources N q
  let sat := (N.primeFactors.erase q).filter
    (fun r => (sigma 1 (ordProj[q] N)).factorization r = N.factorization r)
  have hodd_ci : Odd (componentIndex N q) :=
    ((componentIndex_two_valuation_dichotomy ho hN hq hq4 he hev hq).1 rfl).2
  have hdrop := componentIndex_primeFactors_subset_and_saturation_drop ho hN hq
  dsimp only at hdrop
  have hcard_sat : (componentIndex N q).primeFactors.card + 1 + sat.card ≤ N.primeFactors.card :=
    (hdrop.2 hodd_ci).2
  have hvac := sixth_power_free_incoming_source_vacuum ho hN hq hq4 he hev hfree
  dsimp only at hvac
  have hsub_sat : S₅₀ ∪ Q₂₃ ⊆ sat := by
    intro r hr
    have hfac_eq : (sigma 1 (ordProj[q] N)).factorization r = N.factorization r :=
      (hvac.1 r hr).2.2.2.2.2.2.2.2
    have hr_erase : r ∈ N.primeFactors.erase q := by
      rcases Finset.mem_union.mp hr with hrS | hrQ
      · have hr_sq := (Finset.mem_filter.mp hrS).1
        obtain ⟨hr_mem, _, hr_exp⟩ := Finset.mem_filter.mp hr_sq
        have hrq : r ≠ q := by
          rintro rfl
          omega
        exact Finset.mem_erase.mpr ⟨hrq, hr_mem⟩
      · have hr_lg := (Finset.mem_filter.mp hrQ).1
        obtain ⟨hr_mem, _, hrq, _⟩ := Finset.mem_filter.mp hr_lg
        exact Finset.mem_erase.mpr ⟨hrq, hr_mem⟩
    exact Finset.mem_filter.mpr ⟨hr_erase, hfac_eq⟩
  have hdisj : Disjoint S₅₀ Q₂₃ := by
    apply Finset.disjoint_left.mpr
    intro r hrS hrQ
    have hr_sq := (Finset.mem_filter.mp hrS).1
    have hr_lg := (Finset.mem_filter.mp hrQ).1
    have h2 : N.factorization r = 2 := (Finset.mem_filter.mp hr_sq).2.2
    have h4 : 4 ≤ N.factorization r := (Finset.mem_filter.mp hr_lg).2.2.2
    omega
  have hcard_union : ((squareSources N).filter (· % 5 ≠ 1)).card +
      (twoModThreeLargeSources N q).card ≤ sat.card := by
    change S₅₀.card + Q₂₃.card ≤ sat.card
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hsub_sat
  omega

end OddPerfect
