module

public import OddPerfect.GlobalWave4Obstruction
public import OddPerfect.HirakawaClosure
public import OddPerfect.ZelinskyCollisionDischarge
public import OddPerfect.QuarticTargetCapacity
public import OddPerfect.TothSplitExistence
public import OddPerfect.ExceptionalFermatCongruences
public import OddPerfect.SextupleRepunitObstruction
public import OddPerfect.CyclotomicSlopeRegions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Wave 5 Global Obstruction Synthesis (`OddPerfect.GlobalWave5Obstruction`)

Tier 2 global synthesis unifying the six Wave 5 structural pillars:
1. `OddPerfect.QuarticTargetCapacity`: incoming-source vacuum on sixth-power-free candidates and
   the **unconditional 6-factor component-index drop** (`exists_componentIndex_cardFactors_add_six_le`).
2. `OddPerfect.TothSplitExistence`: unsplit coprime `TothPair` characterization and unique
   `q`-source isolation (`linear_euler_unique_q_source_and_bound`) on `N = q * m ^ 2`.
3. `OddPerfect.ExceptionalFermatCongruences`: 48 excluded residue classes across 15 prime moduli
   for `q ^ d + 1 = 2 * y ^ 2`, plus the `¬ 3 ∣ N` jump to `q % 48 = 1`, `d % 24 = 1`, `73 ≤ d`,
   and `145 ≤ a`.
4. `OddPerfect.HirakawaClosure`: exact `Zsqrtd` / `Pell.IsFundamental` closure for Hirakawa's
   (2024) neighbor and second-block Pell solutions on `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2`.
5. `OddPerfect.ZelinskyCollisionDischarge`: cross-degree `Φ₃` / `Φ₅` root-collision discharge and
   the `5`-unconditional `409/149` coupled multi-block slope under `¬ 3 ∣ N`.
6. `OddPerfect.SextupleRepunitObstruction`: sextuple-repunit obstruction on even prime-power
   component indices (`510508 ≤ j`, `10 ^ 6636604 < i < N`, `9 ≤ ω(N)`) and unified `36207 ≤ j`
   floor across all prime-power component indices.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- Every odd perfect number `N` unconditionally admits a prime factor `p ∈ N.primeFactors`
whose component index drops by at least `6` prime factors (`Ω(i_p) + 6 ≤ Ω(N)`) and whose local
Euler block `p ^ v_p(N) * σ(p ^ v_p(N))` captures at least `7` prime factors with multiplicity. -/
theorem exists_component_capturing_seven_factors {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    ∃ p ∈ N.primeFactors,
      cardFactors (componentIndex N p) + 6 ≤ cardFactors N ∧
      7 ≤ N.factorization p + cardFactors (sigma 1 (ordProj[p] N)) := by
  obtain ⟨p, hp, hdrop⟩ := exists_componentIndex_cardFactors_add_six_le ho hN
  have hcons := cardFactors_componentIndex_add_eq hN hp
  exact ⟨p, hp, hdrop, by omega⟩

/-- On a sixth-power-free odd perfect number `N` with Euler prime `q`, the Euler component index
`componentIndex N q` satisfies `Ω(i_q) + 1 + 2 * |S₅₀| + 4 * |Q₂₃| ≤ Ω(N)` and every prime factor
of `componentIndex N q` satisfies `p % 5 = 1 ∨ p % 3 = 1` (lying strictly inside `S₅₁ ∪ Q₁₃`). -/
theorem sixth_power_free_euler_index_drop_and_support {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    cardFactors (componentIndex N q) + 1 +
      2 * ((squareSources N).filter (· % 5 ≠ 1)).card +
      4 * (twoModThreeLargeSources N q).card ≤ cardFactors N ∧
    ∀ p ∈ (componentIndex N q).primeFactors, p % 5 = 1 ∨ p % 3 = 1 := by
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have hq1 : N.factorization q = 1 := sixth_power_free_euler_exponent_one ho hN hq he hfree
  have hvac := sixth_power_free_incoming_source_vacuum ho hN hq hq4 he hev hfree
  dsimp only at hvac
  obtain ⟨_, _, hcard_le, hnot_dvd⟩ := hvac
  have hcons := cardFactors_componentIndex_add_eq hN hq
  refine ⟨by omega, ?_⟩
  intro p hp_ci
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_ci
  have hp_dvd_ci : p ∣ componentIndex N q := Nat.dvd_of_mem_primeFactors hp_ci
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  obtain ⟨hmul, hci_pos⟩ := componentIndex_mul_eq_two_mul hN hq
  have hsig_q : sigma 1 (ordProj[q] N) = q + 1 := by
    rw [hq1, pow_one, ← pow_one q, sigma_one_apply_prime_pow hq_prime]
    simp [Finset.sum_range_succ]
    ring
  have hp_ne2 : p ≠ 2 := by
    rintro rfl
    have h2_q1 : 2 ∣ sigma 1 (ordProj[q] N) := by
      rw [hsig_q]
      omega
    have h4_rhs : 4 ∣ 2 * N := by
      have h4_lhs : 4 ∣ componentIndex N q * ordProj[q] N * sigma 1 (ordProj[q] N) := by
        obtain ⟨c₁, hc₁⟩ := hp_dvd_ci
        obtain ⟨c₂, hc₂⟩ := h2_q1
        exact ⟨c₁ * ordProj[q] N * c₂, by rw [hc₁, hc₂]; ring⟩
      exact hmul ▸ h4_lhs
    exact ho.not_two_dvd_nat (Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) h4_rhs)
  have hp_dvd_N : p ∣ N := by
    have hp_2N : p ∣ 2 * N :=
      hmul ▸ (hp_dvd_ci.trans (dvd_mul_right _ _)).trans (dvd_mul_right _ _)
    refine (hp_prime.dvd_mul.mp hp_2N).resolve_left fun h2 => ?_
    exact hp_ne2 (((Nat.dvd_prime Nat.prime_two).mp h2).resolve_left hp_prime.ne_one)
  have hp_mem : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd_N, hN.2.ne'⟩
  have hp_neq : p ≠ q := by
    rintro rfl
    have hord_ne0 : ordProj[p] N ≠ 0 := pow_ne_zero _ hp_prime.ne_zero
    have hsig_ne0 : sigma 1 (ordProj[p] N) ≠ 0 := (sigma_pos 1 _ hord_ne0).ne'
    have hfac := congrArg (fun n => n.factorization p) hmul
    rw [Nat.factorization_mul (mul_ne_zero hci_pos.ne' hord_ne0) hsig_ne0, Finsupp.add_apply,
      Nat.factorization_mul hci_pos.ne' hord_ne0, Finsupp.add_apply,
      Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) hN.2.ne', Finsupp.add_apply] at hfac
    have hnot2 : ¬ p ∣ 2 := fun h2 =>
      hp_ne2 (((Nat.dvd_prime Nat.prime_two).mp h2).resolve_left hp_prime.ne_one)
    have h2_fac : (2 : ℕ).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hnot2
    have hord_fac : (ordProj[p] N).factorization p = 1 := by
      rw [hq1, pow_one, hp_prime.factorization_self]
    have hci_ge1 : 1 ≤ (componentIndex N p).factorization p :=
      (hp_prime.dvd_iff_one_le_factorization hci_pos.ne').mp hp_dvd_ci
    omega
  have hp_ne3 : p ≠ 3 := fun h => h3 (h ▸ hp_dvd_N)
  have hp_pos : 0 < N.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp_mem)
  have hp_lt6 : ¬ 6 ≤ N.factorization p := fun hge =>
    hfree p hp_prime ((hp_prime.pow_dvd_iff_le_factorization hN.2.ne').2 hge)
  obtain ⟨k, hk⟩ := hev p hp_neq
  by_cases htwo : N.factorization p = 2
  · have hp_sq : p ∈ squareSources N := Finset.mem_filter.mpr ⟨hp_mem, hp_ne3, htwo⟩
    by_cases hp5 : p % 5 = 1
    · exact Or.inl hp5
    · exfalso
      exact hnot_dvd p
        (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hp_sq, hp5⟩))) hp_dvd_ci
  · have hfour : 4 ≤ N.factorization p := by omega
    have hp_lg : p ∈ largeSources N q := Finset.mem_filter.mpr ⟨hp_mem, hp_ne3, hp_neq, hfour⟩
    by_cases hp3 : p % 3 = 1
    · exact Or.inr hp3
    · exfalso
      exact hnot_dvd p
        (Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hp_lg, hp3⟩))) hp_dvd_ci

/-- `5`-unconditional slope upgrades under `¬ 3 ∣ N` (removing `(h5 : ¬ 5 ∣ N)` from
`CyclotomicSlopeRegions`): a `1/6` cap on `S₅₁` forces `1199 * ω(N) ≤ 447 * Ω(N) + 3297`
(and Zelinsky's `302/113` slope for `ω(N) ≥ 497`), while a `1/7` cap on `S₅₁` forces
`401 * ω(N) ≤ 149 * Ω(N) + 1099` (yielding Zelinsky's `302/113` slope for `ω(N) ≥ 259`
and Clayton–Hansen's `51/19` slope for `ω(N) ≥ 702`). -/
theorem zelinsky_and_clayton_hansen_three_free_uncond_five {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) (h3 : ¬ 3 ∣ N) :
    (6 * ((squareSources N).filter (· % 5 = 1)).card ≤ N.primeFactors.card →
      1199 * N.primeFactors.card ≤ 447 * N.primeFactorsList.length + 3297 ∧
      (497 ≤ N.primeFactors.card →
        302 * N.primeFactors.card ≤ 113 * N.primeFactorsList.length + 286)) ∧
    (7 * ((squareSources N).filter (· % 5 = 1)).card ≤ N.primeFactors.card →
      401 * N.primeFactors.card ≤ 149 * N.primeFactorsList.length + 1099 ∧
      (259 ≤ N.primeFactors.card →
        302 * N.primeFactors.card ≤ 113 * N.primeFactorsList.length + 286) ∧
      (702 ≤ N.primeFactors.card →
        51 * N.primeFactors.card ≤ 19 * N.primeFactorsList.length + 46)) := by
  have h := multi_block_coupled_three_free_uncond_five_simple ho hN h3
  refine ⟨fun h6 => ⟨by omega, fun h497 => by omega⟩,
    fun h7 => ⟨by omega, fun h259 => by omega, fun h702 => by omega⟩⟩

/-- Unified Wave 5 global obstruction profile across every odd perfect number `N`. -/
theorem odd_perfect_wave5_master_profile {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    (∃ p ∈ N.primeFactors,
      cardFactors (componentIndex N p) + 6 ≤ cardFactors N ∧
      7 ≤ N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) ∧
    (∀ r ∈ N.primeFactors, ∀ p j, p.Prime → 0 < j → componentIndex N r = p ^ j →
      36207 ≤ j ∧ 10 ^ 17240 < componentIndex N r ∧ 10 ^ 17240 < N ∧
      (Odd j → ¬ ExcludedFermatResidue r) ∧
      (Even j → HasSixOddPrimeRepunits p ∧ 9 ≤ N.primeFactors.card ∧
        510508 ≤ j ∧ 10 ^ 6636604 < componentIndex N r ∧ 10 ^ 6636604 < N)) ∧
    (¬ 3 ∣ N →
      409 * N.primeFactors.card ≤
        149 * cardFactors N + 1099 +
          42 * ((squareSources N).filter (fun w => w % 5 = 1 ∧ (normalizedSquareSum w).Prime)).card +
          56 * ((squareSources N).filter (fun w => w % 5 = 1 ∧ ¬ (normalizedSquareSum w).Prime)).card) ∧
    ∃ q a m, q.Prime ∧ q % 4 = 1 ∧ a % 4 = 1 ∧ ¬ q ∣ m ∧ N = q ^ a * m ^ 2 ∧
      q ∈ N.primeFactors ∧ N.factorization q = a ∧
      (∀ r, r ≠ q → Even (N.factorization r)) ∧
      (a = 1 →
        (sigma 1 (m ^ 2)).factorization q = 1 ∧
        ∃ r₀ ∈ m.primeFactors,
          q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)) ∧
          (sigma 1 (r₀ ^ (2 * m.factorization r₀))).factorization q = 1 ∧
          sigma 1 (ordCompl[r₀] (m ^ 2)) ∣ sigma 1 (m ^ 2) / q ∧
          2 * q < 3 * r₀ ^ (2 * m.factorization r₀)) ∧
      ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
        a = 1 ∧
        (∏ p ∈ (squareSources N).filter (· % 5 ≠ 1), p ^ 2) *
          (∏ u ∈ twoModThreeLargeSources N q, u ^ 4) ∣ (q + 1) / 2 ∧
        (∀ p ∈ (componentIndex N q).primeFactors, p % 5 = 1 ∨ p % 3 = 1)) ∧
      (∀ l t, 1 < a → (l = 1 ∨ l.Prime) → sigma 1 (m ^ 2) / q ^ a = l * t ^ 2 →
        ¬ ExcludedFermatResidue q) ∧
      (∀ l t, 1 < a → l.Prime → sigma 1 (m ^ 2) / q ^ a = l * t ^ 2 →
        Pell.IsFundamental (hirakawaNeighborPell q) ∧
        ((3 ∣ N ∧ 3 ∣ m) ∨
          (¬ 3 ∣ N ∧ q % 48 = 1 ∧ ((a + 1) / 2) % 24 = 1 ∧ 73 ≤ (a + 1) / 2 ∧ 145 ≤ a)) ∧
        ∃ w z : ℕ, ∃ hd_odd : Odd ((a + 1) / 2),
          ∃ hqd1 : q ^ ((a + 1) / 2) + 1 = 2 * (((a + 1) / 2) * w * z) ^ 2,
          Pell.IsFundamental (hirakawaSecondBlockPell hd_odd hqd1)) := by
  refine ⟨exists_component_capturing_seven_factors ho hN, ?_, ?_, ?_⟩
  · intro r hr p j hp hj hci_eq
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
    obtain ⟨hj36207, hi17240, hN17240, hev_sz⟩ :=
      component_prime_power_index_exponent_ge_36207
        hN ho hr_prime ha_pos hNb hrb hleft hright hp hj hi_eq
    refine ⟨hj36207, hci ▸ hi17240, hN17240, ?_, ?_⟩
    · intro hj_odd hres
      exact componentIndex_ne_odd_prime_power_of_excluded_residue ho hN hr hres hp hj_odd hci_eq
    · intro hj_even
      obtain ⟨hj510508, hi6636604, hN6636604⟩ := hev_sz hj_even
      obtain ⟨u, rfl⟩ := hj_even
      have hu : 0 < u := by omega
      have hi2 : i = p ^ (2 * u) := by
        rw [hi_eq, show u + u = 2 * u by ring]
      obtain ⟨hsix, h9⟩ :=
        even_prime_power_component_forces_six_repunits_and_nine_primes
          hN ho hr_prime ha_pos hNb hrb hleft hright hp hu hi2
      exact ⟨hsix, h9, hj510508, hci ▸ hi6636604, hN6636604⟩
  · intro h3
    simpa [cardFactors_apply] using multi_block_coupled_three_free_uncond_five ho hN h3
  · obtain ⟨q, a, m, hq, hq4, ha4, hqm, hform⟩ := euler_form ho hN
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
    · intro ha1
      have hform1 : N = q * m ^ 2 := by simpa [ha1] using hform
      obtain ⟨hfac_m2, r₀, hr₀, hqdvd, hfac_r0, hcompl, hlt, _⟩ :=
        linear_euler_unique_q_source_and_bound ho hN hq hqm hform1
      exact ⟨hfac_m2, r₀, hr₀, hqdvd, hfac_r0, hcompl, hlt⟩
    · intro hfree
      have hq1 : N.factorization q = 1 := sixth_power_free_euler_exponent_one ho hN hqN he4 hfree
      have ha1 : a = 1 := hval.symm.trans hq1
      have hvac := sixth_power_free_incoming_source_vacuum ho hN hqN hq4 he4 hev hfree
      have hsupp := (sixth_power_free_euler_index_drop_and_support ho hN hqN hq4 he4 hev hfree).2
      exact ⟨ha1, hvac.2.1, hsupp⟩
    · intro l t ha_gt1 hl hi hres
      exact euler_index_ne_prime_mul_square_of_excluded_residue
        hN ho hq hq4 ha4 ha_gt1 hqm hform hl hres hi
    · intro l t ha_gt1 hl hi
      obtain ⟨_, _, _, _, _, _, hfund1, w, z, hd_odd, hqd1, _, _, _, hfund2⟩ :=
        exceptional_euler_pell_fundamental_profile hN ho hq hq4 ha4 ha_gt1 hqm hform hl hi
      have hdich := exceptional_euler_three_dvd_dichotomy hN ho hq hq4 ha4 ha_gt1 hqm hform hl hi
      exact ⟨hfund1, hdich, w, z, hd_odd, hqd1, hfund2⟩

end OddPerfect
