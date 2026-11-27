module

public import OddPerfect.GlobalWave6Obstruction
public import OddPerfect.RestrainedLinearElimination
public import OddPerfect.SharpenedSymbolicRepunit
public import OddPerfect.SixthPowerFreeCofactorObstruction
public import OddPerfect.SevenFactorDropObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Wave 7 Global Obstruction Synthesis (`OddPerfect.GlobalWave7Obstruction`)

Tier 2 global synthesis unifying the four Wave 7 structural pillars:
1. `OddPerfect.RestrainedLinearElimination` + `OddPerfect.SevenFactorDropObstruction`:
   - Complete elimination of linear-Euler (`N.factorization q = 1`) and low-exponent
     (`N.factorization q < 17`) three-free restrained odd perfect candidates (`¬ 3 ∣ N →
     N.factorization q < 17 → 2 ≤ (largeSources N q).card`).
   - Coupling `restrained_three_free_euler_exp_ge_17` (`17 ≤ N.factorization q`) with
     `exists_componentIndex_cardFactors_add_seven_le_of_euler_exp_gt_one` proves unconditionally
     that **every three-free restrained odd perfect candidate admits a seven-factor component-index
     drop** (`exists_componentIndex_cardFactors_add_seven_le_of_three_free_restrained`).
2. `OddPerfect.SharpenedSymbolicRepunit` + `OddPerfect.ComponentIndexMatrix`:
   - Drops the `S₁.card ^ 2` factor in the symbolic repunit bound (`p < 4 * P_L ^ 2 ∨
     p ^ 3 < (2 * S₁.card * P_L) ^ 4`, and `p ^ 11 < (2 * S₁.card * P_L) ^ 12` when `e_min ≥ 6`),
     eliminating both `|S₁| = 7` and `|S₁| = 8` unconditionally and lifting prime-power component
     indices (possible only at `r = q`) for even `j` to `HasNineOddPrimeRepunits p`, `12 ≤ ω(N)`,
     `6469693228 ≤ j`, and `10 ^ 122924171332 < componentIndex N q` (`10 ^ 122924171332 < N`).
3. `OddPerfect.SixthPowerFreeCofactorObstruction`:
   - Quartic mutual exclusion (`∀ u v ∈ largeSources N q, ¬ u ∣ σ(v^4)`), incoming `588`-factor
     budget exclusively from `(q + 1) / 2` and `squareSources N`, and the exact dual mirror
     dichotomy for the unique `q`-source `r₀ ∣ m` (`r₀ ∈ S₅₁` with `c₀` supported in `Q₁₃`, or
     `r₀ ∈ Q₁₃` with `q % 60 = 1 ∧ 61 ≤ q` and `c₀` supported in `S₅₁`).
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- **Cross-Pillar Seven-Factor Drop on Three-Free Restrained Candidates**:
Every three-free restrained odd perfect number (`¬ 3 ∣ N`, `(largeSources N q).card ≤ 1`)
forces `17 ≤ N.factorization q` and therefore unconditionally admits a prime component
`p ∈ N.primeFactors` with `cardFactors (componentIndex N p) + 7 ≤ cardFactors N`. -/
theorem exists_componentIndex_cardFactors_add_seven_le_of_three_free_restrained {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) (hle : (largeSources N q).card ≤ 1) :
    17 ≤ N.factorization q ∧
    ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 7 ≤ cardFactors N := by
  obtain ⟨_, _, _, _, h17, _, _, _⟩ :=
    restrained_three_free_euler_exp_ge_17 ho hN hq hq4 he hev h3 hle
  exact ⟨h17, exists_componentIndex_cardFactors_add_seven_le_of_euler_exp_gt_one
    ho hN hq hq4 he hev (by omega)⟩

/-- **Non-Euler Prime-Power Exclusion & Wave 7 Nonuple-Repunit `10^122924171332` Lift**:
If `r ∈ N.primeFactors` has a prime-power component index `componentIndex N r = p ^ j` (`p.Prime`,
`0 < j`), then `r = q`, `Odd p`, `p ≠ q`, `36207 ≤ j`, `10 ^ 17240 < componentIndex N q`,
`10 ^ 17240 < N`, `Odd j → ¬ ExcludedFermatResidue q`, and for `Even j`:
`N.factorization q = 1`, `HasNineOddPrimeRepunits p`, `12 ≤ ω(N)`, `6469693228 ≤ j`,
`10 ^ 122924171332 < componentIndex N q`, and `10 ^ 122924171332 < N`. -/
theorem component_prime_power_index_euler_only_and_nonuple_lift {N q r p j : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ s : ℕ, s ≠ q → Even (N.factorization s))
    (hr : r ∈ N.primeFactors) (hp : p.Prime) (hj : 0 < j)
    (hci_eq : componentIndex N r = p ^ j) :
    r = q ∧ Odd p ∧ p ≠ q ∧
    36207 ≤ j ∧ 10 ^ 17240 < componentIndex N q ∧ 10 ^ 17240 < N ∧
    (Odd j → ¬ ExcludedFermatResidue q) ∧
    (Even j → N.factorization q = 1 ∧ HasNineOddPrimeRepunits p ∧ 12 ≤ N.primeFactors.card ∧
      6469693228 ≤ j ∧ 10 ^ 122924171332 < componentIndex N q ∧ 10 ^ 122924171332 < N) := by
  obtain ⟨hr_eq_q, hp_odd, hp_neq_q, hj36207, hi17240, hN17240, hodd_j, heven_w6⟩ :=
    component_prime_power_index_euler_only_and_septuple_lift
      ho hN hq hq4 he hev hr hp hj hci_eq
  subst r
  refine ⟨rfl, hp_odd, hp_neq_q, hj36207, hi17240, hN17240, hodd_j, fun hj_even => ?_⟩
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have ha_pos : 0 < N.factorization q := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hq)
  have hNb : N = q ^ N.factorization q * ordCompl[q] N :=
    (Nat.ordProj_mul_ordCompl_eq_self N q).symm
  have hqb : ¬ q ∣ ordCompl[q] N := Nat.not_dvd_ordCompl hq_prime hN.2.ne'
  obtain ⟨i, _, hleft, hright, _⟩ := exists_component_index hN hq_prime hNb hqb
  have hci : componentIndex N q = i := by
    rw [componentIndex, hleft]
    exact Nat.mul_div_cancel_left i (pow_pos hq_prime.pos _)
  have hi_eq : i = p ^ j := hci.symm.trans hci_eq
  obtain ⟨hq1, _, _, _, _, _⟩ := heven_w6 hj_even
  have hj_even' : Even j := hj_even
  obtain ⟨u, rfl⟩ := hj_even
  have hu : 0 < u := by omega
  have hi2 : i = p ^ (2 * u) := by
    rw [hi_eq, show u + u = 2 * u by ring]
  obtain ⟨hnine, h12⟩ :=
    even_prime_power_component_forces_nine_repunits_and_twelve_primes
      hN ho hq_prime ha_pos hNb hqb hleft hright hp hu hi2
  obtain ⟨hj64, hi122, hN122⟩ :=
    even_prime_power_component_size_gt_ten_pow_122924171332
      hN ho hq_prime ha_pos hNb hqb hleft hright hp hj hj_even' hi_eq
  exact ⟨hq1, hnine, h12, hj64, hi122.trans_eq hci.symm, hN122⟩

/-- Unified Wave 7 global obstruction profile across every odd perfect number `N`. -/
theorem odd_perfect_wave7_master_profile {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    (∃ p ∈ N.primeFactors,
      cardFactors (componentIndex N p) + 6 ≤ cardFactors N ∧
      7 ≤ N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) ∧
    ((∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 7 ≤ cardFactors N) ∨
      ((∀ p : ℕ, p.Prime → ¬ p ^ 8 ∣ N) ∧
        (∀ r ∈ N.primeFactors, N.factorization r = 6 → (sigma 1 (r ^ 6)).Prime ∧ r % 7 ≠ 1) ∧
        2 * cardFactors N + 1 ≤ 7 * N.primeFactors.card)) ∧
    ∃ q a m, q.Prime ∧ q % 4 = 1 ∧ a % 4 = 1 ∧ ¬ q ∣ m ∧ N = q ^ a * m ^ 2 ∧
      q ∈ N.primeFactors ∧ N.factorization q = a ∧
      (∀ r, r ≠ q → Even (N.factorization r)) ∧
      (1 < a → ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 7 ≤ cardFactors N) ∧
      (¬ 3 ∣ N → a < 17 → 2 ≤ (largeSources N q).card) ∧
      (¬ 3 ∣ N → (largeSources N q).card ≤ 1 →
        17 ≤ a ∧
        (∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 7 ≤ cardFactors N) ∧
        ∃ r₀, largeSources N q = {r₀} ∧ q % 12 = 1 ∧ r₀ % 3 = 1 ∧
          13 ≤ q ∧ 7 ≤ r₀ ∧ N.factorization r₀ % 3 ≠ 2) ∧
      (∀ r ∈ N.primeFactors, ∀ p j, p.Prime → 0 < j → componentIndex N r = p ^ j →
        r = q ∧ Odd p ∧ p ≠ q ∧ 36207 ≤ j ∧
        10 ^ 17240 < componentIndex N q ∧ 10 ^ 17240 < N ∧
        (Odd j → ¬ ExcludedFermatResidue q) ∧
        (Even j → a = 1 ∧ HasNineOddPrimeRepunits p ∧ 12 ≤ N.primeFactors.card ∧
          6469693228 ≤ j ∧ 10 ^ 122924171332 < componentIndex N q ∧ 10 ^ 122924171332 < N)) := by
  refine ⟨exists_component_capturing_seven_factors ho hN, ?_, ?_⟩
  · by_cases h7 : ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 7 ≤ cardFactors N
    · exact Or.inl h7
    · right
      push_neg at h7
      obtain ⟨q, hq, hq4, he, hev⟩ := euler_exponents ho hN
      obtain ⟨_, _, hfree8, hsex, hdens⟩ := no_seven_factor_drop_profile ho hN hq hq4 he hev h7
      exact ⟨hfree8, hsex, hdens⟩
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
    · intro hgt
      exact exists_componentIndex_cardFactors_add_seven_le_of_euler_exp_gt_one
        ho hN hqN hq4 he4 hev (hgt.trans_eq hval.symm)
    · intro h3 hlt17
      exact two_le_largeSources_of_three_free_euler_exp_lt_17
        ho hN hqN hq4 he4 hev h3 (hval.trans_lt hlt17)
    · intro h3 hle
      obtain ⟨r₀, hr₀, hq12, hr₀3, h17, hq13, hr₀7, hmod3⟩ :=
        restrained_three_free_euler_exp_ge_17 ho hN hqN hq4 he4 hev h3 hle
      have hdrop7 :=
        (exists_componentIndex_cardFactors_add_seven_le_of_three_free_restrained
          ho hN hqN hq4 he4 hev h3 hle).2
      exact ⟨h17.trans_eq hval, hdrop7, r₀, hr₀, hq12, hr₀3, hq13, hr₀7, hmod3⟩
    · intro r hr p j hp hj hci_eq
      obtain ⟨hrq, hp_odd, hp_neq, hj36207, hi17, hN17, hodd_j, heven_j⟩ :=
        component_prime_power_index_euler_only_and_nonuple_lift
          ho hN hqN hq4 he4 hev hr hp hj hci_eq
      refine ⟨hrq, hp_odd, hp_neq, hj36207, hi17, hN17, hodd_j, fun hje => ?_⟩
      obtain ⟨hq1, hnine, h12, hj64, hi122, hN122⟩ := heven_j hje
      exact ⟨hval.symm.trans hq1, hnine, h12, hj64, hi122, hN122⟩

end OddPerfect
