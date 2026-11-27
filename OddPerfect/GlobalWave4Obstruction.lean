module

public import OddPerfect.GlobalAbundancyObstruction
public import OddPerfect.DeficientFourClassification
public import OddPerfect.DeficientEuler
public import OddPerfect.PrimeFive
public import OddPerfect.ZelinskyFullSlope
public import OddPerfect.PrimePowerHigherObstruction
public import OddPerfect.ExceptionalBranchClosure
public import OddPerfect.RestrainedExponents
public import OddPerfect.HarmonicBoundedExp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Wave 4 Global Obstruction Synthesis (`OddPerfect.GlobalWave4Obstruction`)

Tier 2 global synthesis coupling Wave 1 (`DeficientFourClassification`, `PrimeFive`) and
Wave 2 (`ZelinskyFullSlope`, `PrimePowerHigherObstruction`, `ExceptionalBranchClosure`,
`RestrainedExponents`, `HarmonicBoundedExp`) across Bridges `B0`–`B3`:
1. `euler_exp_one_toth_pair_and_six_primes`: isolates Non-Spoofable Invariant `I1` (primality
   of `q`) on `N = q * m ^ 2`, separating genuine `a = 1` odd perfect numbers from Descartes's
   spoof `198585576189 = 22021 * 9018009` via `toth_odd_pair_four_iff`.
2. `near_full_componentIndex_caps_twoModThreeLarge` and
   `exists_componentIndex_cardFactors_add_five_le_of_two_twoModThreeLarge`: unconditional
   Dual Bridge `B3` reduction via Vieta mod-3 root-slot slack (`21 * ω + 11 * |L₂| ≤ 8 * Ω + 39`).
3. `not_all_componentIndex_near_full_of_multi_block`: unconditional Dual Bridge `B3` collapse
   in the multi-block `554/199` slope regime.
4. `three_free_sixthPowerFree_forces_147_largeSources`: couples `sixth_power_or_large_support`
   with `squareSources_vieta_root_slot_incidence_three_free` and `multi_block_slope_above_zelinsky`,
   forcing `147 ≤ (largeSources N q).card` and `1231 ≤ Ω(N)`.
5. `odd_perfect_wave4_master_profile`: unified kernel-checked Wave-4 global obstruction profile.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction
open scoped NumberTheorySymbols

/-- At Euler exponent `a = 1` (`N = q * m ^ 2`), `(m ^ 2, q)` forms a nontrivial odd `TothPair`
and `(m ^ 2, σ(m ^ 2) / q)` is deficient-perfect; `toth_odd_pair_four_iff` combined with
`q.Prime` (`22021 = 19 * 1159` is composite) independently forces `5 ≤ ω(m)` and `6 ≤ ω(N)`. -/
theorem euler_exp_one_toth_pair_and_six_primes {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    TothPair (m ^ 2) q ∧
    DeficientPerfectWith (m ^ 2) (sigma 1 (m ^ 2) / q) ∧
    5 ≤ m.primeFactors.card ∧
    6 ≤ N.primeFactors.card := by
  have hqodd : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2))
  have hm2odd : Odd (m ^ 2) := ho.of_dvd_nat (hform ▸ dvd_mul_left (m ^ 2) q)
  have hc : (m ^ 2).Coprime q :=
    (hq.coprime_iff_not_dvd.mpr (fun h => hqm (hq.dvd_of_dvd_pow h))).symm
  have hp : (m ^ 2 * q).Perfect := by rwa [mul_comm, ← hform]
  have hpair : TothPair (m ^ 2) q := tothPair_of_linear_euler hm2odd hq hc hp
  have hdef : DeficientPerfectWith (m ^ 2) (sigma 1 (m ^ 2) / q) :=
    exponent_one_cofactor_deficientPerfect hN ho hq hqm hform
  have hm_ge5 : 5 ≤ m.primeFactors.card := by
    by_contra! hlt
    have hm2_le4 : (m ^ 2).primeFactors.card ≤ 4 := by
      rw [Nat.primeFactors_pow m (by decide : 2 ≠ 0)]
      omega
    obtain ⟨_, hq_eq⟩ := (toth_odd_pair_four_iff hm2_le4 hqodd hq.one_lt).mp hpair
    rw [hq_eq] at hq
    have h19 : 19 ∣ 22021 := ⟨1159, rfl⟩
    have := hq.eq_one_or_self_of_dvd 19 h19
    omega
  have hq_not_mem : q ∉ m.primeFactors := fun h => hqm (Nat.dvd_of_mem_primeFactors h)
  have hsub : insert q m.primeFactors ⊆ N.primeFactors := by
    intro r hr
    rcases Finset.mem_insert.mp hr with hrq | hrm
    · subst r
      exact Nat.mem_primeFactors.mpr ⟨hq, hform ▸ dvd_mul_right q (m ^ 2), hN.2.ne'⟩
    · have hrp := Nat.prime_of_mem_primeFactors hrm
      have hrd : r ∣ N := (Nat.dvd_of_mem_primeFactors hrm).trans
        (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self m (by decide : 2 ≠ 0)) q)
      exact Nat.mem_primeFactors.mpr ⟨hrp, hrd, hN.2.ne'⟩
  have hcard_ins : (insert q m.primeFactors).card = m.primeFactors.card + 1 :=
    Finset.card_insert_of_notMem hq_not_mem
  have hN_ge6 : 6 ≤ N.primeFactors.card := by
    have := Finset.card_le_card hsub
    omega
  exact ⟨hpair, hdef, hm_ge5, hN_ge6⟩

/-- Unconditional Dual Bridge `B3` cap on `twoModThreeLargeSources`: if every prime component
satisfies `Ω(N) < Ω(i_p) + 5`, then `(twoModThreeLargeSources N q).card ≤ 1`, and if equality
holds (`card = 1`), then `Ω(N) ≤ 59` and `ω(N) ≤ 23`. -/
theorem near_full_componentIndex_caps_twoModThreeLarge {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hnear : ∀ p ∈ N.primeFactors, cardFactors N < cardFactors (componentIndex N p) + 5) :
    (twoModThreeLargeSources N q).card ≤ 1 ∧
      ((twoModThreeLargeSources N q).card = 1 →
        cardFactors N ≤ 59 ∧ N.primeFactors.card ≤ 23) := by
  have hle5 : ∀ p ∈ N.primeFactors,
      N.factorization p + cardFactors (sigma 1 (ordProj[p] N)) ≤ 5 := by
    intro p hp
    have hcons := cardFactors_componentIndex_add_eq hN hp
    have hlt := hnear p hp
    omega
  have hsum : 1 + 2 * cardFactors N ≤ 5 * N.primeFactors.card := by
    calc
      1 + 2 * cardFactors N
          = ∑ p ∈ N.primeFactors, (N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) :=
            (sum_component_factor_capture ho hN).symm
      _ ≤ ∑ _p ∈ N.primeFactors, 5 := Finset.sum_le_sum hle5
      _ = 5 * N.primeFactors.card := by simp [Nat.mul_comm]
  have hlen : cardFactors N = N.primeFactorsList.length := cardFactors_apply
  have h37 := thirty_seven_le_total_prime_factor_count ho hN
  have hslope := sharpened_cyclotomic_prime_factor_count ho hN hq hq4 he hev
  constructor
  · omega
  · intro hcard1
    omega

/-- Unconditionally for all odd perfect numbers (even when `3 ∣ N` and `Ω(N) < 88`),
having two or more large prime factors `r ≢ 1 [MOD 3]` forces some prime component `p ∣ N`
to satisfy `Ω(i_p) + 5 ≤ Ω(N)` and capture at least `6` prime factors with multiplicity. -/
theorem exists_componentIndex_cardFactors_add_five_le_of_two_twoModThreeLarge {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hL2 : 2 ≤ (twoModThreeLargeSources N q).card) :
    ∃ p ∈ N.primeFactors,
      cardFactors (componentIndex N p) + 5 ≤ cardFactors N ∧
      6 ≤ N.factorization p + cardFactors (sigma 1 (ordProj[p] N)) := by
  by_contra! hnot
  have hnear : ∀ p ∈ N.primeFactors, cardFactors N < cardFactors (componentIndex N p) + 5 := by
    intro p hp
    have hcons := cardFactors_componentIndex_add_eq hN hp
    by_contra! hge
    have := hnot p hp hge
    omega
  have hc := (near_full_componentIndex_caps_twoModThreeLarge ho hN hq hq4 he hev hnear).1
  omega

/-- In the multi-block regime (`¬ 3 ∣ N`, `¬ 5 ∣ N`, `∀ u ∈ squareSources N, u % 5 ≠ 1`),
Dual Bridge `B3`'s near-full branch `∀ p ∈ N.primeFactors, Ω(N) < Ω(i_p) + 5` is empty. -/
theorem not_all_componentIndex_near_full_of_multi_block {N : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (h3 : ¬ 3 ∣ N) (_h5 : ¬ 5 ∣ N)
    (_hdisj : ∀ u ∈ squareSources N, u % 5 ≠ 1) :
    ¬ (∀ p ∈ N.primeFactors, cardFactors N < cardFactors (componentIndex N p) + 5) := by
  intro hnear
  obtain ⟨p, hp, h5le, _⟩ :=
    exists_componentIndex_cardFactors_add_five_le_of_large_or_three_free ho hN (Or.inl h3)
  exact (hnear p hp).not_ge h5le

/-- If `¬ 3 ∣ N` and no sixth prime power divides `N`, then every prime in `largeSources N q`
has exact exponent `4`, `147 ≤ (largeSources N q).card`, and if additionally `¬ 5 ∣ N` and
`∀ u ∈ squareSources N, u % 5 ≠ 1`, then `1231 ≤ Ω(N)`. -/
theorem three_free_sixthPowerFree_forces_147_largeSources {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) (hno6 : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    (∀ r ∈ largeSources N q, N.factorization r = 4) ∧
    147 ≤ (largeSources N q).card ∧
    (¬ 5 ∣ N → (∀ u ∈ squareSources N, u % 5 ≠ 1) → 1231 ≤ N.primeFactorsList.length) := by
  obtain ⟨h443, _, _⟩ :=
    (sixth_power_or_large_support ho hN).resolve_left fun ⟨p, hp, hp6⟩ => hno6 p hp hp6
  have hq_prime := Nat.prime_of_mem_primeFactors hq
  have hq_le5 : N.factorization q ≤ 5 := by
    by_contra! hge6
    exact hno6 q hq_prime ((hq_prime.pow_dvd_iff_le_factorization hN.2.ne').2 hge6)
  have hlarge_eq4 : ∀ r ∈ largeSources N q, N.factorization r = 4 := by
    intro r hr
    obtain ⟨hr_mem, _, hrq, hr4⟩ := Finset.mem_filter.mp hr
    have hr_prime := Nat.prime_of_mem_primeFactors hr_mem
    have hr_lt6 : ¬ 6 ≤ N.factorization r := fun hge6 =>
      hno6 r hr_prime ((hr_prime.pow_dvd_iff_le_factorization hN.2.ne').2 hge6)
    obtain ⟨k, hk⟩ := hev r hrq
    omega
  have h3not : 3 ∉ N.primeFactors := fun h => h3 (Nat.dvd_of_mem_primeFactors h)
  have hS1_zero : (squareSourcesOne N).card = 0 := by
    have hb := squareSourcesOne_card_le_three_exponent hN
    have hz : N.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd h3
    omega
  have hsq_card : (squareSources N).card = (squareSourcesTwo N).card := by
    rw [squareSources_eq_union_one_two N,
      Finset.card_union_of_disjoint (squareSourcesOne_disjoint_two N), hS1_zero, zero_add]
  have hpos {r : ℕ} (hr : r ∈ N.primeFactors) : 0 < N.factorization r :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
  have hparts : N.primeFactors.erase q = squareSources N ∪ largeSources N q := by
    ext r
    simp only [Finset.mem_erase, squareSources, largeSources, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hrq, hr⟩
      have hr3 : r ≠ 3 := fun h => h3not (h ▸ hr)
      obtain ⟨k, hk⟩ := hev r hrq
      have := hpos hr
      by_cases htwo : N.factorization r = 2
      · exact Or.inl ⟨hr, hr3, htwo⟩
      · exact Or.inr ⟨hr, hr3, hrq, by omega⟩
    · rintro (⟨hr, _, htwo⟩ | ⟨hr, _, hrq, _⟩)
      · exact ⟨fun h => by subst r; omega, hr⟩
      · exact ⟨hrq, hr⟩
  have hdis : Disjoint (squareSources N) (largeSources N q) := by
    apply Finset.disjoint_left.mpr
    intro r hs hl
    have htwo := (Finset.mem_filter.mp hs).2.2
    have hlarge := (Finset.mem_filter.mp hl).2.2.2
    omega
  have hcard_tot : (squareSourcesTwo N).card + (largeSources N q).card + 1 = N.primeFactors.card := by
    rw [← hsq_card, ← Finset.card_union_of_disjoint hdis, ← hparts, Finset.card_erase_add_one hq]
  have hL1_sub : oneModThreeLargeSources N q ⊆ largeSources N q := Finset.filter_subset _ _
  have hL1_le : (oneModThreeLargeSources N q).card ≤ (largeSources N q).card :=
    Finset.card_le_card hL1_sub
  have hL1_sum : ∑ r ∈ oneModThreeLargeSources N q, N.factorization r =
      4 * (oneModThreeLargeSources N q).card := by
    calc
      _ = ∑ _r ∈ oneModThreeLargeSources N q, (4 : ℕ) :=
        Finset.sum_congr rfl fun r hr => hlarge_eq4 r (hL1_sub hr)
      _ = _ := by simp [Nat.mul_comm]
  have hinc := squareSources_vieta_root_slot_incidence_three_free ho hN hq hq4 he hev h3
  rw [hL1_sum] at hinc
  have h147 : 147 ≤ (largeSources N q).card := by omega
  refine ⟨hlarge_eq4, h147, ?_⟩
  intro h5 hdisj
  have hmb := multi_block_slope_above_zelinsky ho hN h3 h5 hdisj
  have hodd_len := Nat.odd_iff.mp (odd_total_prime_factor_count ho hN)
  omega

/-- Unified Wave-4 global obstruction profile combining Wave 1 (`PrimeFive`,
`DeficientFourClassification`) and Wave 2 (`ZelinskyFullSlope`, `PrimePowerHigherObstruction`,
`ExceptionalBranchClosure`, `RestrainedExponents`). -/
theorem odd_perfect_wave4_master_profile {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    10 ^ 300 < N ∧
    6 ≤ N.primeFactors.card ∧
    37 ≤ cardFactors N ∧
    (∀ r ∈ N.primeFactors, ∀ p j, p.Prime → 0 < j → componentIndex N r = p ^ j →
      30028 ≤ j ∧ 10 ^ 17240 < componentIndex N r ∧ 10 ^ 17240 < N ∧
      (Even j → HasFiveOddPrimeRepunits p ∧ 8 ≤ N.primeFactors.card ∧
        10 ^ 300280 < componentIndex N r ∧ 10 ^ 300280 < N)) ∧
    ∃ q a m, q.Prime ∧ q % 4 = 1 ∧ a % 4 = 1 ∧ ¬ q ∣ m ∧ N = q ^ a * m ^ 2 ∧
      q ∈ N.primeFactors ∧ N.factorization q = a ∧
      (∀ r, r ≠ q → Even (N.factorization r)) ∧
      (a = 1 → TothPair (m ^ 2) q ∧
        DeficientPerfectWith (m ^ 2) (sigma 1 (m ^ 2) / q) ∧
        5 ≤ m.primeFactors.card) ∧
      21 * N.primeFactors.card + 11 * (twoModThreeLargeSources N q).card ≤
        8 * cardFactors N + 39 ∧
      (2 ≤ (twoModThreeLargeSources N q).card →
        ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 5 ≤ cardFactors N) ∧
      (¬ 3 ∣ N ∧ ¬ 5 ∣ N ∧ (∀ u ∈ squareSources N, u % 5 ≠ 1) →
        554 * N.primeFactors.card ≤ 199 * cardFactors N + 595) ∧
      (∀ l t, 1 < a → l.Prime → sigma 1 (m ^ 2) / q ^ a = l * t ^ 2 →
        10 ^ 740 < N ∧ J((((a + 1) / 2 : ℕ) : ℤ) | l) = 1) ∧
      (largeSources N q = ∅ → 8 ≤ N.factorization 3) ∧
      (¬ 3 ∣ N → (largeSources N q).card ≤ 1 →
        ∃ r₀, largeSources N q = {r₀} ∧ 14 ≤ a + N.factorization r₀) := by
  refine ⟨ten_pow_three_hundred_lt_of_odd_perfect ho hN,
    six_le_distinct_prime_factor_count ho hN,
    by simpa [cardFactors_apply] using thirty_seven_le_total_prime_factor_count ho hN,
    ?_, ?_⟩
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
    obtain ⟨hj30028, hi17240, hN17240, hev_sz⟩ :=
      component_prime_power_index_exponent_ge_30028 hN ho hr_prime ha_pos hNb hrb hleft hright hp hj hi_eq
    refine ⟨hj30028, hci ▸ hi17240, hN17240, ?_⟩
    intro hj_even
    obtain ⟨hi300280, hN300280⟩ := hev_sz hj_even
    obtain ⟨u, rfl⟩ := hj_even
    have hu : 0 < u := by omega
    have hi2 : i = p ^ (2 * u) := by
      rw [hi_eq, show u + u = 2 * u by ring]
    obtain ⟨hfive, h8⟩ :=
      even_prime_power_component_forces_five_repunits_and_eight_primes
        hN ho hr_prime ha_pos hNb hrb hleft hright hp hu hi2
    exact ⟨hfive, h8, hci ▸ hi300280, hN300280⟩
  · obtain ⟨q, a, m, hq, hq4, ha4, hqm, hform⟩ := euler_form ho hN
    have ha_pos : 0 < a := by omega
    have hm : Odd m := ho.of_dvd_nat
      (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self m (by decide : 2 ≠ 0)) _)
    have hqN : q ∈ N.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq, hform ▸ dvd_mul_of_dvd_left (dvd_pow_self q ha_pos.ne') _, hN.2.ne'⟩
    have hval : N.factorization q = a := by
      rw [hform, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hm.pos.ne'),
        Finsupp.add_apply, hq.factorization_pow, Finsupp.single_eq_same, Nat.factorization_pow,
        Finsupp.smul_apply, Nat.factorization_eq_zero_of_not_dvd hqm, smul_eq_mul, mul_zero, add_zero]
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
    refine ⟨q, a, m, hq, hq4, ha4, hqm, hform, hqN, hval, hev, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ha1
      have hform1 : N = q * m ^ 2 := by simpa [ha1] using hform
      obtain ⟨hpair, hdef, hm5, _⟩ :=
        euler_exp_one_toth_pair_and_six_primes ho hN hq hqm hform1
      exact ⟨hpair, hdef, hm5⟩
    · simpa [cardFactors_apply] using
        sharpened_cyclotomic_prime_factor_count ho hN hqN hq4 he4 hev
    · intro hL2
      obtain ⟨p, hp, h5, _⟩ :=
        exists_componentIndex_cardFactors_add_five_le_of_two_twoModThreeLarge
          ho hN hqN hq4 he4 hev hL2
      exact ⟨p, hp, h5⟩
    · rintro ⟨h3, h5, hdisj⟩
      simpa [cardFactors_apply] using multi_block_slope_above_zelinsky ho hN h3 h5 hdisj
    · intro l t ha_gt1 hl hi
      exact ⟨exceptional_index_size_gt_ten_pow_740 hN ho hq hq4 ha4 ha_gt1 hqm hform hl hi,
        (exceptional_euler_full_reciprocity_and_source_parity
          hN ho hq hq4 ha4 ha_gt1 hqm hform hl hi).1⟩
    · exact eight_le_three_exponent_of_largeSources_empty ho hN hqN hq4 he4 hev
    · intro h3 hle1
      obtain ⟨r₀, hr₀, _, h14⟩ :=
        restrained_three_free_bounds ho hN hqN hq4 he4 hev h3 hle1
      exact ⟨r₀, hr₀, by simpa [hval] using h14⟩

end OddPerfect
