module

public import OddPerfect.ZsqrtTwoCombinedFirstSecondBlockSieve
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exceptional-Block Coprime Triple Factorization and `l`-Target Routing
(`OddPerfect.ExceptionalBlockCoprimeFactorizationAndTargetRouting`)

Combines the first-block reciprocity and order sieve
(`OddPerfect.ZsqrtTwoCombinedFirstSecondBlockSieve`), the unified second-block
mod-`d ^ 2` and `z.minFac` sieve (`OddPerfect.ZsqrtTwoUnifiedSieveAndSecondBlockModSq`),
and the cofactor factorization (`OddPerfect.DrisRegimes`) on the exceptional Euler-index
branch `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`, `d := (a + 1) / 2`)
to prove two unconditional theorems:

1. `exceptional_euler_coprime_triple_factorization_and_l_routing`:
   aligns the witnesses `(w, z, v)` across the first- and second-block decompositions,
   establishing `m = d * l * w * z * v * t`, full pairwise coprimality of `(d, l, z, w)`,
   `d * l * z ∣ m`, `83 ≤ z.minFac`, `d = 17 → 239 ≤ z.minFac`, `556631 ≤ d * l * z`,
   and the `l`-target routing `∀ p ∈ (sigma 1 (ordProj[l] N)).primeFactors, p = q ∨ p ∣ t`.
2. `exceptional_euler_three_and_five_free_coprime_triple_bounds`:
   sharpens the `z.minFac` and `d * l * z` lower bounds under `¬ 3 ∣ N`
   (`293 ≤ z.minFac`, `37494917 ≤ d * l * z`) and under `¬ 3 ∣ N → ¬ 5 ∣ N`
   (`1637 ≤ z.minFac`, `d = 241 → 2411 ≤ z.minFac`, `6572805461 ≤ d * l * z`).
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

private lemma not_prime_of_mul_eq {a b n : ℕ} (ha : 1 < a) (hb : 1 < b) (h : a * b = n) :
    ¬ Nat.Prime n := by
  intro hp
  have hdvd : a ∣ n := ⟨b, h.symm⟩
  rcases hp.eq_one_or_self_of_dvd a hdvd with h1 | han <;> nlinarith

private lemma d_ge_41_of_ne_17 {d : ℕ} (hd : d.Prime) (hd17 : 17 ≤ d) (hd8 : d % 8 = 1)
    (hne : d ≠ 17) : 41 ≤ d := by
  by_contra hd_lt
  have hd_cases : d = 17 ∨ d = 25 ∨ d = 33 := by omega
  rcases hd_cases with rfl | rfl | rfl
  · exact hne rfl
  · exact not_prime_of_mul_eq (by decide : 1 < 5) (by decide : 1 < 5) (by norm_num) hd
  · exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 11) (by norm_num) hd

private lemma z_minFac_ge_293_of_not_three {d z : ℕ}
    (hd : d.Prime) (hd24 : d % 24 = 1) (hd73 : 73 ≤ d)
    (hz_prime : z.Prime) (h2d : 2 * d ∣ z - 1) (hz_ge : 2 * d + 1 ≤ z) :
    293 ≤ z := by
  obtain ⟨k, hk⟩ := h2d
  have hz_eq : z = 2 * d * k + 1 := by omega
  have hk1 : 1 ≤ k := by
    rcases k with _ | k
    · simp at hk; omega
    · omega
  by_cases hd146 : 146 ≤ d
  · omega
  · have hd_cases : d = 73 ∨ d = 97 ∨ d = 121 ∨ d = 145 := by omega
    rcases hd_cases with rfl | rfl | rfl | rfl
    · have hk2 : 2 ≤ k := by
        by_contra hk_lt
        have hk_eq1 : k = 1 := by omega
        subst hk_eq1
        exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 49) (by norm_num)
          ((by omega : z = 147) ▸ hz_prime)
      omega
    · have hk2 : 2 ≤ k := by
        by_contra hk_lt
        have hk_eq1 : k = 1 := by omega
        subst hk_eq1
        exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 65) (by norm_num)
          ((by omega : z = 195) ▸ hz_prime)
      omega
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 11) (by decide : 1 < 11) (by norm_num))
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 5) (by decide : 1 < 29) (by norm_num))

private lemma d_ge_409_of_ne_241 {d : ℕ}
    (hd : d.Prime) (hd120 : d % 120 ∈ ({1, 49} : Finset ℕ)) (hd241 : 241 ≤ d)
    (hne : d ≠ 241) : 409 ≤ d := by
  have hd_mod : d % 120 = 1 ∨ d % 120 = 49 := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hd120
  by_contra hd_lt
  have hd_cases : d = 241 ∨ d = 289 ∨ d = 361 := by omega
  rcases hd_cases with rfl | rfl | rfl
  · exact hne rfl
  · exact not_prime_of_mul_eq (by decide : 1 < 17) (by decide : 1 < 17) (by norm_num) hd
  · exact not_prime_of_mul_eq (by decide : 1 < 19) (by decide : 1 < 19) (by norm_num) hd

private lemma z_minFac_ge_1637_of_ge_409 {d z : ℕ}
    (hd : d.Prime) (hd120 : d % 120 ∈ ({1, 49} : Finset ℕ)) (hd409 : 409 ≤ d)
    (hz_prime : z.Prime) (h2d : 2 * d ∣ z - 1) (hz_ge : 2 * d + 1 ≤ z) :
    1637 ≤ z := by
  have hd_mod : d % 120 = 1 ∨ d % 120 = 49 := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hd120
  obtain ⟨k, hk⟩ := h2d
  have hz_eq : z = 2 * d * k + 1 := by omega
  have hk1 : 1 ≤ k := by
    rcases k with _ | k
    · simp at hk; omega
    · omega
  by_cases hd818 : 818 ≤ d
  · omega
  · have hd_cases :
        d = 409 ∨ d = 481 ∨ d = 529 ∨ d = 601 ∨ d = 649 ∨ d = 721 ∨ d = 769 := by omega
    rcases hd_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hk2 : 2 ≤ k := by
        by_contra hk_lt
        have hk_eq1 : k = 1 := by omega
        subst hk_eq1
        exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 273) (by norm_num)
          ((by omega : z = 819) ▸ hz_prime)
      omega
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 13) (by decide : 1 < 37) (by norm_num))
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 23) (by decide : 1 < 23) (by norm_num))
    · have hk2 : 2 ≤ k := by
        by_contra hk_lt
        have hk_eq1 : k = 1 := by omega
        subst hk_eq1
        exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 401) (by norm_num)
          ((by omega : z = 1203) ▸ hz_prime)
      omega
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 11) (by decide : 1 < 59) (by norm_num))
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 7) (by decide : 1 < 103) (by norm_num))
    · have hk2 : 2 ≤ k := by
        by_contra hk_lt
        have hk_eq1 : k = 1 := by omega
        subst hk_eq1
        exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 513) (by norm_num)
          ((by omega : z = 1539) ▸ hz_prime)
      omega

/-- On the exceptional Euler-index branch `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2`
(`a > 1`, `l.Prime`, `d := (a + 1) / 2`), aligns the first- and second-block
factorization witnesses `(w, z, v)`, proving `m = d * l * w * z * v * t`, pairwise
coprimality among `d, l, z, w`, `d * l * z ∣ m`, the `z.minFac` and `d * l * z`
floors `83 ≤ z.minFac`, `d = 17 → 239 ≤ z.minFac`, `556631 ≤ d * l * z`, and
`∀ p ∈ (sigma 1 (ordProj[l] N)).primeFactors, p = q ∨ p ∣ t`. -/
theorem exceptional_euler_coprime_triple_factorization_and_l_routing
    {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    ∃ w z v : ℕ,
      0 < w ∧ 3 ≤ z ∧ 3 ≤ t ∧ Odd w ∧ Odd z ∧ Odd v ∧ Odd t ∧
      q + 1 = 2 * d * w ^ 2 ∧
      (q ^ d + 1) / (q + 1) = d * z ^ 2 ∧
      geometricBlock q d = l * v ^ 2 ∧
      m = d * l * w * z * v * t ∧
      Nat.Coprime d l ∧
      Nat.Coprime d z ∧
      Nat.Coprime l z ∧
      Nat.Coprime w z ∧
      Nat.Coprime l w ∧
      d * l * z ∣ m ∧
      83 ≤ z.minFac ∧
      (d = 17 → 239 ≤ z.minFac) ∧
      556631 ≤ d * l * z ∧
      (∀ p ∈ (sigma 1 (ordProj[l] N)).primeFactors, p = q ∨ p ∣ t) := by
  intro d
  obtain ⟨hd_prime, hd17, hd8, _, _, _, _, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  change d.Prime at hd_prime
  change 17 ≤ d at hd17
  change d % 8 = 1 at hd8
  have hd_pos : 0 < d := hd_prime.pos
  obtain ⟨_, _, _, _, _, ht3⟩ :=
    exceptional_index_parameter_floors hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨w, z, v, hw_odd, hz_odd, hv_odd, hq1, hdiv, hqd1, hgeom, hcop_wz, hdz, _⟩ :=
    exceptional_euler_second_block_exact_square hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨w', y', v', hq1', hqd1', hgeom', hm_eq', _, _, _, _, _⟩ :=
    exceptional_index_cofactor_factorization hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨_, _, _, _, hl137, _, w1, z1, _, hq1_1, hdiv_1, _, _, hcop_l1, _⟩ :=
    exceptional_euler_first_block_mod_eight_and_order_sieve
      hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨y2, w2, z2, _, hw2_pos, hz2_ge3, _, _, _, _, hq1_2, hdiv_2, _, _, _, _,
      h2d1_le, hs17, _, _⟩ :=
    exceptional_euler_second_block_mod_sq_and_z_minFac_sieve
      hN ho hq hq4 ha4 ha hqm hform hl hi
  have hw'_eq : w' = w := by
    have hsq : w' ^ 2 = w ^ 2 :=
      Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 * d) (hq1'.symm.trans hq1)
    exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hsq
  have hy'_eq : y' = d * w * z := by
    have hsq : y' ^ 2 = (d * w * z) ^ 2 :=
      Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) (hqd1'.symm.trans hqd1)
    exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hsq
  have hv'_eq : v' = v := by
    have hsq : v' ^ 2 = v ^ 2 :=
      Nat.eq_of_mul_eq_mul_left hl.pos (hgeom'.symm.trans hgeom)
    exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hsq
  have hw1_eq : w1 = w := by
    have hsq : w1 ^ 2 = w ^ 2 :=
      Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 * d) (hq1_1.symm.trans hq1)
    exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hsq
  have hz1_eq : z1 = z := by
    have hsq : z1 ^ 2 = z ^ 2 :=
      Nat.eq_of_mul_eq_mul_left hd_pos (hdiv_1.symm.trans hdiv)
    exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hsq
  have hw2_eq : w2 = w := by
    have hsq : w2 ^ 2 = w ^ 2 :=
      Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 * d) (hq1_2.symm.trans hq1)
    exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hsq
  have hz2_eq : z2 = z := by
    have hsq : z2 ^ 2 = z ^ 2 :=
      Nat.eq_of_mul_eq_mul_left hd_pos (hdiv_2.symm.trans hdiv)
    exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hsq
  have hw_pos : 0 < w := hw2_eq ▸ hw2_pos
  have hz_ge3 : 3 ≤ z := hz2_eq ▸ hz2_ge3
  have hz_min_ge : 2 * d + 1 ≤ z.minFac := hz2_eq ▸ h2d1_le
  have hs17_z : d = 17 → 239 ≤ z.minFac := fun hd => hz2_eq ▸ (hs17 hd).1
  have hm_eq : m = d * l * w * z * v * t := by
    rw [hm_eq', hv'_eq, hy'_eq]
    ring
  have hdlz_dvd : d * l * z ∣ m := ⟨w * v * t, by rw [hm_eq]; ring⟩
  have hm_ne0 : m ≠ 0 := by
    intro hm0
    rw [hm0] at hform
    simp at hform
    exact hN.2.ne' hform
  have hm_dvd_N : m ∣ N := by
    rw [hform]
    exact dvd_mul_of_dvd_right (dvd_pow_self m (by decide : 2 ≠ 0)) _
  have hm_odd : Odd m := ho.of_dvd_nat hm_dvd_N
  have ht_odd : Odd t := hm_odd.of_dvd_nat ⟨d * l * w * z * v, by rw [hm_eq]; ring⟩
  have hcop_l_2dwz : Nat.Coprime l (2 * d * w * z) := by
    simpa [hw1_eq, hz1_eq] using hcop_l1
  have hcop_dl : Nat.Coprime d l :=
    (hcop_l_2dwz.coprime_dvd_right ⟨2 * w * z, by ring⟩).symm
  have hcop_dz : Nat.Coprime d z := hd_prime.coprime_iff_not_dvd.mpr hdz
  have hcop_lz : Nat.Coprime l z := hcop_l_2dwz.coprime_dvd_right (dvd_mul_left z _)
  have hcop_lw : Nat.Coprime l w := hcop_l_2dwz.coprime_dvd_right ⟨2 * d * z, by ring⟩
  have hz_min_le_z : z.minFac ≤ z := Nat.minFac_le (by omega : 0 < z)
  have hz_min_83 : 83 ≤ z.minFac := by
    by_cases hd_eq17 : d = 17
    · exact le_trans (by decide : 83 ≤ 239) (hs17_z hd_eq17)
    · have hd41 : 41 ≤ d := d_ge_41_of_ne_17 hd_prime hd17 hd8 hd_eq17
      omega
  have hdlz_floor : 556631 ≤ d * l * z := by
    by_cases hd_eq17 : d = 17
    · have hz239 : 239 ≤ z := le_trans (hs17_z hd_eq17) hz_min_le_z
      have hmul : 17 * 137 * 239 ≤ d * l * z :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) hl137) hz239
      omega
    · have hd41 : 41 ≤ d := d_ge_41_of_ne_17 hd_prime hd17 hd8 hd_eq17
      have hl329 : 329 ≤ l := by
        have h8d1 : 8 * d + 1 ≤ l := by
          obtain ⟨_, _, _, h8d1_le', _, _⟩ :=
            exceptional_index_parameter_floors hN ho hq hq4 ha4 ha hqm hform hl hi
          exact h8d1_le'
        omega
      have hz83 : 83 ≤ z := le_trans hz_min_83 hz_min_le_z
      have hmul : 41 * 329 * 83 ≤ d * l * z :=
        Nat.mul_le_mul (Nat.mul_le_mul hd41 hl329) hz83
      omega
  have hl_routing : ∀ p ∈ (sigma 1 (ordProj[l] N)).primeFactors, p = q ∨ p ∣ t := by
    obtain ⟨i, _, hleft, _, _⟩ :=
      exists_component_index hN hq hform (fun h => hqm (hq.dvd_of_dvd_pow h))
    have hi_eq : i = l * t ^ 2 := by
      rw [← hi, hleft, Nat.mul_div_cancel_left i (pow_pos hq.pos a)]
    have hsig_m2 : sigma 1 (m ^ 2) = q ^ a * (l * t ^ 2) := by
      rw [hleft, hi_eq]
    have hm2_ne0 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm_ne0
    have hqa_ne0 : q ^ a ≠ 0 := pow_ne_zero a hq.ne_zero
    have hl_dvd_m : l ∣ m := ⟨d * w * z * v * t, by rw [hm_eq]; ring⟩
    have hl_ne_q : l ≠ q := fun h => hqm (h ▸ hl_dvd_m)
    have hl_ndvd_qa : ¬ l ∣ q ^ a := fun h =>
      hl_ne_q ((Nat.prime_dvd_prime_iff_eq hl hq).mp (hl.dvd_of_dvd_pow h))
    have hord_qa : ordProj[l] (q ^ a) = 1 := by
      rw [Nat.factorization_eq_zero_of_not_dvd hl_ndvd_qa, pow_zero]
    have hord_N : ordProj[l] N = ordProj[l] (m ^ 2) := by
      rw [hform, Nat.ordProj_mul l hqa_ne0 hm2_ne0, hord_qa, one_mul]
    have hsig_ord_dvd : sigma 1 (ordProj[l] N) ∣ sigma 1 (m ^ 2) := by
      rw [hord_N]
      have hm2_split : m ^ 2 = ordProj[l] (m ^ 2) * ordCompl[l] (m ^ 2) :=
        (Nat.ordProj_mul_ordCompl_eq_self (m ^ 2) l).symm
      have hm2_cop : (ordProj[l] (m ^ 2)).Coprime (ordCompl[l] (m ^ 2)) :=
        (Nat.coprime_ordCompl hl hm2_ne0).pow_left _
      conv_rhs => rw [hm2_split, isMultiplicative_sigma.map_mul_of_coprime hm2_cop]
      exact dvd_mul_right _ _
    intro p hp_mem
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hp_dvd_sig : p ∣ sigma 1 (ordProj[l] N) := Nat.dvd_of_mem_primeFactors hp_mem
    have hp_dvd_prod : p ∣ q ^ a * (l * t ^ 2) :=
      hsig_m2 ▸ hp_dvd_sig.trans hsig_ord_dvd
    rcases hp_prime.dvd_mul.mp hp_dvd_prod with hp_qa | hp_lt2
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp_prime hq).mp (hp_prime.dvd_of_dvd_pow hp_qa))
    · rcases hp_prime.dvd_mul.mp hp_lt2 with hp_l | hp_t2
      · have hp_eq_l : p = l := (Nat.prime_dvd_prime_iff_eq hp_prime hl).mp hp_l
        exfalso
        have hl_dvd_sig : l ∣ sigma 1 (l ^ N.factorization l) := by
          simpa [hp_eq_l] using hp_dvd_sig
        have hmod1 := sigma_prime_pow_mod_self hl (N.factorization l)
        have hmod0 := Nat.mod_eq_zero_of_dvd hl_dvd_sig
        have := hl.one_lt
        omega
      · exact Or.inr (hp_prime.dvd_of_dvd_pow hp_t2)
  exact ⟨w, z, v, hw_pos, hz_ge3, ht3, hw_odd, hz_odd, hv_odd, ht_odd,
    hq1, hdiv, hgeom, hm_eq, hcop_dl, hcop_dz, hcop_lz, hcop_wz, hcop_lw,
    hdlz_dvd, hz_min_83, hs17_z, hdlz_floor, hl_routing⟩

/-- Under `¬ 3 ∣ N` (resp. `¬ 3 ∣ N` and `¬ 5 ∣ N`) on the exceptional Euler-index branch
`sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`, `d := (a + 1) / 2`), sharpens the
lower bounds on `z.minFac` and `d * l * z` in the coprime triple factorization. -/
theorem exceptional_euler_three_and_five_free_coprime_triple_bounds
    {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    ∃ z : ℕ,
      3 ≤ z ∧
      (q ^ d + 1) / (q + 1) = d * z ^ 2 ∧
      d * l * z ∣ m ∧
      (¬ 3 ∣ N →
        293 ≤ z.minFac ∧
        37494917 ≤ d * l * z) ∧
      (¬ 3 ∣ N → ¬ 5 ∣ N →
        1637 ≤ z.minFac ∧
        (d = 241 → 2411 ≤ z.minFac) ∧
        6572805461 ≤ d * l * z) := by
  intro d
  obtain ⟨hd_prime, hd17, hd8, _, _, _, _, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  change d.Prime at hd_prime
  change 17 ≤ d at hd17
  change d % 8 = 1 at hd8
  have hd_pos : 0 < d := hd_prime.pos
  have hd5 : 5 ≤ d := by omega
  have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
  obtain ⟨w, z, v, hw_pos, hz_ge3, _, hw_odd, hz_odd, _, _, hq1, hdiv, _, _,
      _, hcop_dz, _, hcop_wz, _, hdlz_dvd, _, _, _, _⟩ :=
    exceptional_euler_coprime_triple_factorization_and_l_routing
      hN ho hq hq4 ha4 ha hqm hform hl hi
  have hndvd_dz : ¬ d ∣ z := hd_prime.coprime_iff_not_dvd.mp hcop_dz
  obtain ⟨_, hr_dvd, h2d1_z⟩ :=
    second_block_z_prime_divisors_one_mod_two_d
      hq hd_prime hd5 hd_odd hw_pos hz_odd hq1 hdiv hcop_wz hndvd_dz
  have hz_min_prime : z.minFac.Prime := Nat.minFac_prime (by omega : z ≠ 1)
  have hz_min_mem : z.minFac ∈ z.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hz_min_prime, Nat.minFac_dvd z, by omega⟩
  have h2d_zmin : 2 * d ∣ z.minFac - 1 := hr_dvd z.minFac hz_min_mem
  have hz_min_le_z : z.minFac ≤ z := Nat.minFac_le (by omega : 0 < z)
  obtain ⟨hfb3, hfb35⟩ :=
    exceptional_euler_first_block_three_and_five_free_bounds
      hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨_, _, z2, _, _, _, _, _, _, _, _, hdiv_2, _, _, _, _, _, _, _, hs241⟩ :=
    exceptional_euler_second_block_mod_sq_and_z_minFac_sieve
      hN ho hq hq4 ha4 ha hqm hform hl hi
  have hz2_eq : z2 = z := by
    have hsq : z2 ^ 2 = z ^ 2 :=
      Nat.eq_of_mul_eq_mul_left hd_pos (hdiv_2.symm.trans hdiv)
    exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hsq
  have hs241_z : d = 241 → 2411 ≤ z.minFac := fun hd => hz2_eq ▸ (hs241 hd).1
  refine ⟨z, hz_ge3, hdiv, hdlz_dvd, ?_, ?_⟩
  · intro hN3
    obtain ⟨_, hd24, hd73, _⟩ :=
      exceptional_euler_of_not_three_dvd hN ho hq hq4 ha4 ha hqm hform hl hi hN3
    change d % 24 = 1 at hd24
    change 73 ≤ d at hd73
    obtain ⟨_, hl1553, hl73, _⟩ := hfb3 hN3
    have hz_min_293 : 293 ≤ z.minFac :=
      z_minFac_ge_293_of_not_three hd_prime hd24 hd73 hz_min_prime h2d_zmin h2d1_z
    have hz293 : 293 ≤ z := le_trans hz_min_293 hz_min_le_z
    refine ⟨hz_min_293, ?_⟩
    by_cases hd_eq73 : d = 73
    · have hl1753 : 1753 ≤ l := hl73 hd_eq73
      have hmul : 73 * 1753 * 293 ≤ d * l * z :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) hl1753) hz293
      omega
    · have hd97 : 97 ≤ d := by omega
      have hmul : 97 * 1553 * 293 ≤ d * l * z :=
        Nat.mul_le_mul (Nat.mul_le_mul hd97 hl1553) hz293
      omega
  · intro hN3 hN5
    obtain ⟨_, _, hd120, hd241, _⟩ :=
      exceptional_euler_of_not_three_or_five_dvd hN ho hq hq4 ha4 ha hqm hform hl hi hN3 hN5
    change d % 120 ∈ ({1, 49} : Finset ℕ) at hd120
    change 241 ≤ d at hd241
    obtain ⟨_, hl9817, hl241, _⟩ := hfb35 hN3 hN5
    by_cases hd_eq241 : d = 241
    · have hz_min_2411 : 2411 ≤ z.minFac := hs241_z hd_eq241
      have hz_min_1637 : 1637 ≤ z.minFac := le_trans (by decide : 1637 ≤ 2411) hz_min_2411
      have hz2411 : 2411 ≤ z := le_trans hz_min_2411 hz_min_le_z
      have hl26993 : 26993 ≤ l := hl241 hd_eq241
      have hmul : 241 * 26993 * 2411 ≤ d * l * z :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) hl26993) hz2411
      exact ⟨hz_min_1637, hs241_z, by omega⟩
    · have hd409 : 409 ≤ d := d_ge_409_of_ne_241 hd_prime hd120 hd241 hd_eq241
      have hz_min_1637 : 1637 ≤ z.minFac :=
        z_minFac_ge_1637_of_ge_409 hd_prime hd120 hd409 hz_min_prime h2d_zmin h2d1_z
      have hz1637 : 1637 ≤ z := le_trans hz_min_1637 hz_min_le_z
      have hmul : 409 * 9817 * 1637 ≤ d * l * z :=
        Nat.mul_le_mul (Nat.mul_le_mul hd409 hl9817) hz1637
      exact ⟨hz_min_1637, hs241_z, by omega⟩

end OddPerfect
