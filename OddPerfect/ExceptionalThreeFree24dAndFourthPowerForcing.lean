module

public import OddPerfect.ExceptionalEuler42And486FactorDrop
public import OddPerfect.ZelinskyFullSlope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exceptional Three-Free `24 * d ∣ l - 1`, Fourth-Power Forcing, and Mod-5 Quintic Bounds
(`OddPerfect.ExceptionalThreeFree24dAndFourthPowerForcing`)

Strengthens the exceptional Euler-index branch `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2`
(`a > 1`, `l.Prime`, `d := (a + 1) / 2`) under `¬ 3 ∣ N` and under `¬ 3 ∣ N`, `¬ 5 ∣ N`:
1. `exceptional_euler_three_free_24d_and_fourth_powers`:
   under `¬ 3 ∣ N`, proves `geometricBlock q d % 3 = 1`, `l % 3 = 1`, `l % 24 = 1`,
   `24 * d ∣ l - 1`, `1753 ≤ l`, `d ≠ 73 → 4657 ≤ l`, fourth-power forcing
   `p ^ 4 ∣ N` (`p ∈ oneModThreeLargeSources N q`) for all `p ∣ m` with `p % 3 = 1`
   (in particular `d` and `l`), `d ∣ w * t`, `l ∣ v * t`, `d ^ 2 * l ^ 2 * z ∣ m`,
   and `4798187033573 ≤ d ^ 2 * l ^ 2 * z`.
2. `exceptional_euler_three_and_five_free_mod_five_and_quintic_bounds`:
   under `¬ 3 ∣ N` and `¬ 5 ∣ N`, proves `geometricBlock q d % 5 = 1 ∨ geometricBlock q d % 5 = 4`,
   `l % 5 = 1 ∨ l % 5 = 4`, `d = 241 → 28921 ≤ l`, `d ≠ 241 → 409 ≤ d ∧ 9817 ≤ l`,
   `d ^ 2 * l ^ 2 * z ∣ m`, `d = 241 → 117127239139407131 ≤ d ^ 2 * l ^ 2 * z`, and
   `26390819565150533 ≤ d ^ 2 * l ^ 2 * z`.
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

private lemma not_prime_of_mul_eq {a b n : ℕ} (ha : 1 < a) (hb : 1 < b) (h : a * b = n) :
    ¬ Nat.Prime n := by
  intro hp
  have hdvd : a ∣ n := ⟨b, h.symm⟩
  rcases hp.eq_one_or_self_of_dvd a hdvd with h1 | han <;> nlinarith

private lemma l_ge_4657_of_ne_73 {d l : ℕ}
    (hd : d.Prime) (hd24 : d % 24 = 1) (hd73 : 73 ≤ d) (hne : d ≠ 73)
    (hl : l.Prime) (h24d : 24 * d ∣ l - 1) (hl_ge : 24 * d + 1 ≤ l) :
    4657 ≤ l := by
  obtain ⟨k, hk⟩ := h24d
  have hl_eq : l = 24 * d * k + 1 := by omega
  have hk1 : 1 ≤ k := by
    rcases k with _ | k
    · simp at hk; omega
    · omega
  by_cases hd194 : 194 ≤ d
  · omega
  · have hd_cases : d = 97 ∨ d = 121 ∨ d = 145 ∨ d = 169 ∨ d = 193 := by omega
    rcases hd_cases with rfl | rfl | rfl | rfl | rfl
    · have hk2 : 2 ≤ k := by
        by_contra hk_lt
        have hk_eq1 : k = 1 := by omega
        subst hk_eq1
        exact not_prime_of_mul_eq (by decide : 1 < 17) (by decide : 1 < 137) (by norm_num)
          ((by omega : l = 2329) ▸ hl)
      omega
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 11) (by decide : 1 < 11) (by norm_num))
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 5) (by decide : 1 < 29) (by norm_num))
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 13) (by decide : 1 < 13) (by norm_num))
    · have hk2 : 2 ≤ k := by
        by_contra hk_lt
        have hk_eq1 : k = 1 := by omega
        subst hk_eq1
        exact not_prime_of_mul_eq (by decide : 1 < 41) (by decide : 1 < 113) (by norm_num)
          ((by omega : l = 4633) ▸ hl)
      omega

private lemma l_ge_28921_of_eq_241 {l : ℕ}
    (hl : l.Prime) (h24d : 24 * 241 ∣ l - 1) (hl_ge : 24 * 241 + 1 ≤ l) :
    28921 ≤ l := by
  obtain ⟨k, hk⟩ := h24d
  have hl_eq : l = 5784 * k + 1 := by omega
  have hk1 : 1 ≤ k := by
    rcases k with _ | k
    · simp at hk; omega
    · omega
  have hk5 : 5 ≤ k := by
    by_contra hk_lt
    have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk_cases with rfl | rfl | rfl | rfl
    · exact not_prime_of_mul_eq (by decide : 1 < 5) (by decide : 1 < 1157) (by norm_num)
        ((by omega : l = 5785) ▸ hl)
    · exact not_prime_of_mul_eq (by decide : 1 < 23) (by decide : 1 < 503) (by norm_num)
        ((by omega : l = 11569) ▸ hl)
    · exact not_prime_of_mul_eq (by decide : 1 < 7) (by decide : 1 < 2479) (by norm_num)
        ((by omega : l = 17353) ▸ hl)
    · exact not_prime_of_mul_eq (by decide : 1 < 17) (by decide : 1 < 1361) (by norm_num)
        ((by omega : l = 23137) ▸ hl)
  omega

private lemma d_ge_409_of_ne_241' {d : ℕ}
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

private lemma fourth_power_of_prime_dvd_m_one_mod_three
    {N q a m p : ℕ} (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m)
    (hform : N = q ^ a * m ^ 2) (hN3 : ¬ 3 ∣ N)
    (hp : p.Prime) (hpm : p ∣ m) (hp3 : p % 3 = 1) :
    2 ≤ m.factorization p ∧ p ^ 2 ∣ m ∧ 4 ≤ N.factorization p ∧ p ^ 4 ∣ N ∧
      p ∈ oneModThreeLargeSources N q := by
  have hN_ne0 : N ≠ 0 := hN.2.ne'
  have hm_ne0 : m ≠ 0 := by
    intro hm0
    rw [hm0] at hform
    simp at hform
    exact hN_ne0 hform
  have hm2_ne0 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm_ne0
  have hqa_ne0 : q ^ a ≠ 0 := pow_ne_zero a hq.ne_zero
  have hp_ne_q : p ≠ q := fun h => hqm (h ▸ hpm)
  have hp_ndvd_qa : ¬ p ∣ q ^ a := fun h =>
    hp_ne_q ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h))
  have hfac_qa : (q ^ a).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hp_ndvd_qa
  have hfac_N : N.factorization p = 2 * m.factorization p := by
    rw [hform, Nat.factorization_mul hqa_ne0 hm2_ne0, Finsupp.coe_add, Pi.add_apply,
      hfac_qa, zero_add, Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  have hmp_pos : 1 ≤ m.factorization p :=
    (hp.pow_dvd_iff_le_factorization hm_ne0).mp (by simpa using hpm)
  have hmp_ne1 : m.factorization p ≠ 1 := by
    intro hmp1
    have hNp2 : N.factorization p = 2 := by rw [hfac_N, hmp1]
    have hord_eq : ordProj[p] N = p ^ 2 := by
      rw [hNp2]
    have hN_split : N = ordProj[p] N * ordCompl[p] N :=
      (Nat.ordProj_mul_ordCompl_eq_self N p).symm
    have hN_cop : (ordProj[p] N).Coprime (ordCompl[p] N) :=
      (Nat.coprime_ordCompl hp hN_ne0).pow_left _
    have hsig_dvd : sigma 1 (ordProj[p] N) ∣ sigma 1 N := by
      conv_rhs => rw [hN_split, isMultiplicative_sigma.map_mul_of_coprime hN_cop]
      exact dvd_mul_right _ _
    have hsig_p2 : sigma 1 (ordProj[p] N) = 1 + p + p ^ 2 := by
      rw [hord_eq, sigma_one_apply_prime_pow hp,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      ring
    have h3_dvd_sig : 3 ∣ sigma 1 (ordProj[p] N) := by
      rw [hsig_p2]
      apply Nat.dvd_of_mod_eq_zero
      have hp_mod : p % 3 = 1 := hp3
      have hp2_mod : p ^ 2 % 3 = 1 := by
        rw [pow_two, Nat.mul_mod, hp_mod]
      omega
    have hsig_N : sigma 1 N = 2 * N :=
      (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN)
    have h3_dvd_2N : 3 ∣ 2 * N := by
      rw [← hsig_N]
      exact h3_dvd_sig.trans hsig_dvd
    have h3_dvd_N : 3 ∣ N :=
      (Nat.Prime.dvd_mul Nat.prime_three).mp h3_dvd_2N |>.resolve_left (by decide)
    exact hN3 h3_dvd_N
  have hmp_ge2 : 2 ≤ m.factorization p := by omega
  have hp2_dvd_m : p ^ 2 ∣ m := (hp.pow_dvd_iff_le_factorization hm_ne0).mpr hmp_ge2
  have hNp_ge4 : 4 ≤ N.factorization p := by omega
  have hp4_dvd_N : p ^ 4 ∣ N := (hp.pow_dvd_iff_le_factorization hN_ne0).mpr hNp_ge4
  have hp_dvd_N : p ∣ N := by
    rw [hform]
    exact dvd_mul_of_dvd_right (dvd_trans hpm (dvd_pow_self m (by decide : 2 ≠ 0))) _
  have hp_mem_N : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hp_dvd_N, hN_ne0⟩
  have hp_ne3 : p ≠ 3 := by omega
  have hp_mem : p ∈ oneModThreeLargeSources N q := by
    simp only [oneModThreeLargeSources, largeSources, Finset.mem_filter]
    exact ⟨⟨hp_mem_N, hp_ne3, hp_ne_q, hNp_ge4⟩, hp3⟩
  exact ⟨hmp_ge2, hp2_dvd_m, hNp_ge4, hp4_dvd_N, hp_mem⟩

/-- Under `¬ 3 ∣ N` on the exceptional Euler-index branch `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2`
(`a > 1`, `l.Prime`, `d := (a + 1) / 2`), upgrades `8 * d ∣ l - 1` to `24 * d ∣ l - 1`,
forces `1753 ≤ l` and `d ≠ 73 → 4657 ≤ l`, forces `p ^ 4 ∣ N` (`p ∈ oneModThreeLargeSources N q`)
for all primes `p ∣ m` with `p % 3 = 1` (in particular `d` and `l`), establishes `d ∣ w * t`,
`l ∣ v * t`, and `d ^ 2 * l ^ 2 * z ∣ m`, and yields `4798187033573 ≤ d ^ 2 * l ^ 2 * z`. -/
theorem exceptional_euler_three_free_24d_and_fourth_powers {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2)
    (hN3 : ¬ 3 ∣ N) :
    let d := (a + 1) / 2
    q % 48 = 1 ∧
    d % 24 = 1 ∧
    73 ≤ d ∧
    145 ≤ a ∧
    geometricBlock q d % 3 = 1 ∧
    l % 3 = 1 ∧
    l % 24 = 1 ∧
    24 * d ∣ l - 1 ∧
    24 * d + 1 ≤ l ∧
    1753 ≤ l ∧
    (d ≠ 73 → 4657 ≤ l) ∧
    (∀ p : ℕ, p.Prime → p ∣ m → p % 3 = 1 →
      2 ≤ m.factorization p ∧ p ^ 2 ∣ m ∧ 4 ≤ N.factorization p ∧ p ^ 4 ∣ N ∧
        p ∈ oneModThreeLargeSources N q) ∧
    2 ≤ m.factorization d ∧ d ^ 2 ∣ m ∧ 4 ≤ N.factorization d ∧ d ^ 4 ∣ N ∧
      d ∈ oneModThreeLargeSources N q ∧
    2 ≤ m.factorization l ∧ l ^ 2 ∣ m ∧ 4 ≤ N.factorization l ∧ l ^ 4 ∣ N ∧
      l ∈ oneModThreeLargeSources N q ∧
    ∃ w z v : ℕ,
      0 < w ∧ 3 ≤ z ∧ 3 ≤ t ∧ Odd w ∧ Odd z ∧ Odd v ∧ Odd t ∧
      q + 1 = 2 * d * w ^ 2 ∧
      (q ^ d + 1) / (q + 1) = d * z ^ 2 ∧
      geometricBlock q d = l * v ^ 2 ∧
      m = d * l * w * z * v * t ∧
      d ∣ w * t ∧
      l ∣ v * t ∧
      d ^ 2 * l ^ 2 * z ∣ m ∧
      293 ≤ z.minFac ∧
      4798187033573 ≤ d ^ 2 * l ^ 2 * z := by
  intro d
  obtain ⟨hd_prime, _, _, _, _, _, _, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  change d.Prime at hd_prime
  obtain ⟨hq48, hd24, hd73, ha145⟩ :=
    exceptional_euler_of_not_three_dvd hN ho hq hq4 ha4 ha hqm hform hl hi hN3
  change d % 24 = 1 at hd24
  change 73 ≤ d at hd73
  obtain ⟨_, hl_mod8, h8d_dvd, _, hl137, _, _⟩ :=
    exceptional_euler_first_block_mod_eight_and_order_sieve
      hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨_, _, hl73, _⟩ :=
    (exceptional_euler_first_block_three_and_five_free_bounds
      hN ho hq hq4 ha4 ha hqm hform hl hi).1 hN3
  obtain ⟨_, _, w1, z1, v1, _, _, _, _, _, _, _, hndvd_dv, _, _, hgeom1, _⟩ :=
    exceptional_euler_first_and_second_block_reciprocity_profile
      hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨w, z, v, hw_pos, hz_ge3, ht3, hw_odd, hz_odd, hv_odd, ht_odd,
      hq1, hdiv, hgeom, hm_eq, hcop_dl, hcop_dz, hcop_lz, _, hcop_lw, _, _, _, _⟩ :=
    exceptional_euler_coprime_triple_factorization_and_l_routing
      hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨z0, _, hdiv0, _, h3_z0, _⟩ :=
    exceptional_euler_three_and_five_free_coprime_triple_bounds
      hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨hz_min_293, _⟩ := h3_z0 hN3
  have hz0_eq : z0 = z := by
    have hsq : z0 ^ 2 = z ^ 2 :=
      Nat.eq_of_mul_eq_mul_left hd_prime.pos (hdiv0.symm.trans hdiv)
    exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hsq
  have hz_min_293' : 293 ≤ z.minFac := hz0_eq ▸ hz_min_293
  have hz293 : 293 ≤ z := le_trans hz_min_293' (Nat.minFac_le (by omega : 0 < z))
  have hv1_eq : v1 = v := by
    have hsq : v1 ^ 2 = v ^ 2 :=
      Nat.eq_of_mul_eq_mul_left hl.pos (hgeom1.symm.trans hgeom)
    exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hsq
  have hndvd_dv' : ¬ d ∣ v := hv1_eq ▸ hndvd_dv
  have hgeom_mod3 : geometricBlock q d % 3 = 1 := by
    have hcast : ((geometricBlock q d : ℕ) : ZMod 3) = 1 := by
      have hq3 : (q : ZMod 3) = 1 := by
        rw [← ZMod.natCast_mod, show q % 3 = 1 by omega, Nat.cast_one]
      have hd3 : (d : ZMod 3) = 1 := by
        rw [← ZMod.natCast_mod, show d % 3 = 1 by omega, Nat.cast_one]
      simp [geometricBlock, hq3, hd3]
    have hm := (ZMod.natCast_eq_natCast_iff (geometricBlock q d) 1 3).mp (by simpa using hcast)
    simpa [Nat.ModEq] using hm
  have hv_dvd_m : v ∣ m := ⟨d * l * w * z * t, by rw [hm_eq]; ring⟩
  have hm_dvd_N : m ∣ N := by
    rw [hform]
    exact dvd_mul_of_dvd_right (dvd_pow_self m (by decide : 2 ≠ 0)) _
  have hv_ndvd3 : ¬ 3 ∣ v := fun h3v => hN3 (h3v.trans (hv_dvd_m.trans hm_dvd_N))
  have hv2_mod3 : v ^ 2 % 3 = 1 := by
    have hv3 : v % 3 = 1 ∨ v % 3 = 2 := by
      have h0 : v % 3 ≠ 0 := fun h => hv_ndvd3 (Nat.dvd_of_mod_eq_zero h)
      omega
    rw [pow_two, Nat.mul_mod]
    rcases hv3 with h | h <;> rw [h]
  have hl_mod3 : l % 3 = 1 := by
    have hmod : (l * v ^ 2) % 3 = geometricBlock q d % 3 := by rw [hgeom]
    rw [Nat.mul_mod, hv2_mod3, hgeom_mod3] at hmod
    omega
  have hl_mod24 : l % 24 = 1 := by omega
  have h3_dvd_l1 : 3 ∣ l - 1 := Nat.dvd_of_mod_eq_zero (by omega)
  have hcop_3_8d : Nat.Coprime 3 (8 * d) := by
    have hd_ne3 : d ≠ 3 := by omega
    have h3d : Nat.Coprime 3 d := Nat.prime_three.coprime_iff_not_dvd.mpr (fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hd_prime).mp h
      omega)
    exact Nat.Coprime.mul_right (by decide) h3d
  have h24d_dvd : 24 * d ∣ l - 1 := by
    rw [show 24 * d = 3 * (8 * d) by ring]
    exact hcop_3_8d.mul_dvd_of_dvd_of_dvd h3_dvd_l1 h8d_dvd
  have h24d1_le : 24 * d + 1 ≤ l := by
    obtain ⟨k, hk⟩ := h24d_dvd
    rcases k with _ | k
    · simp at hk; omega
    · have hle : 24 * d ≤ 24 * d * (k + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos k)
      omega
  have hl_4657 : d ≠ 73 → 4657 ≤ l := fun hne =>
    l_ge_4657_of_ne_73 hd_prime hd24 hd73 hne hl h24d_dvd h24d1_le
  have hl_1753 : 1753 ≤ l := by
    by_cases hdeq73 : d = 73
    · exact hl73 hdeq73
    · exact le_trans (by decide : 1753 ≤ 4657) (hl_4657 hdeq73)
  have hfourth : ∀ p : ℕ, p.Prime → p ∣ m → p % 3 = 1 →
      2 ≤ m.factorization p ∧ p ^ 2 ∣ m ∧ 4 ≤ N.factorization p ∧ p ^ 4 ∣ N ∧
        p ∈ oneModThreeLargeSources N q :=
    fun p hp hpm hp3 =>
      fourth_power_of_prime_dvd_m_one_mod_three hN hq hqm hform hN3 hp hpm hp3
  have hd_dvd_m : d ∣ m := ⟨l * w * z * v * t, by rw [hm_eq]; ring⟩
  have hl_dvd_m : l ∣ m := ⟨d * w * z * v * t, by rw [hm_eq]; ring⟩
  have hd_fourth := hfourth d hd_prime hd_dvd_m (by omega)
  have hl_fourth := hfourth l hl hl_dvd_m hl_mod3
  have hcop_dv : Nat.Coprime d v := hd_prime.coprime_iff_not_dvd.mpr hndvd_dv'
  have hcop_d_lzv : Nat.Coprime d (l * z * v) :=
    (hcop_dl.mul_right hcop_dz).mul_right hcop_dv
  have hd_dvd_wt : d ∣ w * t := by
    have hd2_dvd : d * d ∣ d * (l * z * v * (w * t)) := by
      have hm' : m = d * (l * z * v * (w * t)) := by rw [hm_eq]; ring
      rw [← hm', ← pow_two]
      exact hd_fourth.2.1
    have hd_dvd_prod : d ∣ (l * z * v) * (w * t) :=
      Nat.dvd_of_mul_dvd_mul_left hd_prime.pos hd2_dvd
    exact hcop_d_lzv.dvd_of_dvd_mul_left hd_dvd_prod
  have hcop_l_dwz : Nat.Coprime l (d * w * z) :=
    (hcop_dl.symm.mul_right hcop_lw).mul_right hcop_lz
  have hl_dvd_vt : l ∣ v * t := by
    have hl2_dvd : l * l ∣ l * (d * w * z * (v * t)) := by
      have hm' : m = l * (d * w * z * (v * t)) := by rw [hm_eq]; ring
      rw [← hm', ← pow_two]
      exact hl_fourth.2.1
    have hl_dvd_prod : l ∣ (d * w * z) * (v * t) :=
      Nat.dvd_of_mul_dvd_mul_left hl.pos hl2_dvd
    exact hcop_l_dwz.dvd_of_dvd_mul_left hl_dvd_prod
  have hz_dvd_m : z ∣ m := ⟨d * l * w * v * t, by rw [hm_eq]; ring⟩
  have hd2_l2_z_dvd : d ^ 2 * l ^ 2 * z ∣ m := by
    have hcop_d2_l2 : Nat.Coprime (d ^ 2) (l ^ 2) := (hcop_dl.pow_left 2).pow_right 2
    have hcop_d2l2_z : Nat.Coprime (d ^ 2 * l ^ 2) z :=
      (hcop_dz.pow_left 2).mul_left (hcop_lz.pow_left 2)
    have hd2l2_dvd : d ^ 2 * l ^ 2 ∣ m :=
      hcop_d2_l2.mul_dvd_of_dvd_of_dvd hd_fourth.2.1 hl_fourth.2.1
    exact hcop_d2l2_z.mul_dvd_of_dvd_of_dvd hd2l2_dvd hz_dvd_m
  have hprod_floor : 4798187033573 ≤ d ^ 2 * l ^ 2 * z := by
    have hmul : 73 ^ 2 * 1753 ^ 2 * 293 ≤ d ^ 2 * l ^ 2 * z :=
      Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.pow_le_pow_left hd73 2) (Nat.pow_le_pow_left hl_1753 2))
        hz293
    omega
  refine ⟨hq48, hd24, hd73, ha145, hgeom_mod3, hl_mod3, hl_mod24, h24d_dvd, h24d1_le,
    hl_1753, hl_4657, hfourth,
    hd_fourth.1, hd_fourth.2.1, hd_fourth.2.2.1, hd_fourth.2.2.2.1, hd_fourth.2.2.2.2,
    hl_fourth.1, hl_fourth.2.1, hl_fourth.2.2.1, hl_fourth.2.2.2.1, hl_fourth.2.2.2.2,
    w, z, v, hw_pos, hz_ge3, ht3, hw_odd, hz_odd, hv_odd, ht_odd,
    hq1, hdiv, hgeom, hm_eq, hd_dvd_wt, hl_dvd_vt, hd2_l2_z_dvd, hz_min_293', hprod_floor⟩

/-- Under `¬ 3 ∣ N` and `¬ 5 ∣ N` on the exceptional Euler-index branch
`sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`, `d := (a + 1) / 2`),
forces `geometricBlock q d % 5 = 1 ∨ geometricBlock q d % 5 = 4`, `l % 5 = 1 ∨ l % 5 = 4`,
`d = 241 → 28921 ≤ l`, `d ≠ 241 → 409 ≤ d ∧ 9817 ≤ l`, `d ^ 2 * l ^ 2 * z ∣ m`,
`d = 241 → 117127239139407131 ≤ d ^ 2 * l ^ 2 * z`, and `26390819565150533 ≤ d ^ 2 * l ^ 2 * z`. -/
theorem exceptional_euler_three_and_five_free_mod_five_and_quintic_bounds
    {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2)
    (hN3 : ¬ 3 ∣ N) (hN5 : ¬ 5 ∣ N) :
    let d := (a + 1) / 2
    q % 48 = 1 ∧
    (q % 5 = 1 ∨ q % 5 = 2) ∧
    d % 120 ∈ ({1, 49} : Finset ℕ) ∧
    241 ≤ d ∧
    481 ≤ a ∧
    (geometricBlock q d % 5 = 1 ∨ geometricBlock q d % 5 = 4) ∧
    (l % 5 = 1 ∨ l % 5 = 4) ∧
    (d = 241 → 28921 ≤ l) ∧
    (d ≠ 241 → 409 ≤ d ∧ 9817 ≤ l) ∧
    ∃ z : ℕ,
      3 ≤ z ∧
      (q ^ d + 1) / (q + 1) = d * z ^ 2 ∧
      d ^ 2 * l ^ 2 * z ∣ m ∧
      1637 ≤ z.minFac ∧
      (d = 241 → 28921 ≤ l ∧ 2411 ≤ z.minFac ∧ 2411 ≤ z ∧
        117127239139407131 ≤ d ^ 2 * l ^ 2 * z) ∧
      (d ≠ 241 → 409 ≤ d ∧ 9817 ≤ l ∧ 1637 ≤ z.minFac ∧ 1637 ≤ z ∧
        26390819565150533 ≤ d ^ 2 * l ^ 2 * z) ∧
      26390819565150533 ≤ d ^ 2 * l ^ 2 * z := by
  intro d
  obtain ⟨hd_prime, _, _, _, _, _, _, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  change d.Prime at hd_prime
  obtain ⟨hq48, hq5, hd120, hd241, ha481⟩ :=
    exceptional_euler_of_not_three_or_five_dvd hN ho hq hq4 ha4 ha hqm hform hl hi hN3 hN5
  change d % 120 ∈ ({1, 49} : Finset ℕ) at hd120
  change 241 ≤ d at hd241
  obtain ⟨_, _, _, _, _, _, _, h24d_dvd, h24d1_le, _, _, _,
      _, _, _, _, _, _, _, _, _, _,
      w, z, v, _, hz_ge3, _, _, _, _, _, _, hdiv, hgeom, hm_eq, _, _, hd2l2z_dvd, _, _⟩ :=
    exceptional_euler_three_free_24d_and_fourth_powers
      hN ho hq hq4 ha4 ha hqm hform hl hi hN3
  obtain ⟨_, hl9817, _, _⟩ :=
    (exceptional_euler_first_block_three_and_five_free_bounds
      hN ho hq hq4 ha4 ha hqm hform hl hi).2 hN3 hN5
  obtain ⟨z0, _, hdiv0, _, _, h35_z0⟩ :=
    exceptional_euler_three_and_five_free_coprime_triple_bounds
      hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨hz_min_1637, hz_min_241_imp, _⟩ := h35_z0 hN3 hN5
  have hz0_eq : z0 = z := by
    have hsq : z0 ^ 2 = z ^ 2 :=
      Nat.eq_of_mul_eq_mul_left hd_prime.pos (hdiv0.symm.trans hdiv)
    exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hsq
  have hz_min_1637' : 1637 ≤ z.minFac := hz0_eq ▸ hz_min_1637
  have hz_min_241' : d = 241 → 2411 ≤ z.minFac := fun hd => hz0_eq ▸ hz_min_241_imp hd
  have hd_mod120 : d % 120 = 1 ∨ d % 120 = 49 := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hd120
  have hgeom_mod5 : geometricBlock q d % 5 = 1 ∨ geometricBlock q d % 5 = 4 := by
    rcases hq5 with hq5_1 | hq5_2
    · have hcast : ((geometricBlock q d : ℕ) : ZMod 5) = (d : ZMod 5) := by
        have hq5z : (q : ZMod 5) = 1 := by
          rw [← ZMod.natCast_mod, hq5_1, Nat.cast_one]
        simp [geometricBlock, hq5z]
      have hm := (ZMod.natCast_eq_natCast_iff (geometricBlock q d) d 5).mp hcast
      change geometricBlock q d % 5 = d % 5 at hm
      omega
    · have hq5z : (q : ZMod 5) = 2 := by
        rw [← ZMod.natCast_mod, hq5_2]
        norm_num
      have hsum : ((geometricBlock q d : ℕ) : ZMod 5) * ((q : ZMod 5) - 1) =
          (q : ZMod 5) ^ d - 1 := by
        rw [geometricBlock]
        push_cast
        exact geom_sum_mul (q : ZMod 5) d
      have hd4 : d % 4 = 1 := by omega
      have hq_pow : (q : ZMod 5) ^ d = 2 := by
        rw [hq5z, show d = 4 * (d / 4) + 1 by omega, pow_add, pow_mul, pow_one]
        have h24 : (2 : ZMod 5) ^ 4 = 1 := by decide
        rw [h24, one_pow, one_mul]
      rw [hq_pow, hq5z] at hsum
      have hcast : ((geometricBlock q d : ℕ) : ZMod 5) = 1 := by
        norm_num at hsum
        exact hsum
      have hm := (ZMod.natCast_eq_natCast_iff (geometricBlock q d) 1 5).mp (by simpa using hcast)
      change geometricBlock q d % 5 = 1 % 5 at hm
      exact Or.inl (by omega)
  have hv_dvd_m : v ∣ m := ⟨d * l * w * z * t, by rw [hm_eq]; ring⟩
  have hm_dvd_N : m ∣ N := by
    rw [hform]
    exact dvd_mul_of_dvd_right (dvd_pow_self m (by decide : 2 ≠ 0)) _
  have hv_ndvd5 : ¬ 5 ∣ v := fun h5v => hN5 (h5v.trans (hv_dvd_m.trans hm_dvd_N))
  have hv2_mod5 : v ^ 2 % 5 = 1 ∨ v ^ 2 % 5 = 4 := by
    have hv5 : v % 5 = 1 ∨ v % 5 = 2 ∨ v % 5 = 3 ∨ v % 5 = 4 := by
      have h0 : v % 5 ≠ 0 := fun h => hv_ndvd5 (Nat.dvd_of_mod_eq_zero h)
      omega
    rw [pow_two, Nat.mul_mod]
    rcases hv5 with h | h | h | h <;> rw [h] <;> decide
  have hl_mod5 : l % 5 = 1 ∨ l % 5 = 4 := by
    have hmod : (l * v ^ 2) % 5 = geometricBlock q d % 5 := by rw [hgeom]
    rw [Nat.mul_mod] at hmod
    rcases hgeom_mod5 with hg | hg <;> rcases hv2_mod5 with hv | hv
    · rw [hg, hv] at hmod; omega
    · rw [hg, hv] at hmod; omega
    · rw [hg, hv] at hmod; omega
    · rw [hg, hv] at hmod; omega
  have hl_28921 : d = 241 → 28921 ≤ l := by
    intro hdeq
    change 24 * d ∣ l - 1 at h24d_dvd
    change 24 * d + 1 ≤ l at h24d1_le
    rw [hdeq] at h24d_dvd h24d1_le
    exact l_ge_28921_of_eq_241 hl h24d_dvd h24d1_le
  have hne_imp : d ≠ 241 → 409 ≤ d ∧ 9817 ≤ l := fun hne =>
    ⟨d_ge_409_of_ne_241' hd_prime hd120 hd241 hne, hl9817⟩
  have hz_min_le_z : z.minFac ≤ z := Nat.minFac_le (by omega : 0 < z)
  have h241_branch : d = 241 →
      28921 ≤ l ∧ 2411 ≤ z.minFac ∧ 2411 ≤ z ∧
        117127239139407131 ≤ d ^ 2 * l ^ 2 * z := by
    intro hdeq
    have hl_ge := hl_28921 hdeq
    have hz_min := hz_min_241' hdeq
    have hz_ge : 2411 ≤ z := le_trans hz_min hz_min_le_z
    have hmul : 241 ^ 2 * 28921 ^ 2 * 2411 ≤ d ^ 2 * l ^ 2 * z :=
      Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) (Nat.pow_le_pow_left hl_ge 2))
        hz_ge
    exact ⟨hl_ge, hz_min, hz_ge, by omega⟩
  have hne_branch : d ≠ 241 →
      409 ≤ d ∧ 9817 ≤ l ∧ 1637 ≤ z.minFac ∧ 1637 ≤ z ∧
        26390819565150533 ≤ d ^ 2 * l ^ 2 * z := by
    intro hne
    obtain ⟨hd409, hl_ge⟩ := hne_imp hne
    have hz_ge : 1637 ≤ z := le_trans hz_min_1637' hz_min_le_z
    have hmul : 409 ^ 2 * 9817 ^ 2 * 1637 ≤ d ^ 2 * l ^ 2 * z :=
      Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.pow_le_pow_left hd409 2) (Nat.pow_le_pow_left hl_ge 2))
        hz_ge
    exact ⟨hd409, hl_ge, hz_min_1637', hz_ge, by omega⟩
  have hprod_floor : 26390819565150533 ≤ d ^ 2 * l ^ 2 * z := by
    by_cases hdeq : d = 241
    · exact le_trans (by decide : 26390819565150533 ≤ 117127239139407131)
        (h241_branch hdeq).2.2.2
    · exact (hne_branch hdeq).2.2.2.2
  exact ⟨hq48, hq5, hd120, hd241, ha481, hgeom_mod5, hl_mod5, hl_28921, hne_imp,
    z, hz_ge3, hdiv, hd2l2z_dvd, hz_min_1637', h241_branch, hne_branch, hprod_floor⟩

end OddPerfect
