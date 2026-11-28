module

public import OddPerfect.PellMatiyasevicAndFirstBlockReciprocity
public import OddPerfect.ZsqrtTwoUnifiedSieveAndSecondBlockModSq
public import OddPerfect.ExceptionalFermatHigherSieve
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Combined First- and Second-Block Sieve (`OddPerfect.ZsqrtTwoCombinedFirstSecondBlockSieve`)

Combines the first-block reciprocity profile (`OddPerfect.PellMatiyasevicAndFirstBlockReciprocity`),
the second-block cyclotomic order infrastructure (`OddPerfect.ZsqrtTwoUnifiedSieveAndSecondBlockModSq`),
and the `(¬ 3 ∣ N, ¬ 5 ∣ N)` exceptional Fermat congruences (`OddPerfect.ExceptionalFermatHigherSieve`)
to prove two unconditional theorems on the exceptional Euler-index branch
`sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`, `d := (a + 1) / 2`):

1. `exceptional_euler_first_block_mod_eight_and_order_sieve`: proves
   `geometricBlock q d % 8 = 1`, `l % 8 = 1`, `8 * d ∣ l - 1`, `8 * d + 1 ≤ l`, `137 ≤ l`,
   `orderOf (q : ZMod r) = d`, `2 * d ∣ r - 1`, `2 * d + 1 ≤ r`, `83 ≤ r ∧ (d = 17 → 103 ≤ r)`
   for every prime factor `r ∈ (geometricBlock q d).primeFactors`, and full pairwise coprimality
   of `geometricBlock q d`, `l`, `v` with `2 * d * w * z`.
2. `exceptional_euler_first_block_three_and_five_free_bounds`: proves strengthened lower
   bounds on `d`, `l`, and every `r ∈ (geometricBlock q d).primeFactors` under `¬ 3 ∣ N`
   (`73 ≤ d`, `1553 ≤ l`, `d = 73 → 1753 ≤ l`, `293 ≤ r`) and under `¬ 3 ∣ N → ¬ 5 ∣ N`
   (`241 ≤ d`, `9817 ≤ l`, `d = 241 → 26993 ≤ l`, `1447 ≤ r`).
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

private lemma not_prime_of_mul_eq {a b n : ℕ} (ha : 1 < a) (hb : 1 < b) (h : a * b = n) :
    ¬ Nat.Prime n := by
  intro hp
  have hdvd : a ∣ n := ⟨b, h.symm⟩
  rcases hp.eq_one_or_self_of_dvd a hdvd with h1 | han <;> nlinarith

/-- On the exceptional Euler-index branch `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2`
(`a > 1`, `l.Prime`, `d := (a + 1) / 2`), forces `geometricBlock q d % 8 = 1`, `l % 8 = 1`,
`8 * d ∣ l - 1`, `137 ≤ l`, exact multiplicative order `orderOf (q : ZMod r) = d` (hence
`2 * d ∣ r - 1` and `83 ≤ r`, `103 ≤ r` if `d = 17`) for every prime factor `r` of
`geometricBlock q d`, and coprimality of `geometricBlock q d`, `l`, `v` with `2 * d * w * z`. -/
theorem exceptional_euler_first_block_mod_eight_and_order_sieve
    {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    geometricBlock q d % 8 = 1 ∧
    l % 8 = 1 ∧
    8 * d ∣ l - 1 ∧
    8 * d + 1 ≤ l ∧
    137 ≤ l ∧
    (∀ r ∈ (geometricBlock q d).primeFactors,
      orderOf (q : ZMod r) = d ∧
      2 * d ∣ r - 1 ∧
      2 * d + 1 ≤ r ∧
      83 ≤ r ∧
      (d = 17 → 103 ≤ r)) ∧
    ∃ w z v : ℕ,
      q + 1 = 2 * d * w ^ 2 ∧
      (q ^ d + 1) / (q + 1) = d * z ^ 2 ∧
      geometricBlock q d = l * v ^ 2 ∧
      Nat.Coprime (geometricBlock q d) (2 * d * w * z) ∧
      Nat.Coprime l (2 * d * w * z) ∧
      Nat.Coprime v (2 * d * w * z) := by
  intro d
  obtain ⟨hd_prime, hd17, hd8, hq16, _, _, _, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  change d.Prime at hd_prime
  change 17 ≤ d at hd17
  change d % 8 = 1 at hd8
  change q % 16 = 1 at hq16
  have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
  have hd_pos : 0 < d := hd_prime.pos
  obtain ⟨hndvd_geom, _, w, z, v, _, _, _, _, hv_odd, _, _, _, hq1, hdiv, hgeom, _⟩ :=
    exceptional_euler_first_and_second_block_reciprocity_profile
      hN ho hq hq4 ha4 ha hqm hform hl hi
  have hgeom_mod8 : geometricBlock q d % 8 = 1 := by
    have hcast : ((geometricBlock q d : ℕ) : ZMod 8) = 1 := by
      have hq8 : (q : ZMod 8) = 1 := by
        rw [← ZMod.natCast_mod, show q % 8 = 1 by omega, Nat.cast_one]
      have hd8_z : (d : ZMod 8) = 1 := by
        rw [← ZMod.natCast_mod, hd8, Nat.cast_one]
      simp [geometricBlock, hq8, hd8_z]
    have hm := (ZMod.natCast_eq_natCast_iff (geometricBlock q d) 1 8).mp (by simpa using hcast)
    simpa [Nat.ModEq] using hm
  have hgeom_odd : Odd (geometricBlock q d) := Nat.odd_iff.mpr (by omega)
  have hgeom_ne0 : geometricBlock q d ≠ 0 := hgeom_odd.pos.ne'
  have hv2_mod8 : v ^ 2 % 8 = 1 := by
    have hv8 : v % 8 = 1 ∨ v % 8 = 3 ∨ v % 8 = 5 ∨ v % 8 = 7 := by
      have := Nat.odd_iff.mp hv_odd
      omega
    rw [Nat.pow_mod]
    rcases hv8 with h | h | h | h <;> rw [h]
  have hl_mod8 : l % 8 = 1 := by
    have hmul : (l * v ^ 2) % 8 = 1 := hgeom ▸ hgeom_mod8
    rw [Nat.mul_mod, hv2_mod8, mul_one, Nat.mod_mod] at hmul
    exact hmul
  have hr_all : ∀ r ∈ (geometricBlock q d).primeFactors,
      orderOf (q : ZMod r) = d ∧
      2 * d ∣ r - 1 ∧
      2 * d + 1 ≤ r ∧
      83 ≤ r ∧
      (d = 17 → 103 ≤ r) := by
    intro r hr
    have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hr_dvd_geom : r ∣ geometricBlock q d := Nat.dvd_of_mem_primeFactors hr
    have hr_odd : Odd r := hgeom_odd.of_dvd_nat hr_dvd_geom
    have hr_ne_d : r ≠ d := by
      rintro rfl
      exact hndvd_geom hr_dvd_geom
    have : Fact r.Prime := ⟨hr_prime⟩
    have hgeom_zmod : ((geometricBlock q d : ℕ) : ZMod r) = 0 :=
      (ZMod.natCast_eq_zero_iff (geometricBlock q d) r).mpr hr_dvd_geom
    have hqd_zmod : (q : ZMod r) ^ d = 1 := by
      have hmul :
          ((q : ZMod r) - 1) * ((geometricBlock q d : ℕ) : ZMod r) = (q : ZMod r) ^ d - 1 := by
        dsimp [geometricBlock]
        push_cast
        rw [mul_comm, geom_sum_mul]
      rw [hgeom_zmod, mul_zero] at hmul
      exact sub_eq_zero.mp hmul.symm
    have hord_dvd : orderOf (q : ZMod r) ∣ d := orderOf_dvd_of_pow_eq_one hqd_zmod
    have hord_ne1 : orderOf (q : ZMod r) ≠ 1 := by
      intro h1
      have hq1_z : (q : ZMod r) = 1 := orderOf_eq_one_iff.mp h1
      have hd_z : (d : ZMod r) = 0 := by
        calc
          (d : ZMod r) = ∑ _j ∈ Finset.range d, (1 : ZMod r) := by simp
          _ = ∑ j ∈ Finset.range d, (q : ZMod r) ^ j := by simp [hq1_z]
          _ = ((geometricBlock q d : ℕ) : ZMod r) := by simp [geometricBlock]
          _ = 0 := hgeom_zmod
      have hr_dvd_d : r ∣ d := (ZMod.natCast_eq_zero_iff d r).mp hd_z
      have hrd_eq : r = d := (hd_prime.eq_one_or_self_of_dvd r hr_dvd_d).resolve_left hr_prime.ne_one
      exact hr_ne_d hrd_eq
    have hord_eq : orderOf (q : ZMod r) = d :=
      (hd_prime.eq_one_or_self_of_dvd _ hord_dvd).resolve_left hord_ne1
    have hq_ne0 : (q : ZMod r) ≠ 0 := by
      intro h0
      rw [h0, zero_pow hd_pos.ne'] at hqd_zmod
      exact zero_ne_one hqd_zmod
    have hd_dvd_r1 : d ∣ r - 1 := hord_eq ▸ ZMod.orderOf_dvd_card_sub_one hq_ne0
    have h2_dvd_r1 : 2 ∣ r - 1 := by
      have := Nat.odd_iff.mp hr_odd
      exact Nat.dvd_of_mod_eq_zero (by omega)
    have hcop_2d : Nat.Coprime 2 d :=
      Nat.prime_two.coprime_iff_not_dvd.mpr (by have := Nat.odd_iff.mp hd_odd; omega)
    have h2d_dvd_r1 : 2 * d ∣ r - 1 := hcop_2d.mul_dvd_of_dvd_of_dvd h2_dvd_r1 hd_dvd_r1
    have h2d1_le_r : 2 * d + 1 ≤ r := by
      have hr2 := hr_prime.two_le
      have hle : 2 * d ≤ r - 1 := Nat.le_of_dvd (by omega) h2d_dvd_r1
      omega
    have hr_17 : d = 17 → 103 ≤ r := by
      intro hd17_eq
      rw [hd17_eq] at h2d_dvd_r1 h2d1_le_r
      obtain ⟨k, hk⟩ := h2d_dvd_r1
      have hk1 : 1 ≤ k := by
        rcases k with _ | k
        · simp at hk; have := hr_prime.two_le; omega
        · omega
      have hk_ne1 : k ≠ 1 := by
        rintro rfl
        have hr35 : r = 35 := by omega
        exact not_prime_of_mul_eq (by decide : 1 < 5) (by decide : 1 < 7) (by norm_num) (hr35 ▸ hr_prime)
      have hk_ne2 : k ≠ 2 := by
        rintro rfl
        have hr69 : r = 69 := by omega
        exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 23) (by norm_num) (hr69 ▸ hr_prime)
      omega
    have hr83 : 83 ≤ r := by
      by_cases hd41 : 41 ≤ d
      · omega
      · have hd_cases : d = 17 ∨ d = 25 ∨ d = 33 := by omega
        rcases hd_cases with h17 | h25 | h33
        · exact Nat.le_trans (by decide : 83 ≤ 103) (hr_17 h17)
        · exact absurd (h25 ▸ hd_prime)
            (not_prime_of_mul_eq (by decide : 1 < 5) (by decide : 1 < 5) (by norm_num))
        · exact absurd (h33 ▸ hd_prime)
            (not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 11) (by norm_num))
    exact ⟨hord_eq, h2d_dvd_r1, h2d1_le_r, hr83, hr_17⟩
  have hl_mem : l ∈ (geometricBlock q d).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hl, ⟨v ^ 2, hgeom⟩, hgeom_ne0⟩
  have h2d_dvd_l1 : 2 * d ∣ l - 1 := (hr_all l hl_mem).2.1
  have hd_dvd_l1 : d ∣ l - 1 := dvd_trans ⟨2, by ring⟩ h2d_dvd_l1
  have h8_dvd_l1 : 8 ∣ l - 1 := Nat.dvd_of_mod_eq_zero (by omega)
  have hcop_8d : Nat.Coprime 8 d := by
    have h2d : Nat.Coprime 2 d :=
      Nat.prime_two.coprime_iff_not_dvd.mpr (by have := Nat.odd_iff.mp hd_odd; omega)
    simpa using h2d.pow_left 3
  have h8d_dvd_l1 : 8 * d ∣ l - 1 := hcop_8d.mul_dvd_of_dvd_of_dvd h8_dvd_l1 hd_dvd_l1
  have h8d1_le_l : 8 * d + 1 ≤ l := by
    have hl2 : 2 ≤ l := hl.two_le
    have hl_ne1 : l - 1 ≠ 0 := by omega
    have hle : 8 * d ≤ l - 1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hl_ne1) h8d_dvd_l1
    omega
  have h137_le_l : 137 ≤ l := by omega
  have hcop_geom : Nat.Coprime (geometricBlock q d) (2 * d * w * z) := by
    by_contra hncop
    let g := Nat.gcd (geometricBlock q d) (2 * d * w * z)
    have hg_ne1 : g ≠ 1 := hncop
    obtain ⟨p, hp_prime, hp_dvd_g⟩ := Nat.exists_prime_and_dvd hg_ne1
    have hp_geom : p ∣ geometricBlock q d := hp_dvd_g.trans (Nat.gcd_dvd_left _ _)
    have hp_prod : p ∣ 2 * d * w * z := hp_dvd_g.trans (Nat.gcd_dvd_right _ _)
    have hp_ne2 : p ≠ 2 := by
      rintro rfl
      have hmod := Nat.odd_iff.mp hgeom_odd
      omega
    have hp_ne_d : p ≠ d := by
      rintro rfl
      exact hndvd_geom hp_geom
    have hp_qd_sub : (p : ℤ) ∣ (q : ℤ) ^ d - 1 := by
      have hmul : ((q : ℤ) - 1) * (geometricBlock q d : ℤ) = (q : ℤ) ^ d - 1 := by
        dsimp [geometricBlock]
        push_cast
        rw [mul_comm, geom_sum_mul]
      rw [← hmul]
      exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hp_geom) _
    have hp_qd_add_nat : p ∣ q ^ d + 1 := by
      have hdvd_q1 : q + 1 ∣ q ^ d + 1 := by
        simpa using hd_odd.nat_add_dvd_pow_add_pow q 1
      have hmul_nat : (q + 1) * (d * z ^ 2) = q ^ d + 1 := by
        rw [← hdiv]
        exact Nat.mul_div_cancel' hdvd_q1
      rcases hp_prime.dvd_mul.mp hp_prod with hp_2dw | hp_z
      · rcases hp_prime.dvd_mul.mp hp_2dw with hp_2d | hp_w
        · rcases hp_prime.dvd_mul.mp hp_2d with hp_2 | hp_d
          · have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hp_2
            have := hp_prime.two_le
            omega
          · exact absurd ((hd_prime.eq_one_or_self_of_dvd p hp_d).resolve_left hp_prime.ne_one) hp_ne_d
        · have hp_q1 : p ∣ q + 1 := by
            rw [hq1]
            exact dvd_mul_of_dvd_right (dvd_pow hp_w (by decide : 2 ≠ 0)) (2 * d)
          exact hp_q1.trans hdvd_q1
      · have hp_dz2 : p ∣ d * z ^ 2 :=
          dvd_mul_of_dvd_right (dvd_pow hp_z (by decide : 2 ≠ 0)) d
        exact hmul_nat ▸ dvd_mul_of_dvd_right hp_dz2 (q + 1)
    have hp_qd_add : (p : ℤ) ∣ (q : ℤ) ^ d + 1 := by
      exact_mod_cast hp_qd_add_nat
    have hp_2_int : (p : ℤ) ∣ 2 := by
      have h2eq : (2 : ℤ) = ((q : ℤ) ^ d + 1) - ((q : ℤ) ^ d - 1) := by ring
      rw [h2eq]
      exact dvd_sub hp_qd_add hp_qd_sub
    have hp_2 : p ∣ 2 := Int.natCast_dvd_natCast.mp hp_2_int
    have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hp_2
    have := hp_prime.two_le
    omega
  have hcop_l : Nat.Coprime l (2 * d * w * z) :=
    hcop_geom.coprime_dvd_left ⟨v ^ 2, hgeom⟩
  have hcop_v : Nat.Coprime v (2 * d * w * z) :=
    hcop_geom.coprime_dvd_left ⟨l * v, by rw [hgeom]; ring⟩
  exact ⟨hgeom_mod8, hl_mod8, h8d_dvd_l1, h8d1_le_l, h137_le_l, hr_all,
    w, z, v, hq1, hdiv, hgeom, hcop_geom, hcop_l, hcop_v⟩

private lemma prime_mod24_l_bounds {d l : ℕ}
    (hd : d.Prime) (hd24 : d % 24 = 1) (hd73 : 73 ≤ d)
    (hl : l.Prime) (h8d : 8 * d ∣ l - 1) (hl_ge : 8 * d + 1 ≤ l) :
    1553 ≤ l ∧ (d = 73 → 1753 ≤ l) := by
  obtain ⟨k, hk⟩ := h8d
  have hl_eq : l = 8 * d * k + 1 := by omega
  have hk1 : 1 ≤ k := by
    rcases k with _ | k
    · simp at hk; omega
    · omega
  by_cases hd194 : 194 ≤ d
  · constructor
    · omega
    · intro h73; omega
  · have hd_cases : d = 73 ∨ d = 97 ∨ d = 121 ∨ d = 145 ∨ d = 169 ∨ d = 193 := by omega
    rcases hd_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · have hk_ne1 : k ≠ 1 := by
        rintro rfl
        have hval : l = 585 := by omega
        exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 195) (by norm_num)
          (hval ▸ hl)
      have hk_ne2 : k ≠ 2 := by
        rintro rfl
        have hval : l = 1169 := by omega
        exact not_prime_of_mul_eq (by decide : 1 < 7) (by decide : 1 < 167) (by norm_num)
          (hval ▸ hl)
      exact ⟨by omega, fun _ => by omega⟩
    · have hk_ne1 : k ≠ 1 := by
        rintro rfl
        have hval : l = 777 := by omega
        exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 259) (by norm_num)
          (hval ▸ hl)
      exact ⟨by omega, fun h => by omega⟩
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 11) (by decide : 1 < 11) (by norm_num))
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 5) (by decide : 1 < 29) (by norm_num))
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 13) (by decide : 1 < 13) (by norm_num))
    · have hk_ne1 : k ≠ 1 := by
        rintro rfl
        have hval : l = 1545 := by omega
        exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 515) (by norm_num)
          (hval ▸ hl)
      exact ⟨by omega, fun h => by omega⟩

private lemma prime_mod24_r_bound {d r : ℕ}
    (hd : d.Prime) (hd24 : d % 24 = 1) (hd73 : 73 ≤ d)
    (hr : r.Prime) (h2d : 2 * d ∣ r - 1) (hr_ge : 2 * d + 1 ≤ r) :
    293 ≤ r := by
  obtain ⟨k, hk⟩ := h2d
  have hr_eq : r = 2 * d * k + 1 := by omega
  have hk1 : 1 ≤ k := by
    rcases k with _ | k
    · simp at hk; omega
    · omega
  by_cases hd146 : 146 ≤ d
  · omega
  · have hd_cases : d = 73 ∨ d = 97 ∨ d = 121 ∨ d = 145 := by omega
    rcases hd_cases with rfl | rfl | rfl | rfl
    · have hk_ne1 : k ≠ 1 := by
        rintro rfl
        have hval : r = 147 := by omega
        exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 49) (by norm_num)
          (hval ▸ hr)
      omega
    · have hk_ne1 : k ≠ 1 := by
        rintro rfl
        have hval : r = 195 := by omega
        exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 65) (by norm_num)
          (hval ▸ hr)
      omega
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 11) (by decide : 1 < 11) (by norm_num))
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 5) (by decide : 1 < 29) (by norm_num))

private lemma prime_mod120_l_bounds {d l : ℕ}
    (hd : d.Prime) (hd120 : d % 120 ∈ ({1, 49} : Finset ℕ)) (hd241 : 241 ≤ d)
    (hl : l.Prime) (h8d : 8 * d ∣ l - 1) (hl_ge : 8 * d + 1 ≤ l) :
    9817 ≤ l ∧ (d = 241 → 26993 ≤ l) := by
  have hd_mod : d % 120 = 1 ∨ d % 120 = 49 := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hd120
  obtain ⟨k, hk⟩ := h8d
  have hl_eq : l = 8 * d * k + 1 := by omega
  have hk1 : 1 ≤ k := by
    rcases k with _ | k
    · simp at hk; omega
    · omega
  by_cases hd1227 : 1227 ≤ d
  · exact ⟨by omega, fun h => by omega⟩
  · have hd_cases :
        d = 241 ∨ d = 289 ∨ d = 361 ∨ d = 409 ∨ d = 481 ∨ d = 529 ∨
        d = 601 ∨ d = 649 ∨ d = 721 ∨ d = 769 ∨ d = 841 ∨ d = 889 ∨
        d = 961 ∨ d = 1009 ∨ d = 1081 ∨ d = 1129 ∨ d = 1201 := by omega
    rcases hd_cases with
        rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
    · have hk14 : 14 ≤ k := by
        by_contra hk_lt
        have hk_cases :
            k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
            k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 := by omega
        rcases hk_cases with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl
        · exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 643) (by norm_num)
            ((by omega : l = 1929) ▸ hl)
        · exact not_prime_of_mul_eq (by decide : 1 < 7) (by decide : 1 < 551) (by norm_num)
            ((by omega : l = 3857) ▸ hl)
        · exact not_prime_of_mul_eq (by decide : 1 < 5) (by decide : 1 < 1157) (by norm_num)
            ((by omega : l = 5785) ▸ hl)
        · exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 2571) (by norm_num)
            ((by omega : l = 7713) ▸ hl)
        · exact not_prime_of_mul_eq (by decide : 1 < 31) (by decide : 1 < 311) (by norm_num)
            ((by omega : l = 9641) ▸ hl)
        · exact not_prime_of_mul_eq (by decide : 1 < 23) (by decide : 1 < 503) (by norm_num)
            ((by omega : l = 11569) ▸ hl)
        · exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 4499) (by norm_num)
            ((by omega : l = 13497) ▸ hl)
        · exact not_prime_of_mul_eq (by decide : 1 < 5) (by decide : 1 < 3085) (by norm_num)
            ((by omega : l = 15425) ▸ hl)
        · exact not_prime_of_mul_eq (by decide : 1 < 7) (by decide : 1 < 2479) (by norm_num)
            ((by omega : l = 17353) ▸ hl)
        · exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 6427) (by norm_num)
            ((by omega : l = 19281) ▸ hl)
        · exact not_prime_of_mul_eq (by decide : 1 < 127) (by decide : 1 < 167) (by norm_num)
            ((by omega : l = 21209) ▸ hl)
        · exact not_prime_of_mul_eq (by decide : 1 < 17) (by decide : 1 < 1361) (by norm_num)
            ((by omega : l = 23137) ▸ hl)
        · exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 8355) (by norm_num)
            ((by omega : l = 25065) ▸ hl)
      exact ⟨by omega, fun _ => by omega⟩
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 17) (by decide : 1 < 17) (by norm_num))
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 19) (by decide : 1 < 19) (by norm_num))
    · have hk3 : 3 ≤ k := by
        by_contra hk_lt
        rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl
        · exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 1091) (by norm_num)
            ((by omega : l = 3273) ▸ hl)
        · exact not_prime_of_mul_eq (by decide : 1 < 5) (by decide : 1 < 1309) (by norm_num)
            ((by omega : l = 6545) ▸ hl)
      exact ⟨by omega, fun h => by omega⟩
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 13) (by decide : 1 < 37) (by norm_num))
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 23) (by decide : 1 < 23) (by norm_num))
    · have hk3 : 3 ≤ k := by
        by_contra hk_lt
        rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl
        · exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 1603) (by norm_num)
            ((by omega : l = 4809) ▸ hl)
        · exact not_prime_of_mul_eq (by decide : 1 < 59) (by decide : 1 < 163) (by norm_num)
            ((by omega : l = 9617) ▸ hl)
      exact ⟨by omega, fun h => by omega⟩
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 11) (by decide : 1 < 59) (by norm_num))
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 7) (by decide : 1 < 103) (by norm_num))
    · have hk2 : 2 ≤ k := by
        by_contra hk_lt
        have hk_eq1 : k = 1 := by omega
        subst hk_eq1
        exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 2051) (by norm_num)
          ((by omega : l = 6153) ▸ hl)
      exact ⟨by omega, fun h => by omega⟩
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 29) (by decide : 1 < 29) (by norm_num))
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 7) (by decide : 1 < 127) (by norm_num))
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 31) (by decide : 1 < 31) (by norm_num))
    · have hk2 : 2 ≤ k := by
        by_contra hk_lt
        have hk_eq1 : k = 1 := by omega
        subst hk_eq1
        exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 2691) (by norm_num)
          ((by omega : l = 8073) ▸ hl)
      exact ⟨by omega, fun h => by omega⟩
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 23) (by decide : 1 < 47) (by norm_num))
    · have hk2 : 2 ≤ k := by
        by_contra hk_lt
        have hk_eq1 : k = 1 := by omega
        subst hk_eq1
        exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 3011) (by norm_num)
          ((by omega : l = 9033) ▸ hl)
      exact ⟨by omega, fun h => by omega⟩
    · have hk2 : 2 ≤ k := by
        by_contra hk_lt
        have hk_eq1 : k = 1 := by omega
        subst hk_eq1
        exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 3203) (by norm_num)
          ((by omega : l = 9609) ▸ hl)
      exact ⟨by omega, fun h => by omega⟩

private lemma prime_mod120_r_bound {d r : ℕ}
    (hd : d.Prime) (hd120 : d % 120 ∈ ({1, 49} : Finset ℕ)) (hd241 : 241 ≤ d)
    (hr : r.Prime) (h2d : 2 * d ∣ r - 1) (hr_ge : 2 * d + 1 ≤ r) :
    1447 ≤ r := by
  have hd_mod : d % 120 = 1 ∨ d % 120 = 49 := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hd120
  obtain ⟨k, hk⟩ := h2d
  have hr_eq : r = 2 * d * k + 1 := by omega
  have hk1 : 1 ≤ k := by
    rcases k with _ | k
    · simp at hk; omega
    · omega
  by_cases hd723 : 723 ≤ d
  · omega
  · have hd_cases :
        d = 241 ∨ d = 289 ∨ d = 361 ∨ d = 409 ∨ d = 481 ∨
        d = 529 ∨ d = 601 ∨ d = 649 ∨ d = 721 := by omega
    rcases hd_cases with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hk3 : 3 ≤ k := by
        by_contra hk_lt
        rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl
        · exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 161) (by norm_num)
            ((by omega : r = 483) ▸ hr)
        · exact not_prime_of_mul_eq (by decide : 1 < 5) (by decide : 1 < 193) (by norm_num)
            ((by omega : r = 965) ▸ hr)
      omega
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 17) (by decide : 1 < 17) (by norm_num))
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 19) (by decide : 1 < 19) (by norm_num))
    · have hk2 : 2 ≤ k := by
        by_contra hk_lt
        have hk_eq1 : k = 1 := by omega
        subst hk_eq1
        exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 273) (by norm_num)
          ((by omega : r = 819) ▸ hr)
      omega
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 13) (by decide : 1 < 37) (by norm_num))
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 23) (by decide : 1 < 23) (by norm_num))
    · have hk2 : 2 ≤ k := by
        by_contra hk_lt
        have hk_eq1 : k = 1 := by omega
        subst hk_eq1
        exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 401) (by norm_num)
          ((by omega : r = 1203) ▸ hr)
      omega
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 11) (by decide : 1 < 59) (by norm_num))
    · exact absurd hd (not_prime_of_mul_eq (by decide : 1 < 7) (by decide : 1 < 103) (by norm_num))

/-- Under `¬ 3 ∣ N` (resp. `¬ 3 ∣ N` and `¬ 5 ∣ N`) on `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2`
(`a > 1`, `l.Prime`, `d := (a + 1) / 2`), sharpens the lower bounds on `d`, `l`, and every
prime factor `r ∈ (geometricBlock q d).primeFactors`. -/
theorem exceptional_euler_first_block_three_and_five_free_bounds
    {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    (¬ 3 ∣ N →
      73 ≤ d ∧
      1553 ≤ l ∧
      (d = 73 → 1753 ≤ l) ∧
      (∀ r ∈ (geometricBlock q d).primeFactors, 293 ≤ r)) ∧
    (¬ 3 ∣ N → ¬ 5 ∣ N →
      241 ≤ d ∧
      9817 ≤ l ∧
      (d = 241 → 26993 ≤ l) ∧
      (∀ r ∈ (geometricBlock q d).primeFactors, 1447 ≤ r)) := by
  intro d
  obtain ⟨hd_prime, _, _, _, _, _, _, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  change d.Prime at hd_prime
  obtain ⟨_, _, h8d_dvd, h8d1_le, _, hr_all, _⟩ :=
    exceptional_euler_first_block_mod_eight_and_order_sieve
      hN ho hq hq4 ha4 ha hqm hform hl hi
  refine ⟨?_, ?_⟩
  · intro hN3
    obtain ⟨_, hd24, hd73, _⟩ :=
      exceptional_euler_of_not_three_dvd hN ho hq hq4 ha4 ha hqm hform hl hi hN3
    change d % 24 = 1 at hd24
    change 73 ≤ d at hd73
    obtain ⟨hl1553, hl73⟩ := prime_mod24_l_bounds hd_prime hd24 hd73 hl h8d_dvd h8d1_le
    refine ⟨hd73, hl1553, hl73, fun r hr => ?_⟩
    have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr
    obtain ⟨_, h2d_dvd, h2d1_le, _, _⟩ := hr_all r hr
    exact prime_mod24_r_bound hd_prime hd24 hd73 hr_prime h2d_dvd h2d1_le
  · intro hN3 hN5
    obtain ⟨_, _, hd120, hd241, _⟩ :=
      exceptional_euler_of_not_three_or_five_dvd hN ho hq hq4 ha4 ha hqm hform hl hi hN3 hN5
    change d % 120 ∈ ({1, 49} : Finset ℕ) at hd120
    change 241 ≤ d at hd241
    obtain ⟨hl9817, hl241⟩ := prime_mod120_l_bounds hd_prime hd120 hd241 hl h8d_dvd h8d1_le
    refine ⟨hd241, hl9817, hl241, fun r hr => ?_⟩
    have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr
    obtain ⟨_, h2d_dvd, h2d1_le, _, _⟩ := hr_all r hr
    exact prime_mod120_r_bound hd_prime hd120 hd241 hr_prime h2d_dvd h2d1_le

end OddPerfect
