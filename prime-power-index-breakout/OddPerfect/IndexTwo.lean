module

public import OddPerfect.EulerIndex
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith

public section

namespace OddPerfect

open ArithmeticFunction

/-- An odd-exponent component whose divisor sum divides twice a power of an odd
prime has exponent one. -/
theorem exponent_one_of_sigma_dvd_twice_prime_pow {r s q a : ℕ} (hr : Nat.Prime r)
    (hro : Odd r) (hs : Odd s) (hq : Nat.Prime q) (hqo : Odd q)
    (hd : sigma 1 (r ^ s) ∣ 2 * q ^ a) : s = 1 := by
  obtain ⟨k, hk⟩ := hs
  let t := k + 1
  let y := ∑ j ∈ Finset.range t, r ^ j
  have ht : 0 < t := by dsimp [t]; omega
  have hr3 : 3 ≤ r := by have := hr.two_le; have := Nat.odd_iff.mp hro; omega
  have hq3 : 3 ≤ q := by have := hq.two_le; have := Nat.odd_iff.mp hqo; omega
  have hfactor : sigma 1 (r ^ s) = (r ^ t + 1) * y := by
    rw [sigma_one_apply_prime_pow hr, show s + 1 = t + t by dsimp [t]; omega,
      Finset.sum_range_add]
    simp only [pow_add, ← Finset.mul_sum]
    dsimp [y]
    rw [add_mul, one_mul, Nat.add_comm]
  obtain ⟨u, hu⟩ : 2 ∣ r ^ t + 1 := by
    have := Nat.odd_iff.mp (hro.pow (n := t)); omega
  have hxu : 1 < u := by have := one_lt_pow₀ hr.one_lt ht.ne'; omega
  have hud : u ∣ q ^ a := by
    apply Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2)
    rw [← hu]
    exact (dvd_mul_right _ y).trans (hfactor ▸ hd)
  obtain ⟨v, _, hv⟩ := (Nat.dvd_prime_pow hq).mp hud
  have huv : v ≠ 0 := by rintro rfl; simp at hv; omega
  have hqx : q ∣ r ^ t + 1 := hu ▸ (hv ▸ dvd_pow_self _ huv).trans (dvd_mul_left _ _)
  have hn : ¬ q ∣ y := by
    intro h
    have hg : y * (r - 1) = r ^ t - 1 := geom_sum_mul_of_one_le (by omega) t
    have hminus := (h.trans (dvd_mul_right _ (r-1))).trans (dvd_of_eq hg)
    have hd2 := Nat.dvd_sub hqx hminus
    have hpos := Nat.pow_pos hr.pos (n := t)
    rw [show r ^ t + 1 - (r ^ t - 1) = 2 by omega] at hd2
    have := Nat.le_of_dvd (by decide : 0 < 2) hd2
    omega
  have hy2 : y ∣ 2 := ((hq.coprime_iff_not_dvd.mpr hn).symm.pow_right a).dvd_of_dvd_mul_right
    ((dvd_mul_left _ _).trans (hfactor ▸ hd))
  by_contra hs1
  have ht2 : 1 < t := by dsimp [t]; omega
  have hle : r ^ 1 ≤ y :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr ht2)
  have := Nat.le_of_dvd (by decide : 0 < 2) hy2
  simp only [pow_one] at hle
  omega

private theorem four_power_lt_three_exp {a : ℕ} (ha : 12 ≤ a) :
    2 * (a + 1) ^ 4 < 3 ^ (a - 1) := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ a ha ih =>
    rw [show a + 1 - 1 = (a - 1) + 1 by omega, pow_succ 3 (a-1)]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ha
    nlinarith only [ih, Nat.zero_le (k^4), Nat.zero_le (k^3), Nat.zero_le (k^2), Nat.zero_le k]

/-- The two index equations are impossible when the cofactor has Euler shape.
The argument uses only the reciprocal square lemma and arithmetic for odd roots
at most eleven. -/
theorem not_index_two_with_euler_cofactor {r s m q a : ℕ}
    (hr : Nat.Prime r) (hro : Odd r) (hs : Odd s) (hm : Odd m) (hrm : ¬ r ∣ m)
    (hq : Nat.Prime q) (hqo : Odd q) (ha : 0 < a)
    (hback : sigma 1 (q ^ a) = r ^ s * m ^ 2) :
    sigma 1 (r ^ s * m ^ 2) ≠ 2 * q ^ a := by
  intro hout
  have hprod := (isMultiplicative_sigma (k := 1)).map_mul_of_coprime
    (((hr.coprime_iff_not_dvd.mpr hrm).pow_left s).pow_right 2)
  have hrs : sigma 1 (r ^ s) ∣ 2 * q ^ a := by
    rw [← hout, hprod]
    exact dvd_mul_right _ _
  have hs1 := exponent_one_of_sigma_dvd_twice_prime_pow hr hro hs hq hqo hrs
  subst s
  simp only [pow_one] at hout hprod hback
  have hsigmar : sigma 1 r = r + 1 := by
    simpa [Finset.sum_range_succ, add_comm] using sigma_one_apply_prime_pow (i := 1) hr
  rw [hprod, hsigmar] at hout
  obtain ⟨u, hu⟩ : 2 ∣ r + 1 := by have := Nat.odd_iff.mp hro; omega
  have hq3 : 3 ≤ q := by have := hq.two_le; have := Nat.odd_iff.mp hqo; omega
  have hu1 : 1 < u := by have := hr.two_le; omega
  have hfactor : u * sigma 1 (m ^ 2) = q ^ a := by
    apply Nat.mul_left_cancel (by decide : 0 < 2)
    rw [← Nat.mul_assoc, ← hu, hout]
  have hud : u ∣ q ^ a := hfactor ▸ dvd_mul_right _ _
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hq).mp hud
  have hj0 : j ≠ 0 := by rintro rfl; simp at hj; omega
  have hqu : q ∣ u := hj ▸ dvd_pow_self _ hj0
  obtain ⟨β, _, hβ⟩ := (Nat.dvd_prime_pow hq).mp
    (show sigma 1 (m ^ 2) ∣ q ^ a from hfactor ▸ dvd_mul_left _ _)
  have hmlen := root_dvd_length_of_reciprocal_square hm hq hβ (hback ▸ dvd_mul_left _ _)
  have hmle := Nat.le_of_dvd (by omega : 0 < a + 1) hmlen
  let M := m ^ 2
  have hM : 0 < M := Nat.pow_pos hm.pos
  have hQM : sigma 1 (q ^ a) + M = u * (2 * M) := by
    change sigma 1 (q ^ a) = r * M at hback
    rw [hback]
    nlinarith only [congrArg (· * M) hu]
  have hsmod : sigma 1 (q ^ a) ≡ 1 [MOD q] := by
    show sigma 1 (q ^ a) % q = 1 % q
    rw [sigma_prime_pow_mod_self hq, Nat.mod_eq_of_lt hq.one_lt]
  have hqM : q ∣ M + 1 := by
    rw [add_comm]
    exact ((hsmod.add_right M).dvd_iff dvd_rfl).mp (hQM ▸ hqu.trans (dvd_mul_right _ _))
  have hgeom : sigma 1 (q ^ a) * (q - 1) = q ^ (a + 1) - 1 := by
    rw [sigma_one_apply_prime_pow hq]
    exact geom_sum_mul_of_one_le (by omega) _
  have huM : u ∣ (q - 1) * M - 1 := by
    have hz : 1 ≤ (q - 1) * M := Nat.mul_pos (by omega) hM
    have hp : 0 < q ^ (a + 1) := Nat.pow_pos hq.pos
    apply (Nat.dvd_add_iff_right (hud.trans (pow_dvd_pow q (by omega : a ≤ a + 1)))).mpr
    have heq : q ^ (a + 1) + ((q - 1) * M - 1) = u * ((2 * M) * (q - 1)) := by
      nlinarith only [congrArg (· * (q - 1)) hQM, hgeom,
        Nat.sub_add_cancel hz, Nat.sub_add_cancel hp]
    exact heq ▸ dvd_mul_right _ _
  have hum : u < q * M := by
    have hQM2 : 2 ≤ (q - 1) * M := by
      calc
        2 = 2 * 1 := by decide
        _ ≤ _ := Nat.mul_le_mul (by omega) hM
    have := Nat.le_of_dvd (by omega : 0 < (q - 1) * M - 1) huM
    have := Nat.mul_le_mul_right M (Nat.sub_le q 1)
    omega
  have hlt : q ^ a < sigma 1 (q ^ a) := by
    rw [sigma_one_apply_prime_pow hq, Finset.sum_range_succ]
    have := Finset.sum_pos' (s := Finset.range a) (f := fun j => q ^ j)
      (fun _ _ => Nat.zero_le _) ⟨0, Finset.mem_range.mpr ha, by simp⟩
    omega
  have hbound : q ^ (a - 1) < 2 * M ^ 2 := by
    apply Nat.lt_of_mul_lt_mul_left (a := q)
    rw [← pow_succ', show a - 1 + 1 = a by omega]
    calc
      q ^ a < sigma 1 (q ^ a) + M := by omega
      _ = u * (2 * M) := hQM
      _ < (q * M) * (2 * M) := Nat.mul_lt_mul_of_pos_right hum (by omega)
      _ = _ := by ring
  have hsmall : m < 12 := by
    by_contra! h
    by_cases h12 : 12 ≤ a
    · have hfast := (four_power_lt_three_exp h12).trans_le (Nat.pow_le_pow_left hq3 (a-1))
      have hpoly := Nat.pow_le_pow_left hmle 4
      dsimp [M] at hbound
      nlinarith
    · have := Nat.odd_iff.mp hm
      omega
  have hcop : (sigma 1 (m ^ 2)).Coprime (M + 1) := by
    have small : ∀ x : Fin 12, Odd (x : ℕ) → (sigma 1 ((x : ℕ) ^ 2)).Coprime ((x : ℕ) ^ 2 + 1) := by
      decide +kernel
    exact small ⟨m, hsmall⟩ hm
  have hqd : ¬ q ∣ sigma 1 (m ^ 2) := by
    intro h
    exact hq.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h hqM)
  have hβ0 : β = 0 := by
    by_contra hn
    exact hqd (hβ ▸ dvd_pow_self _ hn)
  have hMle : M ≤ sigma 1 (m ^ 2) := by
    rw [sigma_one_apply]
    exact Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) (Nat.mem_divisors_self _ hM.ne')
  simp only [hβ0, pow_zero] at hβ
  have hM1 : M = 1 := by omega
  have := Nat.le_of_dvd (by omega : 0 < M + 1) hqM
  omega

/-- For every exact prime-power component of an odd perfect number, the Euler
component has odd index at least three, and each other component has even index
at least six. -/
theorem component_index_parity_bound {N q a b i : ℕ} (hN : Nat.Perfect N) (ho : Odd N)
    (hq : Nat.Prime q) (ha : 0 < a) (hform : N = q ^ a * b) (hqb : ¬ q ∣ b)
    (hleft : sigma 1 b = q ^ a * i) (hright : sigma 1 (q ^ a) * i = 2 * b) :
    (Odd a ∧ Odd i ∧ 3 ≤ i) ∨ (Even a ∧ i % 4 = 2 ∧ 6 ≤ i) := by
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b (q ^ a))
  have hqo := ho.of_dvd_nat (hform ▸ (dvd_pow_self q ha.ne').trans (dvd_mul_right _ _))
  obtain ⟨r, s, m, hr, hr4, hs4, hrm, hE⟩ := euler_form ho hN
  have hro := Nat.odd_iff.mpr (by omega : r % 2 = 1)
  have hso := Nat.odd_iff.mpr (by omega : s % 2 = 1)
  have hm := ho.of_dvd_nat (hE ▸
    (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left _ _))
  have hb := Nat.ordCompl_pow_mul_of_not_dvd a hq hqb
  rw [← hform, hE] at hb
  rcases eq_or_ne q r with rfl | hqr
  · rw [Nat.ordCompl_pow_mul_of_not_dvd s hr (fun hd => hrm (hr.dvd_of_dvd_pow hd))] at hb
    subst b
    have has : a = s := Nat.pow_right_injective hr.two_le
      (Nat.mul_right_cancel (Nat.pow_pos hm.pos) (hform.symm.trans hE))
    subst a
    obtain ⟨_, j, hjo, hj3, hj, _⟩ := euler_component_index_bound hN ho hr hr4 hs4 hrm hE
    have hij := Nat.mul_left_cancel (Nat.pow_pos hr.pos) (hleft.symm.trans hj)
    exact Or.inl ⟨hso, hij ▸ hjo, hij ▸ hj3⟩
  · let t := m / q ^ m.factorization q
    have htm : t ∣ m := Nat.ordCompl_dvd m q
    have ht := hm.of_dvd_nat htm
    have hrt : ¬ r ∣ t := fun hd => hrm (hd.trans htm)
    have hqrnd : ¬ q ∣ r ^ s := fun hd => hqr ((Nat.prime_dvd_prime_iff_eq hq hr).mp
      (hq.dvd_of_dvd_pow hd))
    rw [Nat.ordCompl_mul, (Nat.ordCompl_eq_self_iff_zero_or_not_dvd _ hq).mpr (Or.inr hqrnd),
      pow_two, Nat.ordCompl_mul] at hb
    change r ^ s * (t * t) = b at hb
    rw [← pow_two] at hb
    have heven : Even i := by
      have hsig : 2 ∣ sigma 1 b := by
        rw [← hb, isMultiplicative_sigma.map_mul_of_coprime
          (((hr.coprime_iff_not_dvd.mpr hrt).pow_left s).pow_right 2)]
        have hrEven : 2 ∣ r + 1 := by have := Nat.odd_iff.mp hro; omega
        exact (hrEven.trans (succ_dvd_sigma_prime_pow hr hso)).trans (dvd_mul_right _ _)
      rw [hleft] at hsig
      exact even_iff_two_dvd.mpr ((Nat.prime_two.dvd_mul.mp hsig).resolve_left hqo.pow.not_two_dvd_nat)
    have haeven : Even a := by
      have hmod := sigma_modEq_of_one hq (Nat.odd_iff.mp hqo) a
      change sigma 1 (q ^ a) % 2 = (a + 1) % 2 at hmod
      have h4 : ¬ 4 ∣ 2 * b := by have := hbo.not_two_dvd_nat; omega
      apply Nat.even_iff.mpr
      by_contra h
      have h2 : 2 ∣ sigma 1 (q ^ a) := by omega
      exact h4 (hright ▸ Nat.mul_dvd_mul h2 (even_iff_two_dvd.mp heven))
    have hi2 : i ≠ 2 := by
      rintro rfl
      have hsig : sigma 1 (q ^ a) = b := Nat.mul_right_cancel (by decide : 0 < 2)
        (hright.trans (Nat.mul_comm _ _))
      exact not_index_two_with_euler_cofactor hr hro hso ht hrt hq hqo ha (hsig.trans hb.symm)
        (hb ▸ hleft.trans (Nat.mul_comm _ _))
    have hi0 : i ≠ 0 := by
      rintro rfl
      simp only [Nat.mul_zero] at hright
      have := hbo.pos
      omega
    have hnd4 : ¬ 4 ∣ i := by
      intro hd
      have h := hd.trans ((dvd_mul_left i (sigma 1 (q ^ a))).trans (dvd_of_eq hright))
      have := hbo.not_two_dvd_nat
      omega
    have hi4 : i % 4 = 2 := by have := Nat.even_iff.mp heven; omega
    exact Or.inr ⟨haeven, hi4, by omega⟩

/-- An arbitrary exact component has index at least three. -/
theorem exists_component_index_ge_three {N q a b : ℕ} (hN : Nat.Perfect N) (ho : Odd N)
    (hq : Nat.Prime q) (ha : 0 < a) (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) :
    ∃ i : ℕ, 3 ≤ i ∧ sigma 1 b = q ^ a * i ∧ sigma 1 (q ^ a) * i = 2 * b := by
  obtain ⟨i, _, hleft, hright, _⟩ := exists_component_index hN hq hform hqb
  refine ⟨i, ?_, hleft, hright⟩
  rcases component_index_parity_bound hN ho hq ha hform hqb hleft hright with h | h
  · exact h.2.2
  · exact (by omega : 3 ≤ 6).trans h.2.2

end OddPerfect
