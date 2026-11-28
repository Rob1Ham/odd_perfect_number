module

public import OddPerfect.SharpenedSymbolicRepunit
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section
namespace OddPerfect
open ArithmeticFunction Finset

private lemma sigma_prime_pow_lt_of_base_lt''''' {a b e : ℕ} (ha : a.Prime) (hb : b.Prime)
    (hab : a < b) (he : 0 < e) : sigma 1 (a ^ e) < sigma 1 (b ^ e) := by
  rw [sigma_one_apply_prime_pow ha, sigma_one_apply_prime_pow hb]
  exact Finset.sum_lt_sum (fun j _ => Nat.pow_le_pow_left hab.le j)
    ⟨1, Finset.mem_range.mpr (by omega), by simpa using hab⟩

private lemma sigma_prime_pow_le_of_exp_le''''' {r a b : ℕ} (hr : r.Prime) (hab : a ≤ b) :
    sigma 1 (r ^ a) ≤ sigma 1 (r ^ b) := by
  rw [sigma_one_apply_prime_pow hr, sigma_one_apply_prime_pow hr]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

private lemma exp_anti_of_sigma_eq''' {p s a b : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hab : a < b) (hfa : 0 < s.factorization a)
    (hσa : sigma 1 (a ^ (2 * s.factorization a)) = p)
    (hσb : sigma 1 (b ^ (2 * s.factorization b)) = p) :
    s.factorization b < s.factorization a := by
  by_contra! hle
  have hlt : sigma 1 (a ^ (2 * s.factorization a)) < sigma 1 (b ^ (2 * s.factorization a)) :=
    sigma_prime_pow_lt_of_base_lt''''' ha hb hab (by omega)
  have hle' : sigma 1 (b ^ (2 * s.factorization a)) ≤ sigma 1 (b ^ (2 * s.factorization b)) :=
    sigma_prime_pow_le_of_exp_le''''' hb (by omega)
  omega

private lemma nine_mul_sq_le_three_pow' {k : ℕ} (hk : 7 ≤ k) :
    9 * k ^ 2 ≤ 3 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hstep : (k + 1) ^ 2 ≤ 3 * k ^ 2 := by nlinarith
    calc 9 * (k + 1) ^ 2 ≤ 3 * (9 * k ^ 2) := by linarith
      _ ≤ 3 * 3 ^ k := Nat.mul_le_mul_left 3 ih
      _ = 3 ^ (k + 1) := by rw [pow_succ']

private lemma two_mul_le_sq_add_sq' (a b : ℕ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : (0 : ℤ) ≤ ((a : ℤ) - b) ^ 2 := sq_nonneg _
  have h2 : ((a : ℤ) - b) ^ 2 = (a : ℤ) ^ 2 - 2 * a * b + b ^ 2 := by ring
  zify
  linarith

private lemma even_index_P_L_lt_SumCoef_and_dvd''' {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    let S₁ := s.primeFactors.filter (v · = 1)
    let l (r : ℕ) := 2 * s.factorization r + 1
    let P_L := ∏ r ∈ S₁, l r
    let SumCoef := ∑ r ∈ S₁, 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t
    P_L < SumCoef ∧ p ∣ SumCoef - P_L := by
  intro v S₁ l P_L SumCoef
  have hS1_ge7 : 7 ≤ S₁.card := even_index_seven_le_S1_card hp hpo hs hu hσq hplus hσs
  have hS1_ne : S₁.Nonempty := Finset.card_pos.mp (by omega)
  have hlt_L : P_L < SumCoef := by
    obtain ⟨r₀, hr₀S⟩ := hS1_ne
    obtain ⟨hr₀, _⟩ := Finset.mem_filter.mp hr₀S
    have hr₀p := Nat.prime_of_mem_primeFactors hr₀
    have hr₀s := Nat.dvd_of_mem_primeFactors hr₀
    have hr₀o : Odd r₀ := hs.of_dvd_nat hr₀s
    have hr₀_sub : 2 ≤ r₀ - 1 := by
      have := hr₀p.two_le
      have := Nat.odd_iff.mp hr₀o
      omega
    have he₀ : 1 ≤ s.factorization r₀ := (hr₀p.dvd_iff_one_le_factorization hs.pos.ne').mp hr₀s
    have hlt_term : l r₀ < 4 * s.factorization r₀ * (r₀ - 1) := by
      dsimp [l]
      have : 8 * s.factorization r₀ ≤ 4 * s.factorization r₀ * (r₀ - 1) := by
        calc 8 * s.factorization r₀ = 4 * s.factorization r₀ * 2 := by ring
          _ ≤ 4 * s.factorization r₀ * (r₀ - 1) := Nat.mul_le_mul_left _ hr₀_sub
      omega
    have hpos_prod : 0 < ∏ t ∈ S₁.erase r₀, l t :=
      Finset.prod_pos fun _ _ => by dsimp [l]; omega
    have hsingle : P_L < 4 * s.factorization r₀ * (r₀ - 1) * ∏ t ∈ S₁.erase r₀, l t := by
      dsimp [P_L]
      rw [← Finset.mul_prod_erase S₁ l hr₀S]
      exact Nat.mul_lt_mul_of_pos_right hlt_term hpos_prod
    have hterm_le : 4 * s.factorization r₀ * (r₀ - 1) * ∏ t ∈ S₁.erase r₀, l t ≤ SumCoef :=
      Finset.single_le_sum
        (f := fun r => 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t)
        (fun _ _ => Nat.zero_le _) hr₀S
    omega
  let R := ZMod (p ^ 2)
  have hl_cop : ∀ r ∈ S₁, Nat.Coprime (l r) (p ^ 2) := by
    intro r hrS
    have hr := (Finset.mem_filter.mp hrS).1
    have hndvd : ¬ p ∣ l r :=
      (even_index_cofactor_component_order_dvd_pred hp hpo hs hσq hplus hσs hr).2.1
    exact (hp.coprime_iff_not_dvd.mpr hndvd).symm.pow_right 2
  have hprod_inv : ∀ r ∈ S₁,
      (∏ t ∈ S₁.erase r, (l t : R)) = (P_L : R) * (l r : R)⁻¹ := by
    intro r hrS
    have hl_inv : (l r : R) * (l r : R)⁻¹ = 1 :=
      ZMod.coe_mul_inv_eq_one (l r) (hl_cop r hrS)
    have hP_eq : (P_L : R) = (l r : R) * (∏ t ∈ S₁.erase r, (l t : R)) := by
      dsimp [P_L]
      push_cast
      exact (Finset.mul_prod_erase S₁ (fun t => (l t : R)) hrS).symm
    calc (∏ t ∈ S₁.erase r, (l t : R))
        = (∏ t ∈ S₁.erase r, (l t : R)) * ((l r : R) * (l r : R)⁻¹) := by rw [hl_inv, mul_one]
      _ = ((l r : R) * (∏ t ∈ S₁.erase r, (l t : R))) * (l r : R)⁻¹ := by ring
      _ = (P_L : R) * (l r : R)⁻¹ := by rw [hP_eq]
  have hcong := even_index_mod_p_sq_second_order_congruence hp hpo hs hu hσq hplus hσs
  change (∑ r ∈ S₁, ((8 * s.factorization r * (r - 1) : ℕ) : R) *
      (2 - ((r - 1 : ℕ) : R) * (p : R)) * ((2 * s.factorization r + 1 : R))⁻¹) =
    4 + 3 * (p : R) at hcong
  have hmul : (P_L : R) * (∑ r ∈ S₁, ((8 * s.factorization r * (r - 1) : ℕ) : R) *
      (2 - ((r - 1 : ℕ) : R) * (p : R)) * ((2 * s.factorization r + 1 : R))⁻¹) =
      (P_L : R) * (4 + 3 * (p : R)) :=
    congrArg ((P_L : R) * ·) hcong
  have hLHS : (P_L : R) * (∑ r ∈ S₁, ((8 * s.factorization r * (r - 1) : ℕ) : R) *
      (2 - ((r - 1 : ℕ) : R) * (p : R)) * ((2 * s.factorization r + 1 : R))⁻¹) =
      ∑ r ∈ S₁, ((8 * s.factorization r * (r - 1) : ℕ) : R) *
        (2 - ((r - 1 : ℕ) : R) * (p : R)) * (∏ t ∈ S₁.erase r, (l t : R)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hrS => ?_
    rw [hprod_inv r hrS]
    dsimp [l]
    push_cast
    ring
  have hcleared_sq : (∑ r ∈ S₁, ((8 * s.factorization r * (r - 1) : ℕ) : R) *
      (2 - ((r - 1 : ℕ) : R) * (p : R)) * (∏ t ∈ S₁.erase r, (l t : R))) =
      (P_L : R) * (4 + 3 * (p : R)) := by
    rw [← hLHS]
    exact hmul
  let f : R →+* ZMod p := ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)
  have hfp_raw := congrArg f hcleared_sq
  simp only [map_sum, map_prod, map_mul, map_sub, map_add, map_natCast, map_ofNat,
    ZMod.natCast_self, mul_zero, sub_zero, add_zero] at hfp_raw
  have h4sum : (4 : ZMod p) * (SumCoef : ZMod p) = (4 : ZMod p) * (P_L : ZMod p) := by
    calc (4 : ZMod p) * (SumCoef : ZMod p)
        = ∑ r ∈ S₁, ((8 * s.factorization r * (r - 1) : ℕ) : ZMod p) * 2 *
            ∏ t ∈ S₁.erase r, (l t : ZMod p) := by
          dsimp [SumCoef]
          push_cast
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          ring
      _ = (P_L : ZMod p) * 4 := hfp_raw
      _ = (4 : ZMod p) * (P_L : ZMod p) := by ring
  have h4_cop : Nat.Coprime 4 p := by
    simpa [show (4 : ℕ) = 2 ^ 2 by norm_num] using (Nat.coprime_two_left.mpr hpo).pow_left 2
  have h4_inv : (4 : ZMod p) * (4 : ZMod p)⁻¹ = 1 := by
    have h := ZMod.coe_mul_inv_eq_one 4 h4_cop
    simpa using h
  have hSumP : (SumCoef : ZMod p) = (P_L : ZMod p) := by
    calc (SumCoef : ZMod p)
        = ((4 : ZMod p) * (4 : ZMod p)⁻¹) * (SumCoef : ZMod p) := by rw [h4_inv, one_mul]
      _ = (4 : ZMod p)⁻¹ * ((4 : ZMod p) * (SumCoef : ZMod p)) := by ring
      _ = (4 : ZMod p)⁻¹ * ((4 : ZMod p) * (P_L : ZMod p)) := by rw [h4sum]
      _ = ((4 : ZMod p) * (4 : ZMod p)⁻¹) * (P_L : ZMod p) := by ring
      _ = (P_L : ZMod p) := by rw [h4_inv, one_mul]
  have hsub_zero : ((SumCoef - P_L : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub hlt_L.le, hSumP, sub_self]
  exact ⟨hlt_L, (ZMod.natCast_eq_zero_iff (SumCoef - P_L) p).mp hsub_zero⟩

/-- Second-order quotient congruence at an even prime-power component index
`p ^ (2 * u)`: writing `SumCoef = P_L + m * p` with `1 ≤ m`, the quadratic
coefficient sum `QuadCoef` satisfies `(QuadCoef + 3 * P_L) % p = (4 * m) % p`
and `((QuadCoef : ZMod p) + 3 * (P_L : ZMod p)) = 4 * (m : ZMod p)`. -/
theorem even_index_second_order_quotient_congruence {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    let S₁ := s.primeFactors.filter (v · = 1)
    let l (r : ℕ) := 2 * s.factorization r + 1
    let P_L := ∏ r ∈ S₁, l r
    let SumCoef := ∑ r ∈ S₁, 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t
    let QuadCoef := ∑ r ∈ S₁, 8 * s.factorization r * (r - 1) ^ 2 * ∏ t ∈ S₁.erase r, l t
    let m := (SumCoef - P_L) / p
    P_L < SumCoef ∧
      1 ≤ m ∧
      SumCoef = P_L + m * p ∧
      (QuadCoef + 3 * P_L) % p = (4 * m) % p ∧
      ((QuadCoef : ZMod p) + 3 * (P_L : ZMod p)) = 4 * (m : ZMod p) := by
  intro v S₁ l P_L SumCoef QuadCoef m
  obtain ⟨hlt_L, hp_dvd⟩ := even_index_P_L_lt_SumCoef_and_dvd''' hp hpo hs hu hσq hplus hσs
  change P_L < SumCoef at hlt_L
  change p ∣ SumCoef - P_L at hp_dvd
  have hsub_eq : SumCoef - P_L = m * p := (Nat.div_mul_cancel hp_dvd).symm
  have hm_pos : 1 ≤ m := by
    have hsub_pos : 0 < SumCoef - P_L := Nat.sub_pos_of_lt hlt_L
    rw [hsub_eq] at hsub_pos
    exact Nat.pos_of_mul_pos_right hsub_pos
  have hSum_eq : SumCoef = P_L + m * p := by
    omega
  have hmod := even_index_quotient_mod_p_congruence hp hpo hs hu hσq hplus hσs
  change 4 * m ≡ 3 * P_L + QuadCoef [MOD p] at hmod
  have hmod' : (QuadCoef + 3 * P_L) % p = (4 * m) % p := by
    simpa [Nat.ModEq, Nat.add_comm] using hmod.symm
  have hzmod : ((QuadCoef : ZMod p) + 3 * (P_L : ZMod p)) = 4 * (m : ZMod p) := by
    have h := (ZMod.natCast_eq_natCast_iff (QuadCoef + 3 * P_L) (4 * m) p).mpr hmod'
    push_cast at h
    exact h
  exact ⟨hlt_L, hm_pos, hSum_eq, hmod', hzmod⟩

/-- Second-order profile when the largest single-copy prime `r₀ ∈ S₁` has
exponent `s.factorization r₀ = 1`: we have `p = r₀ ^ 2 + r₀ + 1`,
`1 ≤ m ∧ m * r₀ < 2 * P_L`, `((r₀ - 1 : ℕ) : ZMod p) ^ 2 = - 3 * (r₀ : ZMod p)`,
and the split quadratic congruence modulo `p` in which the `r₀` term cancels
its denominator `3` into `-8 * r₀ * P_L`. -/
theorem even_index_min_exp_one_second_order_profile {q p s u r₀ : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u))
    (hr_max_mem : r₀ ∈ s.primeFactors.filter
      (fun r => (sigma 1 (r ^ (2 * s.factorization r))).factorization p = 1))
    (hr_max_ge : ∀ r ∈ s.primeFactors.filter
      (fun r => (sigma 1 (r ^ (2 * s.factorization r))).factorization p = 1), r ≤ r₀)
    (he₀ : s.factorization r₀ = 1) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    let S₁ := s.primeFactors.filter (v · = 1)
    let l (r : ℕ) := 2 * s.factorization r + 1
    let P_L := ∏ r ∈ S₁, l r
    let SumCoef := ∑ r ∈ S₁, 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t
    let m := (SumCoef - P_L) / p
    p = r₀ ^ 2 + r₀ + 1 ∧
      (1 ≤ m ∧ m * r₀ < 2 * P_L) ∧
      ((r₀ - 1 : ℕ) : ZMod p) ^ 2 = - 3 * (r₀ : ZMod p) ∧
      ((∑ r ∈ S₁.erase r₀, 8 * s.factorization r * (r - 1) ^ 2 * ∏ t ∈ S₁.erase r, l t : ℕ) : ZMod p) +
        (3 - 8 * (r₀ : ZMod p)) * (P_L : ZMod p) = 4 * (m : ZMod p) := by
  intro v S₁ l P_L SumCoef m
  let QuadCoef := ∑ r ∈ S₁, 8 * s.factorization r * (r - 1) ^ 2 * ∏ t ∈ S₁.erase r, l t
  obtain ⟨_, hm_pos, hSum_eq, _, hzmod⟩ :=
    even_index_second_order_quotient_congruence hp hpo hs hu hσq hplus hσs
  change 1 ≤ m at hm_pos
  change SumCoef = P_L + m * p at hSum_eq
  change ((QuadCoef : ZMod p) + 3 * (P_L : ZMod p)) = 4 * (m : ZMod p) at hzmod
  have hS1_ge7 : 7 ≤ S₁.card := even_index_seven_le_S1_card hp hpo hs hu hσq hplus hσs
  have hS1_ne : S₁.Nonempty := ⟨r₀, hr_max_mem⟩
  have hPL_pos : 0 < P_L := Finset.prod_pos fun _ _ => by dsimp [l]; omega
  obtain ⟨_, hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  have extract : ∀ r ∈ S₁, r.Prime ∧ Odd r ∧ 1 ≤ s.factorization r ∧
      sigma 1 (r ^ (2 * s.factorization r)) = p := by
    intro r hrS
    obtain ⟨hr, hvr⟩ := Finset.mem_filter.mp hrS
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hrs := Nat.dvd_of_mem_primeFactors hr
    have hro : Odd r := hs.of_dvd_nat hrs
    have hepos : 1 ≤ s.factorization r := (hrp.dvd_iff_one_le_factorization hs.pos.ne').mp hrs
    have hσr : sigma 1 (r ^ (2 * s.factorization r)) = p := by
      have H := (hparts r hr).2
      dsimp only at H
      change sigma 1 (r ^ (2 * s.factorization r)) = p ^ v r at H
      rwa [hvr, pow_one] at H
    exact ⟨hrp, hro, hepos, hσr⟩
  obtain ⟨hr₀p, _, _, hσ₀⟩ := extract r₀ hr_max_mem
  have hp_eq : p = r₀ ^ 2 + r₀ + 1 := by
    have h := hσ₀
    rw [he₀, show 2 * 1 = 2 by decide, sigma_one_apply_prime_pow hr₀p] at h
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      pow_zero, pow_one] at h
    omega
  have hp_lt_succ_sq : p < (r₀ + 1) ^ 2 := by
    have := hr₀p.pos
    nlinarith
  have hr₀_sq_lt_p : r₀ ^ 2 < p := by
    have := hr₀p.pos
    omega
  let r_min := S₁.min' hS1_ne
  have hr_min_mem : r_min ∈ S₁ := Finset.min'_mem S₁ hS1_ne
  obtain ⟨hr_min_p, hr_min_o, he_min_pos, hσ_min⟩ := extract r_min hr_min_mem
  have hcard_le_emin : S₁.card ≤ s.factorization r_min := by
    let e₁ := s.factorization r_min
    have hinj : Set.InjOn (fun r => s.factorization r) (S₁ : Set ℕ) := by
      intro a ha b hb hab
      obtain ⟨hap, _, heapos, hσa⟩ := extract a ha
      obtain ⟨hbp, _, hebpos, hσb⟩ := extract b hb
      rcases lt_trichotomy a b with hlt | rfl | hgt
      · exact absurd hab (ne_of_gt (exp_anti_of_sigma_eq''' hap hbp hlt heapos hσa hσb))
      · rfl
      · exact absurd hab.symm (ne_of_gt (exp_anti_of_sigma_eq''' hbp hap hgt hebpos hσb hσa))
    have himg : ∀ r ∈ S₁, s.factorization r ∈ Finset.Icc 1 e₁ := by
      intro r hrS
      obtain ⟨hrp, _, hepos, hσr⟩ := extract r hrS
      refine Finset.mem_Icc.mpr ⟨hepos, ?_⟩
      rcases eq_or_lt_of_le (Finset.min'_le S₁ r hrS) with heq | hlt
      · rw [← heq]
      · exact (exp_anti_of_sigma_eq''' hr_min_p hrp hlt he_min_pos hσ_min hσr).le
    calc S₁.card ≤ (Finset.Icc 1 e₁).card :=
          Finset.card_le_card_of_injOn (fun r => s.factorization r) himg hinj
      _ = e₁ := by simp
  have h9k_le_pow3 : 9 * S₁.card ^ 2 ≤ 3 ^ (s.factorization r_min) := by
    calc 9 * S₁.card ^ 2 ≤ 3 ^ S₁.card := nine_mul_sq_le_three_pow' hS1_ge7
      _ ≤ 3 ^ s.factorization r_min := Nat.pow_le_pow_right (by decide) hcard_le_emin
  have hr_min_ge3 : 3 ≤ r_min := by
    have := hr_min_p.two_le
    have := Nat.odd_iff.mp hr_min_o
    omega
  have hpow3_sq_lt : (3 ^ s.factorization r_min) ^ 2 < (r₀ + 1) ^ 2 := by
    have h1 : (3 ^ s.factorization r_min) ^ 2 = 3 ^ (2 * s.factorization r_min) := by
      rw [← pow_mul]; ring_nf
    have h2 : 3 ^ (2 * s.factorization r_min) ≤ r_min ^ (2 * s.factorization r_min) :=
      Nat.pow_le_pow_left hr_min_ge3 _
    have h3 : r_min ^ (2 * s.factorization r_min) < p := by
      rw [← hσ_min]
      exact self_lt_sigma_of_one_lt (one_lt_pow₀ hr_min_p.one_lt (by omega))
    omega
  have hpow3_le_r0 : 3 ^ s.factorization r_min ≤ r₀ := by
    have hlt : 3 ^ s.factorization r_min < r₀ + 1 := by
      by_contra! hle
      have hsq : (r₀ + 1) ^ 2 ≤ (3 ^ s.factorization r_min) ^ 2 := Nat.pow_le_pow_left hle 2
      omega
    exact Nat.lt_succ_iff.mp hlt
  have h9k_le_r0 : 9 * S₁.card ^ 2 ≤ r₀ := h9k_le_pow3.trans hpow3_le_r0
  have hr_sq_le_r0 : ∀ r ∈ S₁.erase r₀, r ^ 2 ≤ r₀ := by
    intro r hrE
    have hrS : r ∈ S₁ := Finset.mem_of_mem_erase hrE
    have hr_ne : r ≠ r₀ := Finset.ne_of_mem_erase hrE
    have hr_lt : r < r₀ := lt_of_le_of_ne (hr_max_ge r hrS) hr_ne
    obtain ⟨hrp, _, hepos, hσr⟩ := extract r hrS
    have h2_le_exp : 2 ≤ s.factorization r := by
      have := exp_anti_of_sigma_eq''' hrp hr₀p hr_lt hepos hσr hσ₀
      omega
    have hr4_lt_p : (r ^ 2) ^ 2 < (r₀ + 1) ^ 2 := by
      have h1 : (r ^ 2) ^ 2 = r ^ 4 := by ring
      have h2 : r ^ 4 ≤ r ^ (2 * s.factorization r) :=
        Nat.pow_le_pow_right hrp.pos (by omega)
      have h3 : r ^ (2 * s.factorization r) < p := by
        rw [← hσr]
        exact self_lt_sigma_of_one_lt (one_lt_pow₀ hrp.one_lt (by omega))
      omega
    have hlt : r ^ 2 < r₀ + 1 := by
      by_contra! hle
      have hsq : (r₀ + 1) ^ 2 ≤ (r ^ 2) ^ 2 := Nat.pow_le_pow_left hle 2
      omega
    exact Nat.lt_succ_iff.mp hlt
  have hl0 : l r₀ = 3 := by dsimp [l]; omega
  have hPL_eq : P_L = 3 * ∏ t ∈ S₁.erase r₀, l t := by
    change (∏ t ∈ S₁, l t) = 3 * ∏ t ∈ S₁.erase r₀, l t
    rw [← Finset.mul_prod_erase S₁ l hr_max_mem, hl0]
  have hmax_part : 3 * (4 * s.factorization r₀ * (r₀ - 1) * ∏ t ∈ S₁.erase r₀, l t) <
      4 * P_L * r₀ := by
    have h_eq : 3 * (4 * s.factorization r₀ * (r₀ - 1) * ∏ t ∈ S₁.erase r₀, l t) =
        4 * P_L * (r₀ - 1) := by
      rw [he₀, hPL_eq]
      ring
    rw [h_eq]
    have hsub_lt : r₀ - 1 < r₀ := Nat.sub_lt hr₀p.pos (by decide)
    exact Nat.mul_lt_mul_of_pos_left hsub_lt (Nat.mul_pos (by decide) hPL_pos)
  have herase_term_le : ∀ r ∈ S₁.erase r₀,
      S₁.card * (3 * (4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t)) ≤
        2 * P_L * r₀ := by
    intro r hrE
    have hrS : r ∈ S₁ := Finset.mem_of_mem_erase hrE
    have h1 : 4 * s.factorization r ≤ 2 * l r := by dsimp [l]; omega
    have h2 : r - 1 ≤ r := Nat.sub_le r 1
    have hterm_le : 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t ≤ 2 * P_L * r := by
      calc 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t
          ≤ (2 * l r) * r * ∏ t ∈ S₁.erase r, l t := by gcongr
        _ = 2 * (l r * ∏ t ∈ S₁.erase r, l t) * r := by ring
        _ = 2 * P_L * r := by
            rw [show l r * ∏ t ∈ S₁.erase r, l t = ∏ t ∈ S₁, l t from
              Finset.mul_prod_erase S₁ l hrS]
    have hr_sq : r ^ 2 ≤ r₀ := hr_sq_le_r0 r hrE
    have h6kr : 6 * S₁.card * r ≤ 2 * r₀ := by
      have hsq : 2 * (3 * S₁.card) * r ≤ (3 * S₁.card) ^ 2 + r ^ 2 :=
        two_mul_le_sq_add_sq' (3 * S₁.card) r
      have h9 : (3 * S₁.card) ^ 2 = 9 * S₁.card ^ 2 := by ring
      linarith
    calc S₁.card * (3 * (4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t))
        ≤ S₁.card * (3 * (2 * P_L * r)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 3 hterm_le)
      _ = P_L * (6 * S₁.card * r) := by ring
      _ ≤ P_L * (2 * r₀) := Nat.mul_le_mul_left P_L h6kr
      _ = 2 * P_L * r₀ := by ring
  have herase_sum_lt :
      3 * (∑ r ∈ S₁.erase r₀, 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t) <
        2 * P_L * r₀ := by
    have hsum_scaled :
        S₁.card * (3 * ∑ r ∈ S₁.erase r₀,
          4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t) <
          S₁.card * (2 * P_L * r₀) := by
      have hcard_erase : (S₁.erase r₀).card < S₁.card :=
        Finset.card_erase_lt_of_mem hr_max_mem
      have h2PLr_pos : 0 < 2 * P_L * r₀ :=
        Nat.mul_pos (Nat.mul_pos (by decide) hPL_pos) hr₀p.pos
      calc S₁.card * (3 * ∑ r ∈ S₁.erase r₀,
              4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t)
          = ∑ r ∈ S₁.erase r₀,
              S₁.card * (3 * (4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t)) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum]
        _ ≤ ∑ _r ∈ S₁.erase r₀, (2 * P_L * r₀) := Finset.sum_le_sum herase_term_le
        _ = (S₁.erase r₀).card * (2 * P_L * r₀) := Finset.sum_const_nat (fun _ _ => rfl)
        _ < S₁.card * (2 * P_L * r₀) := Nat.mul_lt_mul_of_pos_right hcard_erase h2PLr_pos
    exact lt_of_mul_lt_mul_left hsum_scaled (Nat.zero_le S₁.card)
  have h3Sum : 3 * SumCoef < 6 * P_L * r₀ := by
    have hsplit : SumCoef =
        4 * s.factorization r₀ * (r₀ - 1) * ∏ t ∈ S₁.erase r₀, l t +
          ∑ r ∈ S₁.erase r₀, 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t :=
      (Finset.add_sum_erase S₁
        (fun r => 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t) hr_max_mem).symm
    rw [hsplit, mul_add]
    calc 3 * (4 * s.factorization r₀ * (r₀ - 1) * ∏ t ∈ S₁.erase r₀, l t) +
          3 * ∑ r ∈ S₁.erase r₀, 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t
        < 4 * P_L * r₀ + 2 * P_L * r₀ := Nat.add_lt_add hmax_part herase_sum_lt
      _ = 6 * P_L * r₀ := by ring
  have hSum_lt : SumCoef < 2 * P_L * r₀ := by
    have h3 : 3 * SumCoef < 3 * (2 * P_L * r₀) := by
      calc 3 * SumCoef < 6 * P_L * r₀ := h3Sum
        _ = 3 * (2 * P_L * r₀) := by ring
    exact lt_of_mul_lt_mul_left h3 (Nat.zero_le 3)
  have hm_bound : m * r₀ < 2 * P_L := by
    have hmr_sq_lt : (m * r₀) * r₀ < (2 * P_L) * r₀ := by
      calc (m * r₀) * r₀ = m * r₀ ^ 2 := by ring
        _ ≤ m * p := Nat.mul_le_mul_left m hr₀_sq_lt_p.le
        _ < P_L + m * p := Nat.lt_add_of_pos_left hPL_pos
        _ = SumCoef := hSum_eq.symm
        _ < 2 * P_L * r₀ := hSum_lt
    exact lt_of_mul_lt_mul_right hmr_sq_lt (Nat.zero_le r₀)
  have hr₀_sub_sq : ((r₀ - 1 : ℕ) : ZMod p) ^ 2 = - 3 * (r₀ : ZMod p) := by
    have hr₀_ge1 : 1 ≤ r₀ := hr₀p.pos
    have hp_zero : ((r₀ ^ 2 + r₀ + 1 : ℕ) : ZMod p) = 0 := by
      rw [← hp_eq, ZMod.natCast_self]
    have hcast_sub : ((r₀ - 1 : ℕ) : ZMod p) = (r₀ : ZMod p) - 1 := by
      rw [Nat.cast_sub hr₀_ge1, Nat.cast_one]
    rw [hcast_sub]
    push_cast at hp_zero
    linear_combination hp_zero
  have hQuad_split :
      (QuadCoef : ZMod p) =
        ((8 * s.factorization r₀ * (r₀ - 1) ^ 2 * ∏ t ∈ S₁.erase r₀, l t : ℕ) : ZMod p) +
          ((∑ r ∈ S₁.erase r₀, 8 * s.factorization r * (r - 1) ^ 2 * ∏ t ∈ S₁.erase r, l t : ℕ) : ZMod p) := by
    have hsplit : QuadCoef =
        8 * s.factorization r₀ * (r₀ - 1) ^ 2 * ∏ t ∈ S₁.erase r₀, l t +
          ∑ r ∈ S₁.erase r₀, 8 * s.factorization r * (r - 1) ^ 2 * ∏ t ∈ S₁.erase r, l t :=
      (Finset.add_sum_erase S₁
        (fun r => 8 * s.factorization r * (r - 1) ^ 2 * ∏ t ∈ S₁.erase r, l t) hr_max_mem).symm
    rw [hsplit, Nat.cast_add]
  have hPL_cast : (P_L : ZMod p) = 3 * (∏ t ∈ S₁.erase r₀, (l t : ZMod p)) := by
    rw [hPL_eq]
    push_cast
    ring
  have hterm0 :
      ((8 * s.factorization r₀ * (r₀ - 1) ^ 2 * ∏ t ∈ S₁.erase r₀, l t : ℕ) : ZMod p) =
        -8 * (r₀ : ZMod p) * (P_L : ZMod p) := by
    rw [he₀]
    push_cast
    rw [hr₀_sub_sq, hPL_cast]
    ring
  have hfinal :
      ((∑ r ∈ S₁.erase r₀, 8 * s.factorization r * (r - 1) ^ 2 * ∏ t ∈ S₁.erase r, l t : ℕ) : ZMod p) +
        (3 - 8 * (r₀ : ZMod p)) * (P_L : ZMod p) = 4 * (m : ZMod p) := by
    rw [hQuad_split, hterm0] at hzmod
    linear_combination hzmod
  exact ⟨hp_eq, ⟨hm_pos, hm_bound⟩, hr₀_sub_sq, hfinal⟩

end OddPerfect
