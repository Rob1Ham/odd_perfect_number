module

public import OddPerfect.QuadrupleRepunitObstruction
public import OddPerfect.EvenIndexRadicalLift
public import OddPerfect.EvenIndexExponent256
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section
namespace OddPerfect
open ArithmeticFunction Finset

private lemma one_add_pow_of_sq_zero {R : Type*} [CommRing R] {x : R} (hx : x ^ 2 = 0) :
    ∀ j : ℕ, (1 + x) ^ j = 1 + (j : R) * x := by
  intro j
  induction j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (k : R) * hx

/-- Every single-copy cofactor prime `r ∈ S₁` divides `u + 1` to the exact first power,
and satisfies the quadratic congruence `2 * (u + 1) + r ≡ 0 [MOD r ^ 2]`. -/
theorem even_index_S1_exact_mod_sq {q p s u : ℕ}
    (hp : p.Prime) (hs : Odd s)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    let S₁ := s.primeFactors.filter (v · = 1)
    (∀ r ∈ S₁, 2 * (u + 1) + r ≡ 0 [MOD r ^ 2] ∧ r ∣ u + 1 ∧ ¬ r ^ 2 ∣ u + 1) ∧
    (∏ r ∈ S₁, r) ∣ u + 1 := by
  intro v S₁
  obtain ⟨_, hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  have hr_dvd : ∀ r ∈ S₁, r ∣ u + 1 := by
    intro r hrS
    obtain ⟨hr, hvr⟩ := Finset.mem_filter.mp hrS
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hrs := Nat.dvd_of_mem_primeFactors hr
    have hσr : sigma 1 (r ^ (2 * s.factorization r)) = p := by
      have H := (hparts r hr).2
      dsimp only at H
      change sigma 1 (r ^ (2 * s.factorization r)) = p ^ v r at H
      rwa [hvr, pow_one] at H
    exact single_copy_source_dvd hp hrp hs hrs hσq hplus hσr
  refine ⟨fun r hrS => ?_, ?_⟩
  · obtain ⟨hr, hvr⟩ := Finset.mem_filter.mp hrS
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hrs := Nat.dvd_of_mem_primeFactors hr
    have hro : Odd r := hs.of_dvd_nat hrs
    have hr_ge3 : 3 ≤ r := by
      have := hrp.two_le
      have := Nat.odd_iff.mp hro
      omega
    have hepos : 1 ≤ s.factorization r := (hrp.dvd_iff_one_le_factorization hs.pos.ne').mp hrs
    have hσr : sigma 1 (r ^ (2 * s.factorization r)) = p := by
      have H := (hparts r hr).2
      dsimp only at H
      change sigma 1 (r ^ (2 * s.factorization r)) = p ^ v r at H
      rwa [hvr, pow_one] at H
    have hdu : r ∣ u + 1 := hr_dvd r hrS
    let R := ZMod (r ^ 2)
    let x : R := r
    have hx : x ^ 2 = 0 := by
      change (r : ZMod (r ^ 2)) ^ 2 = 0
      rw [← Nat.cast_pow, ZMod.natCast_self]
    have hp_cast : (p : R) = 1 + x := by
      have hp_expand : p = 1 + r + r ^ 2 * ∑ j ∈ range (2 * s.factorization r - 1), r ^ j := by
        rw [← hσr, sigma_one_apply_prime_pow hrp,
          show 2 * s.factorization r + 1 = (2 * s.factorization r - 1) + 2 by omega,
          Finset.sum_range_succ', Finset.sum_range_succ']
        simp only [pow_zero, pow_succ', ← Finset.mul_sum]
        ring
      have hcast := congrArg (fun n : ℕ => (n : R)) hp_expand
      push_cast at hcast
      change (p : R) = 1 + x + x ^ 2 * _ at hcast
      rw [hx, zero_mul, add_zero] at hcast
      exact hcast
    have hsum_id : ∑ j ∈ range (2 * u + 1), j = u * (2 * u + 1) := by
      have h2 := Finset.sum_range_id_mul_two (2 * u + 1)
      have h2' : (∑ j ∈ range (2 * u + 1), j) * 2 = (u * (2 * u + 1)) * 2 := by
        rw [h2]
        simp only [Nat.add_sub_cancel]
        ring
      omega
    have hq_cast : (q : R) = (2 * u + 1 : R) + ((u * (2 * u + 1) : ℕ) : R) * x := by
      have hcast := congrArg (fun n : ℕ => (n : R)) hσq
      rw [sigma_one_apply_prime_pow hp] at hcast
      push_cast at hcast
      rw [hp_cast] at hcast
      have hsum_eq : ∑ j ∈ range (2 * u + 1), (1 + x) ^ j =
          ∑ j ∈ range (2 * u + 1), (1 + (j : R) * x) :=
        Finset.sum_congr rfl fun j _ => one_add_pow_of_sq_zero hx j
      rw [hsum_eq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_one, ← Finset.sum_mul, ← Nat.cast_sum, hsum_id] at hcast
      push_cast at hcast ⊢
      exact hcast.symm
    have hs2_zero : (s : R) ^ 2 = 0 := by
      rw [← Nat.cast_pow]
      exact (ZMod.natCast_eq_zero_iff (s ^ 2) (r ^ 2)).mpr (pow_dvd_pow_of_dvd hrs 2)
    have hqp1_zero : (q : R) + 1 = 0 := by
      have hcast := congrArg (fun n : ℕ => (n : R)) hplus
      push_cast at hcast
      rw [hs2_zero, mul_zero] at hcast
      exact hcast
    obtain ⟨k, hk⟩ := hdu
    have hu_cast : (u : R) = (k : R) * x - 1 := by
      have hcast := congrArg (fun n : ℕ => (n : R)) hk
      push_cast at hcast
      change (u : R) + 1 = x * (k : R) at hcast
      linear_combination hcast
    have hux_cast : ((u * (2 * u + 1) : ℕ) : R) * x = x := by
      push_cast
      rw [hu_cast]
      linear_combination (2 * (k : R) ^ 2 * x - 3 * (k : R)) * hx
    have hfinal_cast : ((2 * (u + 1) + r : ℕ) : R) = 0 := by
      push_cast
      change 2 * ((u : R) + 1) + x = 0
      linear_combination hqp1_zero - hq_cast - hux_cast
    have hmod_dvd : r ^ 2 ∣ 2 * (u + 1) + r := (ZMod.natCast_eq_zero_iff _ _).mp hfinal_cast
    have hmod : 2 * (u + 1) + r ≡ 0 [MOD r ^ 2] := Nat.modEq_zero_iff_dvd.mpr hmod_dvd
    have hnot_sq : ¬ r ^ 2 ∣ u + 1 := by
      intro hsq
      have h2sq : r ^ 2 ∣ 2 * (u + 1) := dvd_mul_of_dvd_right hsq 2
      have hr_dvd_sq : r ^ 2 ∣ r := (Nat.dvd_add_right h2sq).mp hmod_dvd
      have hle : r ^ 2 ≤ r := Nat.le_of_dvd hrp.pos hr_dvd_sq
      nlinarith
    exact ⟨hmod, hr_dvd r hrS, hnot_sq⟩
  · have hsub : S₁ ⊆ (u + 1).primeFactors := fun r hrS =>
      Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hrS).1,
        hr_dvd r hrS, by omega⟩
    exact (Finset.prod_dvd_prod_of_subset S₁ (u + 1).primeFactors id hsub).trans
      (Nat.prod_primeFactors_dvd (u + 1))

private lemma sigma_prime_pow_lt_of_base_lt' {a b e : ℕ} (ha : a.Prime) (hb : b.Prime)
    (hab : a < b) (he : 0 < e) : sigma 1 (a ^ e) < sigma 1 (b ^ e) := by
  rw [sigma_one_apply_prime_pow ha, sigma_one_apply_prime_pow hb]
  exact Finset.sum_lt_sum (fun j _ => Nat.pow_le_pow_left hab.le j)
    ⟨1, Finset.mem_range.mpr (by omega), by simpa using hab⟩

private lemma sigma_prime_pow_le_of_exp_le' {r a b : ℕ} (hr : r.Prime) (hab : a ≤ b) :
    sigma 1 (r ^ a) ≤ sigma 1 (r ^ b) := by
  rw [sigma_one_apply_prime_pow hr, sigma_one_apply_prime_pow hr]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

/-- At any even prime-power component index `i = p ^ (2 * u)`, `4 ≤ S₁.card` combined with
`∏ r ∈ S₁, r ∣ u + 1` and the repunit representations forces `1154 ≤ u`, `2308 ≤ 2 * u`,
and `12207031 ≤ p`. -/
theorem even_index_exponent_ge_2308_and_base_ge_12207031 {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    1154 ≤ u ∧ 2308 ≤ 2 * u ∧ 12207031 ≤ p := by
  let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
  let S₁ := s.primeFactors.filter (v · = 1)
  have hS1_ge4 : 4 ≤ S₁.card := even_index_four_le_S1_card hp hpo hs hu hσq hplus hσs
  change 4 ≤ S₁.card at hS1_ge4
  have hex4 : ∃ r₁ r₂ r₃ r₄, r₁ ∈ S₁ ∧ r₂ ∈ S₁ ∧ r₃ ∈ S₁ ∧ r₄ ∈ S₁ ∧
      r₁ < r₂ ∧ r₂ < r₃ ∧ r₃ < r₄ := by
    let f := S₁.orderEmbOfFin rfl
    refine ⟨f ⟨0, by omega⟩, f ⟨1, by omega⟩, f ⟨2, by omega⟩, f ⟨3, by omega⟩,
      Finset.orderEmbOfFin_mem S₁ rfl _, Finset.orderEmbOfFin_mem S₁ rfl _,
      Finset.orderEmbOfFin_mem S₁ rfl _, Finset.orderEmbOfFin_mem S₁ rfl _,
      f.strictMono (Fin.mk_lt_mk.mpr (by decide)),
      f.strictMono (Fin.mk_lt_mk.mpr (by decide)),
      f.strictMono (Fin.mk_lt_mk.mpr (by decide))⟩
  obtain ⟨r₁, r₂, r₃, r₄, hr₁S, hr₂S, hr₃S, hr₄S, hr₁₂, hr₂₃, hr₃₄⟩ := hex4
  obtain ⟨_, hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  have extract : ∀ r ∈ S₁, r.Prime ∧ Odd r ∧ 1 ≤ s.factorization r ∧
      (2 * s.factorization r + 1).Prime ∧ sigma 1 (r ^ (2 * s.factorization r)) = p := by
    intro r hrS
    obtain ⟨hr, hvr⟩ := Finset.mem_filter.mp hrS
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hrs := Nat.dvd_of_mem_primeFactors hr
    have hro : Odd r := hs.of_dvd_nat hrs
    have hepos : 1 ≤ s.factorization r := (hrp.dvd_iff_one_le_factorization hs.pos.ne').mp hrs
    have hlp := (even_index_cofactor_component_order_dvd_pred hp hpo hs hσq hplus hσs hr).1
    have hσr : sigma 1 (r ^ (2 * s.factorization r)) = p := by
      have H := (hparts r hr).2
      dsimp only at H
      change sigma 1 (r ^ (2 * s.factorization r)) = p ^ v r at H
      rwa [hvr, pow_one] at H
    exact ⟨hrp, hro, hepos, hlp, hσr⟩
  obtain ⟨hr₁p, hr₁o, he₁pos, hl₁p, hσr₁⟩ := extract r₁ hr₁S
  obtain ⟨hr₂p, hr₂o, he₂pos, hl₂p, hσr₂⟩ := extract r₂ hr₂S
  obtain ⟨hr₃p, hr₃o, he₃pos, hl₃p, hσr₃⟩ := extract r₃ hr₃S
  obtain ⟨hr₄p, hr₄o, he₄pos, hl₄p, hσr₄⟩ := extract r₄ hr₄S
  have hr₁_ge3 : 3 ≤ r₁ := by have := hr₁p.two_le; have := Nat.odd_iff.mp hr₁o; omega
  have hr₂_ge5 : 5 ≤ r₂ := by have := Nat.odd_iff.mp hr₂o; omega
  have hr₃_ge7 : 7 ≤ r₃ := by have := Nat.odd_iff.mp hr₃o; omega
  have hr₄_ge11 : 11 ≤ r₄ := by
    have := Nat.odd_iff.mp hr₄o
    have h9 : r₄ ≠ 9 := by
      intro h9
      rw [h9] at hr₄p
      exact (by decide : ¬ Nat.Prime 9) hr₄p
    omega
  have hprod_dvd : (∏ r ∈ S₁, r) ∣ u + 1 :=
    (even_index_S1_exact_mod_sq hp hs hσq hplus hσs).2
  have hprod_le : ∏ r ∈ S₁, r ≤ u + 1 := Nat.le_of_dvd (by omega) hprod_dvd
  have hsub4 : ({r₁, r₂, r₃, r₄} : Finset ℕ) ⊆ S₁ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hprod4_dvd : (∏ r ∈ ({r₁, r₂, r₃, r₄} : Finset ℕ), r) ∣ ∏ r ∈ S₁, r :=
    Finset.prod_dvd_prod_of_subset _ _ id hsub4
  have hprod4_eq : (∏ r ∈ ({r₁, r₂, r₃, r₄} : Finset ℕ), r) = r₁ * r₂ * r₃ * r₄ := by
    rw [Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
      Finset.prod_insert (by simp; omega), Finset.prod_singleton]
    ring
  have hprod4_le : r₁ * r₂ * r₃ * r₄ ≤ ∏ r ∈ S₁, r := by
    rw [← hprod4_eq]
    exact Nat.le_of_dvd (Finset.prod_pos fun r hr =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1).pos) hprod4_dvd
  have h1155 : 1155 ≤ r₁ * r₂ * r₃ * r₄ := by
    calc 1155 = 3 * 5 * 7 * 11 := by norm_num
      _ ≤ r₁ * r₂ * r₃ * r₄ := by gcongr
  have hu_ge : 1154 ≤ u := by omega
  refine ⟨hu_ge, by omega, ?_⟩
  have exp_anti : ∀ {a b : ℕ}, a.Prime → b.Prime → a < b → 0 < s.factorization a →
      sigma 1 (a ^ (2 * s.factorization a)) = p →
      sigma 1 (b ^ (2 * s.factorization b)) = p →
      s.factorization b < s.factorization a := by
    intro a b hap hbp hab hfa hσa hσb
    by_contra! hle
    have hlt : sigma 1 (a ^ (2 * s.factorization a)) < sigma 1 (b ^ (2 * s.factorization a)) :=
      sigma_prime_pow_lt_of_base_lt' hap hbp hab (by omega)
    have hle' : sigma 1 (b ^ (2 * s.factorization a)) ≤ sigma 1 (b ^ (2 * s.factorization b)) :=
      sigma_prime_pow_le_of_exp_le' hbp (by omega)
    omega
  have he₃₄ : s.factorization r₄ < s.factorization r₃ :=
    exp_anti hr₃p hr₄p hr₃₄ he₃pos hσr₃ hσr₄
  have he₂₃ : s.factorization r₃ < s.factorization r₂ :=
    exp_anti hr₂p hr₃p hr₂₃ he₂pos hσr₂ hσr₃
  have he₁₂ : s.factorization r₂ < s.factorization r₁ :=
    exp_anti hr₁p hr₂p hr₁₂ he₁pos hσr₁ hσr₂
  have he₁_ge5 : 5 ≤ s.factorization r₁ := by
    have hnot9 : 2 * s.factorization r₁ + 1 ≠ 9 := by
      intro h9
      rw [h9] at hl₁p
      exact (by decide : ¬ Nat.Prime 9) hl₁p
    omega
  by_cases he₁_ge8 : 8 ≤ s.factorization r₁
  · have hlt : r₁ ^ (2 * s.factorization r₁) < p := by
      rw [← hσr₁]
      exact self_lt_sigma_of_one_lt (one_lt_pow₀ hr₁p.one_lt (by omega))
    have h3_16 : (3 : ℕ) ^ 16 ≤ r₁ ^ (2 * s.factorization r₁) :=
      (Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 16 ≤ 2 * s.factorization r₁)).trans
        (Nat.pow_le_pow_left hr₁_ge3 (2 * s.factorization r₁))
    have hbig : 12207031 < (3 : ℕ) ^ 16 := by norm_num
    omega
  · have he₁_cases : s.factorization r₁ = 5 ∨ s.factorization r₁ = 6 ∨ s.factorization r₁ = 7 := by
      omega
    rcases he₁_cases with he₁_5 | he₁_6 | he₁_7
    · by_cases hr₁_ge5 : 5 ≤ r₁
      · have h5_10 : sigma 1 (5 ^ 10) ≤ p := by
          rw [← hσr₁, he₁_5, show 2 * 5 = 10 by rfl,
            sigma_one_apply_prime_pow (by decide : Nat.Prime 5),
            sigma_one_apply_prime_pow hr₁p]
          exact Finset.sum_le_sum fun j _ => Nat.pow_le_pow_left hr₁_ge5 j
        have hval : sigma 1 (5 ^ 10) = 12207031 := by
          rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 5)]
          simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
          norm_num
        rw [hval] at h5_10
        exact h5_10
      · have hr₁_eq3 : r₁ = 3 := by have := Nat.odd_iff.mp hr₁o; omega
        have hp_val : p = 88573 := by
          rw [← hσr₁, he₁_5, hr₁_eq3, show 2 * 5 = 10 by rfl,
            sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
          simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
          norm_num
        rw [hp_val] at hp
        have h23 : 23 ∣ 88573 := by norm_num
        have := hp.eq_one_or_self_of_dvd 23 h23
        omega
    · by_cases hr₁_ge5 : 5 ≤ r₁
      · have hlt : r₁ ^ (2 * s.factorization r₁) < p := by
          rw [← hσr₁]
          exact self_lt_sigma_of_one_lt (one_lt_pow₀ hr₁p.one_lt (by omega))
        have h5_12 : (5 : ℕ) ^ 12 ≤ r₁ ^ (2 * s.factorization r₁) := by
          rw [he₁_6, show 2 * 6 = 12 by rfl]
          exact Nat.pow_le_pow_left hr₁_ge5 12
        have hbig : 12207031 < (5 : ℕ) ^ 12 := by norm_num
        exact le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le hbig h5_12) hlt.le)
      · have hr₁_eq3 : r₁ = 3 := by have := Nat.odd_iff.mp hr₁o; omega
        have hp_val : p = 797161 := by
          rw [← hσr₁, he₁_6, hr₁_eq3, show 2 * 6 = 12 by rfl,
            sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
          simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
          norm_num
        have hdvd := (even_index_repunit_lengths_dvd_pred hp hpo hs hσq hplus hσs).1
        have hdiv : ∀ r ∈ S₁, 2 * s.factorization r + 1 ∣ 398580 := by
          intro r hrS
          have H := hdvd r hrS
          rw [hp_val] at H
          exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) H
        have hne5 : ∀ r ∈ S₁, s.factorization r ≠ 5 := by
          intro r hrS h5
          have H := hdiv r hrS
          rw [h5] at H
          exact (by decide : ¬ (11 ∣ 398580)) H
        have hne4 : ∀ r ∈ S₁, (2 * s.factorization r + 1).Prime → s.factorization r ≠ 4 := by
          intro r _ hlp h4
          rw [h4] at hlp
          exact (by decide : ¬ Nat.Prime 9) hlp
        have he₂_lt4 : s.factorization r₂ ≤ 3 := by
          have := hne5 r₂ hr₂S
          have := hne4 r₂ hr₂S hl₂p
          omega
        have he₄_eq1 : s.factorization r₄ = 1 := by omega
        have hσ₄_eq : 1 + r₄ + r₄ ^ 2 = 797161 := by
          rw [← hp_val, ← hσr₄, he₄_eq1, mul_one, sigma_one_apply_prime_pow hr₄p]
          simp [Finset.sum_range_succ, Nat.add_assoc]
        by_cases hr₄_le : r₄ ≤ 892
        · exfalso; nlinarith only [hσ₄_eq, hr₄_le]
        · exfalso; nlinarith only [hσ₄_eq, hr₄_le]
    · rw [he₁_7] at hl₁p
      exact False.elim ((by decide : ¬ Nat.Prime 15) hl₁p)

/-- Every prime-power component index `i = p ^ j` of an odd perfect number satisfies
`2308 ≤ j`, `10 ^ 16156 < i`, and `10 ^ 16156 < N`. -/
theorem component_prime_power_index_exponent_ge_2308 {N q a b i p j : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b)
    (hl : sigma 1 b = q ^ a * i) (hr : sigma 1 (q ^ a) * i = 2 * b)
    (hp : p.Prime) (hj : 0 < j) (hi : i = p ^ j) :
    2308 ≤ j ∧ 10 ^ 16156 < i ∧ 10 ^ 16156 < N := by
  have hbo : Odd b := ho.of_dvd_nat (hform ▸ dvd_mul_left b _)
  have hqo : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_left (dvd_pow_self q ha.ne') b)
  have hq3 : 3 ≤ q := by have := hq.two_le; have := Nat.odd_iff.mp hqo; omega
  have hσqa_ge4 : 4 ≤ sigma 1 (q ^ a) := by
    have h1 : q ^ a < sigma 1 (q ^ a) :=
      self_lt_sigma_of_one_lt (one_lt_pow₀ hq.one_lt ha.ne')
    have h2 : 3 ≤ q ^ a := hq3.trans (Nat.le_self_pow ha.ne' q)
    omega
  have hi_lt_N : i < N := by
    have hi_pos : 0 < i := hi ▸ pow_pos hp.pos j
    have h4i_le : 4 * i ≤ 2 * b := by
      calc 4 * i ≤ sigma 1 (q ^ a) * i := Nat.mul_le_mul_right i hσqa_ge4
        _ = 2 * b := hr
    have h2i_le : 2 * i ≤ b := by omega
    have hb_le : b ≤ N := by
      rw [hform]
      exact Nat.le_mul_of_pos_left b (pow_pos hq.pos a)
    omega
  have hp_ne_two : 2 ≤ j → p ≠ 2 := by
    intro hj2 hp2
    rw [hp2] at hi
    have h4 : 4 ∣ 2 * b := hr ▸ hi ▸ (pow_dvd_pow 2 hj2).trans (dvd_mul_left _ _)
    have := hbo.not_two_dvd_nat
    omega
  suffices hmain : 2308 ≤ j ∧ 10 ^ 16156 < i from
    ⟨hmain.1, hmain.2, hmain.2.trans hi_lt_N⟩
  rcases Nat.even_or_odd j with ⟨u, hu'⟩ | hj_odd
  · have hj2 : j = 2 * u := by omega
    have hu : 0 < u := by omega
    rw [hj2] at hi
    have hp2 : p ≠ 2 := hp_ne_two (by omega)
    have hpo := hp.odd_of_ne_two hp2
    obtain ⟨ha1, hσq⟩ := even_prime_power_index_eq_selected_sigma hN ho hq ha hform hqb hl hr hp hu hi
    obtain ⟨m, _, _, hqm, rfl⟩ :=
      euler_form_of_odd_component_index hN ho hq ha hform hqb hl hr (hi ▸ hpo.pow)
    have hmo := ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _)
    rw [ha1, pow_one] at hform hl hr
    rw [hi] at hl hr
    obtain ⟨s, hs, _, _, _, hplus, hσs⟩ := even_prime_power_cofactor_split hq hp hmo hpo hu hl hr
    obtain ⟨_, h2u_ge, hp_ge⟩ :=
      even_index_exponent_ge_2308_and_base_ge_12207031 hp hpo hs hu hσq hplus hσs
    have hj_ge : 2308 ≤ j := by omega
    have hp_gt : 10 ^ 7 < p := lt_of_lt_of_le (by decide : 10 ^ 7 < 12207031) hp_ge
    have hi_gt : 10 ^ 16156 < i := by
      rw [hi, ← hj2]
      obtain ⟨B, hB_eq, hB_lt⟩ : ∃ B : ℕ, B = 10 ^ 7 ∧ B < p := ⟨10 ^ 7, rfl, hp_gt⟩
      have h1 : 10 ^ 16156 = B ^ 2308 := by
        rw [hB_eq, show 16156 = 7 * 2308 by norm_num, pow_mul]
      have h2 : B ^ 2308 < p ^ 2308 := pow_lt_pow_left₀ hB_lt (Nat.zero_le B) (by omega)
      have h3 : p ^ 2308 ≤ p ^ j := pow_le_pow_right₀ hp.one_le hj_ge
      rw [h1]
      exact lt_of_lt_of_le h2 h3
    exact ⟨hj_ge, hi_gt⟩
  · have hj_ge_36207 : 36207 ≤ j := by
      by_contra! hlt
      exact IndexObstruction.component_index_ne_odd_prime_power_below_36207
        hN ho hq ha hform hqb hl hr hp hj_odd hlt hi
    have hp2 : p ≠ 2 := hp_ne_two (by omega)
    have hp3 : 3 ≤ p := by have := hp.two_le; have := hp.eq_two_or_odd'; omega
    have h3_21 : 10 ^ 10 < 3 ^ 21 := by norm_num
    have hi_gt : 10 ^ 16156 < i := by
      rw [hi]
      calc 10 ^ 16156 < 10 ^ 17240 := pow_lt_pow_right₀ (by decide : 1 < 10) (by decide : 16156 < 17240)
        _ = (10 ^ 10) ^ 1724 := by rw [show 17240 = 10 * 1724 by norm_num, pow_mul]
        _ < (3 ^ 21) ^ 1724 := pow_lt_pow_left₀ h3_21 (by positivity) (by decide : 1724 ≠ 0)
        _ = 3 ^ 36204 := by rw [show 36204 = 21 * 1724 by norm_num, pow_mul]
        _ ≤ 3 ^ j := pow_le_pow_right₀ (by decide : 1 ≤ 3) (by omega : 36204 ≤ j)
        _ ≤ p ^ j := Nat.pow_le_pow_left hp3 j
    exact ⟨by omega, hi_gt⟩

end OddPerfect
