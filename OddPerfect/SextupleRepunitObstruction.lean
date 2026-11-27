module

public import OddPerfect.PrimePowerHigherObstruction
import Mathlib.Data.Finset.Sort
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- The same integer has prime-length repunit representations in six
distinct odd prime bases. -/
@[expose] def HasSixOddPrimeRepunits (z : ℕ) : Prop :=
  ∃ r₁ r₂ r₃ r₄ r₅ r₆ l₁ l₂ l₃ l₄ l₅ l₆ : ℕ,
    r₁.Prime ∧ Odd r₁ ∧ r₂.Prime ∧ Odd r₂ ∧ r₃.Prime ∧ Odd r₃ ∧
    r₄.Prime ∧ Odd r₄ ∧ r₅.Prime ∧ Odd r₅ ∧ r₆.Prime ∧ Odd r₆ ∧
    r₁ ≠ r₂ ∧ r₁ ≠ r₃ ∧ r₁ ≠ r₄ ∧ r₁ ≠ r₅ ∧ r₁ ≠ r₆ ∧
    r₂ ≠ r₃ ∧ r₂ ≠ r₄ ∧ r₂ ≠ r₅ ∧ r₂ ≠ r₆ ∧
    r₃ ≠ r₄ ∧ r₃ ≠ r₅ ∧ r₃ ≠ r₆ ∧
    r₄ ≠ r₅ ∧ r₄ ≠ r₆ ∧
    r₅ ≠ r₆ ∧
    l₁.Prime ∧ 2 < l₁ ∧ l₂.Prime ∧ 2 < l₂ ∧ l₃.Prime ∧ 2 < l₃ ∧
    l₄.Prime ∧ 2 < l₄ ∧ l₅.Prime ∧ 2 < l₅ ∧ l₆.Prime ∧ 2 < l₆ ∧
    geometricBlock r₁ l₁ = z ∧ geometricBlock r₂ l₂ = z ∧
    geometricBlock r₃ l₃ = z ∧ geometricBlock r₄ l₄ = z ∧
    geometricBlock r₅ l₅ = z ∧ geometricBlock r₆ l₆ = z

/-- Exponential domination `100 * (2 * e + 1) ^ 10 ≤ 3 ^ (2 * e)` for `19 ≤ e`. -/
theorem hundred_mul_odd_pow10_le_three_pow {e : ℕ} (he : 19 ≤ e) :
    100 * (2 * e + 1) ^ 10 ≤ 3 ^ (2 * e) := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hstep : 6 * (2 * (k + 1) + 1) ≤ 7 * (2 * k + 1) := by omega
    have hpow10 : 6 ^ 10 * (2 * (k + 1) + 1) ^ 10 ≤ 7 ^ 10 * (2 * k + 1) ^ 10 := by
      calc 6 ^ 10 * (2 * (k + 1) + 1) ^ 10
          = (6 * (2 * (k + 1) + 1)) ^ 10 := by ring
        _ ≤ (7 * (2 * k + 1)) ^ 10 := Nat.pow_le_pow_left hstep 10
        _ = 7 ^ 10 * (2 * k + 1) ^ 10 := by ring
    have hscale : 60466176 * (100 * (2 * (k + 1) + 1) ^ 10) ≤ 60466176 * 3 ^ (2 * (k + 1)) := by
      calc 60466176 * (100 * (2 * (k + 1) + 1) ^ 10)
          = 100 * (6 ^ 10 * (2 * (k + 1) + 1) ^ 10) := by norm_num; ring
        _ ≤ 100 * (7 ^ 10 * (2 * k + 1) ^ 10) := Nat.mul_le_mul_left 100 hpow10
        _ = 282475249 * (100 * (2 * k + 1) ^ 10) := by norm_num; ring
        _ ≤ 544195584 * (100 * (2 * k + 1) ^ 10) := Nat.mul_le_mul_right _ (by decide)
        _ ≤ 544195584 * 3 ^ (2 * k) := Nat.mul_le_mul_left 544195584 ih
        _ = 60466176 * 3 ^ (2 * (k + 1)) := by rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]; ring
    omega

private lemma sigma_prime_pow_lt_of_base_lt'' {a b e : ℕ} (ha : a.Prime) (hb : b.Prime)
    (hab : a < b) (he : 0 < e) : sigma 1 (a ^ e) < sigma 1 (b ^ e) := by
  rw [sigma_one_apply_prime_pow ha, sigma_one_apply_prime_pow hb]
  exact Finset.sum_lt_sum (fun j _ => Nat.pow_le_pow_left hab.le j)
    ⟨1, Finset.mem_range.mpr (by omega), by simpa using hab⟩

private lemma sigma_prime_pow_le_of_exp_le'' {r a b : ℕ} (hr : r.Prime) (hab : a ≤ b) :
    sigma 1 (r ^ a) ≤ sigma 1 (r ^ b) := by
  rw [sigma_one_apply_prime_pow hr, sigma_one_apply_prime_pow hr]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

private lemma exp_anti_of_sigma_eq {p s a b : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hab : a < b) (hfa : 0 < s.factorization a)
    (hσa : sigma 1 (a ^ (2 * s.factorization a)) = p)
    (hσb : sigma 1 (b ^ (2 * s.factorization b)) = p) :
    s.factorization b < s.factorization a := by
  by_contra! hle
  have hlt : sigma 1 (a ^ (2 * s.factorization a)) < sigma 1 (b ^ (2 * s.factorization a)) :=
    sigma_prime_pow_lt_of_base_lt'' ha hb hab (by omega)
  have hle' : sigma 1 (b ^ (2 * s.factorization a)) ≤ sigma 1 (b ^ (2 * s.factorization b)) :=
    sigma_prime_pow_le_of_exp_le'' hb (by omega)
  omega

private lemma even_index_P_L_lt_SumCoef_and_dvd {q p s u : ℕ}
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
  have hS1_ge5 : 5 ≤ S₁.card := even_index_five_le_S1_card hp hpo hs hu hσq hplus hσs
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

private lemma refute_card_five_arith {p r₁ r₂ r₃ r₄ r₅ e₁ e₂ e₃ e₄ e₅ : ℕ}
    (hp : p.Prime) (hr₁p : r₁.Prime) (hr₁o : Odd r₁)
    (hr₂p : r₂.Prime) (hr₃p : r₃.Prime) (hr₄p : r₄.Prime) (hr₅p : r₅.Prime)
    (he₅ : 1 ≤ e₅) (he₄₅ : e₅ < e₄) (he₃₄ : e₄ < e₃) (he₂₃ : e₃ < e₂) (he₁₂ : e₂ < e₁)
    (hr₁₂ : r₁ < r₂) (hr₂₃ : r₂ < r₃) (hr₃₄ : r₃ < r₄) (hr₄₅ : r₄ < r₅)
    (hl₁p : (2 * e₁ + 1).Prime) (hl₂p : (2 * e₂ + 1).Prime)
    (hl₃p : (2 * e₃ + 1).Prime) (hl₄p : (2 * e₄ + 1).Prime) (hl₅p : (2 * e₅ + 1).Prime)
    (hl₂_dvd : 2 * (2 * e₂ + 1) ∣ p - 1)
    (hσr₁ : sigma 1 (r₁ ^ (2 * e₁)) = p)
    (hσr₅ : sigma 1 (r₅ ^ (2 * e₅)) = p)
    (hle_p : p ≤ 4 * e₁ * (r₁ - 1) * (2 * e₂ + 1) * (2 * e₃ + 1) * (2 * e₄ + 1) * (2 * e₅ + 1) +
      4 * e₂ * (r₂ - 1) * (2 * e₁ + 1) * (2 * e₃ + 1) * (2 * e₄ + 1) * (2 * e₅ + 1) +
      4 * e₃ * (r₃ - 1) * (2 * e₁ + 1) * (2 * e₂ + 1) * (2 * e₄ + 1) * (2 * e₅ + 1) +
      4 * e₄ * (r₄ - 1) * (2 * e₁ + 1) * (2 * e₂ + 1) * (2 * e₃ + 1) * (2 * e₅ + 1) +
      4 * e₅ * (r₅ - 1) * (2 * e₁ + 1) * (2 * e₂ + 1) * (2 * e₃ + 1) * (2 * e₄ + 1) -
      (2 * e₁ + 1) * (2 * e₂ + 1) * (2 * e₃ + 1) * (2 * e₄ + 1) * (2 * e₅ + 1)) : False := by
  have he₄ : 2 ≤ e₄ := by omega
  have he₃ : 3 ≤ e₃ := by omega
  have he₂ : 5 ≤ e₂ := by
    have hnot9 : 2 * e₂ + 1 ≠ 9 := by
      intro h9
      rw [h9] at hl₂p
      exact absurd hl₂p (by decide)
    omega
  have he₁ : 6 ≤ e₁ := by omega
  have hr₁_mod : r₁ % 2 = 1 := Nat.odd_iff.mp hr₁o
  have hr₁_ge3 : 3 ≤ r₁ := by have := hr₁p.two_le; omega
  let l₁ := 2 * e₁ + 1
  let l₂ := 2 * e₂ + 1
  let l₃ := 2 * e₃ + 1
  let l₄ := 2 * e₄ + 1
  let l₅ := 2 * e₅ + 1
  let L := 4 * e₁ * (r₁ - 1) * l₂ * l₃ * l₄ * l₅ +
    4 * e₂ * (r₂ - 1) * l₁ * l₃ * l₄ * l₅ +
    4 * e₃ * (r₃ - 1) * l₁ * l₂ * l₄ * l₅ +
    4 * e₄ * (r₄ - 1) * l₁ * l₂ * l₃ * l₅ +
    4 * e₅ * (r₅ - 1) * l₁ * l₂ * l₃ * l₄ - l₁ * l₂ * l₃ * l₄ * l₅
  have hle_p' : p ≤ L := hle_p
  have hr₁₅ : r₁ < r₅ := lt_trans hr₁₂ (lt_trans hr₂₃ (lt_trans hr₃₄ hr₄₅))
  have hr₂₅ : r₂ < r₅ := lt_trans hr₂₃ (lt_trans hr₃₄ hr₄₅)
  have hr₃₅ : r₃ < r₅ := lt_trans hr₃₄ hr₄₅
  have hL_lt_prod : L < 10 * l₁ * l₂ * l₃ * l₄ * l₅ * r₅ := by
    have h1 : 4 * e₁ * (r₁ - 1) * l₂ * l₃ * l₄ * l₅ ≤ 4 * e₁ * r₁ * l₂ * l₃ * l₄ * l₅ := by
      gcongr; omega
    have h2 : 4 * e₂ * (r₂ - 1) * l₁ * l₃ * l₄ * l₅ ≤ 4 * e₂ * r₂ * l₁ * l₃ * l₄ * l₅ := by
      gcongr; omega
    have h3 : 4 * e₃ * (r₃ - 1) * l₁ * l₂ * l₄ * l₅ ≤ 4 * e₃ * r₃ * l₁ * l₂ * l₄ * l₅ := by
      gcongr; omega
    have h4 : 4 * e₄ * (r₄ - 1) * l₁ * l₂ * l₃ * l₅ ≤ 4 * e₄ * r₄ * l₁ * l₂ * l₃ * l₅ := by
      gcongr; omega
    have h5 : 4 * e₅ * (r₅ - 1) * l₁ * l₂ * l₃ * l₄ ≤ 4 * e₅ * r₅ * l₁ * l₂ * l₃ * l₄ := by
      gcongr; omega
    have ht1 : 4 * e₁ * r₁ * l₂ * l₃ * l₄ * l₅ < 2 * l₁ * l₂ * l₃ * l₄ * l₅ * r₅ := by
      have ha : 4 * e₁ * r₁ < 2 * l₁ * r₅ :=
        calc 4 * e₁ * r₁ < 2 * l₁ * r₁ := Nat.mul_lt_mul_of_pos_right (by dsimp [l₁]; omega) hr₁p.pos
          _ < 2 * l₁ * r₅ := Nat.mul_lt_mul_of_pos_left hr₁₅ (by positivity)
      calc 4 * e₁ * r₁ * l₂ * l₃ * l₄ * l₅ < 2 * l₁ * r₅ * l₂ * l₃ * l₄ * l₅ :=
            Nat.mul_lt_mul_of_pos_right
              (Nat.mul_lt_mul_of_pos_right
                (Nat.mul_lt_mul_of_pos_right
                  (Nat.mul_lt_mul_of_pos_right ha (by dsimp [l₂]; omega))
                  (by dsimp [l₃]; omega))
                (by dsimp [l₄]; omega))
              (by dsimp [l₅]; omega)
        _ = 2 * l₁ * l₂ * l₃ * l₄ * l₅ * r₅ := by ring
    have ht2 : 4 * e₂ * r₂ * l₁ * l₃ * l₄ * l₅ < 2 * l₁ * l₂ * l₃ * l₄ * l₅ * r₅ := by
      have ha : 4 * e₂ * r₂ < 2 * l₂ * r₅ :=
        calc 4 * e₂ * r₂ < 2 * l₂ * r₂ := Nat.mul_lt_mul_of_pos_right (by dsimp [l₂]; omega) hr₂p.pos
          _ < 2 * l₂ * r₅ := Nat.mul_lt_mul_of_pos_left hr₂₅ (by positivity)
      calc 4 * e₂ * r₂ * l₁ * l₃ * l₄ * l₅ < 2 * l₂ * r₅ * l₁ * l₃ * l₄ * l₅ :=
            Nat.mul_lt_mul_of_pos_right
              (Nat.mul_lt_mul_of_pos_right
                (Nat.mul_lt_mul_of_pos_right
                  (Nat.mul_lt_mul_of_pos_right ha (by dsimp [l₁]; omega))
                  (by dsimp [l₃]; omega))
                (by dsimp [l₄]; omega))
              (by dsimp [l₅]; omega)
        _ = 2 * l₁ * l₂ * l₃ * l₄ * l₅ * r₅ := by ring
    have ht3 : 4 * e₃ * r₃ * l₁ * l₂ * l₄ * l₅ < 2 * l₁ * l₂ * l₃ * l₄ * l₅ * r₅ := by
      have ha : 4 * e₃ * r₃ < 2 * l₃ * r₅ :=
        calc 4 * e₃ * r₃ < 2 * l₃ * r₃ := Nat.mul_lt_mul_of_pos_right (by dsimp [l₃]; omega) hr₃p.pos
          _ < 2 * l₃ * r₅ := Nat.mul_lt_mul_of_pos_left hr₃₅ (by positivity)
      calc 4 * e₃ * r₃ * l₁ * l₂ * l₄ * l₅ < 2 * l₃ * r₅ * l₁ * l₂ * l₄ * l₅ :=
            Nat.mul_lt_mul_of_pos_right
              (Nat.mul_lt_mul_of_pos_right
                (Nat.mul_lt_mul_of_pos_right
                  (Nat.mul_lt_mul_of_pos_right ha (by dsimp [l₁]; omega))
                  (by dsimp [l₂]; omega))
                (by dsimp [l₄]; omega))
              (by dsimp [l₅]; omega)
        _ = 2 * l₁ * l₂ * l₃ * l₄ * l₅ * r₅ := by ring
    have ht4 : 4 * e₄ * r₄ * l₁ * l₂ * l₃ * l₅ < 2 * l₁ * l₂ * l₃ * l₄ * l₅ * r₅ := by
      have ha : 4 * e₄ * r₄ < 2 * l₄ * r₅ :=
        calc 4 * e₄ * r₄ < 2 * l₄ * r₄ := Nat.mul_lt_mul_of_pos_right (by dsimp [l₄]; omega) hr₄p.pos
          _ < 2 * l₄ * r₅ := Nat.mul_lt_mul_of_pos_left hr₄₅ (by positivity)
      calc 4 * e₄ * r₄ * l₁ * l₂ * l₃ * l₅ < 2 * l₄ * r₅ * l₁ * l₂ * l₃ * l₅ :=
            Nat.mul_lt_mul_of_pos_right
              (Nat.mul_lt_mul_of_pos_right
                (Nat.mul_lt_mul_of_pos_right
                  (Nat.mul_lt_mul_of_pos_right ha (by dsimp [l₁]; omega))
                  (by dsimp [l₂]; omega))
                (by dsimp [l₃]; omega))
              (by dsimp [l₅]; omega)
        _ = 2 * l₁ * l₂ * l₃ * l₄ * l₅ * r₅ := by ring
    have ht5 : 4 * e₅ * r₅ * l₁ * l₂ * l₃ * l₄ < 2 * l₁ * l₂ * l₃ * l₄ * l₅ * r₅ := by
      have ha : 4 * e₅ * r₅ < 2 * l₅ * r₅ :=
        Nat.mul_lt_mul_of_pos_right (by dsimp [l₅]; omega) hr₅p.pos
      calc 4 * e₅ * r₅ * l₁ * l₂ * l₃ * l₄ < 2 * l₅ * r₅ * l₁ * l₂ * l₃ * l₄ :=
            Nat.mul_lt_mul_of_pos_right
              (Nat.mul_lt_mul_of_pos_right
                (Nat.mul_lt_mul_of_pos_right
                  (Nat.mul_lt_mul_of_pos_right ha (by dsimp [l₁]; omega))
                  (by dsimp [l₂]; omega))
                (by dsimp [l₃]; omega))
              (by dsimp [l₄]; omega)
        _ = 2 * l₁ * l₂ * l₃ * l₄ * l₅ * r₅ := by ring
    calc L ≤ 4 * e₁ * (r₁ - 1) * l₂ * l₃ * l₄ * l₅ +
          4 * e₂ * (r₂ - 1) * l₁ * l₃ * l₄ * l₅ +
          4 * e₃ * (r₃ - 1) * l₁ * l₂ * l₄ * l₅ +
          4 * e₄ * (r₄ - 1) * l₁ * l₂ * l₃ * l₅ +
          4 * e₅ * (r₅ - 1) * l₁ * l₂ * l₃ * l₄ := Nat.sub_le _ _
      _ ≤ 4 * e₁ * r₁ * l₂ * l₃ * l₄ * l₅ +
          4 * e₂ * r₂ * l₁ * l₃ * l₄ * l₅ +
          4 * e₃ * r₃ * l₁ * l₂ * l₄ * l₅ +
          4 * e₄ * r₄ * l₁ * l₂ * l₃ * l₅ +
          4 * e₅ * r₅ * l₁ * l₂ * l₃ * l₄ := by omega
      _ < 2 * l₁ * l₂ * l₃ * l₄ * l₅ * r₅ +
          2 * l₁ * l₂ * l₃ * l₄ * l₅ * r₅ +
          2 * l₁ * l₂ * l₃ * l₄ * l₅ * r₅ +
          2 * l₁ * l₂ * l₃ * l₄ * l₅ * r₅ +
          2 * l₁ * l₂ * l₃ * l₄ * l₅ * r₅ := by omega
      _ = 10 * l₁ * l₂ * l₃ * l₄ * l₅ * r₅ := by ring
  have hr₅_sq_lt_p : r₅ ^ 2 < p := by
    have hrange : range 3 ⊆ range (2 * e₅ + 1) := Finset.range_mono (by omega : 3 ≤ 2 * e₅ + 1)
    have hsum3 : 1 + r₅ + r₅ ^ 2 ≤ sigma 1 (r₅ ^ (2 * e₅)) := by
      rw [sigma_one_apply_prime_pow hr₅p]
      calc 1 + r₅ + r₅ ^ 2 = ∑ j ∈ range 3, r₅ ^ j := by
            simp [Finset.sum_range_succ, Nat.add_assoc]
        _ ≤ ∑ j ∈ range (2 * e₅ + 1), r₅ ^ j := Finset.sum_le_sum_of_subset hrange
    rw [hσr₅] at hsum3
    omega
  have hr₁_pow_lt_p : r₁ ^ (2 * e₁) < p := by
    rw [← hσr₁]
    exact self_lt_sigma_of_one_lt (one_lt_pow₀ hr₁p.one_lt (by omega))
  by_cases hr₅_big : 10 * l₁ * l₂ * l₃ * l₄ * l₅ ≤ r₅
  · have : L < r₅ ^ 2 := by
      calc L < 10 * l₁ * l₂ * l₃ * l₄ * l₅ * r₅ := hL_lt_prod
        _ ≤ r₅ * r₅ := Nat.mul_le_mul_right r₅ hr₅_big
        _ = r₅ ^ 2 := by ring
    omega
  · have hr₅_lt : r₅ < 10 * l₁ * l₂ * l₃ * l₄ * l₅ := by omega
    have hL_lt_sq : L < (10 * l₁ * l₂ * l₃ * l₄ * l₅) ^ 2 := by
      have : 10 * l₁ * l₂ * l₃ * l₄ * l₅ * r₅ <
          10 * l₁ * l₂ * l₃ * l₄ * l₅ * (10 * l₁ * l₂ * l₃ * l₄ * l₅) :=
        Nat.mul_lt_mul_of_pos_left hr₅_lt (by positivity)
      calc L < 10 * l₁ * l₂ * l₃ * l₄ * l₅ * r₅ := hL_lt_prod
        _ < 10 * l₁ * l₂ * l₃ * l₄ * l₅ * (10 * l₁ * l₂ * l₃ * l₄ * l₅) := this
        _ = (10 * l₁ * l₂ * l₃ * l₄ * l₅) ^ 2 := by ring
    by_cases he₁_big : 19 ≤ e₁
    · have hl₂_lt : l₂ < l₁ := by dsimp [l₁, l₂]; omega
      have hl₃_lt : l₃ < l₁ := by dsimp [l₁, l₃]; omega
      have hl₄_lt : l₄ < l₁ := by dsimp [l₁, l₄]; omega
      have hl₅_lt : l₅ < l₁ := by dsimp [l₁, l₅]; omega
      have hL_lt_100 : L < 100 * l₁ ^ 10 := by
        have hpow : (10 * l₁ * l₂ * l₃ * l₄ * l₅) ^ 2 < 100 * l₁ ^ 10 := by
          have h1 : l₂ * l₃ * l₄ * l₅ < l₁ * l₁ * l₁ * l₁ := by gcongr
          calc (10 * l₁ * l₂ * l₃ * l₄ * l₅) ^ 2
              = 100 * (l₁ * (l₂ * l₃ * l₄ * l₅)) ^ 2 := by ring
            _ < 100 * (l₁ * (l₁ * l₁ * l₁ * l₁)) ^ 2 := by gcongr
            _ = 100 * l₁ ^ 10 := by ring
        omega
      have h100 := hundred_mul_odd_pow10_le_three_pow he₁_big
      have h3_le : 3 ^ (2 * e₁) ≤ r₁ ^ (2 * e₁) := Nat.pow_le_pow_left hr₁_ge3 (2 * e₁)
      change L < 100 * (2 * e₁ + 1) ^ 10 at hL_lt_100
      omega
    · have hl₂_le : l₂ ≤ l₁ - 2 := by dsimp [l₁, l₂]; omega
      have hl₃_le : l₃ ≤ l₁ - 4 := by dsimp [l₁, l₃]; omega
      have hl₄_le : l₄ ≤ l₁ - 6 := by dsimp [l₁, l₄]; omega
      have hl₅_le : l₅ ≤ l₁ - 8 := by dsimp [l₁, l₅]; omega
      rcases (by omega : e₁ = 6 ∨ e₁ = 7 ∨ e₁ = 8 ∨ e₁ = 9 ∨ e₁ = 10 ∨ e₁ = 11 ∨
          e₁ = 12 ∨ e₁ = 13 ∨ e₁ = 14 ∨ e₁ = 15 ∨ e₁ = 16 ∨ e₁ = 17 ∨ e₁ = 18) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · -- e₁ = 6, l₁ = 13, e₂ = 5 (l₂ = 11)
        have he₂_eq : e₂ = 5 := by omega
        have he₃_eq : e₃ = 3 := by
          have : e₃ ≠ 4 := by intro h4; rw [h4] at hl₃p; exact absurd hl₃p (by decide)
          omega
        have he₄_eq : e₄ = 2 := by omega
        have he₅_eq : e₅ = 1 := by omega
        subst he₂_eq he₃_eq he₄_eq he₅_eq
        change L < (10 * (2 * 6 + 1) * (2 * 5 + 1) * (2 * 3 + 1) * (2 * 2 + 1) * (2 * 1 + 1)) ^ 2 at hL_lt_sq
        norm_num at hL_lt_sq
        by_cases hr₁_ge11 : 11 ≤ r₁
        · have h11 : (11 : ℕ) ^ (2 * 6) = 3138428376721 := by norm_num
          have : 3138428376721 ≤ r₁ ^ (2 * 6) := h11 ▸ Nat.pow_le_pow_left hr₁_ge11 (2 * 6)
          omega
        · rcases (by omega : r₁ = 3 ∨ r₁ = 5 ∨ r₁ = 7 ∨ r₁ = 9) with rfl | rfl | rfl | rfl
          · rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
            norm_num [Finset.sum_range_succ] at hσr₁
            rw [← hσr₁] at hl₂_dvd
            norm_num at hl₂_dvd
          · rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
            norm_num [Finset.sum_range_succ] at hσr₁
            rw [← hσr₁] at hl₂_dvd
            norm_num at hl₂_dvd
          · rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
            norm_num [Finset.sum_range_succ] at hσr₁
            rw [← hσr₁] at hl₂_dvd
            norm_num at hl₂_dvd
          · exact absurd hr₁p (by decide)
      · exact absurd hl₁p (by decide)
      · -- e₁ = 8, l₁ = 17
        have hL_bound : L < 10770539422500 := by
          have hl₁v : l₁ = 17 := rfl
          have hmul : 10 * l₁ * l₂ * l₃ * l₄ * l₅ ≤ 3281850 := by
            calc 10 * l₁ * l₂ * l₃ * l₄ * l₅ = 10 * 17 * l₂ * l₃ * l₄ * l₅ := by rw [hl₁v]
              _ ≤ 10 * 17 * 15 * 13 * 11 * 9 := by gcongr <;> omega
              _ = 3281850 := by norm_num
          have hsq : (10 * l₁ * l₂ * l₃ * l₄ * l₅) ^ 2 ≤ 10770539422500 :=
            (Nat.pow_le_pow_left hmul 2).trans (by norm_num)
          omega
        by_cases hr₁_ge7 : 7 ≤ r₁
        · have h7 : (7 : ℕ) ^ (2 * 8) = 33232930569601 := by norm_num
          have : 33232930569601 ≤ r₁ ^ (2 * 8) := h7 ▸ Nat.pow_le_pow_left hr₁_ge7 (2 * 8)
          omega
        · rcases (by omega : r₁ = 3 ∨ r₁ = 5) with rfl | rfl
          · rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
            norm_num [Finset.sum_range_succ] at hσr₁
            rw [← hσr₁] at hp
            have hdiv : 1871 ∣ 64570081 := by norm_num
            have := hp.eq_one_or_self_of_dvd 1871 hdiv
            omega
          · rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
            norm_num [Finset.sum_range_succ] at hσr₁
            rw [← hσr₁] at hp
            have hdiv : 409 ∣ 190734863281 := by norm_num
            have := hp.eq_one_or_self_of_dvd 409 hdiv
            omega
      · -- e₁ = 9, l₁ = 19
        have hL_bound : L < 48002033722500 := by
          have hl₁v : l₁ = 19 := rfl
          have hmul : 10 * l₁ * l₂ * l₃ * l₄ * l₅ ≤ 6928350 := by
            calc 10 * l₁ * l₂ * l₃ * l₄ * l₅ = 10 * 19 * l₂ * l₃ * l₄ * l₅ := by rw [hl₁v]
              _ ≤ 10 * 19 * 17 * 15 * 13 * 11 := by gcongr <;> omega
              _ = 6928350 := by norm_num
          have hsq : (10 * l₁ * l₂ * l₃ * l₄ * l₅) ^ 2 ≤ 48002033722500 :=
            (Nat.pow_le_pow_left hmul 2).trans (by norm_num)
          omega
        by_cases hr₁_ge7 : 7 ≤ r₁
        · have h7 : (7 : ℕ) ^ (2 * 9) = 1628413597910449 := by norm_num
          have : 1628413597910449 ≤ r₁ ^ (2 * 9) := h7 ▸ Nat.pow_le_pow_left hr₁_ge7 (2 * 9)
          omega
        · rcases (by omega : r₁ = 3 ∨ r₁ = 5) with rfl | rfl
          · rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
            norm_num [Finset.sum_range_succ] at hσr₁
            rw [← hσr₁] at hp
            have hdiv : 1597 ∣ 581130733 := by norm_num
            have := hp.eq_one_or_self_of_dvd 1597 hdiv
            omega
          · rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
            norm_num [Finset.sum_range_succ] at hσr₁
            rw [← hσr₁] at hp
            have hdiv : 191 ∣ 4768371582031 := by norm_num
            have := hp.eq_one_or_self_of_dvd 191 hdiv
            omega
      · exact absurd hl₁p (by decide)
      · -- e₁ = 11, l₁ = 23
        have hL_bound : L < 547623181822500 := by
          have hl₁v : l₁ = 23 := rfl
          have hmul : 10 * l₁ * l₂ * l₃ * l₄ * l₅ ≤ 23401350 := by
            calc 10 * l₁ * l₂ * l₃ * l₄ * l₅ = 10 * 23 * l₂ * l₃ * l₄ * l₅ := by rw [hl₁v]
              _ ≤ 10 * 23 * 21 * 19 * 17 * 15 := by gcongr <;> omega
              _ = 23401350 := by norm_num
          have hsq : (10 * l₁ * l₂ * l₃ * l₄ * l₅) ^ 2 ≤ 547623181822500 :=
            (Nat.pow_le_pow_left hmul 2).trans (by norm_num)
          omega
        by_cases hr₁_ge5 : 5 ≤ r₁
        · have h5 : (5 : ℕ) ^ (2 * 11) = 2384185791015625 := by norm_num
          have : 2384185791015625 ≤ r₁ ^ (2 * 11) := h5 ▸ Nat.pow_le_pow_left hr₁_ge5 (2 * 11)
          omega
        · have hr₁_eq3 : r₁ = 3 := by omega
          subst hr₁_eq3
          rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
          norm_num [Finset.sum_range_succ] at hσr₁
          rw [← hσr₁] at hp
          have hdiv : 47 ∣ 47071589413 := by norm_num
          have := hp.eq_one_or_self_of_dvd 47 hdiv
          omega
      · exact absurd hl₁p (by decide)
      · exact absurd hl₁p (by decide)
      · -- e₁ = 14, l₁ = 29
        have hL_bound : L < 8939182482562500 := by
          have hl₁v : l₁ = 29 := rfl
          have hmul : 10 * l₁ * l₂ * l₃ * l₄ * l₅ ≤ 94547250 := by
            calc 10 * l₁ * l₂ * l₃ * l₄ * l₅ = 10 * 29 * l₂ * l₃ * l₄ * l₅ := by rw [hl₁v]
              _ ≤ 10 * 29 * 27 * 25 * 23 * 21 := by gcongr <;> omega
              _ = 94547250 := by norm_num
          have hsq : (10 * l₁ * l₂ * l₃ * l₄ * l₅) ^ 2 ≤ 8939182482562500 :=
            (Nat.pow_le_pow_left hmul 2).trans (by norm_num)
          omega
        by_cases hr₁_ge5 : 5 ≤ r₁
        · have h5 : (5 : ℕ) ^ (2 * 14) = 37252902984619140625 := by norm_num
          have : 37252902984619140625 ≤ r₁ ^ (2 * 14) := h5 ▸ Nat.pow_le_pow_left hr₁_ge5 (2 * 14)
          omega
        · have hr₁_eq3 : r₁ = 3 := by omega
          subst hr₁_eq3
          rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
          norm_num [Finset.sum_range_succ] at hσr₁
          rw [← hσr₁] at hp
          have hdiv : 59 ∣ 34315188682441 := by norm_num
          have := hp.eq_one_or_self_of_dvd 59 hdiv
          omega
      · -- e₁ = 15, l₁ = 31
        have hL_bound : L < 19479715115062500 := by
          have hl₁v : l₁ = 31 := rfl
          have hmul : 10 * l₁ * l₂ * l₃ * l₄ * l₅ ≤ 139569750 := by
            calc 10 * l₁ * l₂ * l₃ * l₄ * l₅ = 10 * 31 * l₂ * l₃ * l₄ * l₅ := by rw [hl₁v]
              _ ≤ 10 * 31 * 29 * 27 * 25 * 23 := by gcongr <;> omega
              _ = 139569750 := by norm_num
          have hsq : (10 * l₁ * l₂ * l₃ * l₄ * l₅) ^ 2 ≤ 19479715115062500 :=
            (Nat.pow_le_pow_left hmul 2).trans (by norm_num)
          omega
        by_cases hr₁_ge5 : 5 ≤ r₁
        · have h5 : (5 : ℕ) ^ (2 * 15) = 931322574615478515625 := by norm_num
          have : 931322574615478515625 ≤ r₁ ^ (2 * 15) := h5 ▸ Nat.pow_le_pow_left hr₁_ge5 (2 * 15)
          omega
        · have hr₁_eq3 : r₁ = 3 := by omega
          subst hr₁_eq3
          rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
          norm_num [Finset.sum_range_succ] at hσr₁
          rw [← hσr₁] at hp
          have hdiv : 683 ∣ 308836698141973 := by norm_num
          have := hp.eq_one_or_self_of_dvd 683 hdiv
          omega
      · exact absurd hl₁p (by decide)
      · exact absurd hl₁p (by decide)
      · -- e₁ = 18, l₁ = 37
        have hL_bound : L < 147600150412522500 := by
          have hl₁v : l₁ = 37 := rfl
          have hmul : 10 * l₁ * l₂ * l₃ * l₄ * l₅ ≤ 384187650 := by
            calc 10 * l₁ * l₂ * l₃ * l₄ * l₅ = 10 * 37 * l₂ * l₃ * l₄ * l₅ := by rw [hl₁v]
              _ ≤ 10 * 37 * 35 * 33 * 31 * 29 := by gcongr <;> omega
              _ = 384187650 := by norm_num
          have hsq : (10 * l₁ * l₂ * l₃ * l₄ * l₅) ^ 2 ≤ 147600150412522500 :=
            (Nat.pow_le_pow_left hmul 2).trans (by norm_num)
          omega
        have h3 : (3 : ℕ) ^ (2 * 18) = 150094635296999121 := by norm_num
        have : 150094635296999121 ≤ r₁ ^ (2 * 18) := h3 ▸ Nat.pow_le_pow_left hr₁_ge3 (2 * 18)
        omega

/-- Unconditionally, at any even prime-power component index `p ^ (2 * u)`,
at least six distinct cofactor primes return `p` with valuation `1`. -/
theorem even_index_six_le_S1_card {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    6 ≤ (s.primeFactors.filter (v · = 1)).card := by
  intro v
  let S₁ := s.primeFactors.filter (v · = 1)
  let l (r : ℕ) := 2 * s.factorization r + 1
  have hS1_ge5 : 5 ≤ S₁.card := even_index_five_le_S1_card hp hpo hs hu hσq hplus hσs
  change 5 ≤ S₁.card at hS1_ge5
  by_contra! hlt6
  change S₁.card < 6 at hlt6
  have hcard5 : S₁.card = 5 := by omega
  let f := S₁.orderEmbOfFin hcard5
  let r₁ := f ⟨0, by decide⟩
  let r₂ := f ⟨1, by decide⟩
  let r₃ := f ⟨2, by decide⟩
  let r₄ := f ⟨3, by decide⟩
  let r₅ := f ⟨4, by decide⟩
  have hr₁S : r₁ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard5 _
  have hr₂S : r₂ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard5 _
  have hr₃S : r₃ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard5 _
  have hr₄S : r₄ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard5 _
  have hr₅S : r₅ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard5 _
  have hr₁₂ : r₁ < r₂ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₂₃ : r₂ < r₃ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₃₄ : r₃ < r₄ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₄₅ : r₄ < r₅ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hS1_eq : S₁ = {r₁, r₂, r₃, r₄, r₅} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
    · rw [hcard5, Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (by omega)]
  obtain ⟨_, hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  obtain ⟨hdvd_pred, _⟩ := even_index_repunit_lengths_dvd_pred hp hpo hs hσq hplus hσs
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
  obtain ⟨hr₂p, _, he₂pos, hl₂p, hσr₂⟩ := extract r₂ hr₂S
  obtain ⟨hr₃p, _, he₃pos, hl₃p, hσr₃⟩ := extract r₃ hr₃S
  obtain ⟨hr₄p, _, he₄pos, hl₄p, hσr₄⟩ := extract r₄ hr₄S
  obtain ⟨hr₅p, _, he₅pos, hl₅p, hσr₅⟩ := extract r₅ hr₅S
  have he₄₅ : s.factorization r₅ < s.factorization r₄ :=
    exp_anti_of_sigma_eq hr₄p hr₅p hr₄₅ he₄pos hσr₄ hσr₅
  have he₃₄ : s.factorization r₄ < s.factorization r₃ :=
    exp_anti_of_sigma_eq hr₃p hr₄p hr₃₄ he₃pos hσr₃ hσr₄
  have he₂₃ : s.factorization r₃ < s.factorization r₂ :=
    exp_anti_of_sigma_eq hr₂p hr₃p hr₂₃ he₂pos hσr₂ hσr₃
  have he₁₂ : s.factorization r₂ < s.factorization r₁ :=
    exp_anti_of_sigma_eq hr₁p hr₂p hr₁₂ he₁pos hσr₁ hσr₂
  obtain ⟨hlt_L, hp_dvd_A⟩ :=
    even_index_P_L_lt_SumCoef_and_dvd hp hpo hs hu hσq hplus hσs
  have hle_p : p ≤ (∑ r ∈ S₁, 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t) -
      ∏ r ∈ S₁, l r :=
    Nat.le_of_dvd (Nat.sub_pos_of_lt hlt_L) hp_dvd_A
  have hL_eq : (∑ r ∈ S₁, 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t) -
      ∏ r ∈ S₁, l r =
      4 * s.factorization r₁ * (r₁ - 1) * l r₂ * l r₃ * l r₄ * l r₅ +
      4 * s.factorization r₂ * (r₂ - 1) * l r₁ * l r₃ * l r₄ * l r₅ +
      4 * s.factorization r₃ * (r₃ - 1) * l r₁ * l r₂ * l r₄ * l r₅ +
      4 * s.factorization r₄ * (r₄ - 1) * l r₁ * l r₂ * l r₃ * l r₅ +
      4 * s.factorization r₅ * (r₅ - 1) * l r₁ * l r₂ * l r₃ * l r₄ -
      l r₁ * l r₂ * l r₃ * l r₄ * l r₅ := by
    rw [hS1_eq]
    have h1n : r₁ ∉ ({r₂, r₃, r₄, r₅} : Finset ℕ) := by simp; omega
    have h2n : r₂ ∉ ({r₁, r₃, r₄, r₅} : Finset ℕ) := by simp; omega
    have h3n : r₃ ∉ ({r₁, r₂, r₄, r₅} : Finset ℕ) := by simp; omega
    have h4n : r₄ ∉ ({r₁, r₂, r₃, r₅} : Finset ℕ) := by simp; omega
    have h5n : r₅ ∉ ({r₁, r₂, r₃, r₄} : Finset ℕ) := by simp; omega
    have he1 : ({r₁, r₂, r₃, r₄, r₅} : Finset ℕ).erase r₁ = {r₂, r₃, r₄, r₅} :=
      Finset.erase_insert h1n
    have he2 : ({r₁, r₂, r₃, r₄, r₅} : Finset ℕ).erase r₂ = {r₁, r₃, r₄, r₅} := by
      rw [Finset.insert_comm r₁ r₂]; exact Finset.erase_insert h2n
    have he3 : ({r₁, r₂, r₃, r₄, r₅} : Finset ℕ).erase r₃ = {r₁, r₂, r₄, r₅} := by
      rw [Finset.insert_comm r₂ r₃, Finset.insert_comm r₁ r₃]
      exact Finset.erase_insert h3n
    have he4 : ({r₁, r₂, r₃, r₄, r₅} : Finset ℕ).erase r₄ = {r₁, r₂, r₃, r₅} := by
      rw [Finset.insert_comm r₃ r₄, Finset.insert_comm r₂ r₄, Finset.insert_comm r₁ r₄]
      exact Finset.erase_insert h4n
    have he5 : ({r₁, r₂, r₃, r₄, r₅} : Finset ℕ).erase r₅ = {r₁, r₂, r₃, r₄} := by
      rw [Finset.pair_comm r₄ r₅, Finset.insert_comm r₃ r₅, Finset.insert_comm r₂ r₅,
        Finset.insert_comm r₁ r₅]
      exact Finset.erase_insert h5n
    have hsum_eq : (∑ r ∈ ({r₁, r₂, r₃, r₄, r₅} : Finset ℕ),
          4 * s.factorization r * (r - 1) * ∏ t ∈ ({r₁, r₂, r₃, r₄, r₅} : Finset ℕ).erase r, l t) =
        4 * s.factorization r₁ * (r₁ - 1) * l r₂ * l r₃ * l r₄ * l r₅ +
        4 * s.factorization r₂ * (r₂ - 1) * l r₁ * l r₃ * l r₄ * l r₅ +
        4 * s.factorization r₃ * (r₃ - 1) * l r₁ * l r₂ * l r₄ * l r₅ +
        4 * s.factorization r₄ * (r₄ - 1) * l r₁ * l r₂ * l r₃ * l r₅ +
        4 * s.factorization r₅ * (r₅ - 1) * l r₁ * l r₂ * l r₃ * l r₄ := by
      rw [Finset.sum_insert h1n, Finset.sum_insert (by simp; omega),
        Finset.sum_insert (by simp; omega), Finset.sum_pair (by omega),
        he1, he2, he3, he4, he5,
        Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega), Finset.prod_pair (by omega),
        Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega), Finset.prod_pair (by omega),
        Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega), Finset.prod_pair (by omega),
        Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega), Finset.prod_pair (by omega),
        Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega), Finset.prod_pair (by omega)]
      ring
    have hprod_eq : (∏ r ∈ ({r₁, r₂, r₃, r₄, r₅} : Finset ℕ), l r) =
        l r₁ * l r₂ * l r₃ * l r₄ * l r₅ := by
      rw [Finset.prod_insert h1n, Finset.prod_insert (by simp; omega),
        Finset.prod_insert (by simp; omega), Finset.prod_pair (by omega)]
      ring
    rw [hsum_eq, hprod_eq]
  rw [hL_eq] at hle_p
  exact refute_card_five_arith hp hr₁p hr₁o hr₂p hr₃p hr₄p hr₅p he₅pos he₄₅ he₃₄ he₂₃ he₁₂
    hr₁₂ hr₂₃ hr₃₄ hr₄₅ hl₁p hl₂p hl₃p hl₄p hl₅p (hdvd_pred r₂ hr₂S) hσr₁ hσr₅ hle_p

/-- Every even prime-power component index `p ^ (2 * u)` forces at least six
simultaneous odd-prime-base repunit representations of `p`. -/
theorem even_index_forces_six_repunits {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    HasSixOddPrimeRepunits p := by
  let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
  let S₁ := s.primeFactors.filter (v · = 1)
  have hS1_ge6 : 6 ≤ S₁.card := even_index_six_le_S1_card hp hpo hs hu hσq hplus hσs
  let f := S₁.orderEmbOfFin (rfl : S₁.card = S₁.card)
  let r₁ := f ⟨0, by omega⟩
  let r₂ := f ⟨1, by omega⟩
  let r₃ := f ⟨2, by omega⟩
  let r₄ := f ⟨3, by omega⟩
  let r₅ := f ⟨4, by omega⟩
  let r₆ := f ⟨5, by omega⟩
  have hr₁S : r₁ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₂S : r₂ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₃S : r₃ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₄S : r₄ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₅S : r₅ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₆S : r₆ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₁₂ : r₁ < r₂ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₂₃ : r₂ < r₃ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₃₄ : r₃ < r₄ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₄₅ : r₄ < r₅ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₅₆ : r₅ < r₆ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  obtain ⟨_, hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  have extract : ∀ r ∈ S₁, r.Prime ∧ Odd r ∧ (2 * s.factorization r + 1).Prime ∧
      2 < 2 * s.factorization r + 1 ∧ geometricBlock r (2 * s.factorization r + 1) = p := by
    intro r hrS
    obtain ⟨hr, hvr⟩ := Finset.mem_filter.mp hrS
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hrs := Nat.dvd_of_mem_primeFactors hr
    have hro : Odd r := hs.of_dvd_nat hrs
    have hfac : 1 ≤ s.factorization r := (hrp.dvd_iff_one_le_factorization hs.pos.ne').mp hrs
    have hlp := (even_index_cofactor_component_order_dvd_pred hp hpo hs hσq hplus hσs hr).1
    have hgb : geometricBlock r (2 * s.factorization r + 1) = p := by
      dsimp only [geometricBlock]
      rw [← sigma_one_apply_prime_pow hrp]
      have H := (hparts r hr).2
      dsimp only at H
      change sigma 1 (r ^ (2 * s.factorization r)) = p ^ v r at H
      rwa [hvr, pow_one] at H
    exact ⟨hrp, hro, hlp, by omega, hgb⟩
  obtain ⟨hr₁p, hr₁o, hl₁p, hl₁_gt2, hgr₁⟩ := extract r₁ hr₁S
  obtain ⟨hr₂p, hr₂o, hl₂p, hl₂_gt2, hgr₂⟩ := extract r₂ hr₂S
  obtain ⟨hr₃p, hr₃o, hl₃p, hl₃_gt2, hgr₃⟩ := extract r₃ hr₃S
  obtain ⟨hr₄p, hr₄o, hl₄p, hl₄_gt2, hgr₄⟩ := extract r₄ hr₄S
  obtain ⟨hr₅p, hr₅o, hl₅p, hl₅_gt2, hgr₅⟩ := extract r₅ hr₅S
  obtain ⟨hr₆p, hr₆o, hl₆p, hl₆_gt2, hgr₆⟩ := extract r₆ hr₆S
  exact ⟨r₁, r₂, r₃, r₄, r₅, r₆,
    2 * s.factorization r₁ + 1, 2 * s.factorization r₂ + 1, 2 * s.factorization r₃ + 1,
    2 * s.factorization r₄ + 1, 2 * s.factorization r₅ + 1, 2 * s.factorization r₆ + 1,
    hr₁p, hr₁o, hr₂p, hr₂o, hr₃p, hr₃o, hr₄p, hr₄o, hr₅p, hr₅o, hr₆p, hr₆o,
    by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega,
    by omega, by omega, by omega,
    by omega, by omega,
    by omega,
    hl₁p, hl₁_gt2, hl₂p, hl₂_gt2, hl₃p, hl₃_gt2, hl₄p, hl₄_gt2, hl₅p, hl₅_gt2, hl₆p, hl₆_gt2,
    hgr₁, hgr₂, hgr₃, hgr₄, hgr₅, hgr₆⟩

private lemma two_mul_add_one_lt_three_pow' {e : ℕ} (he : 1 ≤ e) :
    2 * e + 1 < 3 ^ (2 * e) := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hpos : 1 ≤ 3 ^ (2 * k) := Nat.one_le_pow _ _ (by decide)
    calc 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
      _ < 3 ^ (2 * k) + 2 := by omega
      _ < 9 * 3 ^ (2 * k) := by omega
      _ = 3 ^ (2 * (k + 1)) := by ring

private lemma even_index_S1_ssubset_primeFactors' {q p s u : ℕ}
    (hp : p.Prime) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    s.primeFactors.filter (v · = 1) ⊂ s.primeFactors := by
  intro v
  let S₁ := s.primeFactors.filter (v · = 1)
  have hS1_ne_full : S₁ ≠ s.primeFactors := by
    intro h_eq
    obtain ⟨hsum, _⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
    change ∑ r ∈ s.primeFactors, v r = 2 * u at hsum
    have h2u_eq : 2 * u = S₁.card := by
      rw [← hsum, ← h_eq]
      calc ∑ r ∈ S₁, v r = ∑ _r ∈ S₁, 1 :=
            Finset.sum_congr rfl fun r hr => (Finset.mem_filter.mp hr).2
        _ = S₁.card := by simp
    have hprod_le_u1 : ∏ r ∈ S₁, r ≤ u + 1 :=
      Nat.le_of_dvd (by omega) (even_index_S1_exact_mod_sq hp hs hσq hplus hσs).2
    have hpow3_le : 3 ^ S₁.card ≤ ∏ r ∈ S₁, r := by
      calc 3 ^ S₁.card = ∏ _r ∈ S₁, 3 := by simp
        _ ≤ ∏ r ∈ S₁, r := Finset.prod_le_prod fun r hrS => by
            have hr := (Finset.mem_filter.mp hrS).1
            have hrp := Nat.prime_of_mem_primeFactors hr
            have hro : Odd r := hs.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr)
            have := hrp.two_le; have := Nat.odd_iff.mp hro; omega
    have hlt := two_mul_add_one_lt_three_pow' hu
    rw [h2u_eq] at hlt
    omega
  exact lt_of_le_of_ne (Finset.filter_subset _ _) hS1_ne_full

/-- Unconditional strengthening at any even prime-power component index `i = p ^ (2 * u)`:
`p` has at least six simultaneous odd-prime-base repunit representations and `N` has
at least 9 distinct prime factors. -/
theorem even_prime_power_component_forces_six_repunits_and_nine_primes {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    HasSixOddPrimeRepunits p ∧ 9 ≤ N.primeFactors.card := by
  obtain ⟨ha1, hσ⟩ := even_prime_power_index_eq_selected_sigma hN ho hq ha hform hqb hl hr hp hu hi
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b _)
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h4 : 4 ∣ 2 * b := hr ▸ hi ▸ (pow_dvd_pow 2 (by omega : 2 ≤ 2 * u)).trans (dvd_mul_left _ _)
    have := hbo.not_two_dvd_nat
    omega
  have hpo := hp.odd_of_ne_two hp2
  obtain ⟨m, _, _, hqm, rfl⟩ :=
    euler_form_of_odd_component_index hN ho hq ha hform hqb hl hr (hi ▸ hpo.pow)
  have hmo := ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _)
  rw [ha1, pow_one] at hform hl hr
  rw [hi] at hl hr
  obtain ⟨s, hso, hcop, hms, _, hplus, hσs⟩ := even_prime_power_cofactor_split hq hp hmo hpo hu hl hr
  have hsix := even_index_forces_six_repunits hp hpo hso hu hσ hplus hσs
  have hS1_ge6 := even_index_six_le_S1_card hp hpo hso hu hσ hplus hσs
  have hS1_ssub := even_index_S1_ssubset_primeFactors' hp hso hu hσ hplus hσs
  have hs_ge7 : 7 ≤ s.primeFactors.card := by
    have := Finset.card_lt_card hS1_ssub
    omega
  have hn := prime_count_of_even_index_split hq hp hmo hso hu hqm hcop hform hms
  exact ⟨hsix, by omega⟩

/-- At any even prime-power component index `i = p ^ (2 * u)`, `6 ≤ S₁.card` combined with
`∏ r ∈ S₁, r ∣ u + 1` and the repunit representations forces `255254 ≤ u`, `510508 ≤ 2 * u`,
`33232930569601 ≤ p`, and `10 ^ 6636604 < p ^ (2 * u)`. -/
theorem even_index_exponent_ge_510508 {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    255254 ≤ u ∧ 510508 ≤ 2 * u ∧ 33232930569601 ≤ p ∧ 10 ^ 6636604 < p ^ (2 * u) := by
  let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
  let S₁ := s.primeFactors.filter (v · = 1)
  have hS1_ge6 : 6 ≤ S₁.card := even_index_six_le_S1_card hp hpo hs hu hσq hplus hσs
  let f := S₁.orderEmbOfFin (rfl : S₁.card = S₁.card)
  let r₁ := f ⟨0, by omega⟩
  let r₂ := f ⟨1, by omega⟩
  let r₃ := f ⟨2, by omega⟩
  let r₄ := f ⟨3, by omega⟩
  let r₅ := f ⟨4, by omega⟩
  let r₆ := f ⟨5, by omega⟩
  have hr₁S : r₁ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₂S : r₂ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₃S : r₃ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₄S : r₄ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₅S : r₅ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₆S : r₆ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₁₂ : r₁ < r₂ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₂₃ : r₂ < r₃ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₃₄ : r₃ < r₄ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₄₅ : r₄ < r₅ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₅₆ : r₅ < r₆ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
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
  obtain ⟨hr₂p, hr₂o, he₂pos, _, hσr₂⟩ := extract r₂ hr₂S
  obtain ⟨hr₃p, hr₃o, he₃pos, hl₃p, hσr₃⟩ := extract r₃ hr₃S
  obtain ⟨hr₄p, hr₄o, he₄pos, _, hσr₄⟩ := extract r₄ hr₄S
  obtain ⟨hr₅p, hr₅o, he₅pos, _, hσr₅⟩ := extract r₅ hr₅S
  obtain ⟨hr₆p, hr₆o, he₆pos, _, hσr₆⟩ := extract r₆ hr₆S
  have hr₁_mod : r₁ % 2 = 1 := Nat.odd_iff.mp hr₁o
  have hr₁_ge3 : 3 ≤ r₁ := by have := hr₁p.two_le; omega
  have hr₂_ge5 : 5 ≤ r₂ := by have := Nat.odd_iff.mp hr₂o; omega
  have hr₃_ge7 : 7 ≤ r₃ := by have := Nat.odd_iff.mp hr₃o; omega
  have hr₄_ge11 : 11 ≤ r₄ := by
    have := Nat.odd_iff.mp hr₄o
    have h9 : r₄ ≠ 9 := by intro h9; rw [h9] at hr₄p; exact absurd hr₄p (by decide)
    omega
  have hr₅_ge13 : 13 ≤ r₅ := by have := Nat.odd_iff.mp hr₅o; omega
  have hr₆_ge17 : 17 ≤ r₆ := by
    have := Nat.odd_iff.mp hr₆o
    have h15 : r₆ ≠ 15 := by intro h15; rw [h15] at hr₆p; exact absurd hr₆p (by decide)
    omega
  have hprod_dvd : (∏ r ∈ S₁, r) ∣ u + 1 :=
    (even_index_S1_exact_mod_sq hp hs hσq hplus hσs).2
  have hprod_le : ∏ r ∈ S₁, r ≤ u + 1 := Nat.le_of_dvd (by omega) hprod_dvd
  have hsub6 : ({r₁, r₂, r₃, r₄, r₅, r₆} : Finset ℕ) ⊆ S₁ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hprod6_dvd : (∏ r ∈ ({r₁, r₂, r₃, r₄, r₅, r₆} : Finset ℕ), r) ∣ ∏ r ∈ S₁, r :=
    Finset.prod_dvd_prod_of_subset _ _ id hsub6
  have hprod6_eq : (∏ r ∈ ({r₁, r₂, r₃, r₄, r₅, r₆} : Finset ℕ), r) =
      r₁ * r₂ * r₃ * r₄ * r₅ * r₆ := by
    rw [Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
      Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
      Finset.prod_pair (by omega)]
    ring
  have hprod6_le : r₁ * r₂ * r₃ * r₄ * r₅ * r₆ ≤ ∏ r ∈ S₁, r := by
    rw [← hprod6_eq]
    exact Nat.le_of_dvd (Finset.prod_pos fun r hr =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1).pos) hprod6_dvd
  have h255255 : 255255 ≤ r₁ * r₂ * r₃ * r₄ * r₅ * r₆ := by
    calc 255255 = 3 * 5 * 7 * 11 * 13 * 17 := by norm_num
      _ ≤ r₁ * r₂ * r₃ * r₄ * r₅ * r₆ := by gcongr
  have hu_ge : 255254 ≤ u := by omega
  have hp_ge : 33232930569601 ≤ p := by
    have he₅₆ : s.factorization r₆ < s.factorization r₅ :=
      exp_anti_of_sigma_eq hr₅p hr₆p hr₅₆ he₅pos hσr₅ hσr₆
    have he₄₅ : s.factorization r₅ < s.factorization r₄ :=
      exp_anti_of_sigma_eq hr₄p hr₅p hr₄₅ he₄pos hσr₄ hσr₅
    have he₃₄ : s.factorization r₄ < s.factorization r₃ :=
      exp_anti_of_sigma_eq hr₃p hr₄p hr₃₄ he₃pos hσr₃ hσr₄
    have he₂₃ : s.factorization r₃ < s.factorization r₂ :=
      exp_anti_of_sigma_eq hr₂p hr₃p hr₂₃ he₂pos hσr₂ hσr₃
    have he₁₂ : s.factorization r₂ < s.factorization r₁ :=
      exp_anti_of_sigma_eq hr₁p hr₂p hr₁₂ he₁pos hσr₁ hσr₂
    have he₁_ge8 : 8 ≤ s.factorization r₁ := by
      have hnot9 : 2 * s.factorization r₃ + 1 ≠ 9 := by
        intro h9; rw [h9] at hl₃p; exact absurd hl₃p (by decide)
      have hnot15 : 2 * s.factorization r₁ + 1 ≠ 15 := by
        intro h15; rw [h15] at hl₁p; exact absurd hl₁p (by decide)
      omega
    have hpow_lt_p : r₁ ^ (2 * s.factorization r₁) < p := by
      rw [← hσr₁]
      exact self_lt_sigma_of_one_lt (one_lt_pow₀ hr₁p.one_lt (by omega))
    by_cases he₁_ge16 : 16 ≤ s.factorization r₁
    · have h3_32 : (3 : ℕ) ^ 32 ≤ r₁ ^ (2 * s.factorization r₁) :=
        (Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 32 ≤ 2 * s.factorization r₁)).trans
          (Nat.pow_le_pow_left hr₁_ge3 (2 * s.factorization r₁))
      have hval : (3 : ℕ) ^ 32 = 1853020188851841 := by norm_num
      omega
    · have hcases : s.factorization r₁ = 8 ∨ s.factorization r₁ = 9 ∨
          s.factorization r₁ = 10 ∨ s.factorization r₁ = 11 ∨ s.factorization r₁ = 12 ∨
          s.factorization r₁ = 13 ∨ s.factorization r₁ = 14 ∨ s.factorization r₁ = 15 := by omega
      rcases hcases with he1 | he1 | he1 | he1 | he1 | he1 | he1 | he1
      · -- e₁ = 8
        by_cases hr₁_ge7 : 7 ≤ r₁
        · have h7 : (7 : ℕ) ^ 16 ≤ r₁ ^ (2 * s.factorization r₁) := by
            rw [he1]; exact Nat.pow_le_pow_left hr₁_ge7 16
          have hval : (7 : ℕ) ^ 16 = 33232930569601 := by norm_num
          omega
        · have hr₁_cases : r₁ = 3 ∨ r₁ = 5 := by have := Nat.odd_iff.mp hr₁o; omega
          rcases hr₁_cases with hr1 | hr1
          · have hp_val : p = 64570081 := by
              rw [← hσr₁, he1, hr1, show 2 * 8 = 16 by rfl,
                sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
              norm_num [Finset.sum_range_succ]
            rw [hp_val] at hp
            have hdiv : 1871 ∣ 64570081 := by norm_num
            have := hp.eq_one_or_self_of_dvd 1871 hdiv
            omega
          · have hp_val : p = 190734863281 := by
              rw [← hσr₁, he1, hr1, show 2 * 8 = 16 by rfl,
                sigma_one_apply_prime_pow (by decide : Nat.Prime 5)]
              norm_num [Finset.sum_range_succ]
            rw [hp_val] at hp
            have hdiv : 409 ∣ 190734863281 := by norm_num
            have := hp.eq_one_or_self_of_dvd 409 hdiv
            omega
      · -- e₁ = 9
        by_cases hr₁_ge7 : 7 ≤ r₁
        · have h7 : (7 : ℕ) ^ 18 ≤ r₁ ^ (2 * s.factorization r₁) := by
            rw [he1]; exact Nat.pow_le_pow_left hr₁_ge7 18
          have hbig : 33232930569601 < (7 : ℕ) ^ 18 := by norm_num
          omega
        · have hr₁_cases : r₁ = 3 ∨ r₁ = 5 := by have := Nat.odd_iff.mp hr₁o; omega
          rcases hr₁_cases with hr1 | hr1
          · have hp_val : p = 581130733 := by
              rw [← hσr₁, he1, hr1, show 2 * 9 = 18 by rfl,
                sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
              norm_num [Finset.sum_range_succ]
            rw [hp_val] at hp
            have hdiv : 1597 ∣ 581130733 := by norm_num
            have := hp.eq_one_or_self_of_dvd 1597 hdiv
            omega
          · have hp_val : p = 4768371582031 := by
              rw [← hσr₁, he1, hr1, show 2 * 9 = 18 by rfl,
                sigma_one_apply_prime_pow (by decide : Nat.Prime 5)]
              norm_num [Finset.sum_range_succ]
            rw [hp_val] at hp
            have hdiv : 191 ∣ 4768371582031 := by norm_num
            have := hp.eq_one_or_self_of_dvd 191 hdiv
            omega
      · rw [he1] at hl₁p
        exact absurd hl₁p (by decide)
      · -- e₁ = 11
        by_cases hr₁_ge5 : 5 ≤ r₁
        · have h5 : (5 : ℕ) ^ 22 ≤ r₁ ^ (2 * s.factorization r₁) := by
            rw [he1]; exact Nat.pow_le_pow_left hr₁_ge5 22
          have hbig : 33232930569601 < (5 : ℕ) ^ 22 := by norm_num
          omega
        · have hr1 : r₁ = 3 := by omega
          have hp_val : p = 47071589413 := by
            rw [← hσr₁, he1, hr1, show 2 * 11 = 22 by rfl,
              sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
            norm_num [Finset.sum_range_succ]
          rw [hp_val] at hp
          have hdiv : 47 ∣ 47071589413 := by norm_num
          have := hp.eq_one_or_self_of_dvd 47 hdiv
          omega
      · rw [he1] at hl₁p
        exact absurd hl₁p (by decide)
      · rw [he1] at hl₁p
        exact absurd hl₁p (by decide)
      · -- e₁ = 14
        by_cases hr₁_ge5 : 5 ≤ r₁
        · have h5 : (5 : ℕ) ^ 28 ≤ r₁ ^ (2 * s.factorization r₁) := by
            rw [he1]; exact Nat.pow_le_pow_left hr₁_ge5 28
          have hbig : 33232930569601 < (5 : ℕ) ^ 28 := by norm_num
          omega
        · have hr1 : r₁ = 3 := by omega
          have hp_val : p = 34315188682441 := by
            rw [← hσr₁, he1, hr1, show 2 * 14 = 28 by rfl,
              sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
            norm_num [Finset.sum_range_succ]
          rw [hp_val] at hp
          have hdiv : 59 ∣ 34315188682441 := by norm_num
          have := hp.eq_one_or_self_of_dvd 59 hdiv
          omega
      · -- e₁ = 15
        by_cases hr₁_ge5 : 5 ≤ r₁
        · have h5 : (5 : ℕ) ^ 30 ≤ r₁ ^ (2 * s.factorization r₁) := by
            rw [he1]; exact Nat.pow_le_pow_left hr₁_ge5 30
          have hbig : 33232930569601 < (5 : ℕ) ^ 30 := by norm_num
          omega
        · have hr1 : r₁ = 3 := by omega
          have hp_val : p = 308836698141973 := by
            rw [← hσr₁, he1, hr1, show 2 * 15 = 30 by rfl,
              sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
            norm_num [Finset.sum_range_succ]
          rw [hp_val] at hp
          have hdiv : 683 ∣ 308836698141973 := by norm_num
          have := hp.eq_one_or_self_of_dvd 683 hdiv
          omega
  have hp_gt13 : 10 ^ 13 < p := lt_of_lt_of_le (by norm_num : 10 ^ 13 < 33232930569601) hp_ge
  have hpow_gt : 10 ^ 6636604 < p ^ (2 * u) := by
    obtain ⟨B, hB_eq, hB_lt⟩ : ∃ B : ℕ, B = 10 ^ 13 ∧ B < p := ⟨10 ^ 13, rfl, hp_gt13⟩
    calc 10 ^ 6636604 = B ^ 510508 := by
          rw [hB_eq, show 6636604 = 13 * 510508 by norm_num, pow_mul]
      _ < p ^ 510508 := pow_lt_pow_left₀ hB_lt (Nat.zero_le B) (by decide : 510508 ≠ 0)
      _ ≤ p ^ (2 * u) := pow_le_pow_right₀ hp.one_le (by omega)
  exact ⟨hu_ge, by omega, hp_ge, hpow_gt⟩

/-- Every prime-power component index `i = p ^ j` of an odd perfect number satisfies
`36207 ≤ j`, `10 ^ 17240 < i`, `10 ^ 17240 < N`, and
`510508 ≤ j ∧ 10 ^ 6636604 < i ∧ 10 ^ 6636604 < N` when `j` is even. -/
theorem component_prime_power_index_exponent_ge_36207 {N q a b i p j : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b)
    (hl : sigma 1 b = q ^ a * i) (hr : sigma 1 (q ^ a) * i = 2 * b)
    (hp : p.Prime) (hj : 0 < j) (hi : i = p ^ j) :
    36207 ≤ j ∧ 10 ^ 17240 < i ∧ 10 ^ 17240 < N ∧
      (Even j → 510508 ≤ j ∧ 10 ^ 6636604 < i ∧ 10 ^ 6636604 < N) := by
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b _)
  have hqo := ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_left (dvd_pow_self q ha.ne') b)
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
  rcases Nat.even_or_odd j with ⟨u, hu'⟩ | hj_odd
  · have hj2 : j = 2 * u := by omega
    have hu : 0 < u := by omega
    have hi_even : i = p ^ (2 * u) := hj2 ▸ hi
    have hp2 : p ≠ 2 := hp_ne_two (by omega)
    have hpo := hp.odd_of_ne_two hp2
    obtain ⟨ha1, hσq⟩ :=
      even_prime_power_index_eq_selected_sigma hN ho hq ha hform hqb hl hr hp hu hi_even
    obtain ⟨m, _, _, _, rfl⟩ :=
      euler_form_of_odd_component_index hN ho hq ha hform hqb hl hr (hi_even ▸ hpo.pow)
    have hmo := ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _)
    rw [ha1, pow_one] at hform hl hr
    rw [hi_even] at hl hr
    obtain ⟨s, hs, _, _, _, hplus, hσs⟩ := even_prime_power_cofactor_split hq hp hmo hpo hu hl hr
    obtain ⟨_, h2u_ge, _, hpow_gt⟩ :=
      even_index_exponent_ge_510508 hp hpo hs hu hσq hplus hσs
    have hi_gt : 10 ^ 6636604 < i := by
      rw [hi_even]
      exact hpow_gt
    have hi_gt17240 : 10 ^ 17240 < i :=
      calc 10 ^ 17240 < 10 ^ 6636604 :=
            pow_lt_pow_right₀ (by decide : 1 < 10) (by decide : 17240 < 6636604)
        _ < i := hi_gt
    exact ⟨by omega, hi_gt17240, hi_gt17240.trans hi_lt_N,
      fun _ => ⟨by omega, hi_gt, hi_gt.trans hi_lt_N⟩⟩
  · have hj_ge_36207 : 36207 ≤ j := by
      by_contra! hlt
      exact IndexObstruction.component_index_ne_odd_prime_power_below_36207
        hN ho hq ha hform hqb hl hr hp hj_odd hlt hi
    have hp2 : p ≠ 2 := hp_ne_two (by omega)
    have hp3 : 3 ≤ p := by have := hp.two_le; have := hp.eq_two_or_odd'; omega
    have h3_21 : 10 ^ 10 < 3 ^ 21 := by norm_num
    have hi_gt : 10 ^ 17240 < i := by
      rw [hi]
      calc 10 ^ 17240 = (10 ^ 10) ^ 1724 := by rw [show 17240 = 10 * 1724 by norm_num, pow_mul]
        _ < (3 ^ 21) ^ 1724 := pow_lt_pow_left₀ h3_21 (by positivity) (by decide : 1724 ≠ 0)
        _ = 3 ^ 36204 := by rw [show 36204 = 21 * 1724 by norm_num, pow_mul]
        _ ≤ 3 ^ j := pow_le_pow_right₀ (by decide : 1 ≤ 3) (by omega : 36204 ≤ j)
        _ ≤ p ^ j := Nat.pow_le_pow_left hp3 j
    exact ⟨hj_ge_36207, hi_gt, hi_gt.trans hi_lt_N,
      fun heven => False.elim ((Nat.not_even_iff_odd.mpr hj_odd) heven)⟩

end OddPerfect
