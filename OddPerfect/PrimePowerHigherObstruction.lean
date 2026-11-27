module

public import OddPerfect.PrimePowerExponent2308
public import OddPerfect.EvenIndexSubexponential
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

/-- The same integer has prime-length repunit representations in five
distinct odd prime bases. -/
@[expose] def HasFiveOddPrimeRepunits (z : ℕ) : Prop :=
  ∃ r₁ r₂ r₃ r₄ r₅ l₁ l₂ l₃ l₄ l₅ : ℕ,
    r₁.Prime ∧ Odd r₁ ∧ r₂.Prime ∧ Odd r₂ ∧ r₃.Prime ∧ Odd r₃ ∧ r₄.Prime ∧ Odd r₄ ∧ r₅.Prime ∧ Odd r₅ ∧
    r₁ ≠ r₂ ∧ r₁ ≠ r₃ ∧ r₁ ≠ r₄ ∧ r₁ ≠ r₅ ∧
    r₂ ≠ r₃ ∧ r₂ ≠ r₄ ∧ r₂ ≠ r₅ ∧
    r₃ ≠ r₄ ∧ r₃ ≠ r₅ ∧ r₄ ≠ r₅ ∧
    l₁.Prime ∧ 2 < l₁ ∧ l₂.Prime ∧ 2 < l₂ ∧ l₃.Prime ∧ 2 < l₃ ∧ l₄.Prime ∧ 2 < l₄ ∧ l₅.Prime ∧ 2 < l₅ ∧
    geometricBlock r₁ l₁ = z ∧ geometricBlock r₂ l₂ = z ∧
    geometricBlock r₃ l₃ = z ∧ geometricBlock r₄ l₄ = z ∧ geometricBlock r₅ l₅ = z

private lemma two_mul_prod_one_add_quad {R : Type*} [CommRing R] (x : R) (hx : x ^ 3 = 0)
    (A : Finset ℕ) (a b : ℕ → R) :
    2 * (∏ r ∈ A, (1 + a r * x + b r * x ^ 2)) =
      2 + 2 * (∑ r ∈ A, a r) * x +
        ((∑ r ∈ A, a r) ^ 2 - ∑ r ∈ A, (a r) ^ 2 + 2 * ∑ r ∈ A, b r) * x ^ 2 := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert r A hr ih =>
    rw [Finset.prod_insert hr, Finset.sum_insert hr, Finset.sum_insert hr, Finset.sum_insert hr]
    set P := ∏ t ∈ A, (1 + a t * x + b t * x ^ 2)
    set S := ∑ t ∈ A, a t
    set Q := ∑ t ∈ A, (a t) ^ 2
    set B := ∑ t ∈ A, b t
    have hmul : 2 * ((1 + a r * x + b r * x ^ 2) * P) = (1 + a r * x + b r * x ^ 2) * (2 * P) := by ring
    rw [hmul, ih]
    linear_combination
      (a r * (S ^ 2 - Q + 2 * B) + 2 * b r * S + b r * (S ^ 2 - Q + 2 * B) * x) * hx

private lemma two_mul_choose_two_add (n : ℕ) : 2 * Nat.choose n 2 + n = n ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    linarith

private lemma modEq_of_mul_p_sq_eq {p x y : ℕ} (hp : 0 < p)
    (h : ((x : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) ^ 2) =
      ((y : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) ^ 2)) :
    x ≡ y [MOD p] := by
  rcases le_total x y with hxy | hyx
  · have hzero : (((y - x) * p ^ 2 : ℕ) : ZMod (p ^ 3)) = 0 := by
      have hsub : x + (y - x) = y := Nat.add_sub_cancel' hxy
      have hcast := congrArg (fun n : ℕ => (n : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) ^ 2) hsub
      push_cast at hcast ⊢
      calc ((y - x : ℕ) : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) ^ 2
          = ((x : ZMod (p ^ 3)) + ((y - x : ℕ) : ZMod (p ^ 3))) * (p : ZMod (p ^ 3)) ^ 2 -
              (x : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) ^ 2 := by ring
        _ = (y : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) ^ 2 -
              (y : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) ^ 2 := by rw [hcast, h]
        _ = 0 := sub_self _
    have hdvd : p ^ 3 ∣ (y - x) * p ^ 2 := (ZMod.natCast_eq_zero_iff _ _).mp hzero
    rw [show p ^ 3 = p * p ^ 2 by ring] at hdvd
    have hp2 : 0 < p ^ 2 := pow_pos hp 2
    exact (Nat.modEq_iff_dvd' hxy).mpr (Nat.dvd_of_mul_dvd_mul_right hp2 hdvd)
  · have hzero : (((x - y) * p ^ 2 : ℕ) : ZMod (p ^ 3)) = 0 := by
      have hsub : y + (x - y) = x := Nat.add_sub_cancel' hyx
      have hcast := congrArg (fun n : ℕ => (n : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) ^ 2) hsub
      push_cast at hcast ⊢
      calc ((x - y : ℕ) : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) ^ 2
          = ((y : ZMod (p ^ 3)) + ((x - y : ℕ) : ZMod (p ^ 3))) * (p : ZMod (p ^ 3)) ^ 2 -
              (y : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) ^ 2 := by ring
        _ = (x : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) ^ 2 -
              (x : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) ^ 2 := by rw [hcast, h]
        _ = 0 := sub_self _
    have hdvd : p ^ 3 ∣ (x - y) * p ^ 2 := (ZMod.natCast_eq_zero_iff _ _).mp hzero
    rw [show p ^ 3 = p * p ^ 2 by ring] at hdvd
    have hp2 : 0 < p ^ 2 := pow_pos hp 2
    exact ((Nat.modEq_iff_dvd' hyx).mpr (Nat.dvd_of_mul_dvd_mul_right hp2 hdvd)).symm

private lemma modEq_mul_p_cast_sq {p x y : ℕ} (h : x ≡ y [MOD p]) :
    (x : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = (y : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) := by
  have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hx : (x : ZMod (p ^ 2)) * p = ((x % p : ℕ) : ZMod (p ^ 2)) * p := by
    conv_lhs => rw [← Nat.div_add_mod x p]
    push_cast
    linear_combination (x / p : ZMod (p ^ 2)) * hp2
  have hy : (y : ZMod (p ^ 2)) * p = ((y % p : ℕ) : ZMod (p ^ 2)) * p := by
    conv_lhs => rw [← Nat.div_add_mod y p]
    push_cast
    linear_combination (y / p : ZMod (p ^ 2)) * hp2
  rw [hx, hy, h]

private lemma even_index_A_pos_and_quotient_modEq {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    let S₁ := s.primeFactors.filter (v · = 1)
    let l (r : ℕ) := 2 * s.factorization r + 1
    let P_L := ∏ r ∈ S₁, l r
    let SumCoef := ∑ r ∈ S₁, 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t
    let A := SumCoef - P_L
    P_L < SumCoef ∧ p ∣ A ∧
      4 * (A / p) ≡ 3 * P_L + ∑ r ∈ S₁, 8 * s.factorization r * (r - 1) ^ 2 * ∏ t ∈ S₁.erase r, l t [MOD p] := by
  intro v S₁ l P_L SumCoef A
  let R := ZMod (p ^ 3)
  let T := (s ^ 2).divisors.card
  let Q_out := ∏ t ∈ s.primeFactors \ S₁, l t
  let m (r : ℕ) := 2 * s.factorization r * (∏ t ∈ s.primeFactors.erase r, l t)
  have hT_prod : T = ∏ r ∈ s.primeFactors, l r := by
    dsimp [T, l]
    rw [Nat.card_divisors (pow_ne_zero 2 hs.pos.ne'), Nat.primeFactors_pow s (by decide : 2 ≠ 0)]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hT_cop : p.Coprime T := by
    rw [hT_prod]
    apply Nat.coprime_prod_right_iff.mpr
    intro r hr
    exact hp.coprime_iff_not_dvd.mpr
      (even_index_cofactor_component_order_dvd_pred hp hpo hs hσq hplus hσs hr).2.1
  have hS1_ge4 : 4 ≤ S₁.card := even_index_four_le_S1_card hp hpo hs hu hσq hplus hσs
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
  have hSum_eq : SumCoef = P_L + A := by dsimp [A]; omega
  have hQ_eq : ∀ r ∈ S₁,
      (∏ t ∈ s.primeFactors.erase r, l t) = (∏ t ∈ S₁.erase r, l t) * Q_out := by
    intro r hrS
    have hsplit : s.primeFactors.erase r = S₁.erase r ∪ (s.primeFactors \ S₁) := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro ⟨hxr, hxs⟩
        by_cases hxS : x ∈ S₁
        · exact Or.inl ⟨hxr, hxS⟩
        · exact Or.inr ⟨hxs, hxS⟩
      · rintro (⟨hxr, hxS⟩ | ⟨hxs, hxS⟩)
        · exact ⟨hxr, (Finset.mem_filter.mp hxS).1⟩
        · exact ⟨fun h => hxS (h ▸ hrS), hxs⟩
    have hdisj : Disjoint (S₁.erase r) (s.primeFactors \ S₁) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_sdiff.mp hx2).2 (Finset.mem_of_mem_erase hx1)
    rw [hsplit, Finset.prod_union hdisj]
  have hT_split : T = P_L * Q_out := by
    dsimp [P_L, Q_out]
    rw [hT_prod, ← Finset.prod_sdiff (Finset.filter_subset (v · = 1) s.primeFactors), mul_comm]
  have hQ_out_cop : p.Coprime Q_out :=
    hT_cop.coprime_dvd_right ⟨P_L, by rw [hT_split, mul_comm]⟩
  have hP_L_ge : 81 ≤ P_L := by
    have h3 : ∏ _r ∈ S₁, 3 ≤ P_L := Finset.prod_le_prod fun r hrS => by
      have hr := (Finset.mem_filter.mp hrS).1
      have hrp := Nat.prime_of_mem_primeFactors hr
      have he : 1 ≤ s.factorization r :=
        (hrp.dvd_iff_one_le_factorization hs.pos.ne').mp (Nat.dvd_of_mem_primeFactors hr)
      dsimp [l]; omega
    rw [Finset.prod_const] at h3
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ S₁.card := Nat.pow_le_pow_right (by decide) hS1_ge4
      _ ≤ P_L := h3
  have hQ_out_pos : 1 ≤ Q_out := Finset.one_le_prod fun _ _ => by dsimp [l]; omega
  have hT_ge2 : 2 ≤ T := by rw [hT_split]; nlinarith
  let S_m := ∑ r ∈ S₁, m r * (r - 1)
  let S_m2 := ∑ r ∈ S₁, m r * (r - 1) ^ 2
  let S_sq := ∑ r ∈ S₁, 8 * s.factorization r * (r - 1) ^ 2 * ∏ t ∈ S₁.erase r, l t
  have hSm_eq : 2 * S_m = T + A * Q_out := by
    have h1 : 2 * S_m = SumCoef * Q_out := by
      dsimp [S_m, SumCoef]
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun r hrS => ?_
      dsimp [m]
      rw [hQ_eq r hrS]
      ring
    rw [h1, hSum_eq, add_mul, hT_split]
  have h4Sm2_eq : 4 * S_m2 = S_sq * Q_out := by
    dsimp [S_m2, S_sq]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r hrS => ?_
    dsimp [m]
    rw [hQ_eq r hrS]
    ring
  have hp3_zero : (p : R) ^ 3 = 0 := by
    change (p : ZMod (p ^ 3)) ^ 3 = 0
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hcube := even_index_mod_p_cube_congruence hp hpo hs hu hσq hplus hσs
  change (2 : R) ^ T *
      (∏ r ∈ S₁, (1 + ((m r * (r - 1) : ℕ) : R) * (p : R) +
        ((Nat.choose (m r) 2 * (r - 1) ^ 2 : ℕ) : R) * (p : R) ^ 2)) =
      (2 : R) ^ T + (T : R) * (2 : R) ^ (T - 1) * ((p : R) + (p : R) ^ 2) +
        (Nat.choose T 2 : R) * (2 : R) ^ (T - 2) * (p : R) ^ 2 at hcube
  have hmul2 := congrArg (fun z : R => 2 * z) hcube
  have hprod_expand := two_mul_prod_one_add_quad (p : R) hp3_zero S₁
    (fun r => ((m r * (r - 1) : ℕ) : R))
    (fun r => ((Nat.choose (m r) 2 * (r - 1) ^ 2 : ℕ) : R))
  have hdiff_sum : (2 * ∑ r ∈ S₁, ((Nat.choose (m r) 2 * (r - 1) ^ 2 : ℕ) : R)) -
      ∑ r ∈ S₁, ((m r * (r - 1) : ℕ) : R) ^ 2 = -(S_m2 : R) := by
    dsimp [S_m2]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hch := two_mul_choose_two_add (m r)
    have hch_cast := congrArg (fun n : ℕ => (n : R) * ((r - 1 : ℕ) : R) ^ 2) hch
    push_cast at hch_cast ⊢
    linear_combination hch_cast
  have h2T : (2 : R) ^ T = 4 * (2 : R) ^ (T - 2) := by
    rw [show T = 2 + (T - 2) by omega, pow_add]
    norm_num
  have h2T1 : (2 : R) ^ (T - 1) = 2 * (2 : R) ^ (T - 2) := by
    rw [show T - 1 = 1 + (T - 2) by omega, pow_add]
    norm_num
  have hT_choose : 2 * (Nat.choose T 2 : R) = (T : R) ^ 2 - (T : R) := by
    have hch_cast := congrArg (fun n : ℕ => (n : R)) (two_mul_choose_two_add T)
    push_cast at hch_cast
    linear_combination hch_cast
  have h2_cop : Nat.Coprime (2 ^ (T - 2)) (p ^ 3) :=
    (Nat.coprime_two_left.mpr hpo).pow (T - 2) 3
  have h2_inv : ((2 : R) ^ (T - 2)) * (((2 ^ (T - 2) : ℕ) : R))⁻¹ = 1 := by
    simpa [Nat.cast_pow] using ZMod.coe_mul_inv_eq_one (2 ^ (T - 2)) h2_cop
  have hsum_m_cast : ∑ r ∈ S₁, ((m r * (r - 1) : ℕ) : R) = (S_m : R) := by
    dsimp [S_m]
    push_cast
    rfl
  have hreduced : (8 : R) + 8 * (S_m : R) * (p : R) + (4 * (S_m : R) ^ 2 - 4 * (S_m2 : R)) * (p : R) ^ 2 =
      8 + 4 * (T : R) * (p : R) + ((T : R) ^ 2 + 3 * (T : R)) * (p : R) ^ 2 := by
    have hL : 2 * ((2 : R) ^ T * (∏ r ∈ S₁, (1 + ((m r * (r - 1) : ℕ) : R) * (p : R) +
        ((Nat.choose (m r) 2 * (r - 1) ^ 2 : ℕ) : R) * (p : R) ^ 2))) =
        (2 : R) ^ (T - 2) * (8 + 8 * (S_m : R) * (p : R) +
          (4 * (S_m : R) ^ 2 - 4 * (S_m2 : R)) * (p : R) ^ 2) := by
      calc 2 * ((2 : R) ^ T * _)
          = (2 : R) ^ T * (2 * _) := by ring
        _ = (4 * (2 : R) ^ (T - 2)) * (2 + 2 * (∑ r ∈ S₁, ((m r * (r - 1) : ℕ) : R)) * (p : R) +
              ((∑ r ∈ S₁, ((m r * (r - 1) : ℕ) : R)) ^ 2 - ∑ r ∈ S₁, ((m r * (r - 1) : ℕ) : R) ^ 2 +
                2 * ∑ r ∈ S₁, ((Nat.choose (m r) 2 * (r - 1) ^ 2 : ℕ) : R)) * (p : R) ^ 2) := by
            rw [h2T, hprod_expand]
        _ = (2 : R) ^ (T - 2) * (8 + 8 * (S_m : R) * (p : R) +
              (4 * (S_m : R) ^ 2 - 4 * (S_m2 : R)) * (p : R) ^ 2) := by
            rw [hsum_m_cast]
            linear_combination (4 * (2 : R) ^ (T - 2) * (p : R) ^ 2) * hdiff_sum
    have hR : 2 * ((2 : R) ^ T + (T : R) * (2 : R) ^ (T - 1) * ((p : R) + (p : R) ^ 2) +
        (Nat.choose T 2 : R) * (2 : R) ^ (T - 2) * (p : R) ^ 2) =
        (2 : R) ^ (T - 2) * (8 + 4 * (T : R) * (p : R) + ((T : R) ^ 2 + 3 * (T : R)) * (p : R) ^ 2) := by
      rw [h2T, h2T1]
      linear_combination (2 : R) ^ (T - 2) * (p : R) ^ 2 * hT_choose
    have hmul_eq : (2 : R) ^ (T - 2) * (8 + 8 * (S_m : R) * (p : R) +
          (4 * (S_m : R) ^ 2 - 4 * (S_m2 : R)) * (p : R) ^ 2) =
        (2 : R) ^ (T - 2) * (8 + 4 * (T : R) * (p : R) + ((T : R) ^ 2 + 3 * (T : R)) * (p : R) ^ 2) := by
      rw [← hL, ← hR]
      exact hmul2
    calc (8 + 8 * (S_m : R) * (p : R) + (4 * (S_m : R) ^ 2 - 4 * (S_m2 : R)) * (p : R) ^ 2)
        = (8 + 8 * (S_m : R) * (p : R) + (4 * (S_m : R) ^ 2 - 4 * (S_m2 : R)) * (p : R) ^ 2) *
            ((2 : R) ^ (T - 2) * (((2 ^ (T - 2) : ℕ) : R))⁻¹) := by
          rw [h2_inv, mul_one]
      _ = ((2 : R) ^ (T - 2) * (8 + 8 * (S_m : R) * (p : R) +
            (4 * (S_m : R) ^ 2 - 4 * (S_m2 : R)) * (p : R) ^ 2)) * (((2 ^ (T - 2) : ℕ) : R))⁻¹ := by
          ring
      _ = ((2 : R) ^ (T - 2) * (8 + 4 * (T : R) * (p : R) +
            ((T : R) ^ 2 + 3 * (T : R)) * (p : R) ^ 2)) * (((2 ^ (T - 2) : ℕ) : R))⁻¹ := by
          rw [hmul_eq]
      _ = (8 + 4 * (T : R) * (p : R) + ((T : R) ^ 2 + 3 * (T : R)) * (p : R) ^ 2) *
            ((2 : R) ^ (T - 2) * (((2 ^ (T - 2) : ℕ) : R))⁻¹) := by ring
      _ = 8 + 4 * (T : R) * (p : R) + ((T : R) ^ 2 + 3 * (T : R)) * (p : R) ^ 2 := by
          rw [h2_inv, mul_one]
  have hp_mul := congrArg (fun z : R => z * (p : R)) hreduced
  have hSm_cast : (2 : R) * (S_m : R) = (T : R) + (A : R) * (Q_out : R) := by
    have hcast := congrArg (fun n : ℕ => (n : R)) hSm_eq
    push_cast at hcast
    exact hcast
  have hA_zero : ((4 * A * Q_out * p ^ 2 : ℕ) : R) = 0 := by
    have hp_eq : 8 * (p : R) + 4 * ((2 : R) * (S_m : R)) * (p : R) ^ 2 =
        8 * (p : R) + 4 * (T : R) * (p : R) ^ 2 := by
      linear_combination hp_mul - (4 * (S_m : R) ^ 2 - 4 * (S_m2 : R) - ((T : R) ^ 2 + 3 * (T : R))) * hp3_zero
    rw [hSm_cast] at hp_eq
    push_cast
    linear_combination hp_eq
  have hp3_dvd : p ^ 3 ∣ 4 * A * Q_out * p ^ 2 := (ZMod.natCast_eq_zero_iff _ _).mp hA_zero
  rw [show p ^ 3 = p * p ^ 2 by ring] at hp3_dvd
  have hp_dvd_prod : p ∣ 4 * A * Q_out := Nat.dvd_of_mul_dvd_mul_right (pow_pos hp.pos 2) hp3_dvd
  have hp_cop4 : p.Coprime 4 := show p.Coprime (2 ^ 2) from (Nat.coprime_two_right.mpr hpo).pow_right 2
  have hp_dvd_4A : p ∣ 4 * A := hQ_out_cop.dvd_of_dvd_mul_right hp_dvd_prod
  have hp_dvd_A : p ∣ A := hp_cop4.dvd_of_dvd_mul_left hp_dvd_4A
  refine ⟨hlt_L, hp_dvd_A, ?_⟩
  set k := A / p
  have hA_eq : A = k * p := (Nat.div_mul_cancel hp_dvd_A).symm
  have h2Sm_k : (2 : R) * (S_m : R) = (T : R) + (k : R) * (Q_out : R) * (p : R) := by
    rw [hSm_cast, hA_eq]
    push_cast
    ring
  have h4Sm_sq : 4 * (S_m : R) ^ 2 * (p : R) ^ 2 = (T : R) ^ 2 * (p : R) ^ 2 := by
    calc 4 * (S_m : R) ^ 2 * (p : R) ^ 2
        = ((2 : R) * (S_m : R)) ^ 2 * (p : R) ^ 2 := by ring
      _ = ((T : R) + (k : R) * (Q_out : R) * (p : R)) ^ 2 * (p : R) ^ 2 := by rw [h2Sm_k]
      _ = (T : R) ^ 2 * (p : R) ^ 2 := by
          linear_combination (2 * (T : R) * (k : R) * (Q_out : R) +
            (k : R) ^ 2 * (Q_out : R) ^ 2 * (p : R)) * hp3_zero
  have h8Sm_p : 8 * (S_m : R) * (p : R) =
      4 * (T : R) * (p : R) + 4 * (k : R) * (Q_out : R) * (p : R) ^ 2 := by
    calc 8 * (S_m : R) * (p : R) = 4 * ((2 : R) * (S_m : R)) * (p : R) := by ring
      _ = 4 * ((T : R) + (k : R) * (Q_out : R) * (p : R)) * (p : R) := by rw [h2Sm_k]
      _ = 4 * (T : R) * (p : R) + 4 * (k : R) * (Q_out : R) * (p : R) ^ 2 := by ring
  have hpsq_eq : ((4 * k * Q_out : ℕ) : R) * (p : R) ^ 2 =
      ((3 * T + 4 * S_m2 : ℕ) : R) * (p : R) ^ 2 := by
    push_cast
    linear_combination hreduced - h8Sm_p - h4Sm_sq
  have hmod_Q : 4 * k * Q_out ≡ 3 * T + 4 * S_m2 [MOD p] :=
    modEq_of_mul_p_sq_eq hp.pos hpsq_eq
  have hmod_Q' : (4 * k) * Q_out ≡ (3 * P_L + S_sq) * Q_out [MOD p] := by
    simpa only [hT_split, h4Sm2_eq, mul_assoc, add_mul] using hmod_Q
  have hzp_eq : ((4 * k : ℕ) : ZMod p) * (Q_out : ZMod p) =
      ((3 * P_L + S_sq : ℕ) : ZMod p) * (Q_out : ZMod p) := by
    simpa [Nat.cast_mul] using (ZMod.natCast_eq_natCast_iff _ _ p).mpr hmod_Q'
  have hQ_inv : (Q_out : ZMod p) * (Q_out : ZMod p)⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one Q_out hQ_out_cop.symm
  have hzp_cancel : ((4 * k : ℕ) : ZMod p) = ((3 * P_L + S_sq : ℕ) : ZMod p) := by
    calc ((4 * k : ℕ) : ZMod p)
        = ((4 * k : ℕ) : ZMod p) * ((Q_out : ZMod p) * (Q_out : ZMod p)⁻¹) := by rw [hQ_inv, mul_one]
      _ = (((4 * k : ℕ) : ZMod p) * (Q_out : ZMod p)) * (Q_out : ZMod p)⁻¹ := by ring
      _ = (((3 * P_L + S_sq : ℕ) : ZMod p) * (Q_out : ZMod p)) * (Q_out : ZMod p)⁻¹ := by rw [hzp_eq]
      _ = ((3 * P_L + S_sq : ℕ) : ZMod p) * ((Q_out : ZMod p) * (Q_out : ZMod p)⁻¹) := by ring
      _ = ((3 * P_L + S_sq : ℕ) : ZMod p) := by rw [hQ_inv, mul_one]
  exact (ZMod.natCast_eq_natCast_iff (4 * k) (3 * P_L + S_sq) p).mp hzp_cancel

/-- Denominator-cleared congruence modulo `p` for the quotient `A / p`
at any even prime-power component index `i = p ^ (2 * u)`. -/
theorem even_index_quotient_mod_p_congruence {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    let S₁ := s.primeFactors.filter (v · = 1)
    let l (r : ℕ) := 2 * s.factorization r + 1
    let P_L := ∏ r ∈ S₁, l r
    let A := (∑ r ∈ S₁, 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t) - P_L
    4 * (A / p) ≡ 3 * P_L + ∑ r ∈ S₁, 8 * s.factorization r * (r - 1) ^ 2 * ∏ t ∈ S₁.erase r, l t [MOD p] :=
  (even_index_A_pos_and_quotient_modEq hp hpo hs hu hσq hplus hσs).2.2

/-- `T`-independent second-order `ZMod (p ^ 2)` congruence on the single-copy primes `S₁`. -/
theorem even_index_mod_p_sq_second_order_congruence {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    let S₁ := s.primeFactors.filter (v · = 1)
    (∑ r ∈ S₁, ((8 * s.factorization r * (r - 1) : ℕ) : ZMod (p ^ 2)) *
      (2 - ((r - 1 : ℕ) : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) *
      ((2 * s.factorization r + 1 : ZMod (p ^ 2)))⁻¹) = 4 + 3 * (p : ZMod (p ^ 2)) := by
  intro v S₁
  let R := ZMod (p ^ 2)
  let l (r : ℕ) := 2 * s.factorization r + 1
  let P_L := ∏ r ∈ S₁, l r
  let SumCoef := ∑ r ∈ S₁, 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t
  let A := SumCoef - P_L
  let S_sq := ∑ r ∈ S₁, 8 * s.factorization r * (r - 1) ^ 2 * ∏ t ∈ S₁.erase r, l t
  obtain ⟨hlt_L, hp_dvd_A, hmod⟩ := even_index_A_pos_and_quotient_modEq hp hpo hs hu hσq hplus hσs
  change P_L < SumCoef at hlt_L
  change p ∣ A at hp_dvd_A
  change 4 * (A / p) ≡ 3 * P_L + S_sq [MOD p] at hmod
  have hA_eq : A = (A / p) * p := (Nat.div_mul_cancel hp_dvd_A).symm
  have hSum_eq : SumCoef = P_L + A := by dsimp [A]; omega
  have hmul_p := modEq_mul_p_cast_sq hmod
  have hcleared : (∑ r ∈ S₁, ((8 * s.factorization r * (r - 1) : ℕ) : R) *
      (2 - ((r - 1 : ℕ) : R) * (p : R)) * (∏ t ∈ S₁.erase r, (l t : R))) =
      (P_L : R) * (4 + 3 * (p : R)) := by
    have h4A : (4 : R) * (A : R) = ((3 * P_L + S_sq : ℕ) : R) * (p : R) := by
      calc (4 : R) * (A : R) = ((4 * (A / p) : ℕ) : R) * (p : R) := by
            conv_lhs => rw [hA_eq]
            push_cast
            ring
        _ = ((3 * P_L + S_sq : ℕ) : R) * (p : R) := hmul_p
    have h4Sum : (4 : R) * (SumCoef : R) = (4 : R) * (P_L : R) + (4 : R) * (A : R) := by
      rw [hSum_eq]; push_cast; ring
    have hL_split : (∑ r ∈ S₁, ((8 * s.factorization r * (r - 1) : ℕ) : R) *
        (2 - ((r - 1 : ℕ) : R) * (p : R)) * (∏ t ∈ S₁.erase r, (l t : R))) =
        (4 : R) * (SumCoef : R) - (S_sq : R) * (p : R) := by
      dsimp [SumCoef, S_sq]
      push_cast
      rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    rw [hL_split, h4Sum, h4A]
    push_cast
    ring
  have hl_cop : ∀ r ∈ S₁, Nat.Coprime (l r) (p ^ 2) := by
    intro r hrS
    have hr := (Finset.mem_filter.mp hrS).1
    have hndvd : ¬ p ∣ l r :=
      (even_index_cofactor_component_order_dvd_pred hp hpo hs hσq hplus hσs hr).2.1
    exact (hp.coprime_iff_not_dvd.mpr hndvd).symm.pow_right 2
  have hP_L_cop : Nat.Coprime P_L (p ^ 2) := by
    dsimp [P_L]
    exact Nat.coprime_prod_left_iff.mpr hl_cop
  have hP_L_inv : (P_L : R) * (P_L : R)⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one P_L hP_L_cop
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
  have hfactor : (∑ r ∈ S₁, ((8 * s.factorization r * (r - 1) : ℕ) : R) *
      (2 - ((r - 1 : ℕ) : R) * (p : R)) * (∏ t ∈ S₁.erase r, (l t : R))) =
      (P_L : R) * ∑ r ∈ S₁, ((8 * s.factorization r * (r - 1) : ℕ) : R) *
        (2 - ((r - 1 : ℕ) : R) * (p : R)) * ((2 * s.factorization r + 1 : R))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hrS => ?_
    rw [hprod_inv r hrS]
    dsimp [l]
    push_cast
    ring
  rw [hfactor] at hcleared
  calc (∑ r ∈ S₁, ((8 * s.factorization r * (r - 1) : ℕ) : R) *
        (2 - ((r - 1 : ℕ) : R) * (p : R)) * ((2 * s.factorization r + 1 : R))⁻¹)
      = ((P_L : R) * _) * (P_L : R)⁻¹ := by
          rw [mul_comm ((P_L : R) * _), ← mul_assoc, mul_comm (P_L : R)⁻¹ (P_L : R), hP_L_inv, one_mul]
    _ = ((P_L : R) * (4 + 3 * (p : R))) * (P_L : R)⁻¹ := by rw [hcleared]
    _ = (4 + 3 * (p : R)) * ((P_L : R) * (P_L : R)⁻¹) := by ring
    _ = 4 + 3 * (p : R) := by rw [hP_L_inv, mul_one]

private lemma sixty_four_mul_odd_pow8_le_three_pow {e : ℕ} (he : 15 ≤ e) :
    64 * (2 * e + 1) ^ 8 ≤ 3 ^ (2 * e) := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hstep : 4 * (2 * (k + 1) + 1) ≤ 5 * (2 * k + 1) := by omega
    have hpow8 : 4 ^ 8 * (2 * (k + 1) + 1) ^ 8 ≤ 5 ^ 8 * (2 * k + 1) ^ 8 := by
      calc 4 ^ 8 * (2 * (k + 1) + 1) ^ 8
          = (4 * (2 * (k + 1) + 1)) ^ 8 := by ring
        _ ≤ (5 * (2 * k + 1)) ^ 8 := Nat.pow_le_pow_left hstep 8
        _ = 5 ^ 8 * (2 * k + 1) ^ 8 := by ring
    have hscale : 65536 * (64 * (2 * (k + 1) + 1) ^ 8) ≤ 65536 * 3 ^ (2 * (k + 1)) := by
      calc 65536 * (64 * (2 * (k + 1) + 1) ^ 8)
          = 64 * (4 ^ 8 * (2 * (k + 1) + 1) ^ 8) := by norm_num; ring
        _ ≤ 64 * (5 ^ 8 * (2 * k + 1) ^ 8) := Nat.mul_le_mul_left 64 hpow8
        _ = 390625 * (64 * (2 * k + 1) ^ 8) := by norm_num; ring
        _ ≤ 589824 * (64 * (2 * k + 1) ^ 8) := Nat.mul_le_mul_right _ (by decide)
        _ ≤ 589824 * 3 ^ (2 * k) := Nat.mul_le_mul_left 589824 ih
        _ = 65536 * 3 ^ (2 * (k + 1)) := by rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]; ring
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

private lemma refute_card_four_arith {p r₁ r₂ r₃ r₄ e₁ e₂ e₃ e₄ : ℕ}
    (hp : p.Prime) (hr₁p : r₁.Prime) (hr₁o : Odd r₁)
    (hr₂p : r₂.Prime) (hr₃p : r₃.Prime) (hr₄p : r₄.Prime)
    (he₄ : 1 ≤ e₄) (he₃₄ : e₄ < e₃) (he₂₃ : e₃ < e₂) (he₁₂ : e₂ < e₁)
    (hr₁₂ : r₁ < r₂) (hr₂₃ : r₂ < r₃) (hr₃₄ : r₃ < r₄)
    (hl₁p : (2 * e₁ + 1).Prime) (hl₂p : (2 * e₂ + 1).Prime)
    (hl₃p : (2 * e₃ + 1).Prime) (hl₄p : (2 * e₄ + 1).Prime)
    (hl₂_dvd : 2 * (2 * e₂ + 1) ∣ p - 1)
    (hσr₁ : sigma 1 (r₁ ^ (2 * e₁)) = p)
    (hσr₄ : sigma 1 (r₄ ^ (2 * e₄)) = p)
    (hle_p : p ≤ 4 * e₁ * (r₁ - 1) * (2 * e₂ + 1) * (2 * e₃ + 1) * (2 * e₄ + 1) +
      4 * e₂ * (r₂ - 1) * (2 * e₁ + 1) * (2 * e₃ + 1) * (2 * e₄ + 1) +
      4 * e₃ * (r₃ - 1) * (2 * e₁ + 1) * (2 * e₂ + 1) * (2 * e₄ + 1) +
      4 * e₄ * (r₄ - 1) * (2 * e₁ + 1) * (2 * e₂ + 1) * (2 * e₃ + 1) -
      (2 * e₁ + 1) * (2 * e₂ + 1) * (2 * e₃ + 1) * (2 * e₄ + 1)) : False := by
  have he₃ : 2 ≤ e₃ := by omega
  have he₂ : 3 ≤ e₂ := by omega
  have he₁ : 5 ≤ e₁ := by
    have hnot9 : 2 * e₁ + 1 ≠ 9 := by
      intro h9
      rw [h9] at hl₁p
      exact absurd hl₁p (by decide)
    omega
  have hr₁_mod : r₁ % 2 = 1 := Nat.odd_iff.mp hr₁o
  have hr₁_ge3 : 3 ≤ r₁ := by have := hr₁p.two_le; omega
  let l₁ := 2 * e₁ + 1
  let l₂ := 2 * e₂ + 1
  let l₃ := 2 * e₃ + 1
  let l₄ := 2 * e₄ + 1
  let L := 4 * e₁ * (r₁ - 1) * l₂ * l₃ * l₄ + 4 * e₂ * (r₂ - 1) * l₁ * l₃ * l₄ +
    4 * e₃ * (r₃ - 1) * l₁ * l₂ * l₄ + 4 * e₄ * (r₄ - 1) * l₁ * l₂ * l₃ - l₁ * l₂ * l₃ * l₄
  have hle_p' : p ≤ L := hle_p
  have hr₁₄ : r₁ < r₄ := lt_trans hr₁₂ (lt_trans hr₂₃ hr₃₄)
  have hr₂₄ : r₂ < r₄ := lt_trans hr₂₃ hr₃₄
  have hL_lt_prod : L < 8 * l₁ * l₂ * l₃ * l₄ * r₄ := by
    have h1 : 4 * e₁ * (r₁ - 1) * l₂ * l₃ * l₄ ≤ 4 * e₁ * r₁ * l₂ * l₃ * l₄ := by gcongr; omega
    have h2 : 4 * e₂ * (r₂ - 1) * l₁ * l₃ * l₄ ≤ 4 * e₂ * r₂ * l₁ * l₃ * l₄ := by gcongr; omega
    have h3 : 4 * e₃ * (r₃ - 1) * l₁ * l₂ * l₄ ≤ 4 * e₃ * r₃ * l₁ * l₂ * l₄ := by gcongr; omega
    have h4 : 4 * e₄ * (r₄ - 1) * l₁ * l₂ * l₃ ≤ 4 * e₄ * r₄ * l₁ * l₂ * l₃ := by gcongr; omega
    have ht1 : 4 * e₁ * r₁ * l₂ * l₃ * l₄ < 2 * l₁ * l₂ * l₃ * l₄ * r₄ := by
      have ha : 4 * e₁ * r₁ < 2 * l₁ * r₄ :=
        calc 4 * e₁ * r₁ < 2 * l₁ * r₁ := Nat.mul_lt_mul_of_pos_right (by dsimp [l₁]; omega) hr₁p.pos
          _ < 2 * l₁ * r₄ := Nat.mul_lt_mul_of_pos_left hr₁₄ (by positivity)
      calc 4 * e₁ * r₁ * l₂ * l₃ * l₄ < 2 * l₁ * r₄ * l₂ * l₃ * l₄ :=
            Nat.mul_lt_mul_of_pos_right
              (Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right ha (by dsimp [l₂]; omega))
                (by dsimp [l₃]; omega)) (by dsimp [l₄]; omega)
        _ = 2 * l₁ * l₂ * l₃ * l₄ * r₄ := by ring
    have ht2 : 4 * e₂ * r₂ * l₁ * l₃ * l₄ < 2 * l₁ * l₂ * l₃ * l₄ * r₄ := by
      have ha : 4 * e₂ * r₂ < 2 * l₂ * r₄ :=
        calc 4 * e₂ * r₂ < 2 * l₂ * r₂ := Nat.mul_lt_mul_of_pos_right (by dsimp [l₂]; omega) hr₂p.pos
          _ < 2 * l₂ * r₄ := Nat.mul_lt_mul_of_pos_left hr₂₄ (by positivity)
      calc 4 * e₂ * r₂ * l₁ * l₃ * l₄ < 2 * l₂ * r₄ * l₁ * l₃ * l₄ :=
            Nat.mul_lt_mul_of_pos_right
              (Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right ha (by dsimp [l₁]; omega))
                (by dsimp [l₃]; omega)) (by dsimp [l₄]; omega)
        _ = 2 * l₁ * l₂ * l₃ * l₄ * r₄ := by ring
    have ht3 : 4 * e₃ * r₃ * l₁ * l₂ * l₄ < 2 * l₁ * l₂ * l₃ * l₄ * r₄ := by
      have ha : 4 * e₃ * r₃ < 2 * l₃ * r₄ :=
        calc 4 * e₃ * r₃ < 2 * l₃ * r₃ := Nat.mul_lt_mul_of_pos_right (by dsimp [l₃]; omega) hr₃p.pos
          _ < 2 * l₃ * r₄ := Nat.mul_lt_mul_of_pos_left hr₃₄ (by positivity)
      calc 4 * e₃ * r₃ * l₁ * l₂ * l₄ < 2 * l₃ * r₄ * l₁ * l₂ * l₄ :=
            Nat.mul_lt_mul_of_pos_right
              (Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right ha (by dsimp [l₁]; omega))
                (by dsimp [l₂]; omega)) (by dsimp [l₄]; omega)
        _ = 2 * l₁ * l₂ * l₃ * l₄ * r₄ := by ring
    have ht4 : 4 * e₄ * r₄ * l₁ * l₂ * l₃ < 2 * l₁ * l₂ * l₃ * l₄ * r₄ := by
      have ha : 4 * e₄ * r₄ < 2 * l₄ * r₄ :=
        Nat.mul_lt_mul_of_pos_right (by dsimp [l₄]; omega) hr₄p.pos
      calc 4 * e₄ * r₄ * l₁ * l₂ * l₃ < 2 * l₄ * r₄ * l₁ * l₂ * l₃ :=
            Nat.mul_lt_mul_of_pos_right
              (Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right ha (by dsimp [l₁]; omega))
                (by dsimp [l₂]; omega)) (by dsimp [l₃]; omega)
        _ = 2 * l₁ * l₂ * l₃ * l₄ * r₄ := by ring
    calc L ≤ 4 * e₁ * (r₁ - 1) * l₂ * l₃ * l₄ + 4 * e₂ * (r₂ - 1) * l₁ * l₃ * l₄ +
          4 * e₃ * (r₃ - 1) * l₁ * l₂ * l₄ + 4 * e₄ * (r₄ - 1) * l₁ * l₂ * l₃ := Nat.sub_le _ _
      _ ≤ 4 * e₁ * r₁ * l₂ * l₃ * l₄ + 4 * e₂ * r₂ * l₁ * l₃ * l₄ +
          4 * e₃ * r₃ * l₁ * l₂ * l₄ + 4 * e₄ * r₄ * l₁ * l₂ * l₃ := by omega
      _ < 2 * l₁ * l₂ * l₃ * l₄ * r₄ + 2 * l₁ * l₂ * l₃ * l₄ * r₄ +
          2 * l₁ * l₂ * l₃ * l₄ * r₄ + 2 * l₁ * l₂ * l₃ * l₄ * r₄ := by omega
      _ = 8 * l₁ * l₂ * l₃ * l₄ * r₄ := by ring
  have hr₄_sq_lt_p : r₄ ^ 2 < p := by
    have hrange : range 3 ⊆ range (2 * e₄ + 1) := Finset.range_mono (by omega : 3 ≤ 2 * e₄ + 1)
    have hsum3 : 1 + r₄ + r₄ ^ 2 ≤ sigma 1 (r₄ ^ (2 * e₄)) := by
      rw [sigma_one_apply_prime_pow hr₄p]
      calc 1 + r₄ + r₄ ^ 2 = ∑ j ∈ range 3, r₄ ^ j := by
            simp [Finset.sum_range_succ, Nat.add_assoc]
        _ ≤ ∑ j ∈ range (2 * e₄ + 1), r₄ ^ j := Finset.sum_le_sum_of_subset hrange
    rw [hσr₄] at hsum3
    omega
  have hr₁_pow_lt_p : r₁ ^ (2 * e₁) < p := by
    rw [← hσr₁]
    exact self_lt_sigma_of_one_lt (one_lt_pow₀ hr₁p.one_lt (by omega))
  by_cases hr₄_big : 8 * l₁ * l₂ * l₃ * l₄ ≤ r₄
  · have : L < r₄ ^ 2 := by
      calc L < 8 * l₁ * l₂ * l₃ * l₄ * r₄ := hL_lt_prod
        _ ≤ r₄ * r₄ := Nat.mul_le_mul_right r₄ hr₄_big
        _ = r₄ ^ 2 := by ring
    omega
  · have hr₄_lt : r₄ < 8 * l₁ * l₂ * l₃ * l₄ := by omega
    have hL_lt_sq : L < (8 * l₁ * l₂ * l₃ * l₄) ^ 2 := by
      have : 8 * l₁ * l₂ * l₃ * l₄ * r₄ < 8 * l₁ * l₂ * l₃ * l₄ * (8 * l₁ * l₂ * l₃ * l₄) :=
        Nat.mul_lt_mul_of_pos_left hr₄_lt (by positivity)
      calc L < 8 * l₁ * l₂ * l₃ * l₄ * r₄ := hL_lt_prod
        _ < 8 * l₁ * l₂ * l₃ * l₄ * (8 * l₁ * l₂ * l₃ * l₄) := this
        _ = (8 * l₁ * l₂ * l₃ * l₄) ^ 2 := by ring
    by_cases he₁_big : 15 ≤ e₁
    · have hl₂_lt : l₂ < l₁ := by dsimp [l₁, l₂]; omega
      have hl₃_lt : l₃ < l₁ := by dsimp [l₁, l₃]; omega
      have hl₄_lt : l₄ < l₁ := by dsimp [l₁, l₄]; omega
      have hL_lt_64 : L < 64 * l₁ ^ 8 := by
        have hpow : (8 * l₁ * l₂ * l₃ * l₄) ^ 2 < 64 * l₁ ^ 8 := by
          have h1 : l₂ * l₃ * l₄ < l₁ * l₁ * l₁ := by gcongr
          calc (8 * l₁ * l₂ * l₃ * l₄) ^ 2
              = 64 * (l₁ * (l₂ * l₃ * l₄)) ^ 2 := by ring
            _ < 64 * (l₁ * (l₁ * l₁ * l₁)) ^ 2 := by gcongr
            _ = 64 * l₁ ^ 8 := by ring
        omega
      have h64 := sixty_four_mul_odd_pow8_le_three_pow he₁_big
      have h3_le : 3 ^ (2 * e₁) ≤ r₁ ^ (2 * e₁) := Nat.pow_le_pow_left hr₁_ge3 (2 * e₁)
      change L < 64 * (2 * e₁ + 1) ^ 8 at hL_lt_64
      omega
    · have hl₂_le : l₂ ≤ l₁ - 2 := by dsimp [l₁, l₂]; omega
      have hl₃_le : l₃ ≤ l₁ - 4 := by dsimp [l₁, l₃]; omega
      have hl₄_le : l₄ ≤ l₁ - 6 := by dsimp [l₁, l₄]; omega
      rcases (by omega : e₁ = 5 ∨ e₁ = 6 ∨ e₁ = 7 ∨ e₁ = 8 ∨ e₁ = 9 ∨ e₁ = 10 ∨
          e₁ = 11 ∨ e₁ = 12 ∨ e₁ = 13 ∨ e₁ = 14) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · -- e₁ = 5, l₁ = 11
        have he₂_eq : e₂ = 3 := by
          have : e₂ ≠ 4 := by intro h4; rw [h4] at hl₂p; exact absurd hl₂p (by decide)
          omega
        have he₃_eq : e₃ = 2 := by omega
        have he₄_eq : e₄ = 1 := by omega
        subst he₂_eq he₃_eq he₄_eq
        change L < (8 * (2 * 5 + 1) * (2 * 3 + 1) * (2 * 2 + 1) * (2 * 1 + 1)) ^ 2 at hL_lt_sq
        norm_num at hL_lt_sq
        by_cases hr₁_ge7 : 7 ≤ r₁
        · have h7 : (7 : ℕ) ^ (2 * 5) = 282475249 := by norm_num
          have : 282475249 ≤ r₁ ^ (2 * 5) := h7 ▸ Nat.pow_le_pow_left hr₁_ge7 (2 * 5)
          omega
        · rcases (by omega : r₁ = 3 ∨ r₁ = 5) with rfl | rfl
          · rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
            norm_num [Finset.sum_range_succ] at hσr₁
            rw [← hσr₁] at hp
            have hdiv : 23 ∣ 88573 := by norm_num
            have := hp.eq_one_or_self_of_dvd 23 hdiv
            omega
          · rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
            norm_num [Finset.sum_range_succ] at hσr₁
            rw [← hσr₁] at hl₂_dvd
            norm_num at hl₂_dvd
      · -- e₁ = 6, l₁ = 13
        have hl₂_le' : l₂ ≤ 11 := by dsimp [l₂]; omega
        have hl₃_le' : l₃ ≤ 7 := by
          have : e₃ ≠ 4 := by intro h4; rw [h4] at hl₃p; exact absurd hl₃p (by decide)
          dsimp [l₃]; omega
        have hl₄_le' : l₄ ≤ 5 := by dsimp [l₄]; omega
        have hL_bound : L < 1603201600 := by
          have hmul : 8 * l₁ * l₂ * l₃ * l₄ ≤ 40040 := by
            have hl₁v : l₁ = 13 := rfl
            calc 8 * l₁ * l₂ * l₃ * l₄ = 8 * 13 * l₂ * l₃ * l₄ := by rw [hl₁v]
              _ ≤ 8 * 13 * 11 * 7 * 5 := by gcongr
              _ = 40040 := by norm_num
          have hsq : (8 * l₁ * l₂ * l₃ * l₄) ^ 2 ≤ 1603201600 :=
            (Nat.pow_le_pow_left hmul 2).trans (by norm_num)
          omega
        by_cases hr₁_ge7 : 7 ≤ r₁
        · have h7 : (7 : ℕ) ^ (2 * 6) = 13841287201 := by norm_num
          have : 13841287201 ≤ r₁ ^ (2 * 6) := h7 ▸ Nat.pow_le_pow_left hr₁_ge7 (2 * 6)
          omega
        · rcases (by omega : r₁ = 3 ∨ r₁ = 5) with rfl | rfl
          · rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
            norm_num [Finset.sum_range_succ] at hσr₁
            have he₂_ne4 : e₂ ≠ 4 := by intro h4; rw [h4] at hl₂p; exact absurd hl₂p (by decide)
            have he₂_ne5 : e₂ ≠ 5 := by
              intro h5; rw [h5, ← hσr₁] at hl₂_dvd; norm_num at hl₂_dvd
            have he₄_eq1 : e₄ = 1 := by omega
            have hσr₄_val : 1 + r₄ + r₄ ^ 2 = 797161 := by
              rw [hσr₁, ← hσr₄, he₄_eq1, mul_one, sigma_one_apply_prime_pow hr₄p]
              simp [Finset.sum_range_succ, Nat.add_assoc]
            by_cases hr₄_le : r₄ ≤ 892 <;> nlinarith only [hσr₄_val, hr₄_le]
          · rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
            norm_num [Finset.sum_range_succ] at hσr₁
            have he₂_ne4 : e₂ ≠ 4 := by intro h4; rw [h4] at hl₂p; exact absurd hl₂p (by decide)
            have he₂_ne5 : e₂ ≠ 5 := by
              intro h5; rw [h5, ← hσr₁] at hl₂_dvd; norm_num at hl₂_dvd
            have he₄_eq1 : e₄ = 1 := by omega
            have hσr₄_val : 1 + r₄ + r₄ ^ 2 = 305175781 := by
              rw [hσr₁, ← hσr₄, he₄_eq1, mul_one, sigma_one_apply_prime_pow hr₄p]
              simp [Finset.sum_range_succ, Nat.add_assoc]
            by_cases hr₄_le : r₄ ≤ 17468 <;> nlinarith only [hσr₄_val, hr₄_le]
      · exact absurd hl₁p (by decide)
      · -- e₁ = 8, l₁ = 17
        have hL_bound : L < 85100558400 := by
          have hl₁v : l₁ = 17 := rfl
          have hmul : 8 * l₁ * l₂ * l₃ * l₄ ≤ 291720 := by
            calc 8 * l₁ * l₂ * l₃ * l₄ = 8 * 17 * l₂ * l₃ * l₄ := by rw [hl₁v]
              _ ≤ 8 * 17 * 15 * 13 * 11 := by gcongr <;> omega
              _ = 291720 := by norm_num
          have hsq : (8 * l₁ * l₂ * l₃ * l₄) ^ 2 ≤ 85100558400 :=
            (Nat.pow_le_pow_left hmul 2).trans (by norm_num)
          omega
        by_cases hr₁_ge5 : 5 ≤ r₁
        · have h5 : (5 : ℕ) ^ (2 * 8) = 152587890625 := by norm_num
          have : 152587890625 ≤ r₁ ^ (2 * 8) := h5 ▸ Nat.pow_le_pow_left hr₁_ge5 (2 * 8)
          omega
        · have hr₁_eq3 : r₁ = 3 := by omega
          subst hr₁_eq3
          rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
          norm_num [Finset.sum_range_succ] at hσr₁
          rw [← hσr₁] at hp
          have hdiv : 1871 ∣ 64570081 := by norm_num
          have := hp.eq_one_or_self_of_dvd 1871 hdiv
          omega
      · -- e₁ = 9, l₁ = 19
        have hL_bound : L < 253895054400 := by
          have hl₁v : l₁ = 19 := rfl
          have hmul : 8 * l₁ * l₂ * l₃ * l₄ ≤ 503880 := by
            calc 8 * l₁ * l₂ * l₃ * l₄ = 8 * 19 * l₂ * l₃ * l₄ := by rw [hl₁v]
              _ ≤ 8 * 19 * 17 * 15 * 13 := by gcongr <;> omega
              _ = 503880 := by norm_num
          have hsq : (8 * l₁ * l₂ * l₃ * l₄) ^ 2 ≤ 253895054400 :=
            (Nat.pow_le_pow_left hmul 2).trans (by norm_num)
          omega
        by_cases hr₁_ge5 : 5 ≤ r₁
        · have h5 : (5 : ℕ) ^ (2 * 9) = 3814697265625 := by norm_num
          have : 3814697265625 ≤ r₁ ^ (2 * 9) := h5 ▸ Nat.pow_le_pow_left hr₁_ge5 (2 * 9)
          omega
        · have hr₁_eq3 : r₁ = 3 := by omega
          subst hr₁_eq3
          rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
          norm_num [Finset.sum_range_succ] at hσr₁
          rw [← hσr₁] at hp
          have hdiv : 1597 ∣ 581130733 := by norm_num
          have := hp.eq_one_or_self_of_dvd 1597 hdiv
          omega
      · exact absurd hl₁p (by decide)
      · -- e₁ = 11, l₁ = 23
        have hL_bound : L < 1557683717184 := by
          have hl₁v : l₁ = 23 := rfl
          have hmul : 8 * l₁ * l₂ * l₃ * l₄ ≤ 1248072 := by
            calc 8 * l₁ * l₂ * l₃ * l₄ = 8 * 23 * l₂ * l₃ * l₄ := by rw [hl₁v]
              _ ≤ 8 * 23 * 21 * 19 * 17 := by gcongr <;> omega
              _ = 1248072 := by norm_num
          have hsq : (8 * l₁ * l₂ * l₃ * l₄) ^ 2 ≤ 1557683717184 :=
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
        have hL_bound : L < 12972963240000 := by
          have hl₁v : l₁ = 29 := rfl
          have hmul : 8 * l₁ * l₂ * l₃ * l₄ ≤ 3601800 := by
            calc 8 * l₁ * l₂ * l₃ * l₄ = 8 * 29 * l₂ * l₃ * l₄ := by rw [hl₁v]
              _ ≤ 8 * 29 * 27 * 25 * 23 := by gcongr <;> omega
              _ = 3601800 := by norm_num
          have hsq : (8 * l₁ * l₂ * l₃ * l₄) ^ 2 ≤ 12972963240000 :=
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

/-- Unconditionally, at any even prime-power component index `p ^ (2 * u)`,
at least five distinct cofactor primes return `p` with valuation `1`. -/
theorem even_index_five_le_S1_card {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    5 ≤ (s.primeFactors.filter (v · = 1)).card := by
  intro v
  let S₁ := s.primeFactors.filter (v · = 1)
  let l (r : ℕ) := 2 * s.factorization r + 1
  have hS1_ge4 : 4 ≤ S₁.card := even_index_four_le_S1_card hp hpo hs hu hσq hplus hσs
  change 4 ≤ S₁.card at hS1_ge4
  by_contra! hlt5
  change S₁.card < 5 at hlt5
  have hcard4 : S₁.card = 4 := by omega
  let f := S₁.orderEmbOfFin hcard4
  let r₁ := f ⟨0, by decide⟩
  let r₂ := f ⟨1, by decide⟩
  let r₃ := f ⟨2, by decide⟩
  let r₄ := f ⟨3, by decide⟩
  have hr₁S : r₁ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard4 _
  have hr₂S : r₂ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard4 _
  have hr₃S : r₃ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard4 _
  have hr₄S : r₄ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard4 _
  have hr₁₂ : r₁ < r₂ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₂₃ : r₂ < r₃ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₃₄ : r₃ < r₄ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hS1_eq : S₁ = {r₁, r₂, r₃, r₄} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    · rw [hcard4, Finset.card_insert_of_notMem (by simp; omega),
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
  have he₃₄ : s.factorization r₄ < s.factorization r₃ :=
    exp_anti_of_sigma_eq hr₃p hr₄p hr₃₄ he₃pos hσr₃ hσr₄
  have he₂₃ : s.factorization r₃ < s.factorization r₂ :=
    exp_anti_of_sigma_eq hr₂p hr₃p hr₂₃ he₂pos hσr₂ hσr₃
  have he₁₂ : s.factorization r₂ < s.factorization r₁ :=
    exp_anti_of_sigma_eq hr₁p hr₂p hr₁₂ he₁pos hσr₁ hσr₂
  obtain ⟨hlt_L, hp_dvd_A, _⟩ :=
    even_index_A_pos_and_quotient_modEq hp hpo hs hu hσq hplus hσs
  have hle_p : p ≤ (∑ r ∈ S₁, 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t) -
      ∏ r ∈ S₁, l r :=
    Nat.le_of_dvd (Nat.sub_pos_of_lt hlt_L) hp_dvd_A
  have hL_eq : (∑ r ∈ S₁, 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t) -
      ∏ r ∈ S₁, l r =
      4 * s.factorization r₁ * (r₁ - 1) * l r₂ * l r₃ * l r₄ +
      4 * s.factorization r₂ * (r₂ - 1) * l r₁ * l r₃ * l r₄ +
      4 * s.factorization r₃ * (r₃ - 1) * l r₁ * l r₂ * l r₄ +
      4 * s.factorization r₄ * (r₄ - 1) * l r₁ * l r₂ * l r₃ -
      l r₁ * l r₂ * l r₃ * l r₄ := by
    rw [hS1_eq]
    have h1n : r₁ ∉ ({r₂, r₃, r₄} : Finset ℕ) := by simp; omega
    have h2n : r₂ ∉ ({r₁, r₃, r₄} : Finset ℕ) := by simp; omega
    have h3n : r₃ ∉ ({r₁, r₂, r₄} : Finset ℕ) := by simp; omega
    have h4n : r₄ ∉ ({r₁, r₂, r₃} : Finset ℕ) := by simp; omega
    have he1 : ({r₁, r₂, r₃, r₄} : Finset ℕ).erase r₁ = {r₂, r₃, r₄} := Finset.erase_insert h1n
    have he2 : ({r₁, r₂, r₃, r₄} : Finset ℕ).erase r₂ = {r₁, r₃, r₄} := by
      rw [Finset.insert_comm r₁ r₂]; exact Finset.erase_insert h2n
    have he3 : ({r₁, r₂, r₃, r₄} : Finset ℕ).erase r₃ = {r₁, r₂, r₄} := by
      rw [Finset.insert_comm r₂ r₃, Finset.insert_comm r₁ r₃]
      exact Finset.erase_insert h3n
    have he4 : ({r₁, r₂, r₃, r₄} : Finset ℕ).erase r₄ = {r₁, r₂, r₃} := by
      rw [Finset.pair_comm r₃ r₄, Finset.insert_comm r₂ r₄, Finset.insert_comm r₁ r₄]
      exact Finset.erase_insert h4n
    have hsum_eq : (∑ r ∈ ({r₁, r₂, r₃, r₄} : Finset ℕ),
          4 * s.factorization r * (r - 1) * ∏ t ∈ ({r₁, r₂, r₃, r₄} : Finset ℕ).erase r, l t) =
        4 * s.factorization r₁ * (r₁ - 1) * l r₂ * l r₃ * l r₄ +
        4 * s.factorization r₂ * (r₂ - 1) * l r₁ * l r₃ * l r₄ +
        4 * s.factorization r₃ * (r₃ - 1) * l r₁ * l r₂ * l r₄ +
        4 * s.factorization r₄ * (r₄ - 1) * l r₁ * l r₂ * l r₃ := by
      rw [Finset.sum_insert h1n, Finset.sum_insert (by simp; omega), Finset.sum_pair (by omega),
        he1, he2, he3, he4,
        Finset.prod_insert (by simp; omega), Finset.prod_pair (by omega),
        Finset.prod_insert (by simp; omega), Finset.prod_pair (by omega),
        Finset.prod_insert (by simp; omega), Finset.prod_pair (by omega),
        Finset.prod_insert (by simp; omega), Finset.prod_pair (by omega)]
      ring
    have hprod_eq : (∏ r ∈ ({r₁, r₂, r₃, r₄} : Finset ℕ), l r) = l r₁ * l r₂ * l r₃ * l r₄ := by
      rw [Finset.prod_insert h1n, Finset.prod_insert (by simp; omega), Finset.prod_pair (by omega)]
      ring
    rw [hsum_eq, hprod_eq]
  rw [hL_eq] at hle_p
  exact refute_card_four_arith hp hr₁p hr₁o hr₂p hr₃p hr₄p he₄pos he₃₄ he₂₃ he₁₂
    hr₁₂ hr₂₃ hr₃₄ hl₁p hl₂p hl₃p hl₄p (hdvd_pred r₂ hr₂S) hσr₁ hσr₄ hle_p

/-- Every even prime-power component index `p ^ (2 * u)` forces at least five
simultaneous odd-prime-base repunit representations of `p`. -/
theorem even_index_forces_five_repunits {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    HasFiveOddPrimeRepunits p := by
  let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
  let S₁ := s.primeFactors.filter (v · = 1)
  have hS1_ge5 : 5 ≤ S₁.card := even_index_five_le_S1_card hp hpo hs hu hσq hplus hσs
  let f := S₁.orderEmbOfFin (rfl : S₁.card = S₁.card)
  let r₁ := f ⟨0, by omega⟩
  let r₂ := f ⟨1, by omega⟩
  let r₃ := f ⟨2, by omega⟩
  let r₄ := f ⟨3, by omega⟩
  let r₅ := f ⟨4, by omega⟩
  have hr₁S : r₁ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₂S : r₂ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₃S : r₃ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₄S : r₄ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₅S : r₅ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₁₂ : r₁ < r₂ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₂₃ : r₂ < r₃ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₃₄ : r₃ < r₄ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₄₅ : r₄ < r₅ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
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
  exact ⟨r₁, r₂, r₃, r₄, r₅,
    2 * s.factorization r₁ + 1, 2 * s.factorization r₂ + 1, 2 * s.factorization r₃ + 1,
    2 * s.factorization r₄ + 1, 2 * s.factorization r₅ + 1,
    hr₁p, hr₁o, hr₂p, hr₂o, hr₃p, hr₃o, hr₄p, hr₄o, hr₅p, hr₅o,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    hl₁p, hl₁_gt2, hl₂p, hl₂_gt2, hl₃p, hl₃_gt2, hl₄p, hl₄_gt2, hl₅p, hl₅_gt2,
    hgr₁, hgr₂, hgr₃, hgr₄, hgr₅⟩

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

private lemma even_index_S1_ssubset_primeFactors {q p s u : ℕ}
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
`p` has at least five simultaneous odd-prime-base repunit representations and `N` has
at least 8 distinct prime factors. -/
theorem even_prime_power_component_forces_five_repunits_and_eight_primes {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    HasFiveOddPrimeRepunits p ∧ 8 ≤ N.primeFactors.card := by
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
  have hfive := even_index_forces_five_repunits hp hpo hso hu hσ hplus hσs
  have hS1_ge5 := even_index_five_le_S1_card hp hpo hso hu hσ hplus hσs
  have hS1_ssub := even_index_S1_ssubset_primeFactors hp hso hu hσ hplus hσs
  have hs_ge6 : 6 ≤ s.primeFactors.card := by
    have := Finset.card_lt_card hS1_ssub
    omega
  have hn := prime_count_of_even_index_split hq hp hmo hso hu hqm hcop hform hms
  exact ⟨hfive, by omega⟩

/-- At any even prime-power component index `i = p ^ (2 * u)`, `5 ≤ S₁.card` combined with
`∏ r ∈ S₁, r ∣ u + 1` and the repunit representations forces `15014 ≤ u`, `30028 ≤ 2 * u`,
`31381059609 ≤ p`, and `10 ^ 300280 < p ^ (2 * u)`. -/
theorem even_index_exponent_ge_30028 {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    15014 ≤ u ∧ 30028 ≤ 2 * u ∧ 31381059609 ≤ p ∧ 10 ^ 300280 < p ^ (2 * u) := by
  let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
  let S₁ := s.primeFactors.filter (v · = 1)
  have hS1_ge5 : 5 ≤ S₁.card := even_index_five_le_S1_card hp hpo hs hu hσq hplus hσs
  let f := S₁.orderEmbOfFin (rfl : S₁.card = S₁.card)
  let r₁ := f ⟨0, by omega⟩
  let r₂ := f ⟨1, by omega⟩
  let r₃ := f ⟨2, by omega⟩
  let r₄ := f ⟨3, by omega⟩
  let r₅ := f ⟨4, by omega⟩
  have hr₁S : r₁ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₂S : r₂ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₃S : r₃ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₄S : r₄ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₅S : r₅ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₁₂ : r₁ < r₂ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₂₃ : r₂ < r₃ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₃₄ : r₃ < r₄ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₄₅ : r₄ < r₅ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
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
  obtain ⟨hr₅p, hr₅o, he₅pos, hl₅p, hσr₅⟩ := extract r₅ hr₅S
  have hr₁_mod : r₁ % 2 = 1 := Nat.odd_iff.mp hr₁o
  have hr₁_ge3 : 3 ≤ r₁ := by have := hr₁p.two_le; omega
  have hr₂_ge5 : 5 ≤ r₂ := by have := Nat.odd_iff.mp hr₂o; omega
  have hr₃_ge7 : 7 ≤ r₃ := by have := Nat.odd_iff.mp hr₃o; omega
  have hr₄_ge11 : 11 ≤ r₄ := by
    have := Nat.odd_iff.mp hr₄o
    have h9 : r₄ ≠ 9 := by intro h9; rw [h9] at hr₄p; exact absurd hr₄p (by decide)
    omega
  have hr₅_ge13 : 13 ≤ r₅ := by have := Nat.odd_iff.mp hr₅o; omega
  have hprod_dvd : (∏ r ∈ S₁, r) ∣ u + 1 :=
    (even_index_S1_exact_mod_sq hp hs hσq hplus hσs).2
  have hprod_le : ∏ r ∈ S₁, r ≤ u + 1 := Nat.le_of_dvd (by omega) hprod_dvd
  have hsub5 : ({r₁, r₂, r₃, r₄, r₅} : Finset ℕ) ⊆ S₁ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hprod5_dvd : (∏ r ∈ ({r₁, r₂, r₃, r₄, r₅} : Finset ℕ), r) ∣ ∏ r ∈ S₁, r :=
    Finset.prod_dvd_prod_of_subset _ _ id hsub5
  have hprod5_eq : (∏ r ∈ ({r₁, r₂, r₃, r₄, r₅} : Finset ℕ), r) = r₁ * r₂ * r₃ * r₄ * r₅ := by
    rw [Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
      Finset.prod_insert (by simp; omega), Finset.prod_pair (by omega)]
    ring
  have hprod5_le : r₁ * r₂ * r₃ * r₄ * r₅ ≤ ∏ r ∈ S₁, r := by
    rw [← hprod5_eq]
    exact Nat.le_of_dvd (Finset.prod_pos fun r hr =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1).pos) hprod5_dvd
  have h15015 : 15015 ≤ r₁ * r₂ * r₃ * r₄ * r₅ := by
    calc 15015 = 3 * 5 * 7 * 11 * 13 := by norm_num
      _ ≤ r₁ * r₂ * r₃ * r₄ * r₅ := by gcongr
  have hu_ge : 15014 ≤ u := by omega
  have hp_ge : 31381059609 ≤ p := by
    have he₄₅ : s.factorization r₅ < s.factorization r₄ :=
      exp_anti_of_sigma_eq hr₄p hr₅p hr₄₅ he₄pos hσr₄ hσr₅
    have he₃₄ : s.factorization r₄ < s.factorization r₃ :=
      exp_anti_of_sigma_eq hr₃p hr₄p hr₃₄ he₃pos hσr₃ hσr₄
    have he₂₃ : s.factorization r₃ < s.factorization r₂ :=
      exp_anti_of_sigma_eq hr₂p hr₃p hr₂₃ he₂pos hσr₂ hσr₃
    have he₁₂ : s.factorization r₂ < s.factorization r₁ :=
      exp_anti_of_sigma_eq hr₁p hr₂p hr₁₂ he₁pos hσr₁ hσr₂
    have he₁_ge6 : 6 ≤ s.factorization r₁ := by
      have hnot9 : 2 * s.factorization r₂ + 1 ≠ 9 := by
        intro h9; rw [h9] at hl₂p; exact absurd hl₂p (by decide)
      omega
    have hpow_lt_p : r₁ ^ (2 * s.factorization r₁) < p := by
      rw [← hσr₁]
      exact self_lt_sigma_of_one_lt (one_lt_pow₀ hr₁p.one_lt (by omega))
    by_cases he₁_ge11 : 11 ≤ s.factorization r₁
    · have h3_22 : (3 : ℕ) ^ 22 ≤ r₁ ^ (2 * s.factorization r₁) :=
        (Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 22 ≤ 2 * s.factorization r₁)).trans
          (Nat.pow_le_pow_left hr₁_ge3 (2 * s.factorization r₁))
      have hval : (3 : ℕ) ^ 22 = 31381059609 := by norm_num
      omega
    · have hcases : s.factorization r₁ = 6 ∨ s.factorization r₁ = 7 ∨
          s.factorization r₁ = 8 ∨ s.factorization r₁ = 9 ∨ s.factorization r₁ = 10 := by omega
      rcases hcases with he1 | he1 | he1 | he1 | he1
      · -- e₁ = 6, l₁ = 13, so l₂ = 11 (e₂ = 5)
        have he₂_eq5 : s.factorization r₂ = 5 := by
          have hnot9 : 2 * s.factorization r₂ + 1 ≠ 9 := by
            intro h9; rw [h9] at hl₂p; exact absurd hl₂p (by decide)
          omega
        have hdvd11 : 11 ∣ (p - 1) / 2 := by
          have H := (even_index_repunit_lengths_dvd_pred hp hpo hs hσq hplus hσs).1 r₂ hr₂S
          rw [he₂_eq5] at H
          exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) (by
            have hp_pred : 2 * ((p - 1) / 2) = p - 1 := by
              have := Nat.odd_iff.mp hpo; omega
            simpa only [hp_pred] using H)
        by_cases hr₁_ge11 : 11 ≤ r₁
        · have h11 : (11 : ℕ) ^ 12 ≤ r₁ ^ (2 * s.factorization r₁) := by
            rw [he1]; exact Nat.pow_le_pow_left hr₁_ge11 12
          have hbig : 31381059609 < (11 : ℕ) ^ 12 := by norm_num
          omega
        · have hr₁_cases : r₁ = 3 ∨ r₁ = 5 ∨ r₁ = 7 ∨ r₁ = 9 := by
            have := Nat.odd_iff.mp hr₁o; omega
          rcases hr₁_cases with hr1 | hr1 | hr1 | hr1
          · rw [← hσr₁, he1, hr1, show 2 * 6 = 12 by rfl,
              sigma_one_apply_prime_pow (by decide : Nat.Prime 3)] at hdvd11
            norm_num [Finset.sum_range_succ] at hdvd11
          · rw [← hσr₁, he1, hr1, show 2 * 6 = 12 by rfl,
              sigma_one_apply_prime_pow (by decide : Nat.Prime 5)] at hdvd11
            norm_num [Finset.sum_range_succ] at hdvd11
          · rw [← hσr₁, he1, hr1, show 2 * 6 = 12 by rfl,
              sigma_one_apply_prime_pow (by decide : Nat.Prime 7)] at hdvd11
            norm_num [Finset.sum_range_succ] at hdvd11
          · rw [hr1] at hr₁p
            exact absurd hr₁p (by decide)
      · rw [he1] at hl₁p
        exact absurd hl₁p (by decide)
      · -- e₁ = 8
        by_cases hr₁_ge7 : 7 ≤ r₁
        · have h7 : (7 : ℕ) ^ 16 ≤ r₁ ^ (2 * s.factorization r₁) := by
            rw [he1]; exact Nat.pow_le_pow_left hr₁_ge7 16
          have hbig : 31381059609 < (7 : ℕ) ^ 16 := by norm_num
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
          have hbig : 31381059609 < (7 : ℕ) ^ 18 := by norm_num
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
  have hp_gt10 : 10 ^ 10 < p := lt_of_lt_of_le (by norm_num : 10 ^ 10 < 31381059609) hp_ge
  have hpow_gt : 10 ^ 300280 < p ^ (2 * u) := by
    obtain ⟨B, hB_eq, hB_lt⟩ : ∃ B : ℕ, B = 10 ^ 10 ∧ B < p := ⟨10 ^ 10, rfl, hp_gt10⟩
    calc 10 ^ 300280 = B ^ 30028 := by
          rw [hB_eq, show 300280 = 10 * 30028 by norm_num, pow_mul]
      _ < p ^ 30028 := pow_lt_pow_left₀ hB_lt (Nat.zero_le B) (by omega)
      _ ≤ p ^ (2 * u) := pow_le_pow_right₀ hp.one_le (by omega)
  exact ⟨hu_ge, by omega, hp_ge, hpow_gt⟩

/-- Every prime-power component index `i = p ^ j` of an odd perfect number satisfies
`30028 ≤ j`, `10 ^ 17240 < i`, `10 ^ 17240 < N`, and `10 ^ 300280 < i ∧ 10 ^ 300280 < N`
when `j` is even. -/
theorem component_prime_power_index_exponent_ge_30028 {N q a b i p j : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b)
    (hl : sigma 1 b = q ^ a * i) (hr : sigma 1 (q ^ a) * i = 2 * b)
    (hp : p.Prime) (hj : 0 < j) (hi : i = p ^ j) :
    30028 ≤ j ∧ 10 ^ 17240 < i ∧ 10 ^ 17240 < N ∧
      (Even j → 10 ^ 300280 < i ∧ 10 ^ 300280 < N) := by
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
      even_index_exponent_ge_30028 hp hpo hs hu hσq hplus hσs
    have hi_gt : 10 ^ 300280 < i := by
      rw [hi_even]
      exact hpow_gt
    have hi_gt17240 : 10 ^ 17240 < i :=
      calc 10 ^ 17240 < 10 ^ 300280 :=
            pow_lt_pow_right₀ (by decide : 1 < 10) (by decide : 17240 < 300280)
        _ < i := hi_gt
    exact ⟨by omega, hi_gt17240, hi_gt17240.trans hi_lt_N,
      fun _ => ⟨hi_gt, hi_gt.trans hi_lt_N⟩⟩
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
    exact ⟨by omega, hi_gt, hi_gt.trans hi_lt_N,
      fun heven => False.elim ((Nat.not_even_iff_odd.mpr hj_odd) heven)⟩

/-- Subexponential coupling on the single-copy repunit primes `S₁` at an even prime-power
component index `i = p ^ (2 * u)`. -/
theorem even_index_repunit_product_le_subexponential {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    let S₁ := s.primeFactors.filter (v · = 1)
    (∏ r ∈ S₁, r) ≤ u + 1 ∧
      2 * (∏ r ∈ S₁, (2 * s.factorization r + 1)) < 8 * (u + 1) * 128 ^ (2 * u).sqrt ∧
      3 ^ S₁.card < 4 * (u + 1) * 128 ^ (2 * u).sqrt := by
  intro v S₁
  have hprod_r : ∏ r ∈ S₁, r ≤ u + 1 :=
    Nat.le_of_dvd (by omega) (even_index_S1_exact_mod_sq hp hs hσq hplus hσs).2
  have hp3 : 3 ≤ p := by have := hp.two_le; have := Nat.odd_iff.mp hpo; omega
  have hhalf_pos : 0 < (p - 1) / 2 := by omega
  have hprod_l_le : ∏ r ∈ S₁, (2 * s.factorization r + 1) ≤ (p - 1) / 2 :=
    Nat.le_of_dvd hhalf_pos (even_index_repunit_lengths_dvd_pred hp hpo hs hσq hplus hσs).2
  have hsub := even_index_base_subexponential hp hpo hs hu hσq hplus hσs
  have h2_prod_lt : 2 * (∏ r ∈ S₁, (2 * s.factorization r + 1)) < 8 * (u + 1) * 128 ^ (2 * u).sqrt := by
    calc 2 * (∏ r ∈ S₁, (2 * s.factorization r + 1))
        ≤ 2 * ((p - 1) / 2) := Nat.mul_le_mul_left 2 hprod_l_le
      _ ≤ p - 1 := Nat.mul_div_le (p - 1) 2
      _ < p := by omega
      _ ≤ 8 * (u + 1) * 128 ^ (2 * u).sqrt := hsub
  have h3_le_prod : 3 ^ S₁.card ≤ ∏ r ∈ S₁, (2 * s.factorization r + 1) := by
    calc 3 ^ S₁.card = ∏ _r ∈ S₁, 3 := by simp
      _ ≤ ∏ r ∈ S₁, (2 * s.factorization r + 1) :=
        Finset.prod_le_prod fun r hrS => by
          have hr := (Finset.mem_filter.mp hrS).1
          have hrp := Nat.prime_of_mem_primeFactors hr
          have he : 1 ≤ s.factorization r :=
            (hrp.dvd_iff_one_le_factorization hs.pos.ne').mp (Nat.dvd_of_mem_primeFactors hr)
          omega
  have h3_lt : 3 ^ S₁.card < 4 * (u + 1) * 128 ^ (2 * u).sqrt := by
    have h2_3 : 2 * 3 ^ S₁.card < 8 * (u + 1) * 128 ^ (2 * u).sqrt :=
      lt_of_le_of_lt (Nat.mul_le_mul_left 2 h3_le_prod) h2_prod_lt
    have h_eq : 8 * (u + 1) * 128 ^ (2 * u).sqrt = 2 * (4 * (u + 1) * 128 ^ (2 * u).sqrt) := by ring
    rw [h_eq] at h2_3
    omega
  exact ⟨hprod_r, h2_prod_lt, h3_lt⟩

end OddPerfect
