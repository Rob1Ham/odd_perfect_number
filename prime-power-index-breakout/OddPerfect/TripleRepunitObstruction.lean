module

public import OddPerfect.PrimePowerObstruction
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- The same integer has prime-length repunit representations in three
distinct odd prime bases. -/
@[expose] def HasThreeOddPrimeRepunits (z : ℕ) : Prop :=
  ∃ r₁ r₂ r₃ l₁ l₂ l₃ : ℕ,
    r₁.Prime ∧ Odd r₁ ∧ r₂.Prime ∧ Odd r₂ ∧ r₃.Prime ∧ Odd r₃ ∧
    r₁ ≠ r₂ ∧ r₁ ≠ r₃ ∧ r₂ ≠ r₃ ∧
    l₁.Prime ∧ 2 < l₁ ∧ l₂.Prime ∧ 2 < l₂ ∧ l₃.Prime ∧ 2 < l₃ ∧
    geometricBlock r₁ l₁ = z ∧ geometricBlock r₂ l₂ = z ∧ geometricBlock r₃ l₃ = z

private lemma add_pow_of_sq_eq_zero {R : Type*} [CommRing R] (a b : R) (hb : b ^ 2 = 0) :
    ∀ m : ℕ, 1 ≤ m → (a + b) ^ m = a ^ m + (m : R) * a ^ (m - 1) * b := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    rcases eq_or_ne m 0 with rfl | hm0
    · simp
    · have ih' := ih (by omega)
      rw [pow_succ, ih']
      simp only [Nat.add_sub_cancel]
      have hsucc : m - 1 + 1 = m := by omega
      have hpow : a * a ^ (m - 1) = a ^ m := by rw [← pow_succ', hsucc]
      push_cast
      calc (a ^ m + (m : R) * a ^ (m - 1) * b) * (a + b)
          = a ^ m * a + (a ^ m + (m : R) * (a * a ^ (m - 1))) * b + (m : R) * a ^ (m - 1) * b ^ 2 := by
            ring
        _ = a ^ (m + 1) + ((m : R) + 1) * a ^ m * b := by
            rw [hpow, hb, mul_zero, add_zero, ← pow_succ]; ring

private lemma linear_lt_even_pow {r e : ℕ} (hr : 3 ≤ r) (he : 2 ≤ e) :
    4 * e * r ≤ r ^ (2 * e) := by
  induction e, he using Nat.le_induction with
  | base =>
    have h1 : 8 ≤ r ^ 3 := by
      rw [show r ^ 3 = r * r * r by ring]
      nlinarith
    calc 4 * 2 * r = 8 * r := by ring
      _ ≤ r ^ 3 * r := Nat.mul_le_mul_right r h1
      _ = r ^ (2 * 2) := by ring
  | succ k hk ih =>
    have h2 : 2 * (k + 1) ≤ 4 * k := by omega
    have h9 : 9 ≤ r ^ 2 := by rw [pow_two]; nlinarith
    calc 4 * (k + 1) * r ≤ 2 * (4 * k * r) := by nlinarith
      _ ≤ 2 * r ^ (2 * k) := Nat.mul_le_mul_left 2 ih
      _ ≤ r ^ 2 * r ^ (2 * k) := Nat.mul_le_mul_right _ (by omega)
      _ = r ^ (2 * (k + 1)) := by ring

private lemma sixteen_mul_odd_pow4_le_three_pow {e : ℕ} (he : 6 ≤ e) :
    16 * (2 * e + 1) ^ 4 ≤ 3 ^ (2 * e) := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hsq : (2 * (k + 1) + 1) ^ 2 ≤ 3 * (2 * k + 1) ^ 2 := by nlinarith
    have hpow4 : (2 * (k + 1) + 1) ^ 4 ≤ 9 * (2 * k + 1) ^ 4 := by
      calc (2 * (k + 1) + 1) ^ 4 = ((2 * (k + 1) + 1) ^ 2) ^ 2 := by ring
        _ ≤ (3 * (2 * k + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left hsq 2
        _ = 9 * (2 * k + 1) ^ 4 := by ring
    calc 16 * (2 * (k + 1) + 1) ^ 4
        ≤ 9 * (16 * (2 * k + 1) ^ 4) := by nlinarith
      _ ≤ 9 * 3 ^ (2 * k) := Nat.mul_le_mul_left 9 ih
      _ = 3 ^ (2 * (k + 1)) := by ring

private lemma sigma_prime_pow_strictMono_exp {r a b : ℕ} (hr : r.Prime) (hab : a < b) :
    sigma 1 (r ^ a) < sigma 1 (r ^ b) := by
  rw [sigma_one_apply_prime_pow hr, sigma_one_apply_prime_pow hr]
  have hsub : range (a + 1) ⊆ range b := Finset.range_mono (by omega : a + 1 ≤ b)
  have hle : ∑ j ∈ range (a + 1), r ^ j ≤ ∑ j ∈ range b, r ^ j :=
    Finset.sum_le_sum_of_subset hsub
  have hlt : ∑ j ∈ range b, r ^ j < ∑ j ∈ range (b + 1), r ^ j := by
    rw [Finset.sum_range_succ]
    have hpos : 0 < r ^ b := pow_pos hr.pos b
    omega
  exact Nat.lt_of_le_of_lt hle hlt

private lemma sigma_prime_pow_lt_of_base_lt {a b e : ℕ} (ha : a.Prime) (hb : b.Prime)
    (hab : a < b) (he : 0 < e) : sigma 1 (a ^ e) < sigma 1 (b ^ e) := by
  rw [sigma_one_apply_prime_pow ha, sigma_one_apply_prime_pow hb]
  exact Finset.sum_lt_sum (fun j _ => Nat.pow_le_pow_left hab.le j)
    ⟨1, Finset.mem_range.mpr (by omega), by simpa using hab⟩

private lemma refute_card_two_arith {p r₁ r₂ e₁ e₂ : ℕ}
    (hp : p.Prime) (hr₁p : r₁.Prime) (hr₁o : Odd r₁) (hr₂p : r₂.Prime)
    (he₂ : 1 ≤ e₂) (he_lt : e₂ < e₁) (hr₁_lt_r₂ : r₁ < r₂)
    (hl₁p : (2 * e₁ + 1).Prime) (hl₂p : (2 * e₂ + 1).Prime)
    (hσr₁ : sigma 1 (r₁ ^ (2 * e₁)) = p) (hσr₂ : sigma 1 (r₂ ^ (2 * e₂)) = p)
    (hle_p : p ≤ 4 * e₁ * (r₁ - 1) * (2 * e₂ + 1) + 4 * e₂ * (r₂ - 1) * (2 * e₁ + 1) -
      (2 * e₁ + 1) * (2 * e₂ + 1)) : False := by
  have he₁ : 2 ≤ e₁ := by omega
  have hr₁_mod : r₁ % 2 = 1 := Nat.odd_iff.mp hr₁o
  have hr₁_ge3 : 3 ≤ r₁ := by have := hr₁p.two_le; omega
  let l₁ := 2 * e₁ + 1
  let l₂ := 2 * e₂ + 1
  let L := 4 * e₁ * (r₁ - 1) * l₂ + 4 * e₂ * (r₂ - 1) * l₁ - l₁ * l₂
  have hle_p' : p ≤ L := hle_p
  have hL_lt_prod : L < 4 * l₁ * l₂ * r₂ := by
    have hsub1 : r₁ - 1 ≤ r₁ := by omega
    have hsub2 : r₂ - 1 ≤ r₂ := by omega
    have h1 : 4 * e₁ * (r₁ - 1) * l₂ ≤ 4 * e₁ * r₁ * l₂ :=
      Nat.mul_le_mul_right l₂ (Nat.mul_le_mul_left (4 * e₁) hsub1)
    have h2 : 4 * e₂ * (r₂ - 1) * l₁ ≤ 4 * e₂ * r₂ * l₁ :=
      Nat.mul_le_mul_right l₁ (Nat.mul_le_mul_left (4 * e₂) hsub2)
    have h3 : 4 * e₁ * r₁ * l₂ < 2 * l₁ * l₂ * r₂ := by
      have h3a : 4 * e₁ * r₁ < 2 * l₁ * r₂ := by
        calc 4 * e₁ * r₁ < 2 * l₁ * r₁ := Nat.mul_lt_mul_of_pos_right (by dsimp [l₁]; omega) hr₁p.pos
          _ < 2 * l₁ * r₂ := Nat.mul_lt_mul_of_pos_left hr₁_lt_r₂ (by positivity)
      calc 4 * e₁ * r₁ * l₂ < 2 * l₁ * r₂ * l₂ :=
            Nat.mul_lt_mul_of_pos_right h3a (by dsimp [l₂]; omega)
        _ = 2 * l₁ * l₂ * r₂ := by ring
    have h4 : 4 * e₂ * r₂ * l₁ < 2 * l₁ * l₂ * r₂ := by
      have h4a : 4 * e₂ * r₂ < 2 * l₂ * r₂ :=
        Nat.mul_lt_mul_of_pos_right (by dsimp [l₂]; omega) hr₂p.pos
      calc 4 * e₂ * r₂ * l₁ < 2 * l₂ * r₂ * l₁ :=
            Nat.mul_lt_mul_of_pos_right h4a (by dsimp [l₁]; omega)
        _ = 2 * l₁ * l₂ * r₂ := by ring
    calc L ≤ 4 * e₁ * (r₁ - 1) * l₂ + 4 * e₂ * (r₂ - 1) * l₁ := Nat.sub_le _ _
      _ ≤ 4 * e₁ * r₁ * l₂ + 4 * e₂ * r₂ * l₁ := Nat.add_le_add h1 h2
      _ < 2 * l₁ * l₂ * r₂ + 2 * l₁ * l₂ * r₂ := Nat.add_lt_add h3 h4
      _ = 4 * l₁ * l₂ * r₂ := by ring
  have hr₂_sq_lt_p : r₂ ^ 2 < p := by
    have hrange : range 3 ⊆ range (2 * e₂ + 1) := Finset.range_mono (by omega : 3 ≤ 2 * e₂ + 1)
    have hsum3 : 1 + r₂ + r₂ ^ 2 ≤ sigma 1 (r₂ ^ (2 * e₂)) := by
      rw [sigma_one_apply_prime_pow hr₂p]
      calc 1 + r₂ + r₂ ^ 2 = ∑ j ∈ range 3, r₂ ^ j := by
            simp [Finset.sum_range_succ, Nat.add_assoc]
        _ ≤ ∑ j ∈ range (2 * e₂ + 1), r₂ ^ j := Finset.sum_le_sum_of_subset hrange
    rw [hσr₂] at hsum3
    omega
  have hr₁_pow_lt_p : r₁ ^ (2 * e₁) < p := by
    rw [← hσr₁]
    exact self_lt_sigma_of_one_lt (one_lt_pow₀ hr₁p.one_lt (by omega))
  by_cases hr₂_big : 4 * l₁ * l₂ ≤ r₂
  · have : L < r₂ ^ 2 := by
      calc L < 4 * l₁ * l₂ * r₂ := hL_lt_prod
        _ ≤ r₂ * r₂ := Nat.mul_le_mul_right r₂ hr₂_big
        _ = r₂ ^ 2 := by ring
    omega
  · have hr₂_lt : r₂ < 4 * l₁ * l₂ := by omega
    have hL_lt_sq : L < (4 * l₁ * l₂) ^ 2 := by
      have : 4 * l₁ * l₂ * r₂ < 4 * l₁ * l₂ * (4 * l₁ * l₂) :=
        Nat.mul_lt_mul_of_pos_left hr₂_lt (by positivity)
      calc L < 4 * l₁ * l₂ * r₂ := hL_lt_prod
        _ < 4 * l₁ * l₂ * (4 * l₁ * l₂) := this
        _ = (4 * l₁ * l₂) ^ 2 := by ring
    by_cases he₁_big : 6 ≤ e₁
    · have hl₂_lt_l₁ : l₂ < l₁ := by dsimp [l₁, l₂]; omega
      have hL_lt_16 : L < 16 * l₁ ^ 4 := by
        have hl₂_sq : l₂ ^ 2 < l₁ ^ 2 := Nat.pow_lt_pow_left hl₂_lt_l₁ (by decide : 2 ≠ 0)
        have hpow : (4 * l₁ * l₂) ^ 2 < 16 * l₁ ^ 4 := by
          calc (4 * l₁ * l₂) ^ 2 = 16 * l₁ ^ 2 * l₂ ^ 2 := by ring
            _ < 16 * l₁ ^ 2 * l₁ ^ 2 := Nat.mul_lt_mul_of_pos_left hl₂_sq (by positivity)
            _ = 16 * l₁ ^ 4 := by ring
        omega
      have h16 := sixteen_mul_odd_pow4_le_three_pow he₁_big
      have h3_le : 3 ^ (2 * e₁) ≤ r₁ ^ (2 * e₁) := Nat.pow_le_pow_left hr₁_ge3 (2 * e₁)
      change L < 16 * (2 * e₁ + 1) ^ 4 at hL_lt_16
      omega
    · rcases (by omega : e₁ = 2 ∨ e₁ = 3 ∨ e₁ = 4 ∨ e₁ = 5) with rfl | rfl | rfl | rfl
      · -- e₁ = 2, l₁ = 5
        have he₂_eq : e₂ = 1 := by omega
        subst he₂_eq
        change L < (4 * (2 * 2 + 1) * (2 * 1 + 1)) ^ 2 at hL_lt_sq
        norm_num at hL_lt_sq
        by_cases hr₁_ge11 : 11 ≤ r₁
        · have h11 : (11 : ℕ) ^ (2 * 2) = 14641 := by norm_num
          have : 14641 ≤ r₁ ^ (2 * 2) := h11 ▸ Nat.pow_le_pow_left hr₁_ge11 (2 * 2)
          omega
        · rcases (by omega : r₁ = 3 ∨ r₁ = 5 ∨ r₁ = 7 ∨ r₁ = 9) with rfl | rfl | rfl | rfl
          · rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
            norm_num [Finset.sum_range_succ] at hσr₁
            rw [← hσr₁] at hp
            have hdiv : 11 ∣ 121 := by norm_num
            have := hp.eq_one_or_self_of_dvd 11 hdiv
            omega
          · rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
            norm_num [Finset.sum_range_succ] at hσr₁
            rw [← hσr₁] at hp
            have hdiv : 11 ∣ 781 := by norm_num
            have := hp.eq_one_or_self_of_dvd 11 hdiv
            omega
          · rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
            norm_num [Finset.sum_range_succ] at hσr₁
            have hσr₂_val : 1 + r₂ + r₂ ^ 2 = 2801 := by
              rw [hσr₁, ← hσr₂, mul_one, sigma_one_apply_prime_pow hr₂p]
              simp [Finset.sum_range_succ, Nat.add_assoc]
            by_cases hr₂_le : r₂ ≤ 52 <;> nlinarith
          · exact absurd hr₁p (by decide)
      · -- e₁ = 3, l₁ = 7
        have hL_bound : L < 19600 := by
          have hl₁_val : l₁ = 7 := rfl
          have hl₂_le : l₂ ≤ 5 := by dsimp [l₂]; omega
          have hmul : 4 * l₁ * l₂ ≤ 140 := by
            calc 4 * l₁ * l₂ = 4 * 7 * l₂ := by rw [hl₁_val]
              _ ≤ 140 := by omega
          have hsq : (4 * l₁ * l₂) ^ 2 ≤ 19600 :=
            (Nat.pow_le_pow_left hmul 2).trans (by norm_num)
          omega
        by_cases hr₁_ge7 : 7 ≤ r₁
        · have h7 : (7 : ℕ) ^ (2 * 3) = 117649 := by norm_num
          have : 117649 ≤ r₁ ^ (2 * 3) := h7 ▸ Nat.pow_le_pow_left hr₁_ge7 (2 * 3)
          omega
        · rcases (by omega : r₁ = 3 ∨ r₁ = 5) with rfl | rfl
          · rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
            norm_num [Finset.sum_range_succ] at hσr₁
            rcases (by omega : e₂ = 1 ∨ e₂ = 2) with rfl | rfl
            · have hσr₂_val : 1 + r₂ + r₂ ^ 2 = 1093 := by
                rw [hσr₁, ← hσr₂, mul_one, sigma_one_apply_prime_pow hr₂p]
                simp [Finset.sum_range_succ, Nat.add_assoc]
              by_cases hr₂_le : r₂ ≤ 32 <;> nlinarith
            · have hσr₂_val : 1 + r₂ + r₂ ^ 2 + r₂ ^ 3 + r₂ ^ 4 = 1093 := by
                rw [hσr₁, ← hσr₂, sigma_one_apply_prime_pow hr₂p]
                simp [Finset.sum_range_succ, Nat.add_assoc]
              by_cases hr₂_le5 : r₂ ≤ 5
              · have hle5 : 1 + r₂ + r₂ ^ 2 + r₂ ^ 3 + r₂ ^ 4 ≤ 1 + 5 + 5 ^ 2 + 5 ^ 3 + 5 ^ 4 := by
                  gcongr
                omega
              · have hge6 : 6 ≤ r₂ := by omega
                have : 6 ^ 4 ≤ r₂ ^ 4 := Nat.pow_le_pow_left hge6 4
                norm_num at this
                omega
          · rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
            norm_num [Finset.sum_range_succ] at hσr₁
            rcases (by omega : e₂ = 1 ∨ e₂ = 2) with rfl | rfl
            · have hσr₂_val : 1 + r₂ + r₂ ^ 2 = 19531 := by
                rw [hσr₁, ← hσr₂, mul_one, sigma_one_apply_prime_pow hr₂p]
                simp [Finset.sum_range_succ, Nat.add_assoc]
              by_cases hr₂_le : r₂ ≤ 139 <;> nlinarith
            · have hσr₂_val : 1 + r₂ + r₂ ^ 2 + r₂ ^ 3 + r₂ ^ 4 = 19531 := by
                rw [hσr₁, ← hσr₂, sigma_one_apply_prime_pow hr₂p]
                simp [Finset.sum_range_succ, Nat.add_assoc]
              by_cases hr₂_le11 : r₂ ≤ 11
              · have hle11 : 1 + r₂ + r₂ ^ 2 + r₂ ^ 3 + r₂ ^ 4 ≤
                    1 + 11 + 11 ^ 2 + 11 ^ 3 + 11 ^ 4 := by
                  gcongr
                omega
              · have hge12 : 12 ≤ r₂ := by omega
                have : 12 ^ 4 ≤ r₂ ^ 4 := Nat.pow_le_pow_left hge12 4
                norm_num at this
                omega
      · -- e₁ = 4, l₁ = 9 (not prime)
        exact absurd hl₁p (by decide)
      · -- e₁ = 5, l₁ = 11
        have he₂_le : e₂ ≤ 3 := by
          by_contra! hge4
          have he₂_eq4 : e₂ = 4 := by omega
          rw [he₂_eq4] at hl₂p
          exact absurd hl₂p (by decide)
        have hL_bound : L < 94864 := by
          have hl₁_val : l₁ = 11 := rfl
          have hl₂_le : l₂ ≤ 7 := by dsimp [l₂]; omega
          have hmul : 4 * l₁ * l₂ ≤ 308 := by
            calc 4 * l₁ * l₂ = 4 * 11 * l₂ := by rw [hl₁_val]
              _ ≤ 308 := by omega
          have hsq : (4 * l₁ * l₂) ^ 2 ≤ 94864 :=
            (Nat.pow_le_pow_left hmul 2).trans (by norm_num)
          omega
        by_cases hr₁_ge5 : 5 ≤ r₁
        · have h5 : (5 : ℕ) ^ (2 * 5) = 9765625 := by norm_num
          have : 9765625 ≤ r₁ ^ (2 * 5) := h5 ▸ Nat.pow_le_pow_left hr₁_ge5 (2 * 5)
          omega
        · have hr₁_eq3 : r₁ = 3 := by omega
          subst hr₁_eq3
          rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
          norm_num [Finset.sum_range_succ] at hσr₁
          rw [← hσr₁] at hp
          have hdiv : 23 ∣ 88573 := by norm_num
          have := hp.eq_one_or_self_of_dvd 23 hdiv
          omega

private lemma even_index_three_le_S1_card {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    3 ≤ (s.primeFactors.filter (v · = 1)).card := by
  let R := ZMod (p ^ 2)
  let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
  let S₁ := s.primeFactors.filter (v · = 1)
  let T := (s ^ 2).divisors.card
  obtain ⟨_, hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  have hT_prod : T = ∏ r ∈ s.primeFactors, (2 * s.factorization r + 1) := by
    dsimp [T]
    rw [Nat.card_divisors (pow_ne_zero 2 hs.pos.ne'), Nat.primeFactors_pow s (by decide : 2 ≠ 0)]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hT_pos : 1 ≤ T := by
    dsimp [T]
    exact Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (pow_ne_zero 2 hs.pos.ne')⟩
  have hT_cop : p.Coprime T := by
    rw [hT_prod]
    apply Nat.coprime_prod_right_iff.mpr
    intro r hr
    exact hp.coprime_iff_not_dvd.mpr
      (even_index_cofactor_component_order_dvd_pred hp hpo hs hσq hplus hσs hr).2.1
  have hp2_zero : (p : R) ^ 2 = 0 := by
    change (p : ZMod (p ^ 2)) ^ 2 = 0
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hq_cast : (q : R) = 1 + (p : R) := by
    have hq_expand : q = 1 + p + p ^ 2 * ∑ j ∈ range (2 * u - 1), p ^ j := by
      rw [← hσq, sigma_one_apply_prime_pow hp, show 2 * u + 1 = (2 * u - 1) + 2 by omega,
        Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [pow_zero, pow_succ', ← Finset.mul_sum]
      ring
    have hcast := congrArg (fun n : ℕ => (n : R)) hq_expand
    push_cast at hcast
    rw [hp2_zero, zero_mul, add_zero] at hcast
    exact hcast
  have h2s2_cast : (2 : R) * (s ^ 2 : R) = 2 + (p : R) := by
    have hcast := congrArg (fun n : ℕ => (n : R)) hplus
    push_cast at hcast
    rw [hq_cast] at hcast
    linear_combination -hcast
  have hpow_T : (2 : R) ^ T * ((s ^ 2 : ℕ) : R) ^ T =
      (2 : R) ^ T + (T : R) * (2 : R) ^ (T - 1) * (p : R) := by
    calc (2 : R) ^ T * ((s ^ 2 : ℕ) : R) ^ T
        = ((2 : R) * (s ^ 2 : R)) ^ T := by push_cast; ring
      _ = (2 + (p : R)) ^ T := by rw [h2s2_cast]
      _ = (2 : R) ^ T + (T : R) * (2 : R) ^ (T - 1) * (p : R) :=
        add_pow_of_sq_eq_zero 2 (p : R) hp2_zero T hT_pos
  have hs2_prod : s ^ 2 = ∏ r ∈ s.primeFactors, r ^ (2 * s.factorization r) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization (pow_ne_zero 2 hs.pos.ne')]
    rw [Nat.primeFactors_pow s (by decide : 2 ≠ 0)]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hs2_pow_T : ((s ^ 2 : ℕ) : R) ^ T =
      ∏ r ∈ s.primeFactors, ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T := by
    conv_lhs => rw [hs2_prod]
    push_cast
    rw [Finset.prod_pow]
  have hlocal_not : ∀ r ∈ s.primeFactors, r ∉ S₁ →
      ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T = 1 := by
    intro r hr hnr
    have hvne : v r ≠ 1 := fun h => hnr (Finset.mem_filter.mpr ⟨hr, h⟩)
    obtain ⟨hvo, hσr⟩ := hparts r hr
    dsimp only at hvo hσr
    change Odd (v r) at hvo
    change sigma 1 (r ^ (2 * s.factorization r)) = p ^ v r at hσr
    have hv3 : 2 ≤ v r := by have := hvo.pos; omega
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hrel : r ^ (2 * s.factorization r + 1) = 1 + (r - 1) * p ^ (v r) := by
      rw [← hσr, sigma_one_apply_prime_pow hrp]
      zify [hrp.one_le]
      have hg := geom_sum_mul (r : ℤ) (2 * s.factorization r + 1)
      linarith
    have hrcast : ((r ^ (2 * s.factorization r + 1) : ℕ) : R) = 1 := by
      rw [hrel]
      push_cast
      have hpv : (p : R) ^ v r = 0 := by
        rw [show v r = 2 + (v r - 2) by omega, pow_add, hp2_zero, zero_mul]
      rw [hpv, mul_zero, add_zero]
    obtain ⟨Q, hTQ⟩ := (Finset.dvd_prod_of_mem (fun t => 2 * s.factorization t + 1) hr).trans
      hT_prod.symm.dvd
    calc ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T
        = ((r ^ (2 * s.factorization r) : ℕ) : R) ^ ((2 * s.factorization r + 1) * Q) := by rw [hTQ]
      _ = ((r ^ (2 * s.factorization r + 1) : ℕ) : R) ^ (2 * s.factorization r * Q) := by
        push_cast; ring
      _ = 1 ^ (2 * s.factorization r * Q) := by rw [hrcast]
      _ = 1 := one_pow _
  have hlocal_mem : ∀ r ∈ S₁,
      let Q := ∏ t ∈ s.primeFactors.erase r, (2 * s.factorization t + 1)
      ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T =
        1 + ((2 * s.factorization r * Q * (r - 1) : ℕ) : R) * (p : R) := by
    intro r hrS Q
    obtain ⟨hr, hv1⟩ := Finset.mem_filter.mp hrS
    obtain ⟨_, hσr⟩ := hparts r hr
    dsimp only at hσr
    change sigma 1 (r ^ (2 * s.factorization r)) = p ^ v r at hσr
    rw [hv1, pow_one] at hσr
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hrs := Nat.dvd_of_mem_primeFactors hr
    have hepos : 1 ≤ s.factorization r := (hrp.dvd_iff_one_le_factorization hs.pos.ne').mp hrs
    have hrel : r ^ (2 * s.factorization r + 1) = 1 + (r - 1) * p := by
      rw [← hσr, sigma_one_apply_prime_pow hrp]
      zify [hrp.one_le]
      have hg := geom_sum_mul (r : ℤ) (2 * s.factorization r + 1)
      linarith
    have hrcast : ((r ^ (2 * s.factorization r + 1) : ℕ) : R) = 1 + ((r - 1 : ℕ) : R) * (p : R) := by
      rw [hrel]
      push_cast
      rfl
    have hTQ : T = (2 * s.factorization r + 1) * Q := by
      rw [hT_prod]
      exact (Finset.mul_prod_erase s.primeFactors (fun t => 2 * s.factorization t + 1) hr).symm
    have hQpos : 1 ≤ Q := Finset.one_le_prod fun _ _ => by omega
    have hexp : 1 ≤ 2 * s.factorization r * Q := by nlinarith
    have hb2 : (((r - 1 : ℕ) : R) * (p : R)) ^ 2 = 0 := by
      calc (((r - 1 : ℕ) : R) * (p : R)) ^ 2 = ((r - 1 : ℕ) : R) ^ 2 * (p : R) ^ 2 := by ring
        _ = 0 := by rw [hp2_zero, mul_zero]
    calc ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T
        = ((r ^ (2 * s.factorization r) : ℕ) : R) ^ ((2 * s.factorization r + 1) * Q) := by rw [hTQ]
      _ = ((r ^ (2 * s.factorization r + 1) : ℕ) : R) ^ (2 * s.factorization r * Q) := by
        push_cast; ring
      _ = (1 + ((r - 1 : ℕ) : R) * (p : R)) ^ (2 * s.factorization r * Q) := by rw [hrcast]
      _ = 1 ^ (2 * s.factorization r * Q) +
          ((2 * s.factorization r * Q : ℕ) : R) * 1 ^ (2 * s.factorization r * Q - 1) *
            (((r - 1 : ℕ) : R) * (p : R)) :=
        add_pow_of_sq_eq_zero 1 (((r - 1 : ℕ) : R) * (p : R)) hb2 (2 * s.factorization r * Q) hexp
      _ = 1 + ((2 * s.factorization r * Q * (r - 1) : ℕ) : R) * (p : R) := by
        simp only [one_pow, mul_one, Nat.cast_mul]; ring
  have hS1_ne0 : S₁.card ≠ 0 := by
    intro h0
    have hS1_empty : S₁ = ∅ := Finset.card_eq_zero.mp h0
    have hs2_one : ((s ^ 2 : ℕ) : R) ^ T = 1 := by
      rw [hs2_pow_T]
      refine Finset.prod_eq_one fun r hr => hlocal_not r hr (by simp [hS1_empty])
    rw [hs2_one, mul_one] at hpow_T
    have hzero : ((T * 2 ^ (T - 1) * p : ℕ) : R) = 0 := by
      push_cast
      linear_combination -hpow_T
    have hdvd : p ^ 2 ∣ T * 2 ^ (T - 1) * p := (ZMod.natCast_eq_zero_iff _ _).mp hzero
    rw [pow_two] at hdvd
    have hdvd1 : p ∣ T * 2 ^ (T - 1) := Nat.dvd_of_mul_dvd_mul_right hp.pos hdvd
    have hdvd2 : p ∣ 2 ^ (T - 1) := hT_cop.dvd_of_dvd_mul_left hdvd1
    have hd2 : p ∣ 2 := hp.dvd_of_dvd_pow hdvd2
    exact hpo.not_two_dvd_nat ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd2 ▸ dvd_rfl)
  have hS1_ne1 : S₁.card ≠ 1 := by
    intro h1
    obtain ⟨r₀, hS1_eq⟩ := Finset.card_eq_one.mp h1
    have hr₀S₁ : r₀ ∈ S₁ := by rw [hS1_eq]; exact Finset.mem_singleton_self r₀
    obtain ⟨hr₀, hv1⟩ := Finset.mem_filter.mp hr₀S₁
    have hr₀p := Nat.prime_of_mem_primeFactors hr₀
    have hr₀s := Nat.dvd_of_mem_primeFactors hr₀
    have hr₀o : Odd r₀ := hs.of_dvd_nat hr₀s
    have hr₀_ge3 : 3 ≤ r₀ := by
      have := hr₀p.two_le
      have := Nat.odd_iff.mp hr₀o
      omega
    set e₀ := s.factorization r₀
    have he₀ : 1 ≤ e₀ := (hr₀p.dvd_iff_one_le_factorization hs.pos.ne').mp hr₀s
    set Q := ∏ t ∈ s.primeFactors.erase r₀, (2 * s.factorization t + 1)
    have hTQ : T = (2 * e₀ + 1) * Q := by
      rw [hT_prod]
      exact (Finset.mul_prod_erase s.primeFactors (fun t => 2 * s.factorization t + 1) hr₀).symm
    have hQ_cop : p.Coprime Q := hT_cop.coprime_dvd_right ⟨2 * e₀ + 1, by rw [hTQ, mul_comm]⟩
    have hs2_val : ((s ^ 2 : ℕ) : R) ^ T = 1 + ((2 * e₀ * Q * (r₀ - 1) : ℕ) : R) * (p : R) := by
      rw [hs2_pow_T, ← Finset.mul_prod_erase s.primeFactors _ hr₀]
      have hrest : (∏ r ∈ s.primeFactors.erase r₀, ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T) = 1 := by
        refine Finset.prod_eq_one fun r hr => ?_
        obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hr
        refine hlocal_not r hmem ?_
        rw [hS1_eq, Finset.mem_singleton]
        exact hne
      rw [hrest, mul_one]
      exact hlocal_mem r₀ hr₀S₁
    rw [hs2_val] at hpow_T
    have h2T : (2 : R) ^ T = (2 : R) * (2 : R) ^ (T - 1) := by
      rw [← pow_succ', show T - 1 + 1 = T by omega]
    have hcongr : (((4 * e₀ * (r₀ - 1) * Q * 2 ^ (T - 1) * p : ℕ)) : R) =
        (((2 * e₀ + 1) * Q * 2 ^ (T - 1) * p : ℕ) : R) := by
      have hA : (2 : R) ^ T * (1 + ((2 * e₀ * Q * (r₀ - 1) : ℕ) : R) * (p : R)) =
          (2 : R) ^ T + (((4 * e₀ * (r₀ - 1) * Q * 2 ^ (T - 1) * p : ℕ)) : R) := by
        push_cast
        calc (2 : R) ^ T * (1 + (2 : R) * (e₀ : R) * (Q : R) * ((r₀ - 1 : ℕ) : R) * (p : R))
            = (2 : R) ^ T + (2 : R) * ((2 : R) * (2 : R) ^ (T - 1)) * (e₀ : R) * (Q : R) *
                ((r₀ - 1 : ℕ) : R) * (p : R) := by rw [← h2T]; ring
          _ = (2 : R) ^ T + (4 : R) * (e₀ : R) * ((r₀ - 1 : ℕ) : R) * (Q : R) *
                (2 : R) ^ (T - 1) * (p : R) := by ring
      have hB : (2 : R) ^ T + (T : R) * (2 : R) ^ (T - 1) * (p : R) =
          (2 : R) ^ T + (((2 * e₀ + 1) * Q * 2 ^ (T - 1) * p : ℕ) : R) := by
        rw [hTQ]
        push_cast
        ring
      rw [hA, hB] at hpow_T
      exact add_left_cancel hpow_T
    have hr₀_sub : 2 ≤ r₀ - 1 := by omega
    have hlt_coeff : 2 * e₀ + 1 < 4 * e₀ * (r₀ - 1) := by nlinarith
    set Δ := 4 * e₀ * (r₀ - 1) - (2 * e₀ + 1)
    have hΔ_pos : 0 < Δ := by omega
    have hΔ_eq : 4 * e₀ * (r₀ - 1) = (2 * e₀ + 1) + Δ := by omega
    have hzero : ((Δ * Q * 2 ^ (T - 1) * p : ℕ) : R) = 0 := by
      have hcast := congrArg (fun n : ℕ => (n : R)) (by
        calc Δ * Q * 2 ^ (T - 1) * p + (2 * e₀ + 1) * Q * 2 ^ (T - 1) * p
            = ((2 * e₀ + 1) + Δ) * Q * 2 ^ (T - 1) * p := by ring
          _ = 4 * e₀ * (r₀ - 1) * Q * 2 ^ (T - 1) * p := by rw [← hΔ_eq])
      push_cast at hcast hcongr ⊢
      linear_combination hcast + hcongr
    have hdvd_prod : p ^ 2 ∣ Δ * Q * 2 ^ (T - 1) * p := (ZMod.natCast_eq_zero_iff _ _).mp hzero
    rw [pow_two] at hdvd_prod
    have hdvd1 : p ∣ Δ * Q * 2 ^ (T - 1) := Nat.dvd_of_mul_dvd_mul_right hp.pos hdvd_prod
    have hdvd2 : p ∣ Δ * Q :=
      ((Nat.coprime_two_right.mpr hpo).pow_right (T - 1)).dvd_of_dvd_mul_right hdvd1
    have hp_dvd_Δ : p ∣ Δ := hQ_cop.dvd_of_dvd_mul_right hdvd2
    have hle_p : p ≤ Δ := Nat.le_of_dvd hΔ_pos hp_dvd_Δ
    obtain ⟨_, hσr₀⟩ := hparts r₀ hr₀
    dsimp only at hσr₀
    change sigma 1 (r₀ ^ (2 * e₀)) = p ^ v r₀ at hσr₀
    rw [hv1, pow_one] at hσr₀
    have hp_gt_Δ : Δ < p := by
      rcases eq_or_ne e₀ 1 with he1 | hene1
      · have hp_val : p = 1 + r₀ + r₀ ^ 2 := by
          rw [← hσr₀, he1, mul_one, sigma_one_apply_prime_pow hr₀p]
          simp [Finset.sum_range_succ]
        have hΔ_val : Δ = 4 * r₀ - 7 := by dsimp [Δ]; rw [he1]; omega
        rw [hp_val, hΔ_val] at hle_p
        have hle_nat : 1 + r₀ + r₀ ^ 2 + 7 ≤ 4 * r₀ := by omega
        rw [pow_two] at hle_nat
        nlinarith
      · have he2 : 2 ≤ e₀ := by omega
        have hlin := linear_lt_even_pow hr₀_ge3 he2
        have hσ_gt : r₀ ^ (2 * e₀) < p := by
          rw [← hσr₀]
          exact self_lt_sigma_of_one_lt (one_lt_pow₀ hr₀p.one_lt (by omega))
        have hΔ_lt : Δ < 4 * e₀ * r₀ := by
          dsimp [Δ]
          have : 4 * e₀ * (r₀ - 1) ≤ 4 * e₀ * r₀ := Nat.mul_le_mul_left _ (by omega)
          omega
        omega
    omega
  have hS1_ne2 : S₁.card ≠ 2 := by
    have refute_ordered : ∀ r₁ r₂ : ℕ, r₁ ≠ r₂ → S₁ = {r₁, r₂} →
        s.factorization r₂ < s.factorization r₁ → False := by
      intro r₁ r₂ hne hS1_eq he_lt
      have hr₁S₁ : r₁ ∈ S₁ := by rw [hS1_eq]; simp
      have hr₂S₁ : r₂ ∈ S₁ := by rw [hS1_eq]; simp
      obtain ⟨hr₁, hv₁⟩ := Finset.mem_filter.mp hr₁S₁
      obtain ⟨hr₂, hv₂⟩ := Finset.mem_filter.mp hr₂S₁
      have hr₁p := Nat.prime_of_mem_primeFactors hr₁
      have hr₂p := Nat.prime_of_mem_primeFactors hr₂
      have hr₁s := Nat.dvd_of_mem_primeFactors hr₁
      have hr₂s := Nat.dvd_of_mem_primeFactors hr₂
      have hr₁o : Odd r₁ := hs.of_dvd_nat hr₁s
      set e₁ := s.factorization r₁
      set e₂ := s.factorization r₂
      have he₂ : 1 ≤ e₂ := (hr₂p.dvd_iff_one_le_factorization hs.pos.ne').mp hr₂s
      have he₁ : 2 ≤ e₁ := by omega
      set l₁ := 2 * e₁ + 1
      set l₂ := 2 * e₂ + 1
      have hl₁p : l₁.Prime :=
        (even_index_cofactor_component_order_dvd_pred hp hpo hs hσq hplus hσs hr₁).1
      have hl₂p : l₂.Prime :=
        (even_index_cofactor_component_order_dvd_pred hp hpo hs hσq hplus hσs hr₂).1
      have hσr₁ : sigma 1 (r₁ ^ (2 * e₁)) = p := by
        have H := (hparts r₁ hr₁).2
        dsimp only at H
        change sigma 1 (r₁ ^ (2 * e₁)) = p ^ v r₁ at H
        rwa [hv₁, pow_one] at H
      have hσr₂ : sigma 1 (r₂ ^ (2 * e₂)) = p := by
        have H := (hparts r₂ hr₂).2
        dsimp only at H
        change sigma 1 (r₂ ^ (2 * e₂)) = p ^ v r₂ at H
        rwa [hv₂, pow_one] at H
      have hr₁_lt_r₂ : r₁ < r₂ := by
        by_contra! hle
        have hle_base : sigma 1 (r₂ ^ (2 * e₂)) ≤ sigma 1 (r₁ ^ (2 * e₂)) := by
          rw [sigma_one_apply_prime_pow hr₂p, sigma_one_apply_prime_pow hr₁p]
          exact Finset.sum_le_sum fun j _ => Nat.pow_le_pow_left hle j
        have hlt_exp : sigma 1 (r₁ ^ (2 * e₂)) < sigma 1 (r₁ ^ (2 * e₁)) :=
          sigma_prime_pow_strictMono_exp hr₁p (by omega)
        omega
      set Q₁₂ := ∏ t ∈ (s.primeFactors.erase r₁).erase r₂, (2 * s.factorization t + 1)
      have hr₂_er₁ : r₂ ∈ s.primeFactors.erase r₁ := Finset.mem_erase.mpr ⟨hne.symm, hr₂⟩
      have hr₁_er₂ : r₁ ∈ s.primeFactors.erase r₂ := Finset.mem_erase.mpr ⟨hne, hr₁⟩
      have hQ₁ : (∏ t ∈ s.primeFactors.erase r₁, (2 * s.factorization t + 1)) = l₂ * Q₁₂ := by
        change _ = (2 * e₂ + 1) * Q₁₂
        exact (Finset.mul_prod_erase (s.primeFactors.erase r₁)
          (fun t => 2 * s.factorization t + 1) hr₂_er₁).symm
      have hQ₂ : (∏ t ∈ s.primeFactors.erase r₂, (2 * s.factorization t + 1)) = l₁ * Q₁₂ := by
        change _ = (2 * e₁ + 1) * ∏ t ∈ (s.primeFactors.erase r₁).erase r₂, (2 * s.factorization t + 1)
        rw [Finset.erase_right_comm]
        exact (Finset.mul_prod_erase (s.primeFactors.erase r₂)
          (fun t => 2 * s.factorization t + 1) hr₁_er₂).symm
      have hTQ₁₂ : T = l₁ * l₂ * Q₁₂ := by
        rw [hT_prod, ← Finset.mul_prod_erase s.primeFactors _ hr₁, hQ₁]
        change (2 * e₁ + 1) * (l₂ * Q₁₂) = l₁ * l₂ * Q₁₂
        dsimp [l₁]
        ring
      have hQ₁₂_cop : p.Coprime Q₁₂ :=
        hT_cop.coprime_dvd_right ⟨l₁ * l₂, by rw [hTQ₁₂, mul_comm]⟩
      have hrest : (∏ r ∈ (s.primeFactors.erase r₁).erase r₂,
          ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T) = 1 := by
        refine Finset.prod_eq_one fun r hr => ?_
        obtain ⟨hn2, hr_er1⟩ := Finset.mem_erase.mp hr
        obtain ⟨hn1, hr_pf⟩ := Finset.mem_erase.mp hr_er1
        refine hlocal_not r hr_pf ?_
        rw [hS1_eq, Finset.mem_insert, Finset.mem_singleton]
        exact not_or.mpr ⟨hn1, hn2⟩
      have hs2_split : ((s ^ 2 : ℕ) : R) ^ T =
          ((r₁ ^ (2 * e₁) : ℕ) : R) ^ T * ((r₂ ^ (2 * e₂) : ℕ) : R) ^ T := by
        rw [hs2_pow_T, ← Finset.mul_prod_erase s.primeFactors _ hr₁,
          ← Finset.mul_prod_erase (s.primeFactors.erase r₁) _ hr₂_er₁, hrest, mul_one]
      have hm₁ := hlocal_mem r₁ hr₁S₁
      dsimp only at hm₁
      rw [hQ₁] at hm₁
      have hm₂ := hlocal_mem r₂ hr₂S₁
      dsimp only at hm₂
      rw [hQ₂] at hm₂
      have hs2_val : ((s ^ 2 : ℕ) : R) ^ T =
          1 + (((2 * e₁ * l₂ * (r₁ - 1) + 2 * e₂ * l₁ * (r₂ - 1)) * Q₁₂ : ℕ) : R) * (p : R) := by
        rw [hs2_split, hm₁, hm₂]
        change (1 + ((2 * e₁ * (l₂ * Q₁₂) * (r₁ - 1) : ℕ) : R) * (p : R)) *
            (1 + ((2 * e₂ * (l₁ * Q₁₂) * (r₂ - 1) : ℕ) : R) * (p : R)) = _
        push_cast
        calc (1 + (2 : R) * e₁ * (l₂ * Q₁₂) * ((r₁ - 1 : ℕ) : R) * p) *
              (1 + (2 : R) * e₂ * (l₁ * Q₁₂) * ((r₂ - 1 : ℕ) : R) * p)
            = 1 + ((2 : R) * e₁ * l₂ * ((r₁ - 1 : ℕ) : R) +
                (2 : R) * e₂ * l₁ * ((r₂ - 1 : ℕ) : R)) * Q₁₂ * p +
                ((2 : R) * e₁ * (l₂ * Q₁₂) * ((r₁ - 1 : ℕ) : R) *
                  ((2 : R) * e₂ * (l₁ * Q₁₂) * ((r₂ - 1 : ℕ) : R))) * (p : R) ^ 2 := by ring
          _ = 1 + ((2 : R) * e₁ * l₂ * ((r₁ - 1 : ℕ) : R) +
                (2 : R) * e₂ * l₁ * ((r₂ - 1 : ℕ) : R)) * Q₁₂ * p := by
              rw [hp2_zero, mul_zero, add_zero]
      rw [hs2_val] at hpow_T
      have h2T : (2 : R) ^ T = (2 : R) * (2 : R) ^ (T - 1) := by
        rw [← pow_succ', show T - 1 + 1 = T by omega]
      have hcongr : ((((4 * e₁ * (r₁ - 1) * l₂ + 4 * e₂ * (r₂ - 1) * l₁) *
            Q₁₂ * 2 ^ (T - 1) * p : ℕ)) : R) =
          (((l₁ * l₂ * Q₁₂ * 2 ^ (T - 1) * p : ℕ)) : R) := by
        have hA : (2 : R) ^ T * (1 + (((2 * e₁ * l₂ * (r₁ - 1) + 2 * e₂ * l₁ * (r₂ - 1)) *
              Q₁₂ : ℕ) : R) * (p : R)) =
            (2 : R) ^ T + ((((4 * e₁ * (r₁ - 1) * l₂ + 4 * e₂ * (r₂ - 1) * l₁) *
              Q₁₂ * 2 ^ (T - 1) * p : ℕ)) : R) := by
          push_cast
          calc (2 : R) ^ T * (1 + ((2 : R) * e₁ * l₂ * ((r₁ - 1 : ℕ) : R) +
                  (2 : R) * e₂ * l₁ * ((r₂ - 1 : ℕ) : R)) * Q₁₂ * p)
              = (2 : R) ^ T + (2 : R) * ((2 : R) * (2 : R) ^ (T - 1)) *
                  (e₁ * l₂ * ((r₁ - 1 : ℕ) : R) + e₂ * l₁ * ((r₂ - 1 : ℕ) : R)) *
                  Q₁₂ * p := by rw [← h2T]; ring
            _ = (2 : R) ^ T + ((4 : R) * e₁ * ((r₁ - 1 : ℕ) : R) * l₂ +
                  (4 : R) * e₂ * ((r₂ - 1 : ℕ) : R) * l₁) * Q₁₂ *
                  (2 : R) ^ (T - 1) * p := by ring
        have hB : (2 : R) ^ T + (T : R) * (2 : R) ^ (T - 1) * (p : R) =
            (2 : R) ^ T + (((l₁ * l₂ * Q₁₂ * 2 ^ (T - 1) * p : ℕ)) : R) := by
          rw [hTQ₁₂]
          push_cast
          ring
        rw [hA, hB] at hpow_T
        exact add_left_cancel hpow_T
      have hr₁_sub : 2 ≤ r₁ - 1 := by
        have := hr₁p.two_le; have := Nat.odd_iff.mp hr₁o; omega
      have hlt_L : l₁ * l₂ < 4 * e₁ * (r₁ - 1) * l₂ + 4 * e₂ * (r₂ - 1) * l₁ := by
        have hl₁_lt : l₁ < 8 * e₁ := by change 2 * e₁ + 1 < 8 * e₁; omega
        have hl₂_pos : 0 < l₂ := by change 0 < 2 * e₂ + 1; omega
        have hm1 : l₁ * l₂ < 8 * e₁ * l₂ := Nat.mul_lt_mul_of_pos_right hl₁_lt hl₂_pos
        have h8 : 8 * e₁ ≤ 4 * e₁ * (r₁ - 1) := by
          calc 8 * e₁ = 4 * e₁ * 2 := by ring
            _ ≤ 4 * e₁ * (r₁ - 1) := Nat.mul_le_mul_left (4 * e₁) hr₁_sub
        have hm2 : 8 * e₁ * l₂ ≤ 4 * e₁ * (r₁ - 1) * l₂ := Nat.mul_le_mul_right l₂ h8
        omega
      set L := 4 * e₁ * (r₁ - 1) * l₂ + 4 * e₂ * (r₂ - 1) * l₁ - l₁ * l₂
      have hL_pos : 0 < L := by omega
      have hL_eq : 4 * e₁ * (r₁ - 1) * l₂ + 4 * e₂ * (r₂ - 1) * l₁ = l₁ * l₂ + L := by omega
      have hzero : ((L * Q₁₂ * 2 ^ (T - 1) * p : ℕ) : R) = 0 := by
        have hcast := congrArg (fun n : ℕ => (n : R)) (by
          calc L * Q₁₂ * 2 ^ (T - 1) * p + l₁ * l₂ * Q₁₂ * 2 ^ (T - 1) * p
              = (l₁ * l₂ + L) * Q₁₂ * 2 ^ (T - 1) * p := by ring
            _ = (4 * e₁ * (r₁ - 1) * l₂ + 4 * e₂ * (r₂ - 1) * l₁) *
                  Q₁₂ * 2 ^ (T - 1) * p := by rw [← hL_eq])
        push_cast at hcast hcongr ⊢
        linear_combination hcast + hcongr
      have hdvd_prod : p ^ 2 ∣ L * Q₁₂ * 2 ^ (T - 1) * p := (ZMod.natCast_eq_zero_iff _ _).mp hzero
      rw [pow_two] at hdvd_prod
      have hdvd1 : p ∣ L * Q₁₂ * 2 ^ (T - 1) := Nat.dvd_of_mul_dvd_mul_right hp.pos hdvd_prod
      have hdvd2 : p ∣ L * Q₁₂ :=
        ((Nat.coprime_two_right.mpr hpo).pow_right (T - 1)).dvd_of_dvd_mul_right hdvd1
      have hp_dvd_L : p ∣ L := hQ₁₂_cop.dvd_of_dvd_mul_right hdvd2
      have hle_p : p ≤ L := Nat.le_of_dvd hL_pos hp_dvd_L
      exact refute_card_two_arith hp hr₁p hr₁o hr₂p he₂ he_lt hr₁_lt_r₂ hl₁p hl₂p hσr₁ hσr₂ hle_p
    intro h2
    obtain ⟨a, b, hab, hS1_eq⟩ := Finset.card_eq_two.mp h2
    have haS₁ : a ∈ S₁ := by rw [hS1_eq]; simp
    have hbS₁ : b ∈ S₁ := by rw [hS1_eq]; simp
    obtain ⟨ha_pf, hva⟩ := Finset.mem_filter.mp haS₁
    obtain ⟨hb_pf, hvb⟩ := Finset.mem_filter.mp hbS₁
    have hap := Nat.prime_of_mem_primeFactors ha_pf
    have hbp := Nat.prime_of_mem_primeFactors hb_pf
    have has := Nat.dvd_of_mem_primeFactors ha_pf
    have hae : 1 ≤ s.factorization a := (hap.dvd_iff_one_le_factorization hs.pos.ne').mp has
    have hσa : sigma 1 (a ^ (2 * s.factorization a)) = p := by
      have H := (hparts a ha_pf).2
      dsimp only at H
      change sigma 1 (a ^ (2 * s.factorization a)) = p ^ v a at H
      rwa [hva, pow_one] at H
    have hσb : sigma 1 (b ^ (2 * s.factorization b)) = p := by
      have H := (hparts b hb_pf).2
      dsimp only at H
      change sigma 1 (b ^ (2 * s.factorization b)) = p ^ v b at H
      rwa [hvb, pow_one] at H
    have he_ne : s.factorization a ≠ s.factorization b := by
      intro heq
      rw [← heq] at hσb
      rcases Nat.lt_trichotomy a b with hlt | rfl | hgt
      · have := sigma_prime_pow_lt_of_base_lt hap hbp hlt (by omega : 0 < 2 * s.factorization a)
        omega
      · exact hab rfl
      · have := sigma_prime_pow_lt_of_base_lt hbp hap hgt (by omega : 0 < 2 * s.factorization a)
        omega
    rcases Nat.lt_or_gt_of_ne he_ne with hlt | hgt
    · exact refute_ordered b a hab.symm (by rw [hS1_eq, Finset.pair_comm]) hlt
    · exact refute_ordered a b hab hS1_eq hgt
  change 3 ≤ S₁.card
  omega

/-- Every even prime-power component index `p ^ (2 * u)` forces at least three
simultaneous odd-prime-base repunit representations of `p`. -/
theorem even_index_forces_three_repunits {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    HasThreeOddPrimeRepunits p := by
  let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
  let S₁ := s.primeFactors.filter (v · = 1)
  have hS1_ge3 : 3 ≤ S₁.card := even_index_three_le_S1_card hp hpo hs hu hσq hplus hσs
  obtain ⟨r₁, hr₁S⟩ := Finset.card_pos.mp (by omega : 0 < S₁.card)
  have hS1_er₁ : 2 ≤ (S₁.erase r₁).card := by rw [Finset.card_erase_of_mem hr₁S]; omega
  obtain ⟨r₂, hr₂S'⟩ := Finset.card_pos.mp (by omega : 0 < (S₁.erase r₁).card)
  have hS1_er₂ : 1 ≤ ((S₁.erase r₁).erase r₂).card := by
    rw [Finset.card_erase_of_mem hr₂S']; omega
  obtain ⟨r₃, hr₃S'⟩ := Finset.card_pos.mp (by omega : 0 < ((S₁.erase r₁).erase r₂).card)
  obtain ⟨h23, hr₃S''⟩ := Finset.mem_erase.mp hr₃S'
  obtain ⟨h13, hr₃S⟩ := Finset.mem_erase.mp hr₃S''
  obtain ⟨h12, hr₂S⟩ := Finset.mem_erase.mp hr₂S'
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
  exact ⟨r₁, r₂, r₃, 2 * s.factorization r₁ + 1, 2 * s.factorization r₂ + 1,
    2 * s.factorization r₃ + 1, hr₁p, hr₁o, hr₂p, hr₂o, hr₃p, hr₃o,
    h12.symm, h13.symm, h23.symm, hl₁p, hl₁_gt2, hl₂p, hl₂_gt2, hl₃p, hl₃_gt2,
    hgr₁, hgr₂, hgr₃⟩

/-- Unconditional strengthening at any even prime-power component index `i = p ^ (2 * u)`:
`p` has at least three simultaneous odd-prime-base repunit representations and `N` has
at least 6 distinct prime factors. -/
theorem even_prime_power_component_forces_three_repunits_and_six_primes {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    HasThreeOddPrimeRepunits p ∧ 6 ≤ N.primeFactors.card := by
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
  have hthree := even_index_forces_three_repunits hp hpo hso hu hσ hplus hσs
  have hS1_ge3 := even_index_three_le_S1_card hp hpo hso hu hσ hplus hσs
  have hs_ge3 : 3 ≤ s.primeFactors.card :=
    hS1_ge3.trans (Finset.card_le_card (Finset.filter_subset _ _))
  have hpar := Nat.even_iff.mp (even_index_cofactor_prime_count hp hso hσ hplus hσs).1
  have hs_ge4 : 4 ≤ s.primeFactors.card := by omega
  have hn := prime_count_of_even_index_split hq hp hmo hso hu hqm hcop hform hms
  exact ⟨hthree, by omega⟩

end OddPerfect
