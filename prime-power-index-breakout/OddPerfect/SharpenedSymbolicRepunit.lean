module

public import OddPerfect.SeptupleRepunitObstruction
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

/-- The same integer has prime-length repunit representations in eight
distinct odd prime bases. -/
@[expose] def HasEightOddPrimeRepunits (z : ℕ) : Prop :=
  ∃ r₁ r₂ r₃ r₄ r₅ r₆ r₇ r₈ l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ : ℕ,
    r₁.Prime ∧ Odd r₁ ∧ r₂.Prime ∧ Odd r₂ ∧ r₃.Prime ∧ Odd r₃ ∧
    r₄.Prime ∧ Odd r₄ ∧ r₅.Prime ∧ Odd r₅ ∧ r₆.Prime ∧ Odd r₆ ∧
    r₇.Prime ∧ Odd r₇ ∧ r₈.Prime ∧ Odd r₈ ∧
    r₁ ≠ r₂ ∧ r₁ ≠ r₃ ∧ r₁ ≠ r₄ ∧ r₁ ≠ r₅ ∧ r₁ ≠ r₆ ∧ r₁ ≠ r₇ ∧ r₁ ≠ r₈ ∧
    r₂ ≠ r₃ ∧ r₂ ≠ r₄ ∧ r₂ ≠ r₅ ∧ r₂ ≠ r₆ ∧ r₂ ≠ r₇ ∧ r₂ ≠ r₈ ∧
    r₃ ≠ r₄ ∧ r₃ ≠ r₅ ∧ r₃ ≠ r₆ ∧ r₃ ≠ r₇ ∧ r₃ ≠ r₈ ∧
    r₄ ≠ r₅ ∧ r₄ ≠ r₆ ∧ r₄ ≠ r₇ ∧ r₄ ≠ r₈ ∧
    r₅ ≠ r₆ ∧ r₅ ≠ r₇ ∧ r₅ ≠ r₈ ∧
    r₆ ≠ r₇ ∧ r₆ ≠ r₈ ∧
    r₇ ≠ r₈ ∧
    l₁.Prime ∧ 2 < l₁ ∧ l₂.Prime ∧ 2 < l₂ ∧ l₃.Prime ∧ 2 < l₃ ∧
    l₄.Prime ∧ 2 < l₄ ∧ l₅.Prime ∧ 2 < l₅ ∧ l₆.Prime ∧ 2 < l₆ ∧
    l₇.Prime ∧ 2 < l₇ ∧ l₈.Prime ∧ 2 < l₈ ∧
    geometricBlock r₁ l₁ = z ∧ geometricBlock r₂ l₂ = z ∧
    geometricBlock r₃ l₃ = z ∧ geometricBlock r₄ l₄ = z ∧
    geometricBlock r₅ l₅ = z ∧ geometricBlock r₆ l₆ = z ∧
    geometricBlock r₇ l₇ = z ∧ geometricBlock r₈ l₈ = z

/-- The same integer has prime-length repunit representations in nine
distinct odd prime bases. -/
@[expose] def HasNineOddPrimeRepunits (z : ℕ) : Prop :=
  ∃ r₁ r₂ r₃ r₄ r₅ r₆ r₇ r₈ r₉ l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ : ℕ,
    r₁.Prime ∧ Odd r₁ ∧ r₂.Prime ∧ Odd r₂ ∧ r₃.Prime ∧ Odd r₃ ∧
    r₄.Prime ∧ Odd r₄ ∧ r₅.Prime ∧ Odd r₅ ∧ r₆.Prime ∧ Odd r₆ ∧
    r₇.Prime ∧ Odd r₇ ∧ r₈.Prime ∧ Odd r₈ ∧ r₉.Prime ∧ Odd r₉ ∧
    r₁ ≠ r₂ ∧ r₁ ≠ r₃ ∧ r₁ ≠ r₄ ∧ r₁ ≠ r₅ ∧ r₁ ≠ r₆ ∧ r₁ ≠ r₇ ∧ r₁ ≠ r₈ ∧ r₁ ≠ r₉ ∧
    r₂ ≠ r₃ ∧ r₂ ≠ r₄ ∧ r₂ ≠ r₅ ∧ r₂ ≠ r₆ ∧ r₂ ≠ r₇ ∧ r₂ ≠ r₈ ∧ r₂ ≠ r₉ ∧
    r₃ ≠ r₄ ∧ r₃ ≠ r₅ ∧ r₃ ≠ r₆ ∧ r₃ ≠ r₇ ∧ r₃ ≠ r₈ ∧ r₃ ≠ r₉ ∧
    r₄ ≠ r₅ ∧ r₄ ≠ r₆ ∧ r₄ ≠ r₇ ∧ r₄ ≠ r₈ ∧ r₄ ≠ r₉ ∧
    r₅ ≠ r₆ ∧ r₅ ≠ r₇ ∧ r₅ ≠ r₈ ∧ r₅ ≠ r₉ ∧
    r₆ ≠ r₇ ∧ r₆ ≠ r₈ ∧ r₆ ≠ r₉ ∧
    r₇ ≠ r₈ ∧ r₇ ≠ r₉ ∧
    r₈ ≠ r₉ ∧
    l₁.Prime ∧ 2 < l₁ ∧ l₂.Prime ∧ 2 < l₂ ∧ l₃.Prime ∧ 2 < l₃ ∧
    l₄.Prime ∧ 2 < l₄ ∧ l₅.Prime ∧ 2 < l₅ ∧ l₆.Prime ∧ 2 < l₆ ∧
    l₇.Prime ∧ 2 < l₇ ∧ l₈.Prime ∧ 2 < l₈ ∧ l₉.Prime ∧ 2 < l₉ ∧
    geometricBlock r₁ l₁ = z ∧ geometricBlock r₂ l₂ = z ∧
    geometricBlock r₃ l₃ = z ∧ geometricBlock r₄ l₄ = z ∧
    geometricBlock r₅ l₅ = z ∧ geometricBlock r₆ l₆ = z ∧
    geometricBlock r₇ l₇ = z ∧ geometricBlock r₈ l₈ = z ∧
    geometricBlock r₉ l₉ = z

private lemma sigma_prime_pow_lt_of_base_lt'''' {a b e : ℕ} (ha : a.Prime) (hb : b.Prime)
    (hab : a < b) (he : 0 < e) : sigma 1 (a ^ e) < sigma 1 (b ^ e) := by
  rw [sigma_one_apply_prime_pow ha, sigma_one_apply_prime_pow hb]
  exact Finset.sum_lt_sum (fun j _ => Nat.pow_le_pow_left hab.le j)
    ⟨1, Finset.mem_range.mpr (by omega), by simpa using hab⟩

private lemma sigma_prime_pow_le_of_exp_le'''' {r a b : ℕ} (hr : r.Prime) (hab : a ≤ b) :
    sigma 1 (r ^ a) ≤ sigma 1 (r ^ b) := by
  rw [sigma_one_apply_prime_pow hr, sigma_one_apply_prime_pow hr]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

private lemma exp_anti_of_sigma_eq'' {p s a b : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hab : a < b) (hfa : 0 < s.factorization a)
    (hσa : sigma 1 (a ^ (2 * s.factorization a)) = p)
    (hσb : sigma 1 (b ^ (2 * s.factorization b)) = p) :
    s.factorization b < s.factorization a := by
  by_contra! hle
  have hlt : sigma 1 (a ^ (2 * s.factorization a)) < sigma 1 (b ^ (2 * s.factorization a)) :=
    sigma_prime_pow_lt_of_base_lt'''' ha hb hab (by omega)
  have hle' : sigma 1 (b ^ (2 * s.factorization a)) ≤ sigma 1 (b ^ (2 * s.factorization b)) :=
    sigma_prime_pow_le_of_exp_le'''' hb (by omega)
  omega

private lemma even_index_P_L_lt_SumCoef_and_dvd'' {q p s u : ℕ}
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

private lemma sigma_three_pow_mul_two_add_one' (m : ℕ) :
    sigma 1 (3 ^ m) * 2 + 1 = 3 ^ (m + 1) := by
  rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
  have hg := geom_sum_mul_add (2 : ℕ) (m + 1)
  rwa [show (2 : ℕ) + 1 = 3 by decide] at hg

private lemma sigma_five_pow_mul_four_add_one' (m : ℕ) :
    sigma 1 (5 ^ m) * 4 + 1 = 5 ^ (m + 1) := by
  rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 5)]
  have hg := geom_sum_mul_add (4 : ℕ) (m + 1)
  rwa [show (4 : ℕ) + 1 = 5 by decide] at hg

private lemma not_prime_of_sigma_three_pow' {p m d val : ℕ}
    (hp : p.Prime) (hσ : sigma 1 (3 ^ m) = p)
    (hpow : val * 2 + 1 = 3 ^ (m + 1)) (hdvd : d ∣ val) (hd1 : 1 < d) (hdv : d < val) :
    False := by
  have h1 := sigma_three_pow_mul_two_add_one' m
  rw [hσ] at h1
  have hp_eq : p = val := by omega
  rw [hp_eq] at hp
  have := hp.eq_one_or_self_of_dvd d hdvd
  omega

private lemma not_prime_of_sigma_five_pow' {p m d val : ℕ}
    (hp : p.Prime) (hσ : sigma 1 (5 ^ m) = p)
    (hpow : val * 4 + 1 = 5 ^ (m + 1)) (hdvd : d ∣ val) (hd1 : 1 < d) (hdv : d < val) :
    False := by
  have h1 := sigma_five_pow_mul_four_add_one' m
  rw [hσ] at h1
  have hp_eq : p = val := by omega
  rw [hp_eq] at hp
  have := hp.eq_one_or_self_of_dvd d hdvd
  omega

private lemma mul7_le {a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℕ}
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (h₃ : a₃ ≤ b₃) (h₄ : a₄ ≤ b₄)
    (h₅ : a₅ ≤ b₅) (h₆ : a₆ ≤ b₆) (h₇ : a₇ ≤ b₇) :
    a₁ * a₂ * a₃ * a₄ * a₅ * a₆ * a₇ ≤ b₁ * b₂ * b₃ * b₄ * b₅ * b₆ * b₇ := by
  gcongr

private lemma mul8_le {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ : ℕ}
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (h₃ : a₃ ≤ b₃) (h₄ : a₄ ≤ b₄)
    (h₅ : a₅ ≤ b₅) (h₆ : a₆ ≤ b₆) (h₇ : a₇ ≤ b₇) (h₈ : a₈ ≤ b₈) :
    a₁ * a₂ * a₃ * a₄ * a₅ * a₆ * a₇ * a₈ ≤ b₁ * b₂ * b₃ * b₄ * b₅ * b₆ * b₇ * b₈ := by
  gcongr

private lemma ne_of_prime_not_prime {x n : ℕ} (hx : x.Prime) (hn : ¬ n.Prime) : x ≠ n :=
  fun h => hn (h ▸ hx)

private lemma even_index_p_lt_SumCoef {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    let S₁ := s.primeFactors.filter (v · = 1)
    let l (r : ℕ) := 2 * s.factorization r + 1
    let SumCoef := ∑ r ∈ S₁, 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t
    p < SumCoef := by
  intro v S₁ l SumCoef
  let P_L := ∏ r ∈ S₁, l r
  obtain ⟨hlt_L, hp_dvd⟩ : P_L < SumCoef ∧ p ∣ SumCoef - P_L :=
    even_index_P_L_lt_SumCoef_and_dvd'' hp hpo hs hu hσq hplus hσs
  have hle_sub : p ≤ SumCoef - P_L := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt_L) hp_dvd
  have hPL_pos : 0 < P_L := Finset.prod_pos fun _ _ => by dsimp [l]; omega
  omega

/-- Higher-moment symbolic bound on `S₁`: whenever every `r ∈ S₁` has
`m ≤ s.factorization r` for `1 ≤ m`, we obtain
`p ^ (2 * m - 1) < (2 * S₁.card * P_L) ^ (2 * m)`. -/
theorem even_index_large_min_exponent_bound {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    let S₁ := s.primeFactors.filter (v · = 1)
    let P_L := ∏ r ∈ S₁, (2 * s.factorization r + 1)
    S₁.Nonempty ∧
      ∀ m : ℕ, 1 ≤ m → (∀ r ∈ S₁, m ≤ s.factorization r) →
        p ^ (2 * m - 1) < (2 * S₁.card * P_L) ^ (2 * m) := by
  intro v S₁ P_L
  have hS1_ge7 : 7 ≤ S₁.card := even_index_seven_le_S1_card hp hpo hs hu hσq hplus hσs
  have hS1_ne : S₁.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨hS1_ne, ?_⟩
  intro m hm hm_le
  let l (r : ℕ) := 2 * s.factorization r + 1
  let SumCoef := ∑ r ∈ S₁, 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t
  have hp_lt_Sum : p < SumCoef := even_index_p_lt_SumCoef hp hpo hs hu hσq hplus hσs
  let r_max := S₁.max' hS1_ne
  have hr_max_mem : r_max ∈ S₁ := Finset.max'_mem S₁ hS1_ne
  have hr_max_le : ∀ r ∈ S₁, r ≤ r_max := fun r hr => Finset.le_max' S₁ r hr
  obtain ⟨hr_max_pf, hr_max_v⟩ := Finset.mem_filter.mp hr_max_mem
  have hr_max_p : r_max.Prime := Nat.prime_of_mem_primeFactors hr_max_pf
  obtain ⟨_, hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  have hσ_max : sigma 1 (r_max ^ (2 * s.factorization r_max)) = p := by
    have H := (hparts r_max hr_max_pf).2
    dsimp only at H
    change sigma 1 (r_max ^ (2 * s.factorization r_max)) = p ^ v r_max at H
    rwa [hr_max_v, pow_one] at H
  have hterm_le : ∀ r ∈ S₁,
      4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t ≤ 2 * P_L * r_max := by
    intro r hrS
    have h1 : 4 * s.factorization r ≤ 2 * l r := by dsimp [l]; omega
    have h2 : r - 1 ≤ r_max := by
      have := hr_max_le r hrS
      omega
    calc 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t
        ≤ (2 * l r) * r_max * ∏ t ∈ S₁.erase r, l t := by gcongr
      _ = 2 * (l r * ∏ t ∈ S₁.erase r, l t) * r_max := by ring
      _ = 2 * P_L * r_max := by
          rw [show l r * ∏ t ∈ S₁.erase r, l t = ∏ t ∈ S₁, l t from
            Finset.mul_prod_erase S₁ l hrS]
  have hSum_le : SumCoef ≤ 2 * S₁.card * P_L * r_max := by
    calc SumCoef
        ≤ ∑ _r ∈ S₁, (2 * P_L * r_max) := Finset.sum_le_sum hterm_le
      _ = S₁.card * (2 * P_L * r_max) := Finset.sum_const_nat (fun _ _ => rfl)
      _ = 2 * S₁.card * P_L * r_max := by ring
  have hp_lt_prod : p < 2 * S₁.card * P_L * r_max := hp_lt_Sum.trans_le hSum_le
  have hm_max : m ≤ s.factorization r_max := hm_le r_max hr_max_mem
  have hr_max_pow_lt_p : r_max ^ (2 * m) < p := by
    have h1 : r_max ^ (2 * m) ≤ r_max ^ (2 * s.factorization r_max) :=
      Nat.pow_le_pow_right hr_max_p.pos (by omega)
    have h2 : r_max ^ (2 * s.factorization r_max) < sigma 1 (r_max ^ (2 * s.factorization r_max)) :=
      self_lt_sigma_of_one_lt (one_lt_pow₀ hr_max_p.one_lt (by omega))
    omega
  have h2m_pos : 0 < 2 * m := by omega
  have h2m_ne : 2 * m ≠ 0 := by omega
  have hp_pow_lt : p ^ (2 * m) < (2 * S₁.card * P_L) ^ (2 * m) * p := by
    have hpow : p ^ (2 * m) < (2 * S₁.card * P_L * r_max) ^ (2 * m) :=
      Nat.pow_lt_pow_left hp_lt_prod h2m_ne
    have hS1_pos : 0 < S₁.card := Finset.card_pos.mpr hS1_ne
    have hPL_pos : 0 < P_L := Finset.prod_pos fun _ _ => by omega
    have hC_pos : 0 < (2 * S₁.card * P_L) ^ (2 * m) :=
      Nat.pow_pos (Nat.mul_pos (Nat.mul_pos (by decide : 0 < 2) hS1_pos) hPL_pos)
    calc p ^ (2 * m)
        < (2 * S₁.card * P_L * r_max) ^ (2 * m) := hpow
      _ = (2 * S₁.card * P_L) ^ (2 * m) * r_max ^ (2 * m) := by rw [mul_pow]
      _ < (2 * S₁.card * P_L) ^ (2 * m) * p :=
          Nat.mul_lt_mul_of_pos_left hr_max_pow_lt_p hC_pos
  have hsplit : p ^ (2 * m) = p ^ (2 * m - 1) * p := by
    conv_lhs => rw [show 2 * m = (2 * m - 1) + 1 by omega, pow_succ]
  rw [hsplit] at hp_pow_lt
  exact lt_of_mul_lt_mul_right hp_pow_lt (Nat.zero_le p)

private lemma nine_mul_sq_le_three_pow {k : ℕ} (hk : 7 ≤ k) :
    9 * k ^ 2 ≤ 3 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hstep : (k + 1) ^ 2 ≤ 3 * k ^ 2 := by nlinarith
    calc 9 * (k + 1) ^ 2 ≤ 3 * (9 * k ^ 2) := by linarith
      _ ≤ 3 * 3 ^ k := Nat.mul_le_mul_left 3 ih
      _ = 3 ^ (k + 1) := by rw [pow_succ']

private lemma two_mul_le_sq_add_sq (a b : ℕ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : (0 : ℤ) ≤ ((a : ℤ) - b) ^ 2 := sq_nonneg _
  have h2 : ((a : ℤ) - b) ^ 2 = (a : ℤ) ^ 2 - 2 * a * b + b ^ 2 := by ring
  zify
  linarith

private lemma even_index_max_exp_one_bound {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u))
    (hne : (s.primeFactors.filter
      (fun r => (sigma 1 (r ^ (2 * s.factorization r))).factorization p = 1)).Nonempty)
    (hmax1 : s.factorization ((s.primeFactors.filter
      (fun r => (sigma 1 (r ^ (2 * s.factorization r))).factorization p = 1)).max' hne) = 1) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    let S₁ := s.primeFactors.filter (v · = 1)
    let P_L := ∏ r ∈ S₁, (2 * s.factorization r + 1)
    p < 4 * P_L ^ 2 := by
  intro v S₁ P_L
  let l (r : ℕ) := 2 * s.factorization r + 1
  let SumCoef := ∑ r ∈ S₁, 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t
  have hp_lt_Sum : p < SumCoef := even_index_p_lt_SumCoef hp hpo hs hu hσq hplus hσs
  have hS1_ge7 : 7 ≤ S₁.card := even_index_seven_le_S1_card hp hpo hs hu hσq hplus hσs
  let r_max := S₁.max' hne
  change s.factorization r_max = 1 at hmax1
  let r_min := S₁.min' hne
  have hr_max_mem : r_max ∈ S₁ := Finset.max'_mem S₁ hne
  have hr_min_mem : r_min ∈ S₁ := Finset.min'_mem S₁ hne
  have hS1_pos : 0 < S₁.card := by omega
  have hPL_pos : 0 < P_L := Finset.prod_pos fun _ _ => by omega
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
  obtain ⟨hr_max_p, _, _, hσ_max⟩ := extract r_max hr_max_mem
  obtain ⟨hr_min_p, hr_min_o, he_min_pos, hσ_min⟩ := extract r_min hr_min_mem
  have hp_eq_max : p = 1 + r_max + r_max ^ 2 := by
    rw [← hσ_max, hmax1, show 2 * 1 = 2 by decide, sigma_one_apply_prime_pow hr_max_p]
    simp [Finset.sum_range_succ, Nat.add_assoc]
  have hp_lt_succ_sq : p < (r_max + 1) ^ 2 := by
    have := hr_max_p.pos
    nlinarith
  have hr_max_sq_lt_p : r_max ^ 2 < p := by
    have := hr_max_p.pos
    omega
  have hcard_le_emin : S₁.card ≤ s.factorization r_min := by
    let e₁ := s.factorization r_min
    have hinj : Set.InjOn (fun r => s.factorization r) (S₁ : Set ℕ) := by
      intro a ha b hb hab
      obtain ⟨hap, _, heapos, hσa⟩ := extract a ha
      obtain ⟨hbp, _, hebpos, hσb⟩ := extract b hb
      rcases lt_trichotomy a b with hlt | rfl | hgt
      · exact absurd hab (ne_of_gt (exp_anti_of_sigma_eq'' hap hbp hlt heapos hσa hσb))
      · rfl
      · exact absurd hab.symm (ne_of_gt (exp_anti_of_sigma_eq'' hbp hap hgt hebpos hσb hσa))
    have himg : ∀ r ∈ S₁, s.factorization r ∈ Finset.Icc 1 e₁ := by
      intro r hrS
      obtain ⟨hrp, _, hepos, hσr⟩ := extract r hrS
      refine Finset.mem_Icc.mpr ⟨hepos, ?_⟩
      rcases eq_or_lt_of_le (Finset.min'_le S₁ r hrS) with heq | hlt
      · rw [← heq]
      · exact (exp_anti_of_sigma_eq'' hr_min_p hrp hlt he_min_pos hσ_min hσr).le
    calc S₁.card ≤ (Finset.Icc 1 e₁).card :=
          Finset.card_le_card_of_injOn (fun r => s.factorization r) himg hinj
      _ = e₁ := by simp
  have h9k_le_pow3 : 9 * S₁.card ^ 2 ≤ 3 ^ (s.factorization r_min) := by
    calc 9 * S₁.card ^ 2 ≤ 3 ^ S₁.card := nine_mul_sq_le_three_pow hS1_ge7
      _ ≤ 3 ^ s.factorization r_min := Nat.pow_le_pow_right (by decide) hcard_le_emin
  have hr_min_ge3 : 3 ≤ r_min := by
    have := hr_min_p.two_le
    have := Nat.odd_iff.mp hr_min_o
    omega
  have hpow3_sq_lt : (3 ^ s.factorization r_min) ^ 2 < (r_max + 1) ^ 2 := by
    have h1 : (3 ^ s.factorization r_min) ^ 2 = 3 ^ (2 * s.factorization r_min) := by
      rw [← pow_mul]; ring_nf
    have h2 : 3 ^ (2 * s.factorization r_min) ≤ r_min ^ (2 * s.factorization r_min) :=
      Nat.pow_le_pow_left hr_min_ge3 _
    have h3 : r_min ^ (2 * s.factorization r_min) < p := by
      rw [← hσ_min]
      exact self_lt_sigma_of_one_lt (one_lt_pow₀ hr_min_p.one_lt (by omega))
    omega
  have hpow3_le_rmax : 3 ^ s.factorization r_min ≤ r_max := by
    have hlt : 3 ^ s.factorization r_min < r_max + 1 := by
      by_contra! hle
      have hsq : (r_max + 1) ^ 2 ≤ (3 ^ s.factorization r_min) ^ 2 := Nat.pow_le_pow_left hle 2
      omega
    exact Nat.lt_succ_iff.mp hlt
  have h9k_le_rmax : 9 * S₁.card ^ 2 ≤ r_max := h9k_le_pow3.trans hpow3_le_rmax
  have hr_sq_le_rmax : ∀ r ∈ S₁.erase r_max, r ^ 2 ≤ r_max := by
    intro r hrE
    have hrS : r ∈ S₁ := Finset.mem_of_mem_erase hrE
    have hr_ne : r ≠ r_max := Finset.ne_of_mem_erase hrE
    have hr_lt : r < r_max := lt_of_le_of_ne (Finset.le_max' S₁ r hrS) hr_ne
    obtain ⟨hrp, _, hepos, hσr⟩ := extract r hrS
    have h2_le_exp : 2 ≤ s.factorization r := by
      have := exp_anti_of_sigma_eq'' hrp hr_max_p hr_lt hepos hσr hσ_max
      omega
    have hr4_lt_p : (r ^ 2) ^ 2 < (r_max + 1) ^ 2 := by
      have h1 : (r ^ 2) ^ 2 = r ^ 4 := by ring
      have h2 : r ^ 4 ≤ r ^ (2 * s.factorization r) :=
        Nat.pow_le_pow_right hrp.pos (by omega)
      have h3 : r ^ (2 * s.factorization r) < p := by
        rw [← hσr]
        exact self_lt_sigma_of_one_lt (one_lt_pow₀ hrp.one_lt (by omega))
      omega
    have hlt : r ^ 2 < r_max + 1 := by
      by_contra! hle
      have hsq : (r_max + 1) ^ 2 ≤ (r ^ 2) ^ 2 := Nat.pow_le_pow_left hle 2
      omega
    exact Nat.lt_succ_iff.mp hlt
  have hmax_part : 3 * (4 * s.factorization r_max * (r_max - 1) * ∏ t ∈ S₁.erase r_max, l t) <
      4 * P_L * r_max := by
    have hlmax : l r_max = 3 := by dsimp [l]; omega
    have hPL_eq : P_L = 3 * ∏ t ∈ S₁.erase r_max, l t := by
      change (∏ t ∈ S₁, l t) = 3 * ∏ t ∈ S₁.erase r_max, l t
      rw [← Finset.mul_prod_erase S₁ l hr_max_mem, hlmax]
    have h_eq : 3 * (4 * s.factorization r_max * (r_max - 1) * ∏ t ∈ S₁.erase r_max, l t) =
        4 * P_L * (r_max - 1) := by
      rw [hmax1, hPL_eq]
      ring
    rw [h_eq]
    have hsub_lt : r_max - 1 < r_max := Nat.sub_lt hr_max_p.pos (by decide)
    exact Nat.mul_lt_mul_of_pos_left hsub_lt (Nat.mul_pos (by decide) hPL_pos)
  have herase_term_le : ∀ r ∈ S₁.erase r_max,
      S₁.card * (3 * (4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t)) ≤
        2 * P_L * r_max := by
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
    have hr_sq : r ^ 2 ≤ r_max := hr_sq_le_rmax r hrE
    have h6kr : 6 * S₁.card * r ≤ 2 * r_max := by
      have hsq : 2 * (3 * S₁.card) * r ≤ (3 * S₁.card) ^ 2 + r ^ 2 :=
        two_mul_le_sq_add_sq (3 * S₁.card) r
      have h9 : (3 * S₁.card) ^ 2 = 9 * S₁.card ^ 2 := by ring
      linarith
    calc S₁.card * (3 * (4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t))
        ≤ S₁.card * (3 * (2 * P_L * r)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 3 hterm_le)
      _ = P_L * (6 * S₁.card * r) := by ring
      _ ≤ P_L * (2 * r_max) := Nat.mul_le_mul_left P_L h6kr
      _ = 2 * P_L * r_max := by ring
  have herase_sum_lt :
      3 * (∑ r ∈ S₁.erase r_max, 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t) <
        2 * P_L * r_max := by
    have hsum_scaled :
        S₁.card * (3 * ∑ r ∈ S₁.erase r_max,
          4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t) <
          S₁.card * (2 * P_L * r_max) := by
      have hcard_erase : (S₁.erase r_max).card < S₁.card := by
        rw [Finset.card_erase_of_mem hr_max_mem]
        omega
      have h2PLr_pos : 0 < 2 * P_L * r_max :=
        Nat.mul_pos (Nat.mul_pos (by decide) hPL_pos) hr_max_p.pos
      calc S₁.card * (3 * ∑ r ∈ S₁.erase r_max,
              4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t)
          = ∑ r ∈ S₁.erase r_max,
              S₁.card * (3 * (4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t)) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum]
        _ ≤ ∑ _r ∈ S₁.erase r_max, (2 * P_L * r_max) := Finset.sum_le_sum herase_term_le
        _ = (S₁.erase r_max).card * (2 * P_L * r_max) := Finset.sum_const_nat (fun _ _ => rfl)
        _ < S₁.card * (2 * P_L * r_max) := Nat.mul_lt_mul_of_pos_right hcard_erase h2PLr_pos
    exact lt_of_mul_lt_mul_left hsum_scaled (Nat.zero_le S₁.card)
  have h3Sum : 3 * SumCoef < 6 * P_L * r_max := by
    have hsplit : SumCoef =
        4 * s.factorization r_max * (r_max - 1) * ∏ t ∈ S₁.erase r_max, l t +
          ∑ r ∈ S₁.erase r_max, 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t :=
      (Finset.add_sum_erase S₁
        (fun r => 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t) hr_max_mem).symm
    rw [hsplit, mul_add]
    calc 3 * (4 * s.factorization r_max * (r_max - 1) * ∏ t ∈ S₁.erase r_max, l t) +
          3 * ∑ r ∈ S₁.erase r_max, 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t
        < 4 * P_L * r_max + 2 * P_L * r_max := Nat.add_lt_add hmax_part herase_sum_lt
      _ = 6 * P_L * r_max := by ring
  have hSum_lt : SumCoef < 2 * P_L * r_max := by
    have h3 : 3 * SumCoef < 3 * (2 * P_L * r_max) := by
      calc 3 * SumCoef < 6 * P_L * r_max := h3Sum
        _ = 3 * (2 * P_L * r_max) := by ring
    exact lt_of_mul_lt_mul_left h3 (Nat.zero_le 3)
  have hp_lt_prod : p < 2 * P_L * r_max := hp_lt_Sum.trans hSum_lt
  have hr_max_sq_lt : r_max * r_max < (2 * P_L) * r_max := by
    calc r_max * r_max = r_max ^ 2 := by ring
      _ < p := hr_max_sq_lt_p
      _ < 2 * P_L * r_max := hp_lt_prod
  have hr_max_lt : r_max < 2 * P_L := lt_of_mul_lt_mul_right hr_max_sq_lt (Nat.zero_le r_max)
  calc p < 2 * P_L * r_max := hp_lt_prod
    _ < 2 * P_L * (2 * P_L) := Nat.mul_lt_mul_of_pos_left hr_max_lt (Nat.mul_pos (by decide) hPL_pos)
    _ = 4 * P_L ^ 2 := by ring

/-- Sharpened symbolic dichotomy at any even prime-power component index:
either `s.factorization r_max = 1`, yielding the cardinality-free bound `p < 4 * P_L ^ 2`,
or every `r ∈ S₁` has `2 ≤ s.factorization r`, yielding `p ^ 3 < (2 * S₁.card * P_L) ^ 4`. -/
theorem even_index_sharpened_symbolic_dichotomy {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    let S₁ := s.primeFactors.filter (v · = 1)
    let P_L := ∏ r ∈ S₁, (2 * s.factorization r + 1)
    p < 4 * P_L ^ 2 ∨ p ^ 3 < (2 * S₁.card * P_L) ^ 4 := by
  intro v S₁ P_L
  obtain ⟨hne, hmoment⟩ := even_index_large_min_exponent_bound hp hpo hs hu hσq hplus hσs
  let r_max := S₁.max' hne
  have hr_max_mem : r_max ∈ S₁ := Finset.max'_mem S₁ hne
  have hr_max_pf : r_max ∈ s.primeFactors := (Finset.mem_filter.mp hr_max_mem).1
  have hr_max_p : r_max.Prime := Nat.prime_of_mem_primeFactors hr_max_pf
  have he_max_pos : 1 ≤ s.factorization r_max :=
    (hr_max_p.dvd_iff_one_le_factorization hs.pos.ne').mp (Nat.dvd_of_mem_primeFactors hr_max_pf)
  by_cases hmax1 : s.factorization r_max = 1
  · exact Or.inl (even_index_max_exp_one_bound hp hpo hs hu hσq hplus hσs hne hmax1)
  · right
    have h2_max : 2 ≤ s.factorization r_max := by omega
    obtain ⟨_, hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
    have hσ_max : sigma 1 (r_max ^ (2 * s.factorization r_max)) = p := by
      have H := (hparts r_max hr_max_pf).2
      dsimp only at H
      change sigma 1 (r_max ^ (2 * s.factorization r_max)) = p ^ v r_max at H
      rwa [(Finset.mem_filter.mp hr_max_mem).2, pow_one] at H
    have h2_all : ∀ r ∈ S₁, 2 ≤ s.factorization r := by
      intro r hrS
      obtain ⟨hr_pf, hr_v⟩ := Finset.mem_filter.mp hrS
      have hrp := Nat.prime_of_mem_primeFactors hr_pf
      have hepos : 1 ≤ s.factorization r :=
        (hrp.dvd_iff_one_le_factorization hs.pos.ne').mp (Nat.dvd_of_mem_primeFactors hr_pf)
      rcases eq_or_lt_of_le (Finset.le_max' S₁ r hrS) with h_eq | hlt
      · rw [h_eq]
        exact h2_max
      · have hσr : sigma 1 (r ^ (2 * s.factorization r)) = p := by
          have H := (hparts r hr_pf).2
          dsimp only at H
          change sigma 1 (r ^ (2 * s.factorization r)) = p ^ v r at H
          rwa [hr_v, pow_one] at H
        have := exp_anti_of_sigma_eq'' hrp hr_max_p hlt hepos hσr hσ_max
        omega
    simpa using hmoment 2 (by decide) h2_all

private lemma thirty_six_mul_odd_pow12_le_three_pow {e : ℕ} (he : 23 ≤ e) :
    36 * (2 * e + 1) ^ 12 ≤ 3 ^ (2 * e) := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hstep : 7 * (2 * (k + 1) + 1) ≤ 8 * (2 * k + 1) := by omega
    have hpow12 : 7 ^ 12 * (2 * (k + 1) + 1) ^ 12 ≤ 8 ^ 12 * (2 * k + 1) ^ 12 := by
      calc 7 ^ 12 * (2 * (k + 1) + 1) ^ 12
          = (7 * (2 * (k + 1) + 1)) ^ 12 := by ring
        _ ≤ (8 * (2 * k + 1)) ^ 12 := Nat.pow_le_pow_left hstep 12
        _ = 8 ^ 12 * (2 * k + 1) ^ 12 := by ring
    have hscale : 7 ^ 12 * (36 * (2 * (k + 1) + 1) ^ 12) ≤
        7 ^ 12 * 3 ^ (2 * (k + 1)) := by
      calc 7 ^ 12 * (36 * (2 * (k + 1) + 1) ^ 12)
          = 36 * (7 ^ 12 * (2 * (k + 1) + 1) ^ 12) := by ring
        _ ≤ 36 * (8 ^ 12 * (2 * k + 1) ^ 12) := Nat.mul_le_mul_left 36 hpow12
        _ = 8 ^ 12 * (36 * (2 * k + 1) ^ 12) := by ring
        _ ≤ (9 * 7 ^ 12) * (36 * (2 * k + 1) ^ 12) :=
            Nat.mul_le_mul_right _ (by norm_num)
        _ ≤ (9 * 7 ^ 12) * 3 ^ (2 * k) := Nat.mul_le_mul_left _ ih
        _ = 7 ^ 12 * 3 ^ (2 * (k + 1)) := by
            rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]; ring
    exact le_of_mul_le_mul_left hscale (by decide : 0 < 7 ^ 12)

private lemma one_ninety_six_mul_odd_pow14_le_three_pow {e : ℕ} (he : 17 ≤ e) :
    196 * (2 * e + 1) ^ 14 ≤ 3 ^ (3 * e) := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hstep : 11 * (2 * (k + 1) + 1) ≤ 12 * (2 * k + 1) := by omega
    have hpow14 : 11 ^ 14 * (2 * (k + 1) + 1) ^ 14 ≤ 12 ^ 14 * (2 * k + 1) ^ 14 := by
      calc 11 ^ 14 * (2 * (k + 1) + 1) ^ 14
          = (11 * (2 * (k + 1) + 1)) ^ 14 := by ring
        _ ≤ (12 * (2 * k + 1)) ^ 14 := Nat.pow_le_pow_left hstep 14
        _ = 12 ^ 14 * (2 * k + 1) ^ 14 := by ring
    have hscale : 11 ^ 14 * (196 * (2 * (k + 1) + 1) ^ 14) ≤
        11 ^ 14 * 3 ^ (3 * (k + 1)) := by
      calc 11 ^ 14 * (196 * (2 * (k + 1) + 1) ^ 14)
          = 196 * (11 ^ 14 * (2 * (k + 1) + 1) ^ 14) := by ring
        _ ≤ 196 * (12 ^ 14 * (2 * k + 1) ^ 14) := Nat.mul_le_mul_left 196 hpow14
        _ = 12 ^ 14 * (196 * (2 * k + 1) ^ 14) := by ring
        _ ≤ (27 * 11 ^ 14) * (196 * (2 * k + 1) ^ 14) :=
            Nat.mul_le_mul_right _ (by norm_num)
        _ ≤ (27 * 11 ^ 14) * 3 ^ (3 * k) := Nat.mul_le_mul_left _ ih
        _ = 11 ^ 14 * 3 ^ (3 * (k + 1)) := by
            rw [show 3 * (k + 1) = 3 * k + 3 by ring, pow_add]; ring
    exact le_of_mul_le_mul_left hscale (by decide : 0 < 11 ^ 14)

private lemma thirty_six_mul_odd_pow14_le_three_pow {e : ℕ} (he : 28 ≤ e) :
    36 * (2 * e + 1) ^ 14 ≤ 3 ^ (2 * e) := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hstep : 7 * (2 * (k + 1) + 1) ≤ 8 * (2 * k + 1) := by omega
    have hpow14 : 7 ^ 14 * (2 * (k + 1) + 1) ^ 14 ≤ 8 ^ 14 * (2 * k + 1) ^ 14 := by
      calc 7 ^ 14 * (2 * (k + 1) + 1) ^ 14
          = (7 * (2 * (k + 1) + 1)) ^ 14 := by ring
        _ ≤ (8 * (2 * k + 1)) ^ 14 := Nat.pow_le_pow_left hstep 14
        _ = 8 ^ 14 * (2 * k + 1) ^ 14 := by ring
    have hscale : 7 ^ 14 * (36 * (2 * (k + 1) + 1) ^ 14) ≤
        7 ^ 14 * 3 ^ (2 * (k + 1)) := by
      calc 7 ^ 14 * (36 * (2 * (k + 1) + 1) ^ 14)
          = 36 * (7 ^ 14 * (2 * (k + 1) + 1) ^ 14) := by ring
        _ ≤ 36 * (8 ^ 14 * (2 * k + 1) ^ 14) := Nat.mul_le_mul_left 36 hpow14
        _ = 8 ^ 14 * (36 * (2 * k + 1) ^ 14) := by ring
        _ ≤ (9 * 7 ^ 14) * (36 * (2 * k + 1) ^ 14) :=
            Nat.mul_le_mul_right _ (by norm_num)
        _ ≤ (9 * 7 ^ 14) * 3 ^ (2 * k) := Nat.mul_le_mul_left _ ih
        _ = 7 ^ 14 * 3 ^ (2 * (k + 1)) := by
            rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]; ring
    exact le_of_mul_le_mul_left hscale (by decide : 0 < 7 ^ 14)

private lemma two_fifty_six_mul_odd_pow16_le_three_pow {e : ℕ} (he : 20 ≤ e) :
    256 * (2 * e + 1) ^ 16 ≤ 3 ^ (3 * e) := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hstep : 11 * (2 * (k + 1) + 1) ≤ 12 * (2 * k + 1) := by omega
    have hpow16 : 11 ^ 16 * (2 * (k + 1) + 1) ^ 16 ≤ 12 ^ 16 * (2 * k + 1) ^ 16 := by
      calc 11 ^ 16 * (2 * (k + 1) + 1) ^ 16
          = (11 * (2 * (k + 1) + 1)) ^ 16 := by ring
        _ ≤ (12 * (2 * k + 1)) ^ 16 := Nat.pow_le_pow_left hstep 16
        _ = 12 ^ 16 * (2 * k + 1) ^ 16 := by ring
    have hscale : 11 ^ 16 * (256 * (2 * (k + 1) + 1) ^ 16) ≤
        11 ^ 16 * 3 ^ (3 * (k + 1)) := by
      calc 11 ^ 16 * (256 * (2 * (k + 1) + 1) ^ 16)
          = 256 * (11 ^ 16 * (2 * (k + 1) + 1) ^ 16) := by ring
        _ ≤ 256 * (12 ^ 16 * (2 * k + 1) ^ 16) := Nat.mul_le_mul_left 256 hpow16
        _ = 12 ^ 16 * (256 * (2 * k + 1) ^ 16) := by ring
        _ ≤ (27 * 11 ^ 16) * (256 * (2 * k + 1) ^ 16) :=
            Nat.mul_le_mul_right _ (by norm_num)
        _ ≤ (27 * 11 ^ 16) * 3 ^ (3 * k) := Nat.mul_le_mul_left _ ih
        _ = 11 ^ 16 * 3 ^ (3 * (k + 1)) := by
            rw [show 3 * (k + 1) = 3 * k + 3 by ring, pow_add]; ring
    exact le_of_mul_le_mul_left hscale (by decide : 0 < 11 ^ 16)

private lemma refute_card_seven_caseA {p r₁ e₁ e₂ e₃ e₄ e₅ e₆ e₇ : ℕ}
    (hp : p.Prime) (hr₁p : r₁.Prime) (hr₁o : Odd r₁)
    (he₇ : e₇ = 1) (he₆₇ : e₇ < e₆) (he₅₆ : e₆ < e₅) (he₄₅ : e₅ < e₄)
    (he₃₄ : e₄ < e₃) (he₂₃ : e₃ < e₂) (he₁₂ : e₂ < e₁)
    (hl₁p : (2 * e₁ + 1).Prime) (hl₂p : (2 * e₂ + 1).Prime)
    (_hl₃p : (2 * e₃ + 1).Prime) (hl₄p : (2 * e₄ + 1).Prime)
    (_hl₅p : (2 * e₅ + 1).Prime) (hl₆p : (2 * e₆ + 1).Prime)
    (hσr₁ : sigma 1 (r₁ ^ (2 * e₁)) = p)
    (hp_lt : p < 4 * ((2 * e₁ + 1) * (2 * e₂ + 1) * (2 * e₃ + 1) *
      (2 * e₄ + 1) * (2 * e₅ + 1) * (2 * e₆ + 1) * (2 * e₇ + 1)) ^ 2) : False := by
  let l₁ := 2 * e₁ + 1
  let l₂ := 2 * e₂ + 1
  let l₃ := 2 * e₃ + 1
  let l₄ := 2 * e₄ + 1
  let l₅ := 2 * e₅ + 1
  let l₆ := 2 * e₆ + 1
  have hl₄_ne9 : l₄ ≠ 9 := ne_of_prime_not_prime hl₄p (by decide)
  have hl₂_ne15 : l₂ ≠ 15 := ne_of_prime_not_prime hl₂p (by decide)
  have he₆ : 2 ≤ e₆ := by omega
  have he₅ : 3 ≤ e₅ := by omega
  have he₄ : 5 ≤ e₄ := by dsimp [l₄] at hl₄_ne9; omega
  have he₃ : 6 ≤ e₃ := by omega
  have he₂ : 8 ≤ e₂ := by dsimp [l₂] at hl₂_ne15; omega
  have he₁ : 9 ≤ e₁ := by omega
  have hr₁_mod : r₁ % 2 = 1 := Nat.odd_iff.mp hr₁o
  have hr₁_ge3 : 3 ≤ r₁ := by have := hr₁p.two_le; omega
  have hr₁_pow_lt_p : r₁ ^ (2 * e₁) < p := by
    rw [← hσr₁]
    exact self_lt_sigma_of_one_lt (one_lt_pow₀ hr₁p.one_lt (by omega))
  by_cases he₁_big : 23 ≤ e₁
  · have hl_le : l₂ ≤ l₁ ∧ l₃ ≤ l₁ ∧ l₄ ≤ l₁ ∧ l₅ ≤ l₁ ∧ l₆ ≤ l₁ := by
      dsimp [l₁, l₂, l₃, l₄, l₅, l₆]
      omega
    rcases hl_le with ⟨h2, h3, h4, h5, h6⟩
    have hl₇_eq : 2 * e₇ + 1 = 3 := by omega
    have hprod_le : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * (2 * e₇ + 1) ≤ 3 * l₁ ^ 6 := by
      rw [hl₇_eq]
      calc l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * 3
          ≤ l₁ * l₁ * l₁ * l₁ * l₁ * l₁ * 3 := by gcongr
        _ = 3 * l₁ ^ 6 := by ring
    have hp_lt_36 : p < 36 * (2 * e₁ + 1) ^ 12 := by
      calc p < 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * (2 * e₇ + 1)) ^ 2 := hp_lt
        _ ≤ 4 * (3 * l₁ ^ 6) ^ 2 := by gcongr
        _ = 36 * (2 * e₁ + 1) ^ 12 := by dsimp [l₁]; ring
    have h36 := thirty_six_mul_odd_pow12_le_three_pow he₁_big
    have h3_le : 3 ^ (2 * e₁) ≤ r₁ ^ (2 * e₁) := Nat.pow_le_pow_left hr₁_ge3 (2 * e₁)
    omega
  · have hl₂_le : l₂ ≤ l₁ - 2 := by dsimp [l₁, l₂]; omega
    have hl₃_le : l₃ ≤ l₁ - 4 := by dsimp [l₁, l₃]; omega
    have hl₄_le : l₄ ≤ l₁ - 6 := by dsimp [l₁, l₄]; omega
    have hl₅_le : l₅ ≤ l₁ - 8 := by dsimp [l₁, l₅]; omega
    have hl₆_le : l₆ ≤ l₁ - 10 := by dsimp [l₁, l₆]; omega
    rcases (by omega : e₁ = 9 ∨ e₁ = 10 ∨ e₁ = 11 ∨ e₁ = 12 ∨ e₁ = 13 ∨
        e₁ = 14 ∨ e₁ = 15 ∨ e₁ = 16 ∨ e₁ = 17 ∨ e₁ = 18 ∨ e₁ = 19 ∨
        e₁ = 20 ∨ e₁ = 21 ∨ e₁ = 22) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · -- e₁ = 9, l₁ = 19
      have hp_bound : p < 7 ^ (2 * 9) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * (2 * e₇ + 1) ≤ 19 * 17 * 15 * 13 * 11 * 9 * 3 :=
          mul7_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
            (by omega)
        have hsq : 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * (2 * e₇ + 1)) ^ 2 < 7 ^ (2 * 9) := by
          calc 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * (2 * e₇ + 1)) ^ 2
              ≤ 4 * (19 * 17 * 15 * 13 * 11 * 9 * 3) ^ 2 := by gcongr
            _ < 7 ^ (2 * 9) := by norm_num
        exact hp_lt.trans hsq
      by_cases hr₁_ge7 : 7 ≤ r₁
      · have h7 : 7 ^ (2 * 9) ≤ r₁ ^ (2 * 9) := Nat.pow_le_pow_left hr₁_ge7 (2 * 9)
        omega
      · rcases (by omega : r₁ = 3 ∨ r₁ = 5) with rfl | rfl
        · exact not_prime_of_sigma_three_pow' hp hσr₁
            (by norm_num : 581130733 * 2 + 1 = 3 ^ (2 * 9 + 1))
            (by norm_num : 1597 ∣ 581130733) (by decide) (by decide)
        · exact not_prime_of_sigma_five_pow' hp hσr₁
            (by norm_num : 4768371582031 * 4 + 1 = 5 ^ (2 * 9 + 1))
            (by norm_num : 191 ∣ 4768371582031) (by decide) (by decide)
    · exact absurd hl₁p (by decide)
    · -- e₁ = 11, l₁ = 23
      have hne21_2 : l₂ ≠ 21 := ne_of_prime_not_prime hl₂p (by decide)
      have hne15_4 : l₄ ≠ 15 := ne_of_prime_not_prime hl₄p (by decide)
      have hne9_6 : l₆ ≠ 9 := ne_of_prime_not_prime hl₆p (by decide)
      have hp_bound : p < 5 ^ (2 * 11) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * (2 * e₇ + 1) ≤ 23 * 19 * 17 * 13 * 11 * 7 * 3 :=
          mul7_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
            (by omega)
        have hsq : 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * (2 * e₇ + 1)) ^ 2 < 5 ^ (2 * 11) := by
          calc 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * (2 * e₇ + 1)) ^ 2
              ≤ 4 * (23 * 19 * 17 * 13 * 11 * 7 * 3) ^ 2 := by gcongr
            _ < 5 ^ (2 * 11) := by norm_num
        exact hp_lt.trans hsq
      by_cases hr₁_ge5 : 5 ≤ r₁
      · have h5 : 5 ^ (2 * 11) ≤ r₁ ^ (2 * 11) := Nat.pow_le_pow_left hr₁_ge5 (2 * 11)
        omega
      · have hr1 : r₁ = 3 := by omega
        subst hr1
        exact not_prime_of_sigma_three_pow' hp hσr₁
          (by norm_num : 47071589413 * 2 + 1 = 3 ^ (2 * 11 + 1))
          (by norm_num : 47 ∣ 47071589413) (by decide) (by decide)
    · exact absurd hl₁p (by decide)
    · exact absurd hl₁p (by decide)
    · -- e₁ = 14, l₁ = 29
      have hp_bound : p < 5 ^ (2 * 14) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * (2 * e₇ + 1) ≤ 29 * 27 * 25 * 23 * 21 * 19 * 3 :=
          mul7_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
            (by omega)
        have hsq : 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * (2 * e₇ + 1)) ^ 2 < 5 ^ (2 * 14) := by
          calc 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * (2 * e₇ + 1)) ^ 2
              ≤ 4 * (29 * 27 * 25 * 23 * 21 * 19 * 3) ^ 2 := by gcongr
            _ < 5 ^ (2 * 14) := by norm_num
        exact hp_lt.trans hsq
      by_cases hr₁_ge5 : 5 ≤ r₁
      · have h5 : 5 ^ (2 * 14) ≤ r₁ ^ (2 * 14) := Nat.pow_le_pow_left hr₁_ge5 (2 * 14)
        omega
      · have hr1 : r₁ = 3 := by omega
        subst hr1
        exact not_prime_of_sigma_three_pow' hp hσr₁
          (by norm_num : 34315188682441 * 2 + 1 = 3 ^ (2 * 14 + 1))
          (by norm_num : 59 ∣ 34315188682441) (by decide) (by decide)
    · -- e₁ = 15, l₁ = 31
      have hp_bound : p < 5 ^ (2 * 15) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * (2 * e₇ + 1) ≤ 31 * 29 * 27 * 25 * 23 * 21 * 3 :=
          mul7_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
            (by omega)
        have hsq : 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * (2 * e₇ + 1)) ^ 2 < 5 ^ (2 * 15) := by
          calc 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * (2 * e₇ + 1)) ^ 2
              ≤ 4 * (31 * 29 * 27 * 25 * 23 * 21 * 3) ^ 2 := by gcongr
            _ < 5 ^ (2 * 15) := by norm_num
        exact hp_lt.trans hsq
      by_cases hr₁_ge5 : 5 ≤ r₁
      · have h5 : 5 ^ (2 * 15) ≤ r₁ ^ (2 * 15) := Nat.pow_le_pow_left hr₁_ge5 (2 * 15)
        omega
      · have hr1 : r₁ = 3 := by omega
        subst hr1
        exact not_prime_of_sigma_three_pow' hp hσr₁
          (by norm_num : 308836698141973 * 2 + 1 = 3 ^ (2 * 15 + 1))
          (by norm_num : 683 ∣ 308836698141973) (by decide) (by decide)
    · exact absurd hl₁p (by decide)
    · exact absurd hl₁p (by decide)
    · -- e₁ = 18, l₁ = 37
      have hp_bound : p < 5 ^ (2 * 18) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * (2 * e₇ + 1) ≤ 37 * 35 * 33 * 31 * 29 * 27 * 3 :=
          mul7_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
            (by omega)
        have hsq : 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * (2 * e₇ + 1)) ^ 2 < 5 ^ (2 * 18) := by
          calc 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * (2 * e₇ + 1)) ^ 2
              ≤ 4 * (37 * 35 * 33 * 31 * 29 * 27 * 3) ^ 2 := by gcongr
            _ < 5 ^ (2 * 18) := by norm_num
        exact hp_lt.trans hsq
      by_cases hr₁_ge5 : 5 ≤ r₁
      · have h5 : 5 ^ (2 * 18) ≤ r₁ ^ (2 * 18) := Nat.pow_le_pow_left hr₁_ge5 (2 * 18)
        omega
      · have hr1 : r₁ = 3 := by omega
        subst hr1
        exact not_prime_of_sigma_three_pow' hp hσr₁
          (by norm_num : 225141952945498681 * 2 + 1 = 3 ^ (2 * 18 + 1))
          (by norm_num : 13097927 ∣ 225141952945498681) (by decide) (by decide)
    · exact absurd hl₁p (by decide)
    · -- e₁ = 20, l₁ = 41
      have hp_bound : p < 5 ^ (2 * 20) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * (2 * e₇ + 1) ≤ 41 * 39 * 37 * 35 * 33 * 31 * 3 :=
          mul7_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
            (by omega)
        have hsq : 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * (2 * e₇ + 1)) ^ 2 < 5 ^ (2 * 20) := by
          calc 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * (2 * e₇ + 1)) ^ 2
              ≤ 4 * (41 * 39 * 37 * 35 * 33 * 31 * 3) ^ 2 := by gcongr
            _ < 5 ^ (2 * 20) := by norm_num
        exact hp_lt.trans hsq
      by_cases hr₁_ge5 : 5 ≤ r₁
      · have h5 : 5 ^ (2 * 20) ≤ r₁ ^ (2 * 20) := Nat.pow_le_pow_left hr₁_ge5 (2 * 20)
        omega
      · have hr1 : r₁ = 3 := by omega
        subst hr1
        exact not_prime_of_sigma_three_pow' hp hσr₁
          (by norm_num : 18236498188585393201 * 2 + 1 = 3 ^ (2 * 20 + 1))
          (by norm_num : 83 ∣ 18236498188585393201) (by decide) (by decide)
    · -- e₁ = 21, l₁ = 43
      have hp_bound : p < 5 ^ (2 * 21) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * (2 * e₇ + 1) ≤ 43 * 41 * 39 * 37 * 35 * 33 * 3 :=
          mul7_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
            (by omega)
        have hsq : 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * (2 * e₇ + 1)) ^ 2 < 5 ^ (2 * 21) := by
          calc 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * (2 * e₇ + 1)) ^ 2
              ≤ 4 * (43 * 41 * 39 * 37 * 35 * 33 * 3) ^ 2 := by gcongr
            _ < 5 ^ (2 * 21) := by norm_num
        exact hp_lt.trans hsq
      by_cases hr₁_ge5 : 5 ≤ r₁
      · have h5 : 5 ^ (2 * 21) ≤ r₁ ^ (2 * 21) := Nat.pow_le_pow_left hr₁_ge5 (2 * 21)
        omega
      · have hr1 : r₁ = 3 := by omega
        subst hr1
        exact not_prime_of_sigma_three_pow' hp hσr₁
          (by norm_num : 164128483697268538813 * 2 + 1 = 3 ^ (2 * 21 + 1))
          (by norm_num : 431 ∣ 164128483697268538813) (by decide) (by decide)
    · exact absurd hl₁p (by decide)

private lemma refute_card_seven_caseB {p r₁ e₁ e₂ e₃ e₄ e₅ e₆ e₇ : ℕ}
    (hp : p.Prime) (hr₁p : r₁.Prime) (hr₁o : Odd r₁)
    (he₇ : 2 ≤ e₇) (he₆₇ : e₇ < e₆) (he₅₆ : e₆ < e₅) (he₄₅ : e₅ < e₄)
    (he₃₄ : e₄ < e₃) (he₂₃ : e₃ < e₂) (he₁₂ : e₂ < e₁)
    (hl₁p : (2 * e₁ + 1).Prime) (hl₂p : (2 * e₂ + 1).Prime)
    (hl₃p : (2 * e₃ + 1).Prime) (_hl₄p : (2 * e₄ + 1).Prime)
    (hl₅p : (2 * e₅ + 1).Prime) (_hl₆p : (2 * e₆ + 1).Prime)
    (hσr₁ : sigma 1 (r₁ ^ (2 * e₁)) = p)
    (hp3_lt : p ^ 3 < (14 * ((2 * e₁ + 1) * (2 * e₂ + 1) * (2 * e₃ + 1) *
      (2 * e₄ + 1) * (2 * e₅ + 1) * (2 * e₆ + 1) * (2 * e₇ + 1))) ^ 4) : False := by
  let l₁ := 2 * e₁ + 1
  let l₂ := 2 * e₂ + 1
  let l₃ := 2 * e₃ + 1
  let l₄ := 2 * e₄ + 1
  let l₅ := 2 * e₅ + 1
  let l₆ := 2 * e₆ + 1
  let l₇ := 2 * e₇ + 1
  have hl₅_ne9 : l₅ ≠ 9 := ne_of_prime_not_prime hl₅p (by decide)
  have hl₃_ne15 : l₃ ≠ 15 := ne_of_prime_not_prime hl₃p (by decide)
  have he₆ : 3 ≤ e₆ := by omega
  have he₅ : 5 ≤ e₅ := by dsimp [l₅] at hl₅_ne9; omega
  have he₄ : 6 ≤ e₄ := by omega
  have he₃ : 8 ≤ e₃ := by dsimp [l₃] at hl₃_ne15; omega
  have he₂ : 9 ≤ e₂ := by omega
  have he₁ : 11 ≤ e₁ := by
    have hl₁_ne21 : l₁ ≠ 21 := ne_of_prime_not_prime hl₁p (by decide)
    dsimp [l₁] at hl₁_ne21
    omega
  have hr₁_mod : r₁ % 2 = 1 := Nat.odd_iff.mp hr₁o
  have hr₁_ge3 : 3 ≤ r₁ := by have := hr₁p.two_le; omega
  have hr₁_pow_lt_p3 : r₁ ^ (6 * e₁) < p ^ 3 := by
    have h1 : r₁ ^ (2 * e₁) < p := by
      rw [← hσr₁]
      exact self_lt_sigma_of_one_lt (one_lt_pow₀ hr₁p.one_lt (by omega))
    calc r₁ ^ (6 * e₁) = (r₁ ^ (2 * e₁)) ^ 3 := by rw [← pow_mul]; ring_nf
      _ < p ^ 3 := Nat.pow_lt_pow_left h1 (by decide)
  by_cases he₁_big : 17 ≤ e₁
  · have hl_le : l₂ ≤ l₁ ∧ l₃ ≤ l₁ ∧ l₄ ≤ l₁ ∧ l₅ ≤ l₁ ∧ l₆ ≤ l₁ ∧ l₇ ≤ l₁ := by
      dsimp [l₁, l₂, l₃, l₄, l₅, l₆, l₇]
      omega
    rcases hl_le with ⟨h2, h3, h4, h5, h6, h7⟩
    have hprod_le : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ ≤ l₁ ^ 7 := by
      calc l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇
          ≤ l₁ * l₁ * l₁ * l₁ * l₁ * l₁ * l₁ := by gcongr
        _ = l₁ ^ 7 := by ring
    have hp3_lt_sq : p ^ 3 < (196 * (2 * e₁ + 1) ^ 14) ^ 2 := by
      calc p ^ 3 < (14 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇)) ^ 4 := hp3_lt
        _ ≤ (14 * l₁ ^ 7) ^ 4 := by gcongr
        _ = (196 * (2 * e₁ + 1) ^ 14) ^ 2 := by dsimp [l₁]; ring
    have h196 := one_ninety_six_mul_odd_pow14_le_three_pow he₁_big
    have h196_sq : (196 * (2 * e₁ + 1) ^ 14) ^ 2 ≤ 3 ^ (6 * e₁) := by
      calc (196 * (2 * e₁ + 1) ^ 14) ^ 2
          ≤ (3 ^ (3 * e₁)) ^ 2 := Nat.pow_le_pow_left h196 2
        _ = 3 ^ (6 * e₁) := by rw [← pow_mul]; ring_nf
    have h3_le : 3 ^ (6 * e₁) ≤ r₁ ^ (6 * e₁) := Nat.pow_le_pow_left hr₁_ge3 (6 * e₁)
    omega
  · have hl₂_le : l₂ ≤ l₁ - 2 := by dsimp [l₁, l₂]; omega
    have hl₃_le : l₃ ≤ l₁ - 4 := by dsimp [l₁, l₃]; omega
    have hl₄_le : l₄ ≤ l₁ - 6 := by dsimp [l₁, l₄]; omega
    have hl₅_le : l₅ ≤ l₁ - 8 := by dsimp [l₁, l₅]; omega
    have hl₆_le : l₆ ≤ l₁ - 10 := by dsimp [l₁, l₆]; omega
    have hl₇_le : l₇ ≤ l₁ - 12 := by dsimp [l₁, l₇]; omega
    rcases (by omega : e₁ = 11 ∨ e₁ = 12 ∨ e₁ = 13 ∨ e₁ = 14 ∨ e₁ = 15 ∨ e₁ = 16) with
      rfl | rfl | rfl | rfl | rfl | rfl
    · -- e₁ = 11, l₁ = 23
      have hp_bound : p ^ 3 < 5 ^ (6 * 11) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ ≤ 23 * 21 * 19 * 17 * 15 * 13 * 11 :=
          mul7_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
            (by dsimp [l₇] at *; omega)
        have h4 : (14 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇)) ^ 4 < 5 ^ (6 * 11) := by
          calc (14 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇)) ^ 4
              ≤ (14 * (23 * 21 * 19 * 17 * 15 * 13 * 11)) ^ 4 := by gcongr
            _ < 5 ^ (6 * 11) := by norm_num
        exact hp3_lt.trans h4
      by_cases hr₁_ge5 : 5 ≤ r₁
      · have h5 : 5 ^ (6 * 11) ≤ r₁ ^ (6 * 11) := Nat.pow_le_pow_left hr₁_ge5 (6 * 11)
        omega
      · have hr1 : r₁ = 3 := by omega
        subst hr1
        exact not_prime_of_sigma_three_pow' hp hσr₁
          (by norm_num : 47071589413 * 2 + 1 = 3 ^ (2 * 11 + 1))
          (by norm_num : 47 ∣ 47071589413) (by decide) (by decide)
    · exact absurd hl₁p (by decide)
    · exact absurd hl₁p (by decide)
    · -- e₁ = 14, l₁ = 29
      have hne27_2 : l₂ ≠ 27 := ne_of_prime_not_prime hl₂p (by decide)
      have hne25_2 : l₂ ≠ 25 := ne_of_prime_not_prime hl₂p (by decide)
      have hne21_3 : l₃ ≠ 21 := ne_of_prime_not_prime hl₃p (by decide)
      have hp_bound : p ^ 3 < 5 ^ (6 * 14) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ ≤ 29 * 27 * 25 * 23 * 21 * 19 * 17 :=
          mul7_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
            (by dsimp [l₇] at *; omega)
        have h4 : (14 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇)) ^ 4 < 5 ^ (6 * 14) := by
          calc (14 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇)) ^ 4
              ≤ (14 * (29 * 27 * 25 * 23 * 21 * 19 * 17)) ^ 4 := by gcongr
            _ < 5 ^ (6 * 14) := by norm_num
        exact hp3_lt.trans h4
      by_cases hr₁_ge5 : 5 ≤ r₁
      · have h5 : 5 ^ (6 * 14) ≤ r₁ ^ (6 * 14) := Nat.pow_le_pow_left hr₁_ge5 (6 * 14)
        omega
      · have hr1 : r₁ = 3 := by omega
        subst hr1
        exact not_prime_of_sigma_three_pow' hp hσr₁
          (by norm_num : 34315188682441 * 2 + 1 = 3 ^ (2 * 14 + 1))
          (by norm_num : 59 ∣ 34315188682441) (by decide) (by decide)
    · -- e₁ = 15, l₁ = 31
      have hp_bound : p ^ 3 < 5 ^ (6 * 15) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ ≤ 31 * 29 * 27 * 25 * 23 * 21 * 19 :=
          mul7_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
            (by dsimp [l₇] at *; omega)
        have h4 : (14 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇)) ^ 4 < 5 ^ (6 * 15) := by
          calc (14 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇)) ^ 4
              ≤ (14 * (31 * 29 * 27 * 25 * 23 * 21 * 19)) ^ 4 := by gcongr
            _ < 5 ^ (6 * 15) := by norm_num
        exact hp3_lt.trans h4
      by_cases hr₁_ge5 : 5 ≤ r₁
      · have h5 : 5 ^ (6 * 15) ≤ r₁ ^ (6 * 15) := Nat.pow_le_pow_left hr₁_ge5 (6 * 15)
        omega
      · have hr1 : r₁ = 3 := by omega
        subst hr1
        exact not_prime_of_sigma_three_pow' hp hσr₁
          (by norm_num : 308836698141973 * 2 + 1 = 3 ^ (2 * 15 + 1))
          (by norm_num : 683 ∣ 308836698141973) (by decide) (by decide)
    · exact absurd hl₁p (by decide)

/-- Unconditionally, at any even prime-power component index `p ^ (2 * u)`,
at least eight distinct cofactor primes return `p` with valuation `1`. -/
theorem even_index_eight_le_S1_card {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    8 ≤ (s.primeFactors.filter (v · = 1)).card := by
  intro v
  let S₁ := s.primeFactors.filter (v · = 1)
  let l (r : ℕ) := 2 * s.factorization r + 1
  have hS1_ge7 : 7 ≤ S₁.card := even_index_seven_le_S1_card hp hpo hs hu hσq hplus hσs
  change 7 ≤ S₁.card at hS1_ge7
  by_contra! hlt8
  change S₁.card < 8 at hlt8
  have hcard7 : S₁.card = 7 := by omega
  let f := S₁.orderEmbOfFin hcard7
  let r₁ := f ⟨0, by decide⟩
  let r₂ := f ⟨1, by decide⟩
  let r₃ := f ⟨2, by decide⟩
  let r₄ := f ⟨3, by decide⟩
  let r₅ := f ⟨4, by decide⟩
  let r₆ := f ⟨5, by decide⟩
  let r₇ := f ⟨6, by decide⟩
  have hr₁S : r₁ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard7 _
  have hr₂S : r₂ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard7 _
  have hr₃S : r₃ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard7 _
  have hr₄S : r₄ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard7 _
  have hr₅S : r₅ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard7 _
  have hr₆S : r₆ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard7 _
  have hr₇S : r₇ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard7 _
  have hr₁₂ : r₁ < r₂ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₂₃ : r₂ < r₃ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₃₄ : r₃ < r₄ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₄₅ : r₄ < r₅ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₅₆ : r₅ < r₆ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₆₇ : r₆ < r₇ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hS1_eq : S₁ = {r₁, r₂, r₃, r₄, r₅, r₆, r₇} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    · rw [hcard7, Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_pair (by omega)]
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
  obtain ⟨hr₂p, _, he₂pos, hl₂p, hσr₂⟩ := extract r₂ hr₂S
  obtain ⟨hr₃p, _, he₃pos, hl₃p, hσr₃⟩ := extract r₃ hr₃S
  obtain ⟨hr₄p, _, he₄pos, hl₄p, hσr₄⟩ := extract r₄ hr₄S
  obtain ⟨hr₅p, _, he₅pos, hl₅p, hσr₅⟩ := extract r₅ hr₅S
  obtain ⟨hr₆p, _, he₆pos, hl₆p, hσr₆⟩ := extract r₆ hr₆S
  obtain ⟨hr₇p, _, he₇pos, _, hσr₇⟩ := extract r₇ hr₇S
  have he₆₇ : s.factorization r₇ < s.factorization r₆ :=
    exp_anti_of_sigma_eq'' hr₆p hr₇p hr₆₇ he₆pos hσr₆ hσr₇
  have he₅₆ : s.factorization r₆ < s.factorization r₅ :=
    exp_anti_of_sigma_eq'' hr₅p hr₆p hr₅₆ he₅pos hσr₅ hσr₆
  have he₄₅ : s.factorization r₅ < s.factorization r₄ :=
    exp_anti_of_sigma_eq'' hr₄p hr₅p hr₄₅ he₄pos hσr₄ hσr₅
  have he₃₄ : s.factorization r₄ < s.factorization r₃ :=
    exp_anti_of_sigma_eq'' hr₃p hr₄p hr₃₄ he₃pos hσr₃ hσr₄
  have he₂₃ : s.factorization r₃ < s.factorization r₂ :=
    exp_anti_of_sigma_eq'' hr₂p hr₃p hr₂₃ he₂pos hσr₂ hσr₃
  have he₁₂ : s.factorization r₂ < s.factorization r₁ :=
    exp_anti_of_sigma_eq'' hr₁p hr₂p hr₁₂ he₁pos hσr₁ hσr₂
  have hprod_eq : (∏ r ∈ S₁, l r) = l r₁ * l r₂ * l r₃ * l r₄ * l r₅ * l r₆ * l r₇ := by
    rw [hS1_eq, Finset.prod_insert (by simp; omega),
      Finset.prod_insert (by simp; omega),
      Finset.prod_insert (by simp; omega),
      Finset.prod_insert (by simp; omega),
      Finset.prod_insert (by simp; omega),
      Finset.prod_pair (by omega)]
    ring
  obtain ⟨hne, hmoment⟩ := even_index_large_min_exponent_bound hp hpo hs hu hσq hplus hσs
  have hrmax_eq : S₁.max' hne = r₇ := by
    refine le_antisymm (Finset.max'_le S₁ hne r₇ fun x hx => ?_) (Finset.le_max' S₁ r₇ hr₇S)
    rw [hS1_eq] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  by_cases he₇_eq1 : s.factorization r₇ = 1
  · have hmax1 : s.factorization (S₁.max' hne) = 1 := hrmax_eq ▸ he₇_eq1
    have hp_lt := even_index_max_exp_one_bound hp hpo hs hu hσq hplus hσs hne hmax1
    change p < 4 * (∏ r ∈ S₁, l r) ^ 2 at hp_lt
    rw [hprod_eq] at hp_lt
    exact refute_card_seven_caseA hp hr₁p hr₁o he₇_eq1 he₆₇ he₅₆ he₄₅ he₃₄ he₂₃ he₁₂
      hl₁p hl₂p hl₃p hl₄p hl₅p hl₆p hσr₁ hp_lt
  · have he₇_ge2 : 2 ≤ s.factorization r₇ := by omega
    have h2_all : ∀ r ∈ S₁, 2 ≤ s.factorization r := by
      intro r hrS
      rw [hS1_eq] at hrS
      simp only [Finset.mem_insert, Finset.mem_singleton] at hrS
      rcases hrS with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have hp3_lt := hmoment 2 (by decide) h2_all
    change p ^ 3 < (2 * S₁.card * ∏ r ∈ S₁, l r) ^ 4 at hp3_lt
    rw [hcard7, hprod_eq] at hp3_lt
    have hp3_lt' : p ^ 3 < (14 * (l r₁ * l r₂ * l r₃ * l r₄ * l r₅ * l r₆ * l r₇)) ^ 4 := by
      simpa [show 2 * 7 = 14 by decide, mul_assoc] using hp3_lt
    exact refute_card_seven_caseB hp hr₁p hr₁o he₇_ge2 he₆₇ he₅₆ he₄₅ he₃₄ he₂₃ he₁₂
      hl₁p hl₂p hl₃p hl₄p hl₅p hl₆p hσr₁ hp3_lt'

private lemma refute_card_eight_caseA {p r₁ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ : ℕ}
    (hp : p.Prime) (hr₁p : r₁.Prime) (hr₁o : Odd r₁)
    (he₈ : e₈ = 1) (he₇₈ : e₈ < e₇) (he₆₇ : e₇ < e₆) (he₅₆ : e₆ < e₅) (he₄₅ : e₅ < e₄)
    (he₃₄ : e₄ < e₃) (he₂₃ : e₃ < e₂) (he₁₂ : e₂ < e₁)
    (hl₁p : (2 * e₁ + 1).Prime) (hl₂p : (2 * e₂ + 1).Prime)
    (hl₃p : (2 * e₃ + 1).Prime) (hl₄p : (2 * e₄ + 1).Prime)
    (hl₅p : (2 * e₅ + 1).Prime) (hl₆p : (2 * e₆ + 1).Prime)
    (hl₇p : (2 * e₇ + 1).Prime)
    (hσr₁ : sigma 1 (r₁ ^ (2 * e₁)) = p)
    (hp_lt : p < 4 * ((2 * e₁ + 1) * (2 * e₂ + 1) * (2 * e₃ + 1) *
      (2 * e₄ + 1) * (2 * e₅ + 1) * (2 * e₆ + 1) * (2 * e₇ + 1) * (2 * e₈ + 1)) ^ 2) : False := by
  let l₁ := 2 * e₁ + 1
  let l₂ := 2 * e₂ + 1
  let l₃ := 2 * e₃ + 1
  let l₄ := 2 * e₄ + 1
  let l₅ := 2 * e₅ + 1
  let l₆ := 2 * e₆ + 1
  let l₇ := 2 * e₇ + 1
  have hl₅_ne9 : l₅ ≠ 9 := ne_of_prime_not_prime hl₅p (by decide)
  have hl₃_ne15 : l₃ ≠ 15 := ne_of_prime_not_prime hl₃p (by decide)
  have hl₁_ne21 : l₁ ≠ 21 := ne_of_prime_not_prime hl₁p (by decide)
  have he₇ : 2 ≤ e₇ := by omega
  have he₆ : 3 ≤ e₆ := by omega
  have he₅ : 5 ≤ e₅ := by dsimp [l₅] at hl₅_ne9; omega
  have he₄ : 6 ≤ e₄ := by omega
  have he₃ : 8 ≤ e₃ := by dsimp [l₃] at hl₃_ne15; omega
  have he₂ : 9 ≤ e₂ := by omega
  have he₁ : 11 ≤ e₁ := by dsimp [l₁] at hl₁_ne21; omega
  have hr₁_mod : r₁ % 2 = 1 := Nat.odd_iff.mp hr₁o
  have hr₁_ge3 : 3 ≤ r₁ := by have := hr₁p.two_le; omega
  have hr₁_pow_lt_p : r₁ ^ (2 * e₁) < p := by
    rw [← hσr₁]
    exact self_lt_sigma_of_one_lt (one_lt_pow₀ hr₁p.one_lt (by omega))
  by_cases he₁_big : 28 ≤ e₁
  · have hl_le : l₂ ≤ l₁ ∧ l₃ ≤ l₁ ∧ l₄ ≤ l₁ ∧ l₅ ≤ l₁ ∧ l₆ ≤ l₁ ∧ l₇ ≤ l₁ := by
      dsimp [l₁, l₂, l₃, l₄, l₅, l₆, l₇]
      omega
    rcases hl_le with ⟨h2, h3, h4, h5, h6, h7⟩
    have hl₈_eq : 2 * e₈ + 1 = 3 := by omega
    have hprod_le : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1) ≤ 3 * l₁ ^ 7 := by
      rw [hl₈_eq]
      calc l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * 3
          ≤ l₁ * l₁ * l₁ * l₁ * l₁ * l₁ * l₁ * 3 := by gcongr
        _ = 3 * l₁ ^ 7 := by ring
    have hp_lt_36 : p < 36 * (2 * e₁ + 1) ^ 14 := by
      calc p < 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1)) ^ 2 := hp_lt
        _ ≤ 4 * (3 * l₁ ^ 7) ^ 2 := by gcongr
        _ = 36 * (2 * e₁ + 1) ^ 14 := by dsimp [l₁]; ring
    have h36 := thirty_six_mul_odd_pow14_le_three_pow he₁_big
    have h3_le : 3 ^ (2 * e₁) ≤ r₁ ^ (2 * e₁) := Nat.pow_le_pow_left hr₁_ge3 (2 * e₁)
    omega
  · have hl₂_le : l₂ ≤ l₁ - 2 := by dsimp [l₁, l₂]; omega
    have hl₃_le : l₃ ≤ l₁ - 4 := by dsimp [l₁, l₃]; omega
    have hl₄_le : l₄ ≤ l₁ - 6 := by dsimp [l₁, l₄]; omega
    have hl₅_le : l₅ ≤ l₁ - 8 := by dsimp [l₁, l₅]; omega
    have hl₆_le : l₆ ≤ l₁ - 10 := by dsimp [l₁, l₆]; omega
    have hl₇_le : l₇ ≤ l₁ - 12 := by dsimp [l₁, l₇]; omega
    rcases (by omega : e₁ = 11 ∨ e₁ = 12 ∨ e₁ = 13 ∨ e₁ = 14 ∨ e₁ = 15 ∨
        e₁ = 16 ∨ e₁ = 17 ∨ e₁ = 18 ∨ e₁ = 19 ∨ e₁ = 20 ∨ e₁ = 21 ∨
        e₁ = 22 ∨ e₁ = 23 ∨ e₁ = 24 ∨ e₁ = 25 ∨ e₁ = 26 ∨ e₁ = 27) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · -- e₁ = 11, l₁ = 23
      have hne21_2 : l₂ ≠ 21 := ne_of_prime_not_prime hl₂p (by decide)
      have hne15_4 : l₄ ≠ 15 := ne_of_prime_not_prime hl₄p (by decide)
      have hne9_6 : l₆ ≠ 9 := ne_of_prime_not_prime hl₆p (by decide)
      have hp_bound : p < 7 ^ (2 * 11) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1) ≤
            23 * 19 * 17 * 13 * 11 * 7 * 5 * 3 :=
          mul8_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
            (by dsimp [l₇] at *; omega) (by omega)
        have hsq : 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1)) ^ 2 < 7 ^ (2 * 11) := by
          calc 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1)) ^ 2
              ≤ 4 * (23 * 19 * 17 * 13 * 11 * 7 * 5 * 3) ^ 2 := by gcongr
            _ < 7 ^ (2 * 11) := by norm_num
        exact hp_lt.trans hsq
      by_cases hr₁_ge7 : 7 ≤ r₁
      · have h7 : 7 ^ (2 * 11) ≤ r₁ ^ (2 * 11) := Nat.pow_le_pow_left hr₁_ge7 (2 * 11)
        omega
      · rcases (by omega : r₁ = 3 ∨ r₁ = 5) with rfl | rfl
        · exact not_prime_of_sigma_three_pow' hp hσr₁
            (by norm_num : 47071589413 * 2 + 1 = 3 ^ (2 * 11 + 1))
            (by norm_num : 47 ∣ 47071589413) (by decide) (by decide)
        · exact not_prime_of_sigma_five_pow' hp hσr₁
            (by norm_num : 2980232238769531 * 4 + 1 = 5 ^ (2 * 11 + 1))
            (by norm_num : 8971 ∣ 2980232238769531) (by decide) (by decide)
    · exact absurd hl₁p (by decide)
    · exact absurd hl₁p (by decide)
    · -- e₁ = 14, l₁ = 29
      have hne27_2 : l₂ ≠ 27 := ne_of_prime_not_prime hl₂p (by decide)
      have hne25_2 : l₂ ≠ 25 := ne_of_prime_not_prime hl₂p (by decide)
      have hne21_3 : l₃ ≠ 21 := ne_of_prime_not_prime hl₃p (by decide)
      have hne15_5 : l₅ ≠ 15 := ne_of_prime_not_prime hl₅p (by decide)
      have hne9_7 : l₇ ≠ 9 := ne_of_prime_not_prime hl₇p (by decide)
      have hp_bound : p < 5 ^ (2 * 14) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1) ≤
            29 * 23 * 19 * 17 * 13 * 11 * 7 * 3 :=
          mul8_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
            (by dsimp [l₇] at *; omega) (by omega)
        have hsq : 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1)) ^ 2 < 5 ^ (2 * 14) := by
          calc 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1)) ^ 2
              ≤ 4 * (29 * 23 * 19 * 17 * 13 * 11 * 7 * 3) ^ 2 := by gcongr
            _ < 5 ^ (2 * 14) := by norm_num
        exact hp_lt.trans hsq
      by_cases hr₁_ge5 : 5 ≤ r₁
      · have h5 : 5 ^ (2 * 14) ≤ r₁ ^ (2 * 14) := Nat.pow_le_pow_left hr₁_ge5 (2 * 14)
        omega
      · have hr1 : r₁ = 3 := by omega
        subst hr1
        exact not_prime_of_sigma_three_pow' hp hσr₁
          (by norm_num : 34315188682441 * 2 + 1 = 3 ^ (2 * 14 + 1))
          (by norm_num : 59 ∣ 34315188682441) (by decide) (by decide)
    · -- e₁ = 15, l₁ = 31
      have hne27_3 : l₃ ≠ 27 := ne_of_prime_not_prime hl₃p (by decide)
      have hne25_3 : l₃ ≠ 25 := ne_of_prime_not_prime hl₃p (by decide)
      have hne21_4 : l₄ ≠ 21 := ne_of_prime_not_prime hl₄p (by decide)
      have hne15_6 : l₆ ≠ 15 := ne_of_prime_not_prime hl₆p (by decide)
      have hp_bound : p < 5 ^ (2 * 15) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1) ≤
            31 * 29 * 23 * 19 * 17 * 13 * 11 * 3 :=
          mul8_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
            (by dsimp [l₇] at *; omega) (by omega)
        have hsq : 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1)) ^ 2 < 5 ^ (2 * 15) := by
          calc 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1)) ^ 2
              ≤ 4 * (31 * 29 * 23 * 19 * 17 * 13 * 11 * 3) ^ 2 := by gcongr
            _ < 5 ^ (2 * 15) := by norm_num
        exact hp_lt.trans hsq
      by_cases hr₁_ge5 : 5 ≤ r₁
      · have h5 : 5 ^ (2 * 15) ≤ r₁ ^ (2 * 15) := Nat.pow_le_pow_left hr₁_ge5 (2 * 15)
        omega
      · have hr1 : r₁ = 3 := by omega
        subst hr1
        exact not_prime_of_sigma_three_pow' hp hσr₁
          (by norm_num : 308836698141973 * 2 + 1 = 3 ^ (2 * 15 + 1))
          (by norm_num : 683 ∣ 308836698141973) (by decide) (by decide)
    · exact absurd hl₁p (by decide)
    · exact absurd hl₁p (by decide)
    · -- e₁ = 18, l₁ = 37
      have hp_bound : p < 5 ^ (2 * 18) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1) ≤
            37 * 35 * 33 * 31 * 29 * 27 * 25 * 3 :=
          mul8_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
            (by dsimp [l₇] at *; omega) (by omega)
        have hsq : 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1)) ^ 2 < 5 ^ (2 * 18) := by
          calc 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1)) ^ 2
              ≤ 4 * (37 * 35 * 33 * 31 * 29 * 27 * 25 * 3) ^ 2 := by gcongr
            _ < 5 ^ (2 * 18) := by norm_num
        exact hp_lt.trans hsq
      by_cases hr₁_ge5 : 5 ≤ r₁
      · have h5 : 5 ^ (2 * 18) ≤ r₁ ^ (2 * 18) := Nat.pow_le_pow_left hr₁_ge5 (2 * 18)
        omega
      · have hr1 : r₁ = 3 := by omega
        subst hr1
        exact not_prime_of_sigma_three_pow' hp hσr₁
          (by norm_num : 225141952945498681 * 2 + 1 = 3 ^ (2 * 18 + 1))
          (by norm_num : 13097927 ∣ 225141952945498681) (by decide) (by decide)
    · exact absurd hl₁p (by decide)
    · -- e₁ = 20, l₁ = 41
      have hp_bound : p < 5 ^ (2 * 20) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1) ≤
            41 * 39 * 37 * 35 * 33 * 31 * 29 * 3 :=
          mul8_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
            (by dsimp [l₇] at *; omega) (by omega)
        have hsq : 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1)) ^ 2 < 5 ^ (2 * 20) := by
          calc 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1)) ^ 2
              ≤ 4 * (41 * 39 * 37 * 35 * 33 * 31 * 29 * 3) ^ 2 := by gcongr
            _ < 5 ^ (2 * 20) := by norm_num
        exact hp_lt.trans hsq
      by_cases hr₁_ge5 : 5 ≤ r₁
      · have h5 : 5 ^ (2 * 20) ≤ r₁ ^ (2 * 20) := Nat.pow_le_pow_left hr₁_ge5 (2 * 20)
        omega
      · have hr1 : r₁ = 3 := by omega
        subst hr1
        exact not_prime_of_sigma_three_pow' hp hσr₁
          (by norm_num : 18236498188585393201 * 2 + 1 = 3 ^ (2 * 20 + 1))
          (by norm_num : 83 ∣ 18236498188585393201) (by decide) (by decide)
    · -- e₁ = 21, l₁ = 43
      have hp_bound : p < 5 ^ (2 * 21) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1) ≤
            43 * 41 * 39 * 37 * 35 * 33 * 31 * 3 :=
          mul8_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
            (by dsimp [l₇] at *; omega) (by omega)
        have hsq : 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1)) ^ 2 < 5 ^ (2 * 21) := by
          calc 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1)) ^ 2
              ≤ 4 * (43 * 41 * 39 * 37 * 35 * 33 * 31 * 3) ^ 2 := by gcongr
            _ < 5 ^ (2 * 21) := by norm_num
        exact hp_lt.trans hsq
      by_cases hr₁_ge5 : 5 ≤ r₁
      · have h5 : 5 ^ (2 * 21) ≤ r₁ ^ (2 * 21) := Nat.pow_le_pow_left hr₁_ge5 (2 * 21)
        omega
      · have hr1 : r₁ = 3 := by omega
        subst hr1
        exact not_prime_of_sigma_three_pow' hp hσr₁
          (by norm_num : 164128483697268538813 * 2 + 1 = 3 ^ (2 * 21 + 1))
          (by norm_num : 431 ∣ 164128483697268538813) (by decide) (by decide)
    · exact absurd hl₁p (by decide)
    · -- e₁ = 23, l₁ = 47
      have hp_bound : p < 5 ^ (2 * 23) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1) ≤
            47 * 45 * 43 * 41 * 39 * 37 * 35 * 3 :=
          mul8_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
            (by dsimp [l₇] at *; omega) (by omega)
        have hsq : 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1)) ^ 2 < 5 ^ (2 * 23) := by
          calc 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1)) ^ 2
              ≤ 4 * (47 * 45 * 43 * 41 * 39 * 37 * 35 * 3) ^ 2 := by gcongr
            _ < 5 ^ (2 * 23) := by norm_num
        exact hp_lt.trans hsq
      by_cases hr₁_ge5 : 5 ≤ r₁
      · have h5 : 5 ^ (2 * 23) ≤ r₁ ^ (2 * 23) := Nat.pow_le_pow_left hr₁_ge5 (2 * 23)
        omega
      · have hr1 : r₁ = 3 := by omega
        subst hr1
        exact not_prime_of_sigma_three_pow' hp hσr₁
          (by norm_num : 13294407179478751643893 * 2 + 1 = 3 ^ (2 * 23 + 1))
          (by norm_num : 1223 ∣ 13294407179478751643893) (by decide) (by decide)
    · exact absurd hl₁p (by decide)
    · exact absurd hl₁p (by decide)
    · -- e₁ = 26, l₁ = 53
      have hne51_2 : l₂ ≠ 51 := ne_of_prime_not_prime hl₂p (by decide)
      have hne49_2 : l₂ ≠ 49 := ne_of_prime_not_prime hl₂p (by decide)
      have hp_bound : p < 3 ^ (2 * 26) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1) ≤
            53 * 47 * 45 * 43 * 41 * 39 * 37 * 3 :=
          mul8_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
            (by dsimp [l₇] at *; omega) (by omega)
        have hsq : 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1)) ^ 2 < 3 ^ (2 * 26) := by
          calc 4 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * (2 * e₈ + 1)) ^ 2
              ≤ 4 * (53 * 47 * 45 * 43 * 41 * 39 * 37 * 3) ^ 2 := by gcongr
            _ < 3 ^ (2 * 26) := by norm_num
        exact hp_lt.trans hsq
      have h3 : 3 ^ (2 * 26) ≤ r₁ ^ (2 * 26) := Nat.pow_le_pow_left hr₁_ge3 (2 * 26)
      omega
    · exact absurd hl₁p (by decide)

private lemma refute_card_eight_caseB {p r₁ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ : ℕ}
    (hp : p.Prime) (hr₁p : r₁.Prime) (hr₁o : Odd r₁)
    (he₈ : 2 ≤ e₈) (he₇₈ : e₈ < e₇) (he₆₇ : e₇ < e₆) (he₅₆ : e₆ < e₅) (he₄₅ : e₅ < e₄)
    (he₃₄ : e₄ < e₃) (he₂₃ : e₃ < e₂) (he₁₂ : e₂ < e₁)
    (hl₁p : (2 * e₁ + 1).Prime) (hl₂p : (2 * e₂ + 1).Prime)
    (_hl₃p : (2 * e₃ + 1).Prime) (hl₄p : (2 * e₄ + 1).Prime)
    (_hl₅p : (2 * e₅ + 1).Prime) (hl₆p : (2 * e₆ + 1).Prime)
    (_hl₇p : (2 * e₇ + 1).Prime)
    (hσr₁ : sigma 1 (r₁ ^ (2 * e₁)) = p)
    (hp3_lt : p ^ 3 < (16 * ((2 * e₁ + 1) * (2 * e₂ + 1) * (2 * e₃ + 1) *
      (2 * e₄ + 1) * (2 * e₅ + 1) * (2 * e₆ + 1) * (2 * e₇ + 1) * (2 * e₈ + 1))) ^ 4) : False := by
  let l₁ := 2 * e₁ + 1
  let l₂ := 2 * e₂ + 1
  let l₃ := 2 * e₃ + 1
  let l₄ := 2 * e₄ + 1
  let l₅ := 2 * e₅ + 1
  let l₆ := 2 * e₆ + 1
  let l₇ := 2 * e₇ + 1
  let l₈ := 2 * e₈ + 1
  have hl₆_ne9 : l₆ ≠ 9 := ne_of_prime_not_prime hl₆p (by decide)
  have hl₄_ne15 : l₄ ≠ 15 := ne_of_prime_not_prime hl₄p (by decide)
  have hl₂_ne21 : l₂ ≠ 21 := ne_of_prime_not_prime hl₂p (by decide)
  have hl₁_ne25 : l₁ ≠ 25 := ne_of_prime_not_prime hl₁p (by decide)
  have hl₁_ne27 : l₁ ≠ 27 := ne_of_prime_not_prime hl₁p (by decide)
  have he₇ : 3 ≤ e₇ := by omega
  have he₆ : 5 ≤ e₆ := by dsimp [l₆] at hl₆_ne9; omega
  have he₅ : 6 ≤ e₅ := by omega
  have he₄ : 8 ≤ e₄ := by dsimp [l₄] at hl₄_ne15; omega
  have he₃ : 9 ≤ e₃ := by omega
  have he₂ : 11 ≤ e₂ := by dsimp [l₂] at hl₂_ne21; omega
  have he₁ : 14 ≤ e₁ := by dsimp [l₁] at hl₁_ne25 hl₁_ne27; omega
  have hr₁_mod : r₁ % 2 = 1 := Nat.odd_iff.mp hr₁o
  have hr₁_ge3 : 3 ≤ r₁ := by have := hr₁p.two_le; omega
  have hr₁_pow_lt_p3 : r₁ ^ (6 * e₁) < p ^ 3 := by
    have h1 : r₁ ^ (2 * e₁) < p := by
      rw [← hσr₁]
      exact self_lt_sigma_of_one_lt (one_lt_pow₀ hr₁p.one_lt (by omega))
    calc r₁ ^ (6 * e₁) = (r₁ ^ (2 * e₁)) ^ 3 := by rw [← pow_mul]; ring_nf
      _ < p ^ 3 := Nat.pow_lt_pow_left h1 (by decide)
  by_cases he₁_big : 20 ≤ e₁
  · have hl_le : l₂ ≤ l₁ ∧ l₃ ≤ l₁ ∧ l₄ ≤ l₁ ∧ l₅ ≤ l₁ ∧ l₆ ≤ l₁ ∧ l₇ ≤ l₁ ∧ l₈ ≤ l₁ := by
      dsimp [l₁, l₂, l₃, l₄, l₅, l₆, l₇, l₈]
      omega
    rcases hl_le with ⟨h2, h3, h4, h5, h6, h7, h8⟩
    have hprod_le : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * l₈ ≤ l₁ ^ 8 := by
      calc l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * l₈
          ≤ l₁ * l₁ * l₁ * l₁ * l₁ * l₁ * l₁ * l₁ := by gcongr
        _ = l₁ ^ 8 := by ring
    have hp3_lt_sq : p ^ 3 < (256 * (2 * e₁ + 1) ^ 16) ^ 2 := by
      calc p ^ 3 < (16 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * l₈)) ^ 4 := hp3_lt
        _ ≤ (16 * l₁ ^ 8) ^ 4 := by gcongr
        _ = (256 * (2 * e₁ + 1) ^ 16) ^ 2 := by dsimp [l₁]; ring
    have h256 := two_fifty_six_mul_odd_pow16_le_three_pow he₁_big
    have h256_sq : (256 * (2 * e₁ + 1) ^ 16) ^ 2 ≤ 3 ^ (6 * e₁) := by
      calc (256 * (2 * e₁ + 1) ^ 16) ^ 2
          ≤ (3 ^ (3 * e₁)) ^ 2 := Nat.pow_le_pow_left h256 2
        _ = 3 ^ (6 * e₁) := by rw [← pow_mul]; ring_nf
    have h3_le : 3 ^ (6 * e₁) ≤ r₁ ^ (6 * e₁) := Nat.pow_le_pow_left hr₁_ge3 (6 * e₁)
    omega
  · have hl₂_le : l₂ ≤ l₁ - 2 := by dsimp [l₁, l₂]; omega
    have hl₃_le : l₃ ≤ l₁ - 4 := by dsimp [l₁, l₃]; omega
    have hl₄_le : l₄ ≤ l₁ - 6 := by dsimp [l₁, l₄]; omega
    have hl₅_le : l₅ ≤ l₁ - 8 := by dsimp [l₁, l₅]; omega
    have hl₆_le : l₆ ≤ l₁ - 10 := by dsimp [l₁, l₆]; omega
    have hl₇_le : l₇ ≤ l₁ - 12 := by dsimp [l₁, l₇]; omega
    have hl₈_le : l₈ ≤ l₁ - 14 := by dsimp [l₁, l₈]; omega
    rcases (by omega : e₁ = 14 ∨ e₁ = 15 ∨ e₁ = 16 ∨ e₁ = 17 ∨ e₁ = 18 ∨ e₁ = 19) with
      rfl | rfl | rfl | rfl | rfl | rfl
    · -- e₁ = 14, l₁ = 29
      have hp_bound : p ^ 3 < 5 ^ (6 * 14) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * l₈ ≤
            29 * 27 * 25 * 23 * 21 * 19 * 17 * 15 :=
          mul8_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
            (by dsimp [l₇] at *; omega) (by dsimp [l₈] at *; omega)
        have h4 : (16 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * l₈)) ^ 4 < 5 ^ (6 * 14) := by
          calc (16 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * l₈)) ^ 4
              ≤ (16 * (29 * 27 * 25 * 23 * 21 * 19 * 17 * 15)) ^ 4 := by gcongr
            _ < 5 ^ (6 * 14) := by norm_num
        exact hp3_lt.trans h4
      by_cases hr₁_ge5 : 5 ≤ r₁
      · have h5 : 5 ^ (6 * 14) ≤ r₁ ^ (6 * 14) := Nat.pow_le_pow_left hr₁_ge5 (6 * 14)
        omega
      · have hr1 : r₁ = 3 := by omega
        subst hr1
        exact not_prime_of_sigma_three_pow' hp hσr₁
          (by norm_num : 34315188682441 * 2 + 1 = 3 ^ (2 * 14 + 1))
          (by norm_num : 59 ∣ 34315188682441) (by decide) (by decide)
    · -- e₁ = 15, l₁ = 31
      have hp_bound : p ^ 3 < 5 ^ (6 * 15) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * l₈ ≤
            31 * 29 * 27 * 25 * 23 * 21 * 19 * 17 :=
          mul8_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
            (by dsimp [l₇] at *; omega) (by dsimp [l₈] at *; omega)
        have h4 : (16 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * l₈)) ^ 4 < 5 ^ (6 * 15) := by
          calc (16 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * l₈)) ^ 4
              ≤ (16 * (31 * 29 * 27 * 25 * 23 * 21 * 19 * 17)) ^ 4 := by gcongr
            _ < 5 ^ (6 * 15) := by norm_num
        exact hp3_lt.trans h4
      by_cases hr₁_ge5 : 5 ≤ r₁
      · have h5 : 5 ^ (6 * 15) ≤ r₁ ^ (6 * 15) := Nat.pow_le_pow_left hr₁_ge5 (6 * 15)
        omega
      · have hr1 : r₁ = 3 := by omega
        subst hr1
        exact not_prime_of_sigma_three_pow' hp hσr₁
          (by norm_num : 308836698141973 * 2 + 1 = 3 ^ (2 * 15 + 1))
          (by norm_num : 683 ∣ 308836698141973) (by decide) (by decide)
    · exact absurd hl₁p (by decide)
    · exact absurd hl₁p (by decide)
    · -- e₁ = 18, l₁ = 37
      have hne35_2 : l₂ ≠ 35 := ne_of_prime_not_prime hl₂p (by decide)
      have hne33_2 : l₂ ≠ 33 := ne_of_prime_not_prime hl₂p (by decide)
      have hne27_4 : l₄ ≠ 27 := ne_of_prime_not_prime hl₄p (by decide)
      have hne25_4 : l₄ ≠ 25 := ne_of_prime_not_prime hl₄p (by decide)
      have hp_bound : p ^ 3 < 3 ^ (6 * 18) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * l₈ ≤
            37 * 31 * 29 * 23 * 21 * 19 * 17 * 15 :=
          mul8_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
            (by dsimp [l₇] at *; omega) (by dsimp [l₈] at *; omega)
        have h4 : (16 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * l₈)) ^ 4 < 3 ^ (6 * 18) := by
          calc (16 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆ * l₇ * l₈)) ^ 4
              ≤ (16 * (37 * 31 * 29 * 23 * 21 * 19 * 17 * 15)) ^ 4 := by gcongr
            _ < 3 ^ (6 * 18) := by norm_num
        exact hp3_lt.trans h4
      have h3 : 3 ^ (6 * 18) ≤ r₁ ^ (6 * 18) := Nat.pow_le_pow_left hr₁_ge3 (6 * 18)
      omega
    · exact absurd hl₁p (by decide)

/-- Unconditionally, at any even prime-power component index `p ^ (2 * u)`,
at least nine distinct cofactor primes return `p` with valuation `1`. -/
theorem even_index_nine_le_S1_card {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    9 ≤ (s.primeFactors.filter (v · = 1)).card := by
  intro v
  let S₁ := s.primeFactors.filter (v · = 1)
  let l (r : ℕ) := 2 * s.factorization r + 1
  have hS1_ge8 : 8 ≤ S₁.card := even_index_eight_le_S1_card hp hpo hs hu hσq hplus hσs
  change 8 ≤ S₁.card at hS1_ge8
  by_contra! hlt9
  change S₁.card < 9 at hlt9
  have hcard8 : S₁.card = 8 := by omega
  let f := S₁.orderEmbOfFin hcard8
  let r₁ := f ⟨0, by decide⟩
  let r₂ := f ⟨1, by decide⟩
  let r₃ := f ⟨2, by decide⟩
  let r₄ := f ⟨3, by decide⟩
  let r₅ := f ⟨4, by decide⟩
  let r₆ := f ⟨5, by decide⟩
  let r₇ := f ⟨6, by decide⟩
  let r₈ := f ⟨7, by decide⟩
  have hr₁S : r₁ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard8 _
  have hr₂S : r₂ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard8 _
  have hr₃S : r₃ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard8 _
  have hr₄S : r₄ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard8 _
  have hr₅S : r₅ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard8 _
  have hr₆S : r₆ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard8 _
  have hr₇S : r₇ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard8 _
  have hr₈S : r₈ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard8 _
  have hr₁₂ : r₁ < r₂ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₂₃ : r₂ < r₃ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₃₄ : r₃ < r₄ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₄₅ : r₄ < r₅ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₅₆ : r₅ < r₆ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₆₇ : r₆ < r₇ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₇₈ : r₇ < r₈ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hS1_eq : S₁ = {r₁, r₂, r₃, r₄, r₅, r₆, r₇, r₈} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    · rw [hcard8, Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_pair (by omega)]
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
  obtain ⟨hr₂p, _, he₂pos, hl₂p, hσr₂⟩ := extract r₂ hr₂S
  obtain ⟨hr₃p, _, he₃pos, hl₃p, hσr₃⟩ := extract r₃ hr₃S
  obtain ⟨hr₄p, _, he₄pos, hl₄p, hσr₄⟩ := extract r₄ hr₄S
  obtain ⟨hr₅p, _, he₅pos, hl₅p, hσr₅⟩ := extract r₅ hr₅S
  obtain ⟨hr₆p, _, he₆pos, hl₆p, hσr₆⟩ := extract r₆ hr₆S
  obtain ⟨hr₇p, _, he₇pos, hl₇p, hσr₇⟩ := extract r₇ hr₇S
  obtain ⟨hr₈p, _, he₈pos, _, hσr₈⟩ := extract r₈ hr₈S
  have he₇₈ : s.factorization r₈ < s.factorization r₇ :=
    exp_anti_of_sigma_eq'' hr₇p hr₈p hr₇₈ he₇pos hσr₇ hσr₈
  have he₆₇ : s.factorization r₇ < s.factorization r₆ :=
    exp_anti_of_sigma_eq'' hr₆p hr₇p hr₆₇ he₆pos hσr₆ hσr₇
  have he₅₆ : s.factorization r₆ < s.factorization r₅ :=
    exp_anti_of_sigma_eq'' hr₅p hr₆p hr₅₆ he₅pos hσr₅ hσr₆
  have he₄₅ : s.factorization r₅ < s.factorization r₄ :=
    exp_anti_of_sigma_eq'' hr₄p hr₅p hr₄₅ he₄pos hσr₄ hσr₅
  have he₃₄ : s.factorization r₄ < s.factorization r₃ :=
    exp_anti_of_sigma_eq'' hr₃p hr₄p hr₃₄ he₃pos hσr₃ hσr₄
  have he₂₃ : s.factorization r₃ < s.factorization r₂ :=
    exp_anti_of_sigma_eq'' hr₂p hr₃p hr₂₃ he₂pos hσr₂ hσr₃
  have he₁₂ : s.factorization r₂ < s.factorization r₁ :=
    exp_anti_of_sigma_eq'' hr₁p hr₂p hr₁₂ he₁pos hσr₁ hσr₂
  have hprod_eq : (∏ r ∈ S₁, l r) = l r₁ * l r₂ * l r₃ * l r₄ * l r₅ * l r₆ * l r₇ * l r₈ := by
    rw [hS1_eq, Finset.prod_insert (by simp; omega),
      Finset.prod_insert (by simp; omega),
      Finset.prod_insert (by simp; omega),
      Finset.prod_insert (by simp; omega),
      Finset.prod_insert (by simp; omega),
      Finset.prod_insert (by simp; omega),
      Finset.prod_pair (by omega)]
    ring
  obtain ⟨hne, hmoment⟩ := even_index_large_min_exponent_bound hp hpo hs hu hσq hplus hσs
  have hrmax_eq : S₁.max' hne = r₈ := by
    refine le_antisymm (Finset.max'_le S₁ hne r₈ fun x hx => ?_) (Finset.le_max' S₁ r₈ hr₈S)
    rw [hS1_eq] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  by_cases he₈_eq1 : s.factorization r₈ = 1
  · have hmax1 : s.factorization (S₁.max' hne) = 1 := hrmax_eq ▸ he₈_eq1
    have hp_lt := even_index_max_exp_one_bound hp hpo hs hu hσq hplus hσs hne hmax1
    change p < 4 * (∏ r ∈ S₁, l r) ^ 2 at hp_lt
    rw [hprod_eq] at hp_lt
    exact refute_card_eight_caseA hp hr₁p hr₁o he₈_eq1 he₇₈ he₆₇ he₅₆ he₄₅ he₃₄ he₂₃ he₁₂
      hl₁p hl₂p hl₃p hl₄p hl₅p hl₆p hl₇p hσr₁ hp_lt
  · have he₈_ge2 : 2 ≤ s.factorization r₈ := by omega
    have h2_all : ∀ r ∈ S₁, 2 ≤ s.factorization r := by
      intro r hrS
      rw [hS1_eq] at hrS
      simp only [Finset.mem_insert, Finset.mem_singleton] at hrS
      rcases hrS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have hp3_lt := hmoment 2 (by decide) h2_all
    change p ^ 3 < (2 * S₁.card * ∏ r ∈ S₁, l r) ^ 4 at hp3_lt
    rw [hcard8, hprod_eq] at hp3_lt
    have hp3_lt' : p ^ 3 <
        (16 * (l r₁ * l r₂ * l r₃ * l r₄ * l r₅ * l r₆ * l r₇ * l r₈)) ^ 4 := by
      simpa [show 2 * 8 = 16 by decide, mul_assoc] using hp3_lt
    exact refute_card_eight_caseB hp hr₁p hr₁o he₈_ge2 he₇₈ he₆₇ he₅₆ he₄₅ he₃₄ he₂₃ he₁₂
      hl₁p hl₂p hl₃p hl₄p hl₅p hl₆p hl₇p hσr₁ hp3_lt'

/-- Every even prime-power component index `p ^ (2 * u)` forces at least nine
simultaneous odd-prime-base repunit representations of `p`. -/
theorem even_index_forces_nine_repunits {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    HasNineOddPrimeRepunits p := by
  let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
  let S₁ := s.primeFactors.filter (v · = 1)
  have hS1_ge9 : 9 ≤ S₁.card := even_index_nine_le_S1_card hp hpo hs hu hσq hplus hσs
  let f := S₁.orderEmbOfFin (rfl : S₁.card = S₁.card)
  let r₁ := f ⟨0, by omega⟩
  let r₂ := f ⟨1, by omega⟩
  let r₃ := f ⟨2, by omega⟩
  let r₄ := f ⟨3, by omega⟩
  let r₅ := f ⟨4, by omega⟩
  let r₆ := f ⟨5, by omega⟩
  let r₇ := f ⟨6, by omega⟩
  let r₈ := f ⟨7, by omega⟩
  let r₉ := f ⟨8, by omega⟩
  have hr₁S : r₁ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₂S : r₂ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₃S : r₃ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₄S : r₄ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₅S : r₅ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₆S : r₆ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₇S : r₇ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₈S : r₈ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₉S : r₉ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₁₂ : r₁ < r₂ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₂₃ : r₂ < r₃ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₃₄ : r₃ < r₄ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₄₅ : r₄ < r₅ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₅₆ : r₅ < r₆ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₆₇ : r₆ < r₇ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₇₈ : r₇ < r₈ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₈₉ : r₈ < r₉ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
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
  obtain ⟨hr₇p, hr₇o, hl₇p, hl₇_gt2, hgr₇⟩ := extract r₇ hr₇S
  obtain ⟨hr₈p, hr₈o, hl₈p, hl₈_gt2, hgr₈⟩ := extract r₈ hr₈S
  obtain ⟨hr₉p, hr₉o, hl₉p, hl₉_gt2, hgr₉⟩ := extract r₉ hr₉S
  exact ⟨r₁, r₂, r₃, r₄, r₅, r₆, r₇, r₈, r₉,
    2 * s.factorization r₁ + 1, 2 * s.factorization r₂ + 1, 2 * s.factorization r₃ + 1,
    2 * s.factorization r₄ + 1, 2 * s.factorization r₅ + 1, 2 * s.factorization r₆ + 1,
    2 * s.factorization r₇ + 1, 2 * s.factorization r₈ + 1, 2 * s.factorization r₉ + 1,
    hr₁p, hr₁o, hr₂p, hr₂o, hr₃p, hr₃o, hr₄p, hr₄o, hr₅p, hr₅o, hr₆p, hr₆o,
    hr₇p, hr₇o, hr₈p, hr₈o, hr₉p, hr₉o,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega,
    by omega, by omega, by omega,
    by omega, by omega,
    by omega,
    hl₁p, hl₁_gt2, hl₂p, hl₂_gt2, hl₃p, hl₃_gt2, hl₄p, hl₄_gt2, hl₅p, hl₅_gt2,
    hl₆p, hl₆_gt2, hl₇p, hl₇_gt2, hl₈p, hl₈_gt2, hl₉p, hl₉_gt2,
    hgr₁, hgr₂, hgr₃, hgr₄, hgr₅, hgr₆, hgr₇, hgr₈, hgr₉⟩

private lemma two_mul_add_one_lt_three_pow''' {e : ℕ} (he : 1 ≤ e) :
    2 * e + 1 < 3 ^ (2 * e) := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hpos : 1 ≤ 3 ^ (2 * k) := Nat.one_le_pow _ _ (by decide)
    calc 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
      _ < 3 ^ (2 * k) + 2 := by omega
      _ < 9 * 3 ^ (2 * k) := by omega
      _ = 3 ^ (2 * (k + 1)) := by ring

private lemma even_index_S1_ssubset_primeFactors''' {q p s u : ℕ}
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
    have hlt := two_mul_add_one_lt_three_pow''' hu
    rw [h2u_eq] at hlt
    omega
  exact lt_of_le_of_ne (Finset.filter_subset _ _) hS1_ne_full

/-- Unconditional strengthening at any even prime-power component index `i = p ^ (2 * u)`:
`p` has at least nine simultaneous odd-prime-base repunit representations and `N` has
at least 12 distinct prime factors. -/
theorem even_prime_power_component_forces_nine_repunits_and_twelve_primes {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    HasNineOddPrimeRepunits p ∧ 12 ≤ N.primeFactors.card := by
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
  have hnine := even_index_forces_nine_repunits hp hpo hso hu hσ hplus hσs
  have hS1_ge9 := even_index_nine_le_S1_card hp hpo hso hu hσ hplus hσs
  have hS1_ssub := even_index_S1_ssubset_primeFactors''' hp hso hu hσ hplus hσs
  have hs_ge10 : 10 ≤ s.primeFactors.card := by
    have := Finset.card_lt_card hS1_ssub
    omega
  have hn := prime_count_of_even_index_split hq hp hmo hso hu hqm hcop hform hms
  exact ⟨hnine, by omega⟩

/-- At any even prime-power component index `i = p ^ (2 * u)`, `9 ≤ S₁.card` combined with
`∏ r ∈ S₁, r ∣ u + 1` and the repunit representations forces `3234846614 ≤ u`,
`6469693228 ≤ 2 * u`, `10 ^ 19 < p`, and `10 ^ 122924171332 < p ^ (2 * u)`. -/
theorem even_index_exponent_ge_6469693228 {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    3234846614 ≤ u ∧ 6469693228 ≤ 2 * u ∧ 10 ^ 19 < p ∧ 10 ^ 122924171332 < p ^ (2 * u) := by
  let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
  let S₁ := s.primeFactors.filter (v · = 1)
  have hS1_ge9 : 9 ≤ S₁.card := even_index_nine_le_S1_card hp hpo hs hu hσq hplus hσs
  let f := S₁.orderEmbOfFin (rfl : S₁.card = S₁.card)
  let r₁ := f ⟨0, by omega⟩
  let r₂ := f ⟨1, by omega⟩
  let r₃ := f ⟨2, by omega⟩
  let r₄ := f ⟨3, by omega⟩
  let r₅ := f ⟨4, by omega⟩
  let r₆ := f ⟨5, by omega⟩
  let r₇ := f ⟨6, by omega⟩
  let r₈ := f ⟨7, by omega⟩
  let r₉ := f ⟨8, by omega⟩
  have hr₁S : r₁ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₂S : r₂ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₃S : r₃ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₄S : r₄ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₅S : r₅ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₆S : r₆ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₇S : r₇ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₈S : r₈ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₉S : r₉ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₁₂ : r₁ < r₂ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₂₃ : r₂ < r₃ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₃₄ : r₃ < r₄ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₄₅ : r₄ < r₅ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₅₆ : r₅ < r₆ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₆₇ : r₆ < r₇ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₇₈ : r₇ < r₈ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₈₉ : r₈ < r₉ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
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
  obtain ⟨hr₃p, hr₃o, he₃pos, _, hσr₃⟩ := extract r₃ hr₃S
  obtain ⟨hr₄p, hr₄o, he₄pos, hl₄p, hσr₄⟩ := extract r₄ hr₄S
  obtain ⟨hr₅p, hr₅o, he₅pos, _, hσr₅⟩ := extract r₅ hr₅S
  obtain ⟨hr₆p, hr₆o, he₆pos, hl₆p, hσr₆⟩ := extract r₆ hr₆S
  obtain ⟨hr₇p, hr₇o, he₇pos, _, hσr₇⟩ := extract r₇ hr₇S
  obtain ⟨hr₈p, hr₈o, he₈pos, _, hσr₈⟩ := extract r₈ hr₈S
  obtain ⟨hr₉p, hr₉o, he₉pos, _, hσr₉⟩ := extract r₉ hr₉S
  have hr₁_mod : r₁ % 2 = 1 := Nat.odd_iff.mp hr₁o
  have hr₁_ge3 : 3 ≤ r₁ := by have := hr₁p.two_le; omega
  have hr₂_ge5 : 5 ≤ r₂ := by have := Nat.odd_iff.mp hr₂o; omega
  have hr₃_ge7 : 7 ≤ r₃ := by have := Nat.odd_iff.mp hr₃o; omega
  have hr₄_ge11 : 11 ≤ r₄ := by
    have := Nat.odd_iff.mp hr₄o
    have h9 := ne_of_prime_not_prime hr₄p (by decide : ¬ Nat.Prime 9)
    omega
  have hr₅_ge13 : 13 ≤ r₅ := by have := Nat.odd_iff.mp hr₅o; omega
  have hr₆_ge17 : 17 ≤ r₆ := by
    have := Nat.odd_iff.mp hr₆o
    have h15 := ne_of_prime_not_prime hr₆p (by decide : ¬ Nat.Prime 15)
    omega
  have hr₇_ge19 : 19 ≤ r₇ := by have := Nat.odd_iff.mp hr₇o; omega
  have hr₈_ge23 : 23 ≤ r₈ := by
    have := Nat.odd_iff.mp hr₈o
    have h21 := ne_of_prime_not_prime hr₈p (by decide : ¬ Nat.Prime 21)
    omega
  have hr₉_ge29 : 29 ≤ r₉ := by
    have := Nat.odd_iff.mp hr₉o
    have h25 := ne_of_prime_not_prime hr₉p (by decide : ¬ Nat.Prime 25)
    have h27 := ne_of_prime_not_prime hr₉p (by decide : ¬ Nat.Prime 27)
    omega
  have hprod_dvd : (∏ r ∈ S₁, r) ∣ u + 1 :=
    (even_index_S1_exact_mod_sq hp hs hσq hplus hσs).2
  have hprod_le : ∏ r ∈ S₁, r ≤ u + 1 := Nat.le_of_dvd (by omega) hprod_dvd
  have hsub9 : ({r₁, r₂, r₃, r₄, r₅, r₆, r₇, r₈, r₉} : Finset ℕ) ⊆ S₁ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hprod9_dvd : (∏ r ∈ ({r₁, r₂, r₃, r₄, r₅, r₆, r₇, r₈, r₉} : Finset ℕ), r) ∣ ∏ r ∈ S₁, r :=
    Finset.prod_dvd_prod_of_subset _ _ id hsub9
  have hprod9_eq : (∏ r ∈ ({r₁, r₂, r₃, r₄, r₅, r₆, r₇, r₈, r₉} : Finset ℕ), r) =
      r₁ * r₂ * r₃ * r₄ * r₅ * r₆ * r₇ * r₈ * r₉ := by
    rw [Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
      Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
      Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
      Finset.prod_insert (by simp; omega), Finset.prod_pair (by omega)]
    ring
  have hprod9_le : r₁ * r₂ * r₃ * r₄ * r₅ * r₆ * r₇ * r₈ * r₉ ≤ ∏ r ∈ S₁, r := by
    rw [← hprod9_eq]
    exact Nat.le_of_dvd (Finset.prod_pos fun r hr =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1).pos) hprod9_dvd
  have h3234846615 : 3234846615 ≤ r₁ * r₂ * r₃ * r₄ * r₅ * r₆ * r₇ * r₈ * r₉ := by
    calc 3234846615 = 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 * 29 := by norm_num
      _ ≤ r₁ * r₂ * r₃ * r₄ * r₅ * r₆ * r₇ * r₈ * r₉ := by gcongr
  have hu_ge : 3234846614 ≤ u := by omega
  have hp_gt19 : 10 ^ 19 < p := by
    have he₈₉ : s.factorization r₉ < s.factorization r₈ :=
      exp_anti_of_sigma_eq'' hr₈p hr₉p hr₈₉ he₈pos hσr₈ hσr₉
    have he₇₈ : s.factorization r₈ < s.factorization r₇ :=
      exp_anti_of_sigma_eq'' hr₇p hr₈p hr₇₈ he₇pos hσr₇ hσr₈
    have he₆₇ : s.factorization r₇ < s.factorization r₆ :=
      exp_anti_of_sigma_eq'' hr₆p hr₇p hr₆₇ he₆pos hσr₆ hσr₇
    have he₅₆ : s.factorization r₆ < s.factorization r₅ :=
      exp_anti_of_sigma_eq'' hr₅p hr₆p hr₅₆ he₅pos hσr₅ hσr₆
    have he₄₅ : s.factorization r₅ < s.factorization r₄ :=
      exp_anti_of_sigma_eq'' hr₄p hr₅p hr₄₅ he₄pos hσr₄ hσr₅
    have he₃₄ : s.factorization r₄ < s.factorization r₃ :=
      exp_anti_of_sigma_eq'' hr₃p hr₄p hr₃₄ he₃pos hσr₃ hσr₄
    have he₂₃ : s.factorization r₃ < s.factorization r₂ :=
      exp_anti_of_sigma_eq'' hr₂p hr₃p hr₂₃ he₂pos hσr₂ hσr₃
    have he₁₂ : s.factorization r₂ < s.factorization r₁ :=
      exp_anti_of_sigma_eq'' hr₁p hr₂p hr₁₂ he₁pos hσr₁ hσr₂
    have he₁_ge14 : 14 ≤ s.factorization r₁ := by
      have hnot9 : 2 * s.factorization r₆ + 1 ≠ 9 := by
        intro h9; rw [h9] at hl₆p; exact absurd hl₆p (by decide)
      have hnot15 : 2 * s.factorization r₄ + 1 ≠ 15 := by
        intro h15; rw [h15] at hl₄p; exact absurd hl₄p (by decide)
      have hnot21 : 2 * s.factorization r₂ + 1 ≠ 21 := by
        intro h21; rw [h21] at hl₂p; exact absurd hl₂p (by decide)
      have hnot25 : 2 * s.factorization r₁ + 1 ≠ 25 := by
        intro h25; rw [h25] at hl₁p; exact absurd hl₁p (by decide)
      have hnot27 : 2 * s.factorization r₁ + 1 ≠ 27 := by
        intro h27; rw [h27] at hl₁p; exact absurd hl₁p (by decide)
      omega
    have hpow_lt_p : r₁ ^ (2 * s.factorization r₁) < p := by
      rw [← hσr₁]
      exact self_lt_sigma_of_one_lt (one_lt_pow₀ hr₁p.one_lt (by omega))
    by_cases he₁_ge20 : 20 ≤ s.factorization r₁
    · have h3_40 : (3 : ℕ) ^ 40 ≤ r₁ ^ (2 * s.factorization r₁) :=
        (Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 40 ≤ 2 * s.factorization r₁)).trans
          (Nat.pow_le_pow_left hr₁_ge3 (2 * s.factorization r₁))
      have hval : 10 ^ 19 < (3 : ℕ) ^ 40 := by norm_num
      omega
    · have hcases : s.factorization r₁ = 14 ∨ s.factorization r₁ = 15 ∨
          s.factorization r₁ = 16 ∨ s.factorization r₁ = 17 ∨ s.factorization r₁ = 18 ∨
          s.factorization r₁ = 19 := by omega
      rcases hcases with he1 | he1 | he1 | he1 | he1 | he1
      · -- e₁ = 14
        by_cases hr₁_ge5 : 5 ≤ r₁
        · have h5 : (5 : ℕ) ^ 28 ≤ r₁ ^ (2 * s.factorization r₁) := by
            rw [he1]; exact Nat.pow_le_pow_left hr₁_ge5 28
          have hbig : 10 ^ 19 < (5 : ℕ) ^ 28 := by norm_num
          omega
        · have hr1 : r₁ = 3 := by omega
          exact False.elim <| not_prime_of_sigma_three_pow' hp (by rwa [he1, hr1] at hσr₁)
            (by norm_num : 34315188682441 * 2 + 1 = 3 ^ (2 * 14 + 1))
            (by norm_num : 59 ∣ 34315188682441) (by decide) (by decide)
      · -- e₁ = 15
        by_cases hr₁_ge5 : 5 ≤ r₁
        · have h5 : (5 : ℕ) ^ 30 ≤ r₁ ^ (2 * s.factorization r₁) := by
            rw [he1]; exact Nat.pow_le_pow_left hr₁_ge5 30
          have hbig : 10 ^ 19 < (5 : ℕ) ^ 30 := by norm_num
          omega
        · have hr1 : r₁ = 3 := by omega
          exact False.elim <| not_prime_of_sigma_three_pow' hp (by rwa [he1, hr1] at hσr₁)
            (by norm_num : 308836698141973 * 2 + 1 = 3 ^ (2 * 15 + 1))
            (by norm_num : 683 ∣ 308836698141973) (by decide) (by decide)
      · rw [he1] at hl₁p
        exact absurd hl₁p (by decide)
      · rw [he1] at hl₁p
        exact absurd hl₁p (by decide)
      · -- e₁ = 18
        by_cases hr₁_ge5 : 5 ≤ r₁
        · have h5 : (5 : ℕ) ^ 36 ≤ r₁ ^ (2 * s.factorization r₁) := by
            rw [he1]; exact Nat.pow_le_pow_left hr₁_ge5 36
          have hbig : 10 ^ 19 < (5 : ℕ) ^ 36 := by norm_num
          omega
        · have hr1 : r₁ = 3 := by omega
          exact False.elim <| not_prime_of_sigma_three_pow' hp (by rwa [he1, hr1] at hσr₁)
            (by norm_num : 225141952945498681 * 2 + 1 = 3 ^ (2 * 18 + 1))
            (by norm_num : 13097927 ∣ 225141952945498681) (by decide) (by decide)
      · rw [he1] at hl₁p
        exact absurd hl₁p (by decide)
  have h2u_ge : 6469693228 ≤ 2 * u := by omega
  have hpow_gt : 10 ^ 122924171332 < p ^ (2 * u) := by
    have h1 : (10 ^ 19) ^ 6469693228 = 10 ^ (19 * 6469693228) := (pow_mul 10 19 6469693228).symm
    have h2 : 19 * 6469693228 = 122924171332 := by norm_num
    have hpow1 : 10 ^ 122924171332 = (10 ^ 19) ^ 6469693228 :=
      (congrArg (10 ^ ·) h2).symm.trans h1.symm
    have hpow2 : (10 ^ 19) ^ 6469693228 < p ^ 6469693228 :=
      pow_lt_pow_left₀ hp_gt19 (Nat.zero_le _) (by decide)
    have hpow3 : p ^ 6469693228 ≤ p ^ (2 * u) :=
      pow_le_pow_right₀ hp.one_le h2u_ge
    exact lt_of_eq_of_lt hpow1 (lt_of_lt_of_le hpow2 hpow3)
  exact ⟨hu_ge, h2u_ge, hp_gt19, hpow_gt⟩

/-- Every even prime-power component index `i = p ^ j` of an odd perfect number
satisfies `6469693228 ≤ j`, `10 ^ 122924171332 < i`, and `10 ^ 122924171332 < N`. -/
theorem even_prime_power_component_size_gt_ten_pow_122924171332 {N q a b i p j : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b)
    (hl : sigma 1 b = q ^ a * i) (hr : sigma 1 (q ^ a) * i = 2 * b)
    (hp : p.Prime) (hj : 0 < j) (hje : Even j) (hi : i = p ^ j) :
    6469693228 ≤ j ∧ 10 ^ 122924171332 < i ∧ 10 ^ 122924171332 < N := by
  rcases hje with ⟨u, hu'⟩
  have hj2 : j = 2 * u := by omega
  have hu : 0 < u := by omega
  have hi_even : i = p ^ (2 * u) := hj2 ▸ hi
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
  have hp2 : p ≠ 2 := by
    intro hp2
    rw [hp2] at hi_even
    have h4 : 4 ∣ 2 * b := hr ▸ hi_even ▸ (pow_dvd_pow 2 (by omega : 2 ≤ 2 * u)).trans (dvd_mul_left _ _)
    have := hbo.not_two_dvd_nat
    omega
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
    even_index_exponent_ge_6469693228 hp hpo hs hu hσq hplus hσs
  have hj_ge : 6469693228 ≤ j := h2u_ge.trans_eq hj2.symm
  have hi_gt : 10 ^ 122924171332 < i := lt_of_lt_of_eq hpow_gt hi_even.symm
  exact ⟨hj_ge, hi_gt, hi_gt.trans hi_lt_N⟩

end OddPerfect
