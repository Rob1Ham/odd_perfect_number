module

public import OddPerfect.SextupleRepunitObstruction
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

/-- The same integer has prime-length repunit representations in seven
distinct odd prime bases. -/
@[expose] def HasSevenOddPrimeRepunits (z : ℕ) : Prop :=
  ∃ r₁ r₂ r₃ r₄ r₅ r₆ r₇ l₁ l₂ l₃ l₄ l₅ l₆ l₇ : ℕ,
    r₁.Prime ∧ Odd r₁ ∧ r₂.Prime ∧ Odd r₂ ∧ r₃.Prime ∧ Odd r₃ ∧
    r₄.Prime ∧ Odd r₄ ∧ r₅.Prime ∧ Odd r₅ ∧ r₆.Prime ∧ Odd r₆ ∧
    r₇.Prime ∧ Odd r₇ ∧
    r₁ ≠ r₂ ∧ r₁ ≠ r₃ ∧ r₁ ≠ r₄ ∧ r₁ ≠ r₅ ∧ r₁ ≠ r₆ ∧ r₁ ≠ r₇ ∧
    r₂ ≠ r₃ ∧ r₂ ≠ r₄ ∧ r₂ ≠ r₅ ∧ r₂ ≠ r₆ ∧ r₂ ≠ r₇ ∧
    r₃ ≠ r₄ ∧ r₃ ≠ r₅ ∧ r₃ ≠ r₆ ∧ r₃ ≠ r₇ ∧
    r₄ ≠ r₅ ∧ r₄ ≠ r₆ ∧ r₄ ≠ r₇ ∧
    r₅ ≠ r₆ ∧ r₅ ≠ r₇ ∧
    r₆ ≠ r₇ ∧
    l₁.Prime ∧ 2 < l₁ ∧ l₂.Prime ∧ 2 < l₂ ∧ l₃.Prime ∧ 2 < l₃ ∧
    l₄.Prime ∧ 2 < l₄ ∧ l₅.Prime ∧ 2 < l₅ ∧ l₆.Prime ∧ 2 < l₆ ∧
    l₇.Prime ∧ 2 < l₇ ∧
    geometricBlock r₁ l₁ = z ∧ geometricBlock r₂ l₂ = z ∧
    geometricBlock r₃ l₃ = z ∧ geometricBlock r₄ l₄ = z ∧
    geometricBlock r₅ l₅ = z ∧ geometricBlock r₆ l₆ = z ∧
    geometricBlock r₇ l₇ = z

/-- Exponential domination `144 * (2 * e + 1) ^ 12 ≤ 3 ^ (2 * e)` for `24 ≤ e`. -/
theorem hundred_forty_four_mul_odd_pow12_le_three_pow {e : ℕ} (he : 24 ≤ e) :
    144 * (2 * e + 1) ^ 12 ≤ 3 ^ (2 * e) := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hstep : 7 * (2 * (k + 1) + 1) ≤ 8 * (2 * k + 1) := by omega
    have hpow12 : 7 ^ 12 * (2 * (k + 1) + 1) ^ 12 ≤ 8 ^ 12 * (2 * k + 1) ^ 12 := by
      calc 7 ^ 12 * (2 * (k + 1) + 1) ^ 12
          = (7 * (2 * (k + 1) + 1)) ^ 12 := by ring
        _ ≤ (8 * (2 * k + 1)) ^ 12 := Nat.pow_le_pow_left hstep 12
        _ = 8 ^ 12 * (2 * k + 1) ^ 12 := by ring
    have hscale : 7 ^ 12 * (144 * (2 * (k + 1) + 1) ^ 12) ≤
        7 ^ 12 * 3 ^ (2 * (k + 1)) := by
      calc 7 ^ 12 * (144 * (2 * (k + 1) + 1) ^ 12)
          = 144 * (7 ^ 12 * (2 * (k + 1) + 1) ^ 12) := by ring
        _ ≤ 144 * (8 ^ 12 * (2 * k + 1) ^ 12) := Nat.mul_le_mul_left 144 hpow12
        _ = 8 ^ 12 * (144 * (2 * k + 1) ^ 12) := by ring
        _ ≤ (9 * 7 ^ 12) * (144 * (2 * k + 1) ^ 12) :=
            Nat.mul_le_mul_right _ (by norm_num)
        _ ≤ (9 * 7 ^ 12) * 3 ^ (2 * k) := Nat.mul_le_mul_left _ ih
        _ = 7 ^ 12 * 3 ^ (2 * (k + 1)) := by
            rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]; ring
    exact le_of_mul_le_mul_left hscale (by decide : 0 < 7 ^ 12)

private lemma sigma_prime_pow_lt_of_base_lt''' {a b e : ℕ} (ha : a.Prime) (hb : b.Prime)
    (hab : a < b) (he : 0 < e) : sigma 1 (a ^ e) < sigma 1 (b ^ e) := by
  rw [sigma_one_apply_prime_pow ha, sigma_one_apply_prime_pow hb]
  exact Finset.sum_lt_sum (fun j _ => Nat.pow_le_pow_left hab.le j)
    ⟨1, Finset.mem_range.mpr (by omega), by simpa using hab⟩

private lemma sigma_prime_pow_le_of_exp_le''' {r a b : ℕ} (hr : r.Prime) (hab : a ≤ b) :
    sigma 1 (r ^ a) ≤ sigma 1 (r ^ b) := by
  rw [sigma_one_apply_prime_pow hr, sigma_one_apply_prime_pow hr]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

private lemma exp_anti_of_sigma_eq' {p s a b : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hab : a < b) (hfa : 0 < s.factorization a)
    (hσa : sigma 1 (a ^ (2 * s.factorization a)) = p)
    (hσb : sigma 1 (b ^ (2 * s.factorization b)) = p) :
    s.factorization b < s.factorization a := by
  by_contra! hle
  have hlt : sigma 1 (a ^ (2 * s.factorization a)) < sigma 1 (b ^ (2 * s.factorization a)) :=
    sigma_prime_pow_lt_of_base_lt''' ha hb hab (by omega)
  have hle' : sigma 1 (b ^ (2 * s.factorization a)) ≤ sigma 1 (b ^ (2 * s.factorization b)) :=
    sigma_prime_pow_le_of_exp_le''' hb (by omega)
  omega

private lemma even_index_P_L_lt_SumCoef_and_dvd' {q p s u : ℕ}
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
  have hS1_ge6 : 6 ≤ S₁.card := even_index_six_le_S1_card hp hpo hs hu hσq hplus hσs
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

/-- General symbolic-cardinality bound on the single-copy primes `S₁` at any even
prime-power component index `p ^ (2 * u)`, without fixing `S₁.card`. -/
theorem even_index_symbolic_S1_bound {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    let S₁ := s.primeFactors.filter (v · = 1)
    let P_L := ∏ r ∈ S₁, (2 * s.factorization r + 1)
    p < 4 * S₁.card ^ 2 * P_L ^ 2 ∧
      P_L ∣ (p - 1) / 2 ∧
      (∏ r ∈ S₁, r) ∣ u + 1 ∧
      p ≤ 8 * (u + 1) * 128 ^ (2 * u).sqrt := by
  intro v S₁ P_L
  let l (r : ℕ) := 2 * s.factorization r + 1
  let SumCoef := ∑ r ∈ S₁, 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t
  obtain ⟨hlt_L, hp_dvd⟩ := even_index_P_L_lt_SumCoef_and_dvd' hp hpo hs hu hσq hplus hσs
  have hlt_L' : P_L < SumCoef := hlt_L
  have hle_sub : p ≤ SumCoef - P_L := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt_L') hp_dvd
  have hPL_pos : 0 < P_L := Finset.prod_pos fun _ _ => by omega
  have hp_lt_Sum : p < SumCoef := by omega
  have hS1_ge6 : 6 ≤ S₁.card := even_index_six_le_S1_card hp hpo hs hu hσq hplus hσs
  have hS1_pos : 0 < S₁.card := by omega
  have hS1_ne : S₁.Nonempty := Finset.card_pos.mp hS1_pos
  let r_max := S₁.max' hS1_ne
  have hr_max_mem : r_max ∈ S₁ := Finset.max'_mem S₁ hS1_ne
  have hr_max_le : ∀ r ∈ S₁, r ≤ r_max := fun r hr => Finset.le_max' S₁ r hr
  obtain ⟨hr_max_pf, hr_max_v⟩ := Finset.mem_filter.mp hr_max_mem
  have hr_max_p : r_max.Prime := Nat.prime_of_mem_primeFactors hr_max_pf
  have hr_max_dvd : r_max ∣ s := Nat.dvd_of_mem_primeFactors hr_max_pf
  have he_max : 1 ≤ s.factorization r_max :=
    (hr_max_p.dvd_iff_one_le_factorization hs.pos.ne').mp hr_max_dvd
  obtain ⟨_, hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  have hσ_max : sigma 1 (r_max ^ (2 * s.factorization r_max)) = p := by
    have H := (hparts r_max hr_max_pf).2
    dsimp only at H
    change sigma 1 (r_max ^ (2 * s.factorization r_max)) = p ^ v r_max at H
    rwa [hr_max_v, pow_one] at H
  have hr_max_sq_lt_p : r_max ^ 2 < p := by
    have hrange : range 3 ⊆ range (2 * s.factorization r_max + 1) :=
      Finset.range_mono (by omega : 3 ≤ 2 * s.factorization r_max + 1)
    have hsum3 : 1 + r_max + r_max ^ 2 ≤ sigma 1 (r_max ^ (2 * s.factorization r_max)) := by
      rw [sigma_one_apply_prime_pow hr_max_p]
      calc 1 + r_max + r_max ^ 2 = ∑ j ∈ range 3, r_max ^ j := by
            simp [Finset.sum_range_succ, Nat.add_assoc]
        _ ≤ ∑ j ∈ range (2 * s.factorization r_max + 1), r_max ^ j :=
            Finset.sum_le_sum_of_subset hrange
    rw [hσ_max] at hsum3
    omega
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
  have hr_max_sq_lt : r_max * r_max < (2 * S₁.card * P_L) * r_max := by
    calc r_max * r_max = r_max ^ 2 := by ring
      _ < p := hr_max_sq_lt_p
      _ < 2 * S₁.card * P_L * r_max := hp_lt_prod
  have hr_max_lt : r_max < 2 * S₁.card * P_L :=
    lt_of_mul_lt_mul_right hr_max_sq_lt (Nat.zero_le r_max)
  have hp_lt_sym : p < 4 * S₁.card ^ 2 * P_L ^ 2 := by
    have hpos_coeff : 0 < 2 * S₁.card * P_L :=
      Nat.mul_pos (Nat.mul_pos (by decide) hS1_pos) hPL_pos
    calc p < 2 * S₁.card * P_L * r_max := hp_lt_prod
      _ < 2 * S₁.card * P_L * (2 * S₁.card * P_L) :=
          Nat.mul_lt_mul_of_pos_left hr_max_lt hpos_coeff
      _ = 4 * S₁.card ^ 2 * P_L ^ 2 := by ring
  exact ⟨hp_lt_sym,
    (even_index_repunit_lengths_dvd_pred hp hpo hs hσq hplus hσs).2,
    (even_index_S1_exact_mod_sq hp hs hσq hplus hσs).2,
    even_index_base_subexponential hp hpo hs hu hσq hplus hσs⟩

private lemma sigma_three_pow_mul_two_add_one (m : ℕ) :
    sigma 1 (3 ^ m) * 2 + 1 = 3 ^ (m + 1) := by
  rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
  have hg := geom_sum_mul_add (2 : ℕ) (m + 1)
  rwa [show (2 : ℕ) + 1 = 3 by decide] at hg

private lemma sigma_five_pow_mul_four_add_one (m : ℕ) :
    sigma 1 (5 ^ m) * 4 + 1 = 5 ^ (m + 1) := by
  rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 5)]
  have hg := geom_sum_mul_add (4 : ℕ) (m + 1)
  rwa [show (4 : ℕ) + 1 = 5 by decide] at hg

private lemma not_prime_of_sigma_three_pow {p m d val : ℕ}
    (hp : p.Prime) (hσ : sigma 1 (3 ^ m) = p)
    (hpow : val * 2 + 1 = 3 ^ (m + 1)) (hdvd : d ∣ val) (hd1 : 1 < d) (hdv : d < val) :
    False := by
  have h1 := sigma_three_pow_mul_two_add_one m
  rw [hσ] at h1
  have hp_eq : p = val := by omega
  rw [hp_eq] at hp
  have := hp.eq_one_or_self_of_dvd d hdvd
  omega

private lemma not_prime_of_sigma_five_pow {p m d val : ℕ}
    (hp : p.Prime) (hσ : sigma 1 (5 ^ m) = p)
    (hpow : val * 4 + 1 = 5 ^ (m + 1)) (hdvd : d ∣ val) (hd1 : 1 < d) (hdv : d < val) :
    False := by
  have h1 := sigma_five_pow_mul_four_add_one m
  rw [hσ] at h1
  have hp_eq : p = val := by omega
  rw [hp_eq] at hp
  have := hp.eq_one_or_self_of_dvd d hdvd
  omega

private lemma mul6_le {a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆ : ℕ}
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (h₃ : a₃ ≤ b₃)
    (h₄ : a₄ ≤ b₄) (h₅ : a₅ ≤ b₅) (h₆ : a₆ ≤ b₆) :
    a₁ * a₂ * a₃ * a₄ * a₅ * a₆ ≤ b₁ * b₂ * b₃ * b₄ * b₅ * b₆ := by
  gcongr

private lemma refute_card_six_arith {p r₁ e₁ e₂ e₃ e₄ e₅ e₆ : ℕ}
    (hp : p.Prime) (hr₁p : r₁.Prime) (hr₁o : Odd r₁)
    (he₆ : 1 ≤ e₆) (he₅₆ : e₆ < e₅) (he₄₅ : e₅ < e₄)
    (he₃₄ : e₄ < e₃) (he₂₃ : e₃ < e₂) (he₁₂ : e₂ < e₁)
    (hl₁p : (2 * e₁ + 1).Prime) (hl₂p : (2 * e₂ + 1).Prime)
    (hl₃p : (2 * e₃ + 1).Prime) (hl₄p : (2 * e₄ + 1).Prime)
    (hl₅p : (2 * e₅ + 1).Prime) (_hl₆p : (2 * e₆ + 1).Prime)
    (hσr₁ : sigma 1 (r₁ ^ (2 * e₁)) = p)
    (hp_lt : p < 144 * ((2 * e₁ + 1) * (2 * e₂ + 1) * (2 * e₃ + 1) *
      (2 * e₄ + 1) * (2 * e₅ + 1) * (2 * e₆ + 1)) ^ 2) : False := by
  have hl_ne9 : ∀ {x : ℕ}, x.Prime → x ≠ 9 := fun hx h => absurd (h ▸ hx) (by decide)
  have hl_ne15 : ∀ {x : ℕ}, x.Prime → x ≠ 15 := fun hx h => absurd (h ▸ hx) (by decide)
  have he₃ : 5 ≤ e₃ := by
    have := hl_ne9 hl₃p
    omega
  have he₂ : 6 ≤ e₂ := by omega
  have he₁ : 8 ≤ e₁ := by
    have := hl_ne15 hl₁p
    omega
  have hr₁_mod : r₁ % 2 = 1 := Nat.odd_iff.mp hr₁o
  have hr₁_ge3 : 3 ≤ r₁ := by have := hr₁p.two_le; omega
  have hr₁_pow_lt_p : r₁ ^ (2 * e₁) < p := by
    rw [← hσr₁]
    exact self_lt_sigma_of_one_lt (one_lt_pow₀ hr₁p.one_lt (by omega))
  let l₁ := 2 * e₁ + 1
  let l₂ := 2 * e₂ + 1
  let l₃ := 2 * e₃ + 1
  let l₄ := 2 * e₄ + 1
  let l₅ := 2 * e₅ + 1
  let l₆ := 2 * e₆ + 1
  by_cases he₁_big : 24 ≤ e₁
  · have hl_le : l₂ ≤ l₁ ∧ l₃ ≤ l₁ ∧ l₄ ≤ l₁ ∧ l₅ ≤ l₁ ∧ l₆ ≤ l₁ := by
      dsimp [l₁, l₂, l₃, l₄, l₅, l₆]
      omega
    rcases hl_le with ⟨h2, h3, h4, h5, h6⟩
    have hprod_le : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ ≤ l₁ ^ 6 := by
      calc l₁ * l₂ * l₃ * l₄ * l₅ * l₆ ≤ l₁ * l₁ * l₁ * l₁ * l₁ * l₁ := by gcongr
        _ = l₁ ^ 6 := by ring
    have hp_lt_144 : p < 144 * (2 * e₁ + 1) ^ 12 := by
      calc p < 144 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆) ^ 2 := hp_lt
        _ ≤ 144 * (l₁ ^ 6) ^ 2 := by gcongr
        _ = 144 * (2 * e₁ + 1) ^ 12 := by dsimp [l₁]; ring
    have h144 := hundred_forty_four_mul_odd_pow12_le_three_pow he₁_big
    have h3_le : 3 ^ (2 * e₁) ≤ r₁ ^ (2 * e₁) := Nat.pow_le_pow_left hr₁_ge3 (2 * e₁)
    omega
  · have hl₂_le : l₂ ≤ l₁ - 2 := by dsimp [l₁, l₂]; omega
    have hl₃_le : l₃ ≤ l₁ - 4 := by dsimp [l₁, l₃]; omega
    have hl₄_le : l₄ ≤ l₁ - 6 := by dsimp [l₁, l₄]; omega
    have hl₅_le : l₅ ≤ l₁ - 8 := by dsimp [l₁, l₅]; omega
    have hl₆_le : l₆ ≤ l₁ - 10 := by dsimp [l₁, l₆]; omega
    rcases (by omega : e₁ = 8 ∨ e₁ = 9 ∨ e₁ = 10 ∨ e₁ = 11 ∨ e₁ = 12 ∨ e₁ = 13 ∨
        e₁ = 14 ∨ e₁ = 15 ∨ e₁ = 16 ∨ e₁ = 17 ∨ e₁ = 18 ∨ e₁ = 19 ∨ e₁ = 20 ∨
        e₁ = 21 ∨ e₁ = 22 ∨ e₁ = 23) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · -- e₁ = 8, l₁ = 17
      have hne15_2 : l₂ ≠ 15 := hl_ne15 hl₂p
      have hne9_4 : l₄ ≠ 9 := hl_ne9 hl₄p
      have hp_bound : p < 7 ^ (2 * 8) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ ≤ 17 * 13 * 11 * 7 * 5 * 3 :=
          mul6_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
        have hsq : 144 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆) ^ 2 < 7 ^ (2 * 8) := by
          calc 144 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆) ^ 2
              ≤ 144 * (17 * 13 * 11 * 7 * 5 * 3) ^ 2 := by gcongr
            _ < 7 ^ (2 * 8) := by norm_num
        exact hp_lt.trans hsq
      by_cases hr₁_ge7 : 7 ≤ r₁
      · have h7 : 7 ^ (2 * 8) ≤ r₁ ^ (2 * 8) := Nat.pow_le_pow_left hr₁_ge7 (2 * 8)
        omega
      · rcases (by omega : r₁ = 3 ∨ r₁ = 5) with rfl | rfl
        · exact not_prime_of_sigma_three_pow hp hσr₁
            (by norm_num : 64570081 * 2 + 1 = 3 ^ (2 * 8 + 1))
            (by norm_num : 1871 ∣ 64570081) (by decide) (by decide)
        · exact not_prime_of_sigma_five_pow hp hσr₁
            (by norm_num : 190734863281 * 4 + 1 = 5 ^ (2 * 8 + 1))
            (by norm_num : 409 ∣ 190734863281) (by decide) (by decide)
    · -- e₁ = 9, l₁ = 19
      have hne15_3 : l₃ ≠ 15 := hl_ne15 hl₃p
      have hne9_5 : l₅ ≠ 9 := hl_ne9 hl₅p
      have hp_bound : p < 7 ^ (2 * 9) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ ≤ 19 * 17 * 13 * 11 * 7 * 5 :=
          mul6_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
        have hsq : 144 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆) ^ 2 < 7 ^ (2 * 9) := by
          calc 144 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆) ^ 2
              ≤ 144 * (19 * 17 * 13 * 11 * 7 * 5) ^ 2 := by gcongr
            _ < 7 ^ (2 * 9) := by norm_num
        exact hp_lt.trans hsq
      by_cases hr₁_ge7 : 7 ≤ r₁
      · have h7 : 7 ^ (2 * 9) ≤ r₁ ^ (2 * 9) := Nat.pow_le_pow_left hr₁_ge7 (2 * 9)
        omega
      · rcases (by omega : r₁ = 3 ∨ r₁ = 5) with rfl | rfl
        · exact not_prime_of_sigma_three_pow hp hσr₁
            (by norm_num : 581130733 * 2 + 1 = 3 ^ (2 * 9 + 1))
            (by norm_num : 1597 ∣ 581130733) (by decide) (by decide)
        · exact not_prime_of_sigma_five_pow hp hσr₁
            (by norm_num : 4768371582031 * 4 + 1 = 5 ^ (2 * 9 + 1))
            (by norm_num : 191 ∣ 4768371582031) (by decide) (by decide)
    · exact absurd hl₁p (by decide)
    · -- e₁ = 11, l₁ = 23
      have hp_bound : p < 7 ^ (2 * 11) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ ≤ 23 * 21 * 19 * 17 * 15 * 13 :=
          mul6_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
        have hsq : 144 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆) ^ 2 < 7 ^ (2 * 11) := by
          calc 144 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆) ^ 2
              ≤ 144 * (23 * 21 * 19 * 17 * 15 * 13) ^ 2 := by gcongr
            _ < 7 ^ (2 * 11) := by norm_num
        exact hp_lt.trans hsq
      by_cases hr₁_ge7 : 7 ≤ r₁
      · have h7 : 7 ^ (2 * 11) ≤ r₁ ^ (2 * 11) := Nat.pow_le_pow_left hr₁_ge7 (2 * 11)
        omega
      · rcases (by omega : r₁ = 3 ∨ r₁ = 5) with rfl | rfl
        · exact not_prime_of_sigma_three_pow hp hσr₁
            (by norm_num : 47071589413 * 2 + 1 = 3 ^ (2 * 11 + 1))
            (by norm_num : 47 ∣ 47071589413) (by decide) (by decide)
        · exact not_prime_of_sigma_five_pow hp hσr₁
            (by norm_num : 2980232238769531 * 4 + 1 = 5 ^ (2 * 11 + 1))
            (by norm_num : 8971 ∣ 2980232238769531) (by decide) (by decide)
    · exact absurd hl₁p (by decide)
    · exact absurd hl₁p (by decide)
    · -- e₁ = 14, l₁ = 29
      have hp_bound : p < 5 ^ (2 * 14) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ ≤ 29 * 27 * 25 * 23 * 21 * 19 :=
          mul6_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
        have hsq : 144 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆) ^ 2 < 5 ^ (2 * 14) := by
          calc 144 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆) ^ 2
              ≤ 144 * (29 * 27 * 25 * 23 * 21 * 19) ^ 2 := by gcongr
            _ < 5 ^ (2 * 14) := by norm_num
        exact hp_lt.trans hsq
      by_cases hr₁_ge5 : 5 ≤ r₁
      · have h5 : 5 ^ (2 * 14) ≤ r₁ ^ (2 * 14) := Nat.pow_le_pow_left hr₁_ge5 (2 * 14)
        omega
      · have hr1 : r₁ = 3 := by omega
        subst hr1
        exact not_prime_of_sigma_three_pow hp hσr₁
          (by norm_num : 34315188682441 * 2 + 1 = 3 ^ (2 * 14 + 1))
          (by norm_num : 59 ∣ 34315188682441) (by decide) (by decide)
    · -- e₁ = 15, l₁ = 31
      have hp_bound : p < 5 ^ (2 * 15) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ ≤ 31 * 29 * 27 * 25 * 23 * 21 :=
          mul6_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
        have hsq : 144 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆) ^ 2 < 5 ^ (2 * 15) := by
          calc 144 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆) ^ 2
              ≤ 144 * (31 * 29 * 27 * 25 * 23 * 21) ^ 2 := by gcongr
            _ < 5 ^ (2 * 15) := by norm_num
        exact hp_lt.trans hsq
      by_cases hr₁_ge5 : 5 ≤ r₁
      · have h5 : 5 ^ (2 * 15) ≤ r₁ ^ (2 * 15) := Nat.pow_le_pow_left hr₁_ge5 (2 * 15)
        omega
      · have hr1 : r₁ = 3 := by omega
        subst hr1
        exact not_prime_of_sigma_three_pow hp hσr₁
          (by norm_num : 308836698141973 * 2 + 1 = 3 ^ (2 * 15 + 1))
          (by norm_num : 683 ∣ 308836698141973) (by decide) (by decide)
    · exact absurd hl₁p (by decide)
    · exact absurd hl₁p (by decide)
    · -- e₁ = 18, l₁ = 37
      have hp_bound : p < 5 ^ (2 * 18) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ ≤ 37 * 35 * 33 * 31 * 29 * 27 :=
          mul6_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
        have hsq : 144 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆) ^ 2 < 5 ^ (2 * 18) := by
          calc 144 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆) ^ 2
              ≤ 144 * (37 * 35 * 33 * 31 * 29 * 27) ^ 2 := by gcongr
            _ < 5 ^ (2 * 18) := by norm_num
        exact hp_lt.trans hsq
      by_cases hr₁_ge5 : 5 ≤ r₁
      · have h5 : 5 ^ (2 * 18) ≤ r₁ ^ (2 * 18) := Nat.pow_le_pow_left hr₁_ge5 (2 * 18)
        omega
      · have hr1 : r₁ = 3 := by omega
        subst hr1
        exact not_prime_of_sigma_three_pow hp hσr₁
          (by norm_num : 225141952945498681 * 2 + 1 = 3 ^ (2 * 18 + 1))
          (by norm_num : 13097927 ∣ 225141952945498681) (by decide) (by decide)
    · exact absurd hl₁p (by decide)
    · -- e₁ = 20, l₁ = 41
      have hp_bound : p < 5 ^ (2 * 20) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ ≤ 41 * 39 * 37 * 35 * 33 * 31 :=
          mul6_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
        have hsq : 144 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆) ^ 2 < 5 ^ (2 * 20) := by
          calc 144 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆) ^ 2
              ≤ 144 * (41 * 39 * 37 * 35 * 33 * 31) ^ 2 := by gcongr
            _ < 5 ^ (2 * 20) := by norm_num
        exact hp_lt.trans hsq
      by_cases hr₁_ge5 : 5 ≤ r₁
      · have h5 : 5 ^ (2 * 20) ≤ r₁ ^ (2 * 20) := Nat.pow_le_pow_left hr₁_ge5 (2 * 20)
        omega
      · have hr1 : r₁ = 3 := by omega
        subst hr1
        exact not_prime_of_sigma_three_pow hp hσr₁
          (by norm_num : 18236498188585393201 * 2 + 1 = 3 ^ (2 * 20 + 1))
          (by norm_num : 83 ∣ 18236498188585393201) (by decide) (by decide)
    · -- e₁ = 21, l₁ = 43
      have hp_bound : p < 5 ^ (2 * 21) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ ≤ 43 * 41 * 39 * 37 * 35 * 33 :=
          mul6_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
        have hsq : 144 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆) ^ 2 < 5 ^ (2 * 21) := by
          calc 144 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆) ^ 2
              ≤ 144 * (43 * 41 * 39 * 37 * 35 * 33) ^ 2 := by gcongr
            _ < 5 ^ (2 * 21) := by norm_num
        exact hp_lt.trans hsq
      by_cases hr₁_ge5 : 5 ≤ r₁
      · have h5 : 5 ^ (2 * 21) ≤ r₁ ^ (2 * 21) := Nat.pow_le_pow_left hr₁_ge5 (2 * 21)
        omega
      · have hr1 : r₁ = 3 := by omega
        subst hr1
        exact not_prime_of_sigma_three_pow hp hσr₁
          (by norm_num : 164128483697268538813 * 2 + 1 = 3 ^ (2 * 21 + 1))
          (by norm_num : 431 ∣ 164128483697268538813) (by decide) (by decide)
    · exact absurd hl₁p (by decide)
    · -- e₁ = 23, l₁ = 47
      have hp_bound : p < 3 ^ (2 * 23) := by
        have hprod : l₁ * l₂ * l₃ * l₄ * l₅ * l₆ ≤ 47 * 45 * 43 * 41 * 39 * 37 :=
          mul6_le (by dsimp [l₁]; omega) (by dsimp [l₂] at *; omega) (by dsimp [l₃] at *; omega)
            (by dsimp [l₄] at *; omega) (by dsimp [l₅] at *; omega) (by dsimp [l₆] at *; omega)
        have hsq : 144 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆) ^ 2 < 3 ^ (2 * 23) := by
          calc 144 * (l₁ * l₂ * l₃ * l₄ * l₅ * l₆) ^ 2
              ≤ 144 * (47 * 45 * 43 * 41 * 39 * 37) ^ 2 := by gcongr
            _ < 3 ^ (2 * 23) := by norm_num
        exact hp_lt.trans hsq
      have h3 : 3 ^ (2 * 23) ≤ r₁ ^ (2 * 23) := Nat.pow_le_pow_left hr₁_ge3 (2 * 23)
      omega

/-- Unconditionally, at any even prime-power component index `p ^ (2 * u)`,
at least seven distinct cofactor primes return `p` with valuation `1`. -/
theorem even_index_seven_le_S1_card {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    7 ≤ (s.primeFactors.filter (v · = 1)).card := by
  intro v
  let S₁ := s.primeFactors.filter (v · = 1)
  let l (r : ℕ) := 2 * s.factorization r + 1
  have hS1_ge6 : 6 ≤ S₁.card := even_index_six_le_S1_card hp hpo hs hu hσq hplus hσs
  change 6 ≤ S₁.card at hS1_ge6
  by_contra! hlt7
  change S₁.card < 7 at hlt7
  have hcard6 : S₁.card = 6 := by omega
  let f := S₁.orderEmbOfFin hcard6
  let r₁ := f ⟨0, by decide⟩
  let r₂ := f ⟨1, by decide⟩
  let r₃ := f ⟨2, by decide⟩
  let r₄ := f ⟨3, by decide⟩
  let r₅ := f ⟨4, by decide⟩
  let r₆ := f ⟨5, by decide⟩
  have hr₁S : r₁ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard6 _
  have hr₂S : r₂ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard6 _
  have hr₃S : r₃ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard6 _
  have hr₄S : r₄ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard6 _
  have hr₅S : r₅ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard6 _
  have hr₆S : r₆ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ hcard6 _
  have hr₁₂ : r₁ < r₂ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₂₃ : r₂ < r₃ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₃₄ : r₃ < r₄ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₄₅ : r₄ < r₅ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₅₆ : r₅ < r₆ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hS1_eq : S₁ = {r₁, r₂, r₃, r₄, r₅, r₆} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    · rw [hcard6, Finset.card_insert_of_notMem (by simp; omega),
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
  have he₅₆ : s.factorization r₆ < s.factorization r₅ :=
    exp_anti_of_sigma_eq' hr₅p hr₆p hr₅₆ he₅pos hσr₅ hσr₆
  have he₄₅ : s.factorization r₅ < s.factorization r₄ :=
    exp_anti_of_sigma_eq' hr₄p hr₅p hr₄₅ he₄pos hσr₄ hσr₅
  have he₃₄ : s.factorization r₄ < s.factorization r₃ :=
    exp_anti_of_sigma_eq' hr₃p hr₄p hr₃₄ he₃pos hσr₃ hσr₄
  have he₂₃ : s.factorization r₃ < s.factorization r₂ :=
    exp_anti_of_sigma_eq' hr₂p hr₃p hr₂₃ he₂pos hσr₂ hσr₃
  have he₁₂ : s.factorization r₂ < s.factorization r₁ :=
    exp_anti_of_sigma_eq' hr₁p hr₂p hr₁₂ he₁pos hσr₁ hσr₂
  have hsym := (even_index_symbolic_S1_bound hp hpo hs hu hσq hplus hσs).1
  change p < 4 * S₁.card ^ 2 * (∏ r ∈ S₁, l r) ^ 2 at hsym
  have hprod_eq : (∏ r ∈ S₁, l r) = l r₁ * l r₂ * l r₃ * l r₄ * l r₅ * l r₆ := by
    rw [hS1_eq, Finset.prod_insert (by simp; omega),
      Finset.prod_insert (by simp; omega),
      Finset.prod_insert (by simp; omega),
      Finset.prod_insert (by simp; omega),
      Finset.prod_pair (by omega)]
    ring
  rw [hcard6, hprod_eq] at hsym
  have hp_lt : p < 144 * ((2 * s.factorization r₁ + 1) * (2 * s.factorization r₂ + 1) *
      (2 * s.factorization r₃ + 1) * (2 * s.factorization r₄ + 1) *
      (2 * s.factorization r₅ + 1) * (2 * s.factorization r₆ + 1)) ^ 2 := by
    simpa [l, show 4 * 6 ^ 2 = 144 by decide] using hsym
  exact refute_card_six_arith hp hr₁p hr₁o he₆pos he₅₆ he₄₅ he₃₄ he₂₃ he₁₂
    hl₁p hl₂p hl₃p hl₄p hl₅p hl₆p hσr₁ hp_lt

/-- Every even prime-power component index `p ^ (2 * u)` forces at least seven
simultaneous odd-prime-base repunit representations of `p`. -/
theorem even_index_forces_seven_repunits {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    HasSevenOddPrimeRepunits p := by
  let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
  let S₁ := s.primeFactors.filter (v · = 1)
  have hS1_ge7 : 7 ≤ S₁.card := even_index_seven_le_S1_card hp hpo hs hu hσq hplus hσs
  let f := S₁.orderEmbOfFin (rfl : S₁.card = S₁.card)
  let r₁ := f ⟨0, by omega⟩
  let r₂ := f ⟨1, by omega⟩
  let r₃ := f ⟨2, by omega⟩
  let r₄ := f ⟨3, by omega⟩
  let r₅ := f ⟨4, by omega⟩
  let r₆ := f ⟨5, by omega⟩
  let r₇ := f ⟨6, by omega⟩
  have hr₁S : r₁ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₂S : r₂ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₃S : r₃ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₄S : r₄ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₅S : r₅ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₆S : r₆ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₇S : r₇ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₁₂ : r₁ < r₂ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₂₃ : r₂ < r₃ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₃₄ : r₃ < r₄ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₄₅ : r₄ < r₅ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₅₆ : r₅ < r₆ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₆₇ : r₆ < r₇ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
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
  exact ⟨r₁, r₂, r₃, r₄, r₅, r₆, r₇,
    2 * s.factorization r₁ + 1, 2 * s.factorization r₂ + 1, 2 * s.factorization r₃ + 1,
    2 * s.factorization r₄ + 1, 2 * s.factorization r₅ + 1, 2 * s.factorization r₆ + 1,
    2 * s.factorization r₇ + 1,
    hr₁p, hr₁o, hr₂p, hr₂o, hr₃p, hr₃o, hr₄p, hr₄o, hr₅p, hr₅o, hr₆p, hr₆o, hr₇p, hr₇o,
    by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega,
    by omega, by omega, by omega,
    by omega, by omega,
    by omega,
    hl₁p, hl₁_gt2, hl₂p, hl₂_gt2, hl₃p, hl₃_gt2, hl₄p, hl₄_gt2, hl₅p, hl₅_gt2, hl₆p, hl₆_gt2,
    hl₇p, hl₇_gt2,
    hgr₁, hgr₂, hgr₃, hgr₄, hgr₅, hgr₆, hgr₇⟩

private lemma two_mul_add_one_lt_three_pow'' {e : ℕ} (he : 1 ≤ e) :
    2 * e + 1 < 3 ^ (2 * e) := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hpos : 1 ≤ 3 ^ (2 * k) := Nat.one_le_pow _ _ (by decide)
    calc 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
      _ < 3 ^ (2 * k) + 2 := by omega
      _ < 9 * 3 ^ (2 * k) := by omega
      _ = 3 ^ (2 * (k + 1)) := by ring

private lemma even_index_S1_ssubset_primeFactors'' {q p s u : ℕ}
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
    have hlt := two_mul_add_one_lt_three_pow'' hu
    rw [h2u_eq] at hlt
    omega
  exact lt_of_le_of_ne (Finset.filter_subset _ _) hS1_ne_full

/-- Unconditional strengthening at any even prime-power component index `i = p ^ (2 * u)`:
`p` has at least seven simultaneous odd-prime-base repunit representations and `N` has
at least 10 distinct prime factors. -/
theorem even_prime_power_component_forces_seven_repunits_and_ten_primes {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    HasSevenOddPrimeRepunits p ∧ 10 ≤ N.primeFactors.card := by
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
  have hseven := even_index_forces_seven_repunits hp hpo hso hu hσ hplus hσs
  have hS1_ge7 := even_index_seven_le_S1_card hp hpo hso hu hσ hplus hσs
  have hS1_ssub := even_index_S1_ssubset_primeFactors'' hp hso hu hσ hplus hσs
  have hs_ge8 : 8 ≤ s.primeFactors.card := by
    have := Finset.card_lt_card hS1_ssub
    omega
  have hn := prime_count_of_even_index_split hq hp hmo hso hu hqm hcop hform hms
  exact ⟨hseven, by omega⟩

/-- At any even prime-power component index `i = p ^ (2 * u)`, `7 ≤ S₁.card` combined with
`∏ r ∈ S₁, r ∣ u + 1` and the repunit representations forces `4849844 ≤ u`, `9699688 ≤ 2 * u`,
`1628413597910449 ≤ p`, and `10 ^ 145495320 < p ^ (2 * u)`. -/
theorem even_index_exponent_ge_9699688 {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    4849844 ≤ u ∧ 9699688 ≤ 2 * u ∧ 1628413597910449 ≤ p ∧ 10 ^ 145495320 < p ^ (2 * u) := by
  let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
  let S₁ := s.primeFactors.filter (v · = 1)
  have hS1_ge7 : 7 ≤ S₁.card := even_index_seven_le_S1_card hp hpo hs hu hσq hplus hσs
  let f := S₁.orderEmbOfFin (rfl : S₁.card = S₁.card)
  let r₁ := f ⟨0, by omega⟩
  let r₂ := f ⟨1, by omega⟩
  let r₃ := f ⟨2, by omega⟩
  let r₄ := f ⟨3, by omega⟩
  let r₅ := f ⟨4, by omega⟩
  let r₆ := f ⟨5, by omega⟩
  let r₇ := f ⟨6, by omega⟩
  have hr₁S : r₁ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₂S : r₂ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₃S : r₃ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₄S : r₄ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₅S : r₅ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₆S : r₆ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₇S : r₇ ∈ S₁ := Finset.orderEmbOfFin_mem S₁ rfl _
  have hr₁₂ : r₁ < r₂ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₂₃ : r₂ < r₃ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₃₄ : r₃ < r₄ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₄₅ : r₄ < r₅ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₅₆ : r₅ < r₆ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
  have hr₆₇ : r₆ < r₇ := f.strictMono (Fin.mk_lt_mk.mpr (by decide))
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
  obtain ⟨hr₆p, hr₆o, he₆pos, _, hσr₆⟩ := extract r₆ hr₆S
  obtain ⟨hr₇p, hr₇o, he₇pos, _, hσr₇⟩ := extract r₇ hr₇S
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
  have hr₇_ge19 : 19 ≤ r₇ := by have := Nat.odd_iff.mp hr₇o; omega
  have hprod_dvd : (∏ r ∈ S₁, r) ∣ u + 1 :=
    (even_index_S1_exact_mod_sq hp hs hσq hplus hσs).2
  have hprod_le : ∏ r ∈ S₁, r ≤ u + 1 := Nat.le_of_dvd (by omega) hprod_dvd
  have hsub7 : ({r₁, r₂, r₃, r₄, r₅, r₆, r₇} : Finset ℕ) ⊆ S₁ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hprod7_dvd : (∏ r ∈ ({r₁, r₂, r₃, r₄, r₅, r₆, r₇} : Finset ℕ), r) ∣ ∏ r ∈ S₁, r :=
    Finset.prod_dvd_prod_of_subset _ _ id hsub7
  have hprod7_eq : (∏ r ∈ ({r₁, r₂, r₃, r₄, r₅, r₆, r₇} : Finset ℕ), r) =
      r₁ * r₂ * r₃ * r₄ * r₅ * r₆ * r₇ := by
    rw [Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
      Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
      Finset.prod_insert (by simp; omega), Finset.prod_pair (by omega)]
    ring
  have hprod7_le : r₁ * r₂ * r₃ * r₄ * r₅ * r₆ * r₇ ≤ ∏ r ∈ S₁, r := by
    rw [← hprod7_eq]
    exact Nat.le_of_dvd (Finset.prod_pos fun r hr =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1).pos) hprod7_dvd
  have h4849845 : 4849845 ≤ r₁ * r₂ * r₃ * r₄ * r₅ * r₆ * r₇ := by
    calc 4849845 = 3 * 5 * 7 * 11 * 13 * 17 * 19 := by norm_num
      _ ≤ r₁ * r₂ * r₃ * r₄ * r₅ * r₆ * r₇ := by gcongr
  have hu_ge : 4849844 ≤ u := by omega
  have hp_ge : 1628413597910449 ≤ p := by
    have he₆₇ : s.factorization r₇ < s.factorization r₆ :=
      exp_anti_of_sigma_eq' hr₆p hr₇p hr₆₇ he₆pos hσr₆ hσr₇
    have he₅₆ : s.factorization r₆ < s.factorization r₅ :=
      exp_anti_of_sigma_eq' hr₅p hr₆p hr₅₆ he₅pos hσr₅ hσr₆
    have he₄₅ : s.factorization r₅ < s.factorization r₄ :=
      exp_anti_of_sigma_eq' hr₄p hr₅p hr₄₅ he₄pos hσr₄ hσr₅
    have he₃₄ : s.factorization r₄ < s.factorization r₃ :=
      exp_anti_of_sigma_eq' hr₃p hr₄p hr₃₄ he₃pos hσr₃ hσr₄
    have he₂₃ : s.factorization r₃ < s.factorization r₂ :=
      exp_anti_of_sigma_eq' hr₂p hr₃p hr₂₃ he₂pos hσr₂ hσr₃
    have he₁₂ : s.factorization r₂ < s.factorization r₁ :=
      exp_anti_of_sigma_eq' hr₁p hr₂p hr₁₂ he₁pos hσr₁ hσr₂
    have he₁_ge9 : 9 ≤ s.factorization r₁ := by
      have hnot9 : 2 * s.factorization r₄ + 1 ≠ 9 := by
        intro h9; rw [h9] at hl₄p; exact absurd hl₄p (by decide)
      have hnot15 : 2 * s.factorization r₂ + 1 ≠ 15 := by
        intro h15; rw [h15] at hl₂p; exact absurd hl₂p (by decide)
      omega
    have hpow_lt_p : r₁ ^ (2 * s.factorization r₁) < p := by
      rw [← hσr₁]
      exact self_lt_sigma_of_one_lt (one_lt_pow₀ hr₁p.one_lt (by omega))
    by_cases he₁_ge23 : 23 ≤ s.factorization r₁
    · have h3_46 : (3 : ℕ) ^ 46 ≤ r₁ ^ (2 * s.factorization r₁) :=
        (Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 46 ≤ 2 * s.factorization r₁)).trans
          (Nat.pow_le_pow_left hr₁_ge3 (2 * s.factorization r₁))
      have hval : 1628413597910449 ≤ (3 : ℕ) ^ 46 := by norm_num
      omega
    · have hcases : s.factorization r₁ = 9 ∨ s.factorization r₁ = 10 ∨
          s.factorization r₁ = 11 ∨ s.factorization r₁ = 12 ∨ s.factorization r₁ = 13 ∨
          s.factorization r₁ = 14 ∨ s.factorization r₁ = 15 ∨ s.factorization r₁ = 16 ∨
          s.factorization r₁ = 17 ∨ s.factorization r₁ = 18 ∨ s.factorization r₁ = 19 ∨
          s.factorization r₁ = 20 ∨ s.factorization r₁ = 21 ∨ s.factorization r₁ = 22 := by omega
      rcases hcases with he1 | he1 | he1 | he1 | he1 | he1 | he1 |
          he1 | he1 | he1 | he1 | he1 | he1 | he1
      · -- e₁ = 9
        by_cases hr₁_ge7 : 7 ≤ r₁
        · have h7 : (7 : ℕ) ^ 18 ≤ r₁ ^ (2 * s.factorization r₁) := by
            rw [he1]; exact Nat.pow_le_pow_left hr₁_ge7 18
          have hval : (7 : ℕ) ^ 18 = 1628413597910449 := by norm_num
          omega
        · have hr₁_cases : r₁ = 3 ∨ r₁ = 5 := by omega
          rcases hr₁_cases with hr1 | hr1
          · exact False.elim <| not_prime_of_sigma_three_pow hp (by rwa [he1, hr1] at hσr₁)
              (by norm_num : 581130733 * 2 + 1 = 3 ^ (2 * 9 + 1))
              (by norm_num : 1597 ∣ 581130733) (by decide) (by decide)
          · exact False.elim <| not_prime_of_sigma_five_pow hp (by rwa [he1, hr1] at hσr₁)
              (by norm_num : 4768371582031 * 4 + 1 = 5 ^ (2 * 9 + 1))
              (by norm_num : 191 ∣ 4768371582031) (by decide) (by decide)
      · rw [he1] at hl₁p
        exact absurd hl₁p (by decide)
      · -- e₁ = 11
        by_cases hr₁_ge7 : 7 ≤ r₁
        · have h7 : (7 : ℕ) ^ 22 ≤ r₁ ^ (2 * s.factorization r₁) := by
            rw [he1]; exact Nat.pow_le_pow_left hr₁_ge7 22
          have hbig : 1628413597910449 < (7 : ℕ) ^ 22 := by norm_num
          omega
        · have hr₁_cases : r₁ = 3 ∨ r₁ = 5 := by omega
          rcases hr₁_cases with hr1 | hr1
          · exact False.elim <| not_prime_of_sigma_three_pow hp (by rwa [he1, hr1] at hσr₁)
              (by norm_num : 47071589413 * 2 + 1 = 3 ^ (2 * 11 + 1))
              (by norm_num : 47 ∣ 47071589413) (by decide) (by decide)
          · exact False.elim <| not_prime_of_sigma_five_pow hp (by rwa [he1, hr1] at hσr₁)
              (by norm_num : 2980232238769531 * 4 + 1 = 5 ^ (2 * 11 + 1))
              (by norm_num : 8971 ∣ 2980232238769531) (by decide) (by decide)
      · rw [he1] at hl₁p
        exact absurd hl₁p (by decide)
      · rw [he1] at hl₁p
        exact absurd hl₁p (by decide)
      · -- e₁ = 14
        by_cases hr₁_ge5 : 5 ≤ r₁
        · have h5 : (5 : ℕ) ^ 28 ≤ r₁ ^ (2 * s.factorization r₁) := by
            rw [he1]; exact Nat.pow_le_pow_left hr₁_ge5 28
          have hbig : 1628413597910449 < (5 : ℕ) ^ 28 := by norm_num
          omega
        · have hr1 : r₁ = 3 := by omega
          exact False.elim <| not_prime_of_sigma_three_pow hp (by rwa [he1, hr1] at hσr₁)
            (by norm_num : 34315188682441 * 2 + 1 = 3 ^ (2 * 14 + 1))
            (by norm_num : 59 ∣ 34315188682441) (by decide) (by decide)
      · -- e₁ = 15
        by_cases hr₁_ge5 : 5 ≤ r₁
        · have h5 : (5 : ℕ) ^ 30 ≤ r₁ ^ (2 * s.factorization r₁) := by
            rw [he1]; exact Nat.pow_le_pow_left hr₁_ge5 30
          have hbig : 1628413597910449 < (5 : ℕ) ^ 30 := by norm_num
          omega
        · have hr1 : r₁ = 3 := by omega
          exact False.elim <| not_prime_of_sigma_three_pow hp (by rwa [he1, hr1] at hσr₁)
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
          have hbig : 1628413597910449 < (5 : ℕ) ^ 36 := by norm_num
          omega
        · have hr1 : r₁ = 3 := by omega
          exact False.elim <| not_prime_of_sigma_three_pow hp (by rwa [he1, hr1] at hσr₁)
            (by norm_num : 225141952945498681 * 2 + 1 = 3 ^ (2 * 18 + 1))
            (by norm_num : 13097927 ∣ 225141952945498681) (by decide) (by decide)
      · rw [he1] at hl₁p
        exact absurd hl₁p (by decide)
      · -- e₁ = 20
        by_cases hr₁_ge5 : 5 ≤ r₁
        · have h5 : (5 : ℕ) ^ 40 ≤ r₁ ^ (2 * s.factorization r₁) := by
            rw [he1]; exact Nat.pow_le_pow_left hr₁_ge5 40
          have hbig : 1628413597910449 < (5 : ℕ) ^ 40 := by norm_num
          omega
        · have hr1 : r₁ = 3 := by omega
          exact False.elim <| not_prime_of_sigma_three_pow hp (by rwa [he1, hr1] at hσr₁)
            (by norm_num : 18236498188585393201 * 2 + 1 = 3 ^ (2 * 20 + 1))
            (by norm_num : 83 ∣ 18236498188585393201) (by decide) (by decide)
      · -- e₁ = 21
        by_cases hr₁_ge5 : 5 ≤ r₁
        · have h5 : (5 : ℕ) ^ 42 ≤ r₁ ^ (2 * s.factorization r₁) := by
            rw [he1]; exact Nat.pow_le_pow_left hr₁_ge5 42
          have hbig : 1628413597910449 < (5 : ℕ) ^ 42 := by norm_num
          omega
        · have hr1 : r₁ = 3 := by omega
          exact False.elim <| not_prime_of_sigma_three_pow hp (by rwa [he1, hr1] at hσr₁)
            (by norm_num : 164128483697268538813 * 2 + 1 = 3 ^ (2 * 21 + 1))
            (by norm_num : 431 ∣ 164128483697268538813) (by decide) (by decide)
      · rw [he1] at hl₁p
        exact absurd hl₁p (by decide)
  have hp_gt15 : 10 ^ 15 < p :=
    lt_of_lt_of_le (by norm_num : 10 ^ 15 < 1628413597910449) hp_ge
  have hpow_gt : 10 ^ 145495320 < p ^ (2 * u) := by
    obtain ⟨B, hB_eq, hB_lt⟩ : ∃ B : ℕ, B = 10 ^ 15 ∧ B < p := ⟨10 ^ 15, rfl, hp_gt15⟩
    calc 10 ^ 145495320 = B ^ 9699688 := by
          rw [hB_eq, show 145495320 = 15 * 9699688 by norm_num, pow_mul]
      _ < p ^ 9699688 := pow_lt_pow_left₀ hB_lt (Nat.zero_le B) (by decide : 9699688 ≠ 0)
      _ ≤ p ^ (2 * u) := pow_le_pow_right₀ hp.one_le (by omega)
  exact ⟨hu_ge, by omega, hp_ge, hpow_gt⟩

/-- Every even prime-power component index `i = p ^ j` of an odd perfect number
satisfies `9699688 ≤ j`, `10 ^ 145495320 < i`, and `10 ^ 145495320 < N`. -/
theorem even_prime_power_component_size_gt_ten_pow_145495320 {N q a b i p j : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b)
    (hl : sigma 1 b = q ^ a * i) (hr : sigma 1 (q ^ a) * i = 2 * b)
    (hp : p.Prime) (hj : 0 < j) (hje : Even j) (hi : i = p ^ j) :
    9699688 ≤ j ∧ 10 ^ 145495320 < i ∧ 10 ^ 145495320 < N := by
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
    even_index_exponent_ge_9699688 hp hpo hs hu hσq hplus hσs
  have hi_gt : 10 ^ 145495320 < i := by
    rw [hi_even]
    exact hpow_gt
  exact ⟨by omega, hi_gt, hi_gt.trans hi_lt_N⟩

end OddPerfect
