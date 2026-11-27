module

public import OddPerfect.GlobalWave11Obstruction
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Even-Index Primorial Obstruction (`OddPerfect.EvenIndexPrimorialObstruction`)

Uses `Mathlib.NumberTheory.Primorial` (`primorial_le_four_pow`) to bound the product
`P_L = ∏ r ∈ S₁, (2 * s.factorization r + 1)` by `2 * 16 ^ e₀` across all `u ≥ 1`,
jumping to symbolic `k = ∞` on even prime-power component indices `i_q = p ^ (2 * u)`:

1. `even_index_P_L_le_two_mul_sixteen_pow`:
   Proves `21 ≤ e₀`, `S₁.card ≤ e₀`, `P_L ≤ ∏ q ∈ (Finset.Icc 3 (2 * e₀ + 1)).filter Nat.Prime, q`,
   and `P_L ≤ 2 * 16 ^ e₀`, where `e₀ = s.factorization (S₁.min' hne)`.
2. `even_index_min_S1_mem_small_five` & `even_index_min_S1_le_thirteen`:
   Unconditionally forces `S₁.min' hne ∈ ({3, 5, 7, 11, 13} : Finset ℕ)` and `S₁.min' hne ≤ 13`.
3. `even_index_three_or_five_mem_S1_or_quadratic_repunit`:
   Unconditionally forces either `3 ∈ S₁ ∨ 5 ∈ S₁` or
   `∃ r_max ∈ S₁, s.factorization r_max = 1 ∧ p = r_max ^ 2 + r_max + 1 ∧ r_max % 3 = 2 ∧ p % 3 = 1`.
4. `even_prime_power_component_forces_small_repunit_base`:
   Lifts (2) and (3) to any odd perfect number `N = q ^ a * b` with `i = p ^ (2 * u)`.
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-! ### Private Arithmetic & Exponent-Ordering Helpers -/

private lemma sigma_prime_pow_lt_of_base_lt' {a b e : ℕ} (ha : a.Prime) (hb : b.Prime)
    (hab : a < b) (he : 0 < e) : sigma 1 (a ^ e) < sigma 1 (b ^ e) := by
  rw [sigma_one_apply_prime_pow ha, sigma_one_apply_prime_pow hb]
  exact Finset.sum_lt_sum (fun j _ => Nat.pow_le_pow_left hab.le j)
    ⟨1, Finset.mem_range.mpr (by omega), by simpa using hab⟩

private lemma sigma_prime_pow_le_of_exp_le' {r a b : ℕ} (hr : r.Prime) (hab : a ≤ b) :
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
    sigma_prime_pow_lt_of_base_lt' ha hb hab (by omega)
  have hle' : sigma 1 (b ^ (2 * s.factorization a)) ≤ sigma 1 (b ^ (2 * s.factorization b)) :=
    sigma_prime_pow_le_of_exp_le' hb (by omega)
  omega

private lemma sixteen_mul_256_pow_le_289_pow {e : ℕ} (he : 23 ≤ e) :
    16 * 256 ^ e ≤ 289 ^ e := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    calc 16 * 256 ^ (k + 1)
        = 256 * (16 * 256 ^ k) := by ring
      _ ≤ 256 * 289 ^ k := Nat.mul_le_mul_left 256 ih
      _ ≤ 289 * 289 ^ k := Nat.mul_le_mul_right _ (by decide)
      _ = 289 ^ (k + 1) := by rw [pow_succ']

private lemma pow4_step_17 {e : ℕ} (he : 1 ≤ e) :
    256 * e ^ 4 * 65536 ^ e ≤ (17 ^ 6) ^ e := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hstep : k + 1 ≤ 2 * k := by omega
    have hpow4 : (k + 1) ^ 4 ≤ 16 * k ^ 4 := by
      calc (k + 1) ^ 4 ≤ (2 * k) ^ 4 := Nat.pow_le_pow_left hstep 4
        _ = 16 * k ^ 4 := by ring
    calc 256 * (k + 1) ^ 4 * 65536 ^ (k + 1)
        ≤ 256 * (16 * k ^ 4) * (65536 * 65536 ^ k) := by gcongr; rw [pow_succ']
      _ = (16 * 65536) * (256 * k ^ 4 * 65536 ^ k) := by ring
      _ ≤ 17 ^ 6 * (17 ^ 6) ^ k := Nat.mul_le_mul (by norm_num) ih
      _ = (17 ^ 6) ^ (k + 1) := (pow_succ' (17 ^ 6) k).symm

private lemma pow4_step_7 {e : ℕ} (he : 34 ≤ e) :
    256 * e ^ 4 * 65536 ^ e ≤ (7 ^ 6) ^ e := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hstep : 34 * (k + 1) ≤ 35 * k := by omega
    have hpow4 : 34 ^ 4 * (k + 1) ^ 4 ≤ 35 ^ 4 * k ^ 4 := by
      rw [← mul_pow, ← mul_pow]
      exact Nat.pow_le_pow_left hstep 4
    have hscale : 34 ^ 4 * (256 * (k + 1) ^ 4 * 65536 ^ (k + 1)) ≤
        34 ^ 4 * (7 ^ 6) ^ (k + 1) := by
      calc 34 ^ 4 * (256 * (k + 1) ^ 4 * 65536 ^ (k + 1))
          = 256 * (34 ^ 4 * (k + 1) ^ 4) * 65536 * 65536 ^ k := by rw [pow_succ']; ring
        _ ≤ 256 * (35 ^ 4 * k ^ 4) * 65536 * 65536 ^ k := by gcongr
        _ = (65536 * 35 ^ 4) * (256 * k ^ 4 * 65536 ^ k) := by ring
        _ ≤ (7 ^ 6 * 34 ^ 4) * (7 ^ 6) ^ k := Nat.mul_le_mul (by norm_num) ih
        _ = 34 ^ 4 * (7 ^ 6) ^ (k + 1) := by rw [pow_succ']; ring
    exact Nat.le_of_mul_le_mul_left hscale (by norm_num)

/-! ### Primorial Upper Bound on `P_L` -/

/-- At any even prime-power component index `p ^ (2 * u)`, let `e₀` be the largest
cofactor exponent in `S₁` (attained at `S₁.min' hne`). Then `21 ≤ e₀`, `S₁.card ≤ e₀`,
`P_L` is bounded by the product of odd primes up to `2 * e₀ + 1`, and `P_L ≤ 2 * 16 ^ e₀`
via `primorial_le_four_pow`. -/
theorem even_index_P_L_le_two_mul_sixteen_pow {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    let S₁ := s.primeFactors.filter (v · = 1)
    let P_L := ∏ r ∈ S₁, (2 * s.factorization r + 1)
    S₁.Nonempty ∧
      ∀ hne : S₁.Nonempty,
        let e₀ := s.factorization (S₁.min' hne)
        21 ≤ e₀ ∧ S₁.card ≤ e₀ ∧
          P_L ≤ ∏ q ∈ (Finset.Icc 3 (2 * e₀ + 1)).filter Nat.Prime, q ∧
          P_L ≤ 2 * 16 ^ e₀ := by
  intro v S₁ P_L
  have hS1_ge13 : 13 ≤ S₁.card := even_index_thirteen_le_S1_card hp hpo hs hu hσq hplus hσs
  have hne₀ : S₁.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨hne₀, fun hne => ?_⟩
  let r₀ := S₁.min' hne
  let e₀ := s.factorization r₀
  obtain ⟨_, hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  have extract : ∀ r ∈ S₁, r.Prime ∧ Odd r ∧ 3 ≤ r ∧ 1 ≤ s.factorization r ∧
      (2 * s.factorization r + 1).Prime ∧ sigma 1 (r ^ (2 * s.factorization r)) = p := by
    intro r hrS
    obtain ⟨hr, hvr⟩ := Finset.mem_filter.mp hrS
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hrs := Nat.dvd_of_mem_primeFactors hr
    have hro : Odd r := hs.of_dvd_nat hrs
    have hr3 : 3 ≤ r := by have := hrp.two_le; have := Nat.odd_iff.mp hro; omega
    have hepos : 1 ≤ s.factorization r :=
      (hrp.dvd_iff_one_le_factorization hs.pos.ne').mp hrs
    have hlp := (even_index_cofactor_component_order_dvd_pred hp hpo hs hσq hplus hσs hr).1
    have hσr : sigma 1 (r ^ (2 * s.factorization r)) = p := by
      have H := (hparts r hr).2
      dsimp only at H
      change sigma 1 (r ^ (2 * s.factorization r)) = p ^ v r at H
      rwa [hvr, pow_one] at H
    exact ⟨hrp, hro, hr3, hepos, hlp, hσr⟩
  have hr₀_mem : r₀ ∈ S₁ := Finset.min'_mem S₁ hne
  obtain ⟨hr₀p, _, _, he₀pos, _, hσr₀⟩ := extract r₀ hr₀_mem
  have hinj_exp : Set.InjOn (fun r => s.factorization r) (S₁ : Set ℕ) := by
    intro a ha b hb hab
    obtain ⟨hap, _, _, heapos, _, hσa⟩ := extract a ha
    obtain ⟨hbp, _, _, hebpos, _, hσb⟩ := extract b hb
    rcases lt_trichotomy a b with hlt | rfl | hgt
    · exact absurd hab (ne_of_gt (exp_anti_of_sigma_eq' hap hbp hlt heapos hσa hσb))
    · rfl
    · exact absurd hab.symm (ne_of_gt (exp_anti_of_sigma_eq' hbp hap hgt hebpos hσb hσa))
  have hexp_le : ∀ r ∈ S₁, s.factorization r ≤ e₀ := by
    intro r hrS
    obtain ⟨hrp, _, _, _, _, hσr⟩ := extract r hrS
    rcases eq_or_lt_of_le (Finset.min'_le S₁ r hrS) with heq | hlt
    · change r₀ = r at heq
      rw [← heq]
    · exact (exp_anti_of_sigma_eq' hr₀p hrp hlt he₀pos hσr₀ hσr).le
  have himg_exp : S₁.image (fun r => s.factorization r) ⊆
      (Finset.Icc 1 e₀).filter (fun m => (2 * m + 1).Prime) := by
    intro m hm
    obtain ⟨r, hrS, rfl⟩ := Finset.mem_image.mp hm
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨(extract r hrS).2.2.2.1, hexp_le r hrS⟩, (extract r hrS).2.2.2.2.1⟩
  have he₀_ge21 : 21 ≤ e₀ := by
    by_contra! hlt
    have hle20 : e₀ ≤ 20 := by omega
    have hsub20 : (Finset.Icc 1 e₀).filter (fun m => (2 * m + 1).Prime) ⊆
        (Finset.Icc 1 20).filter (fun m => (2 * m + 1).Prime) := by
      intro m hm
      obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hm
      obtain ⟨h1m, hme⟩ := Finset.mem_Icc.mp hm1
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1m, hme.trans hle20⟩, hm2⟩
    have hcard_le : S₁.card ≤ ((Finset.Icc 1 20).filter (fun m => (2 * m + 1).Prime)).card := by
      calc S₁.card = (S₁.image (fun r => s.factorization r)).card :=
            (Finset.card_image_of_injOn hinj_exp).symm
        _ ≤ ((Finset.Icc 1 20).filter (fun m => (2 * m + 1).Prime)).card :=
            Finset.card_le_card (himg_exp.trans hsub20)
    have h12 : ((Finset.Icc 1 20).filter (fun m => (2 * m + 1).Prime)).card = 12 := by decide
    omega
  have hcard_le_e₀ : S₁.card ≤ e₀ := by
    calc S₁.card = (S₁.image (fun r => s.factorization r)).card :=
          (Finset.card_image_of_injOn hinj_exp).symm
      _ ≤ ((Finset.Icc 1 e₀).filter (fun m => (2 * m + 1).Prime)).card :=
          Finset.card_le_card himg_exp
      _ ≤ (Finset.Icc 1 e₀).card := Finset.card_filter_le _ _
      _ = e₀ := by simp
  let g (r : ℕ) := 2 * s.factorization r + 1
  let P_odd := (Finset.Icc 3 (2 * e₀ + 1)).filter Nat.Prime
  have hinj_g : Set.InjOn g (S₁ : Set ℕ) := by
    intro a ha b hb hab
    have heq : s.factorization a = s.factorization b := by dsimp [g] at hab; omega
    exact hinj_exp ha hb heq
  have himg_g : S₁.image g ⊆ P_odd := by
    intro q' hq'
    obtain ⟨r, hrS, rfl⟩ := Finset.mem_image.mp hq'
    obtain ⟨_, _, _, hepos, hlp, _⟩ := extract r hrS
    have hle := hexp_le r hrS
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by dsimp [g]; omega, by dsimp [g]; omega⟩, hlp⟩
  have hPL_le_Podd : P_L ≤ ∏ q' ∈ P_odd, q' := by
    have hprod_eq : P_L = ∏ q' ∈ S₁.image g, q' := by
      change (∏ r ∈ S₁, g r) = ∏ q' ∈ S₁.image g, q'
      exact (Finset.prod_image (f := fun x => x) hinj_g).symm
    rw [hprod_eq]
    exact Finset.prod_le_prod_of_subset_of_one_le himg_g fun q' hq' _ =>
      (Finset.mem_filter.mp hq').2.one_le
  have h2_not_mem : 2 ∉ P_odd := by
    intro hmem
    have h3 : 3 ≤ 2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hmem).1).1
    omega
  have hsub_primesLE : insert 2 P_odd ⊆ Nat.primesLE (2 * e₀ + 1) := by
    intro q' hq'
    rcases Finset.mem_insert.mp hq' with rfl | hmem
    · exact Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_two⟩
    · obtain ⟨hIcc, hqp⟩ := Finset.mem_filter.mp hmem
      exact Nat.mem_primesLE.mpr ⟨(Finset.mem_Icc.mp hIcc).2, hqp⟩
  have h2_mul_P_odd : 2 * ∏ q' ∈ P_odd, q' ≤ 4 * 16 ^ e₀ := by
    calc 2 * ∏ q' ∈ P_odd, q'
        = ∏ q' ∈ insert 2 P_odd, q' := (Finset.prod_insert (f := fun x => x) h2_not_mem).symm
      _ ≤ ∏ q' ∈ Nat.primesLE (2 * e₀ + 1), q' :=
          Finset.prod_le_prod_of_subset_of_one_le hsub_primesLE fun q' hq' _ =>
            (Nat.prime_of_mem_primesLE hq').one_le
      _ = primorial (2 * e₀ + 1) := (primorial_eq_prod_primesLE (2 * e₀ + 1)).symm
      _ ≤ 4 ^ (2 * e₀ + 1) := primorial_le_four_pow (2 * e₀ + 1)
      _ = 4 * 16 ^ e₀ := by
          rw [pow_succ, pow_mul]
          norm_num
          ring
  have hPL_le_prim : P_L ≤ 2 * 16 ^ e₀ := by
    have h2 : 2 * P_L ≤ 2 * (2 * 16 ^ e₀) := by
      calc 2 * P_L ≤ 2 * ∏ q' ∈ P_odd, q' := Nat.mul_le_mul_left 2 hPL_le_Podd
        _ ≤ 4 * 16 ^ e₀ := h2_mul_P_odd
        _ = 2 * (2 * 16 ^ e₀) := by ring
    omega
  exact ⟨he₀_ge21, hcard_le_e₀, hPL_le_Podd, hPL_le_prim⟩

/-! ### Unconditional Small-Base Obstructions across All `u ≥ 1` -/

/-- Unconditionally across all `u ≥ 1`, the smallest prime `r₀ = S₁.min' hne`
belongs to `{3, 5, 7, 11, 13}`. -/
theorem even_index_min_S1_mem_small_five {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    let S₁ := s.primeFactors.filter (v · = 1)
    ∃ hne : S₁.Nonempty, S₁.min' hne ∈ ({3, 5, 7, 11, 13} : Finset ℕ) := by
  intro v S₁
  obtain ⟨hne, hbounds⟩ := even_index_P_L_le_two_mul_sixteen_pow hp hpo hs hu hσq hplus hσs
  refine ⟨hne, ?_⟩
  let r₀ := S₁.min' hne
  let e₀ := s.factorization r₀
  let P_L := ∏ r ∈ S₁, (2 * s.factorization r + 1)
  obtain ⟨he₀_ge21, hcard_le_e₀, hPL_le_Podd, hPL_le_prim⟩ := hbounds hne
  by_contra hnot
  have hr₀_mem : r₀ ∈ S₁ := Finset.min'_mem S₁ hne
  obtain ⟨hr₀_pf, hr₀_v⟩ := Finset.mem_filter.mp hr₀_mem
  have hr₀p : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_pf
  have hr₀o : Odd r₀ := hs.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr₀_pf)
  have hr₀_ge17 : 17 ≤ r₀ := by
    have hcheck : ∀ x ≤ 16, x.Prime → x % 2 = 1 →
        x ∈ ({3, 5, 7, 11, 13} : Finset ℕ) := by decide
    have hodd : r₀ % 2 = 1 := Nat.odd_iff.mp hr₀o
    by_contra! hlt17
    exact hnot (hcheck r₀ (by omega) hr₀p hodd)
  obtain ⟨_, hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  have hσr₀ : sigma 1 (r₀ ^ (2 * e₀)) = p := by
    have H := (hparts r₀ hr₀_pf).2
    dsimp only at H
    change sigma 1 (r₀ ^ (2 * e₀)) = p ^ v r₀ at H
    rwa [hr₀_v, pow_one] at H
  have he₀_pos : 1 ≤ e₀ := Nat.le_trans (by decide : 1 ≤ 21) he₀_ge21
  have hr₀_pow_lt_p : r₀ ^ (2 * e₀) < p := by
    rw [← hσr₀]
    exact self_lt_sigma_of_one_lt (one_lt_pow₀ hr₀p.one_lt (by omega))
  have h17_lt_p : (17 ^ 2) ^ e₀ < p := by
    calc (17 ^ 2) ^ e₀ = 17 ^ (2 * e₀) := by rw [← pow_mul]
      _ ≤ r₀ ^ (2 * e₀) := Nat.pow_le_pow_left hr₀_ge17 (2 * e₀)
      _ < p := hr₀_pow_lt_p
  have hdich := even_index_sharpened_symbolic_dichotomy hp hpo hs hu hσq hplus hσs
  change p < 4 * P_L ^ 2 ∨ p ^ 3 < (2 * S₁.card * P_L) ^ 4 at hdich
  rcases hdich with hlt_sq | hlt_cube
  · by_cases he₀_ge23 : 23 ≤ e₀
    · have h4PL : 4 * P_L ^ 2 ≤ (17 ^ 2) ^ e₀ := by
        calc 4 * P_L ^ 2 ≤ 4 * (2 * 16 ^ e₀) ^ 2 :=
              Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hPL_le_prim 2)
          _ = 16 * 256 ^ e₀ := by
              rw [mul_pow, ← pow_mul, mul_comm e₀ 2, pow_mul]
              norm_num
              ring
          _ ≤ 289 ^ e₀ := sixteen_mul_256_pow_le_289_pow he₀_ge23
          _ = (17 ^ 2) ^ e₀ := by norm_num
      exact Nat.lt_irrefl _ (h17_lt_p.trans (hlt_sq.trans_le h4PL))
    · have he₀_mem : e₀ ∈ Finset.Icc 21 22 := Finset.mem_Icc.mpr ⟨he₀_ge21, by omega⟩
      have hcheck : ∀ x ∈ Finset.Icc 21 22,
          4 * (∏ q' ∈ (Finset.Icc 3 (2 * x + 1)).filter Nat.Prime, q') ^ 2 ≤ (17 ^ 2) ^ x := by
        decide
      have h4PL : 4 * P_L ^ 2 ≤ (17 ^ 2) ^ e₀ := by
        calc 4 * P_L ^ 2
            ≤ 4 * (∏ q' ∈ (Finset.Icc 3 (2 * e₀ + 1)).filter Nat.Prime, q') ^ 2 :=
              Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hPL_le_Podd 2)
          _ ≤ (17 ^ 2) ^ e₀ := hcheck e₀ he₀_mem
      exact Nat.lt_irrefl _ (h17_lt_p.trans (hlt_sq.trans_le h4PL))
  · have hcube_upper : (2 * S₁.card * P_L) ^ 4 ≤ (17 ^ 6) ^ e₀ := by
      calc (2 * S₁.card * P_L) ^ 4
          ≤ (2 * e₀ * (2 * 16 ^ e₀)) ^ 4 :=
            Nat.pow_le_pow_left (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hcard_le_e₀) hPL_le_prim) 4
        _ = 256 * e₀ ^ 4 * 65536 ^ e₀ := by
            rw [mul_pow, mul_pow, mul_pow, ← pow_mul, mul_comm e₀ 4, pow_mul]
            norm_num
            ring
        _ ≤ (17 ^ 6) ^ e₀ := pow4_step_17 he₀_pos
    have h17_cube_lt : (17 ^ 6) ^ e₀ < p ^ 3 := by
      have h1 : (17 ^ 6) ^ e₀ = ((17 ^ 2) ^ e₀) ^ 3 := by
        rw [← pow_mul, show 6 * e₀ = 2 * e₀ * 3 by ring, pow_mul, pow_mul]
      rw [h1]
      exact Nat.pow_lt_pow_left h17_lt_p (by decide)
    exact Nat.lt_irrefl _ (h17_cube_lt.trans (hlt_cube.trans_le hcube_upper))

/-- Corollary: `S₁.min' hne ≤ 13` unconditionally across all `u ≥ 1`. -/
theorem even_index_min_S1_le_thirteen {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    let S₁ := s.primeFactors.filter (v · = 1)
    ∃ hne : S₁.Nonempty, S₁.min' hne ≤ 13 := by
  obtain ⟨hne, hmem⟩ := even_index_min_S1_mem_small_five hp hpo hs hu hσq hplus hσs
  refine ⟨hne, ?_⟩
  have hle : ∀ x ∈ ({3, 5, 7, 11, 13} : Finset ℕ), x ≤ 13 := by decide
  exact hle _ hmem

/-- Unconditionally across all `u ≥ 1`, either `3 ∈ S₁ ∨ 5 ∈ S₁`, or `r_max = S₁.max' hne`
has exponent `1`, giving `p = r_max ^ 2 + r_max + 1` with `r_max % 3 = 2` and `p % 3 = 1`. -/
theorem even_index_three_or_five_mem_S1_or_quadratic_repunit {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    let S₁ := s.primeFactors.filter (v · = 1)
    (3 ∈ S₁ ∨ 5 ∈ S₁) ∨
      ∃ r_max ∈ S₁, s.factorization r_max = 1 ∧
        p = r_max ^ 2 + r_max + 1 ∧ r_max % 3 = 2 ∧ p % 3 = 1 := by
  intro v S₁
  by_cases h35 : 3 ∈ S₁ ∨ 5 ∈ S₁
  · exact Or.inl h35
  right
  obtain ⟨hne, hbounds⟩ := even_index_P_L_le_two_mul_sixteen_pow hp hpo hs hu hσq hplus hσs
  let r₀ := S₁.min' hne
  let e₀ := s.factorization r₀
  let P_L := ∏ r ∈ S₁, (2 * s.factorization r + 1)
  obtain ⟨he₀_ge21, hcard_le_e₀, hPL_le_Podd, hPL_le_prim⟩ := hbounds hne
  have hr₀_mem : r₀ ∈ S₁ := Finset.min'_mem S₁ hne
  obtain ⟨hr₀_pf, hr₀_v⟩ := Finset.mem_filter.mp hr₀_mem
  have hr₀p : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_pf
  have hr₀o : Odd r₀ := hs.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr₀_pf)
  have hr₀_ge7 : 7 ≤ r₀ := by
    have hr₀_ne3 : r₀ ≠ 3 := fun h => h35 (Or.inl (h ▸ hr₀_mem))
    have hr₀_ne5 : r₀ ≠ 5 := fun h => h35 (Or.inr (h ▸ hr₀_mem))
    have := hr₀p.two_le
    have := Nat.odd_iff.mp hr₀o
    omega
  obtain ⟨_, hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  have extract : ∀ r ∈ S₁, r.Prime ∧ 1 ≤ s.factorization r ∧
      sigma 1 (r ^ (2 * s.factorization r)) = p := by
    intro r hrS
    obtain ⟨hr, hvr⟩ := Finset.mem_filter.mp hrS
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hepos : 1 ≤ s.factorization r :=
      (hrp.dvd_iff_one_le_factorization hs.pos.ne').mp (Nat.dvd_of_mem_primeFactors hr)
    have hσr : sigma 1 (r ^ (2 * s.factorization r)) = p := by
      have H := (hparts r hr).2
      dsimp only at H
      change sigma 1 (r ^ (2 * s.factorization r)) = p ^ v r at H
      rwa [hvr, pow_one] at H
    exact ⟨hrp, hepos, hσr⟩
  let r_max := S₁.max' hne
  have hr_max_mem : r_max ∈ S₁ := Finset.max'_mem S₁ hne
  obtain ⟨hr_max_p, he_max_pos, hσ_max⟩ := extract r_max hr_max_mem
  by_cases hmax1 : s.factorization r_max = 1
  · have hp_eq : p = r_max ^ 2 + r_max + 1 := by
      rw [← hσ_max, hmax1, show 2 * 1 = 2 by decide, sigma_one_apply_prime_pow hr_max_p]
      simp [Finset.sum_range_succ]
      ring
    have hr_max_ge7 : 7 ≤ r_max := hr₀_ge7.trans (Finset.min'_le S₁ r_max hr_max_mem)
    have hp_gt49 : 49 < p := by nlinarith
    have hr_max_mod3_ne0 : r_max % 3 ≠ 0 := by
      intro h0
      have hdvd : 3 ∣ r_max := Nat.dvd_of_mod_eq_zero h0
      have := hr_max_p.eq_one_or_self_of_dvd 3 hdvd
      omega
    have hr_max_mod3_ne1 : r_max % 3 ≠ 1 := by
      intro h1
      have hp_mod0 : p % 3 = 0 := by
        rw [hp_eq, Nat.add_mod, Nat.add_mod (r_max ^ 2), sq, Nat.mul_mod, h1]
      have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero hp_mod0
      have := hp.eq_one_or_self_of_dvd 3 hdvd
      omega
    have hr_max_mod3 : r_max % 3 = 2 := by omega
    have hp_mod3 : p % 3 = 1 := by
      rw [hp_eq, Nat.add_mod, Nat.add_mod (r_max ^ 2), sq, Nat.mul_mod, hr_max_mod3]
    exact ⟨r_max, hr_max_mem, hmax1, hp_eq, hr_max_mod3, hp_mod3⟩
  · exfalso
    have h2_max : 2 ≤ s.factorization r_max := by omega
    have h2_all : ∀ r ∈ S₁, 2 ≤ s.factorization r := by
      intro r hrS
      obtain ⟨hrp, hepos, hσr⟩ := extract r hrS
      rcases eq_or_lt_of_le (Finset.le_max' S₁ r hrS) with heq | hlt
      · rw [heq]
        exact h2_max
      · have := exp_anti_of_sigma_eq' hrp hr_max_p hlt hepos hσr hσ_max
        omega
    obtain ⟨_, hmoment⟩ := even_index_large_min_exponent_bound hp hpo hs hu hσq hplus hσs
    have hp3_lt : p ^ 3 < (2 * S₁.card * P_L) ^ 4 := by
      simpa using hmoment 2 (by decide) h2_all
    have hr₀_pow_lt_p : r₀ ^ (2 * e₀) < p := by
      have he₀_pos : 1 ≤ e₀ := (extract r₀ hr₀_mem).2.1
      have hσr₀ : sigma 1 (r₀ ^ (2 * e₀)) = p := (extract r₀ hr₀_mem).2.2
      rw [← hσr₀]
      exact self_lt_sigma_of_one_lt (one_lt_pow₀ hr₀p.one_lt (by omega))
    have h7_lt_p : (7 ^ 2) ^ e₀ < p := by
      calc (7 ^ 2) ^ e₀ = 7 ^ (2 * e₀) := by rw [← pow_mul]
        _ ≤ r₀ ^ (2 * e₀) := Nat.pow_le_pow_left hr₀_ge7 (2 * e₀)
        _ < p := hr₀_pow_lt_p
    have h7_cube_lt : (7 ^ 6) ^ e₀ < p ^ 3 := by
      have h1 : (7 ^ 6) ^ e₀ = ((7 ^ 2) ^ e₀) ^ 3 := by
        rw [← pow_mul, show 6 * e₀ = 2 * e₀ * 3 by ring, pow_mul, pow_mul]
      rw [h1]
      exact Nat.pow_lt_pow_left h7_lt_p (by decide)
    by_cases he₀_ge34 : 34 ≤ e₀
    · have hcube_upper : (2 * S₁.card * P_L) ^ 4 ≤ (7 ^ 6) ^ e₀ := by
        calc (2 * S₁.card * P_L) ^ 4
            ≤ (2 * e₀ * (2 * 16 ^ e₀)) ^ 4 :=
              Nat.pow_le_pow_left (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hcard_le_e₀) hPL_le_prim) 4
          _ = 256 * e₀ ^ 4 * 65536 ^ e₀ := by
              rw [mul_pow, mul_pow, mul_pow, ← pow_mul, mul_comm e₀ 4, pow_mul]
              norm_num
              ring
          _ ≤ (7 ^ 6) ^ e₀ := pow4_step_7 he₀_ge34
      exact Nat.lt_irrefl _ (h7_cube_lt.trans (hp3_lt.trans_le hcube_upper))
    · have he₀_mem : e₀ ∈ Finset.Icc 21 33 := Finset.mem_Icc.mpr ⟨he₀_ge21, by omega⟩
      have hcheck : ∀ x ∈ Finset.Icc 21 33,
          (2 * x * ∏ q' ∈ (Finset.Icc 3 (2 * x + 1)).filter Nat.Prime, q') ^ 4 ≤ 7 ^ (6 * x) := by
        decide
      have hcube_upper : (2 * S₁.card * P_L) ^ 4 ≤ (7 ^ 6) ^ e₀ := by
        calc (2 * S₁.card * P_L) ^ 4
            ≤ (2 * e₀ * ∏ q' ∈ (Finset.Icc 3 (2 * e₀ + 1)).filter Nat.Prime, q') ^ 4 :=
              Nat.pow_le_pow_left (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hcard_le_e₀) hPL_le_Podd) 4
          _ ≤ 7 ^ (6 * e₀) := hcheck e₀ he₀_mem
          _ = (7 ^ 6) ^ e₀ := by rw [pow_mul]
      exact Nat.lt_irrefl _ (h7_cube_lt.trans (hp3_lt.trans_le hcube_upper))

/-! ### Global Odd Perfect Number Lift -/

/-- At any even prime-power component index `i = p ^ (2 * u)` of an odd perfect number
`N = q ^ a * b`, `N` must contain the square of a prime `r ∈ {3, 5, 7, 11, 13}` generating `p`
as a prime-length repunit, and must contain the square of `3` or `5` generating `p` unless
`p = r_max ^ 2 + r_max + 1` with `r_max ∈ N.primeFactors`, `r_max % 3 = 2`, and `p % 3 = 1`. -/
theorem even_prime_power_component_forces_small_repunit_base
    {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    (∃ r ∈ ({3, 5, 7, 11, 13} : Finset ℕ),
      r ^ 2 ∣ N ∧ ∃ l : ℕ, l.Prime ∧ 2 < l ∧ geometricBlock r l = p) ∧
    ((∃ r ∈ ({3, 5} : Finset ℕ),
      r ^ 2 ∣ N ∧ ∃ l : ℕ, l.Prime ∧ 2 < l ∧ geometricBlock r l = p) ∨
      (∃ r_max ∈ N.primeFactors,
        r_max % 3 = 2 ∧ p = r_max ^ 2 + r_max + 1 ∧ p % 3 = 1)) := by
  obtain ⟨ha1, hσq⟩ :=
    even_prime_power_index_eq_selected_sigma hN ho hq ha hform hqb hl hr hp hu hi
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b _)
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h4 : 4 ∣ 2 * b := hr ▸ hi ▸ (pow_dvd_pow 2 (by omega : 2 ≤ 2 * u)).trans (dvd_mul_left _ _)
    have := hbo.not_two_dvd_nat
    omega
  have hpo := hp.odd_of_ne_two hp2
  obtain ⟨m, _, _, _, rfl⟩ :=
    euler_form_of_odd_component_index hN ho hq ha hform hqb hl hr (hi ▸ hpo.pow)
  have hmo := ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _)
  rw [ha1, pow_one] at hform hl hr
  rw [hi] at hl hr
  obtain ⟨s, hso, _, hms, _, hplus, hσs⟩ := even_prime_power_cofactor_split hq hp hmo hpo hu hl hr
  let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
  let S₁ := s.primeFactors.filter (v · = 1)
  obtain ⟨_, hparts⟩ := even_index_source_valuation_budget hp hso hσq hplus hσs
  have hlift : ∀ r ∈ S₁, r ∈ N.primeFactors ∧ r ^ 2 ∣ N ∧
      ∃ l : ℕ, l.Prime ∧ 2 < l ∧ geometricBlock r l = p := by
    intro r hrS
    obtain ⟨hr_pf, hr_v⟩ := Finset.mem_filter.mp hrS
    have hrp := Nat.prime_of_mem_primeFactors hr_pf
    have hrs : r ∣ s := Nat.dvd_of_mem_primeFactors hr_pf
    have hrm : r ∣ m := hrs.trans (hms ▸ dvd_mul_left s _)
    have hr2_m2 : r ^ 2 ∣ m ^ 2 := pow_dvd_pow_of_dvd hrm 2
    have hr2_N : r ^ 2 ∣ N := hr2_m2.trans (hform ▸ dvd_mul_left (m ^ 2) q)
    have hr_N : r ∣ N := (dvd_pow_self r (by decide : 2 ≠ 0)).trans hr2_N
    have hr_Npf : r ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hrp, hr_N, hN.2.ne'⟩
    have hepos : 1 ≤ s.factorization r := (hrp.dvd_iff_one_le_factorization hso.pos.ne').mp hrs
    have hlp := (even_index_cofactor_component_order_dvd_pred hp hpo hso hσq hplus hσs hr_pf).1
    have hgb : geometricBlock r (2 * s.factorization r + 1) = p := by
      dsimp only [geometricBlock]
      rw [← sigma_one_apply_prime_pow hrp]
      have H := (hparts r hr_pf).2
      dsimp only at H
      change sigma 1 (r ^ (2 * s.factorization r)) = p ^ v r at H
      rwa [hr_v, pow_one] at H
    exact ⟨hr_Npf, hr2_N, 2 * s.factorization r + 1, hlp, by omega, hgb⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨hne, hmem5⟩ := even_index_min_S1_mem_small_five hp hpo hso hu hσq hplus hσs
    obtain ⟨_, hr2_N, hl_ex⟩ := hlift _ (Finset.min'_mem S₁ hne)
    exact ⟨S₁.min' hne, hmem5, hr2_N, hl_ex⟩
  · rcases even_index_three_or_five_mem_S1_or_quadratic_repunit hp hpo hso hu hσq hplus hσs with
      (h3 | h5) | ⟨r_max, hr_max_S, _, hp_eq, hrmod, hpmod⟩
    · obtain ⟨_, hr2_N, hl_ex⟩ := hlift 3 h3
      exact Or.inl ⟨3, by decide, hr2_N, hl_ex⟩
    · obtain ⟨_, hr2_N, hl_ex⟩ := hlift 5 h5
      exact Or.inl ⟨5, by decide, hr2_N, hl_ex⟩
    · obtain ⟨hr_max_Npf, _, _⟩ := hlift r_max hr_max_S
      exact Or.inr ⟨r_max, hr_max_Npf, hrmod, hp_eq, hpmod⟩

end OddPerfect
