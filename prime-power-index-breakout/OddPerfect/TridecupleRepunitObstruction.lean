module

public import OddPerfect.UndecupleRepunitObstruction
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tridecuple Repunit Obstruction (`OddPerfect.TridecupleRepunitObstruction`)

Upgrades the even prime-power component index obstruction from eleven simultaneous
odd-prime-base repunit representations of `p` (`UndecupleRepunitObstruction`) to
thirteen (`HasThirteenOddPrimeRepunits p`), eliminating `S₁.card = 11` and `S₁.card = 12`
via a unified `Fin k`-indexed sorted-profile refutation (including divisor-counting
refutations of the prime repunits `(3 ^ 71 - 1) / 2` and `(5 ^ 47 - 1) / 4`):

1. `HasTwelveOddPrimeRepunits`, `HasThirteenOddPrimeRepunits`:
   Clean `Finset`-based repunit multiplicity predicates (`HasKOddPrimeRepunits 12` / `13`).
2. `even_index_thirteen_le_S1_card`:
   Proves `13 ≤ S₁.card` at any even prime-power component index `p ^ (2 * u)`.
3. `even_prime_power_component_forces_thirteen_repunits_and_sixteen_primes`:
   Forces `HasThirteenOddPrimeRepunits p ∧ 16 ≤ N.primeFactors.card`.
4. `even_index_exponent_ge_13082761331670028` and
   `even_prime_power_component_size_gt_ten_pow_353234555955090756`:
   Forces `13082761331670028 ≤ j`, `10 ^ 27 < p`, and `10 ^ 353234555955090756 < i < N`.
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- The integer `z` has prime-length repunit representations in twelve distinct odd prime bases. -/
@[expose] def HasTwelveOddPrimeRepunits (z : ℕ) : Prop :=
  HasKOddPrimeRepunits 12 z

/-- The integer `z` has prime-length repunit representations in thirteen distinct odd prime bases. -/
@[expose] def HasThirteenOddPrimeRepunits (z : ℕ) : Prop :=
  HasKOddPrimeRepunits 13 z

/-! ### Generic Arithmetic & Sorted-Product Helpers -/

private lemma sigma_prime_pow_lt_of_base_lt {a b e : ℕ} (ha : a.Prime) (hb : b.Prime)
    (hab : a < b) (he : 0 < e) : sigma 1 (a ^ e) < sigma 1 (b ^ e) := by
  rw [sigma_one_apply_prime_pow ha, sigma_one_apply_prime_pow hb]
  exact Finset.sum_lt_sum (fun j _ => Nat.pow_le_pow_left hab.le j)
    ⟨1, Finset.mem_range.mpr (by omega), by simpa using hab⟩

private lemma sigma_prime_pow_le_of_exp_le {r a b : ℕ} (hr : r.Prime) (hab : a ≤ b) :
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
    sigma_prime_pow_lt_of_base_lt ha hb hab (by omega)
  have hle' : sigma 1 (b ^ (2 * s.factorization a)) ≤ sigma 1 (b ^ (2 * s.factorization b)) :=
    sigma_prime_pow_le_of_exp_le hb (by omega)
  omega

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

private lemma refute_sigma_three {p e d : ℕ} (hp : p.Prime)
    (hσ : sigma 1 (3 ^ (2 * e)) = p)
    (hd1 : 1 < d) (hd_lt : d < (3 ^ (2 * e + 1) - 1) / 2)
    (hdvd : d ∣ (3 ^ (2 * e + 1) - 1) / 2) : False := by
  have h1 := sigma_three_pow_mul_two_add_one (2 * e)
  rw [hσ] at h1
  have hp_eq : p = (3 ^ (2 * e + 1) - 1) / 2 := by omega
  rw [← hp_eq] at hd_lt hdvd
  have := hp.eq_one_or_self_of_dvd d hdvd
  omega

private lemma refute_sigma_five {p e d : ℕ} (hp : p.Prime)
    (hσ : sigma 1 (5 ^ (2 * e)) = p)
    (hd1 : 1 < d) (hd_lt : d < (5 ^ (2 * e + 1) - 1) / 4)
    (hdvd : d ∣ (5 ^ (2 * e + 1) - 1) / 4) : False := by
  have h1 := sigma_five_pow_mul_four_add_one (2 * e)
  rw [hσ] at h1
  have hp_eq : p = (5 ^ (2 * e + 1) - 1) / 4 := by omega
  rw [← hp_eq] at hd_lt hdvd
  have := hp.eq_one_or_self_of_dvd d hdvd
  omega

private lemma not_sigma_three_pow_prime_of_mem {p e : ℕ} (hp : p.Prime)
    (hσ : sigma 1 (3 ^ (2 * e)) = p)
    (he : e ∈ ({18, 20, 21, 23, 26, 29, 30, 33, 36, 39, 41} : Finset ℕ)) : False := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact refute_sigma_three hp hσ (d := 13097927) (by norm_num) (by norm_num) (by norm_num)
  · exact refute_sigma_three hp hσ (d := 83) (by norm_num) (by norm_num) (by norm_num)
  · exact refute_sigma_three hp hσ (d := 431) (by norm_num) (by norm_num) (by norm_num)
  · exact refute_sigma_three hp hσ (d := 1223) (by norm_num) (by norm_num) (by norm_num)
  · exact refute_sigma_three hp hσ (d := 107) (by norm_num) (by norm_num) (by norm_num)
  · exact refute_sigma_three hp hσ (d := 14425532687) (by norm_num) (by norm_num) (by norm_num)
  · exact refute_sigma_three hp hσ (d := 603901) (by norm_num) (by norm_num) (by norm_num)
  · exact refute_sigma_three hp hσ (d := 221101) (by norm_num) (by norm_num) (by norm_num)
  · exact refute_sigma_three hp hσ (d := 11243) (by norm_num) (by norm_num) (by norm_num)
  · exact refute_sigma_three hp hσ (d := 432853009) (by norm_num) (by norm_num) (by norm_num)
  · exact refute_sigma_three hp hσ (d := 167) (by norm_num) (by norm_num) (by norm_num)

private lemma not_sigma_five_pow_prime_of_mem {p e : ℕ} (hp : p.Prime)
    (hσ : sigma 1 (5 ^ (2 * e)) = p)
    (he : e ∈ ({18, 20, 21} : Finset ℕ)) : False := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact refute_sigma_five hp hσ (d := 149) (by norm_num) (by norm_num) (by norm_num)
  · exact refute_sigma_five hp hσ (d := 2238236249) (by norm_num) (by norm_num) (by norm_num)
  · exact refute_sigma_five hp hσ (d := 1644512641) (by norm_num) (by norm_num) (by norm_num)

private lemma refute_three_pow_70_repunit {p k : ℕ} (hk : 11 ≤ k)
    {l : Fin k → ℕ} (hl_prime : ∀ i, (l i).Prime) (hl_anti : StrictAnti l)
    (hl_ge : ∀ i, 3 ≤ l i) (hl_le : ∀ i, l i ≤ 71)
    (hl_dvd : ∀ i, l i ∣ (p - 1) / 2)
    (hσ : sigma 1 (3 ^ 70) = p) : False := by
  have h1 := sigma_three_pow_mul_two_add_one 70
  rw [hσ] at h1
  have hp_eq : p = (3 ^ 71 - 1) / 2 := by omega
  let D := (Finset.Icc 3 71).filter (fun q => q.Prime ∧ q ∣ ((3 ^ 71 - 1) / 2 - 1) / 2)
  have himg : (Finset.univ : Finset (Fin k)).image l ⊆ D := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hl_ge i, hl_le i⟩, hl_prime i, ?_⟩
    rw [← hp_eq]
    exact hl_dvd i
  have hcard_le : k ≤ D.card := by
    have hle := Finset.card_le_card himg
    rwa [Finset.card_image_of_injective _ hl_anti.injective, Finset.card_univ,
      Fintype.card_fin] at hle
  have hD4 : D.card = 4 := by decide
  omega

private lemma refute_five_pow_46_repunit {p k : ℕ} (hk : 11 ≤ k)
    {l : Fin k → ℕ} (hl_prime : ∀ i, (l i).Prime) (hl_anti : StrictAnti l)
    (hl_ge : ∀ i, 3 ≤ l i) (hl_le : ∀ i, l i ≤ 47)
    (hl_dvd : ∀ i, l i ∣ (p - 1) / 2)
    (hσ : sigma 1 (5 ^ 46) = p) : False := by
  have h1 := sigma_five_pow_mul_four_add_one 46
  rw [hσ] at h1
  have hp_eq : p = (5 ^ 47 - 1) / 4 := by omega
  let D := (Finset.Icc 3 47).filter (fun q => q.Prime ∧ q ∣ ((5 ^ 47 - 1) / 4 - 1) / 2)
  have himg : (Finset.univ : Finset (Fin k)).image l ⊆ D := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hl_ge i, hl_le i⟩, hl_prime i, ?_⟩
    rw [← hp_eq]
    exact hl_dvd i
  have hcard_le : k ≤ D.card := by
    have hle := Finset.card_le_card himg
    rwa [Finset.card_image_of_injective _ hl_anti.injective, Finset.card_univ,
      Fintype.card_fin] at hle
  have hD3 : D.card = 3 := by decide
  omega

private lemma exp_domination_of_step {C d c e₀ e : ℕ}
    (he₀ : 11 ≤ e₀) (hle : e₀ ≤ e)
    (hbase : C * (2 * e₀ + 1) ^ d ≤ 3 ^ (c * e₀))
    (hpow : 12 ^ d ≤ 3 ^ c * 11 ^ d) :
    C * (2 * e + 1) ^ d ≤ 3 ^ (c * e) := by
  induction e, hle using Nat.le_induction with
  | base => exact hbase
  | succ k hk ih =>
    have hstep : 11 * (2 * (k + 1) + 1) ≤ 12 * (2 * k + 1) := by omega
    have h1 : 11 ^ d * (2 * (k + 1) + 1) ^ d ≤ 12 ^ d * (2 * k + 1) ^ d := by
      rw [← mul_pow, ← mul_pow]
      exact Nat.pow_le_pow_left hstep d
    have h2 : 11 ^ d * (C * (2 * (k + 1) + 1) ^ d) ≤
        11 ^ d * (3 ^ c * (C * (2 * k + 1) ^ d)) := by
      calc 11 ^ d * (C * (2 * (k + 1) + 1) ^ d)
          = C * (11 ^ d * (2 * (k + 1) + 1) ^ d) := by ring
        _ ≤ C * (12 ^ d * (2 * k + 1) ^ d) := Nat.mul_le_mul_left C h1
        _ ≤ C * ((3 ^ c * 11 ^ d) * (2 * k + 1) ^ d) := by gcongr
        _ = 11 ^ d * (3 ^ c * (C * (2 * k + 1) ^ d)) := by ring
    have h3 : C * (2 * (k + 1) + 1) ^ d ≤ 3 ^ c * (C * (2 * k + 1) ^ d) :=
      Nat.le_of_mul_le_mul_left h2 (pow_pos (by decide) d)
    calc C * (2 * (k + 1) + 1) ^ d
        ≤ 3 ^ c * (C * (2 * k + 1) ^ d) := h3
      _ ≤ 3 ^ c * 3 ^ (c * k) := Nat.mul_le_mul_left _ ih
      _ = 3 ^ (c * (k + 1)) := by rw [← pow_add, mul_add, mul_one, add_comm]

private lemma prod_take_le_cons_take {a m : ℕ} {L : List ℕ}
    (hL : L.SortedGT) (ha : ∀ x ∈ L, x ≤ a) (hm : m ≤ L.length) :
    (L.take m).prod ≤ ((a :: L).take m).prod := by
  induction m generalizing a L with
  | zero => simp
  | succ m' ih =>
    cases L with
    | nil => simp at hm
    | cons b L' =>
      have hpair := hL.pairwise
      rw [List.pairwise_cons] at hpair
      have hL' : L'.SortedGT := hpair.2.sortedGT
      have hb : ∀ x ∈ L', x ≤ b := fun x hx => le_of_lt (hpair.1 x hx)
      have hba : b ≤ a := ha b (by simp)
      have hm' : m' ≤ L'.length := by simp at hm; omega
      have hsub := ih hL' hb hm'
      simp only [List.take_succ_cons, List.prod_cons]
      exact Nat.mul_le_mul hba hsub

private lemma prod_le_sortedGT_take {L : List ℕ} (hL : L.SortedGT)
    {T : Finset ℕ} (hsub : T ⊆ L.toFinset) :
    T.card ≤ L.length ∧ ∏ x ∈ T, x ≤ (L.take T.card).prod := by
  induction L generalizing T with
  | nil =>
    have hT : T = ∅ := Finset.subset_empty.mp (by simpa using hsub)
    subst hT
    simp
  | cons a L' ih =>
    have hpair := hL.pairwise
    rw [List.pairwise_cons] at hpair
    have hL' : L'.SortedGT := hpair.2.sortedGT
    have hlt_a : ∀ x ∈ L', x < a := hpair.1
    by_cases haT : a ∈ T
    · have hsub' : T.erase a ⊆ L'.toFinset := by
        intro x hx
        have hne : x ≠ a := Finset.ne_of_mem_erase hx
        have hxL := hsub (Finset.mem_of_mem_erase hx)
        simp only [List.toFinset_cons, Finset.mem_insert] at hxL
        rcases hxL with rfl | hx'
        · exact absurd rfl hne
        · exact hx'
      obtain ⟨hlen', hprod'⟩ := ih hL' hsub'
      have hcard : T.card = (T.erase a).card + 1 := (Finset.card_erase_add_one haT).symm
      refine ⟨by simp; omega, ?_⟩
      rw [hcard, List.take_succ_cons, List.prod_cons, ← Finset.mul_prod_erase T (fun x => x) haT]
      exact Nat.mul_le_mul_left a hprod'
    · have hsub' : T ⊆ L'.toFinset := by
        intro x hx
        have hxL := hsub hx
        simp only [List.toFinset_cons, Finset.mem_insert] at hxL
        rcases hxL with rfl | hx'
        · exact absurd hx haT
        · exact hx'
      obtain ⟨hlen', hprod'⟩ := ih hL' hsub'
      refine ⟨by simp; omega, ?_⟩
      exact hprod'.trans (prod_take_le_cons_take hL' (fun x hx => le_of_lt (hlt_a x hx)) hlen')

private def primeListDown (n : ℕ) : List ℕ :=
  ((List.range (n + 1)).reverse).filter (fun q => decide (5 ≤ q ∧ q.Prime))

private lemma primeListDown_sortedGT (n : ℕ) : (primeListDown n).SortedGT := by
  have hrev : ((List.range (n + 1)).reverse).SortedGT :=
    List.sortedGT_reverse.mpr (List.sortedLT_range (n + 1))
  exact (hrev.pairwise.filter _).sortedGT

private lemma mem_primeListDown {n q : ℕ} :
    q ∈ primeListDown n ↔ q ≤ n ∧ 5 ≤ q ∧ q.Prime := by
  simp only [primeListDown, List.mem_filter, List.mem_reverse, List.mem_range,
    decide_eq_true_eq]
  exact ⟨fun ⟨h1, h2⟩ => ⟨Nat.lt_succ_iff.mp h1, h2⟩,
    fun ⟨h1, h2⟩ => ⟨Nat.lt_succ_iff.mpr h1, h2⟩⟩

/-! ### Unified `S₁.card = k` Profile & Refutation of `k ∈ {11, 12}` -/

private lemma make_S1Profile {q p s u k : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (_hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u))
    (hk : 0 < k)
    (hcard : (s.primeFactors.filter
      (fun r => (sigma 1 (r ^ (2 * s.factorization r))).factorization p = 1)).card = k) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    let S₁ := s.primeFactors.filter (v · = 1)
    ∃ f : Fin k ↪o ℕ,
      (∀ i, f i ∈ S₁) ∧
      (∀ r ∈ S₁, ∃ i, f i = r) ∧
      (∀ i, (f i).Prime ∧ Odd (f i) ∧ 3 ≤ f i ∧ 1 ≤ s.factorization (f i) ∧
        (2 * s.factorization (f i) + 1).Prime ∧
        (2 * s.factorization (f i) + 1) ∣ (p - 1) / 2 ∧
        sigma 1 ((f i) ^ (2 * s.factorization (f i))) = p ∧
        (f i) ^ (2 * s.factorization (f i)) < p) ∧
      StrictAnti (fun i => s.factorization (f i)) ∧
      StrictAnti (fun i => 2 * s.factorization (f i) + 1) ∧
      (∀ hne : S₁.Nonempty, S₁.max' hne = f ⟨k - 1, Nat.sub_lt hk (by decide)⟩) ∧
      (∏ r ∈ S₁, (2 * s.factorization r + 1)) = ∏ i : Fin k, (2 * s.factorization (f i) + 1) := by
  intro v S₁
  let f := S₁.orderEmbOfFin hcard
  obtain ⟨_, hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  have hmem : ∀ i, f i ∈ S₁ := fun i => Finset.orderEmbOfFin_mem S₁ hcard i
  have hsurj : ∀ r ∈ S₁, ∃ i, f i = r := by
    intro r hrS
    have hr' : r ∈ Finset.image f Finset.univ := by
      rwa [Finset.image_orderEmbOfFin_univ S₁ hcard]
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hr'
    exact ⟨i, hi⟩
  have hextract : ∀ i, (f i).Prime ∧ Odd (f i) ∧ 3 ≤ f i ∧ 1 ≤ s.factorization (f i) ∧
      (2 * s.factorization (f i) + 1).Prime ∧
      (2 * s.factorization (f i) + 1) ∣ (p - 1) / 2 ∧
      sigma 1 ((f i) ^ (2 * s.factorization (f i))) = p ∧
      (f i) ^ (2 * s.factorization (f i)) < p := by
    intro i
    obtain ⟨hr, hvr⟩ := Finset.mem_filter.mp (hmem i)
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hrs := Nat.dvd_of_mem_primeFactors hr
    have hro : Odd (f i) := hs.of_dvd_nat hrs
    have hr3 : 3 ≤ f i := by have := hrp.two_le; have := Nat.odd_iff.mp hro; omega
    have hepos : 1 ≤ s.factorization (f i) :=
      (hrp.dvd_iff_one_le_factorization hs.pos.ne').mp hrs
    have hord := even_index_cofactor_component_order_dvd_pred hp hpo hs hσq hplus hσs hr
    have hlp := hord.1
    have hldvd := hord.2.2.2
    have hσr : sigma 1 ((f i) ^ (2 * s.factorization (f i))) = p := by
      have H := (hparts (f i) hr).2
      dsimp only at H
      change sigma 1 ((f i) ^ (2 * s.factorization (f i))) = p ^ v (f i) at H
      rwa [hvr, pow_one] at H
    have hpowlt : (f i) ^ (2 * s.factorization (f i)) < p := by
      rw [← hσr]
      exact self_lt_sigma_of_one_lt (one_lt_pow₀ hrp.one_lt (by omega))
    exact ⟨hrp, hro, hr3, hepos, hlp, hldvd, hσr, hpowlt⟩
  have he_anti : StrictAnti (fun i => s.factorization (f i)) := by
    intro i j hij
    exact exp_anti_of_sigma_eq (hextract i).1 (hextract j).1 (f.strictMono hij)
      (hextract i).2.2.2.1 (hextract i).2.2.2.2.2.2.1 (hextract j).2.2.2.2.2.2.1
  have hl_anti : StrictAnti (fun i => 2 * s.factorization (f i) + 1) := by
    intro i j hij
    have h := he_anti hij
    dsimp only at h ⊢
    omega
  have hmax : ∀ hne : S₁.Nonempty, S₁.max' hne = f ⟨k - 1, Nat.sub_lt hk (by decide)⟩ :=
    fun _ => (Finset.orderEmbOfFin_last hcard hk).symm
  have hprod : (∏ r ∈ S₁, (2 * s.factorization r + 1)) =
      ∏ i : Fin k, (2 * s.factorization (f i) + 1) := by
    conv_lhs => rw [← Finset.map_orderEmbOfFin_univ S₁ hcard]
    rw [Finset.prod_map]
    rfl
  exact ⟨f, hmem, hsurj, hextract, he_anti, hl_anti, hmax, hprod⟩

private lemma e0_ge_eighteen_of_card_ge_eleven {k : ℕ} (hk11 : 11 ≤ k)
    {e : Fin k → ℕ} (he_pos : ∀ i, 1 ≤ e i) (hl_prime : ∀ i, (2 * e i + 1).Prime)
    (he_anti : StrictAnti e) :
    18 ≤ e ⟨0, by omega⟩ := by
  by_contra! hlt
  have hle17 : e ⟨0, by omega⟩ ≤ 17 := by omega
  let U := (Finset.Icc 1 17).filter (fun m => (2 * m + 1).Prime)
  have himg : (Finset.univ : Finset (Fin k)).image e ⊆ U := by
    intro m hm
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hm
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨he_pos i, ?_⟩, hl_prime i⟩
    have hi : e i ≤ e ⟨0, by omega⟩ := by
      rcases Nat.eq_zero_or_pos i.1 with h0 | h0
      · rw [show i = ⟨0, by omega⟩ from Fin.ext h0]
      · exact (he_anti (Fin.mk_lt_mk.mpr h0)).le
    omega
  have hcard_le : k ≤ U.card := by
    have h1 := Finset.card_le_card himg
    rwa [Finset.card_image_of_injective _ he_anti.injective, Finset.card_univ,
      Fintype.card_fin] at h1
  have hU10 : U.card = 10 := by decide
  omega

private lemma prod_castSucc_le_primeListDown {k : ℕ} (hk : 2 ≤ k)
    {e : Fin k → ℕ} (hl_prime : ∀ i, (2 * e i + 1).Prime) (he_anti : StrictAnti e)
    (he_last : e ⟨k - 1, by omega⟩ = 1) :
    let L := primeListDown (2 * e ⟨0, by omega⟩ + 1)
    k - 1 ≤ L.length ∧
      (∏ i : Fin (k - 1), (2 * e ⟨i.1, by omega⟩ + 1)) ≤ (L.take (k - 1)).prod := by
  intro L
  let l : Fin (k - 1) → ℕ := fun i => 2 * e ⟨i.1, by omega⟩ + 1
  have hl_inj : Function.Injective l := by
    intro i j hij
    have hfi : (⟨i.1, by omega⟩ : Fin k) = ⟨j.1, by omega⟩ := by
      apply he_anti.injective
      dsimp [l] at hij
      omega
    exact Fin.ext (by simpa using congrArg Fin.val hfi)
  let T := (Finset.univ : Finset (Fin (k - 1))).image l
  have hT_sub : T ⊆ L.toFinset := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    rw [List.mem_toFinset, mem_primeListDown]
    have hle0 : e ⟨i.1, by omega⟩ ≤ e ⟨0, by omega⟩ := by
      rcases Nat.eq_zero_or_pos i.1 with h0 | h0
      · rw [show (⟨i.1, by omega⟩ : Fin k) = ⟨0, by omega⟩ from Fin.ext h0]
      · exact (he_anti (Fin.mk_lt_mk.mpr h0)).le
    have hgt_last : (⟨i.1, by omega⟩ : Fin k) < ⟨k - 1, by omega⟩ :=
      Fin.mk_lt_mk.mpr i.2
    have hge2 : 2 ≤ e ⟨i.1, by omega⟩ := by
      have := he_anti hgt_last
      omega
    dsimp [l]
    exact ⟨by omega, by omega, hl_prime ⟨i.1, by omega⟩⟩
  have hT_card : T.card = k - 1 := by
    rw [Finset.card_image_of_injective _ hl_inj, Finset.card_univ, Fintype.card_fin]
  have hprod_eq : ∏ x ∈ T, x = ∏ i : Fin (k - 1), l i := by
    rw [Finset.prod_image (fun a _ b _ h => hl_inj h)]
  obtain ⟨hlen, hprod⟩ := prod_le_sortedGT_take (primeListDown_sortedGT _) hT_sub
  rw [hT_card] at hlen hprod
  exact ⟨hlen, hprod_eq ▸ hprod⟩

private lemma prod_full_le_primeListDown {k : ℕ} (hk : 1 ≤ k)
    {e : Fin k → ℕ} (hl_prime : ∀ i, (2 * e i + 1).Prime) (he_anti : StrictAnti e)
    (he_last : 2 ≤ e ⟨k - 1, by omega⟩) :
    let L := primeListDown (2 * e ⟨0, by omega⟩ + 1)
    k ≤ L.length ∧ (∏ i : Fin k, (2 * e i + 1)) ≤ (L.take k).prod := by
  intro L
  let l : Fin k → ℕ := fun i => 2 * e i + 1
  have hl_inj : Function.Injective l := by
    intro i j hij
    apply he_anti.injective
    dsimp [l] at hij
    omega
  let T := (Finset.univ : Finset (Fin k)).image l
  have hT_sub : T ⊆ L.toFinset := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    rw [List.mem_toFinset, mem_primeListDown]
    have hle0 : e i ≤ e ⟨0, by omega⟩ := by
      rcases Nat.eq_zero_or_pos i.1 with h0 | h0
      · rw [show i = ⟨0, by omega⟩ from Fin.ext h0]
      · exact (he_anti (Fin.mk_lt_mk.mpr h0)).le
    have hge2 : 2 ≤ e i := by
      rcases Nat.lt_or_eq_of_le (Nat.le_pred_of_lt i.2) with hlt | heq
      · have hlt_fin : i < ⟨k - 1, by omega⟩ := Fin.mk_lt_mk.mpr hlt
        have h1 := he_anti hlt_fin
        omega
      · rw [show i = ⟨k - 1, by omega⟩ from Fin.ext heq]
        exact he_last
    dsimp [l]
    exact ⟨by omega, by omega, hl_prime i⟩
  have hT_card : T.card = k := by
    rw [Finset.card_image_of_injective _ hl_inj, Finset.card_univ, Fintype.card_fin]
  have hprod_eq : ∏ x ∈ T, x = ∏ i : Fin k, l i := by
    rw [Finset.prod_image (fun a _ b _ h => hl_inj h)]
  obtain ⟨hlen, hprod⟩ := prod_le_sortedGT_take (primeListDown_sortedGT _) hT_sub
  rw [hT_card] at hlen hprod
  exact ⟨hlen, hprod_eq ▸ hprod⟩

private lemma prod_castSucc_le_pow {k : ℕ} (hk : 2 ≤ k)
    {e : Fin k → ℕ} (he_anti : StrictAnti e) :
    (∏ i : Fin (k - 1), (2 * e ⟨i.1, by omega⟩ + 1)) ≤
      (2 * e ⟨0, by omega⟩ + 1) ^ (k - 1) := by
  calc (∏ i : Fin (k - 1), (2 * e ⟨i.1, by omega⟩ + 1))
      ≤ ∏ _i : Fin (k - 1), (2 * e ⟨0, by omega⟩ + 1) := by
        refine Finset.prod_le_prod fun i _ => ?_
        rcases Nat.eq_zero_or_pos i.1 with h0 | h0
        · rw [show (⟨i.1, by omega⟩ : Fin k) = ⟨0, by omega⟩ from Fin.ext h0]
        · have := he_anti (Fin.mk_lt_mk.mpr h0 : (⟨0, by omega⟩ : Fin k) < ⟨i.1, by omega⟩)
          omega
    _ = (2 * e ⟨0, by omega⟩ + 1) ^ (k - 1) := by simp

private lemma prod_full_le_pow {k : ℕ} (hk : 1 ≤ k)
    {e : Fin k → ℕ} (he_anti : StrictAnti e) :
    (∏ i : Fin k, (2 * e i + 1)) ≤ (2 * e ⟨0, by omega⟩ + 1) ^ k := by
  calc (∏ i : Fin k, (2 * e i + 1))
      ≤ ∏ _i : Fin k, (2 * e ⟨0, by omega⟩ + 1) := by
        refine Finset.prod_le_prod fun i _ => ?_
        rcases Nat.eq_zero_or_pos i.1 with h0 | h0
        · rw [show i = ⟨0, by omega⟩ from Fin.ext h0]
        · have hlt_fin : (⟨0, by omega⟩ : Fin k) < i := Fin.mk_lt_mk.mpr h0
          have h1 := he_anti hlt_fin
          change e i < e ⟨0, by omega⟩ at h1
          omega
    _ = (2 * e ⟨0, by omega⟩ + 1) ^ k := by simp

private lemma refute_card_eleven_or_twelve {q p s u k : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u))
    (hk_cases : k = 11 ∨ k = 12)
    (hcard : (s.primeFactors.filter
      (fun r => (sigma 1 (r ^ (2 * s.factorization r))).factorization p = 1)).card = k) :
    False := by
  have hk11 : 11 ≤ k := by omega
  have hk_le12 : k ≤ 12 := by omega
  have hk_pos : 0 < k := by omega
  have hk2 : 2 ≤ k := by omega
  obtain ⟨f, hmem, hsurj, hextract, he_anti, hl_anti, _, hprod_eq⟩ :=
    make_S1Profile hp hpo hs hu hσq hplus hσs hk_pos hcard
  let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
  let S₁ := s.primeFactors.filter (v · = 1)
  let e : Fin k → ℕ := fun i => s.factorization (f i)
  let l : Fin k → ℕ := fun i => 2 * e i + 1
  let e₀ := e ⟨0, hk_pos⟩
  let r₀ := f ⟨0, hk_pos⟩
  have hr₀o := (hextract ⟨0, hk_pos⟩).2.1
  have hr₀_ge3 : 3 ≤ r₀ := (hextract ⟨0, hk_pos⟩).2.2.1
  have hl₀p : (2 * e₀ + 1).Prime := (hextract ⟨0, hk_pos⟩).2.2.2.2.1
  have hσr₀ : sigma 1 (r₀ ^ (2 * e₀)) = p := (hextract ⟨0, hk_pos⟩).2.2.2.2.2.2.1
  have hr₀_pow_lt : r₀ ^ (2 * e₀) < p := (hextract ⟨0, hk_pos⟩).2.2.2.2.2.2.2
  have he₀_ge18 : 18 ≤ e₀ :=
    e0_ge_eighteen_of_card_ge_eleven hk11 (fun i => (hextract i).2.2.2.1)
      (fun i => (hextract i).2.2.2.2.1) he_anti
  have hl_ge3 : ∀ i, 3 ≤ l i := fun i => by
    have := (hextract i).2.2.2.1
    dsimp [l, e]; omega
  have hl_le0 : ∀ i, l i ≤ 2 * e₀ + 1 := fun i => by
    have hi : e i ≤ e₀ := by
      rcases Nat.eq_zero_or_pos i.1 with h0 | h0
      · rw [show i = ⟨0, hk_pos⟩ from Fin.ext h0]
      · exact (he_anti (Fin.mk_lt_mk.mpr h0)).le
    dsimp [l, e₀] at hi ⊢
    omega
  obtain ⟨_, hmoment⟩ := even_index_large_min_exponent_bound hp hpo hs hu hσq hplus hσs
  let P_L := ∏ r ∈ S₁, (2 * s.factorization r + 1)
  have hPL_eq : P_L = ∏ i : Fin k, l i := hprod_eq
  by_cases he_last1 : e ⟨k - 1, Nat.sub_lt hk_pos (by decide)⟩ = 1
  · -- Case A: smallest exponent = 1 (`l_last = 3`)
    have hdich := even_index_sharpened_symbolic_dichotomy hp hpo hs hu hσq hplus hσs
    change p < 4 * P_L ^ 2 ∨ p ^ 3 < (2 * S₁.card * P_L) ^ 4 at hdich
    rw [hcard] at hdich
    have hPL_split : P_L = 3 * ∏ i : Fin (k - 1), l ⟨i.1, by omega⟩ := by
      rw [hPL_eq]
      have hk_eq : k = (k - 1) + 1 := by omega
      let e_fin : Fin ((k - 1) + 1) → ℕ := fun i => l ⟨i.1, by omega⟩
      have h1 : (∏ i : Fin k, l i) = ∏ i : Fin ((k - 1) + 1), e_fin i := by
        refine Fintype.prod_equiv (finCongr hk_eq) _ _ fun i => ?_
        simp [e_fin]
      rw [h1, Fin.prod_univ_castSucc, mul_comm]
      have hlast : e_fin (Fin.last (k - 1)) = 3 := by
        change l ⟨k - 1, _⟩ = 3
        dsimp [l]; omega
      rw [hlast]
      rfl
    have hbound_or : 3 ^ (2 * e₀) < 4 * P_L ^ 2 ∨ 3 ^ (6 * e₀) < (2 * k * P_L) ^ 4 := by
      have h3_lt_p : 3 ^ (2 * e₀) < p :=
        (Nat.pow_le_pow_left hr₀_ge3 (2 * e₀)).trans_lt hr₀_pow_lt
      have h3_lt_p3 : 3 ^ (6 * e₀) < p ^ 3 := by
        have h1 : 3 ^ (6 * e₀) = (3 ^ (2 * e₀)) ^ 3 := by rw [← pow_mul]; ring_nf
        rw [h1]
        exact Nat.pow_lt_pow_left h3_lt_p (by decide)
      rcases hdich with hp_lt | hp3_lt
      · exact Or.inl (h3_lt_p.trans hp_lt)
      · exact Or.inr (h3_lt_p3.trans hp3_lt)
    have hB_fail_of_ge31 : 31 ≤ e₀ → (2 * k * P_L) ^ 4 ≤ 3 ^ (6 * e₀) := by
      intro he₀_ge31
      have hPL_pow : P_L ≤ 3 * (2 * e₀ + 1) ^ (k - 1) := by
        rw [hPL_split]
        exact Nat.mul_le_mul_left 3 (prod_castSucc_le_pow hk2 he_anti)
      calc (2 * k * P_L) ^ 4
          ≤ (2 * 12 * (3 * (2 * e₀ + 1) ^ (k - 1))) ^ 4 := by gcongr
        _ = 72 ^ 4 * (2 * e₀ + 1) ^ (4 * (k - 1)) := by ring
        _ ≤ 72 ^ 4 * (2 * e₀ + 1) ^ 44 := by
            refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
        _ ≤ 3 ^ (6 * e₀) := by
            exact exp_domination_of_step (e₀ := 31) (by decide) he₀_ge31
              (by norm_num) (by norm_num)
    by_cases he₀_ge48 : 48 ≤ e₀
    · have hPL_pow : P_L ≤ 3 * (2 * e₀ + 1) ^ (k - 1) := by
        rw [hPL_split]
        exact Nat.mul_le_mul_left 3 (prod_castSucc_le_pow hk2 he_anti)
      have hA_fail : 4 * P_L ^ 2 ≤ 3 ^ (2 * e₀) := by
        calc 4 * P_L ^ 2
            ≤ 4 * (3 * (2 * e₀ + 1) ^ (k - 1)) ^ 2 := by gcongr
          _ = 36 * (2 * e₀ + 1) ^ (2 * (k - 1)) := by ring
          _ ≤ 36 * (2 * e₀ + 1) ^ 22 := by
              refine Nat.mul_le_mul_left 36 (Nat.pow_le_pow_right (by omega) (by omega))
          _ ≤ 3 ^ (2 * e₀) := by
              exact exp_domination_of_step (e₀ := 48) (by decide) he₀_ge48
                (by norm_num) (by norm_num)
      rcases hbound_or with hA | hB
      · exact absurd hA (not_lt_of_ge hA_fail)
      · exact absurd hB (not_lt_of_ge (hB_fail_of_ge31 (by omega)))
    · -- Finite check for 18 ≤ e₀ ≤ 47
      obtain ⟨hlen, hprod_L⟩ := prod_castSucc_le_primeListDown hk2
        (fun i => (hextract i).2.2.2.2.1) he_anti he_last1
      let M := ((primeListDown (2 * e₀ + 1)).take (k - 1)).prod
      have hPL_le_M : P_L ≤ 3 * M := by
        rw [hPL_split]
        exact Nat.mul_le_mul_left 3 hprod_L
      have hsurv_3 : e₀ ∈ ({18, 20, 21, 23, 26, 29, 30, 33, 35, 36, 39, 41} : Finset ℕ) := by
        by_cases he₀_ge31 : 31 ≤ e₀
        · have hA : 3 ^ (2 * e₀) < 4 * P_L ^ 2 := by
            rcases hbound_or with hA | hB
            · exact hA
            · exact absurd hB (not_lt_of_ge (hB_fail_of_ge31 he₀_ge31))
          have h3_A : 3 ^ (2 * e₀) < 4 * (3 * M) ^ 2 := hA.trans_le (by gcongr)
          have he₀_mem : e₀ ∈ Finset.Ico 31 48 := Finset.mem_Ico.mpr ⟨he₀_ge31, by omega⟩
          have hcheck_11 : ∀ x ∈ Finset.Ico 31 48, (2 * x + 1).Prime →
              10 ≤ (primeListDown (2 * x + 1)).length →
              3 ^ (2 * x) < 4 * (3 * ((primeListDown (2 * x + 1)).take 10).prod) ^ 2 →
              x ∈ ({18, 20, 21, 23, 26, 29, 30, 33, 35, 36, 39, 41} : Finset ℕ) := by decide
          have hcheck_12 : ∀ x ∈ Finset.Ico 31 48, (2 * x + 1).Prime →
              11 ≤ (primeListDown (2 * x + 1)).length →
              3 ^ (2 * x) < 4 * (3 * ((primeListDown (2 * x + 1)).take 11).prod) ^ 2 →
              x ∈ ({18, 20, 21, 23, 26, 29, 30, 33, 35, 36, 39, 41} : Finset ℕ) := by decide
          rcases hk_cases with rfl | rfl
          · exact hcheck_11 e₀ he₀_mem hl₀p hlen h3_A
          · exact hcheck_12 e₀ he₀_mem hl₀p hlen h3_A
        · have he₀_mem : e₀ ∈ Finset.Ico 18 31 := Finset.mem_Ico.mpr ⟨he₀_ge18, by omega⟩
          have hcheck_11 : ∀ x ∈ Finset.Ico 18 31, (2 * x + 1).Prime →
              10 ≤ (primeListDown (2 * x + 1)).length →
              (3 ^ (2 * x) < 4 * (3 * ((primeListDown (2 * x + 1)).take 10).prod) ^ 2 ∨
                3 ^ (6 * x) < (2 * 11 * (3 * ((primeListDown (2 * x + 1)).take 10).prod)) ^ 4) →
              x ∈ ({18, 20, 21, 23, 26, 29, 30, 33, 35, 36, 39, 41} : Finset ℕ) := by decide
          have hcheck_12 : ∀ x ∈ Finset.Ico 18 31, (2 * x + 1).Prime →
              11 ≤ (primeListDown (2 * x + 1)).length →
              (3 ^ (2 * x) < 4 * (3 * ((primeListDown (2 * x + 1)).take 11).prod) ^ 2 ∨
                3 ^ (6 * x) < (2 * 12 * (3 * ((primeListDown (2 * x + 1)).take 11).prod)) ^ 4) →
              x ∈ ({18, 20, 21, 23, 26, 29, 30, 33, 35, 36, 39, 41} : Finset ℕ) := by decide
          have h3_or : 3 ^ (2 * e₀) < 4 * (3 * M) ^ 2 ∨ 3 ^ (6 * e₀) < (2 * k * (3 * M)) ^ 4 := by
            rcases hbound_or with hA | hB
            · left; exact hA.trans_le (by gcongr)
            · right; exact hB.trans_le (by gcongr)
          rcases hk_cases with rfl | rfl
          · exact hcheck_11 e₀ he₀_mem hl₀p hlen h3_or
          · exact hcheck_12 e₀ he₀_mem hl₀p hlen h3_or
      by_cases hr₀_ge5 : 5 ≤ r₀
      · have hbound_5 : 5 ^ (2 * e₀) < 4 * (3 * M) ^ 2 ∨
            5 ^ (6 * e₀) < (2 * k * (3 * M)) ^ 4 := by
          have h5_lt_p : 5 ^ (2 * e₀) < p :=
            (Nat.pow_le_pow_left hr₀_ge5 (2 * e₀)).trans_lt hr₀_pow_lt
          have h5_lt_p3 : 5 ^ (6 * e₀) < p ^ 3 := by
            have h1 : 5 ^ (6 * e₀) = (5 ^ (2 * e₀)) ^ 3 := by rw [← pow_mul]; ring_nf
            rw [h1]
            exact Nat.pow_lt_pow_left h5_lt_p (by decide)
          rcases hdich with hp_lt | hp3_lt
          · left; exact h5_lt_p.trans (hp_lt.trans_le (by gcongr))
          · right; exact h5_lt_p3.trans (hp3_lt.trans_le (by gcongr))
        have hsurv_5 : e₀ ∈ ({18, 20, 21, 23} : Finset ℕ) := by
          have h5_11 : ∀ x ∈ ({18, 20, 21, 23, 26, 29, 30, 33, 35, 36, 39, 41} : Finset ℕ),
              (5 ^ (2 * x) < 4 * (3 * ((primeListDown (2 * x + 1)).take 10).prod) ^ 2 ∨
                5 ^ (6 * x) < (2 * 11 * (3 * ((primeListDown (2 * x + 1)).take 10).prod)) ^ 4) →
              x ∈ ({18, 20, 21, 23} : Finset ℕ) := by decide
          have h5_12 : ∀ x ∈ ({18, 20, 21, 23, 26, 29, 30, 33, 35, 36, 39, 41} : Finset ℕ),
              (5 ^ (2 * x) < 4 * (3 * ((primeListDown (2 * x + 1)).take 11).prod) ^ 2 ∨
                5 ^ (6 * x) < (2 * 12 * (3 * ((primeListDown (2 * x + 1)).take 11).prod)) ^ 4) →
              x ∈ ({18, 20, 21, 23} : Finset ℕ) := by decide
          rcases hk_cases with rfl | rfl
          · exact h5_11 e₀ hsurv_3 hbound_5
          · exact h5_12 e₀ hsurv_3 hbound_5
        by_cases hr₀_ge7 : 7 ≤ r₀
        · have hbound_7 : 7 ^ (2 * e₀) < 4 * (3 * M) ^ 2 ∨
              7 ^ (6 * e₀) < (2 * k * (3 * M)) ^ 4 := by
            have h7_lt_p : 7 ^ (2 * e₀) < p :=
              (Nat.pow_le_pow_left hr₀_ge7 (2 * e₀)).trans_lt hr₀_pow_lt
            have h7_lt_p3 : 7 ^ (6 * e₀) < p ^ 3 := by
              have h1 : 7 ^ (6 * e₀) = (7 ^ (2 * e₀)) ^ 3 := by rw [← pow_mul]; ring_nf
              rw [h1]
              exact Nat.pow_lt_pow_left h7_lt_p (by decide)
            rcases hdich with hp_lt | hp3_lt
            · left; exact h7_lt_p.trans (hp_lt.trans_le (by gcongr))
            · right; exact h7_lt_p3.trans (hp3_lt.trans_le (by gcongr))
          have h7_11 : ∀ x ∈ ({18, 20, 21, 23} : Finset ℕ),
              ¬ (7 ^ (2 * x) < 4 * (3 * ((primeListDown (2 * x + 1)).take 10).prod) ^ 2 ∨
                7 ^ (6 * x) < (2 * 11 * (3 * ((primeListDown (2 * x + 1)).take 10).prod)) ^ 4) := by
            decide
          have h7_12 : ∀ x ∈ ({18, 20, 21, 23} : Finset ℕ),
              ¬ (7 ^ (2 * x) < 4 * (3 * ((primeListDown (2 * x + 1)).take 11).prod) ^ 2 ∨
                7 ^ (6 * x) < (2 * 12 * (3 * ((primeListDown (2 * x + 1)).take 11).prod)) ^ 4) := by
            decide
          rcases hk_cases with rfl | rfl
          · exact h7_11 e₀ hsurv_5 hbound_7
          · exact h7_12 e₀ hsurv_5 hbound_7
        · have hr₀_eq5 : r₀ = 5 := by have := Nat.odd_iff.mp hr₀o; omega
          rw [hr₀_eq5] at hσr₀
          by_cases he₀_23 : e₀ = 23
          · have hσ46 : sigma 1 (5 ^ 46) = p := by
              simpa [he₀_23] using hσr₀
            exact refute_five_pow_46_repunit hk11 (fun i => (hextract i).2.2.2.2.1)
              hl_anti hl_ge3 (fun i => (hl_le0 i).trans (by omega))
              (fun i => (hextract i).2.2.2.2.2.1) hσ46
          · have hsurv_5_comp : e₀ ∈ ({18, 20, 21} : Finset ℕ) := by
              have hfilter : ∀ x ∈ ({18, 20, 21, 23} : Finset ℕ), x ≠ 23 →
                  x ∈ ({18, 20, 21} : Finset ℕ) := by decide
              exact hfilter e₀ hsurv_5 he₀_23
            exact not_sigma_five_pow_prime_of_mem hp hσr₀ hsurv_5_comp
      · have hr₀_eq3 : r₀ = 3 := by have := Nat.odd_iff.mp hr₀o; omega
        rw [hr₀_eq3] at hσr₀
        by_cases he₀_35 : e₀ = 35
        · have hσ70 : sigma 1 (3 ^ 70) = p := by
            simpa [he₀_35] using hσr₀
          exact refute_three_pow_70_repunit hk11 (fun i => (hextract i).2.2.2.2.1)
            hl_anti hl_ge3 (fun i => (hl_le0 i).trans (by omega))
            (fun i => (hextract i).2.2.2.2.2.1) hσ70
        · have hsurv_3_comp :
              e₀ ∈ ({18, 20, 21, 23, 26, 29, 30, 33, 36, 39, 41} : Finset ℕ) := by
            have hfilter :
                ∀ x ∈ ({18, 20, 21, 23, 26, 29, 30, 33, 35, 36, 39, 41} : Finset ℕ),
                  x ≠ 35 →
                  x ∈ ({18, 20, 21, 23, 26, 29, 30, 33, 36, 39, 41} : Finset ℕ) := by decide
            exact hfilter e₀ hsurv_3 he₀_35
          exact not_sigma_three_pow_prime_of_mem hp hσr₀ hsurv_3_comp
  · -- Case B: all exponents ≥ 2
    have he_last_ge2 : 2 ≤ e ⟨k - 1, Nat.sub_lt hk_pos (by decide)⟩ := by
      have h1 := (hextract ⟨k - 1, Nat.sub_lt hk_pos (by decide)⟩).2.2.2.1
      change 1 ≤ e ⟨k - 1, Nat.sub_lt hk_pos (by decide)⟩ at h1
      omega
    have h2_all : ∀ r ∈ S₁, 2 ≤ s.factorization r := by
      intro r hrS
      obtain ⟨i, rfl⟩ := hsurj r hrS
      change 2 ≤ e i
      rcases Nat.lt_or_eq_of_le (Nat.le_pred_of_lt i.2) with hlt | heq
      · have h1 := he_anti (Fin.mk_lt_mk.mpr hlt : i < ⟨k - 1, Nat.sub_lt hk_pos (by decide)⟩)
        change e ⟨k - 1, Nat.sub_lt hk_pos (by decide)⟩ < e i at h1
        omega
      · rw [show i = ⟨k - 1, Nat.sub_lt hk_pos (by decide)⟩ from Fin.ext heq]
        exact he_last_ge2
    have hp3_lt := hmoment 2 (by decide) h2_all
    change p ^ 3 < (2 * S₁.card * P_L) ^ 4 at hp3_lt
    rw [hcard] at hp3_lt
    by_cases he₀_ge33 : 33 ≤ e₀
    · have h3_lt_p3 : 3 ^ (6 * e₀) < p ^ 3 := by
        have h3p : 3 ^ (2 * e₀) < p :=
          (Nat.pow_le_pow_left hr₀_ge3 (2 * e₀)).trans_lt hr₀_pow_lt
        have h1 : 3 ^ (6 * e₀) = (3 ^ (2 * e₀)) ^ 3 := by rw [← pow_mul]; ring_nf
        rw [h1]
        exact Nat.pow_lt_pow_left h3p (by decide)
      have hPL_pow : P_L ≤ (2 * e₀ + 1) ^ k := by
        rw [hPL_eq]
        exact prod_full_le_pow hk_pos he_anti
      have hB_fail : (2 * k * P_L) ^ 4 ≤ 3 ^ (6 * e₀) := by
        calc (2 * k * P_L) ^ 4
            ≤ (2 * 12 * (2 * e₀ + 1) ^ k) ^ 4 := by gcongr
          _ = 24 ^ 4 * (2 * e₀ + 1) ^ (4 * k) := by ring
          _ ≤ 24 ^ 4 * (2 * e₀ + 1) ^ 48 := by
              refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
          _ ≤ 3 ^ (6 * e₀) := by
              exact exp_domination_of_step (e₀ := 33) (by decide) he₀_ge33
                (by norm_num) (by norm_num)
      exact absurd (h3_lt_p3.trans hp3_lt) (not_lt_of_ge hB_fail)
    · have he₀_mem : e₀ ∈ Finset.Ico 18 33 := Finset.mem_Ico.mpr ⟨he₀_ge18, by omega⟩
      obtain ⟨hlen, hprod_L⟩ := prod_full_le_primeListDown hk_pos
        (fun i => (hextract i).2.2.2.2.1) he_anti he_last_ge2
      let M := ((primeListDown (2 * e₀ + 1)).take k).prod
      have hPL_le_M : P_L ≤ M := by
        rw [hPL_eq]; exact hprod_L
      have h3_lt_M : 3 ^ (6 * e₀) < (2 * k * M) ^ 4 := by
        have h3p : 3 ^ (2 * e₀) < p :=
          (Nat.pow_le_pow_left hr₀_ge3 (2 * e₀)).trans_lt hr₀_pow_lt
        have h1 : 3 ^ (6 * e₀) = (3 ^ (2 * e₀)) ^ 3 := by rw [← pow_mul]; ring_nf
        rw [h1]
        exact (Nat.pow_lt_pow_left h3p (by decide)).trans (hp3_lt.trans_le (by gcongr))
      have hsurv_3 : e₀ ∈ ({20, 21, 23} : Finset ℕ) := by
        have hB_11 : ∀ x ∈ Finset.Ico 18 33, (2 * x + 1).Prime →
            11 ≤ (primeListDown (2 * x + 1)).length →
            3 ^ (6 * x) < (2 * 11 * ((primeListDown (2 * x + 1)).take 11).prod) ^ 4 →
            x ∈ ({20, 21, 23} : Finset ℕ) := by decide
        have hB_12 : ∀ x ∈ Finset.Ico 18 33, (2 * x + 1).Prime →
            12 ≤ (primeListDown (2 * x + 1)).length →
            3 ^ (6 * x) < (2 * 12 * ((primeListDown (2 * x + 1)).take 12).prod) ^ 4 →
            x ∈ ({20, 21, 23} : Finset ℕ) := by decide
        rcases hk_cases with rfl | rfl
        · exact hB_11 e₀ he₀_mem hl₀p hlen h3_lt_M
        · exact hB_12 e₀ he₀_mem hl₀p hlen h3_lt_M
      by_cases hr₀_ge5 : 5 ≤ r₀
      · have h5_lt_M : 5 ^ (6 * e₀) < (2 * k * M) ^ 4 := by
          have h5p : 5 ^ (2 * e₀) < p :=
            (Nat.pow_le_pow_left hr₀_ge5 (2 * e₀)).trans_lt hr₀_pow_lt
          have h1 : 5 ^ (6 * e₀) = (5 ^ (2 * e₀)) ^ 3 := by rw [← pow_mul]; ring_nf
          rw [h1]
          exact (Nat.pow_lt_pow_left h5p (by decide)).trans (hp3_lt.trans_le (by gcongr))
        have hB5_11 : ∀ x ∈ ({20, 21, 23} : Finset ℕ),
            ¬ (5 ^ (6 * x) < (2 * 11 * ((primeListDown (2 * x + 1)).take 11).prod) ^ 4) := by
          decide
        have hB5_12 : ∀ x ∈ ({20, 21, 23} : Finset ℕ),
            ¬ (5 ^ (6 * x) < (2 * 12 * ((primeListDown (2 * x + 1)).take 12).prod) ^ 4) := by
          decide
        rcases hk_cases with rfl | rfl
        · exact hB5_11 e₀ hsurv_3 h5_lt_M
        · exact hB5_12 e₀ hsurv_3 h5_lt_M
      · have hr₀_eq3 : r₀ = 3 := by have := Nat.odd_iff.mp hr₀o; omega
        rw [hr₀_eq3] at hσr₀
        exact not_sigma_three_pow_prime_of_mem hp hσr₀
          (Finset.mem_of_subset (by decide) hsurv_3)

/-! ### Main Tridecuple Repunit & Size Bounds -/

/-- Unconditionally, at any even prime-power component index `p ^ (2 * u)`,
at least thirteen distinct cofactor primes return `p` with valuation `1`. -/
theorem even_index_thirteen_le_S1_card {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    13 ≤ (s.primeFactors.filter (v · = 1)).card := by
  intro v
  have hge11 := even_index_eleven_le_S1_card hp hpo hs hu hσq hplus hσs
  change 11 ≤ (s.primeFactors.filter (v · = 1)).card at hge11
  by_contra! hlt13
  have hk : (s.primeFactors.filter (v · = 1)).card = 11 ∨
      (s.primeFactors.filter (v · = 1)).card = 12 := by omega
  exact refute_card_eleven_or_twelve hp hpo hs hu hσq hplus hσs hk rfl

/-- Every even prime-power component index `p ^ (2 * u)` forces at least thirteen
simultaneous odd-prime-base repunit representations of `p`. -/
theorem even_index_forces_thirteen_repunits {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    HasThirteenOddPrimeRepunits p := by
  let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
  let S₁ := s.primeFactors.filter (v · = 1)
  have hS1_ge13 : 13 ≤ S₁.card := even_index_thirteen_le_S1_card hp hpo hs hu hσq hplus hσs
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hS1_ge13
  obtain ⟨_, hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  refine ⟨T, hTcard, fun r hrT => ?_⟩
  obtain ⟨hr, hvr⟩ := Finset.mem_filter.mp (hTS hrT)
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
  exact ⟨hrp, hro, 2 * s.factorization r + 1, hlp, by omega, hgb⟩

private lemma two_mul_add_one_lt_three_pow {e : ℕ} (he : 1 ≤ e) :
    2 * e + 1 < 3 ^ (2 * e) := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ k _ ih =>
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
    have hlt := two_mul_add_one_lt_three_pow hu
    rw [h2u_eq] at hlt
    omega
  exact lt_of_le_of_ne (Finset.filter_subset _ _) hS1_ne_full

/-- Unconditional strengthening at any even prime-power component index `i = p ^ (2 * u)`:
`p` has at least thirteen simultaneous odd-prime-base repunit representations and `N` has
at least 16 distinct prime factors. -/
theorem even_prime_power_component_forces_thirteen_repunits_and_sixteen_primes
    {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    HasThirteenOddPrimeRepunits p ∧ 16 ≤ N.primeFactors.card := by
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
  have hthirteen := even_index_forces_thirteen_repunits hp hpo hso hu hσ hplus hσs
  have hS1_ge13 := even_index_thirteen_le_S1_card hp hpo hso hu hσ hplus hσs
  have hS1_ssub := even_index_S1_ssubset_primeFactors hp hso hu hσ hplus hσs
  have hs_ge14 : 14 ≤ s.primeFactors.card := by
    have := Finset.card_lt_card hS1_ssub
    omega
  have hn := prime_count_of_even_index_split hq hp hmo hso hu hqm hcop hform hms
  exact ⟨hthirteen, by omega⟩

private def oddPrimes43 : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]

private lemma oddPrimes43_prod_lower_bound {S : Finset ℕ} (h13 : 13 ≤ S.card)
    (hodd : ∀ r ∈ S, r.Prime ∧ 3 ≤ r) :
    6541380665835015 ≤ ∏ r ∈ S, r := by
  let f := S.orderEmbOfCardLe h13
  have hlen : oddPrimes43.length = 13 := rfl
  have hsorted : oddPrimes43.SortedLT := by decide
  have hmem_all : ∀ q ∈ Finset.Icc 3 43, q.Prime → q ∈ oddPrimes43 := by decide
  have hmem_le43 : ∀ q ∈ oddPrimes43, q ≤ 43 := by decide
  have hle_elem : ∀ i : Fin 13, oddPrimes43[i.1]'(by omega) ≤ f i := by
    intro i
    by_contra! hlt
    have hi_le43 : oddPrimes43[i.1]'(by omega) ≤ 43 := hmem_le43 _ (List.getElem_mem _)
    have himg : (Finset.Iic i).image f ⊆ (oddPrimes43.take i.1).toFinset := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      have hj_le : j ≤ i := Finset.mem_Iic.mp hj
      have hfx_le : f j ≤ f i := f.monotone hj_le
      have hfx_lt : f j < oddPrimes43[i.1]'(by omega) := hfx_le.trans_lt hlt
      have hfx_prop := hodd (f j) (Finset.orderEmbOfCardLe_mem S h13 j)
      have hfx_mem : f j ∈ oddPrimes43 :=
        hmem_all (f j) (Finset.mem_Icc.mpr ⟨hfx_prop.2, by omega⟩) hfx_prop.1
      obtain ⟨m, hm_len, hm_eq⟩ := List.mem_iff_getElem.mp hfx_mem
      have hm_lt : m < i.1 := by
        by_contra! hm_ge
        have hle_m : oddPrimes43[i.1]'(by omega) ≤ oddPrimes43[m]'hm_len :=
          hsorted.sortedLE.getElem_le_getElem_of_le hm_ge
        omega
      have htake : (oddPrimes43.take i.1)[m]'(by rw [List.length_take]; omega) = f j := by
        rw [List.getElem_take]
        exact hm_eq
      rw [List.mem_toFinset, ← htake]
      exact List.getElem_mem _
    have hcard_le := Finset.card_le_card himg
    have hcard_lhs : ((Finset.Iic i).image f).card = i.1 + 1 := by
      rw [Finset.card_image_of_injective _ f.injective, Fin.card_Iic]
    have hcard_rhs : (oddPrimes43.take i.1).toFinset.card ≤ i.1 :=
      (List.toFinset_card_le _).trans (by rw [List.length_take]; omega)
    omega
  have hprod_43 : 6541380665835015 = ∏ i : Fin 13, oddPrimes43[i.1]'(by omega) := by
    have h1 : (∏ i : Fin 13, oddPrimes43[i.1]'(by omega)) = oddPrimes43.prod := by
      rw [← Fin.prod_univ_getElem oddPrimes43]
      rfl
    have h2 : oddPrimes43.prod = 6541380665835015 := by norm_num [oddPrimes43]
    omega
  have hprod_sub : ∏ i : Fin 13, f i ≤ ∏ r ∈ S, r := by
    have hsub : (Finset.univ : Finset (Fin 13)).map f.toEmbedding ⊆ S := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
      exact Finset.orderEmbOfCardLe_mem S h13 i
    have hmap_prod : ∏ i : Fin 13, f i =
        ∏ r ∈ (Finset.univ : Finset (Fin 13)).map f.toEmbedding, r := by
      rw [Finset.prod_map]
      rfl
    rw [hmap_prod]
    exact Finset.prod_le_prod_of_subset_of_one_le hsub fun r hr _ =>
      (hodd r hr).1.one_le
  calc 6541380665835015 = ∏ i : Fin 13, oddPrimes43[i.1]'(by omega) := hprod_43
    _ ≤ ∏ i : Fin 13, f i := Finset.prod_le_prod fun i _ => hle_elem i
    _ ≤ ∏ r ∈ S, r := hprod_sub

/-- At any even prime-power component index `i = p ^ (2 * u)`, `13 ≤ S₁.card` combined with
`∏ r ∈ S₁, r ∣ u + 1` and the repunit representations forces `6541380665835014 ≤ u`,
`13082761331670028 ≤ 2 * u`, `10 ^ 27 < p`, and `10 ^ 353234555955090756 < p ^ (2 * u)`. -/
theorem even_index_exponent_ge_13082761331670028 {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    6541380665835014 ≤ u ∧ 13082761331670028 ≤ 2 * u ∧
      10 ^ 27 < p ∧ 10 ^ 353234555955090756 < p ^ (2 * u) := by
  let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
  let S₁ := s.primeFactors.filter (v · = 1)
  have hS1_ge13 : 13 ≤ S₁.card := even_index_thirteen_le_S1_card hp hpo hs hu hσq hplus hσs
  have hS1_pos : 0 < S₁.card := by omega
  obtain ⟨f, _, _, hextract, he_anti, _, _, _⟩ :=
    make_S1Profile hp hpo hs hu hσq hplus hσs hS1_pos rfl
  have hS1_odd : ∀ r ∈ S₁, r.Prime ∧ 3 ≤ r := by
    intro r hrS
    have hr := (Finset.mem_filter.mp hrS).1
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hro := hs.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr)
    have := hrp.two_le; have := Nat.odd_iff.mp hro
    exact ⟨hrp, by omega⟩
  have hprod_ge := oddPrimes43_prod_lower_bound hS1_ge13 hS1_odd
  have hprod_dvd : (∏ r ∈ S₁, r) ∣ u + 1 :=
    (even_index_S1_exact_mod_sq hp hs hσq hplus hσs).2
  have hprod_le : ∏ r ∈ S₁, r ≤ u + 1 := Nat.le_of_dvd (by omega) hprod_dvd
  have hu_ge : 6541380665835014 ≤ u := by omega
  have h2u_ge : 13082761331670028 ≤ 2 * u := by omega
  have hp_gt27 : 10 ^ 27 < p := by
    let e₀ := s.factorization (f ⟨0, hS1_pos⟩)
    let r₀ := f ⟨0, hS1_pos⟩
    have hr₀o : Odd r₀ := (hextract ⟨0, hS1_pos⟩).2.1
    have hr₀_ge3 : 3 ≤ r₀ := (hextract ⟨0, hS1_pos⟩).2.2.1
    have hr₀_pow_lt : r₀ ^ (2 * e₀) < p := (hextract ⟨0, hS1_pos⟩).2.2.2.2.2.2.2
    have hσr₀ : sigma 1 (r₀ ^ (2 * e₀)) = p := (hextract ⟨0, hS1_pos⟩).2.2.2.2.2.2.1
    have he₀_ge21 : 21 ≤ e₀ := by
      by_contra! hlt
      have hle20 : e₀ ≤ 20 := by omega
      let U := (Finset.Icc 1 20).filter (fun m => (2 * m + 1).Prime)
      have himg : (Finset.univ : Finset (Fin S₁.card)).image (fun i => s.factorization (f i)) ⊆ U := by
        intro m hm
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hm
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(hextract i).2.2.2.1, ?_⟩,
          (hextract i).2.2.2.2.1⟩
        have hi : s.factorization (f i) ≤ e₀ := by
          rcases Nat.eq_zero_or_pos i.1 with h0 | h0
          · rw [show i = ⟨0, hS1_pos⟩ from Fin.ext h0]
          · exact (he_anti (Fin.mk_lt_mk.mpr h0)).le
        omega
      have hcard_le : S₁.card ≤ U.card := by
        have h1 := Finset.card_le_card himg
        rwa [Finset.card_image_of_injective _ he_anti.injective, Finset.card_univ,
          Fintype.card_fin] at h1
      have hU12 : U.card = 12 := by decide
      omega
    by_cases hr₀_ge5 : 5 ≤ r₀
    · have h5 : (5 : ℕ) ^ 42 ≤ r₀ ^ (2 * e₀) :=
        (Nat.pow_le_pow_right (by decide : 0 < 5) (by omega : 42 ≤ 2 * e₀)).trans
          (Nat.pow_le_pow_left hr₀_ge5 (2 * e₀))
      have hbig : 10 ^ 27 < (5 : ℕ) ^ 42 := by norm_num
      omega
    · have hr₀_eq3 : r₀ = 3 := by have := Nat.odd_iff.mp hr₀o; omega
      by_cases he₀_ge29 : 29 ≤ e₀
      · have h3 : (3 : ℕ) ^ 58 ≤ r₀ ^ (2 * e₀) :=
          (Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 58 ≤ 2 * e₀)).trans
            (Nat.pow_le_pow_left hr₀_ge3 (2 * e₀))
        have hbig : 10 ^ 27 < (3 : ℕ) ^ 58 := by norm_num
        omega
      · have hl₀p : (2 * e₀ + 1).Prime := (hextract ⟨0, hS1_pos⟩).2.2.2.2.1
        have he₀_mem : e₀ ∈ Finset.Ico 21 29 := Finset.mem_Ico.mpr ⟨he₀_ge21, by omega⟩
        have he₀_surv :
            e₀ ∈ ({18, 20, 21, 23, 26, 29, 30, 33, 36, 39, 41} : Finset ℕ) := by
          have hcheck : ∀ x ∈ Finset.Ico 21 29, (2 * x + 1).Prime →
              x ∈ ({18, 20, 21, 23, 26, 29, 30, 33, 36, 39, 41} : Finset ℕ) := by decide
          exact hcheck e₀ he₀_mem hl₀p
        rw [hr₀_eq3] at hσr₀
        exact False.elim (not_sigma_three_pow_prime_of_mem hp hσr₀ he₀_surv)
  have hpow_gt : 10 ^ 353234555955090756 < p ^ (2 * u) := by
    have h1 : (10 ^ 27) ^ 13082761331670028 = 10 ^ (27 * 13082761331670028) :=
      (pow_mul 10 27 13082761331670028).symm
    have h2 : 27 * 13082761331670028 = 353234555955090756 := by norm_num
    have hpow1 : 10 ^ 353234555955090756 = (10 ^ 27) ^ 13082761331670028 :=
      (congrArg (10 ^ ·) h2).symm.trans h1.symm
    have hpow2 : (10 ^ 27) ^ 13082761331670028 < p ^ 13082761331670028 :=
      pow_lt_pow_left₀ hp_gt27 (Nat.zero_le _) (by decide)
    have hpow3 : p ^ 13082761331670028 ≤ p ^ (2 * u) :=
      pow_le_pow_right₀ hp.one_le h2u_ge
    exact lt_of_eq_of_lt hpow1 (lt_of_lt_of_le hpow2 hpow3)
  exact ⟨hu_ge, h2u_ge, hp_gt27, hpow_gt⟩

/-- Every even prime-power component index `i = p ^ j` of an odd perfect number
satisfies `13082761331670028 ≤ j`, `10 ^ 353234555955090756 < i`, and
`10 ^ 353234555955090756 < N`. -/
theorem even_prime_power_component_size_gt_ten_pow_353234555955090756 {N q a b i p j : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b)
    (hl : sigma 1 b = q ^ a * i) (hr : sigma 1 (q ^ a) * i = 2 * b)
    (hp : p.Prime) (hj : 0 < j) (hje : Even j) (hi : i = p ^ j) :
    13082761331670028 ≤ j ∧ 10 ^ 353234555955090756 < i ∧ 10 ^ 353234555955090756 < N := by
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
    have hb_le : b ≤ N := hform ▸ Nat.le_mul_of_pos_left b (pow_pos hq.pos a)
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
    even_index_exponent_ge_13082761331670028 hp hpo hs hu hσq hplus hσs
  have hj_ge : 13082761331670028 ≤ j := h2u_ge.trans_eq hj2.symm
  have hi_gt : 10 ^ 353234555955090756 < i := lt_of_lt_of_eq hpow_gt hi_even.symm
  exact ⟨hj_ge, hi_gt, hi_gt.trans hi_lt_N⟩

end OddPerfect
