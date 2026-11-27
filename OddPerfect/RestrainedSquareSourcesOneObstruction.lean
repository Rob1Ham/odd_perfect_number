module

public import OddPerfect.GlobalWave11Obstruction
public import OddPerfect.Abundance
public import OddPerfect.Thirteen
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Sort
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Restrained `3^2 ∥ N` Obstruction when `squareSourcesOne N = ∅` (`OddPerfect.RestrainedSquareSourcesOneObstruction`)

Unconditionally proves that for any restrained odd perfect number (`(largeSources N q).card ≤ 1`),
if `squareSourcesOne N = ∅`, then `4 ≤ N.factorization 3` and `81 ∣ N` — removing Wave 11's
`q % 3 = 2` restriction completely whenever `squareSourcesOne N = ∅`.

Consequently, any restrained odd perfect number with `N.factorization 3 = 2` satisfies
`q % 12 = 1 ∧ 13 ≤ q ∧ (squareSourcesOne N).Nonempty ∧ 1 ≤ (squareSourcesOne N).card ≤ 2`.

## Main Theorems
- `four_le_three_exponent_of_restrained_squareSourcesOne_empty`
- `restrained_exact_nine_profile`
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma false_of_dvd_of_two_mul_lt_sigma {N D : ℕ} (hN : N.Perfect)
    (hD : D ∣ N) (hgt : 2 * D < sigma 1 D) : False := by
  have hab : Nat.Abundant D :=
    Nat.abundant_iff_sum_divisors.mpr (by simpa [sigma_one_apply] using hgt)
  exact ((Nat.perfect_iff_not_abundant_and_not_deficient hN.2.ne).mp hN).1
    (hab.of_dvd hD hN.2.ne')

private lemma sigma_prime_pow_ratio_lt {p k c₁ c₂ : ℕ} (hp : p.Prime) (hc₁ : 0 < c₁)
    (hcoef : c₁ * p ≤ c₂ * (p - 1)) :
    c₁ * sigma 1 (p ^ k) < c₂ * p ^ k := by
  have hgeom : (p - 1) * sigma 1 (p ^ k) < p * p ^ k := by
    rw [mul_comm (p - 1), mul_comm p, sigma_one_apply_prime_pow hp]
    have h := geom_sum_mul_add (p - 1) (k + 1)
    rw [Nat.sub_add_cancel hp.one_lt.le, pow_succ] at h
    omega
  have h1 : (p - 1) * (c₁ * sigma 1 (p ^ k)) < (p - 1) * (c₂ * p ^ k) := by
    calc
      (p - 1) * (c₁ * sigma 1 (p ^ k))
          = c₁ * ((p - 1) * sigma 1 (p ^ k)) := by ring
      _ < c₁ * (p * p ^ k) := Nat.mul_lt_mul_of_pos_left hgeom hc₁
      _ = (c₁ * p) * p ^ k := by ring
      _ ≤ (c₂ * (p - 1)) * p ^ k := Nat.mul_le_mul_right (p ^ k) hcoef
      _ = (p - 1) * (c₂ * p ^ k) := by ring
  exact Nat.lt_of_mul_lt_mul_left h1

private lemma sq_prod_ratio_le {u₀ P Q c₁ c₂ : ℕ} (hc₁ : 0 < c₁)
    (hgap_prod : 3 * u₀ * P < (3 * u₀ + 4) * Q)
    (hcoef : c₁ * (3 * u₀ + 4) ≤ c₂ * (3 * u₀)) :
    c₁ * P ≤ c₂ * Q := by
  have h1 : (3 * u₀) * (c₁ * P) < (3 * u₀) * (c₂ * Q) := by
    calc
      (3 * u₀) * (c₁ * P) = c₁ * (3 * u₀ * P) := by ring
      _ < c₁ * ((3 * u₀ + 4) * Q) := Nat.mul_lt_mul_of_pos_left hgap_prod hc₁
      _ = (c₁ * (3 * u₀ + 4)) * Q := by ring
      _ ≤ (c₂ * (3 * u₀)) * Q := Nat.mul_le_mul_right Q hcoef
      _ = (3 * u₀) * (c₂ * Q) := by ring
  exact (Nat.lt_of_mul_lt_mul_left h1).le

private lemma abundancy_contradiction4 {N σ₁ σ₂ σ₃ P p₁ p₂ p₃ Q c₁ d₁ c₂ d₂ c₃ d₃ cS dS : ℕ}
    (_hN_pos : 0 < N)
    (hσ_eq : σ₁ * σ₂ * σ₃ * P = 2 * N)
    (hN_eq : p₁ * p₂ * p₃ * Q = N)
    (h1_pos : 0 < c₁ * σ₁) (h1 : c₁ * σ₁ ≤ d₁ * p₁)
    (h2 : c₂ * σ₂ < d₂ * p₂)
    (h3_pos : 0 < c₃ * σ₃) (h3 : c₃ * σ₃ ≤ d₃ * p₃)
    (hS_pos : 0 < cS * P) (hS : cS * P ≤ dS * Q)
    (hineq : d₁ * d₂ * d₃ * dS ≤ 2 * (c₁ * c₂ * c₃ * cS)) : False := by
  have hd1p1_pos : 0 < d₁ * p₁ := lt_of_lt_of_le h1_pos h1
  have h12 : (c₁ * σ₁) * (c₂ * σ₂) < (d₁ * p₁) * (d₂ * p₂) :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ h1) (Nat.mul_lt_mul_of_pos_left h2 hd1p1_pos)
  have h123 : ((c₁ * σ₁) * (c₂ * σ₂)) * (c₃ * σ₃) < ((d₁ * p₁) * (d₂ * p₂)) * (d₃ * p₃) :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h12 h3_pos) (Nat.mul_le_mul_left _ h3)
  have hprod : (((c₁ * σ₁) * (c₂ * σ₂)) * (c₃ * σ₃)) * (cS * P) <
      (((d₁ * p₁) * (d₂ * p₂)) * (d₃ * p₃)) * (dS * Q) :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h123 hS_pos) (Nat.mul_le_mul_left _ hS)
  have hLHS : (((c₁ * σ₁) * (c₂ * σ₂)) * (c₃ * σ₃)) * (cS * P) =
      (c₁ * c₂ * c₃ * cS) * (σ₁ * σ₂ * σ₃ * P) := by ring
  have hRHS : (((d₁ * p₁) * (d₂ * p₂)) * (d₃ * p₃)) * (dS * Q) =
      (d₁ * d₂ * d₃ * dS) * (p₁ * p₂ * p₃ * Q) := by ring
  rw [hLHS, hRHS, hσ_eq, hN_eq] at hprod
  have hle : (d₁ * d₂ * d₃ * dS) * N ≤ (2 * (c₁ * c₂ * c₃ * cS)) * N :=
    Nat.mul_le_mul_right N hineq
  have hlt : (2 * (c₁ * c₂ * c₃ * cS)) * N < (2 * (c₁ * c₂ * c₃ * cS)) * N := by
    calc
      (2 * (c₁ * c₂ * c₃ * cS)) * N = (c₁ * c₂ * c₃ * cS) * (2 * N) := by ring
      _ < (d₁ * d₂ * d₃ * dS) * N := hprod
      _ ≤ (2 * (c₁ * c₂ * c₃ * cS)) * N := hle
  exact lt_irrefl _ hlt

private lemma abundancy_contradiction5
    {N σ₁ σ₂ σ₃ Pev Pod p₁ p₂ p₃ Qev Qod
      c₁ d₁ c₂ d₂ c₃ d₃ cev dev cod dod : ℕ}
    (_hN_pos : 0 < N)
    (hσ_eq : σ₁ * σ₂ * σ₃ * Pev * Pod = 2 * N)
    (hN_eq : p₁ * p₂ * p₃ * Qev * Qod = N)
    (h1_pos : 0 < c₁ * σ₁) (h1 : c₁ * σ₁ ≤ d₁ * p₁)
    (h2_pos : 0 < c₂ * σ₂) (h2 : c₂ * σ₂ ≤ d₂ * p₂)
    (h3 : c₃ * σ₃ < d₃ * p₃)
    (hpev_pos : 0 < cev * Pev) (hpev : cev * Pev ≤ dev * Qev)
    (hpod_pos : 0 < cod * Pod) (hpod : cod * Pod ≤ dod * Qod)
    (hineq : d₁ * d₂ * d₃ * dev * dod ≤ 2 * (c₁ * c₂ * c₃ * cev * cod)) : False := by
  have h12_pos : 0 < (d₁ * p₁) * (d₂ * p₂) :=
    Nat.mul_pos (lt_of_lt_of_le h1_pos h1) (lt_of_lt_of_le h2_pos h2)
  have h12 : (c₁ * σ₁) * (c₂ * σ₂) ≤ (d₁ * p₁) * (d₂ * p₂) :=
    Nat.mul_le_mul h1 h2
  have h123 : ((c₁ * σ₁) * (c₂ * σ₂)) * (c₃ * σ₃) < ((d₁ * p₁) * (d₂ * p₂)) * (d₃ * p₃) :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ h12) (Nat.mul_lt_mul_of_pos_left h3 h12_pos)
  have h1234 : (((c₁ * σ₁) * (c₂ * σ₂)) * (c₃ * σ₃)) * (cev * Pev) <
      (((d₁ * p₁) * (d₂ * p₂)) * (d₃ * p₃)) * (dev * Qev) :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h123 hpev_pos) (Nat.mul_le_mul_left _ hpev)
  have hprod : ((((c₁ * σ₁) * (c₂ * σ₂)) * (c₃ * σ₃)) * (cev * Pev)) * (cod * Pod) <
      ((((d₁ * p₁) * (d₂ * p₂)) * (d₃ * p₃)) * (dev * Qev)) * (dod * Qod) :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h1234 hpod_pos) (Nat.mul_le_mul_left _ hpod)
  have hLHS : ((((c₁ * σ₁) * (c₂ * σ₂)) * (c₃ * σ₃)) * (cev * Pev)) * (cod * Pod) =
      (c₁ * c₂ * c₃ * cev * cod) * (σ₁ * σ₂ * σ₃ * Pev * Pod) := by ring
  have hRHS : ((((d₁ * p₁) * (d₂ * p₂)) * (d₃ * p₃)) * (dev * Qev)) * (dod * Qod) =
      (d₁ * d₂ * d₃ * dev * dod) * (p₁ * p₂ * p₃ * Qev * Qod) := by ring
  rw [hLHS, hRHS, hσ_eq, hN_eq] at hprod
  have hle : (d₁ * d₂ * d₃ * dev * dod) * N ≤ (2 * (c₁ * c₂ * c₃ * cev * cod)) * N :=
    Nat.mul_le_mul_right N hineq
  have hlt : (2 * (c₁ * c₂ * c₃ * cev * cod)) * N < (2 * (c₁ * c₂ * c₃ * cev * cod)) * N := by
    calc
      (2 * (c₁ * c₂ * c₃ * cev * cod)) * N = (c₁ * c₂ * c₃ * cev * cod) * (2 * N) := by ring
      _ < (d₁ * d₂ * d₃ * dev * dod) * N := hprod
      _ ≤ (2 * (c₁ * c₂ * c₃ * cev * cod)) * N := hle
  exact lt_irrefl _ hlt

private lemma eq_pow_of_primeFactors_subset {n p : ℕ} (hn : n ≠ 0) (hsub : n.primeFactors ⊆ {p}) :
    n = p ^ n.factorization p := by
  have hprod := Nat.prod_primeFactors_pow_factorization hn
  by_cases hp : p ∈ n.primeFactors
  · have heq : n.primeFactors = {p} :=
      Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hp)
    rw [heq, Finset.prod_singleton] at hprod
    exact hprod
  · have heq : n.primeFactors = ∅ := by
      ext x
      simp only [Finset.notMem_empty, iff_false]
      intro hx
      exact hp (Finset.mem_singleton.mp (hsub hx) ▸ hx)
    have hfz : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    rw [heq, Finset.prod_empty] at hprod
    rw [hfz, pow_zero]
    exact hprod

private lemma eq_mul_pow_of_primeFactors_subset_pair {n p r : ℕ} (hn : n ≠ 0) (hpr : p ≠ r)
    (hsub : n.primeFactors ⊆ {p, r}) :
    n = p ^ n.factorization p * r ^ n.factorization r := by
  have hprod := Nat.prod_primeFactors_pow_factorization hn
  have hmul : (∏ x ∈ n.primeFactors, x ^ n.factorization x) =
      ∏ x ∈ ({p, r} : Finset ℕ), x ^ n.factorization x := by
    apply Finset.prod_subset hsub
    intro x _ hx_not
    have hfz : n.factorization x = 0 := Finsupp.notMem_support_iff.mp hx_not
    rw [hfz, pow_zero]
  conv_lhs => rw [hprod, hmul, Finset.prod_pair hpr]

private def evenIdx : List ℕ → List ℕ
  | [] => []
  | [x] => [x]
  | x :: _ :: xs => x :: evenIdx xs

private def oddIdx : List ℕ → List ℕ
  | [] => []
  | [_] => []
  | _ :: y :: xs => y :: oddIdx xs

private lemma prod_map_evenIdx_mul_oddIdx (f : ℕ → ℕ) :
    ∀ L : List ℕ, (L.map f).prod = ((evenIdx L).map f).prod * ((oddIdx L).map f).prod
  | [] => by simp [evenIdx, oddIdx]
  | [x] => by simp [evenIdx, oddIdx]
  | x :: y :: xs => by
      simp only [evenIdx, oddIdx, List.map_cons, List.prod_cons]
      rw [prod_map_evenIdx_mul_oddIdx f xs]
      ring

private lemma mem_evenIdx_subset : ∀ {L : List ℕ} {x : ℕ}, x ∈ evenIdx L → x ∈ L
  | [], _ => by simp [evenIdx]
  | [_], _ => by simp [evenIdx]
  | _ :: _ :: xs, _ => by
      simp only [evenIdx, List.mem_cons]
      rintro (rfl | hx)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (mem_evenIdx_subset hx))

private lemma mem_oddIdx_subset : ∀ {L : List ℕ} {x : ℕ}, x ∈ oddIdx L → x ∈ L
  | [], _ => by simp [oddIdx]
  | [_], _ => by simp [oddIdx]
  | _ :: _ :: xs, _ => by
      simp only [oddIdx, List.mem_cons]
      rintro (rfl | hx)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (mem_oddIdx_subset hx))

private lemma evenIdx_head?_cons (a : ℕ) (t : List ℕ) : (evenIdx (a :: t)).head? = some a := by
  cases t with
  | nil => simp [evenIdx]
  | cons _ _ => simp [evenIdx]

private lemma oddIdx_head_gt {L : List ℕ} {x y₀ : ℕ}
    (hchain : L.IsChain (· < ·)) (hge : ∀ u ∈ L, y₀ ≤ u)
    (hx : x ∈ (oddIdx L).head?) : y₀ < x ∧ x ∈ L := by
  cases L with
  | nil => simp [oddIdx] at hx
  | cons a t =>
      cases t with
      | nil => simp [oddIdx] at hx
      | cons b xs =>
          simp only [oddIdx, List.head?_cons, Option.mem_def, Option.some.injEq] at hx
          subst hx
          have ha : y₀ ≤ a := hge a (by simp)
          have hlt : a < b := hchain.rel
          exact ⟨by omega, by simp⟩

private lemma evenIdx_isChain {R : ℕ → ℕ → Prop} :
    ∀ L : List ℕ, L.IsChain (· < ·) →
      (∀ a b c, a ∈ L → b ∈ L → c ∈ L → a < b → b < c → R a c) →
      (evenIdx L).IsChain R
  | [], _, _ => by simp [evenIdx]
  | [_], _, _ => by simp [evenIdx]
  | [_, _], _, _ => by simp [evenIdx]
  | x :: y :: z :: xs, hchain, hR => by
      have htail : (z :: xs).IsChain (· < ·) := hchain.tail.tail
      have hR' : ∀ a b c, a ∈ z :: xs → b ∈ z :: xs → c ∈ z :: xs → a < b → b < c → R a c :=
        fun a b c ha hb hc hab hbc =>
          hR a b c (by simp [ha]) (by simp [hb]) (by simp [hc]) hab hbc
      have ih := evenIdx_isChain (z :: xs) htail hR'
      have hxy : x < y := hchain.rel
      have hyz : y < z := hchain.tail.rel
      have hxz : R x z := hR x y z (by simp) (by simp) (by simp) hxy hyz
      rw [evenIdx]
      refine ih.cons ?_
      intro v hv
      rw [evenIdx_head?_cons] at hv
      injection hv with hv
      subst hv
      exact hxz

private lemma oddIdx_isChain {R : ℕ → ℕ → Prop} :
    ∀ L : List ℕ, L.IsChain (· < ·) →
      (∀ a b c, a ∈ L → b ∈ L → c ∈ L → a < b → b < c → R a c) →
      (oddIdx L).IsChain R
  | [], _, _ => by simp [oddIdx]
  | [_], _, _ => by simp [oddIdx]
  | [_, _], _, _ => by simp [oddIdx]
  | [_, _, _], _, _ => by simp [oddIdx]
  | x :: y :: z :: w :: xs, hchain, hR => by
      have htail : (z :: w :: xs).IsChain (· < ·) := hchain.tail.tail
      have hR' : ∀ a b c, a ∈ z :: w :: xs → b ∈ z :: w :: xs → c ∈ z :: w :: xs →
          a < b → b < c → R a c :=
        fun a b c ha hb hc hab hbc =>
          hR a b c (by simp [ha]) (by simp [hb]) (by simp [hc]) hab hbc
      have ih := oddIdx_isChain (z :: w :: xs) htail hR'
      have hyz : y < z := hchain.tail.rel
      have hzw : z < w := hchain.tail.tail.rel
      have hyw : R y w := hR y z w (by simp) (by simp) (by simp) hyz hzw
      simp only [oddIdx] at ih ⊢
      refine ih.cons ?_
      intro v hv
      simp only [List.head?_cons] at hv
      injection hv with hv
      subst hv
      exact hyw

private lemma smooth_pair_squareSourcesTwo_bounds_split
    {S₂ : Finset ℕ} {p₁ p₂ y_ev y_od : ℕ}
    (hp₁ : p₁.Prime) (hp₁_odd : Odd p₁) (hp₁3 : p₁ % 3 = 1)
    (hp₂ : p₂.Prime) (hp₂_odd : Odd p₂) (hp₂3 : p₂ % 3 = 1)
    (hy_ev : 5 ≤ y_ev) (hy_od : 5 ≤ y_od)
    (hS₂_odd : ∀ u ∈ S₂, Odd u)
    (hS₂_3 : ∀ u ∈ S₂, u % 3 = 2)
    (hS₂_5 : ∀ u ∈ S₂, 5 ≤ u)
    (hS₂_ev : ∀ u ∈ S₂, y_ev ≤ u)
    (hS₂_od : ∀ x ∈ (oddIdx S₂.sort).head?, y_od ≤ x)
    (hS₂_pow : ∀ u ∈ S₂,
      u ^ 2 + u + 1 = p₁ ^ (u ^ 2 + u + 1).factorization p₁ * p₂ ^ (u ^ 2 + u + 1).factorization p₂) :
    ∃ P_ev_num P_ev_den P_od_num P_od_den : ℕ,
      (∏ u ∈ S₂, (u ^ 2 + u + 1)) = P_ev_num * P_od_num ∧
      (∏ u ∈ S₂, u ^ 2) = P_ev_den * P_od_den ∧
      0 < P_ev_num ∧ 0 < P_od_num ∧
      2 * y_ev * P_ev_num ≤ (2 * y_ev + 5) * P_ev_den ∧
      2 * y_od * P_od_num ≤ (2 * y_od + 5) * P_od_den := by
  let L := S₂.sort
  have hL_chain_lt : L.IsChain (· < ·) := (Finset.sortedLT_sort S₂).isChain
  have hL_mem : ∀ x, x ∈ L ↔ x ∈ S₂ := fun x => Finset.mem_sort (· ≤ ·)
  have hprod_sort : ∀ f : ℕ → ℕ, (∏ u ∈ S₂, f u) = (L.map f).prod := by
    intro f
    rw [← Finset.prod_map_toList S₂ f]
    exact ((Finset.sort_perm_toList S₂ (· ≤ ·)).map f).prod_eq.symm
  let P_ev_num := ((evenIdx L).map (fun u => u ^ 2 + u + 1)).prod
  let P_ev_den := ((evenIdx L).map (fun u => u ^ 2)).prod
  let P_od_num := ((oddIdx L).map (fun u => u ^ 2 + u + 1)).prod
  let P_od_den := ((oddIdx L).map (fun u => u ^ 2)).prod
  refine ⟨P_ev_num, P_ev_den, P_od_num, P_od_den, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hprod_sort]
    exact prod_map_evenIdx_mul_oddIdx (fun u => u ^ 2 + u + 1) L
  · rw [hprod_sort]
    exact prod_map_evenIdx_mul_oddIdx (fun u => u ^ 2) L
  · exact List.prod_pos fun y hy => by
      rcases List.mem_map.mp hy with ⟨u, _, rfl⟩
      positivity
  · exact List.prod_pos fun y hy => by
      rcases List.mem_map.mp hy with ⟨u, _, rfl⟩
      positivity
  · have hstep_triple : ∀ a b c, a ∈ L → b ∈ L → c ∈ L → a < b → b < c → 5 * a + 3 ≤ 2 * c := by
      intro a b c ha hb hc hab hbc
      rw [hL_mem] at ha hb hc
      exact (two_prime_smooth_sq_add_self_add_one_step
        hp₁ hp₁_odd hp₁3 hp₂ hp₂_odd hp₂3
        hab hbc (hS₂_odd a ha) (hS₂_odd b hb) (hS₂_odd c hc)
        (hS₂_5 a ha) (hS₂_3 a ha) (hS₂_3 b hb) (hS₂_3 c hc)
        (hS₂_pow a ha) (hS₂_pow b hb) (hS₂_pow c hc)).2
    have hev_chain : (evenIdx L).IsChain (fun x y => 5 * x + 3 ≤ 2 * y) :=
      evenIdx_isChain L hL_chain_lt hstep_triple
    have hev_ge5 : ∀ x ∈ evenIdx L, 5 ≤ x := fun x hx =>
      hS₂_5 x ((hL_mem x).mp (mem_evenIdx_subset hx))
    have hev_head : ∀ x ∈ (evenIdx L).head?, y_ev ≤ x := fun x hx =>
      hS₂_ev x ((hL_mem x).mp (mem_evenIdx_subset (List.mem_of_head? hx)))
    exact prod_sq_abundancy_le_of_five_halves_step (evenIdx L) hev_chain hev_ge5 y_ev hy_ev hev_head
  · have hstep_triple : ∀ a b c, a ∈ L → b ∈ L → c ∈ L → a < b → b < c → 5 * a + 3 ≤ 2 * c := by
      intro a b c ha hb hc hab hbc
      rw [hL_mem] at ha hb hc
      exact (two_prime_smooth_sq_add_self_add_one_step
        hp₁ hp₁_odd hp₁3 hp₂ hp₂_odd hp₂3
        hab hbc (hS₂_odd a ha) (hS₂_odd b hb) (hS₂_odd c hc)
        (hS₂_5 a ha) (hS₂_3 a ha) (hS₂_3 b hb) (hS₂_3 c hc)
        (hS₂_pow a ha) (hS₂_pow b hb) (hS₂_pow c hc)).2
    have hod_chain : (oddIdx L).IsChain (fun x y => 5 * x + 3 ≤ 2 * y) :=
      oddIdx_isChain L hL_chain_lt hstep_triple
    have hod_ge5 : ∀ x ∈ oddIdx L, 5 ≤ x := fun x hx =>
      hS₂_5 x ((hL_mem x).mp (mem_oddIdx_subset hx))
    exact prod_sq_abundancy_le_of_five_halves_step (oddIdx L) hod_chain hod_ge5 y_od hy_od hS₂_od

private lemma not_sq_add_self_add_one_between {s c u : ℕ}
    (h1 : s ^ 2 + s + 1 < c) (h2 : c < (s + 1) ^ 2 + (s + 1) + 1) :
    u ^ 2 + u + 1 ≠ c := by
  intro heq
  rcases le_or_gt u s with hle | hgt
  · have : u ^ 2 + u + 1 ≤ s ^ 2 + s + 1 := by nlinarith
    omega
  · have : (s + 1) ^ 2 + (s + 1) + 1 ≤ u ^ 2 + u + 1 := by nlinarith
    omega

private lemma ne_thirteen_pow_of_lt_47 {u k : ℕ} (hu5 : 5 ≤ u) (hk : k < 3) :
    u ^ 2 + u + 1 ≠ 13 ^ k := by
  interval_cases k
  · nlinarith
  · nlinarith
  · exact not_sq_add_self_add_one_between (s := 12) (by decide) (by decide)

private lemma not_dvd_seven_thirteen_aux :
    ∀ k ∈ Finset.range 32, ¬ ((6 * k + 5) ^ 2 + (6 * k + 5) + 1 ∣ 480024727) := by
  decide +kernel

private lemma not_dvd_seven_thirteen_of_lt_197 {u : ℕ}
    (hu_lt : u < 197) (hu5 : 5 ≤ u) (hu6 : u % 6 = 5) :
    ¬ (u ^ 2 + u + 1 ∣ 7 ^ 5 * 13 ^ 4) := by
  have hk_lt : (u - 5) / 6 < 32 := by omega
  have hu_eq : u = 6 * ((u - 5) / 6) + 5 := by omega
  have hM : 7 ^ 5 * 13 ^ 4 = 480024727 := by norm_num
  rw [hu_eq, hM]
  exact not_dvd_seven_thirteen_aux ((u - 5) / 6) (Finset.mem_range.mpr hk_lt)

private lemma not_five_dvd_sq_add_self_add_one (x : ℕ) : ¬ 5 ∣ x ^ 2 + x + 1 := by
  have hmod : ∀ r : Fin 5, (r.1 ^ 2 + r.1 + 1) % 5 ≠ 0 := by decide
  intro hd
  have h0 : (x ^ 2 + x + 1) % 5 = 0 := Nat.mod_eq_zero_of_dvd hd
  have hr : ((x % 5) ^ 2 + (x % 5) + 1) % 5 = 0 := by
    simpa [Nat.add_mod, Nat.pow_mod] using h0
  exact hmod ⟨x % 5, Nat.mod_lt x (by decide)⟩ hr

private lemma not_five_dvd_sigma_thirteen_one_mod_four {a : ℕ} (ha : a % 4 = 1) :
    ¬ 5 ∣ sigma 1 (13 ^ a) := by
  rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 13),
    dvd_geom_sum_iff_remainder (t := 4) (by decide)]
  have hmod : (a + 1) % 4 = 2 := by omega
  rw [hmod]
  norm_num [Finset.sum_range_succ]

private lemma two_prime_abundancy_contradiction
    {N q r₀ c₂ d₂ c₃ d₃ y_ev y_od : ℕ}
    (hN : N.Perfect) (hq_prime : q.Prime) (hq_odd : Odd q) (hq3 : q % 3 = 1)
    (hr₀_prime : r₀.Prime) (hr₀_odd : Odd r₀) (hr₀3 : r₀ % 3 = 1)
    (hr₀_ne_q : r₀ ≠ q)
    (h3_eq2 : N.factorization 3 = 2)
    (hpart : N.primeFactors = insert 3 (insert q (insert r₀ (squareSourcesTwo N))))
    (h3_not_ins : (3 : ℕ) ∉ insert q (insert r₀ (squareSourcesTwo N)))
    (hq_not_ins : q ∉ insert r₀ (squareSourcesTwo N))
    (hr₀_not_S₂ : r₀ ∉ squareSourcesTwo N)
    (hS₂_prop : ∀ u ∈ squareSourcesTwo N,
      u.Prime ∧ Odd u ∧ N.factorization u = 2 ∧ u % 3 = 2 ∧ 5 ≤ u ∧
      sigma 1 (u ^ N.factorization u) = u ^ 2 + u + 1 ∧
      (u ^ 2 + u + 1).primeFactors ⊆ N.primeFactors.filter (fun w => w % 3 = 1))
    (hT_pair : N.primeFactors.filter (fun w => w % 3 = 1) ⊆ {q, r₀})
    (hc₂ : 0 < c₂) (hq_ratio : c₂ * sigma 1 (q ^ N.factorization q) ≤ d₂ * q ^ N.factorization q)
    (hr₀_ratio : c₃ * sigma 1 (r₀ ^ N.factorization r₀) < d₃ * r₀ ^ N.factorization r₀)
    (hy_ev : 5 ≤ y_ev) (hy_od : 5 ≤ y_od)
    (hS₂_ev : ∀ u ∈ squareSourcesTwo N, y_ev ≤ u)
    (hS₂_od : ∀ x ∈ (oddIdx (squareSourcesTwo N).sort).head?, y_od ≤ x)
    (hineq : 13 * d₂ * d₃ * (2 * y_ev + 5) * (2 * y_od + 5) ≤
      2 * (9 * c₂ * c₃ * (2 * y_ev) * (2 * y_od))) : False := by
  let S₂ := squareSourcesTwo N
  have hS₂_pow : ∀ u ∈ S₂,
      u ^ 2 + u + 1 = q ^ (u ^ 2 + u + 1).factorization q * r₀ ^ (u ^ 2 + u + 1).factorization r₀ := by
    intro u hu
    exact eq_mul_pow_of_primeFactors_subset_pair (by positivity) hr₀_ne_q.symm
      ((hS₂_prop u hu).2.2.2.2.2.2.trans hT_pair)
  obtain ⟨P_ev_num, P_ev_den, P_od_num, P_od_den,
    hP_prod, hQ_prod, hP_ev_pos, hP_od_pos, hP_ev_bd, hP_od_bd⟩ :=
    smooth_pair_squareSourcesTwo_bounds_split hq_prime hq_odd hq3 hr₀_prime hr₀_odd hr₀3
      hy_ev hy_od (fun u hu => (hS₂_prop u hu).2.1)
      (fun u hu => (hS₂_prop u hu).2.2.2.1)
      (fun u hu => (hS₂_prop u hu).2.2.2.2.1)
      hS₂_ev hS₂_od hS₂_pow
  let P_S := ∏ u ∈ S₂, (u ^ 2 + u + 1)
  let Q_S := ∏ u ∈ S₂, u ^ 2
  have hN_eq : 3 ^ 2 * q ^ N.factorization q * r₀ ^ N.factorization r₀ * Q_S = N := by
    have hfac := Nat.prod_primeFactors_pow_factorization hN.2.ne'
    rw [hpart, Finset.prod_insert h3_not_ins, Finset.prod_insert hq_not_ins,
      Finset.prod_insert hr₀_not_S₂, h3_eq2] at hfac
    have hS_prod : (∏ u ∈ S₂, u ^ N.factorization u) = Q_S :=
      Finset.prod_congr rfl fun u hu => by rw [(hS₂_prop u hu).2.2.1]
    rw [hS_prod] at hfac
    calc
      3 ^ 2 * q ^ N.factorization q * r₀ ^ N.factorization r₀ * Q_S
          = 3 ^ 2 * (q ^ N.factorization q * (r₀ ^ N.factorization r₀ * Q_S)) := by ring
      _ = N := hfac.symm
  have hσ_eq : sigma 1 (3 ^ 2) * sigma 1 (q ^ N.factorization q) *
      sigma 1 (r₀ ^ N.factorization r₀) * P_S = 2 * N := by
    have hσN : sigma 1 N = 2 * N :=
      (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN)
    have hmul : sigma 1 N = ∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p) :=
      isMultiplicative_sigma.multiplicative_factorization (sigma 1) hN.2.ne'
    rw [hσN, hpart, Finset.prod_insert h3_not_ins, Finset.prod_insert hq_not_ins,
      Finset.prod_insert hr₀_not_S₂, h3_eq2] at hmul
    have hS_prod : (∏ u ∈ S₂, sigma 1 (u ^ N.factorization u)) = P_S :=
      Finset.prod_congr rfl fun u hu => (hS₂_prop u hu).2.2.2.2.2.1
    rw [hS_prod] at hmul
    calc
      sigma 1 (3 ^ 2) * sigma 1 (q ^ N.factorization q) * sigma 1 (r₀ ^ N.factorization r₀) * P_S
          = sigma 1 (3 ^ 2) * (sigma 1 (q ^ N.factorization q) *
              (sigma 1 (r₀ ^ N.factorization r₀) * P_S)) := by ring
      _ = 2 * N := hmul.symm
  dsimp only [P_S] at hσ_eq
  dsimp only [Q_S] at hN_eq
  rw [hP_prod] at hσ_eq
  rw [hQ_prod] at hN_eq
  have hσ_eq' : sigma 1 (3 ^ 2) * sigma 1 (q ^ N.factorization q) *
      sigma 1 (r₀ ^ N.factorization r₀) * P_ev_num * P_od_num = 2 * N := by
    calc
      sigma 1 (3 ^ 2) * sigma 1 (q ^ N.factorization q) *
          sigma 1 (r₀ ^ N.factorization r₀) * P_ev_num * P_od_num
          = sigma 1 (3 ^ 2) * sigma 1 (q ^ N.factorization q) *
              sigma 1 (r₀ ^ N.factorization r₀) * (P_ev_num * P_od_num) := by ring
      _ = 2 * N := hσ_eq
  have hN_eq' : 3 ^ 2 * q ^ N.factorization q * r₀ ^ N.factorization r₀ * P_ev_den * P_od_den = N := by
    calc
      3 ^ 2 * q ^ N.factorization q * r₀ ^ N.factorization r₀ * P_ev_den * P_od_den
          = 3 ^ 2 * q ^ N.factorization q * r₀ ^ N.factorization r₀ * (P_ev_den * P_od_den) := by ring
      _ = N := hN_eq
  have h3_ratio : 9 * sigma 1 (3 ^ 2) ≤ 13 * 3 ^ 2 := by
    have h13 : sigma 1 (3 ^ 2) = 13 := by
      rw [sigma_one_apply_prime_pow Nat.prime_three]
      decide
    rw [h13]
    norm_num
  exact abundancy_contradiction5 hN.2 hσ_eq' hN_eq'
    (Nat.mul_pos (by decide) (sigma_pos _ _ (by decide))) h3_ratio
    (Nat.mul_pos hc₂ (sigma_pos _ _ (pow_ne_zero _ hq_prime.ne_zero))) hq_ratio
    hr₀_ratio
    (Nat.mul_pos (by omega) hP_ev_pos) hP_ev_bd
    (Nat.mul_pos (by omega) hP_od_pos) hP_od_bd
    hineq

private lemma restrained_S2_ge_197 {N : ℕ}
    (hS₂_prop : ∀ u ∈ squareSourcesTwo N,
      u.Prime ∧ Odd u ∧ N.factorization u = 2 ∧ u % 3 = 2 ∧ 5 ≤ u ∧
      sigma 1 (u ^ N.factorization u) = u ^ 2 + u + 1 ∧
      (u ^ 2 + u + 1).primeFactors ⊆ N.primeFactors.filter (fun w => w % 3 = 1))
    (hT_sub : N.primeFactors.filter (fun w => w % 3 = 1) ⊆ {13, 7}) :
    ∀ u ∈ squareSourcesTwo N, 197 ≤ u := by
  intro u hu
  by_contra! hu_lt
  have hu_odd := (hS₂_prop u hu).2.1
  have hu3 := (hS₂_prop u hu).2.2.2.1
  have hu5 := (hS₂_prop u hu).2.2.2.2.1
  have hu_mod2 := Nat.odd_iff.mp hu_odd
  have hu6 : u % 6 = 5 := by omega
  have hpow : u ^ 2 + u + 1 =
      7 ^ (u ^ 2 + u + 1).factorization 7 * 13 ^ (u ^ 2 + u + 1).factorization 13 :=
    eq_mul_pow_of_primeFactors_subset_pair (by positivity) (by decide : (7 : ℕ) ≠ 13)
      ((hS₂_prop u hu).2.2.2.2.2.2.trans (by simpa [Finset.pair_comm] using hT_sub))
  set α := (u ^ 2 + u + 1).factorization 7
  set β := (u ^ 2 + u + 1).factorization 13
  have hval_lt : u ^ 2 + u + 1 ≤ 196 ^ 2 + 196 + 1 := by nlinarith
  have hα_lt : 7 ^ α < 7 ^ 6 := by
    calc
      7 ^ α ≤ 7 ^ α * 13 ^ β := Nat.le_mul_of_pos_right _ (by positivity)
      _ = u ^ 2 + u + 1 := hpow.symm
      _ ≤ 196 ^ 2 + 196 + 1 := hval_lt
      _ < 7 ^ 6 := by norm_num
  have hβ_lt : 13 ^ β < 13 ^ 5 := by
    calc
      13 ^ β ≤ 7 ^ α * 13 ^ β := Nat.le_mul_of_pos_left _ (by positivity)
      _ = u ^ 2 + u + 1 := hpow.symm
      _ ≤ 196 ^ 2 + 196 + 1 := hval_lt
      _ < 13 ^ 5 := by norm_num
  have hα5 : α ≤ 5 := Nat.lt_succ_iff.mp ((Nat.pow_lt_pow_iff_right (by decide : 1 < 7)).mp hα_lt)
  have hβ4 : β ≤ 4 := Nat.lt_succ_iff.mp ((Nat.pow_lt_pow_iff_right (by decide : 1 < 13)).mp hβ_lt)
  have hdvd : u ^ 2 + u + 1 ∣ 7 ^ 5 * 13 ^ 4 := by
    rw [hpow]
    exact Nat.mul_dvd_mul (pow_dvd_pow 7 hα5) (pow_dvd_pow 13 hβ4)
  exact not_dvd_seven_thirteen_of_lt_197 hu_lt hu5 hu6 hdvd

private lemma restrained_S2_od_ge_198 {S₂ : Finset ℕ}
    (hS₂_ge197 : ∀ u ∈ S₂, 197 ≤ u) :
    ∀ x ∈ (oddIdx S₂.sort).head?, 198 ≤ x := by
  intro x hx
  have hchain : S₂.sort.IsChain (· < ·) := (Finset.sortedLT_sort S₂).isChain
  have hge_sort : ∀ u ∈ S₂.sort, 197 ≤ u := fun u hu =>
    hS₂_ge197 u ((Finset.mem_sort (· ≤ ·)).mp hu)
  have hgt := (oddIdx_head_gt hchain hge_sort hx).1
  omega

private lemma restrained_exact_nine_case_q13_exp1
    {N r₀ : ℕ} (hN : N.Perfect)
    (h3_eq2 : N.factorization 3 = 2)
    (hpart : N.primeFactors = insert 3 (insert 13 (insert r₀ (squareSourcesTwo N))))
    (h3_not_ins : (3 : ℕ) ∉ insert 13 (insert r₀ (squareSourcesTwo N)))
    (h13_not_ins : (13 : ℕ) ∉ insert r₀ (squareSourcesTwo N))
    (hr₀_not_S₂ : r₀ ∉ squareSourcesTwo N)
    (hS₂_prop : ∀ u ∈ squareSourcesTwo N,
      u.Prime ∧ Odd u ∧ N.factorization u = 2 ∧ u % 3 = 2 ∧ 5 ≤ u ∧
      sigma 1 (u ^ N.factorization u) = u ^ 2 + u + 1 ∧
      (u ^ 2 + u + 1).primeFactors ⊆ N.primeFactors.filter (fun w => w % 3 = 1))
    (hT_sub : N.primeFactors.filter (fun w => w % 3 = 1) ⊆ {13, r₀})
    (h13_exp1 : N.factorization 13 = 1) : False := by
  have h7_dvd : 7 ∣ N := by
    apply seven_dvd_of_exact_thirteen_pow hN (e := 1)
    · simpa using (by decide : Nat.Prime 13).pow_dvd_iff_le_factorization hN.2.ne' |>.mpr
        (by omega : 1 ≤ N.factorization 13)
    · intro hpow
      have hle2 := (by decide : Nat.Prime 13).pow_dvd_iff_le_factorization hN.2.ne' |>.mp
        (by simpa using hpow : 13 ^ 2 ∣ N)
      omega
    · decide
  have h7_mem : 7 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, h7_dvd, hN.2.ne'⟩
  have h7_T : 7 ∈ N.primeFactors.filter (fun w => w % 3 = 1) := Finset.mem_filter.mpr ⟨h7_mem, by decide⟩
  have hr₀_eq7 : r₀ = 7 := by
    have hmem := hT_sub h7_T
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  subst hr₀_eq7
  have hS₂_ge197 := restrained_S2_ge_197 hS₂_prop hT_sub
  have hS₂_od := restrained_S2_od_ge_198 hS₂_ge197
  have h13_ratio : 13 * sigma 1 (13 ^ N.factorization 13) ≤ 14 * 13 ^ N.factorization 13 := by
    rw [h13_exp1, sigma_one_apply_prime_pow (by decide : Nat.Prime 13)]
    norm_num [Finset.sum_range_succ]
  have h7_ratio : 6 * sigma 1 (7 ^ N.factorization 7) < 7 * 7 ^ N.factorization 7 :=
    sigma_prime_pow_ratio_lt (by decide : Nat.Prime 7) (by decide) (by decide)
  exact two_prime_abundancy_contradiction hN (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) h3_eq2 hpart h3_not_ins h13_not_ins
    hr₀_not_S₂ hS₂_prop hT_sub (by decide) h13_ratio h7_ratio (by decide) (by decide)
    hS₂_ge197 hS₂_od (by norm_num)

private lemma restrained_exact_nine_case_q13_r0_mod2
    {N r₀ : ℕ} (hN : N.Perfect) (he : N.factorization 13 % 4 = 1)
    (hr₀_mem : r₀ ∈ N.primeFactors) (hr₀_prime : r₀.Prime) (hr₀_odd : Odd r₀)
    (h3_eq2 : N.factorization 3 = 2)
    (hpart : N.primeFactors = insert 3 (insert 13 (insert r₀ (squareSourcesTwo N))))
    (h3_not_ins : (3 : ℕ) ∉ insert 13 (insert r₀ (squareSourcesTwo N)))
    (h13_not_ins : (13 : ℕ) ∉ insert r₀ (squareSourcesTwo N))
    (hr₀_not_S₂ : r₀ ∉ squareSourcesTwo N)
    (hprime_cases : ∀ p ∈ N.primeFactors, p = 3 ∨ p = 13 ∨ p = r₀ ∨ p ∈ squareSourcesTwo N)
    (hS₂_prop : ∀ u ∈ squareSourcesTwo N,
      u.Prime ∧ Odd u ∧ N.factorization u = 2 ∧ u % 3 = 2 ∧ 5 ≤ u ∧
      sigma 1 (u ^ N.factorization u) = u ^ 2 + u + 1 ∧
      (u ^ 2 + u + 1).primeFactors ⊆ N.primeFactors.filter (fun w => w % 3 = 1))
    (hT_sub : N.primeFactors.filter (fun w => w % 3 = 1) ⊆ {13, r₀})
    (hr₀3 : r₀ % 3 = 2) : False := by
  let S₂ := squareSourcesTwo N
  let T := N.primeFactors.filter (fun w => w % 3 = 1)
  have hT_sub13 : T ⊆ {13} := by
    intro w hw
    have hw_pair := hT_sub hw
    have hw3 := (Finset.mem_filter.mp hw).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw_pair
    rcases hw_pair with rfl | rfl
    · exact Finset.mem_singleton_self 13
    · omega
  by_cases hr₀5 : r₀ = 5
  · subst hr₀5
    have hsum := factorization_eq_sum_sigma_factorizations hN (by decide : Odd 5)
      (by decide : Nat.Prime 5)
    have h5_pos : 0 < N.factorization 5 := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr₀_mem)
    have hex : ∃ p ∈ N.primeFactors, 0 < (sigma 1 (p ^ N.factorization p)).factorization 5 := by
      by_contra! hzero
      have hsum0 : ∑ p ∈ N.primeFactors, (sigma 1 (p ^ N.factorization p)).factorization 5 = 0 :=
        Finset.sum_eq_zero fun p hp => Nat.eq_zero_of_le_zero (hzero p hp)
      omega
    obtain ⟨p, hp_mem, hp_pos⟩ := hex
    have h5_dvd : 5 ∣ sigma 1 (p ^ N.factorization p) :=
      ((by decide : Nat.Prime 5).dvd_iff_one_le_factorization
        (sigma_pos _ _ (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp_mem).ne_zero)).ne').mpr
        hp_pos
    rcases hprime_cases p hp_mem with rfl | rfl | rfl | hpS₂
    · rw [h3_eq2] at h5_dvd
      have h13 : sigma 1 (3 ^ 2) = 13 := by
        rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
        decide
      rw [h13] at h5_dvd
      omega
    · exact not_five_dvd_sigma_thirteen_one_mod_four he h5_dvd
    · have hmod := sigma_prime_pow_mod_self (by decide : Nat.Prime 5) (N.factorization 5)
      have h0 : sigma 1 (5 ^ N.factorization 5) % 5 = 0 := Nat.mod_eq_zero_of_dvd h5_dvd
      omega
    · rw [(hS₂_prop p hpS₂).2.2.2.2.2.1] at h5_dvd
      exact not_five_dvd_sq_add_self_add_one p h5_dvd
  · have hr₀_ge11 : 11 ≤ r₀ := by
      have hr₀2 := Nat.odd_iff.mp hr₀_odd
      have hr₀_gt2 := hr₀_prime.two_le
      omega
    have hS₂_pow : ∀ u ∈ S₂, u ^ 2 + u + 1 = 13 ^ (u ^ 2 + u + 1).factorization 13 := by
      intro u hu
      exact eq_pow_of_primeFactors_subset (by positivity)
        ((hS₂_prop u hu).2.2.2.2.2.2.trans hT_sub13)
    have hS₂_ge47 : ∀ u ∈ S₂, 47 ≤ u := by
      intro u hu
      by_contra! hu_lt
      have hu5 : 5 ≤ u := (hS₂_prop u hu).2.2.2.2.1
      have hpow := hS₂_pow u hu
      set k := (u ^ 2 + u + 1).factorization 13
      have hlt_pow : 13 ^ k < 13 ^ 3 := by
        calc
          13 ^ k = u ^ 2 + u + 1 := hpow.symm
          _ ≤ 46 ^ 2 + 46 + 1 := by nlinarith
          _ < 13 ^ 3 := by norm_num
      have hk3 : k < 3 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 13)).mp hlt_pow
      exact ne_thirteen_pow_of_lt_47 hu5 hk3 hpow
    let P_S := ∏ u ∈ S₂, (u ^ 2 + u + 1)
    let Q_S := ∏ u ∈ S₂, u ^ 2
    have hN_eq : 3 ^ 2 * 13 ^ N.factorization 13 * r₀ ^ N.factorization r₀ * Q_S = N := by
      have hfac := Nat.prod_primeFactors_pow_factorization hN.2.ne'
      rw [hpart, Finset.prod_insert h3_not_ins, Finset.prod_insert h13_not_ins,
        Finset.prod_insert hr₀_not_S₂, h3_eq2] at hfac
      have hS_prod : (∏ u ∈ S₂, u ^ N.factorization u) = Q_S :=
        Finset.prod_congr rfl fun u hu => by rw [(hS₂_prop u hu).2.2.1]
      rw [hS_prod] at hfac
      calc
        3 ^ 2 * 13 ^ N.factorization 13 * r₀ ^ N.factorization r₀ * Q_S
            = 3 ^ 2 * (13 ^ N.factorization 13 * (r₀ ^ N.factorization r₀ * Q_S)) := by ring
        _ = N := hfac.symm
    have hσ_eq : sigma 1 (3 ^ 2) * sigma 1 (13 ^ N.factorization 13) *
        sigma 1 (r₀ ^ N.factorization r₀) * P_S = 2 * N := by
      have hσN : sigma 1 N = 2 * N :=
        (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN)
      have hmul : sigma 1 N = ∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p) :=
        isMultiplicative_sigma.multiplicative_factorization (sigma 1) hN.2.ne'
      rw [hσN, hpart, Finset.prod_insert h3_not_ins, Finset.prod_insert h13_not_ins,
        Finset.prod_insert hr₀_not_S₂, h3_eq2] at hmul
      have hS_prod : (∏ u ∈ S₂, sigma 1 (u ^ N.factorization u)) = P_S :=
        Finset.prod_congr rfl fun u hu => (hS₂_prop u hu).2.2.2.2.2.1
      rw [hS_prod] at hmul
      calc
        sigma 1 (3 ^ 2) * sigma 1 (13 ^ N.factorization 13) *
            sigma 1 (r₀ ^ N.factorization r₀) * P_S
            = sigma 1 (3 ^ 2) * (sigma 1 (13 ^ N.factorization 13) *
                (sigma 1 (r₀ ^ N.factorization r₀) * P_S)) := by ring
        _ = 2 * N := hmul.symm
    have hS_ratio : 141 * P_S ≤ 145 * Q_S := by
      rcases S₂.eq_empty_or_nonempty with hemp | hne
      · simp [P_S, Q_S, hemp]
      · have hu₀_ge : 47 ≤ S₂.min' hne := hS₂_ge47 _ (S₂.min'_mem hne)
        have hgap : ∀ u ∈ S₂, ∀ v ∈ S₂, u < v → 5 * u ^ 2 < v := fun u hu v hv huv =>
          sq_add_self_add_one_prime_pow_gap (by decide : Nat.Prime 13) (by decide)
            (hS₂_prop u hu).2.1 (hS₂_prop v hv).2.1
            (hS₂_prop u hu).2.2.2.1 (hS₂_prop v hv).2.2.2.1 huv
            (hS₂_pow u hu) (hS₂_pow v hv)
        have hgap_prod := prod_sq_abundancy_lt_of_five_sq_gap S₂ hne
          (fun u hu => (hS₂_prop u hu).2.2.2.2.1) hgap
        exact sq_prod_ratio_le (by decide) hgap_prod (by omega)
    have h3_ratio : 9 * sigma 1 (3 ^ 2) ≤ 13 * 3 ^ 2 := by
      rw [sigma_one_apply_prime_pow Nat.prime_three]
      norm_num [Finset.sum_range_succ]
    have hq_strict : 12 * sigma 1 (13 ^ N.factorization 13) < 13 * 13 ^ N.factorization 13 :=
      sigma_prime_pow_ratio_lt (by decide : Nat.Prime 13) (by decide) (by decide)
    have hr₀_ratio : 10 * sigma 1 (r₀ ^ N.factorization r₀) ≤ 11 * r₀ ^ N.factorization r₀ :=
      (sigma_prime_pow_ratio_lt hr₀_prime (by decide) (by omega)).le
    have hP_pos : 0 < P_S := Finset.prod_pos fun u _ => by positivity
    exact abundancy_contradiction4 hN.2 hσ_eq hN_eq
      (Nat.mul_pos (by decide) (sigma_pos _ _ (by decide))) h3_ratio
      hq_strict
      (Nat.mul_pos (by decide) (sigma_pos _ _ (pow_ne_zero _ hr₀_prime.ne_zero))) hr₀_ratio
      (Nat.mul_pos (by decide) hP_pos) hS_ratio
      (by norm_num)

private lemma restrained_exact_nine_case_q13_r0_7
    {N : ℕ} (hN : N.Perfect)
    (h3_eq2 : N.factorization 3 = 2)
    (hpart : N.primeFactors = insert 3 (insert 13 (insert 7 (squareSourcesTwo N))))
    (h3_not_ins : (3 : ℕ) ∉ insert 13 (insert 7 (squareSourcesTwo N)))
    (h13_not_ins : (13 : ℕ) ∉ insert 7 (squareSourcesTwo N))
    (h7_not_S₂ : (7 : ℕ) ∉ squareSourcesTwo N)
    (hS₂_prop : ∀ u ∈ squareSourcesTwo N,
      u.Prime ∧ Odd u ∧ N.factorization u = 2 ∧ u % 3 = 2 ∧ 5 ≤ u ∧
      sigma 1 (u ^ N.factorization u) = u ^ 2 + u + 1 ∧
      (u ^ 2 + u + 1).primeFactors ⊆ N.primeFactors.filter (fun w => w % 3 = 1))
    (hT_sub : N.primeFactors.filter (fun w => w % 3 = 1) ⊆ {13, 7})
    (h13_ratio : 12 * sigma 1 (13 ^ N.factorization 13) ≤ 13 * 13 ^ N.factorization 13) :
    False := by
  have hS₂_ge197 := restrained_S2_ge_197 hS₂_prop hT_sub
  have hS₂_od := restrained_S2_od_ge_198 hS₂_ge197
  have h7_ratio : 6 * sigma 1 (7 ^ N.factorization 7) < 7 * 7 ^ N.factorization 7 :=
    sigma_prime_pow_ratio_lt (by decide : Nat.Prime 7) (by decide) (by decide)
  exact two_prime_abundancy_contradiction hN (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) h3_eq2 hpart h3_not_ins h13_not_ins
    h7_not_S₂ hS₂_prop hT_sub (by decide) h13_ratio h7_ratio (by decide) (by decide)
    hS₂_ge197 hS₂_od (by norm_num)

private lemma sigma_one_four_prime_pows {a b c d e₁ e₂ e₃ e₄ : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hc : c.Prime) (hd : d.Prime)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d) :
    sigma 1 (a ^ e₁ * b ^ e₂ * c ^ e₃ * d ^ e₄) =
      (∑ i ∈ Finset.range (e₁ + 1), a ^ i) *
      (∑ i ∈ Finset.range (e₂ + 1), b ^ i) *
      (∑ i ∈ Finset.range (e₃ + 1), c ^ i) *
      (∑ i ∈ Finset.range (e₄ + 1), d ^ i) := by
  have cop : ∀ {p q : ℕ}, p.Prime → q.Prime → p ≠ q → ∀ i j, (p ^ i).Coprime (q ^ j) :=
    fun hp hq hpq i j => (hp.coprime_iff_not_dvd.mpr ((Nat.dvd_prime hq).not.mpr
      (by rintro (rfl | rfl); exact hp.ne_one rfl; exact hpq rfl))).pow i j
  have h1 := (isMultiplicative_sigma (k := 1)).map_mul_of_coprime
    (((cop ha hd had e₁ e₄).mul_left (cop hb hd hbd e₂ e₄)).mul_left (cop hc hd hcd e₃ e₄))
  have h2 := (isMultiplicative_sigma (k := 1)).map_mul_of_coprime
    ((cop ha hc hac e₁ e₃).mul_left (cop hb hc hbc e₂ e₃))
  have h3 := (isMultiplicative_sigma (k := 1)).map_mul_of_coprime (cop ha hb hab e₁ e₂)
  rw [h1, h2, h3, sigma_one_apply_prime_pow ha, sigma_one_apply_prime_pow hb,
    sigma_one_apply_prime_pow hc, sigma_one_apply_prime_pow hd]

private lemma prime_307 : Nat.Prime 307 := by decide +kernel

private lemma abundancy_3_5_13_31 :
    2 * (3 ^ 2 * 5 ^ 2 * 13 ^ 5 * 31 ^ 4) < sigma 1 (3 ^ 2 * 5 ^ 2 * 13 ^ 5 * 31 ^ 4) := by
  have hσD := sigma_one_four_prime_pows (a := 3) (b := 5) (c := 13) (d := 31)
    (e₁ := 2) (e₂ := 2) (e₃ := 5) (e₄ := 4)
    Nat.prime_three (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [hσD]
  norm_num [Finset.sum_range_succ]

private lemma restrained_exact_nine_case_q13_r0_ge19
    {N r₀ : ℕ} (hN : N.Perfect)
    (hr₀_ne_q : r₀ ≠ 13) (hr₀_ge4 : 4 ≤ N.factorization r₀)
    (hr₀_prime : r₀.Prime) (hr₀_odd : Odd r₀) (hr₀_mod3 : r₀ % 3 = 1) (hr₀_ne7 : r₀ ≠ 7)
    (h9 : 9 ∣ N) (h3_eq2 : N.factorization 3 = 2)
    (hpart : N.primeFactors = insert 3 (insert 13 (insert r₀ (squareSourcesTwo N))))
    (h3_not_ins : (3 : ℕ) ∉ insert 13 (insert r₀ (squareSourcesTwo N)))
    (h13_not_ins : (13 : ℕ) ∉ insert r₀ (squareSourcesTwo N))
    (hr₀_not_S₂ : r₀ ∉ squareSourcesTwo N)
    (hS₂_prop : ∀ u ∈ squareSourcesTwo N,
      u.Prime ∧ Odd u ∧ N.factorization u = 2 ∧ u % 3 = 2 ∧ 5 ≤ u ∧
      sigma 1 (u ^ N.factorization u) = u ^ 2 + u + 1 ∧
      (u ^ 2 + u + 1).primeFactors ⊆ N.primeFactors.filter (fun w => w % 3 = 1))
    (hT_sub : N.primeFactors.filter (fun w => w % 3 = 1) ⊆ {13, r₀})
    (h13_ge5 : 5 ≤ N.factorization 13)
    (h13_ratio : 12 * sigma 1 (13 ^ N.factorization 13) ≤ 13 * 13 ^ N.factorization 13) :
    False := by
  let S₂ := squareSourcesTwo N
  have hr₀_ge19 : 19 ≤ r₀ := by
    have hr₀2 := Nat.odd_iff.mp hr₀_odd
    have hr₀_gt2 := hr₀_prime.two_le
    omega
  by_cases h5_in : 5 ∈ S₂
  · have h31_mem : 31 ∈ (5 ^ 2 + 5 + 1).primeFactors := by
      rw [show (5 : ℕ) ^ 2 + 5 + 1 = 31 by decide]
      exact Nat.mem_primeFactors.mpr ⟨by decide, dvd_refl 31, by decide⟩
    have h31_pair := hT_sub ((hS₂_prop 5 h5_in).2.2.2.2.2.2 h31_mem)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h31_pair
    have hr₀_eq31 : r₀ = 31 := by omega
    subst hr₀_eq31
    have h5_25 : 5 ^ 2 ∣ N :=
      ((by decide : Nat.Prime 5).pow_dvd_iff_le_factorization hN.2.ne').2
        (by rw [(hS₂_prop 5 h5_in).2.2.1])
    have h13_pow : 13 ^ 5 ∣ N :=
      ((by decide : Nat.Prime 13).pow_dvd_iff_le_factorization hN.2.ne').2 h13_ge5
    have h31_pow : 31 ^ 4 ∣ N :=
      ((by decide : Nat.Prime 31).pow_dvd_iff_le_factorization hN.2.ne').2 hr₀_ge4
    have hD_dvd : 3 ^ 2 * 5 ^ 2 * 13 ^ 5 * 31 ^ 4 ∣ N := by
      have h9_25 : 3 ^ 2 * 5 ^ 2 ∣ N :=
        ((by decide : Nat.Coprime 3 5).pow 2 2).mul_dvd_of_dvd_of_dvd
          (by simpa using h9) h5_25
      have h_13 : 3 ^ 2 * 5 ^ 2 * 13 ^ 5 ∣ N :=
        (((by decide : Nat.Coprime 3 13).pow 2 5).mul_left
          ((by decide : Nat.Coprime 5 13).pow 2 5)).mul_dvd_of_dvd_of_dvd h9_25 h13_pow
      exact ((((by decide : Nat.Coprime 3 31).pow 2 4).mul_left
        ((by decide : Nat.Coprime 5 31).pow 2 4)).mul_left
        ((by decide : Nat.Coprime 13 31).pow 5 4)).mul_dvd_of_dvd_of_dvd h_13 h31_pow
    exact false_of_dvd_of_two_mul_lt_sigma hN hD_dvd abundancy_3_5_13_31
  · have h11_not : 11 ∉ S₂ := by
      intro h11
      have h7_mem : 7 ∈ (11 ^ 2 + 11 + 1).primeFactors := by
        rw [show (11 : ℕ) ^ 2 + 11 + 1 = 7 * 19 by decide]
        exact Nat.mem_primeFactors.mpr ⟨by decide, ⟨19, rfl⟩, by decide⟩
      have h7_pair := hT_sub ((hS₂_prop 11 h11).2.2.2.2.2.2 h7_mem)
      simp only [Finset.mem_insert, Finset.mem_singleton] at h7_pair
      omega
    have h23_not : 23 ∉ S₂ := by
      intro h23
      have h7_mem : 7 ∈ (23 ^ 2 + 23 + 1).primeFactors := by
        rw [show (23 : ℕ) ^ 2 + 23 + 1 = 7 * 79 by decide]
        exact Nat.mem_primeFactors.mpr ⟨by decide, ⟨79, rfl⟩, by decide⟩
      have h7_pair := hT_sub ((hS₂_prop 23 h23).2.2.2.2.2.2 h7_mem)
      simp only [Finset.mem_insert, Finset.mem_singleton] at h7_pair
      omega
    by_cases h17_in : 17 ∈ S₂
    · have h307_mem : 307 ∈ (17 ^ 2 + 17 + 1).primeFactors := by
        rw [show (17 : ℕ) ^ 2 + 17 + 1 = 307 by decide]
        exact Nat.mem_primeFactors.mpr ⟨prime_307, dvd_refl 307, by decide⟩
      have h307_pair := hT_sub ((hS₂_prop 17 h17_in).2.2.2.2.2.2 h307_mem)
      simp only [Finset.mem_insert, Finset.mem_singleton] at h307_pair
      have hr₀_eq307 : r₀ = 307 := by omega
      subst hr₀_eq307
      have hS₂_ge17 : ∀ u ∈ S₂, 17 ≤ u := by
        intro u hu
        have hu_mod2 := Nat.odd_iff.mp (hS₂_prop u hu).2.1
        have hu3 := (hS₂_prop u hu).2.2.2.1
        have hu5 := (hS₂_prop u hu).2.2.2.2.1
        have hu_ne5 : u ≠ 5 := fun h => h5_in (h ▸ hu)
        have hu_ne11 : u ≠ 11 := fun h => h11_not (h ▸ hu)
        omega
      have hS₂_od : ∀ x ∈ (oddIdx S₂.sort).head?, 29 ≤ x := by
        intro x hx
        have hchain : S₂.sort.IsChain (· < ·) := (Finset.sortedLT_sort S₂).isChain
        have hge_sort : ∀ u ∈ S₂.sort, 17 ≤ u := fun u hu =>
          hS₂_ge17 u ((Finset.mem_sort (· ≤ ·)).mp hu)
        obtain ⟨hgt, hx_mem⟩ := oddIdx_head_gt hchain hge_sort hx
        have hx_S₂ : x ∈ S₂ := (Finset.mem_sort (· ≤ ·)).mp hx_mem
        have hx_mod2 := Nat.odd_iff.mp (hS₂_prop x hx_S₂).2.1
        have hx3 := (hS₂_prop x hx_S₂).2.2.2.1
        have hx_ne23 : x ≠ 23 := fun h => h23_not (h ▸ hx_S₂)
        omega
      have h307_ratio : 306 * sigma 1 (307 ^ N.factorization 307) <
          307 * 307 ^ N.factorization 307 :=
        sigma_prime_pow_ratio_lt prime_307 (by decide) (by decide)
      exact two_prime_abundancy_contradiction hN (by decide) (by decide) (by decide)
        prime_307 (by decide) (by decide) (by decide) h3_eq2 hpart h3_not_ins h13_not_ins
        hr₀_not_S₂ hS₂_prop hT_sub (by decide) h13_ratio h307_ratio (by decide) (by decide)
        hS₂_ge17 hS₂_od (by norm_num)
    · have hS₂_ge29 : ∀ u ∈ S₂, 29 ≤ u := by
        intro u hu
        have hu_mod2 := Nat.odd_iff.mp (hS₂_prop u hu).2.1
        have hu3 := (hS₂_prop u hu).2.2.2.1
        have hu5 := (hS₂_prop u hu).2.2.2.2.1
        have hu_ne5 : u ≠ 5 := fun h => h5_in (h ▸ hu)
        have hu_ne11 : u ≠ 11 := fun h => h11_not (h ▸ hu)
        have hu_ne17 : u ≠ 17 := fun h => h17_in (h ▸ hu)
        have hu_ne23 : u ≠ 23 := fun h => h23_not (h ▸ hu)
        omega
      have hS₂_od : ∀ x ∈ (oddIdx S₂.sort).head?, 41 ≤ x := by
        intro x hx
        have hchain : S₂.sort.IsChain (· < ·) := (Finset.sortedLT_sort S₂).isChain
        have hge_sort : ∀ u ∈ S₂.sort, 29 ≤ u := fun u hu =>
          hS₂_ge29 u ((Finset.mem_sort (· ≤ ·)).mp hu)
        obtain ⟨hgt, hx_mem⟩ := oddIdx_head_gt hchain hge_sort hx
        have hx_S₂ : x ∈ S₂ := (Finset.mem_sort (· ≤ ·)).mp hx_mem
        have hx_prime := (hS₂_prop x hx_S₂).1
        have hx_mod2 := Nat.odd_iff.mp (hS₂_prop x hx_S₂).2.1
        have hx3 := (hS₂_prop x hx_S₂).2.2.2.1
        have hx_ne35 : x ≠ 35 := by
          intro h
          subst h
          exact (by decide : ¬ Nat.Prime 35) hx_prime
        omega
      have hr₀_ratio : 18 * sigma 1 (r₀ ^ N.factorization r₀) <
          19 * r₀ ^ N.factorization r₀ :=
        sigma_prime_pow_ratio_lt hr₀_prime (by decide) (by omega)
      exact two_prime_abundancy_contradiction hN (by decide) (by decide) (by decide)
        hr₀_prime hr₀_odd hr₀_mod3 hr₀_ne_q h3_eq2 hpart h3_not_ins h13_not_ins
        hr₀_not_S₂ hS₂_prop hT_sub (by decide) h13_ratio hr₀_ratio (by decide) (by decide)
        hS₂_ge29 hS₂_od (by norm_num)

private lemma restrained_exact_nine_case_q_ne_13
    {N q : ℕ} (hN : N.Perfect)
    (hq4 : q % 4 = 1) (hq_prime : q.Prime) (hq_odd : Odd q) (hq3 : q % 3 = 1)
    (h3_eq2 : N.factorization 3 = 2)
    (hpart : N.primeFactors = insert 3 (insert q (insert 13 (squareSourcesTwo N))))
    (h3_not_ins : (3 : ℕ) ∉ insert q (insert 13 (squareSourcesTwo N)))
    (hq_not_ins : q ∉ insert 13 (squareSourcesTwo N))
    (h13_not_S₂ : (13 : ℕ) ∉ squareSourcesTwo N)
    (hS₂_prop : ∀ u ∈ squareSourcesTwo N,
      u.Prime ∧ Odd u ∧ N.factorization u = 2 ∧ u % 3 = 2 ∧ 5 ≤ u ∧
      sigma 1 (u ^ N.factorization u) = u ^ 2 + u + 1 ∧
      (u ^ 2 + u + 1).primeFactors ⊆ N.primeFactors.filter (fun w => w % 3 = 1))
    (hT_sub : N.primeFactors.filter (fun w => w % 3 = 1) ⊆ {q, 13})
    (hq13 : q ≠ 13) : False := by
  let S₂ := squareSourcesTwo N
  have hq_ge37 : 37 ≤ q := by
    have hq_mod12 : q % 12 = 1 := by omega
    have hq_gt2 := hq_prime.two_le
    have hq_ne25 : q ≠ 25 := by
      intro h
      subst h
      exact (by decide : ¬ Nat.Prime 25) hq_prime
    omega
  have hS₂_ge29 : ∀ u ∈ S₂, 29 ≤ u := by
    intro u hu
    have hu_mod2 := Nat.odd_iff.mp (hS₂_prop u hu).2.1
    have hu3 := (hS₂_prop u hu).2.2.2.1
    have hu5 := (hS₂_prop u hu).2.2.2.2.1
    have hu_ne5 : u ≠ 5 := by
      intro h
      subst h
      have h31_mem : 31 ∈ (5 ^ 2 + 5 + 1).primeFactors := by
        rw [show (5 : ℕ) ^ 2 + 5 + 1 = 31 by decide]
        exact Nat.mem_primeFactors.mpr ⟨by decide, dvd_refl 31, by decide⟩
      have h31_pair := hT_sub ((hS₂_prop 5 hu).2.2.2.2.2.2 h31_mem)
      simp only [Finset.mem_insert, Finset.mem_singleton] at h31_pair
      omega
    have hu_ne11 : u ≠ 11 := by
      intro h
      subst h
      have h7_mem : 7 ∈ (11 ^ 2 + 11 + 1).primeFactors := by
        rw [show (11 : ℕ) ^ 2 + 11 + 1 = 7 * 19 by decide]
        exact Nat.mem_primeFactors.mpr ⟨by decide, ⟨19, rfl⟩, by decide⟩
      have h7_pair := hT_sub ((hS₂_prop 11 hu).2.2.2.2.2.2 h7_mem)
      simp only [Finset.mem_insert, Finset.mem_singleton] at h7_pair
      omega
    have hu_ne17 : u ≠ 17 := by
      intro h
      subst h
      have h307_mem : 307 ∈ (17 ^ 2 + 17 + 1).primeFactors := by
        rw [show (17 : ℕ) ^ 2 + 17 + 1 = 307 by decide]
        exact Nat.mem_primeFactors.mpr ⟨prime_307, dvd_refl 307, by decide⟩
      have h307_pair := hT_sub ((hS₂_prop 17 hu).2.2.2.2.2.2 h307_mem)
      simp only [Finset.mem_insert, Finset.mem_singleton] at h307_pair
      rcases h307_pair with h307 | h307
      · rw [← h307] at hq4
        omega
      · omega
    have hu_ne23 : u ≠ 23 := by
      intro h
      subst h
      have h7_mem : 7 ∈ (23 ^ 2 + 23 + 1).primeFactors := by
        rw [show (23 : ℕ) ^ 2 + 23 + 1 = 7 * 79 by decide]
        exact Nat.mem_primeFactors.mpr ⟨by decide, ⟨79, rfl⟩, by decide⟩
      have h7_pair := hT_sub ((hS₂_prop 23 hu).2.2.2.2.2.2 h7_mem)
      simp only [Finset.mem_insert, Finset.mem_singleton] at h7_pair
      omega
    omega
  have hS₂_od : ∀ x ∈ (oddIdx S₂.sort).head?, 41 ≤ x := by
    intro x hx
    have hchain : S₂.sort.IsChain (· < ·) := (Finset.sortedLT_sort S₂).isChain
    have hge_sort : ∀ u ∈ S₂.sort, 29 ≤ u := fun u hu =>
      hS₂_ge29 u ((Finset.mem_sort (· ≤ ·)).mp hu)
    obtain ⟨hgt, hx_mem⟩ := oddIdx_head_gt hchain hge_sort hx
    have hx_S₂ : x ∈ S₂ := (Finset.mem_sort (· ≤ ·)).mp hx_mem
    have hx_prime := (hS₂_prop x hx_S₂).1
    have hx_mod2 := Nat.odd_iff.mp (hS₂_prop x hx_S₂).2.1
    have hx3 := (hS₂_prop x hx_S₂).2.2.2.1
    have hx_ne35 : x ≠ 35 := by
      intro h
      subst h
      exact (by decide : ¬ Nat.Prime 35) hx_prime
    omega
  have hq_ratio : 36 * sigma 1 (q ^ N.factorization q) ≤ 37 * q ^ N.factorization q :=
    (sigma_prime_pow_ratio_lt hq_prime (by decide) (by omega)).le
  have h13_ratio : 12 * sigma 1 (13 ^ N.factorization 13) < 13 * 13 ^ N.factorization 13 :=
    sigma_prime_pow_ratio_lt (by decide : Nat.Prime 13) (by decide) (by decide)
  exact two_prime_abundancy_contradiction hN hq_prime hq_odd hq3
    (by decide) (by decide) (by decide) hq13.symm h3_eq2 hpart h3_not_ins hq_not_ins
    h13_not_S₂ hS₂_prop hT_sub (by decide) hq_ratio h13_ratio (by decide) (by decide)
    hS₂_ge29 hS₂_od (by norm_num)

/-- **Restrained `3^2 ∥ N` Obstruction when `squareSourcesOne N = ∅`**:
Every restrained odd perfect number (`(largeSources N q).card ≤ 1`) with `squareSourcesOne N = ∅`
satisfies `4 ≤ N.factorization 3` and `81 ∣ N`, unconditionally for ALL Euler primes `q`. -/
theorem four_le_three_exponent_of_restrained_squareSourcesOne_empty
    {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hle : (largeSources N q).card ≤ 1)
    (hS₁_empty : squareSourcesOne N = ∅) :
    4 ≤ N.factorization 3 ∧ 81 ∣ N := by
  suffices h4 : 4 ≤ N.factorization 3 by
    have h81 : 81 ∣ N := by
      have hpow : 3 ^ 4 ∣ N :=
        (Nat.prime_three.pow_dvd_iff_le_factorization hN.2.ne').2 h4
      simpa using hpow
    exact ⟨h4, h81⟩
  by_contra! hlt4
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hq_odd : Odd q := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)
  have hq3_ne2 : q % 3 ≠ 2 := by
    intro hq3
    have h4 := (four_le_three_exponent_of_restrained_euler_two_mod_three
      ho hN hq hq4 he hev hle hq3).1
    omega
  have h3_ne_q : (3 : ℕ) ≠ q := by omega
  have hq3 : q % 3 = 1 := by
    have hq_mod3_ne0 : q % 3 ≠ 0 := by
      intro h0
      have hd3 : 3 ∣ q := Nat.dvd_of_mod_eq_zero h0
      rcases (Nat.dvd_prime hq_prime).mp hd3 with h1 | h3
      · omega
      · exact h3_ne_q h3
    omega
  have h3_dvd : 3 ∣ N := three_dvd_of_largeSources_le_one ho hN hq hq4 he hev hle
  have h3_mem : 3 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3_dvd, hN.2.ne'⟩
  have h3_pos : 0 < N.factorization 3 := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp h3_mem)
  have h3_even : Even (N.factorization 3) := hev 3 h3_ne_q
  have h3_eq2 : N.factorization 3 = 2 := by
    obtain ⟨k, hk⟩ := h3_even
    omega
  have hlarge_ne : largeSources N q ≠ ∅ := by
    intro hempty
    have h8 := eight_le_three_exponent_of_largeSources_empty ho hN hq hq4 he hev hempty
    omega
  have hlarge_card : (largeSources N q).card = 1 := by
    have hpos : 0 < (largeSources N q).card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hlarge_ne)
    omega
  obtain ⟨r₀, hr₀_eq⟩ := Finset.card_eq_one.mp hlarge_card
  have hr₀_mem_large : r₀ ∈ largeSources N q := by rw [hr₀_eq]; exact Finset.mem_singleton_self r₀
  obtain ⟨hr₀_mem, hr₀_ne3, hr₀_ne_q, _hr₀_ge4⟩ := Finset.mem_filter.mp hr₀_mem_large
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_mem
  have hr₀_odd : Odd r₀ := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr₀_mem)
  have h9 : 9 ∣ N := by
    have hpow : 3 ^ 2 ∣ N := (Nat.prime_three.pow_dvd_iff_le_factorization hN.2.ne').2 (by omega)
    simpa using hpow
  have h27 : ¬ 27 ∣ N := by
    intro h
    have hle3 : 3 ≤ N.factorization 3 :=
      (Nat.prime_three.pow_dvd_iff_le_factorization hN.2.ne').1 (by simpa using h)
    omega
  have h13_dvd : 13 ∣ N := thirteen_dvd_of_exact_nine hN h9 h27
  have h13_mem : 13 ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨by decide, h13_dvd, hN.2.ne'⟩
  let S₂ := squareSourcesTwo N
  have hS_union : squareSources N = squareSourcesOne N ∪ S₂ := squareSources_eq_union_one_two N
  have hprime_cases : ∀ p ∈ N.primeFactors, p = 3 ∨ p = q ∨ p = r₀ ∨ p ∈ S₂ := by
    intro p hp
    by_cases hp3 : p = 3
    · exact Or.inl hp3
    · by_cases hpq : p = q
      · exact Or.inr (Or.inl hpq)
      · have hpos : 0 < N.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
        obtain ⟨k, hk⟩ := hev p hpq
        by_cases htwo : N.factorization p = 2
        · have hpS : p ∈ squareSources N := Finset.mem_filter.mpr ⟨hp, hp3, htwo⟩
          rw [hS_union, hS₁_empty, Finset.empty_union] at hpS
          exact Or.inr (Or.inr (Or.inr hpS))
        · have hlarge_p : p ∈ largeSources N q :=
            Finset.mem_filter.mpr ⟨hp, hp3, hpq, by omega⟩
          rw [hr₀_eq, Finset.mem_singleton] at hlarge_p
          exact Or.inr (Or.inr (Or.inl hlarge_p))
  have h3_not_S : 3 ∉ squareSources N := fun h => (Finset.mem_filter.mp h).2.1 rfl
  have hq_not_S : q ∉ squareSources N := by
    intro h
    have := (Finset.mem_filter.mp h).2.2
    omega
  have hr₀_not_S : r₀ ∉ squareSources N := by
    intro h
    have := (Finset.mem_filter.mp h).2.2
    omega
  have h3_not_S₂ : 3 ∉ S₂ := fun h => h3_not_S (Finset.mem_filter.mp h).1
  have hq_not_S₂ : q ∉ S₂ := fun h => hq_not_S (Finset.mem_filter.mp h).1
  have hr₀_not_S₂ : r₀ ∉ S₂ := fun h => hr₀_not_S (Finset.mem_filter.mp h).1
  have hpart : N.primeFactors = insert 3 (insert q (insert r₀ S₂)) := by
    ext p
    simp only [Finset.mem_insert]
    constructor
    · intro hp
      exact hprime_cases p hp
    · rintro (rfl | rfl | rfl | hp2)
      · exact h3_mem
      · exact hq
      · exact hr₀_mem
      · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp2).1).1
  have h3_not_ins : (3 : ℕ) ∉ insert q (insert r₀ S₂) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨h3_ne_q, hr₀_ne3.symm, h3_not_S₂⟩
  have hq_not_ins : q ∉ insert r₀ S₂ := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hr₀_ne_q.symm, hq_not_S₂⟩
  let T := N.primeFactors.filter (fun w => w % 3 = 1)
  have h13_T : 13 ∈ T := Finset.mem_filter.mpr ⟨h13_mem, by decide⟩
  have hT_sub : T ⊆ {q, r₀} := by
    intro w hw
    obtain ⟨hw_mem, hw3⟩ := Finset.mem_filter.mp hw
    rcases hprime_cases w hw_mem with rfl | rfl | rfl | hw2
    · omega
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · have hw_ne1 := (Finset.mem_filter.mp hw2).2
      omega
  have hS₂_prop : ∀ u ∈ S₂,
      u.Prime ∧ Odd u ∧ N.factorization u = 2 ∧ u % 3 = 2 ∧ 5 ≤ u ∧
      sigma 1 (u ^ N.factorization u) = u ^ 2 + u + 1 ∧
      (u ^ 2 + u + 1).primeFactors ⊆ T := by
    intro u hu
    obtain ⟨huS, hu_ne1⟩ := Finset.mem_filter.mp hu
    obtain ⟨hu_mem, hu_ne3, hu_exp2⟩ := Finset.mem_filter.mp huS
    have hu_prime := Nat.prime_of_mem_primeFactors hu_mem
    have hu_odd := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hu_mem)
    have hu_mod3 : u % 3 = 2 := by
      by_contra! hne2
      have h0 : u % 3 = 0 := by omega
      have hd3 : 3 ∣ u := Nat.dvd_of_mod_eq_zero h0
      rcases (Nat.dvd_prime hu_prime).mp hd3 with h1 | h3
      · omega
      · exact hu_ne3 h3.symm
    have hu5 : 5 ≤ u := by
      have hu_ge2 := hu_prime.two_le
      have hu_mod2 := Nat.odd_iff.mp hu_odd
      omega
    have hsig : sigma 1 (u ^ N.factorization u) = u ^ 2 + u + 1 := by
      rw [hu_exp2, sigma_one_apply_prime_pow hu_prime, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_zero]
      ring
    have hsub : (u ^ 2 + u + 1).primeFactors ⊆ T := by
      intro w hw
      obtain ⟨hw_prime, hw_dvd, _⟩ := Nat.mem_primeFactors.mp hw
      have hsum_odd : Odd (u ^ 2 + u + 1) :=
        ((hu_odd.pow).add_odd hu_odd).add_odd (by decide : Odd 1)
      have hw_odd : Odd w := hsum_odd.of_dvd_nat hw_dvd
      have hw_ne3 : w ≠ 3 := by
        intro h
        subst h
        have hsum_mod3 : (u ^ 2 + u + 1) % 3 = 1 := by
          rw [Nat.add_mod, Nat.add_mod (u ^ 2), Nat.pow_mod, hu_mod3]
        omega
      have hw_mod3 : w % 3 = 1 :=
        (prime_dvd_sq_add_self_add_one hw_prime hw_dvd).resolve_left hw_ne3
      have hwN : w ∣ N := by
        apply dvd_perfect_of_exact_prime_pow hN hu_prime (Nat.ordProj_dvd N u) _ hw_prime hw_odd
        · rw [← sigma_one_apply, hsig]
          exact hw_dvd
        · rw [hu_prime.pow_dvd_iff_le_factorization hN.2.ne']
          omega
      exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hw_prime, hwN, hN.2.ne'⟩, hw_mod3⟩
    exact ⟨hu_prime, hu_odd, hu_exp2, hu_mod3, hu5, hsig, hsub⟩
  by_cases hq13 : q = 13
  · subst hq13
    by_cases h13_exp1 : N.factorization 13 = 1
    · exact restrained_exact_nine_case_q13_exp1 hN h3_eq2 hpart h3_not_ins hq_not_ins
        hr₀_not_S₂ hS₂_prop hT_sub h13_exp1
    · have h13_ge5 : 5 ≤ N.factorization 13 := by omega
      have h13_ratio : 12 * sigma 1 (13 ^ N.factorization 13) ≤ 13 * 13 ^ N.factorization 13 :=
        (sigma_prime_pow_ratio_lt (by decide : Nat.Prime 13) (by decide) (by decide)).le
      by_cases hr₀3 : r₀ % 3 = 2
      · exact restrained_exact_nine_case_q13_r0_mod2 hN he hr₀_mem hr₀_prime hr₀_odd
          h3_eq2 hpart h3_not_ins hq_not_ins hr₀_not_S₂ hprime_cases hS₂_prop hT_sub hr₀3
      · have hr₀_mod3 : r₀ % 3 = 1 := by
          have hr₀_ne0 : r₀ % 3 ≠ 0 := by
            intro h0
            rcases (Nat.dvd_prime hr₀_prime).mp (Nat.dvd_of_mod_eq_zero h0) with h1 | h3
            · omega
            · exact hr₀_ne3 h3.symm
          omega
        by_cases hr₀7 : r₀ = 7
        · subst hr₀7
          exact restrained_exact_nine_case_q13_r0_7 hN h3_eq2 hpart h3_not_ins hq_not_ins
            hr₀_not_S₂ hS₂_prop hT_sub h13_ratio
        · exact restrained_exact_nine_case_q13_r0_ge19 hN hr₀_ne_q _hr₀_ge4 hr₀_prime
            hr₀_odd hr₀_mod3 hr₀7 h9 h3_eq2 hpart h3_not_ins hq_not_ins hr₀_not_S₂
            hS₂_prop hT_sub h13_ge5 h13_ratio
  · have hr₀_eq13 : r₀ = 13 := by
      have hmem := hT_sub h13_T
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      omega
    subst hr₀_eq13
    exact restrained_exact_nine_case_q_ne_13 hN hq4 hq_prime hq_odd hq3 h3_eq2 hpart
      h3_not_ins hq_not_ins hr₀_not_S₂ hS₂_prop hT_sub hq13

/-- **Restrained `3^2 ∥ N` Structural Profile**:
Every restrained odd perfect number (`(largeSources N q).card ≤ 1`) with exact 3-adic exponent
`N.factorization 3 = 2` satisfies `q % 12 = 1`, `13 ≤ q`, `(squareSourcesOne N).Nonempty`,
`1 ≤ (squareSourcesOne N).card`, and `(squareSourcesOne N).card ≤ 2`. -/
theorem restrained_exact_nine_profile
    {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hle : (largeSources N q).card ≤ 1) (h3 : N.factorization 3 = 2) :
    q % 12 = 1 ∧ 13 ≤ q ∧
    (squareSourcesOne N).Nonempty ∧
    1 ≤ (squareSourcesOne N).card ∧ (squareSourcesOne N).card ≤ 2 := by
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hq3_ne2 : q % 3 ≠ 2 := by
    intro hq3
    have h4 := (four_le_three_exponent_of_restrained_euler_two_mod_three
      ho hN hq hq4 he hev hle hq3).1
    omega
  have hq_ne3 : q ≠ 3 := by omega
  have hq3_ne0 : q % 3 ≠ 0 := by
    intro h0
    rcases (Nat.dvd_prime hq_prime).mp (Nat.dvd_of_mod_eq_zero h0) with h1 | h3'
    · omega
    · exact hq_ne3 h3'.symm
  have hq12 : q % 12 = 1 := by omega
  have hq13 : 13 ≤ q := by
    have hgt2 := hq_prime.two_le
    omega
  have hS₁_ne : squareSourcesOne N ≠ ∅ := by
    intro hempty
    have h4 := (four_le_three_exponent_of_restrained_squareSourcesOne_empty
      ho hN hq hq4 he hev hle hempty).1
    omega
  have hS₁_nonempty : (squareSourcesOne N).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hS₁_ne
  have hS₁_one : 1 ≤ (squareSourcesOne N).card := Finset.card_pos.mpr hS₁_nonempty
  have hS₁_two : (squareSourcesOne N).card ≤ 2 := by
    simpa [h3] using squareSourcesOne_card_le_three_exponent hN
  exact ⟨hq12, hq13, hS₁_nonempty, hS₁_one, hS₁_two⟩

end OddPerfect
