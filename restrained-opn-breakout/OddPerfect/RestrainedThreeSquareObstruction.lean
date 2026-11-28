module

public import OddPerfect.ThreeFreeRestrainedClosure
public import OddPerfect.CyclotomicRootSlope
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
# Restrained `3^2 ∥ N` Obstruction for `q ≡ 2 [MOD 3]` (`OddPerfect.RestrainedThreeSquareObstruction`)

Unconditionally proves that for any restrained odd perfect number (`(largeSources N q).card ≤ 1`)
with Euler prime `q ≡ 2 [MOD 3]` (hence `q ≡ 5 [MOD 12]`, including `q = 5`), the 3-adic exponent
satisfies `4 ≤ N.factorization 3` and `81 ∣ N`.

## Main Theorems
- `four_le_three_exponent_of_restrained_euler_two_mod_three`
- `four_le_three_exponent_of_restrained_euler_five`
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

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

private lemma abundancy_contradiction6
    {N σ₁ σ₂ σ₃ σ₄ Pev Pod p₁ p₂ p₃ p₄ Qev Qod
      c₁ d₁ c₂ d₂ c₃ d₃ c₄ d₄ cev dev cod dod : ℕ}
    (_hN_pos : 0 < N)
    (hσ_eq : σ₁ * σ₂ * σ₃ * σ₄ * Pev * Pod = 2 * N)
    (hN_eq : p₁ * p₂ * p₃ * p₄ * Qev * Qod = N)
    (h1_pos : 0 < c₁ * σ₁) (h1 : c₁ * σ₁ ≤ d₁ * p₁)
    (h2 : c₂ * σ₂ < d₂ * p₂)
    (h3_pos : 0 < c₃ * σ₃) (h3 : c₃ * σ₃ ≤ d₃ * p₃)
    (h4_pos : 0 < c₄ * σ₄) (h4 : c₄ * σ₄ ≤ d₄ * p₄)
    (hpev_pos : 0 < cev * Pev) (hpev : cev * Pev ≤ dev * Qev)
    (hpod_pos : 0 < cod * Pod) (hpod : cod * Pod ≤ dod * Qod)
    (hineq : d₁ * d₂ * d₃ * d₄ * dev * dod ≤ 2 * (c₁ * c₂ * c₃ * c₄ * cev * cod)) : False := by
  have hd1p1_pos : 0 < d₁ * p₁ := lt_of_lt_of_le h1_pos h1
  have h12 : (c₁ * σ₁) * (c₂ * σ₂) < (d₁ * p₁) * (d₂ * p₂) :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ h1) (Nat.mul_lt_mul_of_pos_left h2 hd1p1_pos)
  have h123 : ((c₁ * σ₁) * (c₂ * σ₂)) * (c₃ * σ₃) < ((d₁ * p₁) * (d₂ * p₂)) * (d₃ * p₃) :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h12 h3_pos) (Nat.mul_le_mul_left _ h3)
  have h1234 : (((c₁ * σ₁) * (c₂ * σ₂)) * (c₃ * σ₃)) * (c₄ * σ₄) <
      (((d₁ * p₁) * (d₂ * p₂)) * (d₃ * p₃)) * (d₄ * p₄) :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h123 h4_pos) (Nat.mul_le_mul_left _ h4)
  have h12345 : ((((c₁ * σ₁) * (c₂ * σ₂)) * (c₃ * σ₃)) * (c₄ * σ₄)) * (cev * Pev) <
      ((((d₁ * p₁) * (d₂ * p₂)) * (d₃ * p₃)) * (d₄ * p₄)) * (dev * Qev) :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h1234 hpev_pos) (Nat.mul_le_mul_left _ hpev)
  have hprod : (((((c₁ * σ₁) * (c₂ * σ₂)) * (c₃ * σ₃)) * (c₄ * σ₄)) * (cev * Pev)) * (cod * Pod) <
      (((((d₁ * p₁) * (d₂ * p₂)) * (d₃ * p₃)) * (d₄ * p₄)) * (dev * Qev)) * (dod * Qod) :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h12345 hpod_pos) (Nat.mul_le_mul_left _ hpod)
  have hLHS : (((((c₁ * σ₁) * (c₂ * σ₂)) * (c₃ * σ₃)) * (c₄ * σ₄)) * (cev * Pev)) * (cod * Pod) =
      (c₁ * c₂ * c₃ * c₄ * cev * cod) * (σ₁ * σ₂ * σ₃ * σ₄ * Pev * Pod) := by ring
  have hRHS : (((((d₁ * p₁) * (d₂ * p₂)) * (d₃ * p₃)) * (d₄ * p₄)) * (dev * Qev)) * (dod * Qod) =
      (d₁ * d₂ * d₃ * d₄ * dev * dod) * (p₁ * p₂ * p₃ * p₄ * Qev * Qod) := by ring
  rw [hLHS, hRHS, hσ_eq, hN_eq] at hprod
  have hle : (d₁ * d₂ * d₃ * d₄ * dev * dod) * N ≤
      (2 * (c₁ * c₂ * c₃ * c₄ * cev * cod)) * N :=
    Nat.mul_le_mul_right N hineq
  have hlt : (2 * (c₁ * c₂ * c₃ * c₄ * cev * cod)) * N <
      (2 * (c₁ * c₂ * c₃ * c₄ * cev * cod)) * N := by
    calc
      (2 * (c₁ * c₂ * c₃ * c₄ * cev * cod)) * N =
          (c₁ * c₂ * c₃ * c₄ * cev * cod) * (2 * N) := by ring
      _ < (d₁ * d₂ * d₃ * d₄ * dev * dod) * N := hprod
      _ ≤ (2 * (c₁ * c₂ * c₃ * c₄ * cev * cod)) * N := hle
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

private lemma eq_three_mul_pow_of_primeFactors_subset {n : ℕ} (hn : n ≠ 0)
    (h3 : n.factorization 3 = 1) (hsub : n.primeFactors ⊆ {3, 13}) :
    n = 3 * 13 ^ n.factorization 13 := by
  have h := eq_mul_pow_of_primeFactors_subset_pair hn (by decide : (3 : ℕ) ≠ 13) hsub
  rw [h3, pow_one] at h
  exact h

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
  | [a], x => by simp [evenIdx]
  | a :: b :: xs, x => by
      simp only [evenIdx, List.mem_cons]
      rintro (rfl | hx)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (mem_evenIdx_subset hx))

private lemma mem_oddIdx_subset : ∀ {L : List ℕ} {x : ℕ}, x ∈ oddIdx L → x ∈ L
  | [], _ => by simp [oddIdx]
  | [a], _ => by simp [oddIdx]
  | a :: b :: xs, x => by
      simp only [oddIdx, List.mem_cons]
      rintro (rfl | hx)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (mem_oddIdx_subset hx))

private lemma evenIdx_head?_cons (a : ℕ) (t : List ℕ) : (evenIdx (a :: t)).head? = some a := by
  cases t with
  | nil => simp [evenIdx]
  | cons b xs => simp [evenIdx]

private lemma evenIdx_isChain {R : ℕ → ℕ → Prop} :
    ∀ L : List ℕ, L.IsChain (· < ·) →
      (∀ a b c, a ∈ L → b ∈ L → c ∈ L → a < b → b < c → R a c) →
      (evenIdx L).IsChain R
  | [], _, _ => by simp [evenIdx]
  | [x], _, _ => by simp [evenIdx]
  | [x, y], _, _ => by simp [evenIdx]
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
  | [_, y], _, _ => by simp [oddIdx]
  | [_, y, _], _, _ => by simp [oddIdx]
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

private lemma smooth_pair_squareSourcesTwo_bounds
    {S₂ : Finset ℕ} {p₁ p₂ y₀ : ℕ}
    (hp₁ : p₁.Prime) (hp₁_odd : Odd p₁) (hp₁3 : p₁ % 3 = 1)
    (hp₂ : p₂.Prime) (hp₂_odd : Odd p₂) (hp₂3 : p₂ % 3 = 1)
    (hy₀ : 5 ≤ y₀)
    (hS₂_odd : ∀ u ∈ S₂, Odd u)
    (hS₂_3 : ∀ u ∈ S₂, u % 3 = 2)
    (hS₂_5 : ∀ u ∈ S₂, 5 ≤ u)
    (hS₂_ge : ∀ u ∈ S₂, y₀ ≤ u)
    (hS₂_pow : ∀ u ∈ S₂,
      u ^ 2 + u + 1 = p₁ ^ (u ^ 2 + u + 1).factorization p₁ * p₂ ^ (u ^ 2 + u + 1).factorization p₂) :
    ∃ P_ev_num P_ev_den P_od_num P_od_den : ℕ,
      (∏ u ∈ S₂, (u ^ 2 + u + 1)) = P_ev_num * P_od_num ∧
      (∏ u ∈ S₂, u ^ 2) = P_ev_den * P_od_den ∧
      0 < P_ev_num ∧ 0 < P_od_num ∧
      2 * y₀ * P_ev_num ≤ (2 * y₀ + 5) * P_ev_den ∧
      2 * y₀ * P_od_num ≤ (2 * y₀ + 5) * P_od_den := by
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
    have hev_head : ∀ x ∈ (evenIdx L).head?, y₀ ≤ x := fun x hx =>
      hS₂_ge x ((hL_mem x).mp (mem_evenIdx_subset (List.mem_of_head? hx)))
    exact prod_sq_abundancy_le_of_five_halves_step (evenIdx L) hev_chain hev_ge5 y₀ hy₀ hev_head
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
    have hod_head : ∀ x ∈ (oddIdx L).head?, y₀ ≤ x := fun x hx =>
      hS₂_ge x ((hL_mem x).mp (mem_oddIdx_subset (List.mem_of_head? hx)))
    exact prod_sq_abundancy_le_of_five_halves_step (oddIdx L) hod_chain hod_ge5 y₀ hy₀ hod_head

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

private lemma ne_thirteen_pow_of_lt_65 {u k : ℕ} (hu5 : 5 ≤ u) (hk : k < 4) :
    u ^ 2 + u + 1 ≠ 13 ^ k := by
  interval_cases k
  · nlinarith
  · nlinarith
  · exact not_sq_add_self_add_one_between (s := 12) (by decide) (by decide)
  · exact not_sq_add_self_add_one_between (s := 46) (by decide) (by decide)

private lemma ne_three_mul_thirteen_pow_of_odd_ge7 {s k : ℕ}
    (hs_odd : Odd s) (hs7 : 7 ≤ s) (hk : k < 7) :
    s ^ 2 + s + 1 ≠ 3 * 13 ^ k := by
  interval_cases k
  · omega
  · exact not_sq_add_self_add_one_between (s := 5) (by decide) (by decide)
  · intro heq
    have hmod : s % 2 = 1 := Nat.odd_iff.mp hs_odd
    rcases lt_trichotomy s 22 with hlt | rfl | hgt
    · have : s ^ 2 + s + 1 < 3 * 13 ^ 2 := by nlinarith
      omega
    · omega
    · have : 3 * 13 ^ 2 < s ^ 2 + s + 1 := by nlinarith
      omega
  · exact not_sq_add_self_add_one_between (s := 80) (by decide) (by decide)
  · exact not_sq_add_self_add_one_between (s := 292) (by decide) (by decide)
  · exact not_sq_add_self_add_one_between (s := 1054) (by decide) (by decide)
  · exact not_sq_add_self_add_one_between (s := 3804) (by decide) (by decide)

private def thirteenSixtyOneBounds : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 4), (0, 1, 7), (0, 2, 60), (0, 3, 475),
   (1, 0, 4), (1, 1, 27), (1, 2, 219), (1, 3, 1717),
   (2, 0, 12), (2, 1, 101), (2, 2, 792), (2, 3, 6193),
   (3, 0, 46), (3, 1, 365), (3, 2, 2858), (3, 3, 22330),
   (4, 0, 168), (4, 1, 1319), (4, 2, 10308), (4, 3, 80515),
   (5, 0, 608), (5, 1, 4758), (5, 2, 37169), (5, 3, 290303)]

private lemma thirteenSixtyOneBounds_cover :
    ∀ a ∈ Finset.range 6, ∀ b ∈ Finset.range 4,
      ∃ t ∈ thirteenSixtyOneBounds, t.1 = a ∧ t.2.1 = b := by
  decide

private lemma thirteenSixtyOneBounds_ok :
    ∀ t ∈ thirteenSixtyOneBounds,
      (t.2.2 = 4 ∨ t.2.2 ^ 2 + t.2.2 + 1 < 13 ^ t.1 * 61 ^ t.2.1) ∧
      13 ^ t.1 * 61 ^ t.2.1 < (t.2.2 + 1) ^ 2 + (t.2.2 + 1) + 1 := by
  decide

private lemma ne_thirteen_mul_sixtyOne_pow_of_ge5 {u α β : ℕ}
    (hu5 : 5 ≤ u) (hα : α < 6) (hβ : β < 4) :
    u ^ 2 + u + 1 ≠ 13 ^ α * 61 ^ β := by
  obtain ⟨t, ht_mem, hta, htb⟩ :=
    thirteenSixtyOneBounds_cover α (Finset.mem_range.mpr hα) β (Finset.mem_range.mpr hβ)
  obtain ⟨hlow, hhigh⟩ := thirteenSixtyOneBounds_ok t ht_mem
  rw [hta, htb] at hlow hhigh
  rcases hlow with hs4 | hlow
  · rw [hs4] at hhigh
    have hge31 : 31 ≤ u ^ 2 + u + 1 := by nlinarith
    omega
  · exact not_sq_add_self_add_one_between hlow hhigh

private lemma not_five_dvd_sq_add_self_add_one (x : ℕ) : ¬ 5 ∣ x ^ 2 + x + 1 := by
  have hmod : ∀ r : Fin 5, (r.1 ^ 2 + r.1 + 1) % 5 ≠ 0 := by decide
  intro hd
  have h0 : (x ^ 2 + x + 1) % 5 = 0 := Nat.mod_eq_zero_of_dvd hd
  have hr : ((x % 5) ^ 2 + (x % 5) + 1) % 5 = 0 := by
    simpa [Nat.add_mod, Nat.pow_mod] using h0
  exact hmod ⟨x % 5, Nat.mod_lt x (by decide)⟩ hr

private lemma not_five_dvd_sigma_thirteen_even_pow (m : ℕ) :
    ¬ 5 ∣ sigma 1 (13 ^ (2 * m)) := by
  rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 13),
    dvd_geom_sum_iff_remainder (t := 4) (by decide)]
  have hmod : (2 * m + 1) % 4 = 1 ∨ (2 * m + 1) % 4 = 3 := by omega
  rcases hmod with h | h <;> rw [h] <;> norm_num [Finset.sum_range_succ]

private lemma three_dvd_sigma_odd_pow_of_mod_three_eq_two {q a : ℕ}
    (hq : q.Prime) (hq3 : q % 3 = 2) (ha : Odd a) :
    3 ∣ sigma 1 (q ^ a) := by
  obtain ⟨k, rfl⟩ := ha
  rw [sigma_one_apply_prime_pow hq]
  have hsum : ∑ i ∈ Finset.range (2 * k + 1 + 1), q ^ i =
      (q + 1) * ∑ j ∈ Finset.range (k + 1), q ^ (2 * j) := by
    induction k with
    | zero =>
        simp [Finset.sum_range_succ]
        ring
    | succ k ih =>
        have heq : 2 * (k + 1) + 1 + 1 = (2 * k + 1 + 1) + 2 := by omega
        rw [heq, Finset.sum_range_add, ih, Finset.sum_range_succ (n := k + 1)]
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
        have hp1 : q ^ (2 * k + 1 + 1 + 0) = q ^ (2 * (k + 1)) := by ring_nf
        have hp2 : q ^ (2 * k + 1 + 1 + 1) = q * q ^ (2 * (k + 1)) := by ring_nf
        rw [hp1, hp2]
        ring
  rw [hsum]
  exact dvd_mul_of_dvd_left ⟨(q + 1) / 3, by omega⟩ _

private lemma five_adic_vacuum_contradiction {N r₀ : ℕ}
    (hN : N.Perfect) (h3_exp : N.factorization 3 = 2)
    (h5 : 5 ∈ N.primeFactors) (hr₀_exp : Even (N.factorization r₀))
    (hr₀_eq13 : r₀ = 13)
    (hpart : ∀ p ∈ N.primeFactors,
      p = 3 ∨ p = 5 ∨ p = r₀ ∨ p ∈ squareSources N) : False := by
  have hsum := factorization_eq_sum_sigma_factorizations hN (by decide : Odd 5) (by decide : Nat.Prime 5)
  have h5_pos : 0 < N.factorization 5 := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp h5)
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
  rcases hpart p hp_mem with rfl | rfl | rfl | hpS
  · rw [h3_exp] at h5_dvd
    have h13 : sigma 1 (3 ^ 2) = 13 := by
      rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
      decide
    rw [h13] at h5_dvd
    omega
  · have hmod := sigma_prime_pow_mod_self (by decide : Nat.Prime 5) (N.factorization 5)
    have h0 : sigma 1 (5 ^ N.factorization 5) % 5 = 0 := Nat.mod_eq_zero_of_dvd h5_dvd
    omega
  · rw [hr₀_eq13] at h5_dvd hr₀_exp
    obtain ⟨m, hm⟩ := hr₀_exp
    have h2m : N.factorization 13 = 2 * m := by omega
    rw [h2m] at h5_dvd
    exact not_five_dvd_sigma_thirteen_even_pow m h5_dvd
  · have hp_prime := Nat.prime_of_mem_primeFactors hp_mem
    have hp_exp : N.factorization p = 2 := (Finset.mem_filter.mp hpS).2.2
    rw [hp_exp, sigma_one_apply_prime_pow hp_prime, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero] at h5_dvd
    have hsq : 0 + p ^ 0 + p ^ 1 + p ^ 2 = p ^ 2 + p + 1 := by ring
    rw [hsq] at h5_dvd
    exact not_five_dvd_sq_add_self_add_one p h5_dvd

private lemma restrained_case_sq1_empty {N q r₀ : ℕ}
    (hN : N.Perfect) (hq : q ∈ N.primeFactors) (hq_prime : q.Prime) (hq_odd : Odd q)
    (hq4 : q % 4 = 1) (hq3 : q % 3 = 2)
    (h3_mem : 3 ∈ N.primeFactors) (h3_eq2 : N.factorization 3 = 2) (h3_ne_q : (3 : ℕ) ≠ q)
    (hr₀_mem : r₀ ∈ N.primeFactors) (hr₀_prime : r₀.Prime) (hr₀_ne3 : r₀ ≠ 3)
    (hr₀_ne_q : r₀ ≠ q) (hr₀_even : Even (N.factorization r₀))
    (hS₁_empty : squareSourcesOne N = ∅)
    (hprime_cases : ∀ p ∈ N.primeFactors,
      p = 3 ∨ p = q ∨ p = r₀ ∨ p ∈ squareSourcesOne N ∨ p ∈ squareSourcesTwo N)
    (hT_sub : ∀ w ∈ N.primeFactors.filter (fun w => w % 3 = 1), w = r₀ ∨ w ∈ squareSourcesOne N)
    (h13_T : 13 ∈ N.primeFactors.filter (fun w => w % 3 = 1))
    (hS₂_prop : ∀ u ∈ squareSourcesTwo N,
      u.Prime ∧ Odd u ∧ N.factorization u = 2 ∧ u % 3 = 2 ∧ 5 ≤ u ∧
      sigma 1 (u ^ N.factorization u) = u ^ 2 + u + 1 ∧
      (u ^ 2 + u + 1).primeFactors ⊆ N.primeFactors.filter (fun w => w % 3 = 1))
    (h3_not_S₂ : 3 ∉ squareSourcesTwo N) (hq_not_S₂ : q ∉ squareSourcesTwo N)
    (hr₀_not_S₂ : r₀ ∉ squareSourcesTwo N) : False := by
  let S₂ := squareSourcesTwo N
  have hr₀_eq13 : r₀ = 13 := by
    rcases hT_sub 13 h13_T with h13 | h13
    · exact h13.symm
    · rw [hS₁_empty] at h13
      simp at h13
  have hT_sub13 : N.primeFactors.filter (fun w => w % 3 = 1) ⊆ {13} := by
    intro w hw
    rcases hT_sub w hw with rfl | hw1
    · rw [hr₀_eq13]
      exact Finset.mem_singleton_self 13
    · rw [hS₁_empty] at hw1
      simp at hw1
  by_cases hq5 : q = 5
  · subst hq5
    exact five_adic_vacuum_contradiction hN h3_eq2 hq hr₀_even hr₀_eq13 fun p hp => by
      rcases hprime_cases p hp with rfl | rfl | rfl | hp1 | hp2
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · rw [hS₁_empty] at hp1
        simp at hp1
      · exact Or.inr (Or.inr (Or.inr (Finset.mem_filter.mp hp2).1))
  · have hq17 : 17 ≤ q := by
      have hq2 := Nat.odd_iff.mp hq_odd
      have hq_gt2 := hq_prime.two_le
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
    have hpart1 : N.primeFactors = insert 3 (insert q (insert r₀ S₂)) := by
      ext p
      simp only [Finset.mem_insert]
      constructor
      · intro hp
        rcases hprime_cases p hp with rfl | rfl | rfl | hp1 | hp2
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · rw [hS₁_empty] at hp1
          simp at hp1
        · exact Or.inr (Or.inr (Or.inr hp2))
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
    let P_S := ∏ u ∈ S₂, (u ^ 2 + u + 1)
    let Q_S := ∏ u ∈ S₂, u ^ 2
    have hN_eq : 3 ^ 2 * q ^ N.factorization q * r₀ ^ N.factorization r₀ * Q_S = N := by
      have hfac := Nat.prod_primeFactors_pow_factorization hN.2.ne'
      rw [hpart1, Finset.prod_insert h3_not_ins, Finset.prod_insert hq_not_ins,
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
      rw [hσN, hpart1, Finset.prod_insert h3_not_ins, Finset.prod_insert hq_not_ins,
        Finset.prod_insert hr₀_not_S₂, h3_eq2] at hmul
      have hS_prod : (∏ u ∈ S₂, sigma 1 (u ^ N.factorization u)) = P_S :=
        Finset.prod_congr rfl fun u hu => (hS₂_prop u hu).2.2.2.2.2.1
      rw [hS_prod] at hmul
      calc
        sigma 1 (3 ^ 2) * sigma 1 (q ^ N.factorization q) *
            sigma 1 (r₀ ^ N.factorization r₀) * P_S
            = sigma 1 (3 ^ 2) * (sigma 1 (q ^ N.factorization q) *
                (sigma 1 (r₀ ^ N.factorization r₀) * P_S)) := by ring
        _ = 2 * N := hmul.symm
    have h3_ratio : 9 * sigma 1 (3 ^ 2) ≤ 13 * 3 ^ 2 := by
      rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
      decide
    have hq_ratio : 16 * sigma 1 (q ^ N.factorization q) < 17 * q ^ N.factorization q :=
      sigma_prime_pow_ratio_lt hq_prime (by decide) (by omega)
    have hr_ratio : 12 * sigma 1 (r₀ ^ N.factorization r₀) ≤ 13 * r₀ ^ N.factorization r₀ :=
      (sigma_prime_pow_ratio_lt hr₀_prime (by decide) (by omega)).le
    have hP_pos : 0 < P_S := Finset.prod_pos fun u _ => by positivity
    have hS_ratio : 141 * P_S ≤ 145 * Q_S := by
      rcases S₂.eq_empty_or_nonempty with hemp | hne
      · simp [P_S, Q_S, hemp]
      · have h5 : ∀ u ∈ S₂, 5 ≤ u := fun u hu => (hS₂_prop u hu).2.2.2.2.1
        have hgap : ∀ u ∈ S₂, ∀ v ∈ S₂, u < v → 5 * u ^ 2 < v := by
          intro u hu v hv huv
          obtain ⟨_, hu_odd, _, hu3, _, _, _⟩ := hS₂_prop u hu
          obtain ⟨_, hv_odd, _, hv3, _, _, _⟩ := hS₂_prop v hv
          exact sq_add_self_add_one_prime_pow_gap (by decide : Nat.Prime 13) (by decide)
            hu_odd hv_odd hu3 hv3 huv (hS₂_pow u hu) (hS₂_pow v hv)
        have hgap_prod := prod_sq_abundancy_lt_of_five_sq_gap S₂ hne h5 hgap
        have hu₀_47 : 47 ≤ S₂.min' hne := hS₂_ge47 (S₂.min' hne) (S₂.min'_mem hne)
        exact sq_prod_ratio_le (by decide) hgap_prod (by omega)
    exact abundancy_contradiction4 hN.2 hσ_eq hN_eq
      (Nat.mul_pos (by decide) (sigma_pos _ _ (by decide))) h3_ratio
      hq_ratio
      (Nat.mul_pos (by decide) (sigma_pos _ _ (pow_ne_zero _ hr₀_prime.ne_zero))) hr_ratio
      (Nat.mul_pos (by decide) hP_pos) hS_ratio (by norm_num)

private lemma restrained_subcase_s1_eq13 {N q r₀ s₁ : ℕ}
    (hN : N.Perfect) (_hq : q ∈ N.primeFactors) (hq_prime : q.Prime) (hq_odd : Odd q)
    (hq3 : q % 3 = 2)
    (_h3_mem : 3 ∈ N.primeFactors) (h3_eq2 : N.factorization 3 = 2)
    (_hr₀_mem : r₀ ∈ N.primeFactors) (hr₀_prime : r₀.Prime)
    (_hs₁_mem : s₁ ∈ N.primeFactors) (hs₁_prime : s₁.Prime)
    (hs₁_exp2 : N.factorization s₁ = 2) (hs₁_sig : sigma 1 (s₁ ^ N.factorization s₁) = s₁ ^ 2 + s₁ + 1)
    (hs₁_eq : squareSourcesOne N = {s₁}) (hs₁_13 : s₁ = 13)
    (hT_sub : ∀ w ∈ N.primeFactors.filter (fun w => w % 3 = 1), w = r₀ ∨ w ∈ squareSourcesOne N)
    (hS₂_prop : ∀ u ∈ squareSourcesTwo N,
      u.Prime ∧ Odd u ∧ N.factorization u = 2 ∧ u % 3 = 2 ∧ 5 ≤ u ∧
      sigma 1 (u ^ N.factorization u) = u ^ 2 + u + 1 ∧
      (u ^ 2 + u + 1).primeFactors ⊆ N.primeFactors.filter (fun w => w % 3 = 1))
    (hpart2 : N.primeFactors = insert 3 (insert q (insert r₀ (insert s₁ (squareSourcesTwo N)))))
    (h3_not_ins : (3 : ℕ) ∉ insert q (insert r₀ (insert s₁ (squareSourcesTwo N))))
    (hq_not_ins : q ∉ insert r₀ (insert s₁ (squareSourcesTwo N)))
    (hr₀_not_ins : r₀ ∉ insert s₁ (squareSourcesTwo N))
    (hs₁_not_S₂ : s₁ ∉ squareSourcesTwo N) : False := by
  let S₂ := squareSourcesTwo N
  have h13_exp2 : N.factorization 13 = 2 := hs₁_13 ▸ hs₁_exp2
  have h169 : 169 ∣ N := by
    have hpow : 13 ^ 2 ∣ N :=
      ((by decide : Nat.Prime 13).pow_dvd_iff_le_factorization hN.2.ne').2 (by omega)
    simpa using hpow
  have h2197 : ¬ 2197 ∣ N := by
    intro h
    have hle3 : 3 ≤ N.factorization 13 :=
      ((by decide : Nat.Prime 13).pow_dvd_iff_le_factorization hN.2.ne').1 (by simpa using h)
    omega
  have h61_dvd : 61 ∣ N := sixtyOne_dvd_of_exact_thirteen_sq hN h169 h2197
  have h61_mem : 61 ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨by decide, h61_dvd, hN.2.ne'⟩
  have h61_T : 61 ∈ N.primeFactors.filter (fun w => w % 3 = 1) :=
    Finset.mem_filter.mpr ⟨h61_mem, by decide⟩
  have hr₀_eq61 : r₀ = 61 := by
    rcases hT_sub 61 h61_T with h61 | h61
    · exact h61.symm
    · rw [hs₁_eq, hs₁_13, Finset.mem_singleton] at h61
      omega
  have hT_sub_pair : N.primeFactors.filter (fun w => w % 3 = 1) ⊆ {13, 61} := by
    intro w hw
    rcases hT_sub w hw with rfl | hw1
    · rw [hr₀_eq61]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self 61)
    · rw [hs₁_eq, hs₁_13, Finset.mem_singleton] at hw1
      rw [hw1]
      exact Finset.mem_insert_self 13 {61}
  have hS₂_pow : ∀ u ∈ S₂,
      u ^ 2 + u + 1 =
        13 ^ (u ^ 2 + u + 1).factorization 13 * 61 ^ (u ^ 2 + u + 1).factorization 61 := by
    intro u hu
    exact eq_mul_pow_of_primeFactors_subset_pair (by positivity) (by decide : (13 : ℕ) ≠ 61)
      ((hS₂_prop u hu).2.2.2.2.2.2.trans hT_sub_pair)
  have hS₂_ge1048 : ∀ u ∈ S₂, 1048 ≤ u := by
    intro u hu
    by_contra! hu_lt
    have hu5 : 5 ≤ u := (hS₂_prop u hu).2.2.2.2.1
    have hpow := hS₂_pow u hu
    set α := (u ^ 2 + u + 1).factorization 13
    set β := (u ^ 2 + u + 1).factorization 61
    have hle_sum : 13 ^ α * 61 ^ β ≤ 1047 ^ 2 + 1047 + 1 := by
      rw [← hpow]
      nlinarith
    have hα6 : α < 6 := by
      have h13_le : 13 ^ α ≤ 13 ^ α * 61 ^ β := Nat.le_mul_of_pos_right _ (by positivity)
      have hlt : 13 ^ α < 13 ^ 6 := lt_of_le_of_lt (h13_le.trans hle_sum) (by norm_num)
      exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 13)).mp hlt
    have hβ4 : β < 4 := by
      have h61_le : 61 ^ β ≤ 13 ^ α * 61 ^ β := Nat.le_mul_of_pos_left _ (by positivity)
      have hlt : 61 ^ β < 61 ^ 4 := lt_of_le_of_lt (h61_le.trans hle_sum) (by norm_num)
      exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 61)).mp hlt
    exact ne_thirteen_mul_sixtyOne_pow_of_ge5 hu5 hα6 hβ4 hpow
  obtain ⟨P_ev_num, P_ev_den, P_od_num, P_od_den, hP_prod, hQ_prod, hP_ev_pos, hP_od_pos,
      hP_ev_bd, hP_od_bd⟩ :=
    smooth_pair_squareSourcesTwo_bounds
      (by decide : Nat.Prime 13) ⟨6, rfl⟩ (by decide)
      (by decide : Nat.Prime 61) ⟨30, rfl⟩ (by decide)
      (by decide)
      (fun u hu => (hS₂_prop u hu).2.1)
      (fun u hu => (hS₂_prop u hu).2.2.2.1)
      (fun u hu => (hS₂_prop u hu).2.2.2.2.1)
      hS₂_ge1048
      hS₂_pow
  have hN_eq : 3 ^ 2 * q ^ N.factorization q * r₀ ^ N.factorization r₀ *
      s₁ ^ 2 * P_ev_den * P_od_den = N := by
    have hfac := Nat.prod_primeFactors_pow_factorization hN.2.ne'
    rw [hpart2, Finset.prod_insert h3_not_ins, Finset.prod_insert hq_not_ins,
      Finset.prod_insert hr₀_not_ins, Finset.prod_insert hs₁_not_S₂, h3_eq2, hs₁_exp2] at hfac
    have hS_prod : (∏ u ∈ S₂, u ^ N.factorization u) = P_ev_den * P_od_den := by
      rw [← hQ_prod]
      exact Finset.prod_congr rfl fun u hu => by rw [(hS₂_prop u hu).2.2.1]
    rw [hS_prod] at hfac
    calc
      3 ^ 2 * q ^ N.factorization q * r₀ ^ N.factorization r₀ * s₁ ^ 2 * P_ev_den * P_od_den
          = 3 ^ 2 * (q ^ N.factorization q * (r₀ ^ N.factorization r₀ *
              (s₁ ^ 2 * (P_ev_den * P_od_den)))) := by ring
      _ = N := hfac.symm
  have hσ_eq : sigma 1 (3 ^ 2) * sigma 1 (q ^ N.factorization q) *
      sigma 1 (r₀ ^ N.factorization r₀) * sigma 1 (s₁ ^ N.factorization s₁) *
      P_ev_num * P_od_num = 2 * N := by
    have hσN : sigma 1 N = 2 * N :=
      (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN)
    have hmul : sigma 1 N = ∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p) :=
      isMultiplicative_sigma.multiplicative_factorization (sigma 1) hN.2.ne'
    rw [hσN, hpart2, Finset.prod_insert h3_not_ins, Finset.prod_insert hq_not_ins,
      Finset.prod_insert hr₀_not_ins, Finset.prod_insert hs₁_not_S₂, h3_eq2] at hmul
    have hS_prod : (∏ u ∈ S₂, sigma 1 (u ^ N.factorization u)) = P_ev_num * P_od_num := by
      rw [← hP_prod]
      exact Finset.prod_congr rfl fun u hu => (hS₂_prop u hu).2.2.2.2.2.1
    rw [hS_prod] at hmul
    calc
      sigma 1 (3 ^ 2) * sigma 1 (q ^ N.factorization q) *
          sigma 1 (r₀ ^ N.factorization r₀) * sigma 1 (s₁ ^ N.factorization s₁) *
          P_ev_num * P_od_num
          = sigma 1 (3 ^ 2) * (sigma 1 (q ^ N.factorization q) *
              (sigma 1 (r₀ ^ N.factorization r₀) * (sigma 1 (s₁ ^ N.factorization s₁) *
                (P_ev_num * P_od_num)))) := by ring
      _ = 2 * N := hmul.symm
  have h3_ratio : 9 * sigma 1 (3 ^ 2) ≤ 13 * 3 ^ 2 := by
    rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
    decide
  have hq5 : 5 ≤ q := by
    have hq_ge2 := hq_prime.two_le
    have hq_mod2 := Nat.odd_iff.mp hq_odd
    omega
  have hq_ratio : 4 * sigma 1 (q ^ N.factorization q) < 5 * q ^ N.factorization q :=
    sigma_prime_pow_ratio_lt hq_prime (by decide) (by omega)
  have hr_ratio : 60 * sigma 1 (r₀ ^ N.factorization r₀) ≤ 61 * r₀ ^ N.factorization r₀ :=
    (sigma_prime_pow_ratio_lt hr₀_prime (by decide) (by rw [hr₀_eq61])).le
  have hs₁_ratio : 169 * sigma 1 (s₁ ^ N.factorization s₁) ≤ 183 * s₁ ^ 2 := by
    rw [hs₁_sig, hs₁_13]
    norm_num
  exact abundancy_contradiction6 hN.2 hσ_eq hN_eq
    (Nat.mul_pos (by decide) (sigma_pos _ _ (by decide))) h3_ratio
    hq_ratio
    (Nat.mul_pos (by decide) (sigma_pos _ _ (pow_ne_zero _ hr₀_prime.ne_zero))) hr_ratio
    (Nat.mul_pos (by decide) (sigma_pos _ _ (pow_ne_zero _ hs₁_prime.ne_zero))) hs₁_ratio
    (Nat.mul_pos (by decide) hP_ev_pos) hP_ev_bd
    (Nat.mul_pos (by decide) hP_od_pos) hP_od_bd
    (by norm_num)

private lemma restrained_subcase_s1_ne13 {N q r₀ s₁ : ℕ}
    (hN : N.Perfect) (hq : q ∈ N.primeFactors) (hq_prime : q.Prime) (hq_odd : Odd q)
    (hq4 : q % 4 = 1) (hq3 : q % 3 = 2)
    (_h3_mem : 3 ∈ N.primeFactors) (h3_eq2 : N.factorization 3 = 2)
    (_hr₀_mem : r₀ ∈ N.primeFactors) (hr₀_prime : r₀.Prime) (hr₀_even : Even (N.factorization r₀))
    (_hs₁_mem : s₁ ∈ N.primeFactors) (hs₁_prime : s₁.Prime) (hs₁_odd : Odd s₁)
    (hs₁_mod3 : s₁ % 3 = 1) (hs₁_exp2 : N.factorization s₁ = 2)
    (hs₁_sig : sigma 1 (s₁ ^ N.factorization s₁) = s₁ ^ 2 + s₁ + 1)
    (hs₁_eq : squareSourcesOne N = {s₁}) (hs₁_13 : s₁ ≠ 13)
    (hprime_cases : ∀ p ∈ N.primeFactors,
      p = 3 ∨ p = q ∨ p = r₀ ∨ p ∈ squareSourcesOne N ∨ p ∈ squareSourcesTwo N)
    (hT_sub : ∀ w ∈ N.primeFactors.filter (fun w => w % 3 = 1), w = r₀ ∨ w ∈ squareSourcesOne N)
    (h13_T : 13 ∈ N.primeFactors.filter (fun w => w % 3 = 1))
    (hS₂_prop : ∀ u ∈ squareSourcesTwo N,
      u.Prime ∧ Odd u ∧ N.factorization u = 2 ∧ u % 3 = 2 ∧ 5 ≤ u ∧
      sigma 1 (u ^ N.factorization u) = u ^ 2 + u + 1 ∧
      (u ^ 2 + u + 1).primeFactors ⊆ N.primeFactors.filter (fun w => w % 3 = 1))
    (hpart2 : N.primeFactors = insert 3 (insert q (insert r₀ (insert s₁ (squareSourcesTwo N)))))
    (h3_not_ins : (3 : ℕ) ∉ insert q (insert r₀ (insert s₁ (squareSourcesTwo N))))
    (hq_not_ins : q ∉ insert r₀ (insert s₁ (squareSourcesTwo N)))
    (hr₀_not_ins : r₀ ∉ insert s₁ (squareSourcesTwo N))
    (hs₁_not_S₂ : s₁ ∉ squareSourcesTwo N) : False := by
  let S₂ := squareSourcesTwo N
  have hr₀_eq13 : r₀ = 13 := by
    rcases hT_sub 13 h13_T with h13 | h13
    · exact h13.symm
    · rw [hs₁_eq, Finset.mem_singleton] at h13
      exact (hs₁_13 h13.symm).elim
  by_cases hq5 : q = 5
  · subst hq5
    exact five_adic_vacuum_contradiction hN h3_eq2 hq hr₀_even hr₀_eq13 fun p hp => by
      rcases hprime_cases p hp with rfl | rfl | rfl | hp1 | hp2
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Finset.mem_filter.mp hp1).1))
      · exact Or.inr (Or.inr (Or.inr (Finset.mem_filter.mp hp2).1))
  · have hq17 : 17 ≤ q := by
      have hq2 := Nat.odd_iff.mp hq_odd
      have hq_gt2 := hq_prime.two_le
      omega
    have hT_sub_pair : N.primeFactors.filter (fun w => w % 3 = 1) ⊆ {13, s₁} := by
      intro w hw
      rcases hT_sub w hw with rfl | hw1
      · rw [hr₀_eq13]
        exact Finset.mem_insert_self 13 {s₁}
      · rw [hs₁_eq, Finset.mem_singleton] at hw1
        rw [hw1]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self s₁)
    have hs₁_ge7 : 7 ≤ s₁ := by
      have hs₁_ge2 := hs₁_prime.two_le
      have hs₁_mod2 := Nat.odd_iff.mp hs₁_odd
      omega
    have hs₁_sub : (s₁ ^ 2 + s₁ + 1).primeFactors ⊆ {3, 13} := by
      intro w hw
      obtain ⟨hw_prime, hw_dvd, _⟩ := Nat.mem_primeFactors.mp hw
      by_cases hw3 : w = 3
      · rw [hw3]
        exact Finset.mem_insert_self 3 {13}
      · have hsum_odd : Odd (s₁ ^ 2 + s₁ + 1) :=
          ((hs₁_odd.pow).add_odd hs₁_odd).add_odd (by decide : Odd 1)
        have hw_odd : Odd w := hsum_odd.of_dvd_nat hw_dvd
        have hw_mod3 : w % 3 = 1 :=
          (prime_dvd_sq_add_self_add_one hw_prime hw_dvd).resolve_left hw3
        have hwN : w ∣ N := by
          apply dvd_perfect_of_exact_prime_pow hN hs₁_prime (Nat.ordProj_dvd N s₁) _ hw_prime hw_odd
          · rw [← sigma_one_apply, hs₁_sig]
            exact hw_dvd
          · rw [hs₁_prime.pow_dvd_iff_le_factorization hN.2.ne']
            omega
        have hw_T : w ∈ N.primeFactors.filter (fun w => w % 3 = 1) :=
          Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hw_prime, hwN, hN.2.ne'⟩, hw_mod3⟩
        have hw_pair := hT_sub_pair hw_T
        rcases Finset.mem_insert.mp hw_pair with h13 | hs1_mem
        · rw [h13]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self 13)
        · exfalso
          rw [Finset.mem_singleton.mp hs1_mem] at hw_dvd
          have hmod_s1 : (s₁ ^ 2 + s₁ + 1) % s₁ = 1 := by
            have h1 : s₁ ^ 2 + s₁ + 1 = s₁ * (s₁ + 1) + 1 := by ring
            rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega : 1 < s₁)]
          have h0 : (s₁ ^ 2 + s₁ + 1) % s₁ = 0 := Nat.mod_eq_zero_of_dvd hw_dvd
          omega
    have hs₁_fac3 : (s₁ ^ 2 + s₁ + 1).factorization 3 = 1 := by
      obtain ⟨t, ht⟩ : ∃ t, s₁ = 3 * t + 1 := ⟨s₁ / 3, by omega⟩
      have hid : s₁ ^ 2 + s₁ + 1 = 3 * (3 * t ^ 2 + 3 * t + 1) := by
        rw [ht]; ring
      have hndvd : ¬ 3 ∣ (3 * t ^ 2 + 3 * t + 1) := by omega
      rw [hid, Nat.factorization_mul (by decide : 3 ≠ 0) (by omega), Finsupp.add_apply,
        Nat.prime_three.factorization_self, Nat.factorization_eq_zero_of_not_dvd hndvd]
    have hs₁_pow : s₁ ^ 2 + s₁ + 1 = 3 * 13 ^ (s₁ ^ 2 + s₁ + 1).factorization 13 :=
      eq_three_mul_pow_of_primeFactors_subset (by positivity) hs₁_fac3 hs₁_sub
    have hs₁_ge3806 : 3806 ≤ s₁ := by
      by_contra! hs₁_lt
      set k := (s₁ ^ 2 + s₁ + 1).factorization 13
      have hlt_pow : 3 * 13 ^ k < 3 * 13 ^ 7 := by
        calc
          3 * 13 ^ k = s₁ ^ 2 + s₁ + 1 := hs₁_pow.symm
          _ ≤ 3805 ^ 2 + 3805 + 1 := by nlinarith
          _ < 3 * 13 ^ 7 := by norm_num
      have hk7 : k < 7 :=
        (Nat.pow_lt_pow_iff_right (by decide : 1 < 13)).mp (Nat.lt_of_mul_lt_mul_left hlt_pow)
      exact ne_three_mul_thirteen_pow_of_odd_ge7 hs₁_odd hs₁_ge7 hk7 hs₁_pow
    have hS₂_pow : ∀ u ∈ S₂,
        u ^ 2 + u + 1 =
          13 ^ (u ^ 2 + u + 1).factorization 13 * s₁ ^ (u ^ 2 + u + 1).factorization s₁ := by
      intro u hu
      exact eq_mul_pow_of_primeFactors_subset_pair (by positivity) (Ne.symm hs₁_13)
        ((hS₂_prop u hu).2.2.2.2.2.2.trans hT_sub_pair)
    have hS₂_ge65 : ∀ u ∈ S₂, 65 ≤ u := by
      intro u hu
      by_contra! hu_lt
      obtain ⟨_, hu_odd, _, hu3, hu5, _, hsub_u⟩ := hS₂_prop u hu
      have hu2 : u % 2 = 1 := Nat.odd_iff.mp hu_odd
      have hu_le59 : u ≤ 59 := by omega
      have hnot_s₁ : s₁ ∉ (u ^ 2 + u + 1).primeFactors := by
        intro hmem
        have hdvd : s₁ ∣ u ^ 2 + u + 1 := Nat.dvd_of_mem_primeFactors hmem
        have hle_sum : s₁ ≤ u ^ 2 + u + 1 := Nat.le_of_dvd (by positivity) hdvd
        have hsum_le : u ^ 2 + u + 1 ≤ 59 ^ 2 + 59 + 1 := by nlinarith
        omega
      have hsub13 : (u ^ 2 + u + 1).primeFactors ⊆ {13} := by
        intro w hw
        have hw_pair := (hsub_u.trans hT_sub_pair) hw
        rcases Finset.mem_insert.mp hw_pair with h13 | hs1_mem
        · rw [h13]
          exact Finset.mem_singleton_self 13
        · exfalso
          rw [Finset.mem_singleton.mp hs1_mem] at hw
          exact hnot_s₁ hw
      have hpow13 := eq_pow_of_primeFactors_subset (by positivity) hsub13
      set α := (u ^ 2 + u + 1).factorization 13
      have hlt_pow : 13 ^ α < 13 ^ 4 := by
        calc
          13 ^ α = u ^ 2 + u + 1 := hpow13.symm
          _ ≤ 59 ^ 2 + 59 + 1 := by nlinarith
          _ < 13 ^ 4 := by norm_num
      have hα4 : α < 4 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 13)).mp hlt_pow
      exact ne_thirteen_pow_of_lt_65 hu5 hα4 hpow13
    obtain ⟨P_ev_num, P_ev_den, P_od_num, P_od_den, hP_prod, hQ_prod, hP_ev_pos, hP_od_pos,
        hP_ev_bd, hP_od_bd⟩ :=
      smooth_pair_squareSourcesTwo_bounds
        (by decide : Nat.Prime 13) ⟨6, rfl⟩ (by decide)
        hs₁_prime hs₁_odd hs₁_mod3
        (by decide : 5 ≤ 65)
        (fun u hu => (hS₂_prop u hu).2.1)
        (fun u hu => (hS₂_prop u hu).2.2.2.1)
        (fun u hu => (hS₂_prop u hu).2.2.2.2.1)
        hS₂_ge65
        hS₂_pow
    have hN_eq : 3 ^ 2 * q ^ N.factorization q * r₀ ^ N.factorization r₀ *
        s₁ ^ 2 * P_ev_den * P_od_den = N := by
      have hfac := Nat.prod_primeFactors_pow_factorization hN.2.ne'
      rw [hpart2, Finset.prod_insert h3_not_ins, Finset.prod_insert hq_not_ins,
        Finset.prod_insert hr₀_not_ins, Finset.prod_insert hs₁_not_S₂, h3_eq2, hs₁_exp2] at hfac
      have hS_prod : (∏ u ∈ S₂, u ^ N.factorization u) = P_ev_den * P_od_den := by
        rw [← hQ_prod]
        exact Finset.prod_congr rfl fun u hu => by rw [(hS₂_prop u hu).2.2.1]
      rw [hS_prod] at hfac
      calc
        3 ^ 2 * q ^ N.factorization q * r₀ ^ N.factorization r₀ * s₁ ^ 2 * P_ev_den * P_od_den
            = 3 ^ 2 * (q ^ N.factorization q * (r₀ ^ N.factorization r₀ *
                (s₁ ^ 2 * (P_ev_den * P_od_den)))) := by ring
        _ = N := hfac.symm
    have hσ_eq : sigma 1 (3 ^ 2) * sigma 1 (q ^ N.factorization q) *
        sigma 1 (r₀ ^ N.factorization r₀) * sigma 1 (s₁ ^ N.factorization s₁) *
        P_ev_num * P_od_num = 2 * N := by
      have hσN : sigma 1 N = 2 * N :=
        (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN)
      have hmul : sigma 1 N = ∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p) :=
        isMultiplicative_sigma.multiplicative_factorization (sigma 1) hN.2.ne'
      rw [hσN, hpart2, Finset.prod_insert h3_not_ins, Finset.prod_insert hq_not_ins,
        Finset.prod_insert hr₀_not_ins, Finset.prod_insert hs₁_not_S₂, h3_eq2] at hmul
      have hS_prod : (∏ u ∈ S₂, sigma 1 (u ^ N.factorization u)) = P_ev_num * P_od_num := by
        rw [← hP_prod]
        exact Finset.prod_congr rfl fun u hu => (hS₂_prop u hu).2.2.2.2.2.1
      rw [hS_prod] at hmul
      calc
        sigma 1 (3 ^ 2) * sigma 1 (q ^ N.factorization q) *
            sigma 1 (r₀ ^ N.factorization r₀) * sigma 1 (s₁ ^ N.factorization s₁) *
            P_ev_num * P_od_num
            = sigma 1 (3 ^ 2) * (sigma 1 (q ^ N.factorization q) *
                (sigma 1 (r₀ ^ N.factorization r₀) * (sigma 1 (s₁ ^ N.factorization s₁) *
                  (P_ev_num * P_od_num)))) := by ring
        _ = 2 * N := hmul.symm
    have h3_ratio : 9 * sigma 1 (3 ^ 2) ≤ 13 * 3 ^ 2 := by
      rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
      decide
    have hq_ratio : 16 * sigma 1 (q ^ N.factorization q) < 17 * q ^ N.factorization q :=
      sigma_prime_pow_ratio_lt hq_prime (by decide) (by omega)
    have hr_ratio : 12 * sigma 1 (r₀ ^ N.factorization r₀) ≤ 13 * r₀ ^ N.factorization r₀ :=
      (sigma_prime_pow_ratio_lt hr₀_prime (by decide) (by omega)).le
    have hs₁_ratio : 3806 ^ 2 * sigma 1 (s₁ ^ N.factorization s₁) ≤
        (3806 ^ 2 + 3806 + 1) * s₁ ^ 2 := by
      rw [hs₁_sig]
      nlinarith [hs₁_ge3806]
    exact abundancy_contradiction6 hN.2 hσ_eq hN_eq
      (Nat.mul_pos (by decide) (sigma_pos _ _ (by decide))) h3_ratio
      hq_ratio
      (Nat.mul_pos (by decide) (sigma_pos _ _ (pow_ne_zero _ hr₀_prime.ne_zero))) hr_ratio
      (Nat.mul_pos (by decide) (sigma_pos _ _ (pow_ne_zero _ hs₁_prime.ne_zero))) hs₁_ratio
      (Nat.mul_pos (by decide) hP_ev_pos) hP_ev_bd
      (Nat.mul_pos (by decide) hP_od_pos) hP_od_bd
      (by norm_num)

/-- **Restrained `3^2 ∥ N` Obstruction for `q ≡ 2 [MOD 3]`**:
Every restrained odd perfect number (`(largeSources N q).card ≤ 1`) whose Euler prime satisfies
`q ≡ 2 [MOD 3]` (hence `q ≡ 5 [MOD 12]`, including `q = 5`) must satisfy `3 ^ 4 ∣ N`. -/
theorem four_le_three_exponent_of_restrained_euler_two_mod_three
    {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hle : (largeSources N q).card ≤ 1) (hq3 : q % 3 = 2) :
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
  have h3_dvd : 3 ∣ N := three_dvd_of_largeSources_le_one ho hN hq hq4 he hev hle
  have h3_mem : 3 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3_dvd, hN.2.ne'⟩
  have h3_pos : 0 < N.factorization 3 := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp h3_mem)
  have h3_ne_q : (3 : ℕ) ≠ q := by omega
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
  obtain ⟨hr₀_mem, hr₀_ne3, hr₀_ne_q, hr₀_ge4⟩ := Finset.mem_filter.mp hr₀_mem_large
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_mem
  have hr₀_odd : Odd r₀ := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr₀_mem)
  have hr₀_even : Even (N.factorization r₀) := hev r₀ hr₀_ne_q
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
  -- 3-adic valuation balance: `(squareSourcesOne N).card ≤ 1`
  have hq_not_sq1 : q ∉ squareSourcesOne N := by
    intro hmem
    have h1 := (Finset.mem_filter.mp hmem).2
    omega
  have hsq1_sub : insert q (squareSourcesOne N) ⊆ N.primeFactors := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp1
    · exact hq
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp1).1).1
  have hq_sig3 : 1 ≤ (sigma 1 (q ^ N.factorization q)).factorization 3 := by
    have hq_exp_odd : Odd (N.factorization q) := Nat.odd_iff.mpr (by omega)
    have h3_dvd_sig := three_dvd_sigma_odd_pow_of_mod_three_eq_two hq_prime hq3 hq_exp_odd
    exact (Nat.prime_three.dvd_iff_one_le_factorization
      (sigma_pos _ _ (pow_ne_zero _ hq_prime.ne_zero)).ne').mp h3_dvd_sig
  have hsq1_sig3 : ∀ s ∈ squareSourcesOne N,
      1 ≤ (sigma 1 (s ^ N.factorization s)).factorization 3 := by
    intro s hs
    have hs_sq := (Finset.mem_filter.mp hs).1
    have hs_mem := (Finset.mem_filter.mp hs_sq).1
    have hs_prime := Nat.prime_of_mem_primeFactors hs_mem
    have hs_exp := (Finset.mem_filter.mp hs_sq).2.2
    have hs_mod3 := (Finset.mem_filter.mp hs).2
    have h3_dvd_sig : 3 ∣ sigma 1 (s ^ N.factorization s) := by
      rw [hs_exp, sigma_one_apply_prime_pow hs_prime, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_zero]
      have hsum_mod : (0 + s ^ 0 + s ^ 1 + s ^ 2) % 3 = 0 := by
        have h1 : 0 + s ^ 0 + s ^ 1 + s ^ 2 = s ^ 2 + s + 1 := by ring
        rw [h1, Nat.add_mod, Nat.add_mod (s ^ 2), Nat.pow_mod, hs_mod3]
      exact Nat.dvd_of_mod_eq_zero hsum_mod
    exact (Nat.prime_three.dvd_iff_one_le_factorization
      (sigma_pos _ _ (pow_ne_zero _ hs_prime.ne_zero)).ne').mp h3_dvd_sig
  have hsq1_card_le : (squareSourcesOne N).card ≤ 1 := by
    have hsum3 := factorization_eq_sum_sigma_factorizations hN (by decide : Odd 3) Nat.prime_three
    have hsub_sum : ∑ p ∈ insert q (squareSourcesOne N), (sigma 1 (p ^ N.factorization p)).factorization 3 ≤
        ∑ p ∈ N.primeFactors, (sigma 1 (p ^ N.factorization p)).factorization 3 :=
      Finset.sum_le_sum_of_subset hsq1_sub
    rw [← hsum3, h3_eq2, Finset.sum_insert hq_not_sq1] at hsub_sum
    have hsum_sq1 : (squareSourcesOne N).card ≤
        ∑ s ∈ squareSourcesOne N, (sigma 1 (s ^ N.factorization s)).factorization 3 := by
      calc
        (squareSourcesOne N).card = ∑ _s ∈ squareSourcesOne N, (1 : ℕ) := by simp
        _ ≤ ∑ s ∈ squareSourcesOne N, (sigma 1 (s ^ N.factorization s)).factorization 3 :=
          Finset.sum_le_sum hsq1_sig3
    omega
  -- Partition of `N.primeFactors`
  let S₁ := squareSourcesOne N
  let S₂ := squareSourcesTwo N
  have hS_union : squareSources N = S₁ ∪ S₂ := squareSources_eq_union_one_two N
  have hS_disj : Disjoint S₁ S₂ := squareSourcesOne_disjoint_two N
  have hprime_cases : ∀ p ∈ N.primeFactors,
      p = 3 ∨ p = q ∨ p = r₀ ∨ p ∈ S₁ ∨ p ∈ S₂ := by
    intro p hp
    by_cases hp3 : p = 3
    · exact Or.inl hp3
    · by_cases hpq : p = q
      · exact Or.inr (Or.inl hpq)
      · have hpos : 0 < N.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
        obtain ⟨k, hk⟩ := hev p hpq
        by_cases htwo : N.factorization p = 2
        · have hpS : p ∈ squareSources N := Finset.mem_filter.mpr ⟨hp, hp3, htwo⟩
          rw [hS_union, Finset.mem_union] at hpS
          rcases hpS with hp1 | hp2
          · exact Or.inr (Or.inr (Or.inr (Or.inl hp1)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr hp2)))
        · have hlarge_p : p ∈ largeSources N q :=
            Finset.mem_filter.mpr ⟨hp, hp3, hpq, by omega⟩
          rw [hr₀_eq, Finset.mem_singleton] at hlarge_p
          exact Or.inr (Or.inr (Or.inl hlarge_p))
  let T := N.primeFactors.filter (fun w => w % 3 = 1)
  have h13_T : 13 ∈ T := Finset.mem_filter.mpr ⟨h13_mem, by decide⟩
  have hT_sub : ∀ w ∈ T, w = r₀ ∨ w ∈ S₁ := by
    intro w hw
    obtain ⟨hw_mem, hw3⟩ := Finset.mem_filter.mp hw
    rcases hprime_cases w hw_mem with rfl | rfl | rfl | hw1 | hw2
    · omega
    · omega
    · exact Or.inl rfl
    · exact Or.inr hw1
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
      have heq3 := (Nat.dvd_prime hu_prime).mp hd3
      rcases heq3 with h1 | h3
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
  rcases Nat.eq_zero_or_pos S₁.card with hcard0 | hcard1
  · exact restrained_case_sq1_empty hN hq hq_prime hq_odd hq4 hq3 h3_mem h3_eq2 h3_ne_q
      hr₀_mem hr₀_prime hr₀_ne3 hr₀_ne_q hr₀_even (Finset.card_eq_zero.mp hcard0)
      hprime_cases hT_sub h13_T hS₂_prop h3_not_S₂ hq_not_S₂ hr₀_not_S₂
  · have hS₁_card_le : S₁.card ≤ 1 := hsq1_card_le
    have hS₁_card : S₁.card = 1 := by omega
    obtain ⟨s₁, hs₁_eq⟩ := Finset.card_eq_one.mp hS₁_card
    have hs₁_mem_sq1 : s₁ ∈ S₁ := by rw [hs₁_eq]; exact Finset.mem_singleton_self s₁
    have hs₁_sq := (Finset.mem_filter.mp hs₁_mem_sq1).1
    obtain ⟨hs₁_mem, hs₁_ne3, hs₁_exp2⟩ := Finset.mem_filter.mp hs₁_sq
    have hs₁_mod3 : s₁ % 3 = 1 := (Finset.mem_filter.mp hs₁_mem_sq1).2
    have hs₁_prime := Nat.prime_of_mem_primeFactors hs₁_mem
    have hs₁_odd : Odd s₁ := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hs₁_mem)
    have hs₁_ne_q : s₁ ≠ q := by intro h; subst h; exact hq_not_S hs₁_sq
    have hs₁_ne_r₀ : s₁ ≠ r₀ := by intro h; subst h; exact hr₀_not_S hs₁_sq
    have hs₁_not_S₂ : s₁ ∉ S₂ := fun h => (Finset.disjoint_left.mp hS_disj hs₁_mem_sq1) h
    have hs₁_sig : sigma 1 (s₁ ^ N.factorization s₁) = s₁ ^ 2 + s₁ + 1 := by
      rw [hs₁_exp2, sigma_one_apply_prime_pow hs₁_prime, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_zero]
      ring
    have hpart2 : N.primeFactors = insert 3 (insert q (insert r₀ (insert s₁ S₂))) := by
      ext p
      simp only [Finset.mem_insert]
      constructor
      · intro hp
        rcases hprime_cases p hp with rfl | rfl | rfl | hp1 | hp2
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · rw [hs₁_eq, Finset.mem_singleton] at hp1
          exact Or.inr (Or.inr (Or.inr (Or.inl hp1)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr hp2)))
      · rintro (rfl | rfl | rfl | rfl | hp2)
        · exact h3_mem
        · exact hq
        · exact hr₀_mem
        · exact hs₁_mem
        · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp2).1).1
    have h3_not_ins : (3 : ℕ) ∉ insert q (insert r₀ (insert s₁ S₂)) := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨h3_ne_q, hr₀_ne3.symm, hs₁_ne3.symm, h3_not_S₂⟩
    have hq_not_ins : q ∉ insert r₀ (insert s₁ S₂) := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨hr₀_ne_q.symm, hs₁_ne_q.symm, hq_not_S₂⟩
    have hr₀_not_ins : r₀ ∉ insert s₁ S₂ := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨hs₁_ne_r₀.symm, hr₀_not_S₂⟩
    by_cases hs₁_13 : s₁ = 13
    · exact restrained_subcase_s1_eq13 hN hq hq_prime hq_odd hq3 h3_mem h3_eq2 hr₀_mem hr₀_prime
        hs₁_mem hs₁_prime hs₁_exp2 hs₁_sig hs₁_eq hs₁_13 hT_sub hS₂_prop
        hpart2 h3_not_ins hq_not_ins hr₀_not_ins hs₁_not_S₂
    · exact restrained_subcase_s1_ne13 hN hq hq_prime hq_odd hq4 hq3 h3_mem h3_eq2
        hr₀_mem hr₀_prime hr₀_even hs₁_mem hs₁_prime hs₁_odd hs₁_mod3 hs₁_exp2 hs₁_sig
        hs₁_eq hs₁_13 hprime_cases hT_sub h13_T hS₂_prop hpart2 h3_not_ins hq_not_ins
        hr₀_not_ins hs₁_not_S₂

/-- Specialization to Euler prime `q = 5`: every restrained odd perfect number with `q = 5`
satisfies `4 ≤ N.factorization 3` and `81 ∣ N`. -/
theorem four_le_three_exponent_of_restrained_euler_five
    {N : ℕ} (ho : Odd N) (hN : N.Perfect)
    (h5 : 5 ∈ N.primeFactors) (he : N.factorization 5 % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ 5 → Even (N.factorization r))
    (hle : (largeSources N 5).card ≤ 1) :
    4 ≤ N.factorization 3 ∧ 81 ∣ N :=
  four_le_three_exponent_of_restrained_euler_two_mod_three
    ho hN h5 (by decide) he hev hle (by decide)

end OddPerfect
