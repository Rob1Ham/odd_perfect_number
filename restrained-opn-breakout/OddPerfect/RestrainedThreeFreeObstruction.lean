module

public import OddPerfect.RestrainedExponents
public import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Three-Free Restrained Abundancy Obstruction (`OddPerfect.RestrainedThreeFreeObstruction`)

Doubly-exponential telescoping abundancy elimination of three-free restrained odd perfect
candidates (`¬ 3 ∣ N`, `(largeSources N q).card ≤ 1`), forcing both `q % 12 = 1` and `r₀ % 3 = 1`
(together with `13 ≤ q`, `7 ≤ r₀`, `N.factorization r₀ % 3 ≠ 2`, and `16 ≤ N.factorization r₀`
when `N.factorization q = 1`).
-/

public section

namespace OddPerfect

open ArithmeticFunction

private lemma nat_mul_lt_mul {a b c d : ℕ} (h1 : a < b) (h2 : c < d) : a * c < b * d :=
  lt_of_le_of_lt (Nat.mul_le_mul_right c h1.le) (Nat.mul_lt_mul_of_pos_left h2 (by omega))

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

private lemma sq_prod_ratio_lt {u₀ P Q c₁ c₂ : ℕ} (hc₁ : 0 < c₁)
    (hgap_prod : 3 * u₀ * P < (3 * u₀ + 4) * Q)
    (hcoef : c₁ * (3 * u₀ + 4) ≤ c₂ * (3 * u₀)) :
    c₁ * P < c₂ * Q := by
  have h1 : (3 * u₀) * (c₁ * P) < (3 * u₀) * (c₂ * Q) := by
    calc
      (3 * u₀) * (c₁ * P) = c₁ * (3 * u₀ * P) := by ring
      _ < c₁ * ((3 * u₀ + 4) * Q) := Nat.mul_lt_mul_of_pos_left hgap_prod hc₁
      _ = (c₁ * (3 * u₀ + 4)) * Q := by ring
      _ ≤ (c₂ * (3 * u₀)) * Q := Nat.mul_le_mul_right Q hcoef
      _ = (3 * u₀) * (c₂ * Q) := by ring
  exact Nat.lt_of_mul_lt_mul_left h1

private lemma abundancy_contradiction {N σq σr P q_pow r_pow Q cq dq cr dr cs ds : ℕ}
    (_hN_pos : 0 < N)
    (hσ_eq : σq * σr * P = 2 * N)
    (hN_eq : q_pow * r_pow * Q = N)
    (hq : cq * σq < dq * q_pow)
    (hr : cr * σr < dr * r_pow)
    (hs : cs * P < ds * Q)
    (hineq : dq * dr * ds ≤ 2 * (cq * cr * cs)) : False := by
  have hprod := nat_mul_lt_mul (nat_mul_lt_mul hq hr) hs
  have hLHS : (cq * σq) * (cr * σr) * (cs * P) = (cq * cr * cs) * (σq * σr * P) := by ring
  have hRHS : (dq * q_pow) * (dr * r_pow) * (ds * Q) = (dq * dr * ds) * (q_pow * r_pow * Q) := by
    ring
  rw [hLHS, hRHS, hσ_eq, hN_eq] at hprod
  have hle : (dq * dr * ds) * N ≤ (2 * (cq * cr * cs)) * N := Nat.mul_le_mul_right N hineq
  have hlt : (2 * (cq * cr * cs)) * N < (2 * (cq * cr * cs)) * N := by
    calc
      (2 * (cq * cr * cs)) * N = (cq * cr * cs) * (2 * N) := by ring
      _ < (dq * dr * ds) * N := hprod
      _ ≤ (2 * (cq * cr * cs)) * N := hle
  exact lt_irrefl _ hlt

/-- If two odd primes `u < v` with `u ≡ v ≡ 2 [MOD 3]` both map `x ↦ x^2 + x + 1` into powers of
the same prime `P ≡ 1 [MOD 3]`, then `5 * u ^ 2 < v`. -/
theorem sq_add_self_add_one_prime_pow_gap {P u v a b : ℕ}
    (hP : P.Prime) (hP3 : P % 3 = 1) (hu_odd : Odd u) (hv_odd : Odd v)
    (hu3 : u % 3 = 2) (hv3 : v % 3 = 2) (huv : u < v)
    (hua : u ^ 2 + u + 1 = P ^ a) (hvb : v ^ 2 + v + 1 = P ^ b) :
    5 * u ^ 2 < v := by
  have hu2 : u % 2 = 1 := Nat.odd_iff.mp hu_odd
  have hv2 : v % 2 = 1 := Nat.odd_iff.mp hv_odd
  have hu1 : 1 ≤ u := by omega
  have ha_pos : 1 ≤ a := by
    by_contra! ha0
    have ha_eq : a = 0 := by omega
    rw [ha_eq, pow_zero] at hua
    nlinarith [hu1]
  have hlt_pow : P ^ a < P ^ b := by
    rw [← hua, ← hvb]
    obtain ⟨d, rfl⟩ : ∃ d, v = u + d + 1 := ⟨v - u - 1, by omega⟩
    nlinarith
  have hab : a ≤ b := ((Nat.pow_lt_pow_iff_right hP.one_lt).mp hlt_pow).le
  have hprod_eq : (v - u) * (u + v + 1) + (u ^ 2 + u + 1) = v ^ 2 + v + 1 := by
    obtain ⟨d, hd⟩ : ∃ d, v = u + d := ⟨v - u, by omega⟩
    have hd_sub : v - u = d := by omega
    rw [hd_sub, hd]
    ring
  have hPa_dvd : P ^ a ∣ (v - u) * (u + v + 1) := by
    have hpab : P ^ a ∣ P ^ b := pow_dvd_pow P hab
    rw [← hvb, ← hprod_eq] at hpab
    have hPa_u : P ^ a ∣ u ^ 2 + u + 1 := by rw [hua]
    exact (Nat.dvd_add_iff_left hPa_u).mpr hpab
  have hcop : Nat.Coprime (P ^ a) (v - u) ∨ Nat.Coprime (P ^ a) (u + v + 1) := by
    by_cases h1 : P ∣ v - u
    · by_cases h2 : P ∣ u + v + 1
      · exfalso
        have h2u1 : P ∣ 2 * u + 1 := by
          obtain ⟨k₁, hk₁⟩ := h1
          obtain ⟨k₂, hk₂⟩ := h2
          have hle_uv : v - u ≤ u + v + 1 := by omega
          have hk : k₁ ≤ k₂ := by
            by_contra! hk_lt
            have : P * k₂ < P * k₁ := Nat.mul_lt_mul_of_pos_left hk_lt hP.pos
            omega
          refine ⟨k₂ - k₁, ?_⟩
          have hsum : P * (k₂ - k₁) + P * k₁ = P * k₂ := by
            rw [← mul_add, Nat.sub_add_cancel hk]
          rw [← hk₁, ← hk₂] at hsum
          omega
        have hsq_dvd : P ∣ (2 * u + 1) ^ 2 := by
          rw [sq]
          exact dvd_mul_of_dvd_left h2u1 (2 * u + 1)
        have h4Pa : P ∣ 4 * P ^ a :=
          dvd_mul_of_dvd_right (dvd_pow_self P (by omega : a ≠ 0)) 4
        have hsq_eq : (2 * u + 1) ^ 2 + 3 = 4 * P ^ a := by
          rw [← hua]
          ring
        have hP3_dvd : P ∣ 3 := by
          obtain ⟨m₁, hm₁⟩ := hsq_dvd
          obtain ⟨m₂, hm₂⟩ := h4Pa
          have hm : m₁ ≤ m₂ := by
            by_contra! hm_lt
            have : P * m₂ < P * m₁ := Nat.mul_lt_mul_of_pos_left hm_lt hP.pos
            omega
          refine ⟨m₂ - m₁, ?_⟩
          have hsum : P * (m₂ - m₁) + P * m₁ = P * m₂ := by
            rw [← mul_add, Nat.sub_add_cancel hm]
          rw [← hm₁, ← hm₂] at hsum
          omega
        have hle3 : P ≤ 3 := Nat.le_of_dvd (by decide) hP3_dvd
        have hge2 : 2 ≤ P := hP.two_le
        omega
      · exact Or.inr (hP.coprime_pow_of_not_dvd h2).symm
    · exact Or.inl (hP.coprime_pow_of_not_dvd h1).symm
  rcases hcop with hcop1 | hcop2
  · have hdvd_sum : P ^ a ∣ u + v + 1 := hcop1.dvd_of_dvd_mul_left hPa_dvd
    obtain ⟨m, hm⟩ := hdvd_sum
    have hP_mod2 : P % 2 = 1 := by
      have hP_ne2 : P ≠ 2 := by intro h; rw [h] at hP3; omega
      exact Nat.odd_iff.mp (hP.odd_of_ne_two hP_ne2)
    have hPa2 : P ^ a % 2 = 1 := by
      have h1 : P ^ a ≡ 1 ^ a [MOD 2] := Nat.ModEq.pow a hP_mod2
      change P ^ a % 2 = 1 ^ a % 2 at h1
      simpa using h1
    have hPa3 : P ^ a % 3 = 1 := by
      have h1 : P ^ a ≡ 1 ^ a [MOD 3] := Nat.ModEq.pow a hP3
      change P ^ a % 3 = 1 ^ a % 3 at h1
      simpa using h1
    have hPa6 : P ^ a % 6 = 1 := by omega
    have hm_mod6 : m % 6 = 5 := by
      have h1 : (P ^ a * m) % 6 = 5 := by rw [← hm]; omega
      rw [Nat.mul_mod, hPa6, one_mul, Nat.mod_mod] at h1
      exact h1
    have hm5 : 5 ≤ m := by omega
    have hmul : 5 * P ^ a ≤ P ^ a * m := by
      rw [mul_comm 5 (P ^ a)]
      exact Nat.mul_le_mul_left (P ^ a) hm5
    rw [← hm, ← hua] at hmul
    omega
  · have hdvd_sub : P ^ a ∣ v - u := hcop2.dvd_of_dvd_mul_right hPa_dvd
    obtain ⟨c, hc⟩ := hdvd_sub
    have hc_pos : 0 < c := by
      by_contra! hc0
      have : c = 0 := by omega
      rw [this, mul_zero] at hc
      omega
    have h6_sub : 6 ∣ v - u := ⟨(v - u) / 6, by omega⟩
    have hP_not2 : ¬ P ∣ 2 := fun h => by
      have := Nat.le_of_dvd (by decide) h
      have := hP.two_le
      omega
    have hP_not3 : ¬ P ∣ 3 := fun h => by
      have := Nat.le_of_dvd (by decide) h
      have := hP.two_le
      omega
    have hcop6 : Nat.Coprime 6 (P ^ a) :=
      ((hP.coprime_iff_not_dvd.mpr hP_not2).symm.mul_left
        (hP.coprime_iff_not_dvd.mpr hP_not3).symm).pow_right a
    have h6c : 6 ∣ c := hcop6.dvd_of_dvd_mul_left (hc ▸ h6_sub)
    have hc6 : 6 ≤ c := Nat.le_of_dvd hc_pos h6c
    have hmul : 6 * P ^ a ≤ P ^ a * c := by
      rw [mul_comm 6 (P ^ a)]
      exact Nat.mul_le_mul_left (P ^ a) hc6
    rw [← hc, ← hua] at hmul
    omega

/-- Doubly-exponential telescoping abundancy bound for a nonempty finite set `S ⊆ [5, ∞)`
satisfying the gap `u < v → 5 * u ^ 2 < v`. -/
theorem prod_sq_abundancy_lt_of_five_sq_gap (S : Finset ℕ) (hne : S.Nonempty)
    (h5 : ∀ u ∈ S, 5 ≤ u) (hgap : ∀ u ∈ S, ∀ v ∈ S, u < v → 5 * u ^ 2 < v) :
    3 * S.min' hne * (∏ u ∈ S, (u ^ 2 + u + 1)) < (3 * S.min' hne + 4) * ∏ u ∈ S, u ^ 2 := by
  suffices h : ∀ n : ℕ, ∀ S : Finset ℕ, S.card = n → ∀ (hne : S.Nonempty),
      (∀ u ∈ S, 5 ≤ u) → (∀ u ∈ S, ∀ v ∈ S, u < v → 5 * u ^ 2 < v) →
      3 * S.min' hne * (∏ u ∈ S, (u ^ 2 + u + 1)) < (3 * S.min' hne + 4) * ∏ u ∈ S, u ^ 2 by
    exact h S.card S rfl hne h5 hgap
  intro n
  refine Nat.strong_induction_on n fun n ih => ?_
  intro S hcard hne h5 hgap
  let u₀ := S.min' hne
  have hu₀ : u₀ ∈ S := S.min'_mem hne
  have hu₀5 : 5 ≤ u₀ := h5 u₀ hu₀
  have hprod1 : (∏ u ∈ S, (u ^ 2 + u + 1)) =
      (u₀ ^ 2 + u₀ + 1) * ∏ u ∈ S.erase u₀, (u ^ 2 + u + 1) :=
    (Finset.mul_prod_erase S (fun u => u ^ 2 + u + 1) hu₀).symm
  have hprod2 : (∏ u ∈ S, u ^ 2) = u₀ ^ 2 * ∏ u ∈ S.erase u₀, u ^ 2 :=
    (Finset.mul_prod_erase S (fun u => u ^ 2) hu₀).symm
  change 3 * u₀ * (∏ u ∈ S, (u ^ 2 + u + 1)) < (3 * u₀ + 4) * ∏ u ∈ S, u ^ 2
  rw [hprod1, hprod2]
  rcases (S.erase u₀).eq_empty_or_nonempty with hemp | hne'
  · rw [hemp, Finset.prod_empty, Finset.prod_empty, mul_one, mul_one]
    obtain ⟨a, ha⟩ : ∃ a, u₀ = 5 + a := ⟨u₀ - 5, by omega⟩
    rw [ha]
    have hdiff : (3 * (5 + a) + 4) * (5 + a) ^ 2 =
        3 * (5 + a) * ((5 + a) ^ 2 + (5 + a) + 1) + (10 + 7 * a + a ^ 2) := by ring
    omega
  · let S' := S.erase u₀
    have hcard' : S'.card < n := by
      rw [← hcard]
      exact Finset.card_erase_lt_of_mem hu₀
    have h5' : ∀ u ∈ S', 5 ≤ u := fun u hu => h5 u (Finset.mem_of_mem_erase hu)
    have hgap' : ∀ u ∈ S', ∀ v ∈ S', u < v → 5 * u ^ 2 < v :=
      fun u hu v hv huv => hgap u (Finset.mem_of_mem_erase hu) v (Finset.mem_of_mem_erase hv) huv
    have hih := ih S'.card hcard' S' rfl hne' h5' hgap'
    let u₁ := S'.min' hne'
    have hu₁' : u₁ ∈ S' := S'.min'_mem hne'
    have hu₁ : u₁ ∈ S := Finset.mem_of_mem_erase hu₁'
    have hu₀_le : u₀ ≤ u₁ := S.min'_le u₁ hu₁
    have hu₁_ne : u₁ ≠ u₀ := Finset.ne_of_mem_erase hu₁'
    have hu₀₁_lt : u₀ < u₁ := lt_of_le_of_ne hu₀_le hu₁_ne.symm
    have hu₀₁ : 5 * u₀ ^ 2 + 1 ≤ u₁ := hgap u₀ hu₀ u₁ hu₁ hu₀₁_lt
    have hle : 3 * u₀ * (u₀ ^ 2 + u₀ + 1) * (3 * u₁ + 4) ≤ 3 * u₁ * (3 * u₀ + 4) * u₀ ^ 2 := by
      obtain ⟨a, ha⟩ : ∃ a, u₀ = 5 + a := ⟨u₀ - 5, by omega⟩
      have hu₀₁' : 5 * (5 + a) ^ 2 + 1 ≤ u₁ := by rwa [ha] at hu₀₁
      obtain ⟨b, hb⟩ : ∃ b, u₁ = 5 * (5 + a) ^ 2 + 1 + b :=
        ⟨u₁ - (5 * (5 + a) ^ 2 + 1), by omega⟩
      rw [ha, hb]
      have hdiff : 3 * (5 * (5 + a) ^ 2 + 1 + b) * (3 * (5 + a) + 4) * (5 + a) ^ 2 =
          3 * (5 + a) * ((5 + a) ^ 2 + (5 + a) + 1) * (3 * (5 * (5 + a) ^ 2 + 1 + b) + 4) +
          3 * (5 + a) * (128 + 182 * a + 56 * a ^ 2 + 5 * a ^ 3 + (2 + a) * b) := by ring
      omega
    let P₁ := ∏ u ∈ S', (u ^ 2 + u + 1)
    let Q₁ := ∏ u ∈ S', u ^ 2
    have hih' : 3 * u₁ * P₁ < (3 * u₁ + 4) * Q₁ := hih
    have hpos_coef : 0 < 3 * u₀ * (u₀ ^ 2 + u₀ + 1) :=
      Nat.mul_pos (by omega) (by nlinarith [hu₀5])
    have hstep1 : (3 * u₁) * (3 * u₀ * ((u₀ ^ 2 + u₀ + 1) * P₁)) <
        (3 * u₀ * (u₀ ^ 2 + u₀ + 1) * (3 * u₁ + 4)) * Q₁ := by
      calc
        (3 * u₁) * (3 * u₀ * ((u₀ ^ 2 + u₀ + 1) * P₁))
            = (3 * u₀ * (u₀ ^ 2 + u₀ + 1)) * (3 * u₁ * P₁) := by ring
        _ < (3 * u₀ * (u₀ ^ 2 + u₀ + 1)) * ((3 * u₁ + 4) * Q₁) :=
            Nat.mul_lt_mul_of_pos_left hih' hpos_coef
        _ = (3 * u₀ * (u₀ ^ 2 + u₀ + 1) * (3 * u₁ + 4)) * Q₁ := by ring
    have hstep2 : (3 * u₀ * (u₀ ^ 2 + u₀ + 1) * (3 * u₁ + 4)) * Q₁ ≤
        (3 * u₁) * ((3 * u₀ + 4) * (u₀ ^ 2 * Q₁)) := by
      calc
        (3 * u₀ * (u₀ ^ 2 + u₀ + 1) * (3 * u₁ + 4)) * Q₁
            ≤ (3 * u₁ * (3 * u₀ + 4) * u₀ ^ 2) * Q₁ := Nat.mul_le_mul_right Q₁ hle
        _ = (3 * u₁) * ((3 * u₀ + 4) * (u₀ ^ 2 * Q₁)) := by ring
    exact Nat.lt_of_mul_lt_mul_left (lt_of_lt_of_le hstep1 hstep2)

/-- In the three-free restrained regime (`¬ 3 ∣ N`, `(largeSources N q).card ≤ 1`),
doubly-exponential telescoping abundancy eliminates every candidate unless `q % 12 = 1`
and `r₀ % 3 = 1`, with `13 ≤ q`, `7 ≤ r₀`, and `N.factorization r₀ % 3 ≠ 2`. -/
theorem restrained_three_free_forces_both_one_mod_three {N q : ℕ} (ho : Odd N)
    (hN : N.Perfect) (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1)
    (he : N.factorization q % 4 = 1) (hev : ∀ r, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) (hle : (largeSources N q).card ≤ 1) :
    ∃ r₀, largeSources N q = {r₀} ∧ q % 12 = 1 ∧ r₀ % 3 = 1 ∧ 13 ≤ q ∧ 7 ≤ r₀ ∧
      N.factorization r₀ % 3 ≠ 2 := by
  obtain ⟨r₀, hr₀, _, _⟩ := restrained_three_free_bounds ho hN hq hq4 he hev h3 hle
  have hr₀_mem_large : r₀ ∈ largeSources N q := by rw [hr₀]; exact Finset.mem_singleton_self r₀
  obtain ⟨hr₀_mem, hr₀3, hr₀q, hr₀_exp⟩ := Finset.mem_filter.mp hr₀_mem_large
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_mem
  have hr₀_odd : Odd r₀ := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr₀_mem)
  have hr₀5 : 5 ≤ r₀ := by
    have := hr₀_prime.two_le
    have := Nat.odd_iff.mp hr₀_odd
    omega
  have h3not : 3 ∉ N.primeFactors := fun h => h3 (Nat.dvd_of_mem_primeFactors h)
  have hsq1_zero : (squareSourcesOne N).card = 0 := by
    have h3zero : N.factorization 3 = 0 := Finsupp.notMem_support_iff.mp h3not
    have := squareSourcesOne_card_le_three_exponent hN
    omega
  let S := squareSources N
  have hpart : N.primeFactors = insert q (insert r₀ S) := by
    ext r
    simp only [Finset.mem_insert, S, squareSources, Finset.mem_filter]
    constructor
    · intro hr
      by_cases hrq : r = q
      · exact Or.inl hrq
      · have hr3 : r ≠ 3 := fun h => h3not (h ▸ hr)
        have hpos : 0 < N.factorization r := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
        obtain ⟨k, hk⟩ := hev r hrq
        by_cases htwo : N.factorization r = 2
        · exact Or.inr (Or.inr ⟨hr, hr3, htwo⟩)
        · have hlarge_r : r ∈ largeSources N q :=
            Finset.mem_filter.mpr ⟨hr, hr3, hrq, by omega⟩
          rw [hr₀, Finset.mem_singleton] at hlarge_r
          exact Or.inr (Or.inl hlarge_r)
    · rintro (rfl | rfl | ⟨hr, _, _⟩)
      · exact hq
      · exact hr₀_mem
      · exact hr
  have hr₀_not_S : r₀ ∉ S := by
    intro h
    have := (Finset.mem_filter.mp h).2.2
    omega
  have hq_not_ins : q ∉ insert r₀ S := by
    intro h
    rcases Finset.mem_insert.mp h with hqr | hqS
    · exact hr₀q hqr.symm
    · have := (Finset.mem_filter.mp hqS).2.2
      omega
  have hS_ne : S.Nonempty := by
    have h8 := eight_le_distinct_prime_factor_count_of_three_free ho hN h3
    rw [hpart, Finset.card_insert_of_notMem hq_not_ins, Finset.card_insert_of_notMem hr₀_not_S] at h8
    exact Finset.card_pos.mp (by omega)
  have hS_prop : ∀ u ∈ S, u.Prime ∧ Odd u ∧ u ≠ 3 ∧ u ≠ q ∧ N.factorization u = 2 ∧
      u % 3 = 2 ∧ 5 ≤ u ∧ normalizedSquareSum u = u ^ 2 + u + 1 := by
    intro u hu
    obtain ⟨hu_mem, hu3, hu_exp2⟩ := Finset.mem_filter.mp hu
    have hup := Nat.prime_of_mem_primeFactors hu_mem
    have hu_odd := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hu_mem)
    have huq : u ≠ q := fun h => by subst h; omega
    have hu_mod3 : u % 3 = 2 := by
      by_contra! hne2
      have h0or1 : u % 3 = 0 ∨ u % 3 = 1 := by omega
      rcases h0or1 with h0 | h1
      · have hd3 : 3 ∣ u := Nat.dvd_of_mod_eq_zero h0
        have heq3 := (Nat.dvd_prime hup).mp hd3
        have := hup.two_le
        omega
      · have hu_sq1 : u ∈ squareSourcesOne N := Finset.mem_filter.mpr ⟨hu, h1⟩
        have hpos : 0 < (squareSourcesOne N).card := Finset.card_pos.mpr ⟨u, hu_sq1⟩
        omega
    have hu5 : 5 ≤ u := by
      have := hup.two_le
      have := Nat.odd_iff.mp hu_odd
      omega
    have hu_norm : normalizedSquareSum u = u ^ 2 + u + 1 := by
      rw [normalizedSquareSum, ite_eq_right (by omega)]
    exact ⟨hup, hu_odd, hu3, huq, hu_exp2, hu_mod3, hu5, hu_norm⟩
  have hS_ge5 : ∀ u ∈ S, 5 ≤ u := fun u hu => (hS_prop u hu).2.2.2.2.2.2.1
  have hN_eq : q ^ N.factorization q * r₀ ^ N.factorization r₀ * (∏ u ∈ S, u ^ 2) = N := by
    have hfac := Nat.prod_primeFactors_pow_factorization hN.2.ne'
    rw [hpart, Finset.prod_insert hq_not_ins, Finset.prod_insert hr₀_not_S] at hfac
    have hS_prod : (∏ u ∈ S, u ^ N.factorization u) = ∏ u ∈ S, u ^ 2 :=
      Finset.prod_congr rfl fun u hu => by rw [(hS_prop u hu).2.2.2.2.1]
    rw [hS_prod, ← mul_assoc] at hfac
    exact hfac.symm
  have hσ_eq : sigma 1 (q ^ N.factorization q) * sigma 1 (r₀ ^ N.factorization r₀) *
      (∏ u ∈ S, (u ^ 2 + u + 1)) = 2 * N := by
    have hσN : sigma 1 N = 2 * N :=
      (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN)
    have hmul : sigma 1 N = ∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p) :=
      isMultiplicative_sigma.multiplicative_factorization (sigma 1) hN.2.ne'
    rw [hσN, hpart, Finset.prod_insert hq_not_ins, Finset.prod_insert hr₀_not_S] at hmul
    have hS_prod : (∏ u ∈ S, sigma 1 (u ^ N.factorization u)) = ∏ u ∈ S, (u ^ 2 + u + 1) := by
      refine Finset.prod_congr rfl fun u hu => ?_
      have hup := (hS_prop u hu).1
      rw [(hS_prop u hu).2.2.2.2.1, sigma_one_apply_prime_pow hup]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero]
      ring
    rw [hS_prod, ← mul_assoc] at hmul
    exact hmul.symm
  have hr₀_mod3 : r₀ % 3 = 1 := by
    by_contra hr₀_ne1
    obtain ⟨hcover, hq_mod3, _, _⟩ :=
      restrained_three_free_residue_obstruction ho hN hq hq4 he hev h3 hr₀ hr₀_ne1
    have hq13 : 13 ≤ q := by
      have := hq_prime.two_le
      omega
    have hS_pow : ∀ u ∈ S, u ^ 2 + u + 1 = q ^ (u ^ 2 + u + 1).factorization q := by
      intro u hu
      have hnorm := (hS_prop u hu).2.2.2.2.2.2.2
      have hsub := hcover u hu
      rw [hnorm] at hsub
      exact eq_pow_of_primeFactors_subset (by omega : u ^ 2 + u + 1 ≠ 0) hsub
    have hS_gap : ∀ u ∈ S, ∀ v ∈ S, u < v → 5 * u ^ 2 < v := by
      intro u hu v hv huv
      exact sq_add_self_add_one_prime_pow_gap hq_prime hq_mod3
        (hS_prop u hu).2.1 (hS_prop v hv).2.1
        (hS_prop u hu).2.2.2.2.2.1 (hS_prop v hv).2.2.2.2.2.1
        huv (hS_pow u hu) (hS_pow v hv)
    have hgap_prod := prod_sq_abundancy_lt_of_five_sq_gap S hS_ne hS_ge5 hS_gap
    have hu₀5 : 5 ≤ S.min' hS_ne := hS_ge5 _ (S.min'_mem hS_ne)
    exact abundancy_contradiction (cq := 12) (dq := 13) (cr := 4) (dr := 5) (cs := 15) (ds := 19)
      hN.2 hσ_eq hN_eq
      (sigma_prime_pow_ratio_lt hq_prime (by decide) (by omega))
      (sigma_prime_pow_ratio_lt hr₀_prime (by decide) (by omega))
      (sq_prod_ratio_lt (by decide) hgap_prod (by omega))
      (by norm_num)
  have hr₀7 : 7 ≤ r₀ := by
    have := hr₀_prime.two_le
    have := Nat.odd_iff.mp hr₀_odd
    omega
  have hq_mod3 : q % 3 = 1 := by
    by_contra hq_ne1
    have hq_not_dvd : ∀ u ∈ S, ¬ q ∣ u ^ 2 + u + 1 := by
      intro u _ hd
      rcases prime_dvd_sq_add_self_add_one hq_prime hd with rfl | hmod
      · omega
      · exact hq_ne1 hmod
    have hS_sub : ∀ u ∈ S, (u ^ 2 + u + 1).primeFactors ⊆ {r₀} := by
      intro u hu w hw
      obtain ⟨hw_prime, hw_dvd, _⟩ := Nat.mem_primeFactors.mp hw
      have hup := (hS_prop u hu).1
      have hu_odd := (hS_prop u hu).2.1
      have hu_exp2 := (hS_prop u hu).2.2.2.2.1
      have hu_mod3 := (hS_prop u hu).2.2.2.2.2.1
      have hsum_odd : Odd (u ^ 2 + u + 1) :=
        ((hu_odd.pow).add_odd hu_odd).add_odd (by decide : Odd 1)
      have hw_odd : Odd w := hsum_odd.of_dvd_nat hw_dvd
      have hsum_mod3 : (u ^ 2 + u + 1) % 3 = 1 := by
        rw [Nat.add_mod, Nat.add_mod (u ^ 2), Nat.pow_mod, hu_mod3]
      have hw_ne3 : w ≠ 3 := by
        intro h
        subst h
        omega
      have hw_mod3 : w % 3 = 1 :=
        (prime_dvd_sq_add_self_add_one hw_prime hw_dvd).resolve_left hw_ne3
      have hwN : w ∣ N := by
        apply dvd_perfect_of_exact_prime_pow hN hup (Nat.ordProj_dvd N u) _ hw_prime hw_odd
        · rw [← sigma_one_apply, sigma_one_apply_prime_pow hup, hu_exp2]
          have hsum3 : (∑ i ∈ Finset.range (2 + 1), u ^ i) = u ^ 2 + u + 1 := by
            rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
              Finset.sum_range_zero]
            ring
          rw [hsum3]
          exact hw_dvd
        · rw [hup.pow_dvd_iff_le_factorization hN.2.ne']
          omega
      have hw_mem := Nat.mem_primeFactors.mpr ⟨hw_prime, hwN, hN.2.ne'⟩
      rw [hpart, Finset.mem_insert, Finset.mem_insert] at hw_mem
      rcases hw_mem with rfl | rfl | hwS
      · exact (hq_not_dvd u hu hw_dvd).elim
      · exact Finset.mem_singleton_self w
      · have hw_sq1 : w ∈ squareSourcesOne N := Finset.mem_filter.mpr ⟨hwS, hw_mod3⟩
        have hpos : 0 < (squareSourcesOne N).card := Finset.card_pos.mpr ⟨w, hw_sq1⟩
        omega
    have hS_pow : ∀ u ∈ S, u ^ 2 + u + 1 = r₀ ^ (u ^ 2 + u + 1).factorization r₀ :=
      fun u hu => eq_pow_of_primeFactors_subset (by omega : u ^ 2 + u + 1 ≠ 0) (hS_sub u hu)
    have hS_gap : ∀ u ∈ S, ∀ v ∈ S, u < v → 5 * u ^ 2 < v := by
      intro u hu v hv huv
      exact sq_add_self_add_one_prime_pow_gap hr₀_prime hr₀_mod3
        (hS_prop u hu).2.1 (hS_prop v hv).2.1
        (hS_prop u hu).2.2.2.2.2.1 (hS_prop v hv).2.2.2.2.2.1
        huv (hS_pow u hu) (hS_pow v hv)
    have hgap_prod := prod_sq_abundancy_lt_of_five_sq_gap S hS_ne hS_ge5 hS_gap
    by_cases hq5 : q = 5
    · have hu₀_mem := S.min'_mem hS_ne
      have hu₀_odd := Nat.odd_iff.mp (hS_prop _ hu₀_mem).2.1
      have hu₀_mod3 := (hS_prop _ hu₀_mem).2.2.2.2.2.1
      have hu₀_neq : S.min' hS_ne ≠ q := (hS_prop _ hu₀_mem).2.2.2.1
      have hu₀11 : 11 ≤ S.min' hS_ne := by omega
      exact abundancy_contradiction (cq := 4) (dq := 5) (cr := 6) (dr := 7) (cs := 33) (ds := 37)
        hN.2 hσ_eq hN_eq
        (sigma_prime_pow_ratio_lt hq_prime (by decide) (by omega))
        (sigma_prime_pow_ratio_lt hr₀_prime (by decide) (by omega))
        (sq_prod_ratio_lt (by decide) hgap_prod (by omega))
        (by norm_num)
    · have hq_mod3_ne0 : q % 3 ≠ 0 := by
        intro h0
        have h3q := (Nat.dvd_prime hq_prime).mp (Nat.dvd_of_mod_eq_zero h0)
        omega
      have hq17 : 17 ≤ q := by omega
      have hu₀5 : 5 ≤ S.min' hS_ne := hS_ge5 _ (S.min'_mem hS_ne)
      exact abundancy_contradiction (cq := 16) (dq := 17) (cr := 6) (dr := 7) (cs := 15) (ds := 19)
        hN.2 hσ_eq hN_eq
        (sigma_prime_pow_ratio_lt hq_prime (by decide) (by omega))
        (sigma_prime_pow_ratio_lt hr₀_prime (by decide) (by omega))
        (sq_prod_ratio_lt (by decide) hgap_prod (by omega))
        (by norm_num)
  have hq12 : q % 12 = 1 := by omega
  have hq13 : 13 ≤ q := by
    have := hq_prime.two_le
    omega
  have hr₀_exp_mod3 : N.factorization r₀ % 3 ≠ 2 := by
    intro hmod2
    have hS3 := sigma_modEq_of_one hr₀_prime (show r₀ ≡ 1 [MOD 3] from hr₀_mod3) (N.factorization r₀)
    change sigma 1 (r₀ ^ N.factorization r₀) % 3 = (N.factorization r₀ + 1) % 3 at hS3
    have h3_sig : 3 ∣ sigma 1 (r₀ ^ N.factorization r₀) := Nat.dvd_of_mod_eq_zero (by omega)
    have h3_2N : 3 ∣ 2 * N := by
      rw [← hσ_eq]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h3_sig _) _
    have h2N_mod : (2 * N) % 3 = 0 := Nat.mod_eq_zero_of_dvd h3_2N
    exact h3 (Nat.dvd_of_mod_eq_zero (by omega))
  exact ⟨r₀, hr₀, hq12, hr₀_mod3, hq13, hr₀7, hr₀_exp_mod3⟩

/-- If `¬ 3 ∣ N`, `N.factorization q = 1`, and `largeSources N q = {r₀}`, then
`16 ≤ N.factorization r₀` (improving `14 ≤ N.factorization r₀` since `14 % 3 = 2` is excluded). -/
theorem restrained_three_free_euler_exp_one_forces_sixteenth_power {N q r₀ : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1)
    (he : N.factorization q = 1) (hev : ∀ r, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) (hlarge : largeSources N q = {r₀}) :
    16 ≤ N.factorization r₀ := by
  have h14 := restrained_three_free_euler_exp_one_forces_sixth_power ho hN hq hq4 he hev h3 hlarge
  have he4 : N.factorization q % 4 = 1 := by omega
  have hle : (largeSources N q).card ≤ 1 := by rw [hlarge]; simp
  obtain ⟨r₁, hr₁, _, _, _, _, hmod3⟩ :=
    restrained_three_free_forces_both_one_mod_three ho hN hq hq4 he4 hev h3 hle
  have hr_eq : r₁ = r₀ := by
    have : r₁ ∈ ({r₀} : Finset ℕ) := by rw [← hlarge, hr₁]; exact Finset.mem_singleton_self r₁
    exact Finset.mem_singleton.mp this
  subst r₁
  have hr₀_mem : r₀ ∈ largeSources N q := by rw [hlarge]; exact Finset.mem_singleton_self r₀
  have hr₀_neq : r₀ ≠ q := (Finset.mem_filter.mp hr₀_mem).2.2.1
  obtain ⟨k, hk⟩ := hev r₀ hr₀_neq
  omega

end OddPerfect
