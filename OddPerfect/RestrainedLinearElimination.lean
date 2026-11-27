module

public import OddPerfect.RestrainedThreeFreeObstruction
public import OddPerfect.Valuations
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Three-Free Restrained Linear Elimination (`OddPerfect.RestrainedLinearElimination`)

Eliminates all three-free restrained odd perfect candidates (`¬ 3 ∣ N`, `(largeSources N q).card ≤ 1`)
with Euler exponent `N.factorization q < 17` (in particular `N.factorization q = 1`), forcing
`17 ≤ N.factorization q`.

The key mechanism splits `S = squareSources N` into `S_q := S.filter (fun u => q ∣ u ^ 2 + u + 1)`
and `S_0 := S.filter (fun u => ¬ q ∣ u ^ 2 + u + 1)`:
- On `S_0`, every `u ^ 2 + u + 1` is a power of `r₀`, yielding the doubly-exponential `19/15` bound.
- On `S_q`, `q % 12 = 1` forces `29 ≤ u`, so `S_q ∩ [0, 83) ⊆ {29, 41, 47, 53, 59, 71}`, while
  `S_q.card ≤ N.factorization q ≤ 13` caps the remaining `u ≥ 83` terms by `(6973 / 6889)^7`,
  yielding total abundancy `< (13/12) * (7/6) * (19/15) * 1.24157 < 2`.
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

private lemma abundancy_contradiction4 {N σq σr Pq P0 q_pow r_pow Qq Q0 cq dq cr dr cq' dq' c0 d0 : ℕ}
    (_hN_pos : 0 < N)
    (hσ_eq : σq * σr * Pq * P0 = 2 * N)
    (hN_eq : q_pow * r_pow * Qq * Q0 = N)
    (hq : cq * σq < dq * q_pow)
    (hr : cr * σr < dr * r_pow)
    (hpq_pos : 0 < cq' * Pq)
    (hpq : cq' * Pq ≤ dq' * Qq)
    (hp0 : c0 * P0 < d0 * Q0)
    (hineq : dq * dr * dq' * d0 ≤ 2 * (cq * cr * cq' * c0)) : False := by
  have hlt3 : (cq * σq) * (cr * σr) * (c0 * P0) < (dq * q_pow) * (dr * r_pow) * (d0 * Q0) :=
    nat_mul_lt_mul (nat_mul_lt_mul hq hr) hp0
  have hprod : ((cq * σq) * (cr * σr) * (c0 * P0)) * (cq' * Pq) <
      ((dq * q_pow) * (dr * r_pow) * (d0 * Q0)) * (dq' * Qq) :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlt3 hpq_pos) (Nat.mul_le_mul_left _ hpq)
  have hLHS : ((cq * σq) * (cr * σr) * (c0 * P0)) * (cq' * Pq) =
      (cq * cr * cq' * c0) * (σq * σr * Pq * P0) := by ring
  have hRHS : ((dq * q_pow) * (dr * r_pow) * (d0 * Q0)) * (dq' * Qq) =
      (dq * dr * dq' * d0) * (q_pow * r_pow * Qq * Q0) := by ring
  rw [hLHS, hRHS, hσ_eq, hN_eq] at hprod
  have hle : (dq * dr * dq' * d0) * N ≤ (2 * (cq * cr * cq' * c0)) * N :=
    Nat.mul_le_mul_right N hineq
  have hlt : (2 * (cq * cr * cq' * c0)) * N < (2 * (cq * cr * cq' * c0)) * N := by
    calc
      (2 * (cq * cr * cq' * c0)) * N = (cq * cr * cq' * c0) * (2 * N) := by ring
      _ < (dq * dr * dq' * d0) * N := hprod
      _ ≤ (2 * (cq * cr * cq' * c0)) * N := hle
  exact lt_irrefl _ hlt

/-- If an odd prime `q ≡ 1 [MOD 12]` divides `u ^ 2 + u + 1` where `u` is odd and `u ≡ 2 [MOD 3]`,
then `29 ≤ u`. -/
theorem sq_add_self_add_one_ge_29_of_one_mod_twelve_prime_dvd {u q : ℕ}
    (hu_odd : Odd u) (hu3 : u % 3 = 2) (hq : q.Prime) (hq12 : q % 12 = 1)
    (hd : q ∣ u ^ 2 + u + 1) :
    29 ≤ u := by
  by_contra! hlt
  have hu2 : u % 2 = 1 := Nat.odd_iff.mp hu_odd
  have hcases : u = 5 ∨ u = 11 ∨ u = 17 ∨ u = 23 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · have hd31 : q ∣ 31 := by simpa using hd
    have hq_eq : q = 31 := ((Nat.dvd_prime (by norm_num)).mp hd31).resolve_left hq.ne_one
    omega
  · have hd_mul : q ∣ 7 * 19 := by simpa using hd
    rcases hq.dvd_mul.mp hd_mul with hd7 | hd19
    · have hq_eq : q = 7 := ((Nat.dvd_prime (by norm_num)).mp hd7).resolve_left hq.ne_one
      omega
    · have hq_eq : q = 19 := ((Nat.dvd_prime (by norm_num)).mp hd19).resolve_left hq.ne_one
      omega
  · have hd307 : q ∣ 307 := by simpa using hd
    have hq_eq : q = 307 := ((Nat.dvd_prime (by norm_num)).mp hd307).resolve_left hq.ne_one
    omega
  · have hd_mul : q ∣ 7 * 79 := by simpa using hd
    rcases hq.dvd_mul.mp hd_mul with hd7 | hd79
    · have hq_eq : q = 7 := ((Nat.dvd_prime (by norm_num)).mp hd7).resolve_left hq.ne_one
      omega
    · have hq_eq : q = 79 := ((Nat.dvd_prime (by norm_num)).mp hd79).resolve_left hq.ne_one
      omega

private def smallSqQuasiTargets : Finset ℕ := {29, 41, 47, 53, 59, 71}

private lemma smallSqQuasiTargets_card : smallSqQuasiTargets.card = 6 := by decide

private lemma smallSqQuasiTargets_ratio (u : ℕ) (hu : u ∈ smallSqQuasiTargets) :
    6973 * u ^ 2 ≤ 6889 * (u ^ 2 + u + 1) := by
  simp only [smallSqQuasiTargets, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

private lemma big_ratio_of_ge_83 {u : ℕ} (hu : 83 ≤ u) :
    6889 * (u ^ 2 + u + 1) ≤ 6973 * u ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, u = 83 + k := ⟨u - 83, by omega⟩
  have hdiff : 6973 * (83 + k) ^ 2 =
      6889 * ((83 + k) ^ 2 + (83 + k) + 1) + (7055 * k + 84 * k ^ 2) := by ring
  omega

private lemma sq_set_linear_bound (S_q : Finset ℕ)
    (hcard : S_q.card ≤ 13)
    (hprop : ∀ u ∈ S_q, u.Prime ∧ Odd u ∧ u % 3 = 2 ∧ 29 ≤ u) :
    ((∏ u ∈ smallSqQuasiTargets, u ^ 2) * 6889 ^ 7) * (∏ u ∈ S_q, (u ^ 2 + u + 1)) ≤
      ((∏ u ∈ smallSqQuasiTargets, (u ^ 2 + u + 1)) * 6973 ^ 7) * (∏ u ∈ S_q, u ^ 2) := by
  let S_small := S_q.filter (· < 83)
  let S_big := S_q.filter (fun u => ¬ u < 83)
  have hS_small_sub : S_small ⊆ smallSqQuasiTargets := by
    intro u hu
    obtain ⟨hu_mem, hu_lt⟩ := Finset.mem_filter.mp hu
    obtain ⟨hup, hu_odd, hu3, hu29⟩ := hprop u hu_mem
    have hu2 : u % 2 = 1 := Nat.odd_iff.mp hu_odd
    have hcases : u = 29 ∨ u = 35 ∨ u = 41 ∨ u = 47 ∨ u = 53 ∨ u = 59 ∨ u = 65 ∨ u = 71 ∨
        u = 77 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [smallSqQuasiTargets]
    · exact absurd hup (by decide)
    · simp [smallSqQuasiTargets]
    · simp [smallSqQuasiTargets]
    · simp [smallSqQuasiTargets]
    · simp [smallSqQuasiTargets]
    · exact absurd hup (by decide)
    · simp [smallSqQuasiTargets]
    · exact absurd hup (by decide)
  have hS_card : S_small.card + S_big.card = S_q.card :=
    Finset.card_filter_add_card_filter_not (s := S_q) (· < 83)
  have hS_prod_num : (∏ u ∈ S_q, (u ^ 2 + u + 1)) =
      (∏ u ∈ S_small, (u ^ 2 + u + 1)) * (∏ u ∈ S_big, (u ^ 2 + u + 1)) :=
    (Finset.prod_filter_mul_prod_filter_not S_q (· < 83) (fun u => u ^ 2 + u + 1)).symm
  have hS_prod_den : (∏ u ∈ S_q, u ^ 2) =
      (∏ u ∈ S_small, u ^ 2) * (∏ u ∈ S_big, u ^ 2) :=
    (Finset.prod_filter_mul_prod_filter_not S_q (· < 83) (fun u => u ^ 2)).symm
  let T_rem := smallSqQuasiTargets \ S_small
  have hT_disj : Disjoint S_small T_rem := disjoint_sdiff_self_right
  have hT_union : S_small ∪ T_rem = smallSqQuasiTargets :=
    Finset.union_sdiff_of_subset hS_small_sub
  have hT_card : S_small.card + T_rem.card = 6 := by
    rw [← Finset.card_union_of_disjoint hT_disj, hT_union, smallSqQuasiTargets_card]
  have hT_prod_num : (∏ u ∈ smallSqQuasiTargets, (u ^ 2 + u + 1)) =
      (∏ u ∈ S_small, (u ^ 2 + u + 1)) * (∏ u ∈ T_rem, (u ^ 2 + u + 1)) := by
    rw [← hT_union, Finset.prod_union hT_disj]
  have hT_prod_den : (∏ u ∈ smallSqQuasiTargets, u ^ 2) =
      (∏ u ∈ S_small, u ^ 2) * (∏ u ∈ T_rem, u ^ 2) := by
    rw [← hT_union, Finset.prod_union hT_disj]
  let A := ∏ u ∈ S_small, (u ^ 2 + u + 1)
  let B := ∏ u ∈ S_small, u ^ 2
  let C := ∏ u ∈ T_rem, (u ^ 2 + u + 1)
  let D := ∏ u ∈ T_rem, u ^ 2
  let E := ∏ u ∈ S_big, (u ^ 2 + u + 1)
  let F := ∏ u ∈ S_big, u ^ 2
  have hm_le : S_big.card ≤ 7 + T_rem.card := by omega
  let r := 7 + T_rem.card - S_big.card
  have hmr : S_big.card + r = 7 + T_rem.card := by omega
  have hbig_prod : (∏ u ∈ S_big, (6889 * (u ^ 2 + u + 1))) ≤
      ∏ u ∈ S_big, (6973 * u ^ 2) := by
    refine Finset.prod_le_prod fun u hu => ?_
    have hu83 : 83 ≤ u := by
      have := (Finset.mem_filter.mp hu).2
      omega
    exact big_ratio_of_ge_83 hu83
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const]
    at hbig_prod
  have hbig : 6889 ^ S_big.card * E ≤ 6973 ^ S_big.card * F := hbig_prod
  have hrem_prod : (∏ u ∈ T_rem, (6973 * u ^ 2)) ≤
      ∏ u ∈ T_rem, (6889 * (u ^ 2 + u + 1)) := by
    refine Finset.prod_le_prod fun u hu => ?_
    exact smallSqQuasiTargets_ratio u (Finset.mem_sdiff.mp hu).1
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const]
    at hrem_prod
  have hrem : 6973 ^ T_rem.card * D ≤ 6889 ^ T_rem.card * C := hrem_prod
  have hr_le : 6889 ^ r ≤ 6973 ^ r := Nat.pow_le_pow_left (by decide) r
  have hcomb : (6889 ^ S_big.card * E) * (6973 ^ T_rem.card * D) * 6889 ^ r ≤
      (6973 ^ S_big.card * F) * (6889 ^ T_rem.card * C) * 6973 ^ r :=
    Nat.mul_le_mul (Nat.mul_le_mul hbig hrem) hr_le
  have hLHS_pow : (6889 ^ S_big.card * E) * (6973 ^ T_rem.card * D) * 6889 ^ r =
      (6889 ^ T_rem.card * 6973 ^ T_rem.card) * (D * 6889 ^ 7 * E) := by
    calc
      (6889 ^ S_big.card * E) * (6973 ^ T_rem.card * D) * 6889 ^ r
          = (6889 ^ (S_big.card + r) * 6973 ^ T_rem.card) * (D * E) := by
            rw [pow_add]; ring
      _ = (6889 ^ (7 + T_rem.card) * 6973 ^ T_rem.card) * (D * E) := by rw [hmr]
      _ = (6889 ^ T_rem.card * 6973 ^ T_rem.card) * (D * 6889 ^ 7 * E) := by
            rw [pow_add]; ring
  have hRHS_pow : (6973 ^ S_big.card * F) * (6889 ^ T_rem.card * C) * 6973 ^ r =
      (6889 ^ T_rem.card * 6973 ^ T_rem.card) * (C * 6973 ^ 7 * F) := by
    calc
      (6973 ^ S_big.card * F) * (6889 ^ T_rem.card * C) * 6973 ^ r
          = (6889 ^ T_rem.card * 6973 ^ (S_big.card + r)) * (C * F) := by
            rw [pow_add]; ring
      _ = (6889 ^ T_rem.card * 6973 ^ (7 + T_rem.card)) * (C * F) := by rw [hmr]
      _ = (6889 ^ T_rem.card * 6973 ^ T_rem.card) * (C * 6973 ^ 7 * F) := by
            rw [pow_add]; ring
  rw [hLHS_pow, hRHS_pow] at hcomb
  have hcore : D * 6889 ^ 7 * E ≤ C * 6973 ^ 7 * F :=
    Nat.le_of_mul_le_mul_left hcomb (Nat.mul_pos (by positivity) (by positivity))
  have hfinal := Nat.mul_le_mul_left (A * B) hcore
  have hL : (A * B) * (D * 6889 ^ 7 * E) = ((B * D) * 6889 ^ 7) * (A * E) := by ring
  have hR : (A * B) * (C * 6973 ^ 7 * F) = ((A * C) * 6973 ^ 7) * (B * F) := by ring
  rw [hL, hR] at hfinal
  change ((B * D) * 6889 ^ 7) * (A * E) ≤ ((A * C) * 6973 ^ 7) * (B * F) at hfinal
  rw [← hT_prod_den, ← hT_prod_num, ← hS_prod_num, ← hS_prod_den] at hfinal
  exact hfinal

/-- In the three-free restrained regime (`¬ 3 ∣ N`), Euler exponent `N.factorization q < 17`
forces `2 ≤ (largeSources N q).card`. -/
theorem two_le_largeSources_of_three_free_euler_exp_lt_17 {N q : ℕ} (ho : Odd N)
    (hN : N.Perfect) (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1)
    (he : N.factorization q % 4 = 1) (hev : ∀ r, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) (hlt : N.factorization q < 17) :
    2 ≤ (largeSources N q).card := by
  by_contra! hlt2
  have hle : (largeSources N q).card ≤ 1 := by omega
  obtain ⟨r₀, hr₀, hq12, hr₀3, hq13, hr₀7, _⟩ :=
    restrained_three_free_forces_both_one_mod_three ho hN hq hq4 he hev h3 hle
  have hq_le13 : N.factorization q ≤ 13 := by omega
  have hr₀_mem_large : r₀ ∈ largeSources N q := by rw [hr₀]; exact Finset.mem_singleton_self r₀
  obtain ⟨hr₀_mem, _, hr₀q, _⟩ := Finset.mem_filter.mp hr₀_mem_large
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_mem
  have hq_odd : Odd q := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)
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
  have hS_prop : ∀ u ∈ S, u.Prime ∧ Odd u ∧ u ≠ 3 ∧ u ≠ q ∧ N.factorization u = 2 ∧
      u % 3 = 2 ∧ 5 ≤ u ∧ sigma 1 (u ^ N.factorization u) = u ^ 2 + u + 1 := by
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
    have hsig : sigma 1 (u ^ N.factorization u) = u ^ 2 + u + 1 := by
      rw [hu_exp2, sigma_one_apply_prime_pow hup]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero]
      ring
    exact ⟨hup, hu_odd, hu3, huq, hu_exp2, hu_mod3, hu5, hsig⟩
  let S_q := S.filter (fun u => q ∣ u ^ 2 + u + 1)
  let S_0 := S.filter (fun u => ¬ q ∣ u ^ 2 + u + 1)
  have hN_eq : q ^ N.factorization q * r₀ ^ N.factorization r₀ *
      (∏ u ∈ S_q, u ^ 2) * (∏ u ∈ S_0, u ^ 2) = N := by
    have hfac := Nat.prod_primeFactors_pow_factorization hN.2.ne'
    rw [hpart, Finset.prod_insert hq_not_ins, Finset.prod_insert hr₀_not_S] at hfac
    have hS_prod : (∏ u ∈ S, u ^ N.factorization u) =
        (∏ u ∈ S_q, u ^ 2) * (∏ u ∈ S_0, u ^ 2) := by
      have h1 : (∏ u ∈ S, u ^ N.factorization u) = ∏ u ∈ S, u ^ 2 :=
        Finset.prod_congr rfl fun u hu => by rw [(hS_prop u hu).2.2.2.2.1]
      rw [h1]
      exact (Finset.prod_filter_mul_prod_filter_not S (fun u => q ∣ u ^ 2 + u + 1)
        (fun u => u ^ 2)).symm
    rw [hS_prod] at hfac
    calc
      q ^ N.factorization q * r₀ ^ N.factorization r₀ *
          (∏ u ∈ S_q, u ^ 2) * (∏ u ∈ S_0, u ^ 2)
          = q ^ N.factorization q * (r₀ ^ N.factorization r₀ *
              ((∏ u ∈ S_q, u ^ 2) * (∏ u ∈ S_0, u ^ 2))) := by ring
      _ = N := hfac.symm
  have hσ_eq : sigma 1 (q ^ N.factorization q) * sigma 1 (r₀ ^ N.factorization r₀) *
      (∏ u ∈ S_q, (u ^ 2 + u + 1)) * (∏ u ∈ S_0, (u ^ 2 + u + 1)) = 2 * N := by
    have hσN : sigma 1 N = 2 * N :=
      (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN)
    have hmul : sigma 1 N = ∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p) :=
      isMultiplicative_sigma.multiplicative_factorization (sigma 1) hN.2.ne'
    rw [hσN, hpart, Finset.prod_insert hq_not_ins, Finset.prod_insert hr₀_not_S] at hmul
    have hS_prod : (∏ u ∈ S, sigma 1 (u ^ N.factorization u)) =
        (∏ u ∈ S_q, (u ^ 2 + u + 1)) * (∏ u ∈ S_0, (u ^ 2 + u + 1)) := by
      have h1 : (∏ u ∈ S, sigma 1 (u ^ N.factorization u)) = ∏ u ∈ S, (u ^ 2 + u + 1) :=
        Finset.prod_congr rfl fun u hu => (hS_prop u hu).2.2.2.2.2.2.2
      rw [h1]
      exact (Finset.prod_filter_mul_prod_filter_not S (fun u => q ∣ u ^ 2 + u + 1)
        (fun u => u ^ 2 + u + 1)).symm
    rw [hS_prod] at hmul
    calc
      sigma 1 (q ^ N.factorization q) * sigma 1 (r₀ ^ N.factorization r₀) *
          (∏ u ∈ S_q, (u ^ 2 + u + 1)) * (∏ u ∈ S_0, (u ^ 2 + u + 1))
          = sigma 1 (q ^ N.factorization q) * (sigma 1 (r₀ ^ N.factorization r₀) *
              ((∏ u ∈ S_q, (u ^ 2 + u + 1)) * (∏ u ∈ S_0, (u ^ 2 + u + 1)))) := by ring
      _ = 2 * N := hmul.symm
  have hS_q_card : S_q.card ≤ 13 := by
    have hle_q : S_q.card ≤ N.factorization q := by
      apply card_le_factorization_of_sigma_sources hN hq_odd hq_prime S_q
      · exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
      · intro u hu
        obtain ⟨hu_S, hu_dvd⟩ := Finset.mem_filter.mp hu
        rw [(hS_prop u hu_S).2.2.2.2.2.2.2]
        exact hu_dvd
    omega
  have hS_q_prop : ∀ u ∈ S_q, u.Prime ∧ Odd u ∧ u % 3 = 2 ∧ 29 ≤ u := by
    intro u hu
    obtain ⟨hu_S, hu_dvd⟩ := Finset.mem_filter.mp hu
    obtain ⟨hup, hu_odd, _, _, _, hu3, _, _⟩ := hS_prop u hu_S
    have hu29 := sq_add_self_add_one_ge_29_of_one_mod_twelve_prime_dvd hu_odd hu3 hq_prime hq12
      hu_dvd
    exact ⟨hup, hu_odd, hu3, hu29⟩
  have hSq_bound := sq_set_linear_bound S_q hS_q_card hS_q_prop
  have hSq_pos : 0 < ((∏ u ∈ smallSqQuasiTargets, u ^ 2) * 6889 ^ 7) *
      (∏ u ∈ S_q, (u ^ 2 + u + 1)) := by
    refine Nat.mul_pos (Nat.mul_pos (Finset.prod_pos fun u hu => ?_) (by positivity))
      (Finset.prod_pos fun u hu => by positivity)
    simp only [smallSqQuasiTargets, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> positivity
  have hS0_bound : 15 * (∏ u ∈ S_0, (u ^ 2 + u + 1)) < 19 * (∏ u ∈ S_0, u ^ 2) := by
    rcases S_0.eq_empty_or_nonempty with hemp | hne0
    · rw [hemp, Finset.prod_empty, Finset.prod_empty]
      omega
    · have hS0_sub : ∀ u ∈ S_0, (u ^ 2 + u + 1).primeFactors ⊆ {r₀} := by
        intro u hu w hw
        obtain ⟨hu_S, hu_nq⟩ := Finset.mem_filter.mp hu
        obtain ⟨hw_prime, hw_dvd, _⟩ := Nat.mem_primeFactors.mp hw
        obtain ⟨hup, hu_odd, _, _, hu_exp2, hu_mod3, _, _⟩ := hS_prop u hu_S
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
        · exact (hu_nq hw_dvd).elim
        · exact Finset.mem_singleton_self w
        · have hw_sq1 : w ∈ squareSourcesOne N := Finset.mem_filter.mpr ⟨hwS, hw_mod3⟩
          have hpos : 0 < (squareSourcesOne N).card := Finset.card_pos.mpr ⟨w, hw_sq1⟩
          omega
      have hS0_pow : ∀ u ∈ S_0, u ^ 2 + u + 1 = r₀ ^ (u ^ 2 + u + 1).factorization r₀ :=
        fun u hu => eq_pow_of_primeFactors_subset (by omega : u ^ 2 + u + 1 ≠ 0) (hS0_sub u hu)
      have hS0_gap : ∀ u ∈ S_0, ∀ v ∈ S_0, u < v → 5 * u ^ 2 < v := by
        intro u hu v hv huv
        have hu_S := (Finset.mem_filter.mp hu).1
        have hv_S := (Finset.mem_filter.mp hv).1
        exact sq_add_self_add_one_prime_pow_gap hr₀_prime hr₀3
          (hS_prop u hu_S).2.1 (hS_prop v hv_S).2.1
          (hS_prop u hu_S).2.2.2.2.2.1 (hS_prop v hv_S).2.2.2.2.2.1
          huv (hS0_pow u hu) (hS0_pow v hv)
      have hS0_ge5 : ∀ u ∈ S_0, 5 ≤ u := fun u hu =>
        (hS_prop u (Finset.mem_filter.mp hu).1).2.2.2.2.2.2.1
      have hgap_prod := prod_sq_abundancy_lt_of_five_sq_gap S_0 hne0 hS0_ge5 hS0_gap
      have hu₀5 : 5 ≤ S_0.min' hne0 := hS0_ge5 _ (S_0.min'_mem hne0)
      exact sq_prod_ratio_lt (c₁ := 15) (c₂ := 19) (by decide) hgap_prod (by nlinarith only [hu₀5])
  have hineq :
      13 * 7 * ((∏ u ∈ smallSqQuasiTargets, (u ^ 2 + u + 1)) * 6973 ^ 7) * 19 ≤
      2 * (12 * 6 * ((∏ u ∈ smallSqQuasiTargets, u ^ 2) * 6889 ^ 7) * 15) := by
    have hnum : (∏ u ∈ smallSqQuasiTargets, (u ^ 2 + u + 1)) =
        871 * 1723 * 2257 * 2863 * 3541 * 5113 := by
      simp only [smallSqQuasiTargets]
      rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_singleton]
      norm_num
    have hden : (∏ u ∈ smallSqQuasiTargets, u ^ 2) =
        841 * 1681 * 2209 * 2809 * 3481 * 5041 := by
      simp only [smallSqQuasiTargets]
      rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_singleton]
      norm_num
    rw [hnum, hden]
    norm_num
  have hq_coef : 12 * q ≤ 13 * (q - 1) := by
    have hq1 : 1 ≤ q := le_trans (by decide) hq13
    zify [hq1]
    linarith [hq13]
  have hr₀_coef : 6 * r₀ ≤ 7 * (r₀ - 1) := by
    have hr1 : 1 ≤ r₀ := le_trans (by decide) hr₀7
    zify [hr1]
    linarith [hr₀7]
  exact abundancy_contradiction4 (cq := 12) (dq := 13) (cr := 6) (dr := 7) (c0 := 15) (d0 := 19)
    hN.2 hσ_eq hN_eq
    (sigma_prime_pow_ratio_lt (c₁ := 12) (c₂ := 13) hq_prime (by decide) hq_coef)
    (sigma_prime_pow_ratio_lt (c₁ := 6) (c₂ := 7) hr₀_prime (by decide) hr₀_coef)
    hSq_pos hSq_bound hS0_bound hineq

/-- In the three-free restrained regime (`¬ 3 ∣ N`), Euler exponent `N.factorization q = 1`
forces `2 ≤ (largeSources N q).card`. -/
theorem two_le_largeSources_of_three_free_euler_exp_one {N q : ℕ} (ho : Odd N)
    (hN : N.Perfect) (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1)
    (he : N.factorization q = 1) (hev : ∀ r, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) :
    2 ≤ (largeSources N q).card :=
  two_le_largeSources_of_three_free_euler_exp_lt_17 ho hN hq hq4 (by omega) hev h3 (by omega)

/-- In the three-free restrained regime (`¬ 3 ∣ N`, `(largeSources N q).card ≤ 1`),
`N.factorization q` must be at least `17`, alongside `q % 12 = 1`, `r₀ % 3 = 1`,
`13 ≤ q`, `7 ≤ r₀`, and `N.factorization r₀ % 3 ≠ 2`. -/
theorem restrained_three_free_euler_exp_ge_17 {N q : ℕ} (ho : Odd N)
    (hN : N.Perfect) (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1)
    (he : N.factorization q % 4 = 1) (hev : ∀ r, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) (hle : (largeSources N q).card ≤ 1) :
    ∃ r₀, largeSources N q = {r₀} ∧ q % 12 = 1 ∧ r₀ % 3 = 1 ∧
      17 ≤ N.factorization q ∧ 13 ≤ q ∧ 7 ≤ r₀ ∧ N.factorization r₀ % 3 ≠ 2 := by
  obtain ⟨r₀, hr₀, hq12, hr₀3, hq13, hr₀7, hmod3⟩ :=
    restrained_three_free_forces_both_one_mod_three ho hN hq hq4 he hev h3 hle
  have h17 : 17 ≤ N.factorization q := by
    by_contra! hlt
    have h2 := two_le_largeSources_of_three_free_euler_exp_lt_17 ho hN hq hq4 he hev h3 hlt
    omega
  exact ⟨r₀, hr₀, hq12, hr₀3, h17, hq13, hr₀7, hmod3⟩

end OddPerfect
