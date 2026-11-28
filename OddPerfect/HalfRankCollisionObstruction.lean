module

public import OddPerfect.DoubleCollisionExcessObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Half-Rank Collision Obstruction (`OddPerfect.HalfRankCollisionObstruction`)

Upgrades the global Ljunggren collision-excess inequality from `ω(N) ≤ 3 * E + 3` (slope `1/3`)
to `ω(N) ≤ 2 * E + 3` (`ω(N) ≤ 2 * E + 2` when `v_3(N) ≠ 4`, slope `1/2`) by proving that not
even multi-factor components `p ∈ N.primeFactors.erase q` can avoid hitting the target set
`C = {q} ∪ {r ∈ N.primeFactors | 2 ≤ indeg r}` unless `p = 3 ∧ v_3(N) = 4`:

1. `oddComponentSigma_hits_euler_or_collided_of_ne_three_four`: Every non-Euler component
   `p ∈ N.primeFactors.erase q` with `¬ (p = 3 ∧ N.factorization 3 = 4)` has a prime factor
   `r` with `r = q` or `2 ≤ indeg r`.
2. `odd_perfect_half_rank_collision_excess_bound`: Double-counting hits into `C` gives
   `ω(N) ≤ 2 * collisionExcess N q + 3`, and `≤ 2 * collisionExcess N q + 2` when
   `N.factorization 3 ≠ 4` (in particular when `¬ 3 ∣ N`).
3. `three_le_collisionExcess_of_three_free` & `sixth_power_free_collision_excess_ge_221`:
   Couples (2) with `8 ≤ ω(N)` (for `¬ 3 ∣ N`) and `443 ≤ ω(N)` (for sixth-power-free `N`) to
   prove `3 ≤ collisionExcess N q` for `3 ∤ N` and `221 ≤ collisionExcess N q` (and
   `664 ≤ totalIncidences`) for sixth-power-free `N`.
4. `half_rank_collision_least_prime_log_bound`: Couples (2) with `omega_gt_least_prime_mul_log_two`
   to bound `((N.minFac : ℝ) - 1) * Real.log 2` by `2 * collisionExcess N q + 3` (`+ 2` when
   `N.factorization 3 ≠ 4` or `¬ 3 ∣ N`).
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private theorem sum_sub_one_eq_sum_sub_card {s : Finset ℕ} (g : ℕ → ℕ)
    (hg : ∀ x ∈ s, 1 ≤ g x) :
    (∑ x ∈ s, (g x - 1)) = (∑ x ∈ s, g x) - s.card := by
  have hsum : (∑ x ∈ s, (g x - 1)) + s.card = ∑ x ∈ s, g x := by
    calc
      (∑ x ∈ s, (g x - 1)) + s.card
          = (∑ x ∈ s, (g x - 1)) + ∑ _x ∈ s, 1 := by simp
      _ = ∑ x ∈ s, ((g x - 1) + 1) := by rw [← Finset.sum_add_distrib]
      _ = ∑ x ∈ s, g x := Finset.sum_congr rfl fun x hx => Nat.sub_add_cancel (hg x hx)
  omega

private theorem oddComponentSigma_double_counting {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    let indeg : ℕ → ℕ := fun r =>
      (N.primeFactors.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors)).card
    (∀ p ∈ N.primeFactors, (oddComponentSigma N q p).primeFactors ⊆ N.primeFactors) ∧
    (∑ p ∈ N.primeFactors, (oddComponentSigma N q p).primeFactors.card) =
      ∑ r ∈ N.primeFactors, indeg r ∧
    (∀ r ∈ N.primeFactors, 1 ≤ indeg r) ∧
    collisionExcess N q =
      ∑ p ∈ N.primeFactors, ((oddComponentSigma N q p).primeFactors.card - 1) ∧
    collisionExcess N q =
      ∑ r ∈ N.primeFactors, (indeg r - 1) := by
  obtain ⟨_, _, hbi, hcard⟩ := prod_oddComponentSigma_eq_self ho hN hq hq4 he hev
  let S := N.primeFactors
  let f : ℕ → Finset ℕ := fun p => (oddComponentSigma N q p).primeFactors
  let indeg : ℕ → ℕ := fun r => (S.filter (fun p => r ∈ f p)).card
  have hsub : ∀ p ∈ S, f p ⊆ S := by
    intro p hp r hr
    dsimp only [S]
    rw [← hbi]
    exact Finset.mem_biUnion.mpr ⟨p, hp, hr⟩
  have hdouble : (∑ p ∈ S, (f p).card) = ∑ r ∈ S, indeg r := by
    have h1 : ∀ p ∈ S, (f p).card = ∑ r ∈ S, (if r ∈ f p then 1 else 0) := by
      intro p hp
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (hsub p hp)]
    have h2 : ∀ r ∈ S, indeg r = ∑ p ∈ S, (if r ∈ f p then 1 else 0) := by
      intro r _
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    calc
      ∑ p ∈ S, (f p).card
          = ∑ p ∈ S, ∑ r ∈ S, (if r ∈ f p then 1 else 0) := Finset.sum_congr rfl h1
      _ = ∑ r ∈ S, ∑ p ∈ S, (if r ∈ f p then 1 else 0) := Finset.sum_comm
      _ = ∑ r ∈ S, indeg r := Finset.sum_congr rfl fun r hr => (h2 r hr).symm
  have hindeg_pos : ∀ r ∈ S, 1 ≤ indeg r := by
    intro r hr
    have hr' : r ∈ S.biUnion f := hbi.symm ▸ hr
    obtain ⟨p, hp, hrp⟩ := Finset.mem_biUnion.mp hr'
    exact Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hrp⟩⟩
  have hE1 : collisionExcess N q = ∑ p ∈ S, ((f p).card - 1) := by
    unfold collisionExcess
    exact (sum_sub_one_eq_sum_sub_card (fun p => (f p).card) hcard).symm
  have hE2 : collisionExcess N q = ∑ r ∈ S, (indeg r - 1) := by
    unfold collisionExcess
    rw [hdouble]
    exact (sum_sub_one_eq_sum_sub_card indeg hindeg_pos).symm
  exact ⟨hsub, hdouble, hindeg_pos, hE1, hE2⟩

private theorem factorization_eq_of_indeg_one {N q p r : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hpS : p ∈ N.primeFactors) (hrS : r ∈ N.primeFactors)
    (hrp : r ∈ (oddComponentSigma N q p).primeFactors)
    (hindeg1 : (N.primeFactors.filter (fun x => r ∈ (oddComponentSigma N q x).primeFactors)).card = 1) :
    (oddComponentSigma N q p).factorization r = N.factorization r := by
  obtain ⟨hprops, hprod, _, _⟩ := prod_oddComponentSigma_eq_self ho hN hq hq4 he hev
  let S := N.primeFactors
  let f : ℕ → Finset ℕ := fun x => (oddComponentSigma N q x).primeFactors
  have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hrS
  have hr_not_other : ∀ x ∈ S.erase p, r ∉ f x := by
    intro x hx hrx
    have hxp : x ≠ p := (Finset.mem_erase.mp hx).1
    have hxS : x ∈ S := Finset.mem_of_mem_erase hx
    have hsub2 : ({x, p} : Finset ℕ) ⊆ S.filter (fun y => r ∈ f y) := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hxS, hrx⟩
      · exact Finset.mem_filter.mpr ⟨hpS, hrp⟩
    have h2le : 2 ≤ (S.filter (fun y => r ∈ f y)).card := by
      calc
        2 = ({x, p} : Finset ℕ).card := (Finset.card_pair hxp).symm
        _ ≤ (S.filter (fun y => r ∈ f y)).card := Finset.card_le_card hsub2
    dsimp only [S, f] at h2le
    omega
  have hfac_zero : ∀ x ∈ S.erase p, (oddComponentSigma N q x).factorization r = 0 := by
    intro x hx
    have hne0 : oddComponentSigma N q x ≠ 0 := by
      have := (hprops x (Finset.mem_of_mem_erase hx)).2.2
      omega
    have hndvd : ¬ r ∣ oddComponentSigma N q x := fun hd =>
      hr_not_other x hx (Nat.mem_primeFactors.mpr ⟨hr_prime, hd, hne0⟩)
    exact Nat.factorization_eq_zero_of_not_dvd hndvd
  have hmul_eq : oddComponentSigma N q p * ∏ x ∈ S.erase p, oddComponentSigma N q x = N := by
    rw [Finset.mul_prod_erase _ _ hpS]
    exact hprod
  have hp0 : oddComponentSigma N q p ≠ 0 := by
    have := (hprops p hpS).2.2
    omega
  have hrest0 : (∏ x ∈ S.erase p, oddComponentSigma N q x) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun x hx => by
      have := (hprops x (Finset.mem_of_mem_erase hx)).2.2
      omega
  have hfac := congrArg (fun n => n.factorization r) hmul_eq
  rw [Nat.factorization_mul hp0 hrest0, Finsupp.add_apply,
    Nat.factorization_prod_apply fun x hx => by
      have := (hprops x (Finset.mem_of_mem_erase hx)).2.2
      omega] at hfac
  have hsum0 : (∑ x ∈ S.erase p, (oddComponentSigma N q x).factorization r) = 0 :=
    Finset.sum_eq_zero hfac_zero
  omega

/-- **1. Universal Target-Hit Theorem (Including Multi-Factor Components)**:
Every non-Euler component `p ∈ N.primeFactors.erase q` with `¬ (p = 3 ∧ N.factorization 3 = 4)`
contains a prime factor `r` that is either the Euler prime `q` or collided (`2 ≤ indeg r`). -/
theorem oddComponentSigma_hits_euler_or_collided_of_ne_three_four {N q p : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hp : p ∈ N.primeFactors.erase q)
    (hne34 : ¬ (p = 3 ∧ N.factorization 3 = 4)) :
    ∃ r ∈ (oddComponentSigma N q p).primeFactors,
      r = q ∨
      2 ≤ (N.primeFactors.filter (fun x => r ∈ (oddComponentSigma N q x).primeFactors)).card := by
  obtain ⟨hprops, _, _, _⟩ := prod_oddComponentSigma_eq_self ho hN hq hq4 he hev
  obtain ⟨hsub, _, _, _, _⟩ := oddComponentSigma_double_counting ho hN hq hq4 he hev
  have hpq : p ≠ q := (Finset.mem_erase.mp hp).1
  have hpS : p ∈ N.primeFactors := Finset.mem_of_mem_erase hp
  have hp0 : oddComponentSigma N q p ≠ 0 := by
    have := (hprops p hpS).2.2
    omega
  by_contra! hall
  have heven_fac : ∀ r : ℕ, r.Prime → Even ((oddComponentSigma N q p).factorization r) := by
    intro r hr_prime
    by_cases hrp : r ∈ (oddComponentSigma N q p).primeFactors
    · obtain ⟨hrq, hlt2⟩ := hall r hrp
      have hrS : r ∈ N.primeFactors := hsub p hpS hrp
      have hpos :
          1 ≤ (N.primeFactors.filter (fun x => r ∈ (oddComponentSigma N q x).primeFactors)).card :=
        Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hpS, hrp⟩⟩
      have hindeg1 :
          (N.primeFactors.filter (fun x => r ∈ (oddComponentSigma N q x).primeFactors)).card = 1 := by
        omega
      rw [factorization_eq_of_indeg_one ho hN hq hq4 he hev hpS hrS hrp hindeg1]
      exact hev r hrq
    · have hndvd : ¬ r ∣ oddComponentSigma N q p := fun hd =>
        hrp (Nat.mem_primeFactors.mpr ⟨hr_prime, hd, hp0⟩)
      rw [Nat.factorization_eq_zero_of_not_dvd hndvd]
      exact Even.zero
  have hsq : IsSquare (oddComponentSigma N q p) :=
    Nat.isSquare_iff_even_factorization.mpr heven_fac
  have hsig_sq : IsSquare (sigma 1 (p ^ N.factorization p)) := by
    have hcomp : oddComponentSigma N q p = sigma 1 (ordProj[p] N) := by
      unfold oddComponentSigma
      simp only [hpq, ite_false]
    rwa [← hcomp]
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hpS
  have hp_pos : 0 < N.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hpS)
  have hp_even : Even (N.factorization p) := hev p hpq
  rcases (sigma_prime_pow_isSquare_iff_of_even hp_prime hp_pos hp_even).mp hsig_sq with ⟨rfl, h4⟩
  exact hne34 ⟨rfl, h4⟩

/-- **2. Half-Rank Collision Excess Bound (`ω(N) ≤ 2 * E + 3`)**:
Double-counting hits from non-Euler components into `C = {q} ∪ {r ∈ N.primeFactors | 2 ≤ indeg r}`
upgrades `ω(N) ≤ 3 * E + 3` to `ω(N) ≤ 2 * E + 3` unconditionally, and `ω(N) ≤ 2 * E + 2`
whenever `N.factorization 3 ≠ 4` (in particular whenever `¬ 3 ∣ N`). -/
theorem odd_perfect_half_rank_collision_excess_bound {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    N.primeFactors.card ≤ 2 * collisionExcess N q + 3 ∧
    (N.factorization 3 ≠ 4 → N.primeFactors.card ≤ 2 * collisionExcess N q + 2) ∧
    (¬ 3 ∣ N → N.primeFactors.card ≤ 2 * collisionExcess N q + 2) := by
  obtain ⟨hsub, _, hindeg_pos, _, hE_r⟩ :=
    oddComponentSigma_double_counting ho hN hq hq4 he hev
  let S := N.primeFactors
  let f : ℕ → Finset ℕ := fun p => (oddComponentSigma N q p).primeFactors
  let indeg : ℕ → ℕ := fun r => (S.filter (fun p => r ∈ f p)).card
  let C := S.filter (fun r => r = q ∨ 2 ≤ indeg r)
  let U := (S.erase q).filter (fun p => ¬ (p = 3 ∧ N.factorization 3 = 4))
  have hC_sub : C ⊆ S := Finset.filter_subset _ _
  have hqC : q ∈ C := Finset.mem_filter.mpr ⟨hq, Or.inl rfl⟩
  have hC_erase_le : (C.erase q).card ≤ collisionExcess N q := by
    have h1 : (C.erase q).card ≤ ∑ r ∈ C.erase q, (indeg r - 1) := by
      calc
        (C.erase q).card = ∑ _r ∈ C.erase q, 1 := by simp
        _ ≤ ∑ r ∈ C.erase q, (indeg r - 1) := by
          refine Finset.sum_le_sum fun r hr => ?_
          have hrq : r ≠ q := (Finset.mem_erase.mp hr).1
          have hrC := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hr)).2
          rcases hrC with rfl | h2
          · exact (hrq rfl).elim
          · omega
    have h2 : ∑ r ∈ C.erase q, (indeg r - 1) ≤ ∑ r ∈ S, (indeg r - 1) :=
      Finset.sum_le_sum_of_subset fun r hr => (Finset.mem_filter.mp (Finset.mem_of_mem_erase hr)).1
    exact h1.trans (h2.trans_eq hE_r.symm)
  have hC_le : C.card ≤ collisionExcess N q + 1 := by
    have h := Finset.card_erase_add_one hqC
    omega
  have hsum_C_indeg : ∑ r ∈ C, indeg r ≤ 2 * collisionExcess N q + 1 := by
    have hsub_le : ∑ r ∈ C, (indeg r - 1) ≤ collisionExcess N q :=
      (Finset.sum_le_sum_of_subset hC_sub).trans_eq hE_r.symm
    have hC_eq : ∑ r ∈ C, (indeg r - 1) = (∑ r ∈ C, indeg r) - C.card :=
      sum_sub_one_eq_sum_sub_card indeg fun r hr => hindeg_pos r (hC_sub hr)
    have hC_pos : C.card ≤ ∑ r ∈ C, indeg r := by
      calc
        C.card = ∑ _r ∈ C, 1 := by simp
        _ ≤ ∑ r ∈ C, indeg r := Finset.sum_le_sum fun r hr => hindeg_pos r (hC_sub hr)
    omega
  have hU_le_sum : U.card ≤ ∑ r ∈ C, indeg r := by
    have h1 : U.card ≤ ∑ p ∈ U, (f p ∩ C).card := by
      calc
        U.card = ∑ _p ∈ U, 1 := by simp
        _ ≤ ∑ p ∈ U, (f p ∩ C).card := by
          refine Finset.sum_le_sum fun p hp => ?_
          obtain ⟨hpS', hne34⟩ := Finset.mem_filter.mp hp
          have hpS : p ∈ S := Finset.mem_of_mem_erase hpS'
          obtain ⟨r, hrp, hr_cond⟩ :=
            oddComponentSigma_hits_euler_or_collided_of_ne_three_four ho hN hq hq4 he hev hpS' hne34
          have hrS : r ∈ S := hsub p hpS hrp
          have hrC : r ∈ C := Finset.mem_filter.mpr ⟨hrS, hr_cond⟩
          exact Finset.card_pos.mpr ⟨r, Finset.mem_inter.mpr ⟨hrp, hrC⟩⟩
    have h2 : ∑ p ∈ U, (f p ∩ C).card ≤ ∑ p ∈ S, (f p ∩ C).card :=
      Finset.sum_le_sum_of_subset fun p hp =>
        Finset.mem_of_mem_erase (Finset.mem_filter.mp hp).1
    have h3 : ∑ p ∈ S, (f p ∩ C).card = ∑ r ∈ C, indeg r := by
      have hL : ∀ p ∈ S, (f p ∩ C).card = ∑ r ∈ C, (if r ∈ f p then 1 else 0) := by
        intro p _
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one,
          Finset.filter_mem_eq_inter, Finset.inter_comm]
      have hR : ∀ r ∈ C, indeg r = ∑ p ∈ S, (if r ∈ f p then 1 else 0) := by
        intro r _
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      calc
        ∑ p ∈ S, (f p ∩ C).card
            = ∑ p ∈ S, ∑ r ∈ C, (if r ∈ f p then 1 else 0) := Finset.sum_congr rfl hL
        _ = ∑ r ∈ C, ∑ p ∈ S, (if r ∈ f p then 1 else 0) := Finset.sum_comm
        _ = ∑ r ∈ C, indeg r := Finset.sum_congr rfl fun r hr => (hR r hr).symm
    exact h1.trans (h2.trans_eq h3)
  have hU_le : U.card ≤ 2 * collisionExcess N q + 1 := hU_le_sum.trans hsum_C_indeg
  have hS'_eq : (S.erase q).card + 1 = S.card := Finset.card_erase_add_one hq
  have hS'_le : (S.erase q).card ≤ U.card + 1 := by
    have hsdiff : (S.erase q \ U) ⊆ ({3} : Finset ℕ) := by
      intro p hp
      obtain ⟨hpS', hpU⟩ := Finset.mem_sdiff.mp hp
      have hp34 : p = 3 ∧ N.factorization 3 = 4 := by
        by_contra hnot
        exact hpU (Finset.mem_filter.mpr ⟨hpS', hnot⟩)
      exact Finset.mem_singleton.mpr hp34.1
    have hcard_sdiff : (S.erase q \ U).card ≤ 1 :=
      (Finset.card_le_card hsdiff).trans (by simp)
    have hsum_card := Finset.card_sdiff_add_card_eq_card
      (Finset.filter_subset (fun p => ¬ (p = 3 ∧ N.factorization 3 = 4)) (S.erase q))
    change (S.erase q \ U).card + U.card = (S.erase q).card at hsum_card
    omega
  have h_uncond : S.card ≤ 2 * collisionExcess N q + 3 := by omega
  have h_ne4 : N.factorization 3 ≠ 4 → S.card ≤ 2 * collisionExcess N q + 2 := by
    intro hne4
    have hU_eq : U = S.erase q := by
      ext p
      simp only [U, Finset.mem_filter]
      constructor
      · intro hp; exact hp.1
      · intro hp; exact ⟨hp, fun h => hne4 h.2⟩
    rw [hU_eq] at hU_le
    omega
  have h_not3 : ¬ 3 ∣ N → S.card ≤ 2 * collisionExcess N q + 2 := by
    intro hnd3
    apply h_ne4
    rw [Nat.factorization_eq_zero_of_not_dvd hnd3]
    omega
  exact ⟨h_uncond, h_ne4, h_not3⟩

/-- **3a. Three-Free Collision Excess Lower Bound (`3 ≤ E`)**:
When `¬ 3 ∣ N`, combining `8 ≤ ω(N)` with `ω(N) ≤ 2 * E + 2` yields `3 ≤ collisionExcess N q`
and `ω(N) + 3 ≤ ∑ p ∈ N.primeFactors, ω(oddComponentSigma N q p)`. -/
theorem three_le_collisionExcess_of_three_free {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) :
    3 ≤ collisionExcess N q ∧
    N.primeFactors.card + 3 ≤ ∑ p ∈ N.primeFactors, (oddComponentSigma N q p).primeFactors.card := by
  have h8 := eight_le_distinct_prime_factor_count_of_three_free ho hN h3
  have hbound := (odd_perfect_half_rank_collision_excess_bound ho hN hq hq4 he hev).2.2 h3
  have hle := (odd_perfect_collision_excess_bound ho hN hq hq4 he hev).1
  unfold collisionExcess
  have hE3 : 3 ≤ collisionExcess N q := by
    unfold collisionExcess at hbound ⊢
    omega
  unfold collisionExcess at hE3
  omega

/-- **3b. Sixth-Power-Free Collision Excess Lower Bound (`221 ≤ E`)**:
On any sixth-power-free odd perfect number `N`, combining `¬ 3 ∣ N` and `443 ≤ ω(N)` with
`odd_perfect_half_rank_collision_excess_bound` yields `221 ≤ collisionExcess N q` and
`664 ≤ ∑ p ∈ N.primeFactors, (oddComponentSigma N q p).primeFactors.card`. -/
theorem sixth_power_free_collision_excess_ge_221 {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    443 ≤ N.primeFactors.card ∧
    221 ≤ collisionExcess N q ∧
    664 ≤ ∑ p ∈ N.primeFactors, (oddComponentSigma N q p).primeFactors.card := by
  have h443 : 443 ≤ N.primeFactors.card := by
    rcases sixth_power_or_large_support ho hN with ⟨p, hp, hpow⟩ | ⟨hcard, _, _⟩
    · exact (hfree p hp hpow).elim
    · exact hcard
  have hnot3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have hbound := (odd_perfect_half_rank_collision_excess_bound ho hN hq hq4 he hev).2.2 hnot3
  have hle := (odd_perfect_collision_excess_bound ho hN hq hq4 he hev).1
  unfold collisionExcess at hbound ⊢
  omega

/-- **4. Half-Rank Least-Prime Logarithmic Bound**:
Couples `odd_perfect_half_rank_collision_excess_bound` with `omega_gt_least_prime_mul_log_two`
to bound `((N.minFac : ℝ) - 1) * Real.log 2` unconditionally by `2 * collisionExcess N q + 3`
(and `2 * collisionExcess N q + 2` when `N.factorization 3 ≠ 4` or `¬ 3 ∣ N`). -/
theorem half_rank_collision_least_prime_log_bound {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    ((N.minFac : ℝ) - 1) * Real.log 2 < 2 * (collisionExcess N q : ℝ) + 3 ∧
    (N.factorization 3 ≠ 4 →
      ((N.minFac : ℝ) - 1) * Real.log 2 < 2 * (collisionExcess N q : ℝ) + 2) ∧
    (¬ 3 ∣ N →
      ((N.minFac : ℝ) - 1) * Real.log 2 < 2 * (collisionExcess N q : ℝ) + 2) := by
  have h5 := five_le_distinct_prime_factor_count ho hN
  have hN1 : N ≠ 1 := by
    rintro rfl
    simp at h5
  have hp_mem : N.minFac ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime hN1, Nat.minFac_dvd N, hN.2.ne'⟩
  have hmin : ∀ s ∈ N.primeFactors, N.minFac ≤ s := fun s hs =>
    Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hs).two_le
      (Nat.dvd_of_mem_primeFactors hs)
  have homega := omega_gt_least_prime_mul_log_two ho hN hp_mem hmin
  obtain ⟨h_uncond, h_ne4, h_not3⟩ :=
    odd_perfect_half_rank_collision_excess_bound ho hN hq hq4 he hev
  have h_uncond_r : (N.primeFactors.card : ℝ) ≤ 2 * (collisionExcess N q : ℝ) + 3 := by
    exact_mod_cast h_uncond
  refine ⟨by linarith, fun hne4 => ?_, fun hnd3 => ?_⟩
  · have h_ne4_r : (N.primeFactors.card : ℝ) ≤ 2 * (collisionExcess N q : ℝ) + 2 := by
      exact_mod_cast h_ne4 hne4
    linarith
  · have h_not3_r : (N.primeFactors.card : ℝ) ≤ 2 * (collisionExcess N q : ℝ) + 2 := by
      exact_mod_cast h_not3 hnd3
    linarith

end OddPerfect
