module

public import OddPerfect.UniversalSigmaCollisionObstruction
public import OddPerfect.PrimeFive
public import OddPerfect.GlobalLogSlopePinch
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Double Collision Excess Obstruction (`OddPerfect.DoubleCollisionExcessObstruction`)

Refines `OddPerfect.UniversalSigmaCollisionObstruction` from `1 ≤ E` to unconditional
`2 ≤ E` across EVERY odd perfect number `N`, establishes the exact additive multiplicity
decomposition of `Ω(N)`, deduces universal double-or-triple sigma collisions, and couples
the collision excess bound with the logarithmic least-prime lower bound:

1. `collisionExcess`, `localRepeatExcess`, and
   `cardFactors_eq_primeFactors_add_localRepeat_add_collisionExcess`:
   exact additive decomposition `Ω(N) = ω(N) + localRepeatExcess N q + collisionExcess N q`.
2. `two_le_collisionExcess_of_odd_perfect`: unconditional proof that `collisionExcess N q ≠ 1`
   (and hence `2 ≤ collisionExcess N q`) for every odd perfect number `N`, ruling out the
   unique zero-slack `6 = 3 * 1 + 3` (`3^4 ∣ N`, `11^2 ∣ N`, `7, 19 ∣ N`) configuration.
3. `odd_perfect_double_or_triple_sigma_collision`: unconditionally every odd perfect number `N`
   admits either an odd prime dividing three distinct component divisor sums or two distinct
   odd primes each colliding across two distinct components.
4. `collision_excess_least_prime_log_bound`: couples `odd_perfect_collision_excess_bound` with
   `omega_gt_least_prime_mul_log_two` to bound `((N.minFac : ℝ) - 1) * Real.log 2` in terms
   of `collisionExcess N q`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- The global collision excess `E = (∑ p ∈ N.primeFactors, ω(oddComponentSigma N q p)) - ω(N)`. -/
@[expose] def collisionExcess (N q : ℕ) : ℕ :=
  (∑ p ∈ N.primeFactors, (oddComponentSigma N q p).primeFactors.card) - N.primeFactors.card

/-- The local repeat multiplicity excess `∑ p ∈ N.primeFactors, (Ω(c_p) - ω(c_p))`. -/
@[expose] def localRepeatExcess (N q : ℕ) : ℕ :=
  ∑ p ∈ N.primeFactors,
    (cardFactors (oddComponentSigma N q p) - (oddComponentSigma N q p).primeFactors.card)

private theorem cardFactors_finset_prod (s : Finset ℕ) (f : ℕ → ℕ)
    (hf : ∀ x ∈ s, f x ≠ 0) :
    cardFactors (∏ x ∈ s, f x) = ∑ x ∈ s, cardFactors (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cardFactors_one]
  | insert a s ha ih =>
    have ha0 : f a ≠ 0 := hf a (Finset.mem_insert_self a s)
    have hs0 : ∀ x ∈ s, f x ≠ 0 := fun x hx => hf x (Finset.mem_insert_of_mem hx)
    have hprod0 : (∏ x ∈ s, f x) ≠ 0 := Finset.prod_ne_zero_iff.mpr hs0
    rw [Finset.prod_insert ha, cardFactors_mul ha0 hprod0, Finset.sum_insert ha, ih hs0]

/-- Every natural number has at least as many total prime factors (with multiplicity) as
distinct prime factors. -/
theorem primeFactors_card_le_cardFactors (n : ℕ) :
    n.primeFactors.card ≤ cardFactors n := by
  rw [← cardDistinctFactors_eq_card_primeFactors,
    cardDistinctFactors_eq_length_dedup_primeFactorsList, cardFactors_apply]
  exact n.primeFactorsList.dedup_sublist.length_le

/-- The sum of total prime-factor multiplicities of all odd components `oddComponentSigma N q p`
equals `Ω(N)`. -/
theorem sum_cardFactors_oddComponentSigma_eq {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    (∑ p ∈ N.primeFactors, cardFactors (oddComponentSigma N q p)) = cardFactors N := by
  obtain ⟨hprops, hprod, _, _⟩ := prod_oddComponentSigma_eq_self ho hN hq hq4 he hev
  rw [← cardFactors_finset_prod N.primeFactors (oddComponentSigma N q) fun p hp => by
    have := (hprops p hp).2.2; omega, hprod]

/-- **1. Exact Additive Multiplicity Decomposition**:
`Ω(N) = ω(N) + localRepeatExcess N q + collisionExcess N q`. -/
theorem cardFactors_eq_primeFactors_add_localRepeat_add_collisionExcess {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    cardFactors N = N.primeFactors.card + localRepeatExcess N q + collisionExcess N q := by
  have hsum_cf :
      (∑ p ∈ N.primeFactors, cardFactors (oddComponentSigma N q p)) = cardFactors N :=
    sum_cardFactors_oddComponentSigma_eq ho hN hq hq4 he hev
  have hbound := odd_perfect_collision_excess_bound ho hN hq hq4 he hev
  have hle_inc :
      N.primeFactors.card ≤ ∑ p ∈ N.primeFactors, (oddComponentSigma N q p).primeFactors.card :=
    hbound.1
  have hlocal_add :
      localRepeatExcess N q + ∑ p ∈ N.primeFactors, (oddComponentSigma N q p).primeFactors.card =
        ∑ p ∈ N.primeFactors, cardFactors (oddComponentSigma N q p) := by
    unfold localRepeatExcess
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hle := primeFactors_card_le_cardFactors (oddComponentSigma N q p)
    omega
  unfold collisionExcess
  omega

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

private theorem oddComponentSigma_eq_prime_pow_of_card_one {N q p r : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hpS : p ∈ N.primeFactors) (hfp : (oddComponentSigma N q p).primeFactors = {r}) :
    oddComponentSigma N q p = r ^ (oddComponentSigma N q p).factorization r := by
  obtain ⟨hprops, _, _, _⟩ := prod_oddComponentSigma_eq_self ho hN hq hq4 he hev
  have hp0 : oddComponentSigma N q p ≠ 0 := by
    have := (hprops p hpS).2.2
    omega
  have hpf : oddComponentSigma N q p = (oddComponentSigma N q p).factorization.prod (· ^ ·) :=
    (Nat.prod_factorization_pow_eq_self hp0).symm
  conv_lhs => rw [hpf]
  unfold Finsupp.prod
  rw [Nat.support_factorization, hfp, Finset.prod_singleton]

private theorem isolated_singleton_forces_three {N q p r : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hpS : p ∈ N.primeFactors) (hpq : p ≠ q)
    (hfp : (oddComponentSigma N q p).primeFactors = {r})
    (hrq : r ≠ q)
    (hindeg1 : (N.primeFactors.filter (fun x => r ∈ (oddComponentSigma N q x).primeFactors)).card = 1) :
    p = 3 ∧ N.factorization 3 = 4 := by
  obtain ⟨hsub, _, _, _, _⟩ := oddComponentSigma_double_counting ho hN hq hq4 he hev
  have hr_fp : r ∈ (oddComponentSigma N q p).primeFactors := by
    rw [hfp]
    exact Finset.mem_singleton_self r
  have hrS : r ∈ N.primeFactors := hsub p hpS hr_fp
  have hfac_eq := factorization_eq_of_indeg_one ho hN hq hq4 he hev hpS hrS hr_fp hindeg1
  have hcomp_eq := oddComponentSigma_eq_prime_pow_of_card_one ho hN hq hq4 he hev hpS hfp
  rw [hfac_eq] at hcomp_eq
  have hsig_eq : sigma 1 (p ^ N.factorization p) = r ^ N.factorization r := by
    have h1 : oddComponentSigma N q p = sigma 1 (ordProj[p] N) := by
      unfold oddComponentSigma
      simp only [hpq, ite_false]
    rw [← h1]
    exact hcomp_eq
  obtain ⟨m, hm⟩ := hev r hrq
  have hsq : IsSquare (sigma 1 (p ^ N.factorization p)) := by
    rw [hsig_eq]
    exact ⟨r ^ m, by rw [hm, pow_add]⟩
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hpS
  have hp_pos : 0 < N.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hpS)
  have hp_even : Even (N.factorization p) := hev p hpq
  rcases (sigma_prime_pow_isSquare_iff_of_even hp_prime hp_pos hp_even).mp hsq with ⟨rfl, h4⟩
  exact ⟨rfl, h4⟩

private theorem not_dvd_sigma_prime_pow_self {q a : ℕ} (hq : q.Prime) :
    ¬ q ∣ sigma 1 (q ^ a) := by
  rw [sigma_one_apply_prime_pow hq, Finset.sum_range_succ']
  have hdvd : q ∣ ∑ i ∈ Finset.range a, q ^ (i + 1) := by
    refine Finset.dvd_sum fun i _ => ?_
    rw [pow_succ']
    exact dvd_mul_right q (q ^ i)
  intro hq_dvd
  rw [pow_zero] at hq_dvd
  have h1 : q ∣ 1 := (Nat.dvd_add_right hdvd).mp hq_dvd
  exact hq.not_dvd_one h1

private theorem oddComponentSigma_three_eq {N q : ℕ}
    (hq4 : q % 4 = 1) (hf3 : N.factorization 3 = 4) :
    oddComponentSigma N q 3 = 121 ∧ (oddComponentSigma N q 3).primeFactors = {11} := by
  have h3q : (3 : ℕ) ≠ q := by omega
  have hsig : sigma 1 (3 ^ 4) = 121 := by
    rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
    norm_num [Finset.sum_range_succ]
  have hval : oddComponentSigma N q 3 = 121 := by
    unfold oddComponentSigma
    simp only [h3q, ite_false]
    rw [hf3]
    exact hsig
  have hpf : (121 : ℕ).primeFactors = {11} := by
    have h121 : (121 : ℕ) = 11 ^ 2 := by norm_num
    rw [h121]
    exact Nat.primeFactors_prime_pow (by norm_num) (by decide : Nat.Prime 11)
  exact ⟨hval, by rw [hval]; exact hpf⟩

private theorem oddComponentSigma_eleven_eq {N q : ℕ}
    (hq4 : q % 4 = 1) (hf11 : N.factorization 11 = 2) :
    oddComponentSigma N q 11 = 133 ∧ (oddComponentSigma N q 11).primeFactors = {7, 19} := by
  have h11q : (11 : ℕ) ≠ q := by omega
  have hsig : sigma 1 (11 ^ 2) = 133 := by
    rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 11)]
    norm_num [Finset.sum_range_succ]
  have hval : oddComponentSigma N q 11 = 133 := by
    unfold oddComponentSigma
    simp only [h11q, ite_false]
    rw [hf11]
    exact hsig
  have hpf : (133 : ℕ).primeFactors = {7, 19} := by
    have h133 : (133 : ℕ) = 7 ^ 1 * 19 ^ 1 := by norm_num
    rw [h133, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_prime_pow (by norm_num) (by decide : Nat.Prime 7),
      Nat.primeFactors_prime_pow (by norm_num) (by decide : Nat.Prime 19)]
    rfl
  exact ⟨hval, by rw [hval]; exact hpf⟩

private theorem collisionExcess_eq_one_absurd_of_two_le_indeg11 {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hE1 : collisionExcess N q = 1)
    (hS6 : N.primeFactors.card = 6)
    (h11S : 11 ∈ N.primeFactors)
    (hf3_pf : (oddComponentSigma N q 3).primeFactors = {11})
    (hindeg11_2 :
      2 ≤ (N.primeFactors.filter (fun p => 11 ∈ (oddComponentSigma N q p).primeFactors)).card) :
    False := by
  obtain ⟨_, _, _, hcard⟩ := prod_oddComponentSigma_eq_self ho hN hq hq4 he hev
  obtain ⟨hsub, _, hindeg_pos, hE_p, hE_r⟩ :=
    oddComponentSigma_double_counting ho hN hq hq4 he hev
  have hsum_p : (∑ p ∈ N.primeFactors, ((oddComponentSigma N q p).primeFactors.card - 1)) = 1 :=
    hE_p.symm.trans hE1
  have hsum_r :
      (∑ r ∈ N.primeFactors,
        ((N.primeFactors.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors)).card - 1)) = 1 :=
    hE_r.symm.trans hE1
  have h11q : (11 : ℕ) ≠ q := by omega
  have hindeg11_eq :
      (N.primeFactors.filter (fun p => 11 ∈ (oddComponentSigma N q p).primeFactors)).card = 2 := by
    have hle :
        (N.primeFactors.filter (fun p => 11 ∈ (oddComponentSigma N q p).primeFactors)).card - 1 ≤
          ∑ r ∈ N.primeFactors,
            ((N.primeFactors.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors)).card - 1) :=
      Finset.single_le_sum (f := fun r =>
        (N.primeFactors.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors)).card - 1)
        (fun _ _ => Nat.zero_le _) h11S
    omega
  have hindeg_other_1 : ∀ r ∈ N.primeFactors.erase 11,
      (N.primeFactors.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors)).card = 1 := by
    intro r hr
    have hr11 : r ≠ 11 := (Finset.mem_erase.mp hr).1
    have hrS : r ∈ N.primeFactors := Finset.mem_of_mem_erase hr
    have hsub_pair : ({r, 11} : Finset ℕ) ⊆ N.primeFactors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hpair := Finset.sum_le_sum_of_subset (f := fun x =>
      (N.primeFactors.filter (fun p => x ∈ (oddComponentSigma N q p).primeFactors)).card - 1)
      hsub_pair
    rw [Finset.sum_pair hr11, hsum_r, hindeg11_eq] at hpair
    have hr_pos := hindeg_pos r hrS
    dsimp only at hr_pos
    omega
  have hindeg_q :
      (N.primeFactors.filter (fun p => q ∈ (oddComponentSigma N q p).primeFactors)).card = 1 :=
    hindeg_other_1 q (Finset.mem_erase.mpr ⟨h11q.symm, hq⟩)
  let S' := N.primeFactors.erase q
  let B := S'.filter (fun p => (oddComponentSigma N q p).primeFactors.card = 1)
  have hS'5 : S'.card = 5 := by
    have hqer := Finset.card_erase_add_one hq
    change S'.card + 1 = N.primeFactors.card at hqer
    omega
  have hB_ge4 : 4 ≤ B.card := by
    have hdiff_le : (S' \ B).card ≤ 1 := by
      have h1 : (S' \ B).card ≤ ∑ p ∈ S' \ B, ((oddComponentSigma N q p).primeFactors.card - 1) := by
        calc
          (S' \ B).card = ∑ _p ∈ S' \ B, 1 := by simp
          _ ≤ ∑ p ∈ S' \ B, ((oddComponentSigma N q p).primeFactors.card - 1) := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hpS' : p ∈ S' := (Finset.mem_sdiff.mp hp).1
            have hpS : p ∈ N.primeFactors := Finset.mem_of_mem_erase hpS'
            have hpnotB : p ∉ B := (Finset.mem_sdiff.mp hp).2
            have hpne1 : (oddComponentSigma N q p).primeFactors.card ≠ 1 := fun h =>
              hpnotB (Finset.mem_filter.mpr ⟨hpS', h⟩)
            have := hcard p hpS
            omega
      have h2 : ∑ p ∈ S' \ B, ((oddComponentSigma N q p).primeFactors.card - 1) ≤
          ∑ p ∈ N.primeFactors, ((oddComponentSigma N q p).primeFactors.card - 1) :=
        Finset.sum_le_sum_of_subset fun p hp =>
          Finset.mem_of_mem_erase (Finset.mem_sdiff.mp hp).1
      omega
    have hsum_card := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset
      (fun p => (oddComponentSigma N q p).primeFactors.card = 1) S')
    change (S' \ B).card + B.card = S'.card at hsum_card
    omega
  let C : Finset ℕ := {q, 11}
  have hB_to_C : ∀ p ∈ B, (oddComponentSigma N q p).primeFactors ⊆ C := by
    intro p hpB
    obtain ⟨hpS', hfp1⟩ := Finset.mem_filter.mp hpB
    have hpq : p ≠ q := (Finset.mem_erase.mp hpS').1
    have hpS : p ∈ N.primeFactors := Finset.mem_of_mem_erase hpS'
    obtain ⟨r, hfr⟩ := Finset.card_eq_one.mp hfp1
    have hr_fp : r ∈ (oddComponentSigma N q p).primeFactors := by
      rw [hfr]; exact Finset.mem_singleton_self r
    have hrS : r ∈ N.primeFactors := hsub p hpS hr_fp
    have hrC : r ∈ C := by
      by_contra hrnotC
      have hrq : r ≠ q := fun h => hrnotC (by simp [C, h])
      have hr11 : r ≠ 11 := fun h => hrnotC (by simp [C, h])
      have hindeg_r := hindeg_other_1 r (Finset.mem_erase.mpr ⟨hr11, hrS⟩)
      have hp3 := (isolated_singleton_forces_three ho hN hq hq4 he hev hpS hpq hfr hrq hindeg_r).1
      subst hp3
      rw [hf3_pf, Finset.singleton_inj] at hfr
      exact hr11 hfr.symm
    intro x hx
    rw [hfr, Finset.mem_singleton] at hx
    subst hx
    exact hrC
  have hB_le3 : B.card ≤ 3 := by
    have h1 : B.card ≤
        ∑ p ∈ B, ∑ r ∈ C, (if r ∈ (oddComponentSigma N q p).primeFactors then 1 else 0) := by
      calc
        B.card = ∑ _p ∈ B, 1 := by simp
        _ ≤ ∑ p ∈ B, ∑ r ∈ C, (if r ∈ (oddComponentSigma N q p).primeFactors then 1 else 0) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hfp1 : (oddComponentSigma N q p).primeFactors.card = 1 :=
            (Finset.mem_filter.mp hp).2
          rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one,
            Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (hB_to_C p hp), hfp1]
    have h2 :
        ∑ p ∈ B, ∑ r ∈ C, (if r ∈ (oddComponentSigma N q p).primeFactors then 1 else 0) ≤
          ∑ r ∈ C,
            (N.primeFactors.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors)).card := by
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun r _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      refine Finset.card_le_card fun p hp => ?_
      obtain ⟨hpB, hrp⟩ := Finset.mem_filter.mp hp
      have hpS : p ∈ N.primeFactors := Finset.mem_of_mem_erase (Finset.mem_filter.mp hpB).1
      exact Finset.mem_filter.mpr ⟨hpS, hrp⟩
    have h3 :
        ∑ r ∈ C,
          (N.primeFactors.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors)).card = 3 := by
      rw [Finset.sum_pair h11q.symm, hindeg_q, hindeg11_eq]
    omega
  omega

private theorem sigma_euler_eq_162_absurd {q a : ℕ} (hq : q.Prime)
    (hq4 : q % 4 = 1) (ha4 : a % 4 = 1) (hsig : sigma 1 (q ^ a) = 162) : False := by
  by_cases ha1 : a = 1
  · have hsig_q : sigma 1 (q ^ a) = 1 + q := by
      rw [ha1, sigma_one_apply_prime_pow hq, Finset.sum_range_succ, Finset.sum_range_one]
      simp
    have hq161 : q = 161 := by omega
    rw [hq161] at hq
    have h7 : 7 ∣ 161 := by norm_num
    rcases (Nat.dvd_prime hq).mp h7 with h | h <;> omega
  · have ha5 : 5 ≤ a := by omega
    have hq5 : 5 ≤ q := by
      have := hq.two_le
      omega
    have hpow4_le : q ^ 4 ≤ sigma 1 (q ^ a) := by
      rw [sigma_one_apply_prime_pow hq]
      exact Finset.single_le_sum (f := fun i => q ^ i) (a := 4) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (by omega))
    have h625_le : 625 ≤ q ^ 4 := by
      calc
        625 = 5 ^ 4 := by norm_num
        _ ≤ q ^ 4 := Nat.pow_le_pow_left hq5 4
    omega

private theorem collisionExcess_eq_one_absurd_of_indeg11_one {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hE1 : collisionExcess N q = 1)
    (hf3 : N.factorization 3 = 4)
    (hS6 : N.primeFactors.card = 6)
    (h3S : 3 ∈ N.primeFactors)
    (h11S : 11 ∈ N.primeFactors)
    (hval3 : oddComponentSigma N q 3 = 121)
    (h11_f3 : 11 ∈ (oddComponentSigma N q 3).primeFactors)
    (hindeg11_eq :
      (N.primeFactors.filter (fun p => 11 ∈ (oddComponentSigma N q p).primeFactors)).card = 1) :
    False := by
  obtain ⟨_, hprod, _, hcard⟩ := prod_oddComponentSigma_eq_self ho hN hq hq4 he hev
  obtain ⟨hsub, _, hindeg_pos, hE_p, hE_r⟩ :=
    oddComponentSigma_double_counting ho hN hq hq4 he hev
  let indeg : ℕ → ℕ := fun r =>
    (N.primeFactors.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors)).card
  have hsum_p : (∑ p ∈ N.primeFactors, ((oddComponentSigma N q p).primeFactors.card - 1)) = 1 :=
    hE_p.symm.trans hE1
  have hsum_r : (∑ r ∈ N.primeFactors, (indeg r - 1)) = 1 :=
    hE_r.symm.trans hE1
  have h3q : (3 : ℕ) ≠ q := by omega
  have h11q : (11 : ℕ) ≠ q := by omega
  have hfac11_eq :=
    factorization_eq_of_indeg_one ho hN hq hq4 he hev h3S h11S h11_f3 hindeg11_eq
  have hfac11_2 : N.factorization 11 = 2 := by
    rw [← hfac11_eq, hval3]
    have h121 : (121 : ℕ) = 11 ^ 2 := by norm_num
    rw [h121, Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    have h11p : Nat.Prime 11 := by decide
    simp [h11p.factorization_self]
  obtain ⟨_, hf11_pf⟩ := oddComponentSigma_eleven_eq hq4 hfac11_2
  have h7_f11 : 7 ∈ (oddComponentSigma N q 11).primeFactors := by rw [hf11_pf]; simp
  have h19_f11 : 19 ∈ (oddComponentSigma N q 11).primeFactors := by rw [hf11_pf]; simp
  have h7S : 7 ∈ N.primeFactors := hsub 11 h11S h7_f11
  have h19S : 19 ∈ N.primeFactors := hsub 11 h11S h19_f11
  have h7q : (7 : ℕ) ≠ q := by omega
  have h19q : (19 : ℕ) ≠ q := by omega
  have hf11_card : (oddComponentSigma N q 11).primeFactors.card = 2 := by
    rw [hf11_pf, Finset.card_pair (by decide)]
  have hcard_other_1 : ∀ p ∈ N.primeFactors.erase 11,
      (oddComponentSigma N q p).primeFactors.card = 1 := by
    intro p hp
    have hp11 : p ≠ 11 := (Finset.mem_erase.mp hp).1
    have hpS : p ∈ N.primeFactors := Finset.mem_of_mem_erase hp
    have hsub_pair : ({p, 11} : Finset ℕ) ⊆ N.primeFactors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hpair := Finset.sum_le_sum_of_subset
      (f := fun x => (oddComponentSigma N q x).primeFactors.card - 1) hsub_pair
    rw [Finset.sum_pair hp11, hsum_p, hf11_card] at hpair
    have hp_pos := hcard p hpS
    omega
  let T := ((N.primeFactors.erase q).erase 11).erase 3
  have hT_sub : T ⊆ N.primeFactors := fun p hp =>
    Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp))
  have hT3 : T.card = 3 := by
    have h11_erq : 11 ∈ N.primeFactors.erase q := Finset.mem_erase.mpr ⟨h11q, h11S⟩
    have h3_erq11 : 3 ∈ (N.primeFactors.erase q).erase 11 :=
      Finset.mem_erase.mpr ⟨by decide, Finset.mem_erase.mpr ⟨h3q, h3S⟩⟩
    have c1 := Finset.card_erase_add_one hq
    have c2 := Finset.card_erase_add_one h11_erq
    have c3 := Finset.card_erase_add_one h3_erq11
    change (N.primeFactors.erase q).card + 1 = N.primeFactors.card at c1
    change ((N.primeFactors.erase q).erase 11).card + 1 = (N.primeFactors.erase q).card at c2
    change T.card + 1 = ((N.primeFactors.erase q).erase 11).card at c3
    omega
  let C := N.primeFactors.filter (fun r => r = q ∨ 2 ≤ indeg r)
  have hC_sub : C ⊆ N.primeFactors := Finset.filter_subset _ _
  have hqC : q ∈ C := Finset.mem_filter.mpr ⟨hq, Or.inl rfl⟩
  have hC_bound : ∀ k : ℕ, C.card ≤ k → ∑ r ∈ C, indeg r ≤ k + 1 := by
    intro k hk
    have hsub_le : ∑ r ∈ C, (indeg r - 1) ≤ 1 := by
      have h := Finset.sum_le_sum_of_subset (f := fun r => indeg r - 1) hC_sub
      exact h.trans_eq hsum_r
    have hC_eq : ∑ r ∈ C, (indeg r - 1) = (∑ r ∈ C, indeg r) - C.card :=
      sum_sub_one_eq_sum_sub_card indeg fun r hr => hindeg_pos r (hC_sub hr)
    have hC_pos : C.card ≤ ∑ r ∈ C, indeg r := by
      calc
        C.card = ∑ _r ∈ C, 1 := by simp
        _ ≤ ∑ r ∈ C, indeg r := Finset.sum_le_sum fun r hr => hindeg_pos r (hC_sub hr)
    omega
  have hC_le2 : C.card ≤ 2 := by
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
    have h2 : ∑ r ∈ C.erase q, (indeg r - 1) ≤ ∑ r ∈ N.primeFactors, (indeg r - 1) :=
      Finset.sum_le_sum_of_subset fun r hr =>
        (Finset.mem_filter.mp (Finset.mem_of_mem_erase hr)).1
    have h3 := Finset.card_erase_add_one hqC
    omega
  have hsum_C_le3 : ∑ r ∈ C, indeg r ≤ 3 := hC_bound 2 hC_le2
  have hT_to_C : ∀ p ∈ T, (oddComponentSigma N q p).primeFactors ⊆ C := by
    intro p hpT
    have hp3_mem := Finset.mem_erase.mp hpT
    have hp11_mem := Finset.mem_erase.mp hp3_mem.2
    have hpq_mem := Finset.mem_erase.mp hp11_mem.2
    have hp3 : p ≠ 3 := hp3_mem.1
    have hp11 : p ≠ 11 := hp11_mem.1
    have hpq : p ≠ q := hpq_mem.1
    have hpS : p ∈ N.primeFactors := hpq_mem.2
    have hfp1 : (oddComponentSigma N q p).primeFactors.card = 1 :=
      hcard_other_1 p (Finset.mem_erase.mpr ⟨hp11, hpS⟩)
    obtain ⟨r, hfr⟩ := Finset.card_eq_one.mp hfp1
    have hr_fp : r ∈ (oddComponentSigma N q p).primeFactors := by
      rw [hfr]; exact Finset.mem_singleton_self r
    have hrS : r ∈ N.primeFactors := hsub p hpS hr_fp
    have hrC : r ∈ C := by
      by_contra hrnotC
      have hr_not_or : ¬ (r = q ∨ 2 ≤ indeg r) := fun h =>
        hrnotC (Finset.mem_filter.mpr ⟨hrS, h⟩)
      have hrq : r ≠ q := fun h => hr_not_or (Or.inl h)
      have hr_pos := hindeg_pos r hrS
      dsimp only at hr_pos
      have hindeg_r :
          (N.primeFactors.filter (fun x => r ∈ (oddComponentSigma N q x).primeFactors)).card = 1 := by
        dsimp only [indeg] at hr_not_or
        omega
      have hp_eq3 := (isolated_singleton_forces_three ho hN hq hq4 he hev hpS hpq hfr hrq hindeg_r).1
      exact hp3 hp_eq3
    intro x hx
    rw [hfr, Finset.mem_singleton] at hx
    subst hx
    exact hrC
  have hT_sum_eq :
      ∑ r ∈ C, (T.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors)).card = 3 := by
    have h1 :
        ∑ p ∈ T, ∑ r ∈ C, (if r ∈ (oddComponentSigma N q p).primeFactors then 1 else 0) = 3 := by
      calc
        ∑ p ∈ T, ∑ r ∈ C, (if r ∈ (oddComponentSigma N q p).primeFactors then 1 else 0)
            = ∑ p ∈ T, 1 := by
              refine Finset.sum_congr rfl fun p hp => ?_
              have hp11_mem := Finset.mem_erase.mp (Finset.mem_erase.mp hp).2
              have hpS : p ∈ N.primeFactors := (Finset.mem_erase.mp hp11_mem.2).2
              have hfp1 : (oddComponentSigma N q p).primeFactors.card = 1 :=
                hcard_other_1 p (Finset.mem_erase.mpr ⟨hp11_mem.1, hpS⟩)
              rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one,
                Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (hT_to_C p hp), hfp1]
        _ = T.card := by simp
        _ = 3 := hT3
    rw [Finset.sum_comm] at h1
    refine h1.symm ▸ Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
  have hT_filt_le :
      ∀ r ∈ C, (T.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors)).card ≤ indeg r :=
    fun r _ => Finset.card_le_card fun p hp => by
      obtain ⟨hpT, hrf⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hT_sub hpT, hrf⟩
  have hsum_C_eq3 : ∑ r ∈ C, indeg r = 3 := by
    have hle :
        ∑ r ∈ C, (T.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors)).card ≤
          ∑ r ∈ C, indeg r :=
      Finset.sum_le_sum hT_filt_le
    omega
  have hnot_C_of_not_T :
      ∀ p ∈ N.primeFactors, p ∉ T → ∀ r ∈ C, r ∉ (oddComponentSigma N q p).primeFactors := by
    intro p hpS hpnotT r hrC hrf
    have hlt_r : (T.filter (fun x => r ∈ (oddComponentSigma N q x).primeFactors)).card < indeg r := by
      refine Finset.card_lt_card (Finset.ssubset_iff_of_subset ?_ |>.mpr ?_)
      · intro x hx
        obtain ⟨hxT, hxrf⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨hT_sub hxT, hxrf⟩
      · exact ⟨p, Finset.mem_filter.mpr ⟨hpS, hrf⟩, fun hpT => hpnotT (Finset.mem_filter.mp hpT).1⟩
    have hsum_lt :
        ∑ x ∈ C, (T.filter (fun y => x ∈ (oddComponentSigma N q y).primeFactors)).card <
          ∑ x ∈ C, indeg x :=
      Finset.sum_lt_sum hT_filt_le ⟨r, hrC, hlt_r⟩
    omega
  have hC_eq2 : C.card = 2 := by
    by_contra hne2
    have hC1 : C.card ≤ 1 := by omega
    have hC_le2' := hC_bound 1 hC1
    omega
  have hCer1 : (C.erase q).card = 1 := by
    have := Finset.card_erase_add_one hqC
    omega
  obtain ⟨rstar, hrstar_eq⟩ := Finset.card_eq_one.mp hCer1
  have hrstar_mem : rstar ∈ C.erase q := by
    rw [hrstar_eq]; exact Finset.mem_singleton_self rstar
  have hrstar_q : rstar ≠ q := (Finset.mem_erase.mp hrstar_mem).1
  have hrstar_C : rstar ∈ C := Finset.mem_of_mem_erase hrstar_mem
  have hrstar_S : rstar ∈ N.primeFactors := hC_sub hrstar_C
  have hrstar_indeg2 : 2 ≤ indeg rstar := by
    rcases (Finset.mem_filter.mp hrstar_C).2 with rfl | h2
    · exact (hrstar_q rfl).elim
    · exact h2
  have hrstar_indeg_eq2 : indeg rstar = 2 := by
    have hle : indeg rstar - 1 ≤ ∑ r ∈ N.primeFactors, (indeg r - 1) :=
      Finset.single_le_sum (f := fun r => indeg r - 1) (fun _ _ => Nat.zero_le _) hrstar_S
    omega
  have hindeg_not_rstar_1 : ∀ r ∈ N.primeFactors, r ≠ rstar → indeg r = 1 := by
    intro r hrS hrr
    have hsub_pair : ({r, rstar} : Finset ℕ) ⊆ N.primeFactors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hpair := Finset.sum_le_sum_of_subset (f := fun x => indeg x - 1) hsub_pair
    rw [Finset.sum_pair hrr, hsum_r, hrstar_indeg_eq2] at hpair
    have hr_pos := hindeg_pos r hrS
    dsimp only at hr_pos
    dsimp only [indeg] at hpair hr_pos ⊢
    omega
  have hT_filt_eq :
      ∀ r ∈ C, (T.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors)).card = indeg r := by
    intro r hrC
    by_contra hne
    have hlt : (T.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors)).card < indeg r :=
      lt_of_le_of_ne (hT_filt_le r hrC) hne
    have hsum_lt :
        ∑ x ∈ C, (T.filter (fun p => x ∈ (oddComponentSigma N q p).primeFactors)).card <
          ∑ x ∈ C, indeg x :=
      Finset.sum_lt_sum hT_filt_le ⟨r, hrC, hlt⟩
    omega
  by_cases hrstar3 : rstar = 3
  · subst hrstar3
    have hT_3_card :
        (T.filter (fun p => 3 ∈ (oddComponentSigma N q p).primeFactors)).card = 2 := by
      have h := hT_filt_eq 3 hrstar_C
      omega
    obtain ⟨u₁, u₂, hu₁_mem, hu₂_mem, hu₁₂⟩ := Finset.one_lt_card_iff.mp
      (by omega : 1 < (T.filter (fun p => 3 ∈ (oddComponentSigma N q p).primeFactors)).card)
    obtain ⟨hu₁T, h3_u₁⟩ := Finset.mem_filter.mp hu₁_mem
    obtain ⟨hu₂T, h3_u₂⟩ := Finset.mem_filter.mp hu₂_mem
    have hu₁_3 : u₁ ≠ 3 := (Finset.mem_erase.mp hu₁T).1
    have hu₁_11 : u₁ ≠ 11 := (Finset.mem_erase.mp (Finset.mem_erase.mp hu₁T).2).1
    have hu₁_q : u₁ ≠ q :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hu₁T).2).2).1
    have hu₁S : u₁ ∈ N.primeFactors := hT_sub hu₁T
    have hu₂_11 : u₂ ≠ 11 := (Finset.mem_erase.mp (Finset.mem_erase.mp hu₂T).2).1
    have hu₂S : u₂ ∈ N.primeFactors := hT_sub hu₂T
    have hfu₁_card : (oddComponentSigma N q u₁).primeFactors.card = 1 :=
      hcard_other_1 u₁ (Finset.mem_erase.mpr ⟨hu₁_11, hu₁S⟩)
    have hfu₂_card : (oddComponentSigma N q u₂).primeFactors.card = 1 :=
      hcard_other_1 u₂ (Finset.mem_erase.mpr ⟨hu₂_11, hu₂S⟩)
    have hfu₁ : (oddComponentSigma N q u₁).primeFactors = {3} := by
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hfu₁_card
      have hx3 := h3_u₁
      rw [hx, Finset.mem_singleton] at hx3
      subst hx3
      exact hx
    have hfu₂ : (oddComponentSigma N q u₂).primeFactors = {3} := by
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hfu₂_card
      have hx3 := h3_u₂
      rw [hx, Finset.mem_singleton] at hx3
      subst hx3
      exact hx
    have hcomp₁ := oddComponentSigma_eq_prime_pow_of_card_one ho hN hq hq4 he hev hu₁S hfu₁
    have hcomp₂ := oddComponentSigma_eq_prime_pow_of_card_one ho hN hq hq4 he hev hu₂S hfu₂
    set k₁ := (oddComponentSigma N q u₁).factorization 3
    set k₂ := (oddComponentSigma N q u₂).factorization 3
    have hk₁_pos : 1 ≤ k₁ :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by rw [Nat.support_factorization]; exact h3_u₁))
    have hk₂_pos : 1 ≤ k₂ :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by rw [Nat.support_factorization]; exact h3_u₂))
    have hdvd_prod : oddComponentSigma N q u₁ * oddComponentSigma N q u₂ ∣ N := by
      conv_rhs =>
        rw [← hprod, ← Finset.mul_prod_erase N.primeFactors (oddComponentSigma N q) hu₁S,
          ← Finset.mul_prod_erase (N.primeFactors.erase u₁) (oddComponentSigma N q)
            (Finset.mem_erase.mpr ⟨hu₁₂.symm, hu₂S⟩), ← mul_assoc]
      exact dvd_mul_right _ _
    have h3pow_dvd : 3 ^ (k₁ + k₂) ∣ N := by
      rw [pow_add, ← hcomp₁, ← hcomp₂]
      exact hdvd_prod
    have hk_sum_le : k₁ + k₂ ≤ 4 := by
      have hle := ((by decide : Nat.Prime 3).pow_dvd_iff_le_factorization hN.2.ne').mp h3pow_dvd
      omega
    have hk₁_le3 : k₁ ≤ 3 := by omega
    have hcomp₁_le27 : oddComponentSigma N q u₁ ≤ 27 := by
      rw [hcomp₁]
      calc
        3 ^ k₁ ≤ 3 ^ 3 := Nat.pow_le_pow_right (by decide) hk₁_le3
        _ = 27 := by norm_num
    have hu₁_prime : u₁.Prime := Nat.prime_of_mem_primeFactors hu₁S
    have hu₁_odd : Odd u₁ := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hu₁S)
    have hu₁_ge5 : 5 ≤ u₁ := by
      have := hu₁_prime.two_le
      have := Nat.odd_iff.mp hu₁_odd
      omega
    obtain ⟨m, hm⟩ := hev u₁ hu₁_q
    have hu₁_pos : 0 < N.factorization u₁ :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hu₁S)
    have hu₁_ge2 : 2 ≤ N.factorization u₁ := by omega
    have hsum_ge : ∑ i ∈ Finset.range 3, u₁ ^ i ≤ oddComponentSigma N q u₁ := by
      have hcomp_eq : oddComponentSigma N q u₁ = sigma 1 (ordProj[u₁] N) := by
        unfold oddComponentSigma
        simp only [hu₁_q, ite_false]
      rw [hcomp_eq, sigma_one_apply_prime_pow hu₁_prime]
      exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega : 3 ≤ N.factorization u₁ + 1))
    have h3_sum : ∑ i ∈ Finset.range 3, u₁ ^ i = 1 + u₁ + u₁ ^ 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      ring
    have hge31 : 31 ≤ oddComponentSigma N q u₁ := by
      rw [h3_sum] at hsum_ge
      nlinarith
    omega
  · have h11_not_T : 11 ∉ T := fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).1 rfl
    have hq_not_T : q ∉ T := fun h =>
      (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).2).1 rfl
    have h7_not_C : 7 ∉ C := fun h => hnot_C_of_not_T 11 h11S h11_not_T 7 h h7_f11
    have h19_not_C : 19 ∉ C := fun h => hnot_C_of_not_T 11 h11S h11_not_T 19 h h19_f11
    have hrstar_7 : rstar ≠ 7 := fun h => h7_not_C (h ▸ hrstar_C)
    have hrstar_19 : rstar ≠ 19 := fun h => h19_not_C (h ▸ hrstar_C)
    have hrstar_11 : rstar ≠ 11 := fun h => by
      subst h
      change indeg 11 = 2 at hrstar_indeg_eq2
      change indeg 11 = 1 at hindeg11_eq
      omega
    let S6 : Finset ℕ := {q, 3, 11, 7, 19, rstar}
    have hS6_sub : S6 ⊆ N.primeFactors := by
      intro x hx
      simp only [S6, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    have hS6_card : S6.card = 6 := by
      have hq_notin : q ∉ ({3, 11, 7, 19, rstar} : Finset ℕ) := by
        simp [h3q.symm, h11q.symm, h7q.symm, h19q.symm, hrstar_q.symm]
      have h3_notin : 3 ∉ ({11, 7, 19, rstar} : Finset ℕ) := by simp [Ne.symm hrstar3]
      have h11_notin : 11 ∉ ({7, 19, rstar} : Finset ℕ) := by simp [Ne.symm hrstar_11]
      have h7_notin : 7 ∉ ({19, rstar} : Finset ℕ) := by simp [Ne.symm hrstar_7]
      have h19_notin : 19 ∉ ({rstar} : Finset ℕ) := by simp [Ne.symm hrstar_19]
      dsimp only [S6]
      rw [Finset.card_insert_of_notMem hq_notin, Finset.card_insert_of_notMem h3_notin,
        Finset.card_insert_of_notMem h11_notin, Finset.card_insert_of_notMem h7_notin,
        Finset.card_insert_of_notMem h19_notin, Finset.card_singleton]
    have hS_eq_S6 : N.primeFactors = S6 := (Finset.eq_of_subset_of_card_le hS6_sub (by omega)).symm
    have hfq_card : (oddComponentSigma N q q).primeFactors.card = 1 :=
      hcard_other_1 q (Finset.mem_erase.mpr ⟨h11q.symm, hq⟩)
    obtain ⟨tq, hfq_eq⟩ := Finset.card_eq_one.mp hfq_card
    have htq_fq : tq ∈ (oddComponentSigma N q q).primeFactors := by
      rw [hfq_eq]; exact Finset.mem_singleton_self tq
    have htq_S : tq ∈ N.primeFactors := hsub q hq htq_fq
    have htq_not_q : tq ≠ q := by
      intro htqq
      have hq_prime := Nat.prime_of_mem_primeFactors hq
      have hdvd : q ∣ oddComponentSigma N q q := Nat.dvd_of_mem_primeFactors (htqq ▸ htq_fq)
      have hdvd_sig : q ∣ sigma 1 (ordProj[q] N) := by
        refine hdvd.trans ?_
        unfold oddComponentSigma
        simp only [ite_true]
        exact Nat.div_dvd_of_dvd (by
          have hS4 := sigma_modEq_of_one hq_prime (show q ≡ 1 [MOD 4] from hq4) (N.factorization q)
          change sigma 1 (ordProj[q] N) % 4 = (N.factorization q + 1) % 4 at hS4
          exact Nat.dvd_of_mod_eq_zero (by omega))
      exact not_dvd_sigma_prime_pow_self hq_prime hdvd_sig
    have htq_not_rstar : tq ≠ rstar := fun h =>
      hnot_C_of_not_T q hq hq_not_T rstar hrstar_C (h ▸ htq_fq)
    have htq_not_11 : tq ≠ 11 := by
      intro h
      subst h
      have hsub2 : ({3, q} : Finset ℕ) ⊆
          N.primeFactors.filter (fun p => 11 ∈ (oddComponentSigma N q p).primeFactors) := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨h3S, h11_f3⟩
        · exact Finset.mem_filter.mpr ⟨hq, htq_fq⟩
      have h2le :
          2 ≤ (N.primeFactors.filter (fun p => 11 ∈ (oddComponentSigma N q p).primeFactors)).card := by
        calc
          2 = ({3, q} : Finset ℕ).card := (Finset.card_pair h3q).symm
          _ ≤ _ := Finset.card_le_card hsub2
      omega
    have htq_not_7 : tq ≠ 7 := by
      intro h
      subst h
      have hindeg7 := hindeg_not_rstar_1 7 h7S hrstar_7.symm
      have hsub2 : ({11, q} : Finset ℕ) ⊆
          N.primeFactors.filter (fun p => 7 ∈ (oddComponentSigma N q p).primeFactors) := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨h11S, h7_f11⟩
        · exact Finset.mem_filter.mpr ⟨hq, htq_fq⟩
      have h2le : 2 ≤ indeg 7 := by
        calc
          2 = ({11, q} : Finset ℕ).card := (Finset.card_pair h11q).symm
          _ ≤ indeg 7 := Finset.card_le_card hsub2
      omega
    have htq_not_19 : tq ≠ 19 := by
      intro h
      subst h
      have hindeg19 := hindeg_not_rstar_1 19 h19S hrstar_19.symm
      have hsub2 : ({11, q} : Finset ℕ) ⊆
          N.primeFactors.filter (fun p => 19 ∈ (oddComponentSigma N q p).primeFactors) := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨h11S, h19_f11⟩
        · exact Finset.mem_filter.mpr ⟨hq, htq_fq⟩
      have h2le : 2 ≤ indeg 19 := by
        calc
          2 = ({11, q} : Finset ℕ).card := (Finset.card_pair h11q).symm
          _ ≤ indeg 19 := Finset.card_le_card hsub2
      omega
    have htq_eq3 : tq = 3 := by
      have htq_S6 : tq ∈ S6 := hS_eq_S6 ▸ htq_S
      simp only [S6, Finset.mem_insert, Finset.mem_singleton] at htq_S6
      rcases htq_S6 with h | h | h | h | h | h
      · exact (htq_not_q h).elim
      · exact h
      · exact (htq_not_11 h).elim
      · exact (htq_not_7 h).elim
      · exact (htq_not_19 h).elim
      · exact (htq_not_rstar h).elim
    subst htq_eq3
    have hindeg3 := hindeg_not_rstar_1 3 h3S (Ne.symm hrstar3)
    have hfac3_eq :=
      factorization_eq_of_indeg_one ho hN hq hq4 he hev hq h3S htq_fq hindeg3
    have hcomp_q := oddComponentSigma_eq_prime_pow_of_card_one ho hN hq hq4 he hev hq hfq_eq
    rw [hfac3_eq, hf3] at hcomp_q
    have hcomp_q_81 : oddComponentSigma N q q = 81 := by
      rw [hcomp_q]
      norm_num
    have hq_prime := Nat.prime_of_mem_primeFactors hq
    have hS4 := sigma_modEq_of_one hq_prime (show q ≡ 1 [MOD 4] from hq4) (N.factorization q)
    change sigma 1 (ordProj[q] N) % 4 = (N.factorization q + 1) % 4 at hS4
    have hmod2 : sigma 1 (ordProj[q] N) % 4 = 2 := by omega
    have hsig_162 : sigma 1 (q ^ N.factorization q) = 162 := by
      have h1 : oddComponentSigma N q q = sigma 1 (ordProj[q] N) / 2 := by
        unfold oddComponentSigma
        simp only [ite_true]
      change oddComponentSigma N q q = sigma 1 (q ^ N.factorization q) / 2 at h1
      omega
    exact sigma_euler_eq_162_absurd hq_prime hq4 he hsig_162

/-- **2. Unconditional `2 ≤ collisionExcess N q` Across Every Odd Perfect Number**:
Rules out `collisionExcess N q = 0` via `6 ≤ ω(N)` and `ω(N) ≤ 3 * E + 3`, and rules out
`collisionExcess N q = 1` by exhaustive zero-slack structural analysis (`ω(N) = 6`, `3^4 ∣ N`,
`11 ∈ N.primeFactors`, both `2 ≤ indeg 11` and `indeg 11 = 1` with `7, 19 ∈ N.primeFactors`). -/
theorem two_le_collisionExcess_of_odd_perfect {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    2 ≤ collisionExcess N q := by
  have h6 : 6 ≤ N.primeFactors.card := six_le_distinct_prime_factor_count ho hN
  have hbound := odd_perfect_collision_excess_bound ho hN hq hq4 he hev
  have h3_uncond : N.primeFactors.card ≤ 3 * collisionExcess N q + 3 := hbound.2.1
  have h3_ne4 : N.factorization 3 ≠ 4 → N.primeFactors.card ≤ 3 * collisionExcess N q + 2 :=
    hbound.2.2.1
  by_contra! hlt
  have hE_cases : collisionExcess N q = 0 ∨ collisionExcess N q = 1 := by omega
  rcases hE_cases with hE0 | hE1
  · rw [hE0] at h3_uncond
    omega
  · have hf3 : N.factorization 3 = 4 := by
      by_contra hne4
      have := h3_ne4 hne4
      omega
    have hS6 : N.primeFactors.card = 6 := by omega
    have h3S : 3 ∈ N.primeFactors := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
      omega
    obtain ⟨hval3, hf3_pf⟩ := oddComponentSigma_three_eq hq4 hf3
    obtain ⟨hsub, _, hindeg_pos, _, _⟩ :=
      oddComponentSigma_double_counting ho hN hq hq4 he hev
    have h11_f3 : 11 ∈ (oddComponentSigma N q 3).primeFactors := by
      rw [hf3_pf]
      exact Finset.mem_singleton_self 11
    have h11S : 11 ∈ N.primeFactors := hsub 3 h3S h11_f3
    by_cases hindeg11_2 :
        2 ≤ (N.primeFactors.filter (fun p => 11 ∈ (oddComponentSigma N q p).primeFactors)).card
    · exact collisionExcess_eq_one_absurd_of_two_le_indeg11 ho hN hq hq4 he hev hE1 hS6
        h11S hf3_pf hindeg11_2
    · have hindeg11_pos := hindeg_pos 11 h11S
      dsimp only at hindeg11_pos
      have hindeg11_eq :
          (N.primeFactors.filter (fun p => 11 ∈ (oddComponentSigma N q p).primeFactors)).card = 1 := by
        omega
      exact collisionExcess_eq_one_absurd_of_indeg11_one ho hN hq hq4 he hev hE1 hf3 hS6 h3S
        h11S hval3 h11_f3 hindeg11_eq

/-- **3. Universal Double-or-Triple Sigma Collision**:
Every odd perfect number `N` satisfies `2 ≤ collisionExcess N q` (`ω(N) + 2 ≤ ∑ p, ω(c_p)`)
and unconditionally admits either an odd prime dividing three distinct component divisor sums
or two distinct odd primes each colliding across two distinct components. -/
theorem odd_perfect_double_or_triple_sigma_collision {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) :
    ((∃ r : ℕ, r.Prime ∧ Odd r ∧ r ∈ N.primeFactors ∧
        ∃ p₁ ∈ N.primeFactors, ∃ p₂ ∈ N.primeFactors, ∃ p₃ ∈ N.primeFactors,
          p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧
          r ∣ sigma 1 (ordProj[p₁] N) ∧
          r ∣ sigma 1 (ordProj[p₂] N) ∧
          r ∣ sigma 1 (ordProj[p₃] N)) ∨
      (∃ r₁ r₂ : ℕ, r₁.Prime ∧ r₂.Prime ∧ Odd r₁ ∧ Odd r₂ ∧
        r₁ ∈ N.primeFactors ∧ r₂ ∈ N.primeFactors ∧ r₁ ≠ r₂ ∧
        (∃ p₁ ∈ N.primeFactors, ∃ p₂ ∈ N.primeFactors, p₁ ≠ p₂ ∧
          r₁ ∣ sigma 1 (ordProj[p₁] N) ∧ r₁ ∣ sigma 1 (ordProj[p₂] N)) ∧
        (∃ p₁ ∈ N.primeFactors, ∃ p₂ ∈ N.primeFactors, p₁ ≠ p₂ ∧
          r₂ ∣ sigma 1 (ordProj[p₁] N) ∧ r₂ ∣ sigma 1 (ordProj[p₂] N)))) ∧
    (∃ q ∈ N.primeFactors, q % 4 = 1 ∧ N.factorization q % 4 = 1 ∧
      (∀ r : ℕ, r ≠ q → Even (N.factorization r)) ∧
      2 ≤ collisionExcess N q ∧
      N.primeFactors.card + 2 ≤ ∑ p ∈ N.primeFactors, (oddComponentSigma N q p).primeFactors.card) := by
  obtain ⟨q, hq, hq4, he, hev⟩ := euler_exponents ho hN
  have hE2 := two_le_collisionExcess_of_odd_perfect ho hN hq hq4 he hev
  have hle_inc := (odd_perfect_collision_excess_bound ho hN hq hq4 he hev).1
  obtain ⟨_, _, _, _, hE_r⟩ := oddComponentSigma_double_counting ho hN hq hq4 he hev
  let indeg : ℕ → ℕ := fun r =>
    (N.primeFactors.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors)).card
  have hsum2 : 2 ≤ ∑ r ∈ N.primeFactors, (indeg r - 1) := by
    have : collisionExcess N q = ∑ r ∈ N.primeFactors, (indeg r - 1) := hE_r
    omega
  have hdvd_of_mem : ∀ {p r : ℕ}, r ∈ (oddComponentSigma N q p).primeFactors →
      r ∣ sigma 1 (ordProj[p] N) := by
    intro p r hrp
    have hdvd1 : r ∣ oddComponentSigma N q p := Nat.dvd_of_mem_primeFactors hrp
    have hdvd2 : oddComponentSigma N q p ∣ sigma 1 (ordProj[p] N) := by
      unfold oddComponentSigma
      split_ifs with hpq
      · subst hpq
        have hq_prime := Nat.prime_of_mem_primeFactors hq
        have hS4 := sigma_modEq_of_one hq_prime (show p ≡ 1 [MOD 4] from hq4) (N.factorization p)
        change sigma 1 (ordProj[p] N) % 4 = (N.factorization p + 1) % 4 at hS4
        exact Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero (by omega))
      · exact dvd_rfl
    exact hdvd1.trans hdvd2
  let H := N.primeFactors.filter (fun r => 2 ≤ indeg r)
  have hH_sum : 2 ≤ ∑ r ∈ H, (indeg r - 1) := by
    have hsplit : ∑ r ∈ N.primeFactors, (indeg r - 1) =
        ∑ r ∈ H, (indeg r - 1) + ∑ r ∈ N.primeFactors \ H, (indeg r - 1) := by
      rw [← Finset.sum_sdiff (Finset.filter_subset (fun r => 2 ≤ indeg r) N.primeFactors), add_comm]
    have hzero : ∑ r ∈ N.primeFactors \ H, (indeg r - 1) = 0 := by
      refine Finset.sum_eq_zero fun r hr => ?_
      have hrN : r ∈ N.primeFactors := (Finset.mem_sdiff.mp hr).1
      have hrnotH : r ∉ H := (Finset.mem_sdiff.mp hr).2
      have hlt2 : ¬ 2 ≤ indeg r := fun h => hrnotH (Finset.mem_filter.mpr ⟨hrN, h⟩)
      omega
    omega
  have hdisj :
      (∃ r : ℕ, r.Prime ∧ Odd r ∧ r ∈ N.primeFactors ∧
        ∃ p₁ ∈ N.primeFactors, ∃ p₂ ∈ N.primeFactors, ∃ p₃ ∈ N.primeFactors,
          p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧
          r ∣ sigma 1 (ordProj[p₁] N) ∧
          r ∣ sigma 1 (ordProj[p₂] N) ∧
          r ∣ sigma 1 (ordProj[p₃] N)) ∨
      (∃ r₁ r₂ : ℕ, r₁.Prime ∧ r₂.Prime ∧ Odd r₁ ∧ Odd r₂ ∧
        r₁ ∈ N.primeFactors ∧ r₂ ∈ N.primeFactors ∧ r₁ ≠ r₂ ∧
        (∃ p₁ ∈ N.primeFactors, ∃ p₂ ∈ N.primeFactors, p₁ ≠ p₂ ∧
          r₁ ∣ sigma 1 (ordProj[p₁] N) ∧ r₁ ∣ sigma 1 (ordProj[p₂] N)) ∧
        (∃ p₁ ∈ N.primeFactors, ∃ p₂ ∈ N.primeFactors, p₁ ≠ p₂ ∧
          r₂ ∣ sigma 1 (ordProj[p₁] N) ∧ r₂ ∣ sigma 1 (ordProj[p₂] N))) := by
    by_cases htriple : ∃ r ∈ H, 3 ≤ indeg r
    · left
      obtain ⟨r, hrH, hr3⟩ := htriple
      have hrN : r ∈ N.primeFactors := (Finset.mem_filter.mp hrH).1
      have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hrN
      have hr_odd : Odd r := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hrN)
      have h2lt :
          2 < (N.primeFactors.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors)).card := by
        dsimp only [indeg] at hr3
        omega
      obtain ⟨p₁, hp₁, p₂, hp₂, p₃, hp₃, h12, h13, h23⟩ := Finset.two_lt_card.mp h2lt
      obtain ⟨hp₁N, hrp₁⟩ := Finset.mem_filter.mp hp₁
      obtain ⟨hp₂N, hrp₂⟩ := Finset.mem_filter.mp hp₂
      obtain ⟨hp₃N, hrp₃⟩ := Finset.mem_filter.mp hp₃
      exact ⟨r, hr_prime, hr_odd, hrN, p₁, hp₁N, p₂, hp₂N, p₃, hp₃N, h12, h13, h23,
        hdvd_of_mem hrp₁, hdvd_of_mem hrp₂, hdvd_of_mem hrp₃⟩
    · right
      push Not at htriple
      have hH_le : ∑ r ∈ H, (indeg r - 1) ≤ H.card := by
        calc
          ∑ r ∈ H, (indeg r - 1) ≤ ∑ _r ∈ H, 1 := by
            refine Finset.sum_le_sum fun r hr => ?_
            have := htriple r hr
            omega
          _ = H.card := by simp
      have h1lt_H : 1 < H.card := by omega
      obtain ⟨r₁, r₂, hr₁H, hr₂H, hrne⟩ := Finset.one_lt_card_iff.mp h1lt_H
      obtain ⟨hr₁N, hr₁2⟩ := Finset.mem_filter.mp hr₁H
      obtain ⟨hr₂N, hr₂2⟩ := Finset.mem_filter.mp hr₂H
      have h1lt₁ :
          1 < (N.primeFactors.filter (fun p => r₁ ∈ (oddComponentSigma N q p).primeFactors)).card := by
        dsimp only [indeg] at hr₁2; omega
      have h1lt₂ :
          1 < (N.primeFactors.filter (fun p => r₂ ∈ (oddComponentSigma N q p).primeFactors)).card := by
        dsimp only [indeg] at hr₂2; omega
      obtain ⟨p₁, p₂, hp₁, hp₂, hpne1⟩ := Finset.one_lt_card_iff.mp h1lt₁
      obtain ⟨hp₁N, hr₁p₁⟩ := Finset.mem_filter.mp hp₁
      obtain ⟨hp₂N, hr₁p₂⟩ := Finset.mem_filter.mp hp₂
      obtain ⟨p₃, p₄, hp₃, hp₄, hpne2⟩ := Finset.one_lt_card_iff.mp h1lt₂
      obtain ⟨hp₃N, hr₂p₃⟩ := Finset.mem_filter.mp hp₃
      obtain ⟨hp₄N, hr₂p₄⟩ := Finset.mem_filter.mp hp₄
      exact ⟨r₁, r₂, Nat.prime_of_mem_primeFactors hr₁N, Nat.prime_of_mem_primeFactors hr₂N,
        ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr₁N),
        ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr₂N),
        hr₁N, hr₂N, hrne,
        ⟨p₁, hp₁N, p₂, hp₂N, hpne1, hdvd_of_mem hr₁p₁, hdvd_of_mem hr₁p₂⟩,
        ⟨p₃, hp₃N, p₄, hp₄N, hpne2, hdvd_of_mem hr₂p₃, hdvd_of_mem hr₂p₄⟩⟩
  refine ⟨hdisj, ⟨q, hq, hq4, he, hev, hE2, ?_⟩⟩
  unfold collisionExcess at hE2
  omega

/-- **4. Collision Excess Least-Prime Logarithmic Bound**:
Couples `odd_perfect_collision_excess_bound` with `omega_gt_least_prime_mul_log_two` to bound
`((N.minFac : ℝ) - 1) * Real.log 2` unconditionally by `3 * collisionExcess N q + 3` (and
`3 * collisionExcess N q + 2` when `¬ 3 ∣ N`). -/
theorem collision_excess_least_prime_log_bound {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    ((N.minFac : ℝ) - 1) * Real.log 2 < 3 * (collisionExcess N q : ℝ) + 3 ∧
    (¬ 3 ∣ N → ((N.minFac : ℝ) - 1) * Real.log 2 < 3 * (collisionExcess N q : ℝ) + 2) := by
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
  have hbound := odd_perfect_collision_excess_bound ho hN hq hq4 he hev
  have h3_uncond : (N.primeFactors.card : ℝ) ≤ 3 * (collisionExcess N q : ℝ) + 3 := by
    exact_mod_cast hbound.2.1
  refine ⟨by linarith, fun h3 => ?_⟩
  have h3_free : (N.primeFactors.card : ℝ) ≤ 3 * (collisionExcess N q : ℝ) + 2 := by
    exact_mod_cast hbound.2.2.2 h3
  linarith

end OddPerfect
