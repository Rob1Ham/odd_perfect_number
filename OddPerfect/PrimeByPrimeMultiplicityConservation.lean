module

public import OddPerfect.LocalRepeatSquarefreeObstruction
public import OddPerfect.HalfRankCollisionObstruction
import OddPerfect.OddValuationCycleObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Prime-by-Prime Multiplicity Conservation (`OddPerfect.PrimeByPrimeMultiplicityConservation`)

Formalizes exact prime-by-prime incoming multiplicity conservation across the multiplicative
Euler-component decomposition `N = ∏ p ∈ N.primeFactors, oddComponentSigma N q p`, mutual exclusion
between collisions and local repeats at exponent-two primes, and the global exponential-radical
lower bound on `N`:

1. `indegAt` and `localRepeatAt`: incoming component degree and incoming local-repeat excess at
   a prime `r`.
2. `factorization_eq_indegAt_add_localRepeatAt`:
   For every `r ∈ N.primeFactors`, `1 ≤ indegAt N q r`, `N.factorization r = indegAt N q r + localRepeatAt N q r`,
   and `indegAt N q r ≤ N.factorization r`, together with the dual global sum identities
   `∑ r ∈ N.primeFactors, localRepeatAt N q r = localRepeatExcess N q` and
   `∑ r ∈ N.primeFactors, (indegAt N q r - 1) = collisionExcess N q`.
3. `euler_linear_and_exponent_two_mutual_exclusion`:
   When `N.factorization q = 1`, `indegAt N q q = 1`, `localRepeatAt N q q = 0`, and no component
   is divisible by `q ^ 2`; for every prime `r ∈ N.primeFactors` with `N.factorization r = 2`,
   either `r` splits squarefree across two distinct components (`indegAt N q r = 2`,
   `localRepeatAt N q r = 0`) or concentrates as a prime square in a single component
   (`indegAt N q r = 1`, `localRepeatAt N q r = 1`).
4. `rad_mul_minFac_pow_excess_le_self`:
   `(∏ r ∈ N.primeFactors, r) * N.minFac ^ (localRepeatExcess N q + collisionExcess N q) ≤ N`,
   `N.minFac ^ (N.primeFactors.card + localRepeatExcess N q + collisionExcess N q) ≤ N`, and on
   any sixth-power-free `N`, `53 ≤ N.minFac`, `(∏ r ∈ N.primeFactors, r) * 53 ^ 736 ≤ N`, and
   `53 ^ 1179 ≤ N`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- Incoming component multiplicity (number of prime components `p ∈ N.primeFactors` whose divisor
sum `oddComponentSigma N q p` is divisible by `r`). -/
@[expose] def indegAt (N q r : ℕ) : ℕ :=
  (N.primeFactors.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors)).card

/-- Total local repeat multiplicity of prime `r` accumulated across all components
`oddComponentSigma N q p`. -/
@[expose] def localRepeatAt (N q r : ℕ) : ℕ :=
  ∑ p ∈ N.primeFactors,
    ((oddComponentSigma N q p).factorization r -
      if r ∈ (oddComponentSigma N q p).primeFactors then 1 else 0)

/-- **1. Prime-by-Prime Multiplicity Conservation**:
For every prime factor `r ∈ N.primeFactors`, `N.factorization r = indegAt N q r + localRepeatAt N q r`
with `1 ≤ indegAt N q r ≤ N.factorization r`, and summing `localRepeatAt N q r` and
`indegAt N q r - 1` over `r ∈ N.primeFactors` recovers `localRepeatExcess N q` and
`collisionExcess N q`, respectively. -/
theorem factorization_eq_indegAt_add_localRepeatAt {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1)
    (he : N.factorization q % 4 = 1) (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    (∀ r ∈ N.primeFactors,
      1 ≤ indegAt N q r ∧
      N.factorization r = indegAt N q r + localRepeatAt N q r ∧
      indegAt N q r ≤ N.factorization r) ∧
    (∑ r ∈ N.primeFactors, localRepeatAt N q r) = localRepeatExcess N q ∧
    (∑ r ∈ N.primeFactors, (indegAt N q r - 1)) = collisionExcess N q := by
  obtain ⟨hprops, hprod, hbi, _⟩ := prod_oddComponentSigma_eq_self ho hN hq hq4 he hev
  let S := N.primeFactors
  let f : ℕ → Finset ℕ := fun p => (oddComponentSigma N q p).primeFactors
  have hc0 : ∀ p ∈ S, oddComponentSigma N q p ≠ 0 := fun p hp => by
    have := (hprops p hp).2.2
    omega
  have hsub : ∀ p ∈ S, f p ⊆ S := by
    intro p hp r hr
    dsimp only [S]
    rw [← hbi]
    exact Finset.mem_biUnion.mpr ⟨p, hp, hr⟩
  have hindeg_sum : ∀ r : ℕ,
      indegAt N q r = ∑ p ∈ S, (if r ∈ f p then 1 else 0) := by
    intro r
    unfold indegAt
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
  have hfac_add : ∀ r : ℕ,
      N.factorization r = indegAt N q r + localRepeatAt N q r := by
    intro r
    have hprod_fac : N.factorization r = ∑ p ∈ S, (oddComponentSigma N q p).factorization r := by
      conv_lhs => rw [← hprod]
      exact Nat.factorization_prod_apply hc0
    rw [hprod_fac, hindeg_sum r]
    unfold localRepeatAt
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    dsimp only [f]
    split_ifs with hrp
    · have hpos : 1 ≤ (oddComponentSigma N q p).factorization r :=
        Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hrp)
      omega
    · simp
  have hindeg_pos : ∀ r ∈ S, 1 ≤ indegAt N q r := by
    intro r hr
    have hr' : r ∈ S.biUnion f := hbi.symm ▸ hr
    obtain ⟨p, hp, hrp⟩ := Finset.mem_biUnion.mp hr'
    exact Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hrp⟩⟩
  have hpart1 : ∀ r ∈ N.primeFactors,
      1 ≤ indegAt N q r ∧
      N.factorization r = indegAt N q r + localRepeatAt N q r ∧
      indegAt N q r ≤ N.factorization r := by
    intro r hr
    have h1 := hindeg_pos r hr
    have h2 := hfac_add r
    exact ⟨h1, h2, by omega⟩
  have hpart2 : (∑ r ∈ S, localRepeatAt N q r) = localRepeatExcess N q := by
    unfold localRepeatAt localRepeatExcess
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hsum_ind : (∑ r ∈ S, (if r ∈ f p then 1 else 0)) = (f p).card := by
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (hsub p hp)]
    have hsum_fac : (∑ r ∈ S, (oddComponentSigma N q p).factorization r) =
        cardFactors (oddComponentSigma N q p) := by
      rw [cardFactors_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
      exact (Finset.sum_subset (hsub p hp) fun r _ hrf =>
        Finsupp.notMem_support_iff.mp hrf).symm
    have hadd :
        (∑ r ∈ S,
          ((oddComponentSigma N q p).factorization r -
            if r ∈ (oddComponentSigma N q p).primeFactors then 1 else 0)) +
          (oddComponentSigma N q p).primeFactors.card =
        cardFactors (oddComponentSigma N q p) := by
      rw [← hsum_fac, ← hsum_ind, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      dsimp only [f]
      split_ifs with hrp
      · have hpos : 1 ≤ (oddComponentSigma N q p).factorization r :=
          Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hrp)
        omega
      · simp
    exact Nat.eq_sub_of_add_eq hadd
  have hpart3 : (∑ r ∈ S, (indegAt N q r - 1)) = collisionExcess N q := by
    have hsum_sub : (∑ r ∈ S, (indegAt N q r - 1)) + S.card = ∑ r ∈ S, indegAt N q r := by
      calc
        (∑ r ∈ S, (indegAt N q r - 1)) + S.card
            = (∑ r ∈ S, (indegAt N q r - 1)) + ∑ _r ∈ S, 1 := by simp
        _ = ∑ r ∈ S, ((indegAt N q r - 1) + 1) := by rw [← Finset.sum_add_distrib]
        _ = ∑ r ∈ S, indegAt N q r := Finset.sum_congr rfl fun r hr =>
            Nat.sub_add_cancel (hindeg_pos r hr)
    have hdouble : (∑ r ∈ S, indegAt N q r) = ∑ p ∈ S, (f p).card := by
      calc
        ∑ r ∈ S, indegAt N q r
            = ∑ r ∈ S, ∑ p ∈ S, (if r ∈ f p then 1 else 0) :=
              Finset.sum_congr rfl fun r _ => hindeg_sum r
        _ = ∑ p ∈ S, ∑ r ∈ S, (if r ∈ f p then 1 else 0) := Finset.sum_comm
        _ = ∑ p ∈ S, (f p).card := by
              refine Finset.sum_congr rfl fun p hp => ?_
              rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one,
                Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (hsub p hp)]
    have hadd : (∑ r ∈ N.primeFactors, (indegAt N q r - 1)) + N.primeFactors.card =
        ∑ p ∈ N.primeFactors, (oddComponentSigma N q p).primeFactors.card :=
      hsum_sub.trans hdouble
    unfold collisionExcess
    exact Nat.eq_sub_of_add_eq hadd
  exact ⟨hpart1, hpart2, hpart3⟩

/-- **2. Linear-Euler & Exponent-Two Mutual Exclusion**:
- If `N.factorization q = 1`, then `indegAt N q q = 1`, `localRepeatAt N q q = 0`, and no
  component `oddComponentSigma N q p` is divisible by `q ^ 2`.
- For every `r ∈ N.primeFactors` with `N.factorization r = 2`, either `r` splits across two
  distinct components (`indegAt N q r = 2 ∧ localRepeatAt N q r = 0` and no component is
  divisible by `r ^ 2`) or `r ^ 2` concentrates in a unique component (`indegAt N q r = 1 ∧
  localRepeatAt N q r = 1`). -/
theorem euler_linear_and_exponent_two_mutual_exclusion {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1)
    (he : N.factorization q % 4 = 1) (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    (N.factorization q = 1 →
      indegAt N q q = 1 ∧
      localRepeatAt N q q = 0 ∧
      ∀ p ∈ N.primeFactors, ¬ q ^ 2 ∣ oddComponentSigma N q p) ∧
    (∀ r ∈ N.primeFactors, N.factorization r = 2 →
      (indegAt N q r = 2 ∧
        localRepeatAt N q r = 0 ∧
        ∀ p ∈ N.primeFactors, ¬ r ^ 2 ∣ oddComponentSigma N q p) ∨
      (indegAt N q r = 1 ∧
        localRepeatAt N q r = 1 ∧
        ∃ p ∈ N.primeFactors,
          r ^ 2 ∣ oddComponentSigma N q p ∧
          ∀ x ∈ N.primeFactors, x ≠ p → ¬ r ∣ oddComponentSigma N q x)) := by
  obtain ⟨hprops, hprod, _, _⟩ := prod_oddComponentSigma_eq_self ho hN hq hq4 he hev
  obtain ⟨hcons, _, _⟩ := factorization_eq_indegAt_add_localRepeatAt ho hN hq hq4 he hev
  have hc0 : ∀ p ∈ N.primeFactors, oddComponentSigma N q p ≠ 0 := fun p hp => by
    have := (hprops p hp).2.2
    omega
  have hlinear : N.factorization q = 1 →
      indegAt N q q = 1 ∧
      localRepeatAt N q q = 0 ∧
      ∀ p ∈ N.primeFactors, ¬ q ^ 2 ∣ oddComponentSigma N q p := by
    intro hq1
    obtain ⟨h1, h2, h3⟩ := hcons q hq
    refine ⟨by omega, by omega, fun p hp hdvd => ?_⟩
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have h2le : 2 ≤ (oddComponentSigma N q p).factorization q :=
      (hq_prime.pow_dvd_iff_le_factorization (hc0 p hp)).mp hdvd
    have hsum_le : (oddComponentSigma N q p).factorization q ≤
        ∑ x ∈ N.primeFactors, (oddComponentSigma N q x).factorization q :=
      Finset.single_le_sum (f := fun x => (oddComponentSigma N q x).factorization q)
        (fun _ _ => Nat.zero_le _) hp
    have hprod_fac : N.factorization q =
        ∑ x ∈ N.primeFactors, (oddComponentSigma N q x).factorization q := by
      conv_lhs => rw [← hprod]
      exact Nat.factorization_prod_apply hc0
    omega
  refine ⟨hlinear, fun r hr hr2 => ?_⟩
  have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr
  obtain ⟨h1, h2, _⟩ := hcons r hr
  have hsplit : (indegAt N q r = 2 ∧ localRepeatAt N q r = 0) ∨
      (indegAt N q r = 1 ∧ localRepeatAt N q r = 1) := by omega
  rcases hsplit with ⟨hi2, hl0⟩ | ⟨hi1, hl1⟩
  · left
    refine ⟨hi2, hl0, fun p hp hdvd => ?_⟩
    have h2le : 2 ≤ (oddComponentSigma N q p).factorization r :=
      (hr_prime.pow_dvd_iff_le_factorization (hc0 p hp)).mp hdvd
    have hrp : r ∈ (oddComponentSigma N q p).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hr_prime, (dvd_pow_self r (by decide : 2 ≠ 0)).trans hdvd, hc0 p hp⟩
    have hterm_le : ((oddComponentSigma N q p).factorization r -
        if r ∈ (oddComponentSigma N q p).primeFactors then 1 else 0) ≤ localRepeatAt N q r := by
      unfold localRepeatAt
      exact Finset.single_le_sum
        (f := fun x => (oddComponentSigma N q x).factorization r -
          if r ∈ (oddComponentSigma N q x).primeFactors then 1 else 0)
        (fun _ _ => Nat.zero_le _) hp
    simp [hrp] at hterm_le
    omega
  · right
    refine ⟨hi1, hl1, ?_⟩
    have hne : (N.primeFactors.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors)).Nonempty :=
      Finset.card_pos.mp (by unfold indegAt at hi1; omega)
    obtain ⟨p, hp_filt⟩ := hne
    obtain ⟨hpS, hrp⟩ := Finset.mem_filter.mp hp_filt
    have hnot_other : ∀ x ∈ N.primeFactors, x ≠ p → ¬ r ∣ oddComponentSigma N q x := by
      intro x hx hxp hdvd
      have hrx : r ∈ (oddComponentSigma N q x).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hr_prime, hdvd, hc0 x hx⟩
      have hsub2 : ({x, p} : Finset ℕ) ⊆
          N.primeFactors.filter (fun y => r ∈ (oddComponentSigma N q y).primeFactors) := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hx, hrx⟩
        · exact Finset.mem_filter.mpr ⟨hpS, hrp⟩
      have h2le : 2 ≤ indegAt N q r := by
        unfold indegAt
        calc
          2 = ({x, p} : Finset ℕ).card := (Finset.card_pair hxp).symm
          _ ≤ (N.primeFactors.filter (fun y => r ∈ (oddComponentSigma N q y).primeFactors)).card :=
            Finset.card_le_card hsub2
      omega
    have hprod_fac : N.factorization r =
        ∑ x ∈ N.primeFactors, (oddComponentSigma N q x).factorization r := by
      conv_lhs => rw [← hprod]
      exact Nat.factorization_prod_apply hc0
    have hsum_erase : (∑ x ∈ N.primeFactors.erase p, (oddComponentSigma N q x).factorization r) = 0 :=
      Finset.sum_eq_zero fun x hx =>
        Nat.factorization_eq_zero_of_not_dvd
          (hnot_other x (Finset.mem_of_mem_erase hx) (Finset.mem_erase.mp hx).1)
    have hsplit_sum :
        (∑ x ∈ N.primeFactors, (oddComponentSigma N q x).factorization r) =
          (oddComponentSigma N q p).factorization r +
            ∑ x ∈ N.primeFactors.erase p, (oddComponentSigma N q x).factorization r :=
      (Finset.add_sum_erase N.primeFactors (fun x => (oddComponentSigma N q x).factorization r) hpS).symm
    have hp_fac2 : (oddComponentSigma N q p).factorization r = 2 := by omega
    have hp_sq : r ^ 2 ∣ oddComponentSigma N q p :=
      (hr_prime.pow_dvd_iff_le_factorization (hc0 p hpS)).mpr (by omega)
    exact ⟨p, hpS, hp_sq, hnot_other⟩

/-- **3. Global Exponential-Radical Lower Bound**:
`(∏ r ∈ N.primeFactors, r) * N.minFac ^ (localRepeatExcess N q + collisionExcess N q) ≤ N`,
`N.minFac ^ (N.primeFactors.card + localRepeatExcess N q + collisionExcess N q) ≤ N`, and on
any sixth-power-free odd perfect number `N`, `53 ≤ N.minFac`,
`(∏ r ∈ N.primeFactors, r) * 53 ^ 736 ≤ N`, and `53 ^ 1179 ≤ N`. -/
theorem rad_mul_minFac_pow_excess_le_self {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1)
    (he : N.factorization q % 4 = 1) (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    (∏ r ∈ N.primeFactors, r) * N.minFac ^ (localRepeatExcess N q + collisionExcess N q) ≤ N ∧
    N.minFac ^ (N.primeFactors.card + localRepeatExcess N q + collisionExcess N q) ≤ N ∧
    ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
      53 ≤ N.minFac ∧ (∏ r ∈ N.primeFactors, r) * 53 ^ 736 ≤ N ∧ 53 ^ 1179 ≤ N) := by
  have hN0 : N ≠ 0 := hN.2.ne'
  have hdecomp := cardFactors_eq_primeFactors_add_localRepeat_add_collisionExcess ho hN hq hq4 he hev
  have hpos_fac : ∀ r ∈ N.primeFactors, 1 ≤ N.factorization r := fun r hr =>
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
  have hmin_le : ∀ r ∈ N.primeFactors, N.minFac ≤ r := fun r hr =>
    Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hr).two_le (Nat.dvd_of_mem_primeFactors hr)
  have hsum_sub :
      ∑ r ∈ N.primeFactors, (N.factorization r - 1) = localRepeatExcess N q + collisionExcess N q := by
    have hcf : cardFactors N = ∑ r ∈ N.primeFactors, N.factorization r := by
      rw [cardFactors_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
    have hadd : (∑ r ∈ N.primeFactors, (N.factorization r - 1)) + N.primeFactors.card =
        ∑ r ∈ N.primeFactors, N.factorization r := by
      calc
        (∑ r ∈ N.primeFactors, (N.factorization r - 1)) + N.primeFactors.card
            = (∑ r ∈ N.primeFactors, (N.factorization r - 1)) + ∑ _r ∈ N.primeFactors, 1 := by simp
        _ = ∑ r ∈ N.primeFactors, ((N.factorization r - 1) + 1) := by rw [← Finset.sum_add_distrib]
        _ = ∑ r ∈ N.primeFactors, N.factorization r :=
            Finset.sum_congr rfl fun r hr => Nat.sub_add_cancel (hpos_fac r hr)
    omega
  have hN_eq : N = (∏ r ∈ N.primeFactors, r) * ∏ r ∈ N.primeFactors, r ^ (N.factorization r - 1) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hN0]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun r hr => ?_
    have h1 := hpos_fac r hr
    conv_lhs => rw [← Nat.add_sub_of_le h1, pow_add, pow_one]
  have hpow_le :
      N.minFac ^ (localRepeatExcess N q + collisionExcess N q) ≤
        ∏ r ∈ N.primeFactors, r ^ (N.factorization r - 1) := by
    rw [← hsum_sub, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod fun r hr => Nat.pow_le_pow_left (hmin_le r hr) _
  have hrad_bound :
      (∏ r ∈ N.primeFactors, r) * N.minFac ^ (localRepeatExcess N q + collisionExcess N q) ≤ N := by
    calc
      (∏ r ∈ N.primeFactors, r) * N.minFac ^ (localRepeatExcess N q + collisionExcess N q)
          ≤ (∏ r ∈ N.primeFactors, r) * ∏ r ∈ N.primeFactors, r ^ (N.factorization r - 1) :=
            Nat.mul_le_mul_left _ hpow_le
      _ = N := hN_eq.symm
  have hfull_pow :
      N.minFac ^ (N.primeFactors.card + localRepeatExcess N q + collisionExcess N q) ≤ N := by
    have hcf : cardFactors N = ∑ r ∈ N.primeFactors, N.factorization r := by
      rw [cardFactors_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
    rw [← hdecomp, hcf, ← Finset.prod_pow_eq_pow_sum]
    calc
      ∏ r ∈ N.primeFactors, N.minFac ^ N.factorization r
          ≤ ∏ r ∈ N.primeFactors, r ^ N.factorization r :=
            Finset.prod_le_prod fun r hr => Nat.pow_le_pow_left (hmin_le r hr) _
      _ = N := (Nat.prod_primeFactors_pow_factorization hN0).symm
  refine ⟨hrad_bound, hfull_pow, ?_⟩
  intro hfree
  have hN1 : N ≠ 1 := by
    rintro rfl
    simp at hq
  have hmin_mem : N.minFac ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime hN1, Nat.minFac_dvd N, hN0⟩
  have h53 : 53 ≤ N.minFac := sixth_power_free_min_prime_ge_53 ho hN hfree hmin_mem
  have h736 : 736 ≤ localRepeatExcess N q + collisionExcess N q :=
    (cyclotomic_slope_excess_bounds ho hN hq hq4 he hev).2.2 hfree
  have h443 : 443 ≤ N.primeFactors.card :=
    (sixth_power_free_collision_excess_ge_221 ho hN hq hq4 he hev hfree).1
  have hpow736 : 53 ^ 736 ≤ N.minFac ^ (localRepeatExcess N q + collisionExcess N q) := by
    have h1 : 53 ^ 736 ≤ 53 ^ (localRepeatExcess N q + collisionExcess N q) :=
      pow_le_pow_right₀ (by decide : 1 ≤ 53) h736
    have h2 : 53 ^ (localRepeatExcess N q + collisionExcess N q) ≤
        N.minFac ^ (localRepeatExcess N q + collisionExcess N q) :=
      Nat.pow_le_pow_left h53 (localRepeatExcess N q + collisionExcess N q)
    exact h1.trans h2
  have hrad53 : (∏ r ∈ N.primeFactors, r) * 53 ^ 736 ≤ N :=
    (Nat.mul_le_mul_left _ hpow736).trans hrad_bound
  have hpow1179 : 53 ^ 1179 ≤ N := by
    have h1 : 53 ^ 1179 ≤ 53 ^ (N.primeFactors.card + localRepeatExcess N q + collisionExcess N q) :=
      pow_le_pow_right₀ (by decide : 1 ≤ 53) (by omega)
    have h2 : 53 ^ (N.primeFactors.card + localRepeatExcess N q + collisionExcess N q) ≤
        N.minFac ^ (N.primeFactors.card + localRepeatExcess N q + collisionExcess N q) :=
      Nat.pow_le_pow_left h53 (N.primeFactors.card + localRepeatExcess N q + collisionExcess N q)
    exact (h1.trans h2).trans hfull_pow
  exact ⟨h53, hrad53, hpow1179⟩

end OddPerfect
