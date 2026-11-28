module

public import OddPerfect.PrimeByPrimeMultiplicityConservation
public import OddPerfect.GlobalObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Local Repeat Drop Conservation (`OddPerfect.LocalRepeatDropConservation`)

Formalizes the exact global component-index drop vs. excess conservation identity, its
pigeonhole and uniform-drop rank-cap corollaries, and local-repeat ramification lower bounds
at quadratic and quartic components:

1. `componentIndex_drop_eq_exponent_add_oddComponentSigma`:
   Expresses `Ω(i_p) + v_p(N) + Ω(c_p)` in terms of `Ω(N)` for `p = q` and `p ≠ q`, and shows
   `Ω(i_p) ≤ Ω(N)` for all `p ∈ N.primeFactors`.
2. `sum_componentIndex_drop_eq_primeFactors_add_two_mul_excess`:
   `∑ p ∈ N.primeFactors, (Ω(N) - Ω(i_p)) = ω(N) + 2 * (localRepeatExcess N q + collisionExcess N q) + 1`.
3. `exists_componentIndex_drop_mul_ge_and_uniform_drop_cap`:
   Pigeonhole drop lower bound, uniform drop cap `2 * (M + E) + 1 ≤ (D - 1) * ω(N)`, and the
   `D = 4` rank caps `ω(N) ≤ 35` (and `ω(N) ≤ 11` when `¬ 3 ∣ N`).
4. `localRepeat_quadratic_and_quartic_ramification_bounds`:
   `rad(c_p) * 7 ^ (Ω(c_p) - ω(c_p)) ≤ c_p` at `v_p(N) = 2` and
   `rad(c_p) * 11 ^ (Ω(c_p) - ω(c_p)) ≤ c_p` at `v_p(N) = 4`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- **1. Component-Index Drop vs. Odd Component Multiplicity**:
At the Euler prime `q`, `Ω(i_q) + v_q(N) + Ω(c_q) = Ω(N)`; at every non-Euler prime
`p ∈ N.primeFactors.erase q`, `Ω(i_p) + v_p(N) + Ω(c_p) = 1 + Ω(N)`. Consequently,
`Ω(i_p) ≤ Ω(N)` for all `p ∈ N.primeFactors`. -/
theorem componentIndex_drop_eq_exponent_add_oddComponentSigma {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1)
    (he : N.factorization q % 4 = 1) (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    (cardFactors (componentIndex N q) + N.factorization q + cardFactors (oddComponentSigma N q q) =
      cardFactors N) ∧
    (∀ p ∈ N.primeFactors.erase q,
      cardFactors (componentIndex N p) + N.factorization p + cardFactors (oddComponentSigma N q p) =
        1 + cardFactors N) ∧
    (∀ p ∈ N.primeFactors, cardFactors (componentIndex N p) ≤ cardFactors N) := by
  obtain ⟨hprops, _, _, _⟩ := prod_oddComponentSigma_eq_self ho hN hq hq4 he hev
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hS4 := sigma_modEq_of_one hq_prime (show q ≡ 1 [MOD 4] from hq4) (N.factorization q)
  change sigma 1 (ordProj[q] N) % 4 = (N.factorization q + 1) % 4 at hS4
  have hS_even : sigma 1 (ordProj[q] N) = 2 * oddComponentSigma N q q := by
    have hdef : oddComponentSigma N q q = sigma 1 (ordProj[q] N) / 2 := by
      simp [oddComponentSigma]
    omega
  have hcq0 : oddComponentSigma N q q ≠ 0 := by
    have := (hprops q hq).2.2
    omega
  have hcard_sig_q :
      cardFactors (sigma 1 (ordProj[q] N)) = 1 + cardFactors (oddComponentSigma N q q) := by
    rw [hS_even, cardFactors_mul (by decide : (2 : ℕ) ≠ 0) hcq0,
      cardFactors_apply_prime Nat.prime_two]
  have hq_eq :
      cardFactors (componentIndex N q) + N.factorization q + cardFactors (oddComponentSigma N q q) =
        cardFactors N := by
    have hcons := cardFactors_componentIndex_add_eq hN hq
    rw [hcard_sig_q] at hcons
    omega
  have hp_eq :
      ∀ p ∈ N.primeFactors.erase q,
        cardFactors (componentIndex N p) + N.factorization p +
            cardFactors (oddComponentSigma N q p) =
          1 + cardFactors N := by
    intro p hp
    obtain ⟨hpq, hp_mem⟩ := Finset.mem_erase.mp hp
    have hdef : oddComponentSigma N q p = sigma 1 (ordProj[p] N) := by
      simp [oddComponentSigma, hpq]
    rw [hdef]
    exact cardFactors_componentIndex_add_eq hN hp_mem
  have hle : ∀ p ∈ N.primeFactors, cardFactors (componentIndex N p) ≤ cardFactors N := by
    intro p hp
    by_cases hpq : p = q
    · subst hpq
      omega
    · have hp_er : p ∈ N.primeFactors.erase q := Finset.mem_erase.mpr ⟨hpq, hp⟩
      have hcons := hp_eq p hp_er
      have hpos : 1 ≤ N.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
      have hev_p : Even (N.factorization p) := hev p hpq
      have h2le : 2 ≤ N.factorization p := by
        rcases hev_p with ⟨k, hk⟩
        omega
      omega
  exact ⟨hq_eq, hp_eq, hle⟩

/-- **2. Global Component-Index Drop vs. Excess Conservation Identity**:
`∑ p ∈ N.primeFactors, (Ω(N) - Ω(i_p)) = ω(N) + 2 * (localRepeatExcess N q + collisionExcess N q) + 1`. -/
theorem sum_componentIndex_drop_eq_primeFactors_add_two_mul_excess {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1)
    (he : N.factorization q % 4 = 1) (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    (∑ p ∈ N.primeFactors, (cardFactors N - cardFactors (componentIndex N p))) =
      N.primeFactors.card + 2 * (localRepeatExcess N q + collisionExcess N q) + 1 := by
  obtain ⟨hq_eq, hp_eq, hle⟩ :=
    componentIndex_drop_eq_exponent_add_oddComponentSigma ho hN hq hq4 he hev
  have hsplit_drop :
      (∑ p ∈ N.primeFactors, (cardFactors N - cardFactors (componentIndex N p))) =
        (cardFactors N - cardFactors (componentIndex N q)) +
          ∑ p ∈ N.primeFactors.erase q, (cardFactors N - cardFactors (componentIndex N p)) :=
    (Finset.add_sum_erase N.primeFactors
      (fun p => cardFactors N - cardFactors (componentIndex N p)) hq).symm
  have hcard_erase : (N.primeFactors.erase q).card = N.primeFactors.card - 1 :=
    Finset.card_erase_of_mem hq
  have hadd_erase :
      (∑ p ∈ N.primeFactors.erase q, (cardFactors N - cardFactors (componentIndex N p))) +
          (N.primeFactors.card - 1) =
        ∑ p ∈ N.primeFactors.erase q,
          (N.factorization p + cardFactors (oddComponentSigma N q p)) := by
    calc
      (∑ p ∈ N.primeFactors.erase q, (cardFactors N - cardFactors (componentIndex N p))) +
          (N.primeFactors.card - 1)
          = (∑ p ∈ N.primeFactors.erase q, (cardFactors N - cardFactors (componentIndex N p))) +
              ∑ _p ∈ N.primeFactors.erase q, 1 := by
            rw [Finset.sum_const, smul_eq_mul, mul_one, hcard_erase]
      _ = ∑ p ∈ N.primeFactors.erase q,
            ((cardFactors N - cardFactors (componentIndex N p)) + 1) := by
            rw [← Finset.sum_add_distrib]
      _ = ∑ p ∈ N.primeFactors.erase q,
            (N.factorization p + cardFactors (oddComponentSigma N q p)) := by
            refine Finset.sum_congr rfl fun p hp => ?_
            have hle_p := hle p (Finset.mem_of_mem_erase hp)
            have hcons := hp_eq p hp
            omega
  have hsum_all :
      (∑ p ∈ N.primeFactors, (cardFactors N - cardFactors (componentIndex N p))) +
          (N.primeFactors.card - 1) =
        (∑ p ∈ N.primeFactors, N.factorization p) +
          ∑ p ∈ N.primeFactors, cardFactors (oddComponentSigma N q p) := by
    calc
      (∑ p ∈ N.primeFactors, (cardFactors N - cardFactors (componentIndex N p))) +
          (N.primeFactors.card - 1)
          = (cardFactors N - cardFactors (componentIndex N q)) +
              ((∑ p ∈ N.primeFactors.erase q, (cardFactors N - cardFactors (componentIndex N p))) +
                (N.primeFactors.card - 1)) := by
            rw [hsplit_drop, add_assoc]
      _ = (N.factorization q + cardFactors (oddComponentSigma N q q)) +
            ∑ p ∈ N.primeFactors.erase q,
              (N.factorization p + cardFactors (oddComponentSigma N q p)) := by
            have hle_q := hle q hq
            rw [hadd_erase]
            congr 1
            omega
      _ = ∑ p ∈ N.primeFactors, (N.factorization p + cardFactors (oddComponentSigma N q p)) :=
            Finset.add_sum_erase N.primeFactors
              (fun p => N.factorization p + cardFactors (oddComponentSigma N q p)) hq
      _ = (∑ p ∈ N.primeFactors, N.factorization p) +
            ∑ p ∈ N.primeFactors, cardFactors (oddComponentSigma N q p) :=
            Finset.sum_add_distrib
  have hsum_fac : (∑ p ∈ N.primeFactors, N.factorization p) = cardFactors N := by
    rw [cardFactors_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
  have hsum_sig :
      (∑ p ∈ N.primeFactors, cardFactors (oddComponentSigma N q p)) = cardFactors N :=
    sum_cardFactors_oddComponentSigma_eq ho hN hq hq4 he hev
  have hdecomp := cardFactors_eq_primeFactors_add_localRepeat_add_collisionExcess ho hN hq hq4 he hev
  have hω_pos : 1 ≤ N.primeFactors.card := Finset.card_pos.mpr ⟨q, hq⟩
  rw [hsum_fac, hsum_sig] at hsum_all
  omega

/-- **3. Pigeonhole Drop Lower Bound and Uniform-Drop Rank Caps**:
- Some prime `p ∈ N.primeFactors` satisfies
  `ω(N) + 2 * (localRepeatExcess N q + collisionExcess N q) + 1 ≤ ω(N) * (Ω(N) - Ω(i_p))`.
- Any uniform drop bound `Ω(N) - Ω(i_p) ≤ D` forces
  `2 * (localRepeatExcess N q + collisionExcess N q) + 1 ≤ (D - 1) * ω(N)`.
- In particular, a uniform drop bound `D = 4` forces `ω(N) ≤ 35` unconditionally and
  `ω(N) ≤ 11` whenever `¬ 3 ∣ N`. -/
theorem exists_componentIndex_drop_mul_ge_and_uniform_drop_cap {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1)
    (he : N.factorization q % 4 = 1) (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    (∃ p ∈ N.primeFactors,
      N.primeFactors.card + 2 * (localRepeatExcess N q + collisionExcess N q) + 1 ≤
        N.primeFactors.card * (cardFactors N - cardFactors (componentIndex N p))) ∧
    (∀ D : ℕ,
      (∀ p ∈ N.primeFactors, cardFactors N - cardFactors (componentIndex N p) ≤ D) →
        2 * (localRepeatExcess N q + collisionExcess N q) + 1 ≤ (D - 1) * N.primeFactors.card) ∧
    ((∀ p ∈ N.primeFactors, cardFactors N - cardFactors (componentIndex N p) ≤ 4) →
      N.primeFactors.card ≤ 35 ∧ (¬ 3 ∣ N → N.primeFactors.card ≤ 11)) := by
  have hsum := sum_componentIndex_drop_eq_primeFactors_add_two_mul_excess ho hN hq hq4 he hev
  have hpig :
      ∃ p ∈ N.primeFactors,
        N.primeFactors.card + 2 * (localRepeatExcess N q + collisionExcess N q) + 1 ≤
          N.primeFactors.card * (cardFactors N - cardFactors (componentIndex N p)) := by
    by_contra! hlt
    have hsum_lt :
        (∑ p ∈ N.primeFactors,
            N.primeFactors.card * (cardFactors N - cardFactors (componentIndex N p))) <
          ∑ _p ∈ N.primeFactors,
            (N.primeFactors.card + 2 * (localRepeatExcess N q + collisionExcess N q) + 1) :=
      Finset.sum_lt_sum_of_nonempty ⟨q, hq⟩ hlt
    rw [← Finset.mul_sum, hsum, Finset.sum_const, smul_eq_mul] at hsum_lt
    exact (lt_irrefl _) hsum_lt
  have hunif :
      ∀ D : ℕ,
        (∀ p ∈ N.primeFactors, cardFactors N - cardFactors (componentIndex N p) ≤ D) →
          2 * (localRepeatExcess N q + collisionExcess N q) + 1 ≤
            (D - 1) * N.primeFactors.card := by
    intro D hD
    obtain ⟨p, hp, hge⟩ := hpig
    have hmul_le :
        N.primeFactors.card * (cardFactors N - cardFactors (componentIndex N p)) ≤
          N.primeFactors.card * D :=
      Nat.mul_le_mul_left _ (hD p hp)
    have hleD :
        N.primeFactors.card + 2 * (localRepeatExcess N q + collisionExcess N q) + 1 ≤
          N.primeFactors.card * D :=
      hge.trans hmul_le
    have hω_pos : 1 ≤ N.primeFactors.card := Finset.card_pos.mpr ⟨q, hq⟩
    rcases eq_or_ne D 0 with rfl | hD0
    · simp at hleD
    · have hmul_eq : N.primeFactors.card * D = N.primeFactors.card + (D - 1) * N.primeFactors.card := by
        calc
          N.primeFactors.card * D = D * N.primeFactors.card := Nat.mul_comm _ _
          _ = (1 + (D - 1)) * N.primeFactors.card := by rw [Nat.add_sub_of_le (by omega)]
          _ = 1 * N.primeFactors.card + (D - 1) * N.primeFactors.card := Nat.add_mul 1 (D - 1) _
          _ = N.primeFactors.card + (D - 1) * N.primeFactors.card := by rw [one_mul]
      omega
  refine ⟨hpig, hunif, ?_⟩
  intro h4
  have hcap3 := hunif 4 h4
  have hslope := cyclotomic_slope_excess_bounds ho hN hq hq4 he hev
  have h13 :
      13 * N.primeFactors.card ≤ 8 * (localRepeatExcess N q + collisionExcess N q) + 39 := by
    have := hslope.1
    omega
  refine ⟨by omega, fun h3 => ?_⟩
  have h5 :
      5 * N.primeFactors.card ≤ 3 * (localRepeatExcess N q + collisionExcess N q) + 7 := by
    have := hslope.2.1 h3
    omega
  omega

private theorem rad_mul_base_pow_localRepeat_le {c B : ℕ} (hc0 : c ≠ 0)
    (hB : ∀ r ∈ c.primeFactors, 2 ≤ c.factorization r → B ≤ r) :
    (∏ r ∈ c.primeFactors, r) * B ^ (cardFactors c - c.primeFactors.card) ≤ c := by
  have hc_eq : c = (∏ r ∈ c.primeFactors, r) * ∏ r ∈ c.primeFactors, r ^ (c.factorization r - 1) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hc0]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun r hr => ?_
    have h1 : 1 ≤ c.factorization r := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
    conv_lhs => rw [← Nat.add_sub_of_le h1, pow_add, pow_one]
  have hsum_sub :
      ∑ r ∈ c.primeFactors, (c.factorization r - 1) = cardFactors c - c.primeFactors.card := by
    have hcf : cardFactors c = ∑ r ∈ c.primeFactors, c.factorization r := by
      rw [cardFactors_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
    have hadd :
        (∑ r ∈ c.primeFactors, (c.factorization r - 1)) + c.primeFactors.card =
          ∑ r ∈ c.primeFactors, c.factorization r := by
      calc
        (∑ r ∈ c.primeFactors, (c.factorization r - 1)) + c.primeFactors.card
            = (∑ r ∈ c.primeFactors, (c.factorization r - 1)) + ∑ _r ∈ c.primeFactors, 1 := by
              simp
        _ = ∑ r ∈ c.primeFactors, ((c.factorization r - 1) + 1) := by
              rw [← Finset.sum_add_distrib]
        _ = ∑ r ∈ c.primeFactors, c.factorization r :=
              Finset.sum_congr rfl fun r hr =>
                Nat.sub_add_cancel (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr))
    omega
  have hpow_le :
      B ^ (cardFactors c - c.primeFactors.card) ≤
        ∏ r ∈ c.primeFactors, r ^ (c.factorization r - 1) := by
    rw [← hsum_sub, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod fun r hr => ?_
    by_cases hr2 : 2 ≤ c.factorization r
    · exact Nat.pow_le_pow_left (hB r hr hr2) _
    · have h1 : 1 ≤ c.factorization r := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
      have h0 : c.factorization r - 1 = 0 := by omega
      rw [h0, pow_zero, pow_zero]
  calc
    (∏ r ∈ c.primeFactors, r) * B ^ (cardFactors c - c.primeFactors.card)
        ≤ (∏ r ∈ c.primeFactors, r) * ∏ r ∈ c.primeFactors, r ^ (c.factorization r - 1) :=
          Nat.mul_le_mul_left _ hpow_le
    _ = c := hc_eq.symm

/-- **4. Local-Repeat Ramification Lower Bounds (`7^Δ` and `11^Δ`)**:
- At every quadratic non-Euler component `p ∈ N.primeFactors.erase q` with `v_p(N) = 2`,
  `rad(c_p) * 7 ^ (Ω(c_p) - ω(c_p)) ≤ c_p`.
- At every quartic non-Euler component `p ∈ N.primeFactors.erase q` with `v_p(N) = 4`,
  `rad(c_p) * 11 ^ (Ω(c_p) - ω(c_p)) ≤ c_p`. -/
theorem localRepeat_quadratic_and_quartic_ramification_bounds {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1)
    (he : N.factorization q % 4 = 1) (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    (∀ p ∈ N.primeFactors.erase q, N.factorization p = 2 →
      (∏ r ∈ (oddComponentSigma N q p).primeFactors, r) *
        7 ^ (cardFactors (oddComponentSigma N q p) - (oddComponentSigma N q p).primeFactors.card) ≤
        oddComponentSigma N q p) ∧
    (∀ p ∈ N.primeFactors.erase q, N.factorization p = 4 →
      (∏ r ∈ (oddComponentSigma N q p).primeFactors, r) *
        11 ^ (cardFactors (oddComponentSigma N q p) - (oddComponentSigma N q p).primeFactors.card) ≤
        oddComponentSigma N q p) := by
  obtain ⟨hprops, _, _, _⟩ := prod_oddComponentSigma_eq_self ho hN hq hq4 he hev
  constructor
  · intro p hp hp2
    obtain ⟨hpq, hp_mem⟩ := Finset.mem_erase.mp hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hp_odd : Odd p := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp_mem)
    have hc0 : oddComponentSigma N q p ≠ 0 := by
      have := (hprops p hp_mem).2.2
      omega
    have hceq : oddComponentSigma N q p = sigma 1 (p ^ 2) := by
      simp [oddComponentSigma, hpq, hp2]
    refine rad_mul_base_pow_localRepeat_le hc0 fun r hr hr2 => ?_
    have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hdvd : r ^ 2 ∣ sigma 1 (p ^ 2) := by
      rw [← hceq]
      exact (hr_prime.pow_dvd_iff_le_factorization hc0).mpr hr2
    exact (sigma_prime_sq_sq_dvd_prime_mod_three hp_prime hp_odd hr_prime hdvd).2.2.1
  · intro p hp hp4
    obtain ⟨hpq, hp_mem⟩ := Finset.mem_erase.mp hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hp_odd : Odd p := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp_mem)
    have hc0 : oddComponentSigma N q p ≠ 0 := by
      have := (hprops p hp_mem).2.2
      omega
    have hceq : oddComponentSigma N q p = sigma 1 (p ^ 4) := by
      simp [oddComponentSigma, hpq, hp4]
    refine rad_mul_base_pow_localRepeat_le hc0 fun r hr hr2 => ?_
    have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hdvd : r ^ 2 ∣ sigma 1 (p ^ 4) := by
      rw [← hceq]
      exact (hr_prime.pow_dvd_iff_le_factorization hc0).mpr hr2
    exact (sigma_prime_pow_four_sq_dvd_prime_mod_five hp_prime hp_odd hr_prime hdvd).2.2.1

end OddPerfect
