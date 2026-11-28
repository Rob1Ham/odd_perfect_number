module

public import OddPerfect.PrimeReciprocalLog
public import OddPerfect.ZelinskyReciprocal
public import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dyadic prime-reciprocal obstruction for odd perfect numbers

Using `one_half_le_sum_primes_ge_one_div` from Mathlib (`∑_{k ≤ p ≤ 4^(π(k-1)+1)} 1/p ≥ 1/2`)
and the unconditional bound `∑_{p ∣ N} 1/p < log 2 < 5/6` from `OddPerfect.PrimeReciprocalLog`,
we show that:
1. Any two consecutive dyadic prime blocks sum to at least `1` in prime reciprocals.
2. Every odd perfect number omits a prime in every double dyadic block `[k₁, B₂]`.
3. Every odd perfect number divisible by `3` omits a prime in every single dyadic block
   `[k, 4^(π(k-1)+1)]` for `k ≥ 4`, and in particular omits a prime in `[5, 61]`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma le_four_pow_primesBelow_card_add_one (k : ℕ) :
    k ≤ 4 ^ (k.primesBelow.card + 1) := by
  have hsum : (1 / 2 : ℝ) ≤
      ∑ p ∈ (4 ^ (k.primesBelow.card + 1) + 1).primesBelow \ k.primesBelow, (1 / (p : ℝ)) := by
    simpa [Nat.succ_eq_add_one] using one_half_le_sum_primes_ge_one_div k
  have hne : ((4 ^ (k.primesBelow.card + 1) + 1).primesBelow \ k.primesBelow).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hsum
    linarith
  obtain ⟨p, hp⟩ := hne
  rw [Finset.mem_sdiff, Nat.mem_primesBelow, Nat.mem_primesBelow] at hp
  have hp_ge : k ≤ p := by
    by_contra hlt
    exact hp.2 ⟨by omega, hp.1.2⟩
  omega

private lemma log_two_lt_five_sixths : Real.log 2 < 5 / 6 := by
  have hexp1 : (17 / 12 : ℝ) ≤ Real.exp (5 / 12) := by
    linarith [Real.add_one_le_exp (5 / 12 : ℝ)]
  have hexp2 : (2 : ℝ) < Real.exp (5 / 6) := by
    have hsq : (17 / 12 : ℝ) ^ 2 ≤ Real.exp (5 / 12) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hexp1 2
    have hadd : Real.exp (5 / 12) ^ 2 = Real.exp (5 / 6) := by
      rw [sq, ← Real.exp_add]
      norm_num
    linarith [show (2 : ℝ) < (17 / 12 : ℝ) ^ 2 by norm_num]
  exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr hexp2

/-- Two consecutive dyadic prime-reciprocal blocks are disjoint, cover
`(B₂ + 1).primesBelow \ k₁.primesBelow`, and have reciprocal sum at least `1`. -/
theorem dyadic_two_block_prime_reciprocal_ge_one (k₁ : ℕ) :
    let B₁ := 4 ^ (k₁.primesBelow.card + 1)
    let B₂ := 4 ^ ((B₁ + 1).primesBelow.card + 1)
    Disjoint ((B₁ + 1).primesBelow \ k₁.primesBelow)
      ((B₂ + 1).primesBelow \ (B₁ + 1).primesBelow) ∧
    ((B₁ + 1).primesBelow \ k₁.primesBelow) ∪
      ((B₂ + 1).primesBelow \ (B₁ + 1).primesBelow) =
      (B₂ + 1).primesBelow \ k₁.primesBelow ∧
    (1 : ℝ) ≤ ∑ p ∈ (B₂ + 1).primesBelow \ k₁.primesBelow, (1 / (p : ℝ)) := by
  dsimp only
  set B₁ := 4 ^ (k₁.primesBelow.card + 1)
  set B₂ := 4 ^ ((B₁ + 1).primesBelow.card + 1)
  have hkB₁ : k₁ ≤ B₁ + 1 := Nat.le_succ_of_le (le_four_pow_primesBelow_card_add_one k₁)
  have hB₁B₂ : B₁ + 1 ≤ B₂ + 1 := Nat.le_succ_of_le (le_four_pow_primesBelow_card_add_one (B₁ + 1))
  have hsub₁ : k₁.primesBelow ⊆ (B₁ + 1).primesBelow := Nat.primesBelow_mono hkB₁
  have hsub₂ : (B₁ + 1).primesBelow ⊆ (B₂ + 1).primesBelow := Nat.primesBelow_mono hB₁B₂
  have hdisj :
      Disjoint ((B₁ + 1).primesBelow \ k₁.primesBelow)
        ((B₂ + 1).primesBelow \ (B₁ + 1).primesBelow) :=
    Finset.disjoint_left.mpr fun p hp1 hp2 =>
      (Finset.mem_sdiff.mp hp2).2 (Finset.mem_sdiff.mp hp1).1
  have hunion :
      ((B₁ + 1).primesBelow \ k₁.primesBelow) ∪
        ((B₂ + 1).primesBelow \ (B₁ + 1).primesBelow) =
        (B₂ + 1).primesBelow \ k₁.primesBelow := by
    ext p
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
      · exact ⟨hsub₂ hp1, hp2⟩
      · exact ⟨hp1, fun hk => hp2 (hsub₁ hk)⟩
    · rintro ⟨hp1, hp2⟩
      by_cases h : p ∈ (B₁ + 1).primesBelow
      · exact Or.inl ⟨h, hp2⟩
      · exact Or.inr ⟨hp1, h⟩
  refine ⟨hdisj, hunion, ?_⟩
  rw [← hunion, Finset.sum_union hdisj]
  have h1 : (1 / 2 : ℝ) ≤ ∑ p ∈ (B₁ + 1).primesBelow \ k₁.primesBelow, (1 / (p : ℝ)) := by
    simpa [B₁, Nat.succ_eq_add_one] using one_half_le_sum_primes_ge_one_div k₁
  have h2 : (1 / 2 : ℝ) ≤ ∑ p ∈ (B₂ + 1).primesBelow \ (B₁ + 1).primesBelow, (1 / (p : ℝ)) := by
    simpa [B₂, Nat.succ_eq_add_one] using one_half_le_sum_primes_ge_one_div (B₁ + 1)
  linarith

/-- Every odd perfect number omits at least one prime in every double dyadic interval
`[k₁, B₂]`. -/
theorem odd_perfect_omits_prime_in_every_double_dyadic_interval {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) (k₁ : ℕ) :
    let B₁ := 4 ^ (k₁.primesBelow.card + 1)
    let B₂ := 4 ^ ((B₁ + 1).primesBelow.card + 1)
    ∃ p : ℕ, p.Prime ∧ k₁ ≤ p ∧ p ≤ B₂ ∧ ¬ p ∣ N := by
  dsimp only
  set B₁ := 4 ^ (k₁.primesBelow.card + 1)
  set B₂ := 4 ^ ((B₁ + 1).primesBelow.card + 1)
  have hge : (1 : ℝ) ≤ ∑ p ∈ (B₂ + 1).primesBelow \ k₁.primesBelow, (1 / (p : ℝ)) :=
    (dyadic_two_block_prime_reciprocal_ge_one k₁).2.2
  have hlt_log : (∑ p ∈ N.primeFactors, (1 : ℝ) / (p : ℝ)) < Real.log 2 :=
    sum_inv_primeFactors_lt_log_two ho hN
  have hlog : Real.log 2 < 5 / 6 := log_two_lt_five_sixths
  have hnot_sub : ¬ ((B₂ + 1).primesBelow \ k₁.primesBelow ⊆ N.primeFactors) := by
    intro hsub
    have hsum_le :
        (∑ p ∈ (B₂ + 1).primesBelow \ k₁.primesBelow, (1 / (p : ℝ))) ≤
          ∑ p ∈ N.primeFactors, (1 : ℝ) / (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity
    linarith
  obtain ⟨p, hp_in, hp_out⟩ := Finset.not_subset.mp hnot_sub
  rw [Finset.mem_sdiff, Nat.mem_primesBelow, Nat.mem_primesBelow] at hp_in
  have hp_prime : p.Prime := hp_in.1.2
  have hp_le : p ≤ B₂ := by omega
  have hk_le : k₁ ≤ p := by
    by_contra hlt
    exact hp_in.2 ⟨by omega, hp_prime⟩
  have hndvd : ¬ p ∣ N := by
    intro hdvd
    exact hp_out (Nat.mem_primeFactors.mpr ⟨hp_prime, hdvd, hN.2.ne'⟩)
  exact ⟨p, hp_prime, hk_le, hp_le, hndvd⟩

/-- If `3 ∣ N` for an odd perfect number `N`, then `N` omits a prime in every single dyadic
interval `[k, 4^(π(k-1)+1)]` for `k ≥ 4`, and in particular omits a prime in `[5, 61]`. -/
theorem odd_perfect_three_dvd_omits_prime_in_single_dyadic_interval {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) (h3 : 3 ∣ N) :
    (∀ k : ℕ, 4 ≤ k →
      ∃ p : ℕ, p.Prime ∧ k ≤ p ∧ p ≤ 4 ^ (k.primesBelow.card + 1) ∧ ¬ p ∣ N) ∧
    (∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ≤ 61 ∧ ¬ p ∣ N) := by
  have hforall :
      ∀ k : ℕ, 4 ≤ k →
        ∃ p : ℕ, p.Prime ∧ k ≤ p ∧ p ≤ 4 ^ (k.primesBelow.card + 1) ∧ ¬ p ∣ N := by
    intro k hk4
    set B := 4 ^ (k.primesBelow.card + 1)
    have h3_in_k : 3 ∈ k.primesBelow := Nat.mem_primesBelow.mpr ⟨by omega, by decide⟩
    have h3_not_in_diff : 3 ∉ (B + 1).primesBelow \ k.primesBelow := fun h =>
      (Finset.mem_sdiff.mp h).2 h3_in_k
    have h3_mem : 3 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, h3, hN.2.ne'⟩
    have hge_half : (1 / 2 : ℝ) ≤ ∑ p ∈ (B + 1).primesBelow \ k.primesBelow, (1 / (p : ℝ)) := by
      simpa [B, Nat.succ_eq_add_one] using one_half_le_sum_primes_ge_one_div k
    have hlt_log : (∑ p ∈ N.primeFactors, (1 : ℝ) / (p : ℝ)) < Real.log 2 :=
      sum_inv_primeFactors_lt_log_two ho hN
    have hlog : Real.log 2 < 5 / 6 := log_two_lt_five_sixths
    have hnot_sub : ¬ ((B + 1).primesBelow \ k.primesBelow ⊆ N.primeFactors) := by
      intro hsub
      have hsub_ins : insert 3 ((B + 1).primesBelow \ k.primesBelow) ⊆ N.primeFactors :=
        Finset.insert_subset_iff.mpr ⟨h3_mem, hsub⟩
      have hsum_le :
          (∑ p ∈ insert 3 ((B + 1).primesBelow \ k.primesBelow), (1 / (p : ℝ))) ≤
            ∑ p ∈ N.primeFactors, (1 : ℝ) / (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub_ins fun p _ _ => by positivity
      rw [Finset.sum_insert h3_not_in_diff] at hsum_le
      simp only [Nat.cast_ofNat] at hsum_le
      linarith
    obtain ⟨p, hp_in, hp_out⟩ := Finset.not_subset.mp hnot_sub
    rw [Finset.mem_sdiff, Nat.mem_primesBelow, Nat.mem_primesBelow] at hp_in
    have hp_prime : p.Prime := hp_in.1.2
    have hp_le : p ≤ B := by omega
    have hk_le : k ≤ p := by
      by_contra hlt
      exact hp_in.2 ⟨by omega, hp_prime⟩
    have hndvd : ¬ p ∣ N := by
      intro hdvd
      exact hp_out (Nat.mem_primeFactors.mpr ⟨hp_prime, hdvd, hN.2.ne'⟩)
    exact ⟨p, hp_prime, hk_le, hp_le, hndvd⟩
  refine ⟨hforall, ?_⟩
  obtain ⟨p, hp_prime, hp5, hp_le, hndvd⟩ := hforall 5 (by decide)
  have hcard : (5 : ℕ).primesBelow.card = 2 := by decide
  rw [hcard] at hp_le
  norm_num at hp_le
  have hp_ne62 : p ≠ 62 := by rintro rfl; exact absurd hp_prime (by decide)
  have hp_ne63 : p ≠ 63 := by rintro rfl; exact absurd hp_prime (by decide)
  have hp_ne64 : p ≠ 64 := by rintro rfl; exact absurd hp_prime (by decide)
  exact ⟨p, hp_prime, hp5, by omega, hndvd⟩

end OddPerfect
