module

public import OddPerfect.GlobalObstruction
public import OddPerfect.CyclotomicRootSlope
public import OddPerfect.QuadrupleRepunitObstruction
public import OddPerfect.ExceptionalBlockSquare
public import OddPerfect.CountBound
public import OddPerfect.CountBound37
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Global Abundancy & Component-Index Conservation Obstructions (`OddPerfect.GlobalAbundancyObstruction`)

Couples the cyclotomic root-slot slopes (`OddPerfect.CyclotomicRootSlope`:
`21 * ω(N) ≤ 8 * Ω(N) + 39` unconditionally and `8 * ω(N) ≤ 3 * Ω(N) + 7` for `¬ 3 ∣ N`)
with Global Component-Index Conservation (`OddPerfect.GlobalObstruction`) and the `37` prime-factor
multiplicity lower bound (`OddPerfect.CountBound37`) to prove:
1. `sum_component_factor_capture`: exact global component factor-capture conservation
   `∑ p ∈ N.primeFactors, (e_p + Ω(σ(p^{e_p}))) = 1 + 2 * Ω(N)`.
2. `exists_componentIndex_cardFactors_add_five_le_of_large_or_three_free`: sharpened component-index
   drop `∃ p ∈ N.primeFactors, Ω(i_p) + 5 ≤ Ω(N)` whenever `¬ 3 ∣ N` or `88 ≤ Ω(N)`.
3. `finite_of_all_componentIndex_near_full`: Dual Bridge `B3` finiteness theorem showing that
   `∀ p ∈ N.primeFactors, Ω(N) < Ω(i_p) + 5` forces `Ω(N) ≤ 87` and `ω(N) ≤ 35`, yielding explicit
   finiteness via Dickson's theorem.
4. `odd_perfect_wave3_master_profile`: Wave-3 master profile combining size, multiplicity,
   cyclotomic slope, factor-capture conservation, and sixth-power/support dichotomies.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private theorem cardFactors_finset_prod {s : Finset ℕ} (f : ℕ → ℕ) (h : ∀ p ∈ s, 0 < f p) :
    cardFactors (∏ p ∈ s, f p) = ∑ p ∈ s, cardFactors (f p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    have hpos : ∀ p ∈ s, 0 < f p := fun p hp => h p (Finset.mem_insert_of_mem hp)
    rw [Finset.prod_insert hx, Finset.sum_insert hx,
      cardFactors_mul (h x (Finset.mem_insert_self ..)).ne' (Finset.prod_pos hpos).ne', ih hpos]

/-- Exact global component factor-capture conservation law:
`∑ p ∈ N.primeFactors, (e_p + Ω(σ(p^{e_p}))) = 1 + 2 * Ω(N)`. -/
theorem sum_component_factor_capture {N : ℕ} (_ho : Odd N) (hN : N.Perfect) :
    (∑ p ∈ N.primeFactors, (N.factorization p + cardFactors (sigma 1 (ordProj[p] N)))) =
      1 + 2 * cardFactors N := by
  rw [Finset.sum_add_distrib]
  have hfst : (∑ p ∈ N.primeFactors, N.factorization p) = cardFactors N := by
    rw [cardFactors_eq_sum_factorization]
    rfl
  have hsig_prod : (∏ p ∈ N.primeFactors, sigma 1 (ordProj[p] N)) = sigma 1 N :=
    (isMultiplicative_sigma.multiplicative_factorization (sigma 1) hN.2.ne').symm
  have hsig : sigma 1 N = 2 * N :=
    (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN)
  have hpos : ∀ p ∈ N.primeFactors, 0 < sigma 1 (ordProj[p] N) := fun p hp =>
    sigma_pos 1 _ (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)
  have hcard := congrArg cardFactors (hsig_prod.trans hsig)
  rw [cardFactors_finset_prod (fun p => sigma 1 (ordProj[p] N)) hpos,
    cardFactors_mul (by decide : (2 : ℕ) ≠ 0) hN.2.ne',
    cardFactors_apply_prime Nat.prime_two] at hcard
  rw [hfst, hcard]
  omega

/-- Whenever `¬ 3 ∣ N` or `88 ≤ Ω(N)`, some prime component `p ∣ N` has
`Ω(i_p) + 5 ≤ Ω(N)` and captures at least `6` prime factors with multiplicity. -/
theorem exists_componentIndex_cardFactors_add_five_le_of_large_or_three_free
    {N : ℕ} (ho : Odd N) (hN : N.Perfect) (h : ¬ 3 ∣ N ∨ 88 ≤ cardFactors N) :
    ∃ p ∈ N.primeFactors,
      cardFactors (componentIndex N p) + 5 ≤ cardFactors N ∧
      6 ≤ N.factorization p + cardFactors (sigma 1 (ordProj[p] N)) := by
  by_contra! hnot
  have hle : ∀ p ∈ N.primeFactors,
      N.factorization p + cardFactors (sigma 1 (ordProj[p] N)) ≤ 5 := by
    intro p hp
    have hcons := cardFactors_componentIndex_add_eq hN hp
    by_contra! hgt
    have := hnot p hp (by omega)
    omega
  have hsum : 1 + 2 * cardFactors N ≤ 5 * N.primeFactors.card := by
    calc
      1 + 2 * cardFactors N
          = ∑ p ∈ N.primeFactors, (N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) :=
            (sum_component_factor_capture ho hN).symm
      _ ≤ ∑ _p ∈ N.primeFactors, 5 := Finset.sum_le_sum hle
      _ = 5 * N.primeFactors.card := by simp [Nat.mul_comm]
  have hlen : cardFactors N = N.primeFactorsList.length := cardFactors_apply
  rcases h with h3 | h88
  · have hslope := cyclotomic_slope_three_free ho hN h3
    have h37 := thirty_seven_le_total_prime_factor_count ho hN
    omega
  · have hslope := cyclotomic_prime_factor_count ho hN
    omega

/-- Dual Bridge `B3` finiteness: bounding all component indices near `Ω(N)` (`Ω(N) < Ω(i_p) + 5`)
forces `Ω(N) ≤ 87` and `ω(N) ≤ 35`, making the candidate set finite by Dickson's theorem. -/
theorem finite_of_all_componentIndex_near_full :
    Set.Finite {N : ℕ | Odd N ∧ N.Perfect ∧
      ∀ p ∈ N.primeFactors, cardFactors N < cardFactors (componentIndex N p) + 5} := by
  apply (dickson_finite 35).subset
  rintro N ⟨ho, hN, hnear⟩
  refine ⟨ho, hN, ?_⟩
  have hlt88 : cardFactors N < 88 := by
    by_contra! h88
    obtain ⟨p, hp, h5, _⟩ :=
      exists_componentIndex_cardFactors_add_five_le_of_large_or_three_free ho hN (Or.inr h88)
    exact (hnear p hp).not_ge h5
  have hlen : cardFactors N = N.primeFactorsList.length := cardFactors_apply
  have hslope := cyclotomic_prime_factor_count ho hN
  omega

/-- Wave-3 master structural obstruction profile for odd perfect numbers. -/
theorem odd_perfect_wave3_master_profile {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    10 ^ 300 < N ∧
    37 ≤ cardFactors N ∧
    21 * N.primeFactors.card ≤ 8 * cardFactors N + 39 ∧
    (¬ 3 ∣ N → 8 * N.primeFactors.card ≤ 3 * cardFactors N + 7 ∧
      ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 5 ≤ cardFactors N) ∧
    (∑ p ∈ N.primeFactors, (N.factorization p + cardFactors (sigma 1 (ordProj[p] N)))) =
      1 + 2 * cardFactors N ∧
    ((∃ p, p.Prime ∧ p ^ 6 ∣ N) ∨
      (443 ≤ N.primeFactors.card ∧
        ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 5 ≤ cardFactors N)) := by
  refine ⟨ten_pow_three_hundred_lt_of_odd_perfect ho hN,
    by simpa [cardFactors_apply] using thirty_seven_le_total_prime_factor_count ho hN,
    by simpa [cardFactors_apply] using cyclotomic_prime_factor_count ho hN,
    ?_,
    sum_component_factor_capture ho hN,
    ?_⟩
  · intro h3
    refine ⟨by simpa [cardFactors_apply] using cyclotomic_slope_three_free ho hN h3, ?_⟩
    obtain ⟨p, hp, h5, _⟩ :=
      exists_componentIndex_cardFactors_add_five_le_of_large_or_three_free ho hN (Or.inl h3)
    exact ⟨p, hp, h5⟩
  · rcases sixth_power_or_large_support ho hN with h6 | ⟨h443, h1137, _⟩
    · exact Or.inl h6
    · refine Or.inr ⟨h443, ?_⟩
      have h88 : 88 ≤ cardFactors N := by
        rw [cardFactors_apply]
        omega
      obtain ⟨p, hp, h5, _⟩ :=
        exists_componentIndex_cardFactors_add_five_le_of_large_or_three_free ho hN (Or.inr h88)
      exact ⟨p, hp, h5⟩

end OddPerfect
