module

public import OddPerfect.CountClasses
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Normalized square-component sums and Lemma 3 of Ochem and Rao (2014). -/

public section

namespace OddPerfect

open ArithmeticFunction

/-- The quadratic divisor sum with its factor of three removed when present. -/
@[expose] def normalizedSquareSum (u : ℕ) : ℕ :=
  if u % 3 = 1 then (u ^ 2 + u + 1) / 3 else u ^ 2 + u + 1

private theorem normalized_at_one (k : ℕ) :
    normalizedSquareSum (3 * k + 1) = 3 * k ^ 2 + 3 * k + 1 := by
  rw [normalizedSquareSum, ite_eq_left (show (3 * k + 1) % 3 = 1 by omega)]
  rw [show (3 * k + 1) ^ 2 + (3 * k + 1) + 1 = 3 * (3 * k ^ 2 + 3 * k + 1) by ring]
  simp

private theorem triple_normalized {u : ℕ} (h : u % 3 = 1) :
    3 * normalizedSquareSum u = u ^ 2 + u + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, u = 3 * k + 1 := ⟨u / 3, by omega⟩
  rw [normalized_at_one]
  ring

theorem normalizedSquareSum_one_lt {u : ℕ} (_hu : u.Prime) (h3 : 3 < u) :
    1 < normalizedSquareSum u := by
  by_cases hu1 : u % 3 = 1
  · have := triple_normalized hu1
    nlinarith
  · simp only [normalizedSquareSum, ite_eq_right hu1]
    omega

theorem normalizedSquareSum_dvd_sigma {u : ℕ} (hu : u.Prime) (_h3 : 3 < u) :
    normalizedSquareSum u ∣ sigma 1 (u ^ 2) := by
  rw [sigma_one_apply_prime_pow hu]
  have hv : (∑ i ∈ Finset.range (2 + 1), u ^ i) = u ^ 2 + u + 1 := by
    simp [Finset.sum_range_succ, add_comm, add_assoc, add_left_comm]
  rw [hv]
  by_cases h : u % 3 = 1
  · rw [← triple_normalized h]
    exact dvd_mul_left _ _
  · simp [normalizedSquareSum, h]

theorem three_not_dvd_normalizedSquareSum {u : ℕ} (_hu : u.Prime) (_h3 : 3 < u) :
    ¬ 3 ∣ normalizedSquareSum u := by
  rcases (show u % 3 = 0 ∨ u % 3 = 1 ∨ u % 3 = 2 by omega) with h | h | h
  · have hc : u ≡ 0 [MOD 3] := h
    have hmod := ((hc.pow 2).add hc).add (Nat.ModEq.refl 1)
    change (u ^ 2 + u + 1) % 3 = 1 at hmod
    simp only [normalizedSquareSum, ite_eq_right (show u % 3 ≠ 1 by omega)]
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, u = 3 * k + 1 := ⟨u / 3, by omega⟩
    rw [normalized_at_one]
    omega
  · have hc : u ≡ 2 [MOD 3] := h
    have hmod := ((hc.pow 2).add hc).add (Nat.ModEq.refl 1)
    change (u ^ 2 + u + 1) % 3 = 1 at hmod
    simp only [normalizedSquareSum, ite_eq_right (show u % 3 ≠ 1 by omega)]
    omega

/-- A crossing between the two normalization cases would solve the equation
in Lemma 3 with a prime greater than three. -/
private theorem no_triple_collision {u v : ℕ} (hu : u.Prime) (hu3 : 3 < u)
    (hv3 : 3 < v) (hv1 : v % 3 = 1) : v ^ 2 + v + 1 ≠ 3 * (u ^ 2 + u + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, v = 3 * k + 1 := ⟨v / 3, by omega⟩
  intro heq
  have hprod : u * (u + 1) = 3 * (k * (k + 1)) := by nlinarith
  have hdiv : u ∣ 3 * (k * (k + 1)) := hprod ▸ dvd_mul_right _ _
  have hnot : ¬ u ∣ 3 := fun hd => (Nat.not_lt_of_ge (Nat.le_of_dvd (by decide) hd)) hu3
  have hsmall : u ≤ k + 1 := by
    rcases hu.dvd_mul.mp ((hu.dvd_mul.mp hdiv).resolve_left hnot) with hk | hk
    · have := Nat.le_of_dvd (show 0 < k by omega) hk
      omega
    · exact Nat.le_of_dvd (Nat.zero_lt_succ _) hk
  have hprod_le := Nat.mul_le_mul hsmall (Nat.succ_le_succ hsmall)
  have hsq := Nat.mul_self_le_mul_self (show 2 ≤ k by omega)
  nlinarith

theorem normalizedSquareSum_injective {u v : ℕ} (hu : u.Prime) (hu3 : 3 < u)
    (hv : v.Prime) (hv3 : 3 < v) (heq : normalizedSquareSum u = normalizedSquareSum v) :
    u = v := by
  have mono : StrictMono (fun x : ℕ => x ^ 2 + x + 1) := by
    intro a b hab
    have hsq := Nat.mul_self_le_mul_self hab.le
    dsimp
    nlinarith
  by_cases hu1 : u % 3 = 1 <;> by_cases hv1 : v % 3 = 1
  · apply mono.injective
    exact (triple_normalized hu1).symm.trans ((congrArg (3 * ·) heq).trans (triple_normalized hv1))
  · have hval : normalizedSquareSum v = v ^ 2 + v + 1 := ite_eq_right hv1
    exact (no_triple_collision hv hv3 hu3 hu1
      ((triple_normalized hu1).symm.trans (congrArg (3 * ·) (heq.trans hval)))).elim
  · have hval : normalizedSquareSum u = u ^ 2 + u + 1 := ite_eq_right hu1
    exact (no_triple_collision hu hu3 hv3 hv1
      ((triple_normalized hv1).symm.trans (congrArg (3 * ·) (heq.symm.trans hval)))).elim
  · apply mono.injective
    simpa [normalizedSquareSum, hu1, hv1] using heq

/-- Every normalized square component supplies at least two prime factors with
multiplicity, unless it is prime and supplies exactly one. -/
theorem squareSources_count_le_normalized_count {N : ℕ} (ho : Odd N) :
    2 * (squareSources N).card ≤
      (∑ u ∈ squareSources N, cardFactors (normalizedSquareSum u)) +
        ((squareSources N).filter fun u => (normalizedSquareSum u).Prime).card := by
  calc
    _ = ∑ _u ∈ squareSources N, (2 : ℕ) := by simp [Nat.mul_comm]
    _ ≤ ∑ u ∈ squareSources N, (cardFactors (normalizedSquareSum u) +
        if (normalizedSquareSum u).Prime then 1 else 0) := by
      apply Finset.sum_le_sum
      intro u hmem
      obtain ⟨hu, hu3, _⟩ := Finset.mem_filter.mp hmem
      have hup := Nat.prime_of_mem_primeFactors hu
      have huo := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hu)
      have hmin := hup.two_le
      have hne := huo.not_two_dvd_nat
      have hgt : 3 < u := by omega
      have hcount := cardFactors_pos_iff_one_lt.mpr (normalizedSquareSum_one_lt hup hgt)
      by_cases h : (normalizedSquareSum u).Prime
      · simp [h]
      · have hne1 : cardFactors (normalizedSquareSum u) ≠ 1 := mt cardFactors_eq_one_iff_prime.mp h
        simp [h]
        omega
    _ = _ := by simp [Finset.sum_add_distrib]

end OddPerfect
