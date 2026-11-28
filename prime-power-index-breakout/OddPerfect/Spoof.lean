module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.FactorisationProperties

public section

namespace OddPerfect

open ArithmeticFunction

/-- A positive odd spoof with one coprime composite base `w` of exponent one.
The contribution of the other factor `m` is its genuine divisor sum. -/
structure SingleCompositeSpoof (m w : ℕ) : Prop where
  odd_left : Odd m
  odd_right : Odd w
  one_lt : 1 < w
  not_prime : ¬ Nat.Prime w
  coprime : m.Coprime w
  balance : sigma 1 m * (w + 1) = 2 * (m * w)

/-- A composite base contributes more than the sum of its two endpoint divisors. -/
theorem add_one_lt_sigma_of_composite {w : ℕ} (hw : 1 < w) (hc : ¬ Nat.Prime w) :
    w + 1 < sigma 1 w := by
  have hle : 1 ≤ ∑ d ∈ w.properDivisors, d :=
    Finset.single_le_sum (f := fun d : ℕ => d) (fun d _ => Nat.zero_le d)
      (Nat.one_mem_properDivisors_iff_one_lt.mpr hw)
  have hne := mt Nat.sum_properDivisors_eq_one_iff_prime.mp hc
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  omega

/-- In the relaxed coprime equation, the product is perfect precisely for a genuine prime base. -/
theorem perfect_iff_prime_of_spoof_balance {m w : ℕ} (hm : 0 < m) (hw : 1 < w)
    (hcop : m.Coprime w) (hbal : sigma 1 m * (w + 1) = 2 * (m * w)) :
    Nat.Perfect (m * w) ↔ Nat.Prime w := by
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul (Nat.mul_pos hm (by omega)), ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime hcop, ← hbal,
    Nat.mul_left_cancel_iff (sigma_pos_iff.mpr hm)]
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  exact ⟨fun h => Nat.sum_properDivisors_eq_one_iff_prime.mp (by omega),
    fun h => by rw [Nat.sum_properDivisors_eq_one_iff_prime.mpr h, Nat.add_comm]⟩

theorem SingleCompositeSpoof.true_sigma_gt {m w : ℕ} (h : SingleCompositeSpoof m w) :
    2 * (m * w) < sigma 1 (m * w) := by
  rw [← h.balance, isMultiplicative_sigma.map_mul_of_coprime h.coprime]
  exact Nat.mul_lt_mul_of_pos_left (add_one_lt_sigma_of_composite h.one_lt h.not_prime)
    (sigma_pos_iff.mpr h.odd_left.pos)

theorem SingleCompositeSpoof.abundant {m w : ℕ} (h : SingleCompositeSpoof m w) :
    Nat.Abundant (m * w) :=
  Nat.abundant_iff_sum_divisors.mpr (by simpa only [sigma_one_apply] using h.true_sigma_gt)

theorem SingleCompositeSpoof.not_perfect {m w : ℕ} (h : SingleCompositeSpoof m w) :
    ¬ Nat.Perfect (m * w) :=
  mt (perfect_iff_prime_of_spoof_balance h.odd_left.pos h.one_lt h.coprime h.balance).mp h.not_prime

private theorem descartes_left_sigma : sigma 1 9018009 = 18035199 := by
  change sigma 1 (9 * 49 * 121 * 169) = _
  rw [isMultiplicative_sigma.map_mul_of_coprime (by decide : Nat.Coprime (9 * 49 * 121) 169),
    isMultiplicative_sigma.map_mul_of_coprime (by decide : Nat.Coprime (9 * 49) 121),
    isMultiplicative_sigma.map_mul_of_coprime (by decide : Nat.Coprime 9 49)]
  decide +kernel

/-- Descartes's example, with `m = (3 * 7 * 11 * 13)^2` and `w = 19^2 * 61`. -/
theorem descartes_singleCompositeSpoof : SingleCompositeSpoof 9018009 22021 := by
  have hc : ¬ Nat.Prime 22021 :=
    Nat.not_prime_of_mul_eq (a := 19 ^ 2) (b := 61) (by decide) (by decide) (by decide)
  refine ⟨by decide, by decide, by decide, hc, by decide, ?_⟩
  calc
    sigma 1 9018009 * (22021 + 1) = 18035199 * (22021 + 1) :=
      congrArg (· * (22021 + 1)) descartes_left_sigma
    _ = 2 * (9018009 * 22021) := by decide

private theorem sigma_one_mul (m w : ℕ) (h : m.Coprime w) :
    sigma 1 (m * w) = sigma 1 m * sigma 1 w :=
  isMultiplicative_sigma.map_mul_of_coprime h

/-- The actual divisor sum after restoring the factors of 22021. -/
theorem descartes_true_sigma : sigma 1 198585576189 = 426027470778 := by
  calc
    sigma 1 198585576189 = sigma 1 (9018009 * 22021) :=
      congrArg (sigma 1) (by decide : 198585576189 = 9018009 * 22021)
    _ = sigma 1 9018009 * sigma 1 22021 :=
      sigma_one_mul 9018009 22021 descartes_singleCompositeSpoof.coprime
    _ = 18035199 * (sigma 1 361 * sigma 1 61) := congrArg₂ (· * ·) descartes_left_sigma
      ((congrArg (sigma 1) (by decide : 22021 = 361 * 61)).trans
        (sigma_one_mul 361 61 (by decide)))
    _ = 426027470778 := by decide +kernel

end OddPerfect
