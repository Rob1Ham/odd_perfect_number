module

-- Run in a checkout of google-deepmind/formal-conjectures.
public import FormalConjectures.Wikipedia.DescartesNumber

/-! # Inspect the upstream declarations and their proof dependencies -/

#print DescartesNumber.IsDescartesFactorization
#print Nat.Composite
#print DescartesNumber.descartes_non_example_factor_gt_ten_pow_twelve
#print axioms DescartesNumber.descartes_non_example_factor_gt_ten_pow_twelve
#print axioms DescartesNumber.descartes_cubeFree_lt_seven_primeFactors_unique
#print axioms DescartesNumber.descartes_number_unique

-- A change in the upstream definitions that breaks these comparisons should be
-- investigated before reusing either external proof reference.
example (m w : ℕ) : DescartesNumber.IsDescartesFactorization m w ↔
    (1 < w ∧ ¬ w.Prime) ∧ Odd (m * w) ∧ Nat.Coprime m w ∧
    ArithmeticFunction.sigma 1 m * (w + 1) = 2 * m * w := Iff.rfl

example (n : ℕ) : DescartesNumber.IsDescartesNumber n ↔
    ∃ m w : ℕ, n = m * w ∧ DescartesNumber.IsDescartesFactorization m w := Iff.rfl

example (n : ℕ) : Powerfree 3 n ↔ (∀ ⦃x : ℕ⦄, x ^ 3 ∣ n → IsUnit x) := Iff.rfl

example : DescartesNumber.descartesExample = 198585576189 := rfl
