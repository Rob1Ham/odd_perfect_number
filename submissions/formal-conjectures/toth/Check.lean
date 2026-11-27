module

public import OddPerfect.TothTrillion

/-! Comparison with the Tóth declaration in DeepMind's DescartesNumber.lean.
The external proposition below expands their composite and factorization predicates.
Only the project proof is imported, so the upstream placeholder cannot supply the result. -/

public section

namespace DescartesSubmission

open ArithmeticFunction

def CatalogFactorization (m w : ℕ) : Prop :=
  (1 < w ∧ ¬ w.Prime) ∧ Odd (m * w) ∧ Nat.Coprime m w ∧
    sigma 1 m * (w + 1) = 2 * m * w

theorem toSingleCompositeSpoof {m w : ℕ} (hf : CatalogFactorization m w) :
    OddPerfect.SingleCompositeSpoof m w := by
  obtain ⟨⟨hw, hnp⟩, ho, hcop, hbal⟩ := hf
  obtain ⟨hm, hwo⟩ := Nat.odd_mul.mp ho
  exact ⟨hm, hwo, hw, hnp, hcop, by simpa only [Nat.mul_assoc] using hbal⟩

theorem toth_cofactor_bound (m w : ℕ) (hf : CatalogFactorization m w)
    (hne : m * w ≠ 198585576189) : 10 ^ 12 < m :=
  OddPerfect.trillion_lt_spoof_cofactor (toSingleCompositeSpoof hf) hne

#print axioms OddPerfect.trillion_lt_spoof_cofactor
#print axioms toth_cofactor_bound

end DescartesSubmission
