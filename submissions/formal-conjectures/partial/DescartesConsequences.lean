module

public import CubeFree
public import OddPerfect.TothTrillion

/-! # Necessary conditions for a second Descartes number -/

public section

namespace DescartesSubmission

open OddPerfect

/-- A second example has a large cofactor with at least five primes. In addition,
either some prime cube divides the number or the number has at least seven primes. -/
theorem second_descartes_restrictions {m w : ℕ} (h : SingleCompositeSpoof m w)
    (hne : m * w ≠ 198585576189) :
    10 ^ 12 < m ∧ 5 ≤ m.primeFactors.card ∧
      ((∃ p : ℕ, p.Prime ∧ p ^ 3 ∣ m * w) ∨ 7 ≤ (m * w).primeFactors.card) := by
  refine ⟨trillion_lt_spoof_cofactor h hne, ?_, ?_⟩
  · by_contra! hfew
    have hpair : TothPair m w := ⟨h.odd_left, h.odd_right.pos, h.balance⟩
    obtain ⟨hm, hw⟩ := (toth_odd_pair_four_iff (by omega) h.odd_right h.one_lt).mp hpair
    exact hne (by rw [hm, hw])
  · by_cases hc : 7 ≤ (m * w).primeFactors.card
    · exact Or.inr hc
    · apply Or.inl
      by_contra! hfree
      exact hne (cube_free_unique_of_spoof h hfree (by omega))

#print axioms second_descartes_restrictions

end DescartesSubmission
