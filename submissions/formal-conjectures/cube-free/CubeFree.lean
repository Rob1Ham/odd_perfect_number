module

public import FactorChains
public import Structure
public import ThreeDivides
public import Valuations

/-! # Cube-free Descartes numbers with fewer than seven prime divisors

A proof of the Banks–Güloğlu–Nevans–Saidak uniqueness theorem, using the
classification of odd deficient-perfect cofactors with at most four primes.
-/

public section

namespace DescartesSubmission

open ArithmeticFunction OddPerfect

theorem cube_free_unique_of_spoof {m w : ℕ} (h : SingleCompositeSpoof m w)
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ m * w)
    (hc : (m * w).primeFactors.card < 7) : m * w = 198585576189 := by
  by_contra hne
  obtain ⟨r, hr, hw, he⟩ := support_shape h hfree hc hne
  have h3 : 3 ∈ (m * w).primeFactors := Nat.mem_primeFactors.mpr
    ⟨by decide, OddPerfect.Submissions.three_dvd_of_spoof_card_le_six h (by omega),
      Nat.mul_ne_zero h.odd_left.pos.ne' h.odd_right.pos.ne'⟩
  exact factor_chain_contradiction (S := fun p => p ∈ (m * w).primeFactors)
    (r := r) h3 (ordinary_edge h hw hr he) (exceptional_edge h hw)
    (capacity_of_exact h hw hr hfree he)

/-- The Google DeepMind declaration with its three catalog definitions unfolded. -/
theorem catalog_cubeFree_lt_seven_primeFactors_unique (n : ℕ)
    (hd : ∃ m w : ℕ, n = m * w ∧ ((1 < w ∧ ¬ w.Prime) ∧ Odd (m * w) ∧
      Nat.Coprime m w ∧ sigma 1 m * (w + 1) = 2 * m * w))
    (hcf : ∀ ⦃x : ℕ⦄, x ^ 3 ∣ n → IsUnit x)
    (hcard : n.primeFactors.card < 7) : n = 198585576189 := by
  obtain ⟨m, w, rfl, ⟨hw, hnp⟩, ho, hcop, hbal⟩ := hd
  obtain ⟨hm, hwo⟩ := Nat.odd_mul.mp ho
  have h : SingleCompositeSpoof m w :=
    ⟨hm, hwo, hw, hnp, hcop, by simpa only [Nat.mul_assoc] using hbal⟩
  apply cube_free_unique_of_spoof h _ hcard
  intro p hp hdvd
  exact hp.ne_one (Nat.isUnit_iff.mp (hcf hdvd))

#print axioms cube_free_unique_of_spoof
#print axioms catalog_cubeFree_lt_seven_primeFactors_unique

end DescartesSubmission
