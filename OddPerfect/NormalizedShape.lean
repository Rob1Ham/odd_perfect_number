module

public import OddPerfect.QuasiFactors
public import OddPerfect.NearPerfect
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

/-- Once the linear entries have been removed, even exponents contribute
a single square, including in lists with repeated or composite bases. -/
theorem square_after_linear_entries (X : List (ℕ × ℕ))
    (he : ∀ z ∈ X, z.2 = 1 ∨ Even z.2) :
    ∃ s : ℕ, listValue X = listValue (X.filter (fun z => z.2 == 1)) * s^2 := by
  induction X with
  | nil => exact ⟨1, rfl⟩
  | cons z zs ih =>
    obtain ⟨s, hs⟩ := ih (fun w hw => he w (.tail _ hw))
    by_cases h1 : z.2=1
    · refine ⟨s, ?_⟩
      rw [List.filter_cons_of_pos (p := fun z : ℕ × ℕ => z.2 == 1) (by simp [h1])]
      change z.1^z.2 * listValue zs = (z.1^z.2 * listValue _) * s^2
      rw [hs, mul_assoc]
    · obtain ⟨d, hd⟩ := (he z (.head _)).resolve_left h1
      refine ⟨z.1^d*s, ?_⟩
      rw [List.filter_cons_of_neg (p := fun z : ℕ × ℕ => z.2 == 1) (by simpa using h1)]
      change z.1^z.2 * listValue zs = listValue _ * (z.1^d*s)^2
      rw [hd, pow_add, hs]
      ring

/-- Every normalized candidate has squarefree part exactly its unique linear
prime q. The square tail may still contain q. -/
theorem normalized_spoof_squarefree_part {N : ℕ} (h : N ∈ normalizedSpoofCandidates) :
    ∃ q : ℕ, q.Prime ∧ q%4=1 ∧ ∃ s : ℕ, N=q*s^2 := by
  obtain ⟨_, X, hv, _, hparts, q, _, hq, h4, hlin⟩ := h
  obtain ⟨s,hs⟩ := square_after_linear_entries X (by
    intro z hz
    obtain ⟨_, _, _, _, _, hl⟩ := hparts z hz
    rcases hl.eq_two_or_odd with he | he
    · exact Or.inl (by omega)
    · exact Or.inr (Nat.even_iff.mpr (by omega)))
  rw [hv,hlin] at hs
  exact ⟨q,hq,h4,s,by simpa [listValue] using hs⟩

theorem normalized_spoof_not_square {N : ℕ} (h : N ∈ normalizedSpoofCandidates) :
    ¬IsSquare N := by
  obtain ⟨q,hq,_,s,hs⟩ := normalized_spoof_squarefree_part h
  have ho : Odd N := h.1
  have hsn : s ≠ 0 := by rintro rfl; simp at hs; exact ho.pos.ne' hs
  intro hsq
  have hev := (Nat.isSquare_iff_even_factorization.mp hsq) q hq
  rw [hs, Nat.factorization_mul hq.ne_zero (pow_ne_zero _ hsn), Finsupp.add_apply,
    hq.factorization_self, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hev
  obtain ⟨k,hk⟩ := hev
  omega

/-- Every odd near-perfect example with one redundant proper divisor fails
Dittmer's normalized spoof predicate, regardless of the choice of entries. -/
theorem nearPerfect_not_normalized_spoof {N d : ℕ} (h : NearPerfectWith N d) :
    N ∉ normalizedSpoofCandidates := by
  intro hc
  exact normalized_spoof_not_square hc (h.isSquare_of_odd hc.1)

theorem johnson_not_normalized_spoof : 173369889 ∉ normalizedSpoofCandidates :=
  nearPerfect_not_normalized_spoof johnson_nearPerfect.2

end OddPerfect
