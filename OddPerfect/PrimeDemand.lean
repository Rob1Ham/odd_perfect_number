module

public import OddPerfect.PrimeCover

public section

namespace OddPerfect.SpoofBox

open Finset

/-- Each required value is already fixed, or an odd prime delivered by
a local geometric sum. In either case the value must occur as a true base. -/
@[expose] def requiredPrime {k : ℕ} (rows : Vector Slot k) (r : ℕ) : Bool :=
  decide (HasFixed rows r ∨ (r.Prime ∧ Odd r ∧ ∃ i : Fin k, delivers rows[i] r = true))

theorem requiredPrime_sound {k r : ℕ} {rows : Vector Slot k} {x : Fin k → ℕ × ℕ}
    (hg : GenuineSlots x) (hx : ∀ i : Fin k, rows[i].Fits (x i))
    (hb : formalSigma univ (fun i => (x i).1) (fun i => (x i).2) = 2*∏ i, (x i).1^(x i).2)
    (h : requiredPrime rows r) : ∃ i, (x i).1=r := by
  rcases of_decide_eq_true h with hf|⟨hp,ho,i,hi⟩
  · exact occurs_of_fixed hx hf
  · exact prime_slot_forcing hp ho hg.prime i (delivers_sound (hx i) hi) hb

/-- A finite set of forced primes cannot fit into fewer admissible slots.
The search may propose any subset of obligations and any receiving set. -/
theorem primeCovered_overfull {k : ℕ} (rows : Vector Slot k) (required : Finset ℕ) (slots : Finset (Fin k))
    (forced : ∀ r ∈ required, requiredPrime rows r = true)
    (admissible : ∀ r ∈ required, ∀ j : Fin k, admitsBase rows[j] r = true → j∈slots)
    (excess : slots.card < required.card) : PrimeCovered rows := by
  intro x _ hx hb hg
  have hs : required ⊆ slots.image (fun j => (x j).1) := by
    intro r hr
    obtain ⟨j,hj⟩ := requiredPrime_sound hg hx hb (forced r hr)
    have fits := admitsBase_of_fits (hx j)
    rw [hj] at fits
    exact mem_image.mpr ⟨j,admissible r hr j fits,hj⟩
  exact excess.not_ge ((card_le_card hs).trans card_image_le)

end OddPerfect.SpoofBox
