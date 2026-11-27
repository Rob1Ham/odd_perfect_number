module

public import OddPerfect.PrimeNarrowing

public section

namespace OddPerfect.SpoofBox

theorem primeCovered_reject {k : ℕ} (rows : Vector Slot k)
    (h : acceptedLeaf (fun i : Fin k => rows[i]) []) : PrimeCovered rows := by
  intro x hm hx hf _
  exact List.not_mem_nil (covered_standard rows [] h x hm hx hf)

/-- Keep the primality witness outside the boolean interval tests so a
large forced prime can use an independently proved primality certificate. -/
theorem primeCovered_missing {k : ℕ} (rows : Vector Slot k) (source : Fin k) (r : ℕ)
    (hr : r.Prime) (ho : r%2=1) (hd : delivers rows[source] r)
    (hmiss : ∀ j : Fin k, admitsBase rows[j] r = false) : PrimeCovered rows := by
  intro x _ hx hb hg
  obtain ⟨j,hj⟩ := prime_slot_forcing hr (Nat.odd_iff.mpr ho) hg.prime source
    (delivers_sound (hx source) hd) hb
  have h := admitsBase_of_fits (hx j)
  rw [hj,hmiss j] at h
  contradiction

theorem primeCovered_last {k : ℕ} (rows : Vector Slot k) (i : Fin k)
    (h : lastLeaf (fun j : Fin k => rows[j]) i [] = true ∨
      (fixedApart (fun j : Fin k => rows[j]) i = true ∧
      ¬((completeBox (fun j : Fin k => rows[j]) i i).1).Prime)) : PrimeCovered rows := by
  intro x hm hx hf hg
  rcases h with h|⟨ha,hp⟩
  · exact List.not_mem_nil (covered_last rows i [] h x hm hx hf)
  · rw [← eq_completeBox _ i x hx hf ha] at hp
    exact hp (hg.prime i)

/-- Explicit cuts allow the search to isolate the smallest remaining
prime at any chosen point. Both branches remain independently mandatory. -/
@[expose] def childAt {k : ℕ} (left : Bool) (rows : Vector Slot k) (i : Fin k) (a : Axis) (cut : ℕ) :
    Vector Slot k :=
  let s := fun j : Fin k => rows[j]
  if left then Vector.ofFn (leftChild s i a cut) else Vector.ofFn (rightChild s i a cut)

theorem primeCovered_split {k : ℕ} (rows : Vector Slot k) (i : Fin k) (a : Axis) (cut : ℕ)
    (hl : PrimeCovered (childAt true rows i a cut)) (hr : PrimeCovered (childAt false rows i a cut)) :
    PrimeCovered rows := by
  intro x hm hx hf
  rcases split_covers (fun j : Fin k => rows[j]) i a cut x hm hx with h|h
  · exact hl x hm (by simpa [childAt] using h) hf
  · exact hr x hm (by simpa [childAt] using h) hf

/-- The sieve excludes a genuine support size once its k choices for the
location of the Euler component all close. -/
theorem exclude_prime_count_of_covers {k : ℕ} (hk : k < 8)
    (covers : ∀ j : Fin k, PrimeCovered (primeInitial j)) {N : ℕ} (hN : N.Perfect) (ho : Odd N) :
    N.primeFactors.card ≠ k := by
  intro he
  let x := primeSlots N he
  obtain ⟨hg,hx,_,hb⟩ := primeSlots_of_odd_perfect ho hN he
  obtain ⟨i,hi⟩ := realizing_initial x hx hb
  exact covers i x hg.strict.monotone (realizing_prime_initial hg hk i hi) hb hg

end OddPerfect.SpoofBox
