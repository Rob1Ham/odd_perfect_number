module

public import OddPerfect.IndexAbundant

public section

namespace OddPerfect.IndexComponent

/-- Trees with both multiplicity-rounding and partial-abundancy terminal cases. -/
inductive AbundanceTree where
  | automatic
  | round (allowance : ℕ) (factors : List (ℕ × ℕ))
  | abundant (factors : List (ℕ × ℕ))
  | split (p : ℕ) (cases : List (ℕ × AbundanceTree))

@[expose] def replayAbundance (pool : PrimeBank) (seed avoid X : ℕ) : ℕ → State → AbundanceTree → Bool
  | 0, _, _ => false
  | fuel+1, s, t =>
    if s.automatic avoid X then true else
    match t with
    | .automatic => false
    | .round a ps => s.checkRound pool X a ps
    | .abundant ps => abundantTail s pool s.joined 1 1 ps
    | .split p cs =>
      if pool.contains p = true ∧ ¬ p ∣ s.component ∧ (p ∣ s.joined ∨ p = seed) then
        (List.range (Nat.log p (X/s.component))).all fun i =>
          let e := i+1
          if (e+1).Prime ∧ (e = 1 ∨ p^(2*e) < X) then
            replayAbundance pool seed avoid X fuel (s.extend p e) ((cs.lookup e).getD .automatic)
          else true
      else false

theorem replayAbundance_correct {N seed avoid X : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : seed ∣ N)
    (hav : avoid.Coprime N) (hx : N ≤ X) (pool : PrimeBank) (hp : pool.Certified)
    (fuel : ℕ) {s : State} (h : Valid s N) (t : AbundanceTree)
    (test : replayAbundance pool seed avoid X fuel s t = true) : False := by
  induction fuel generalizing s t with
  | zero => simp [replayAbundance] at test
  | succ fuel ih =>
    by_cases ha : s.automatic avoid X = true
    · exact automatic_false h ho hN hav hx ha
    cases t with
    | automatic => simp [replayAbundance, ha] at test
    | round a ps => exact checkRound_false h ho hN hx pool hp ps (by simpa [replayAbundance, ha] using test)
    | abundant ps =>
      exact abundantTail_false (a := 1) h ho hN pool hp (one_dvd _) (by simp) ps (by simpa [replayAbundance, ha] using test)
    | split p cs =>
      by_cases hg : pool.contains p = true ∧ ¬ p ∣ s.component ∧ (p ∣ s.joined ∨ p = seed)
      · simp only [replayAbundance, ha, Bool.false_eq_true, ↓reduceIte, ite_eq_left hg,
          List.all_eq_true, List.mem_range] at test
        obtain ⟨hpin, hnew, hwhere⟩ := hg
        have hd : p ∣ N := hwhere.elim (fun hdiv => hdiv.trans (joined_dvd h hN)) (fun he => he ▸ hs)
        obtain ⟨e, he, hmax, hc, hn⟩ := exists_index_child ho hN hx h (pool.prime_of_contains hp hpin) hnew hd
        have hnext := test (e-1) (by omega)
        rw [Nat.sub_add_cancel he, ite_eq_left hc] at hnext
        exact ih hn _ hnext
      · simp [replayAbundance, ha, hg] at test

end OddPerfect.IndexComponent
