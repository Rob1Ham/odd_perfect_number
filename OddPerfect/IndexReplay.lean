module

public import OddPerfect.IndexRounding

/-! Exhaustive prime-index branching under an absolute size limit. -/

public section

namespace OddPerfect.IndexComponent

/-- Missing exponents have to pass the directly checked arithmetic tests. -/
inductive ProofTree where
  | automatic
  | round (allowance : ℕ) (factors : List (ℕ × ℕ))
  | split (p : ℕ) (cases : List (ℕ × ProofTree))

@[expose] def replay (pool : PrimeBank) (seed avoid X : ℕ) : ℕ → State → ProofTree → Bool
  | 0, _, _ => false
  | fuel+1, s, t =>
    if s.automatic avoid X then true else
    match t with
    | .automatic => false
    | .round a ps => s.checkRound pool X a ps
    | .split p cs =>
      if pool.contains p = true ∧ ¬ p ∣ s.component ∧ (p ∣ s.joined ∨ p = seed) then
        (List.range (Nat.log p (X/s.component))).all fun i =>
          let e := i+1
          if (e+1).Prime ∧ (e = 1 ∨ p^(2*e) < X) then
            replay pool seed avoid X fuel (s.extend p e) ((cs.lookup e).getD .automatic)
          else true
      else false

theorem replay_correct {N seed avoid X : ℕ} (ho : Odd N) (hN : N.Perfect) (hseed : seed ∣ N)
    (hav : avoid.Coprime N) (hx : N ≤ X) (pool : PrimeBank) (hp : pool.Certified)
    (fuel : ℕ) {s : State} (h : Valid s N) (t : ProofTree) (test : replay pool seed avoid X fuel s t = true) : False := by
  induction fuel generalizing s t with
  | zero => simp [replay] at test
  | succ fuel ih =>
    by_cases ha : s.automatic avoid X = true
    · exact automatic_false h ho hN hav hx ha
    cases t with
    | automatic => simp [replay, ha] at test
    | round a ps => exact checkRound_false h ho hN hx pool hp ps (by simpa [replay, ha] using test)
    | split p cs =>
      by_cases hg : pool.contains p = true ∧ ¬ p ∣ s.component ∧ (p ∣ s.joined ∨ p = seed)
      · simp only [replay, ha, Bool.false_eq_true, ↓reduceIte] at test
        rw [ite_eq_left hg] at test
        simp only [List.all_eq_true, List.mem_range] at test
        obtain ⟨hpin, hnew, hwhere⟩ := hg
        have hprime := pool.prime_of_contains hp hpin
        have hd : p ∣ N := hwhere.elim (fun hdiv => hdiv.trans (joined_dvd h hN)) (fun he => he ▸ hseed)
        let v := N.factorization p
        have hvpos : 0 < v := (hprime.dvd_iff_one_le_factorization hN.2.ne').mp hd
        obtain ⟨l, hl, hdlen⟩ := Nat.exists_prime_and_dvd (by omega : v+1 ≠ 1)
        let e := l-1
        have hlen : e+1 = l := Nat.sub_add_cancel hl.one_le
        have he : 0 < e := by have := hl.one_lt; dsimp [e]; omega
        have hidx : e+1 ∣ v+1 := hlen ▸ hdlen
        have hn := extend_valid h hN.2.ne' hprime hnew hidx
        have hD : 0 < s.component := Nat.pos_of_ne_zero (fun he => hN.2.ne' (zero_dvd_iff.mp (he ▸ h.divides)))
        have hmax : e ≤ Nat.log p (X/s.component) := by
          apply Nat.le_log_of_pow_le hprime.one_lt
          apply (Nat.le_div_iff_mul_le hD).2
          have hs : s.component*p^e ≤ X := (Nat.le_of_dvd hN.2 hn.divides).trans hx
          simpa [Nat.mul_comm] using hs
        have hc : (e+1).Prime ∧ (e = 1 ∨ p^(2*e) < X) := by
          refine ⟨hlen ▸ hl, ?_⟩
          rcases hl.eq_two_or_odd with htwo | hodd
          · left; omega
          · right
            have hpar : Even e := by rw [Nat.even_iff]; omega
            exact (even_component_sq_lt ho hN hprime hd he hpar hidx).trans_le hx
        have hnext := test (e-1) (by omega)
        rw [Nat.sub_add_cancel he, ite_eq_left hc] at hnext
        exact ih hn _ hnext
      · simp [replay, ha, hg] at test

end OddPerfect.IndexComponent
