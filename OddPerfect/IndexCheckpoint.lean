module

public import OddPerfect.IndexReplay

/-! Join independently checked prime-index subtrees at a single index split. -/

public section

namespace OddPerfect.IndexComponent

@[expose] def State.same (s t : State) : Bool :=
  decide (s.component = t.component ∧ s.divisorSum = t.divisorSum ∧ s.special = t.special)

private theorem eq_of_same {s t : State} (h : s.same t = true) : s=t := by
  cases s
  cases t
  simp [State.same] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

/-- Recompute the next component for every admissible prime length. Each
child must either close arithmetically or match one of the separately verified states. -/
@[expose] def checkChildren (pool : PrimeBank) (seed avoid X : ℕ) (s : State)
    (p : ℕ) (states : List State) : Bool :=
  (pool.contains p && decide (¬ p ∣ s.component ∧ (p ∣ s.joined ∨ p = seed))) &&
    (List.range (Nat.log p (X/s.component))).all fun i =>
      let e := i+1
      let child := s.extend p e
      if (e+1).Prime ∧ (e = 1 ∨ p^(2*e) < X) then
        child.automatic avoid X || states.any child.same
      else true

/-- Any postulated prime divisor outside the selected component admits a
compatible prime length within both numeric cutoffs. -/
theorem exists_index_child {N X p : ℕ} (ho : Odd N) (hN : N.Perfect) (hx : N ≤ X)
    {s : State} (h : Valid s N) (hprime : p.Prime) (hnew : ¬p ∣ s.component) (hd : p ∣ N) :
    ∃ e, 0 < e ∧ e ≤ Nat.log p (X/s.component) ∧
      ((e+1).Prime ∧ (e = 1 ∨ p^(2*e) < X)) ∧ Valid (s.extend p e) N := by
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
  exact ⟨e, he, hmax, hc, hn⟩

theorem checkChildren_correct {N seed avoid X p : ℕ} (ho : Odd N) (hN : N.Perfect) (hseed : seed ∣ N)
    (hav : avoid.Coprime N) (hx : N ≤ X) (pool : PrimeBank) (hp : pool.Certified)
    {s : State} (h : Valid s N) (states : List State) (prior : ∀ t ∈ states, Valid t N → False)
    (test : checkChildren pool seed avoid X s p states = true) : False := by
  simp only [checkChildren, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at test
  obtain ⟨⟨hpin, hnew, hwhere⟩, test⟩ := test
  have hprime := pool.prime_of_contains hp hpin
  have hd : p ∣ N := hwhere.elim (fun hdiv => hdiv.trans (joined_dvd h hN)) (fun he => he ▸ hseed)
  obtain ⟨e, he, hmax, hc, hn⟩ := exists_index_child ho hN hx h hprime hnew hd
  have hnext := test (e-1) (by omega)
  rw [Nat.sub_add_cancel he, ite_eq_left hc] at hnext
  rcases Bool.or_eq_true_iff.mp hnext with hauto | hshared
  · exact automatic_false hn ho hN hav hx hauto
  · obtain ⟨t, ht, hsame⟩ := List.any_eq_true.mp hshared
    exact prior t ht (eq_of_same hsame ▸ hn)

end OddPerfect.IndexComponent
