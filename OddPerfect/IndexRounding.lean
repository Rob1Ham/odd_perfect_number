module

public import OddPerfect.IndexState
public import OddPerfect.PrimeBank

/-! The least multiplicities compatible with Euler's unique odd valuation. -/

public section

namespace OddPerfect.IndexComponent

open Finset

@[expose] def roundPrimes (pairs : List (ℕ × ℕ)) : Finset ℕ := (pairs.map Prod.fst).toFinset

/-- Exact odd valuations of a known divisor must rise by at least one,
except possibly at the Euler prime. The allowance bounds that one omission. -/
@[expose] def State.checkRound (s : State) (pool : PrimeBank) (X allowance : ℕ) (pairs : List (ℕ × ℕ)) : Bool :=
  let U := s.joined
  pairs.all (fun (p,e) => decide (pool.contains p = true ∧ p ≠ s.special ∧ Odd e ∧ p^e ∣ U ∧ ¬ p^(e+1) ∣ U ∧
    (s.special ≠ 0 ∨ p%4 ≠ 1 ∨ p ≤ allowance))) &&
  decide (0 < allowance ∧ X*allowance < U*(∏ p ∈ roundPrimes pairs, p))

theorem checkRound_false {N X allowance : ℕ} {s : State} (h : Valid s N) (ho : Odd N)
    (hN : N.Perfect) (hx : N ≤ X) (pool : PrimeBank) (hp : pool.Certified)
    (pairs : List (ℕ × ℕ)) (test : s.checkRound pool X allowance pairs = true) : False := by
  simp only [State.checkRound, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at test
  obtain ⟨hdata, hallow, hbig⟩ := test
  let U := s.joined
  let T := roundPrimes pairs
  obtain ⟨m, hm : N = U*m⟩ := joined_dvd h hN
  obtain ⟨hU0, hm0⟩ := mul_ne_zero_iff.mp (hm ▸ hN.2.ne')
  obtain ⟨q, _, hq4, _, hev⟩ := euler_exponents ho hN
  have data (p) (hpt : p ∈ T) : ∃ e, (p,e) ∈ pairs := by
    obtain ⟨⟨k,e⟩, hk, heq⟩ := List.mem_map.mp (List.mem_toFinset.mp hpt)
    exact ⟨e, heq ▸ hk⟩
  have hsub : T.erase q ⊆ m.primeFactors := by
    intro p hpt
    obtain ⟨hne,hpt⟩ := mem_erase.mp hpt
    obtain ⟨e, he⟩ := data p hpt
    obtain ⟨hp', _, heodd, hex, hnext, _⟩ := hdata (p,e) he
    have hprime : p.Prime := pool.prime_of_contains hp hp'
    change p^e ∣ U at hex
    change ¬ p^(e+1) ∣ U at hnext
    change Odd e at heodd
    have hlow : e ≤ U.factorization p := (hprime.pow_dvd_iff_le_factorization hU0).mp hex
    have hhigh : ¬ e+1 ≤ U.factorization p := mt (hprime.pow_dvd_iff_le_factorization hU0).mpr hnext
    obtain ⟨j,hj⟩ := hev p hne
    rw [hm, Nat.factorization_mul hU0 hm0, Finsupp.add_apply] at hj
    have hval : U.factorization p = e := by omega
    rw [hval] at hj
    have hpar := Nat.odd_iff.mp heodd
    have hpos : 1 ≤ m.factorization p := by omega
    exact Nat.mem_primeFactors.mpr ⟨hprime, (hprime.dvd_iff_one_le_factorization hm0).mpr hpos, hm0⟩
  have hprod : (∏ p ∈ T.erase q, p) ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0)
    ((prod_dvd_prod_of_subset _ _ id hsub).trans (Nat.prod_primeFactors_dvd m))
  have hrest : (∏ p ∈ T, p) ≤ m*allowance := by
    by_cases hqT : q ∈ T
    · obtain ⟨e, he⟩ := data q hqT
      obtain ⟨_, hdiff, _, _, _, hcase⟩ := hdata (q,e) he
      have hsq : s.special = 0 := by
        by_contra hn
        have heven := Nat.even_iff.mp (hev s.special hdiff.symm)
        have hodd := Nat.odd_iff.mp (h.special hn)
        omega
      have hql : q ≤ allowance := hcase.resolve_left (not_not_intro hsq) |>.resolve_left (not_not_intro hq4)
      rw [← mul_prod_erase T (fun p => p) hqT, Nat.mul_comm m]
      exact Nat.mul_le_mul hql hprod
    · rw [erase_eq_of_notMem hqT] at hprod
      exact hprod.trans (Nat.le_mul_of_pos_right m hallow)
  have bound := Nat.mul_le_mul_left U hrest
  rw [← Nat.mul_assoc, ← hm] at bound
  exact hbig.not_ge (bound.trans (Nat.mul_le_mul_right allowance hx))

end OddPerfect.IndexComponent
