module

public import OddPerfect.IndexCheckpoint

/-! Close a prime-index branch when its forced prime powers form an abundant divisor. -/

public section

namespace OddPerfect.IndexComponent
open ArithmeticFunction

@[expose] def State.powerForced (s : State) (u p e : ℕ) : Bool :=
  decide (p^e ∣ u ∨ (Even e ∧ p^(e-1) ∣ u ∧ p ≠ s.special ∧ (s.special ≠ 0 ∨ p%4 ≠ 1)))

private theorem powerForced_dvd {N p e : ℕ} {s : State} (h : Valid s N) (ho : Odd N)
    (hN : N.Perfect) (hp : p.Prime) (test : s.powerForced s.joined p e = true) : p^e ∣ N := by
  have hj := joined_dvd h hN
  rcases of_decide_eq_true test with hdiv | ⟨he, hlo, hdiff, hspecial⟩
  · exact hdiv.trans hj
  obtain ⟨q, _, hq4, _, hev⟩ := euler_exponents ho hN
  have hne : p ≠ q := by
    rintro rfl
    rcases hspecial with hsp | hmod
    · have hval := Nat.even_iff.mp (hev s.special hdiff.symm)
      have hodd := Nat.odd_iff.mp (h.special hsp)
      omega
    · exact hmod hq4
  have hlo' := (hp.pow_dvd_iff_le_factorization hN.2.ne').mp (hlo.trans hj)
  have hpar := Nat.even_iff.mp (hev p hne)
  have hepar := Nat.even_iff.mp he
  exact (hp.pow_dvd_iff_le_factorization hN.2.ne').mpr (by omega)

/-- Test each prime, its admissible exponent and its absence from the previous
partial product before multiplying its geometric sum into the numerator. -/
@[expose] def abundantTail (s : State) (pool : PrimeBank) (u : ℕ) : ℕ → ℕ → List (ℕ × ℕ) → Bool
  | d, a, [] => decide (2*d < a)
  | d, a, (p,e)::rest =>
    pool.contains p && decide (¬p ∣ d) && s.powerForced u p e &&
      abundantTail s pool u (d*p^e) (a*SupportSieve.geomValue p (e+1)) rest

theorem abundantTail_false {N d a : ℕ} {s : State} (h : Valid s N) (ho : Odd N) (hN : N.Perfect)
    (pool : PrimeBank) (hp : pool.Certified) (hd : d ∣ N) (ha : sigma 1 d = a) (ps : List (ℕ × ℕ))
    (test : abundantTail s pool s.joined d a ps = true) : False := by
  induction ps generalizing d a with
  | nil =>
    have hab := of_decide_eq_true test
    have hAb : d.Abundant := by
      rwa [Nat.abundant_iff_sum_divisors, ← sigma_one_apply, ha]
    exact (Nat.perfect_iff_not_abundant_and_not_deficient hN.2.ne).mp hN |>.1
      (hAb.of_dvd hd hN.2.ne')
  | cons x xs ih =>
    obtain ⟨p,e⟩ := x
    simp only [abundantTail, Bool.and_eq_true, decide_eq_true_eq] at test
    obtain ⟨⟨⟨hpin, hnew⟩, hforced⟩, hnext⟩ := test
    have hprime := pool.prime_of_contains hp hpin
    have hpow := powerForced_dvd h ho hN hprime hforced
    have hc := (hprime.coprime_iff_not_dvd.mpr hnew).symm.pow_right e
    have hg : SupportSieve.geomValue p (e+1) = sigma 1 (p^e) := by
      rw [sigma_one_apply_prime_pow hprime, SupportSieve.geomValue, ← geom_sum_mul_of_one_le hprime.one_le,
        Nat.mul_div_cancel _ (by have := hprime.one_lt; omega)]
    apply ih (hc.mul_dvd_of_dvd_of_dvd hd hpow) _ hnext
    rw [isMultiplicative_sigma.map_mul_of_coprime hc, ha, hg]

end OddPerfect.IndexComponent
