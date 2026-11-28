module

public import OddPerfect.Euler
public import OddPerfect.SteuerwaldFree
public import OddPerfect.Valuations

/-! The remaining case of Steuerwald's 1937 theorem, when 3 divides the number. -/

public section

namespace OddPerfect

open ArithmeticFunction

/-- If all nonspecial primes occurred to exponent two, the branch containing 3
would receive at least three copies of 3 from distinct divisor sums. -/
theorem steuerwald_three_present {N p : ℕ} (hN : N.Perfect) (hp : p.Prime)
    (hp4 : p % 4 = 1) (he : N.factorization p % 4 = 1)
    (hsq : ∀ q : ℕ, q.Prime → q ∣ N → q ≠ p → N.factorization q = 2)
    (h3 : 3 ∣ N) : False := by
  have h3exp := hsq 3 (by decide) h3 (by omega)
  have force {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (ho : Odd r)
      (hd : r ∣ ∑ d ∈ (q ^ N.factorization q).divisors, d) : r ∣ N := by
    apply dvd_perfect_of_exact_prime_pow hN hq _ _ hr ho hd
    · exact Nat.ordProj_dvd _ _
    · rw [hq.pow_dvd_iff_le_factorization hN.2.ne']
      omega
  have step (q r : ℕ) (hqN : q ∣ N) (hne : q ≠ p)
      (cert : q.Prime ∧ r.Prime ∧ Odd r ∧ r ∣ 1 + q + q ^ 2) : r ∣ N := by
    obtain ⟨hq, hr, ho, hd⟩ := cert
    apply force hq hr ho
    rw [hsq q hq hqN hne, Nat.sum_divisors_prime_pow (f := fun x => x) hq]
    simpa [Finset.sum_range_succ] using hd
  have special {r : ℕ} (hr : r.Prime) (ho : Odd r) (hd : r ∣ 1 + p) : r ∣ N := by
    apply force hp hr ho
    rw [Nat.sum_divisors_prime_pow (f := fun x => x) hp]
    have hpair : r ∣ ∑ i ∈ Finset.range 2, p ^ i := by simpa [Finset.sum_range_succ] using hd
    rw [dvd_geom_sum_iff_remainder hpair, show (N.factorization p + 1) % 2 = 0 by omega]
    simp
  have close (s : Finset ℕ) (hcard : s.card = 3)
      (hcert : ∀ q ∈ s, q.Prime ∧ 3 ∣ 1 + q + q ^ 2)
      (hmem : ∀ q ∈ s, q ∣ N ∧ q ≠ p) : False := by
    have bound := card_le_factorization_of_sigma_sources hN (by decide : Odd 3)
      (by decide) s (fun q hq => Nat.mem_primeFactors.mpr
        ⟨(hcert q hq).1, (hmem q hq).1, hN.2.ne'⟩) (by
          intro q hq
          obtain ⟨hprime, hdvd⟩ := hcert q hq
          obtain ⟨hqN, hne⟩ := hmem q hq
          rw [hsq q hprime hqN hne, sigma_one_apply_prime_pow hprime]
          simpa [Finset.sum_range_succ] using hdvd)
    omega
  have h13 := step 3 13 h3 (by omega) (by decide +kernel)
  by_cases h13p : 13 = p
  · subst p
    have h7 : 7 ∣ N := special (by decide) (by decide) (by decide)
    have h19 := step 7 19 h7 (by decide) (by decide +kernel)
    have h127 := step 19 127 h19 (by decide) (by decide +kernel)
    exact close {7, 19, 127} (by decide) (by decide) (by simp_all)
  have h61 := step 13 61 h13 h13p (by decide +kernel)
  by_cases h61p : 61 = p
  · subst p
    have h31 : 31 ∣ N := special (by decide) (by decide) (by decide)
    have h331 := step 31 331 h31 (by decide) (by decide +kernel)
    exact close {13, 31, 331} (by decide) (by decide +kernel) (by simp_all)
  have h97 := step 61 97 h61 h61p (by decide +kernel)
  by_cases h97p : 97 = p
  · subst p
    have h7 : 7 ∣ N := special (by decide) (by decide) (by decide)
    exact close {13, 61, 7} (by decide) (by decide) (by simp_all)
  exact close {13, 61, 97} (by decide) (by decide) (by simp_all)

/-- Steuerwald's theorem. Every odd perfect number has a nonspecial prime
whose exponent is at least four. The witness prime has even exponent. -/
theorem steuerwald {N : ℕ} (hodd : Odd N) (hN : N.Perfect) :
    ∃ p ∈ N.primeFactors, p % 4 = 1 ∧ N.factorization p % 4 = 1 ∧
      ∃ q ∈ N.primeFactors, q ≠ p ∧ Even (N.factorization q) ∧ 4 ≤ N.factorization q := by
  obtain ⟨p, hp, hp4, he, hEven⟩ := euler_exponents hodd hN
  refine ⟨p, hp, hp4, he, ?_⟩
  by_contra h
  have hsq (q : ℕ) (hq : q.Prime) (hd : q ∣ N) (hne : q ≠ p) : N.factorization q = 2 := by
    have hpos := (hq.dvd_iff_one_le_factorization hN.2.ne').mp hd
    have hev := hEven q hne
    have hlt : ¬ 4 ≤ N.factorization q := fun h4 => h ⟨q, Nat.mem_primeFactors.mpr
      ⟨hq, hd, hN.2.ne'⟩, hne, hev, h4⟩
    obtain ⟨k, hk⟩ := hev
    omega
  have hprime := Nat.prime_of_mem_primeFactors hp
  by_cases h3 : 3 ∣ N
  · exact steuerwald_three_present hN hprime hp4 he hsq h3
  · exact steuerwald_three_free hN hodd hprime hp4 he hsq h3

end OddPerfect
