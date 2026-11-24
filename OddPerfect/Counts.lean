module

public import OddPerfect.Steuerwald

/-! The total and distinct prime-factor counts of a number in Euler form. -/

public section

namespace OddPerfect

/-- The excess over Euler's baseline is the sum of the excess exponents. -/
theorem prime_factor_count_excess {N p : ℕ} (hp : p ∈ N.primeFactors)
    (heven : ∀ q : ℕ, q ≠ p → Even (N.factorization q)) :
    N.primeFactorsList.length + 1 = 2 * N.primeFactors.card +
      (N.factorization p - 1) + ∑ q ∈ N.primeFactors.erase p, (N.factorization q - 2) := by
  let S := N.primeFactors.erase p
  have hpos (q : ℕ) (hq : q ∈ N.primeFactors) : 0 < N.factorization q := by
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hq)
  have hmin (q : ℕ) (hq : q ∈ S) : 2 ≤ N.factorization q := by
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hq
    obtain ⟨k, hk⟩ := heven q hne
    have := hpos q hmem
    omega
  have hsum : (∑ q ∈ S, N.factorization q) =
      S.card * 2 + ∑ q ∈ S, (N.factorization q - 2) := by
    calc
      _ = ∑ q ∈ S, (2 + (N.factorization q - 2)) :=
        Finset.sum_congr rfl (fun q hq => by have := hmin q hq; omega)
      _ = _ := by simp [Finset.sum_add_distrib]
  have htotal : N.primeFactorsList.length = N.factorization p + ∑ q ∈ S, N.factorization q := by
    rw [← ArithmeticFunction.cardFactors_apply, ArithmeticFunction.cardFactors_eq_sum_factorization]
    exact (Finset.add_sum_erase N.primeFactors _ hp).symm
  have hcard : S.card + 1 = N.primeFactors.card := Finset.card_erase_add_one hp
  have := hpos p hp
  change N.primeFactorsList.length + 1 = _ + ∑ q ∈ S, _
  omega

/-- Euler's lower bound Ω(N) ≥ 2ω(N) − 1, expressed without truncated subtraction. -/
theorem euler_prime_factor_count {N : ℕ} (ho : Odd N) (hN : Nat.Perfect N) :
    2 * N.primeFactors.card ≤ N.primeFactorsList.length + 1 := by
  obtain ⟨p, hp, _, _, he⟩ := euler_exponents ho hN
  have := prime_factor_count_excess hp he
  omega

/-- Any fourth power of a prime in an odd perfect number improves Euler's
count bound to Ω(N) ≥ 2ω(N) + 1. -/
theorem prime_factor_count_of_fourth_power {N r : ℕ} (ho : Odd N) (hN : Nat.Perfect N)
    (hr : r.Prime) (hpow : r ^ 4 ∣ N) :
    2 * N.primeFactors.card + 1 ≤ N.primeFactorsList.length := by
  obtain ⟨p, hp, _, _, he⟩ := euler_exponents ho hN
  have h := prime_factor_count_excess hp he
  have hlarge := (hr.pow_dvd_iff_le_factorization ho.pos.ne').1 hpow
  by_cases hrp : r = p
  · subst r
    omega
  have hmem : r ∈ N.primeFactors := Finsupp.mem_support_iff.mpr
    (show N.factorization r ≠ 0 by omega)
  have hterm : N.factorization r - 2 ≤
      ∑ q ∈ N.primeFactors.erase p, (N.factorization q - 2) :=
    Finset.single_le_sum (f := fun q => N.factorization q - 2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hrp, hmem⟩)
  omega

/-- Steuerwald's unconditional count bound for every odd perfect number. -/
theorem steuerwald_prime_factor_count {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    2 * N.primeFactors.card + 1 ≤ N.primeFactorsList.length := by
  obtain ⟨_, _, _, _, q, hq, _, _, h4⟩ := steuerwald ho hN
  have hprime := Nat.prime_of_mem_primeFactors hq
  exact prime_factor_count_of_fourth_power ho hN hprime
    ((hprime.pow_dvd_iff_le_factorization ho.pos.ne').2 h4)

/-- The total number of prime factors of an odd perfect number is odd because
only the special prime occurs to odd exponent. -/
theorem odd_total_prime_factor_count {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    Odd N.primeFactorsList.length := by
  obtain ⟨p, a, m, hp, _, ha, _, heq⟩ := euler_form ho hN
  have hm : m ≠ 0 := by
    rintro rfl
    simp [heq] at ho
  rw [← ArithmeticFunction.cardFactors_apply, heq,
    ArithmeticFunction.cardFactors_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hm),
    ArithmeticFunction.cardFactors_apply_prime_pow hp, ArithmeticFunction.cardFactors_pow]
  exact Nat.odd_iff.mpr (by omega)

end OddPerfect
