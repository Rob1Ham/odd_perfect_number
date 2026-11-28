module

public import OddPerfect.FactorialStirlingSupportObstruction
public import OddPerfect.PrimeByPrimeMultiplicityConservation
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic.Positivity

/-!
# p-adic Valuation Conservation and Legendre Factorial Dyadic-Radical Bounds

Establishes two unconditional structural theorems on odd perfect numbers `N`:

1. `OddPerfect.odd_perfect_multiplicity_conservation_and_dyadic_isolation`:
   Translates `sigma 1 N = 2 * N` and the prime-power multiplicativity of `sigma 1` into
   exact `multiplicity` conservation laws for `p = 2` and every odd prime `p`, together with
   dyadic isolation of the unique Euler prime component `q ∈ N.primeFactors` satisfying
   `multiplicity 2 (sigma 1 (ordProj[q] N)) = 1`.
2. `OddPerfect.odd_perfect_legendre_factorial_dyadic_radical_bound`:
   Applies Legendre's formula (`Nat.Prime.sub_one_mul_multiplicity_factorial` and
   `sub_one_mul_multiplicity_factorial_lt_of_ne_zero`) to `ω = N.primeFactors.card ≥ 5` to
   evaluate `multiplicity 2 (2 ^ ω * ω!) = 2 * ω - (Nat.digits 2 ω).sum`, deduce
   `3 * 2 ^ (2 * ω - (Nat.digits 2 ω).sum) ≤ 2 ^ ω * ω! < rad`, and combine with
   `rad ^ 6 < 3 * N ^ 4` to obtain `(3 * 2 ^ (2 * ω - (Nat.digits 2 ω).sum)) ^ 6 < 3 * N ^ 4`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- Exact `multiplicity` conservation for `p = 2` and every odd prime `p` across the
prime-power components `sigma 1 (ordProj[q] N)` of an odd perfect number `N`, together with
dyadic isolation of the unique Euler component `q ∈ N.primeFactors`. -/
theorem odd_perfect_multiplicity_conservation_and_dyadic_isolation
    {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    multiplicity 2 N = 0 ∧
    multiplicity 2 (sigma 1 N) = 1 ∧
    (∑ q ∈ N.primeFactors, multiplicity 2 (sigma 1 (ordProj[q] N))) = 1 ∧
    (∀ p : ℕ, p.Prime → Odd p →
      multiplicity p N = N.factorization p ∧
      multiplicity p (sigma 1 N) = N.factorization p ∧
      (∑ q ∈ N.primeFactors, multiplicity p (sigma 1 (ordProj[q] N))) = multiplicity p N) ∧
    (∃ q ∈ N.primeFactors, multiplicity 2 (sigma 1 (ordProj[q] N)) = 1 ∧
      ∀ r ∈ N.primeFactors, r ≠ q → multiplicity 2 (sigma 1 (ordProj[r] N)) = 0) := by
  have hN0 : N ≠ 0 := hN.2.ne'
  have hσ_eq : sigma 1 N = 2 * N :=
    (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN)
  have hprod_σ : (∏ q ∈ N.primeFactors, sigma 1 (ordProj[q] N)) = sigma 1 N :=
    (isMultiplicative_sigma.multiplicative_factorization (sigma 1) hN0).symm
  have hcomp_ne0 : ∀ q ∈ N.primeFactors, sigma 1 (ordProj[q] N) ≠ 0 := by
    intro q hq
    have hq_prime := Nat.prime_of_mem_primeFactors hq
    exact (sigma_pos 1 _ (pow_ne_zero _ hq_prime.ne_zero)).ne'
  have hN_fac2 : N.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd ho.not_two_dvd_nat
  have hN_mult2 : multiplicity 2 N = 0 := by
    rw [← Nat.factorization_def N Nat.prime_two, hN_fac2]
  have hσ_fac2 : (sigma 1 N).factorization 2 = 1 := by
    rw [hσ_eq, Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) hN0, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two, hN_fac2, add_zero]
  have hσ_mult2 : multiplicity 2 (sigma 1 N) = 1 := by
    rw [← Nat.factorization_def (sigma 1 N) Nat.prime_two, hσ_fac2]
  have hsum_mult : ∀ p : ℕ, p.Prime →
      (∑ q ∈ N.primeFactors, multiplicity p (sigma 1 (ordProj[q] N))) =
        (sigma 1 N).factorization p := by
    intro p hp
    have hprod_fac : (sigma 1 N).factorization p =
        ∑ q ∈ N.primeFactors, (sigma 1 (ordProj[q] N)).factorization p := by
      rw [← hprod_σ]
      exact Nat.factorization_prod_apply hcomp_ne0
    rw [hprod_fac]
    refine Finset.sum_congr rfl fun q _ => ?_
    exact (Nat.factorization_def (sigma 1 (ordProj[q] N)) hp).symm
  have hsum_mult2 : (∑ q ∈ N.primeFactors, multiplicity 2 (sigma 1 (ordProj[q] N))) = 1 := by
    rw [hsum_mult 2 Nat.prime_two, hσ_fac2]
  have hodd_primes : ∀ p : ℕ, p.Prime → Odd p →
      multiplicity p N = N.factorization p ∧
      multiplicity p (sigma 1 N) = N.factorization p ∧
      (∑ q ∈ N.primeFactors, multiplicity p (sigma 1 (ordProj[q] N))) = multiplicity p N := by
    intro p hp hp_odd
    have hp_ne2 : p ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hp_odd)
    have h2_facp : (2 : ℕ).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun hd =>
        hp_ne2 (Nat.le_antisymm (Nat.le_of_dvd (by decide) hd) hp.two_le)
    have hσ_facp : (sigma 1 N).factorization p = N.factorization p := by
      rw [hσ_eq, Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) hN0, Finsupp.add_apply,
        h2_facp, zero_add]
    have hmN : multiplicity p N = N.factorization p :=
      (Nat.factorization_def N hp).symm
    have hmσ : multiplicity p (sigma 1 N) = N.factorization p := by
      rw [← Nat.factorization_def (sigma 1 N) hp, hσ_facp]
    have hsum_p : (∑ q ∈ N.primeFactors, multiplicity p (sigma 1 (ordProj[q] N))) =
        multiplicity p N := by
      rw [hsum_mult p hp, hσ_facp, hmN]
    exact ⟨hmN, hmσ, hsum_p⟩
  obtain ⟨q, hq, hq4, he4, hev⟩ := euler_exponents ho hN
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hq_mod : sigma 1 (ordProj[q] N) % 4 = 2 := by
    have hS4 := sigma_modEq_of_one hq_prime (show q ≡ 1 [MOD 4] from hq4) (N.factorization q)
    change sigma 1 (ordProj[q] N) % 4 = (N.factorization q + 1) % 4 at hS4
    omega
  have hq_dvd2 : 2 ∣ sigma 1 (ordProj[q] N) := Nat.dvd_of_mod_eq_zero (by omega)
  have hq_ndvd4 : ¬ 2 ^ 2 ∣ sigma 1 (ordProj[q] N) := by
    intro hd
    have : sigma 1 (ordProj[q] N) % 4 = 0 := Nat.mod_eq_zero_of_dvd hd
    omega
  have hq_ne0 : sigma 1 (ordProj[q] N) ≠ 0 := hcomp_ne0 q hq
  have hq_fac2_ge1 : 1 ≤ (sigma 1 (ordProj[q] N)).factorization 2 :=
    (Nat.prime_two.dvd_iff_one_le_factorization hq_ne0).mp hq_dvd2
  have hq_fac2_lt2 : (sigma 1 (ordProj[q] N)).factorization 2 < 2 :=
    Nat.lt_of_not_le fun hge =>
      hq_ndvd4 ((Nat.prime_two.pow_dvd_iff_le_factorization hq_ne0).mpr hge)
  have hq_mult2 : multiplicity 2 (sigma 1 (ordProj[q] N)) = 1 := by
    rw [← Nat.factorization_def (sigma 1 (ordProj[q] N)) Nat.prime_two]
    omega
  have hr_mult2 : ∀ r ∈ N.primeFactors, r ≠ q → multiplicity 2 (sigma 1 (ordProj[r] N)) = 0 := by
    intro r hr hrq
    obtain ⟨k, hk⟩ := hev r hrq
    have hord_sq : IsSquare (ordProj[r] N) := ⟨r ^ k, by rw [hk, pow_add]⟩
    have hord_odd : Odd (ordProj[r] N) := ho.of_dvd_nat (Nat.ordProj_dvd N r)
    have hsig_odd : Odd (sigma 1 (ordProj[r] N)) :=
      (odd_sigma_iff_square_of_odd hord_odd).mpr hord_sq
    have hsig_fac2 : (sigma 1 (ordProj[r] N)).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hsig_odd.not_two_dvd_nat
    rw [← Nat.factorization_def (sigma 1 (ordProj[r] N)) Nat.prime_two, hsig_fac2]
  exact ⟨hN_mult2, hσ_mult2, hsum_mult2, hodd_primes, q, hq, hq_mult2, hr_mult2⟩

/-- Legendre's dyadic valuation identity for `2 ^ ω * ω!` combined with the odd-prime
factorial radical bound `2 ^ ω * ω! < rad` and the Acquaah–Konyagin sixth-power bound
`rad ^ 6 < 3 * N ^ 4`. -/
theorem odd_perfect_legendre_factorial_dyadic_radical_bound
    {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    let ω := N.primeFactors.card
    let rad := ∏ p ∈ N.primeFactors, p
    multiplicity 2 (Nat.factorial ω) + (Nat.digits 2 ω).sum = ω ∧
    multiplicity 2 (Nat.factorial ω) < ω ∧
    1 ≤ (Nat.digits 2 ω).sum ∧
    multiplicity 2 (2 ^ ω * Nat.factorial ω) = 2 * ω - (Nat.digits 2 ω).sum ∧
    2 ^ (2 * ω - (Nat.digits 2 ω).sum) ∣ 2 ^ ω * Nat.factorial ω ∧
    3 * 2 ^ (2 * ω - (Nat.digits 2 ω).sum) ≤ 2 ^ ω * Nat.factorial ω ∧
    3 * 2 ^ (2 * ω - (Nat.digits 2 ω).sum) < rad ∧
    (3 * 2 ^ (2 * ω - (Nat.digits 2 ω).sum)) ^ 6 < 3 * N ^ 4 := by
  intro ω rad
  have h5 : 5 ≤ ω := five_le_distinct_prime_factor_count ho hN
  have hω0 : ω ≠ 0 := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hleg : multiplicity 2 ω.factorial = ω - (Nat.digits 2 ω).sum := by
    have h := Nat.Prime.sub_one_mul_multiplicity_factorial (n := ω) Nat.prime_two
    simpa using h
  have hdig_le : (Nat.digits 2 ω).sum ≤ ω := Nat.digit_sum_le 2 ω
  have hadd : multiplicity 2 ω.factorial + (Nat.digits 2 ω).sum = ω := by
    omega
  have hlt : multiplicity 2 ω.factorial < ω := by
    have h := sub_one_mul_multiplicity_factorial_lt_of_ne_zero 2 hω0
    simpa using h
  have hdig_ge1 : 1 ≤ (Nat.digits 2 ω).sum := by
    omega
  have hmult_prod : multiplicity 2 (2 ^ ω * ω.factorial) = 2 * ω - (Nat.digits 2 ω).sum := by
    rw [multiplicity_base_pow_mul (by decide : 1 < 2) (Nat.factorial_ne_zero ω) ω]
    omega
  have hpow_ne0 : 2 ^ ω * ω.factorial ≠ 0 := by positivity
  have hdvd_pow : 2 ^ (2 * ω - (Nat.digits 2 ω).sum) ∣ 2 ^ ω * ω.factorial := by
    rw [Nat.pow_dvd_iff_le_multiplicity (by decide : (2 : ℕ) ≠ 1) hpow_ne0, hmult_prod]
  have hdvd_3 : 3 ∣ 2 ^ ω * ω.factorial :=
    dvd_mul_of_dvd_right (Nat.dvd_factorial (by decide : 0 < 3) (by omega)) (2 ^ ω)
  have hcop : Nat.Coprime 3 (2 ^ (2 * ω - (Nat.digits 2 ω).sum)) :=
    (by decide : Nat.Coprime 3 2).pow_right _
  have hdvd_3pow : 3 * 2 ^ (2 * ω - (Nat.digits 2 ω).sum) ∣ 2 ^ ω * ω.factorial :=
    hcop.mul_dvd_of_dvd_of_dvd hdvd_3 hdvd_pow
  have hle_prod : 3 * 2 ^ (2 * ω - (Nat.digits 2 ω).sum) ≤ 2 ^ ω * ω.factorial :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hpow_ne0) hdvd_3pow
  obtain ⟨q, a, m, hq, _, ha4, hqm, hform⟩ := euler_form ho hN
  have ha : 0 < a := by omega
  obtain ⟨h2rad, _, hrad6⟩ :=
    odd_perfect_radical_sq_le_euler_mul_and_pow_six_lt ho hN hq ha hqm hform
  have hlt_rad : 3 * 2 ^ (2 * ω - (Nat.digits 2 ω).sum) < rad :=
    lt_of_le_of_lt hle_prod h2rad
  have hlt_pow6 : (3 * 2 ^ (2 * ω - (Nat.digits 2 ω).sum)) ^ 6 < 3 * N ^ 4 :=
    lt_trans (Nat.pow_lt_pow_left hlt_rad (by decide : 6 ≠ 0)) hrad6
  exact ⟨hadd, hlt, hdig_ge1, hmult_prod, hdvd_pow, hle_prod, hlt_rad, hlt_pow6⟩

end OddPerfect
