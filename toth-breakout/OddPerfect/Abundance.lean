module

public import OddPerfect.Forcing
public import Mathlib.NumberTheory.FactorisationProperties

/-!
J. J. Sylvester, *Sur les nombres parfaits*, Comptes rendus 106 (1888), 403–405.
The corollary excluding 105 appears on p. 605 of the collected papers, vol. IV.
[Sylvester's paper](https://rcin.org.pl/impan/Content/122671/PDF/WA35_145312_11371-4_Art55.pdf)
-/

public section

namespace OddPerfect

/-- A prime congruent to three modulo four cannot occur exactly once in an odd perfect number. -/
theorem sq_dvd_of_prime_mod_four_three {N p : ℕ} (hN : Nat.Perfect N) (ho : Odd N)
    (hp : Nat.Prime p) (hmod : p % 4 = 3) (hd : p ∣ N) : p ^ 2 ∣ N := by
  by_contra hsq
  obtain ⟨b, hb, hcop⟩ := exists_coprime_cofactor_of_exact_prime_pow (k := 1) hp
    (by simpa only [pow_one] using hd) hsq
  have hs := sum_divisors_dvd_two_mul hN hb hcop
  rw [pow_one, hp.divisors] at hs
  simp [Ne.symm hp.ne_one] at hs
  have h4 : 4 ∣ 1 + p := by omega
  exact ho.not_two_dvd_nat ((Nat.mul_dvd_mul_iff_left (a := 2) (by decide)).mp (h4.trans hs))

/-- Sylvester's exclusion of 105. The forced divisor 3² · 5 · 7² is abundant. -/
theorem not_dvd_105_of_odd_perfect {N : ℕ} (hN : Nat.Perfect N) (ho : Odd N) : ¬ 105 ∣ N := by
  intro h105
  have h9 : 9 ∣ N := sq_dvd_of_prime_mod_four_three hN ho (p := 3)
    (by decide) (by decide) ((by decide : 3 ∣ 105).trans h105)
  have h49 : 49 ∣ N := sq_dvd_of_prime_mod_four_three hN ho (p := 7)
    (by decide) (by decide) ((by decide : 7 ∣ 105).trans h105)
  have h5 := (by decide : 5 ∣ 105).trans h105
  have h45 : 45 ∣ N := (by decide : Nat.Coprime 9 5).mul_dvd_of_dvd_of_dvd h9 h5
  have h2205 : 2205 ∣ N := (by decide : Nat.Coprime 45 49).mul_dvd_of_dvd_of_dvd h45 h49
  have ha : Nat.Abundant 2205 := by decide +kernel
  exact ((Nat.perfect_iff_not_abundant_and_not_deficient hN.2.ne).mp hN).1
    (ha.of_dvd h2205 hN.2.ne')

end OddPerfect
