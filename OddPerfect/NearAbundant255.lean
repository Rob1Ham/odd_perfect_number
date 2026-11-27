module

public import OddPerfect.ExceptionalNonresidues
public import OddPerfect.AbundancyLimit
public import OddPerfect.Forcing

public section
namespace OddPerfect
open Finset ArithmeticFunction

/-- If a known divisor nearly reaches abundance, every additional prime
through the stated threshold makes the perfect number abundant. -/
theorem not_dvd_of_partial_abundancy {N D r K : ℕ} (hN : N.Perfect) (hD : D∣N)
    (hr : r.Prime) (hrD : ¬r∣D) (hrK : r≤K) (hcut : 2*D*K<sigma 1 D*(K+1)) : ¬r∣N := by
  intro hrN
  have hcop := (hr.coprime_iff_not_dvd.mpr hrD).symm
  have hdv := hcop.mul_dvd_of_dvd_of_dvd hD hrN
  have hratio : r*(K+1)≤K*(r+1) := by nlinarith
  have hlt : (2*D*r)*K<(sigma 1 D*(r+1))*K := calc
    _ = (2*D*K)*r := by ring
    _ < (sigma 1 D*(K+1))*r := Nat.mul_lt_mul_of_pos_right hcut hr.pos
    _ ≤ _ := by nlinarith [Nat.mul_le_mul_left (sigma 1 D) hratio]
  have hsmall := Nat.lt_of_mul_lt_mul_right hlt
  have hab : (D*r).Abundant := by
    rw [Nat.abundant_iff_sum_divisors,←sigma_one_apply,isMultiplicative_sigma.map_mul_of_coprime hcop]
    have hprime : sigma 1 r=r+1 := by simpa [sum_range_succ,add_comm] using sigma_one_apply_prime_pow (i:=1) hr
    rw [hprime]
    simpa only [mul_assoc] using hsmall
  exact (Nat.perfect_iff_not_abundant_and_not_deficient hN.2.ne).mp hN |>.1 (hab.of_dvd hdv hN.2.ne')

private def core255 (a b : ℕ) := 3^a*5^b*17^2

private theorem sigma_core255 (a b : ℕ) : sigma 1 (core255 a b)=
    (∑ j∈range (a+1),3^j)*(∑ j∈range (b+1),5^j)*(∑ j∈range 3,17^j) := by
  have hc3 := ((by decide : Nat.Coprime 3 17).pow_left a).pow_right 2
  have hc5 := ((by decide : Nat.Coprime 5 17).pow_left b).pow_right 2
  have hc35 := ((by decide : Nat.Coprime 3 5).pow_left a).pow_right b
  rw [core255,isMultiplicative_sigma.map_mul_of_coprime (hc3.mul_left hc5),
    isMultiplicative_sigma.map_mul_of_coprime hc35,sigma_one_apply_prime_pow Nat.prime_three,
    sigma_one_apply_prime_pow (by decide : Nat.Prime 5),sigma_one_apply_prime_pow (by decide : Nat.Prime 17)]

private theorem forced_from_exact_sigma {N p e r : ℕ} (hN : N.Perfect) (hp : p.Prime)
    (he : N.factorization p=e) (hr : r.Prime) (hro : Odd r) (hdiv : r∣sigma 1 (p^e)) : r∣N := by
  apply dvd_perfect_of_exact_prime_pow hN hp ((hp.pow_dvd_iff_le_factorization hN.2.ne').mpr he.ge)
    (fun H => by have := (hp.pow_dvd_iff_le_factorization hN.2.ne').mp H; omega) hr hro
  rwa [←sigma_one_apply]

private theorem core_excludes {N r a b K : ℕ} (hN : N.Perfect) (hcore : core255 a b ∣ N)
    (hr : r.Prime) (hr3 : r≠3) (hr5 : r≠5) (hr17 : r≠17) (hrK : r≤K)
    (hcut : 2*core255 a b*K<(∑ j∈range (a+1),3^j)*(∑ j∈range (b+1),5^j)*(∑ j∈range 3,17^j)*(K+1)) : ¬r∣N := by
  have hn {p : ℕ} (hp : p.Prime) (hne : r≠p) {j : ℕ} : ¬r∣p^j :=
    fun h => hne ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow h))
  apply not_dvd_of_partial_abundancy hN hcore hr _ hrK
  · rwa [sigma_core255]
  · intro h
    rcases hr.dvd_mul.mp (show r∣3^a*5^b*17^2 from h) with h | h
    · rcases hr.dvd_mul.mp h with h | h
      · exact hn Nat.prime_three hr3 h
      · exact hn (by decide : Nat.Prime 5) hr5 h
    · exact hn (by decide : Nat.Prime 17) hr17 h

/-- A square divisor 255² forces the exponents of three and five above
their first cases and excludes every additional prime through 217. -/
theorem exponents_and_prime_gap_of_255_sq {N : ℕ} (hN : N.Perfect) (ho : Odd N) (h255 : 255^2∣N) :
    6≤N.factorization 3 ∧ 6≤N.factorization 5 ∧
      ∀ r, r.Prime → r∣N → r≠3 → r≠5 → r≠17 → 217<r := by
  have h22 : core255 2 2∣N := (by decide : core255 2 2∣255^2).trans h255
  have e3 := (Nat.prime_three.pow_dvd_iff_le_factorization hN.2.ne' (k:=2)).mp ((by decide : 3^2∣255^2).trans h255)
  have h5p : Nat.Prime 5 := by decide
  have e5 := (h5p.pow_dvd_iff_le_factorization hN.2.ne' (k:=2)).mp ((by decide : 5^2∣255^2).trans h255)
  have no19 {r : ℕ} (hr : r.Prime) (hr3 : r≠3) (hr5 : r≠5) (hr17 : r≠17) (hrK : r≤19) : ¬r∣N :=
    core_excludes hN h22 hr hr3 hr5 hr17 hrK (by decide)
  have h3six : 6≤N.factorization 3 := by
    by_contra! hh
    obtain ⟨q,_,hq4,_,hrest⟩ := euler_exponents ho hN
    have he := Nat.even_iff.mp (hrest 3 (by rintro rfl; omega))
    rcases (by omega : N.factorization 3=2 ∨ N.factorization 3=4) with heq | heq
    · exact no19 (by decide : Nat.Prime 13) (by decide) (by decide) (by decide) (by decide)
        (forced_from_exact_sigma hN Nat.prime_three heq (by decide) (by decide) (by rw [sigma_one_apply_prime_pow Nat.prime_three]; decide))
    · exact no19 (by decide : Nat.Prime 11) (by decide) (by decide) (by decide) (by decide)
        (forced_from_exact_sigma hN Nat.prime_three heq (by decide) (by decide) (by rw [sigma_one_apply_prime_pow Nat.prime_three]; decide))
  have h36 := (Nat.prime_three.pow_dvd_iff_le_factorization hN.2.ne').mpr h3six
  have h62 : core255 6 2∣N := (by decide : core255 6 2∣Nat.lcm (3^6) (255^2)).trans (Nat.lcm_dvd h36 h255)
  have no78 {r : ℕ} (hr : r.Prime) (hr3 : r≠3) (hr5 : r≠5) (hr17 : r≠17) (hrK : r≤78) : ¬r∣N :=
    core_excludes hN h62 hr hr3 hr5 hr17 hrK (by decide)
  have h5six : 6≤N.factorization 5 := by
    by_contra! hh
    rcases (by omega : N.factorization 5=2 ∨ N.factorization 5=3 ∨ N.factorization 5=4 ∨ N.factorization 5=5) with e | e | e | e
    · exact no78 (by decide : Nat.Prime 31) (by decide) (by decide) (by decide) (by decide)
        (forced_from_exact_sigma hN h5p e (by decide) (by decide) (by rw [sigma_one_apply_prime_pow h5p]; decide))
    · exact no78 (by decide : Nat.Prime 13) (by decide) (by decide) (by decide) (by decide)
        (forced_from_exact_sigma hN h5p e (by decide) (by decide) (by rw [sigma_one_apply_prime_pow h5p]; decide))
    · exact no78 (by decide : Nat.Prime 11) (by decide) (by decide) (by decide) (by decide)
        (forced_from_exact_sigma hN h5p e (by decide) (by decide) (by rw [sigma_one_apply_prime_pow h5p]; decide))
    · exact no78 (by decide : Nat.Prime 31) (by decide) (by decide) (by decide) (by decide)
        (forced_from_exact_sigma hN h5p e (by decide) (by decide) (by rw [sigma_one_apply_prime_pow h5p]; decide))
  have h56 := (h5p.pow_dvd_iff_le_factorization hN.2.ne').mpr h5six
  have h66 : core255 6 6∣N := (by decide : core255 6 6∣Nat.lcm (5^6) (core255 6 2)).trans (Nat.lcm_dvd h56 h62)
  refine ⟨h3six,h5six,?_⟩
  intro r hr hrN hr3 hr5 hr17
  by_contra! hle
  exact core_excludes hN h66 hr hr3 hr5 hr17 hle (by decide) hrN

end OddPerfect
