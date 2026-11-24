module

public import OddPerfect.Cuts
public import OddPerfect.Order
import OddPerfect.Euler
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-! # Quadratic reciprocity on divisor-sum edges -/

public section

namespace OddPerfect

open ArithmeticFunction

/-- A prime divisor of an even-exponent component sees the component base as a square. -/
theorem isSquare_of_dvd_sigma_even {p r e : ℕ} (hp : p.Prime) (hr : r.Prime)
    (he : Even e) (hd : r ∣ sigma 1 (p^e)) : IsSquare (p : ZMod r) := by
  have hpow : (p : ZMod r)^(e+1) = 1 := by
    by_cases h : (p : ZMod r) = 1
    · simp [h]
    · rw [sigma_one_apply] at hd
      exact orderOf_dvd_iff_pow_eq_one.mp (by simpa [h] using (dvd_sum_divisors_prime_pow_iff hp hr e).mp hd)
  obtain ⟨k,hk⟩ := he
  refine ⟨(p : ZMod r)^(k+1), ?_⟩
  rw [← pow_add, show k+1+(k+1)=e+1+1 by omega, pow_succ, hpow, one_mul]

/-- At a target prime `3 mod 4`, quadratic residuosity is also sufficient for some
positive even exponent to supply an edge. -/
theorem exists_even_dvd_sigma_iff_isSquare {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hpr : p ≠ r) (hr4 : r%4 = 3) :
    (∃ e : ℕ, 0 < e ∧ Even e ∧ r ∣ sigma 1 (p^e)) ↔ IsSquare (p : ZMod r) := by
  let : Fact r.Prime := ⟨hr⟩
  constructor
  · rintro ⟨e,_,he,hd⟩
    exact isSquare_of_dvd_sigma_even hp hr he hd
  · intro hs
    have hc : (p : ZMod r) ≠ 0 := fun h => hpr ((Nat.prime_dvd_prime_iff_eq hr hp).mp
      ((ZMod.natCast_eq_zero_iff p r).mp h)).symm
    by_cases hone : (p : ZMod r) = 1
    · refine ⟨r-1, by omega, Nat.even_iff.mpr (by omega), ?_⟩
      rw [sigma_one_apply, dvd_sum_divisors_prime_pow_iff hp hr, ite_eq_left hone,
        Nat.sub_add_cancel hr.one_le]
    · let e := 3*(r/2)-1
      have he : e+1 = 3*(r/2) := by dsimp [e]; omega
      refine ⟨e, by dsimp [e]; omega, Nat.even_iff.mpr (by dsimp [e]; omega), ?_⟩
      rw [sigma_one_apply, dvd_sum_divisors_prime_pow_iff hp hr, ite_eq_right hone, he]
      exact dvd_mul_of_dvd_right (orderOf_dvd_iff_pow_eq_one.mpr ((ZMod.euler_criterion r hc).mp hs)) _

/-- Between distinct `3 mod 4` primes, exactly one direction can occur at some
positive even exponent. The exponents in this statement may vary independently. -/
theorem even_sigma_direction_iff_not_reverse {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hpr : p ≠ r) (hp4 : p%4=3) (hr4 : r%4=3) :
    (∃ e : ℕ, 0 < e ∧ Even e ∧ r ∣ sigma 1 (p^e)) ↔
      ¬ ∃ f : ℕ, 0 < f ∧ Even f ∧ p ∣ sigma 1 (r^f) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact r.Prime := ⟨hr⟩
  rw [exists_even_dvd_sigma_iff_isSquare hp hr hpr hr4,
    exists_even_dvd_sigma_iff_isSquare hr hp hpr.symm hp4]
  exact ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three hr4 hp4 hpr.symm

private theorem even_exponent_of_three_mod_four {N p : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hp4 : p%4=3) : Even (N.factorization p) := by
  obtain ⟨q,_,hq4,_,hrest⟩ := euler_exponents ho hN
  exact hrest p (by rintro rfl; omega)

/-- A divisor-sum edge between two primes `3 mod 4` in an odd perfect number
excludes the reverse edge at the actual component exponents. -/
theorem not_sigmaEdge_reverse_of_three_mod_four {N p r : ℕ} (hN : N.Perfect) (ho : Odd N)
    (edge : sigmaEdge N p r) (hpr : p ≠ r) (hp4 : p%4=3) (hr4 : r%4=3) : ¬ sigmaEdge N r p := by
  intro rev
  apply (even_sigma_direction_iff_not_reverse (Nat.prime_of_mem_primeFactors edge.1)
    (Nat.prime_of_mem_primeFactors edge.2.1) hpr hp4 hr4).mp
    ⟨_, Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp edge.1), even_exponent_of_three_mod_four hN ho hp4,
      edge.2.2⟩
  exact ⟨_, Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp edge.2.1), even_exponent_of_three_mod_four hN ho hr4,
    rev.2.2⟩

/-- A genuine three-cycle of even-exponent geometric sums at three `3 mod 4` primes. -/
theorem even_sigma_three_cycle : 11 ∣ sigma 1 (3^4) ∧ 7 ∣ sigma 1 (11^2) ∧ 3 ∣ sigma 1 (7^2) := by
  rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 3),
    sigma_one_apply_prime_pow (by decide : Nat.Prime 11), sigma_one_apply_prime_pow (by decide : Nat.Prime 7)]
  norm_num [Finset.sum_range_succ]

/-- The integer containing those three exact components is deficient. -/
theorem even_sigma_three_cycle_deficient : sigma 1 (3^4 * 11^2 * 7^2) < 2*(3^4 * 11^2 * 7^2) := by
  rw [isMultiplicative_sigma.map_mul_of_coprime (by decide : Nat.Coprime (3^4 * 11^2) (7^2)),
    isMultiplicative_sigma.map_mul_of_coprime (by decide : Nat.Coprime (3^4) (11^2)),
    sigma_one_apply_prime_pow (by decide : Nat.Prime 3), sigma_one_apply_prime_pow (by decide : Nat.Prime 11),
    sigma_one_apply_prime_pow (by decide : Nat.Prime 7)]
  norm_num [Finset.sum_range_succ]

/-- Distinct primes in different residue classes can supply each other at even exponents. -/
theorem even_sigma_two_cycle_mixed_residues : 13 ∣ sigma 1 (3^2) ∧ 3 ∣ sigma 1 (13^2) := by
  rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 3), sigma_one_apply_prime_pow (by decide : Nat.Prime 13)]
  norm_num [Finset.sum_range_succ]

private theorem exists_prime_three_mod_four {n : ℕ} (hn : n%4=3) :
    ∃ r : ℕ, r.Prime ∧ r%4=3 ∧ r ∣ n := by
  induction n using induction_on_primes with
  | zero | one => omega
  | prime_mul p a hp ih =>
    by_cases hp3 : p%4 = 3
    · exact ⟨p,hp,hp3,dvd_mul_right _ _⟩
    · have hodd : Odd (p*a) := Nat.odd_iff.mpr (by omega)
      have hpo := Nat.odd_iff.mp (hodd.of_dvd_nat (dvd_mul_right p a))
      have hp1 : p%4=1 := by omega
      rw [Nat.mul_mod,hp1,one_mul,Nat.mod_mod] at hn
      obtain ⟨r,hr,hr4,hd⟩ := ih hn
      exact ⟨r,hr,hr4,dvd_mul_of_dvd_right hd _⟩

private theorem nonsquare_of_dvd_succ {q r : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hq4 : q%4=1) (hr4 : r%4=3) (hd : r ∣ q+1) : ¬ IsSquare (r : ZMod q) := by
  let : Fact q.Prime := ⟨hq⟩
  let : Fact r.Prime := ⟨hr⟩
  intro h
  have hs := (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one hq4 (by omega : r ≠ 2)).mp h
  have hneg : (q : ZMod r) = -1 := by
    have hz := (ZMod.natCast_eq_zero_iff (q+1) r).mpr hd
    simpa [Nat.cast_add, eq_neg_iff_add_eq_zero] using hz
  exact (ZMod.exists_sq_eq_neg_one_iff.mp (hneg ▸ hs)) hr4

/-- A prime `3 mod 4` dividing `q+1` cannot send an even-exponent edge to
`q` when the latter prime is `1 mod 4`. -/
theorem not_dvd_sigma_even_of_dvd_succ {q r e : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hq4 : q%4=1) (hr4 : r%4=3) (hd : r ∣ q+1) (he : Even e) : ¬ q ∣ sigma 1 (r^e) :=
  fun h => nonsquare_of_dvd_succ hq hr hq4 hr4 hd (isSquare_of_dvd_sigma_even hr hq he h)

/-- An Euler prime `5 mod 8` forces a `3 mod 4` successor that cannot send an edge back. -/
theorem exists_oneway_sigmaEdge_of_euler_five_mod_eight {N q : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hqN : q ∈ N.primeFactors) (hq8 : q%8=5) (he : Odd (N.factorization q)) :
    ∃ r ∈ N.primeFactors, r%4=3 ∧ r ∣ q+1 ∧ sigmaEdge N q r ∧ ¬ sigmaEdge N r q := by
  have hq := Nat.prime_of_mem_primeFactors hqN
  obtain ⟨r,hr,hr4,hd⟩ := exists_prime_three_mod_four (n := (q+1)/2) (by omega)
  have hdiv : r ∣ q+1 := hd.trans ⟨2, by omega⟩
  have hs := hdiv.trans (succ_dvd_sigma_prime_pow hq he)
  have hrN : r ∣ N := by
    apply dvd_perfect_of_exact_prime_pow hN hq (Nat.ordProj_dvd _ _)
      (fun h => by have := (hq.pow_dvd_iff_le_factorization hN.2.ne').mp h; omega) hr (Nat.odd_iff.mpr (by omega))
    simpa [sigma_one_apply] using hs
  have hm := Nat.mem_primeFactors.mpr ⟨hr,hrN,hN.2.ne'⟩
  refine ⟨r,hm,hr4,hdiv,⟨hqN,hm,hs⟩,fun h => ?_⟩
  exact not_dvd_sigma_even_of_dvd_succ hq hr (by omega) hr4 hdiv
    (even_exponent_of_three_mod_four hN ho hr4) h.2.2

/-- Across the cut isolating an Euler prime `5 mod 8`, some incoming source is a
quadratic residue and some outgoing target is a nonresidue modulo that Euler prime. -/
theorem euler_five_mod_eight_two_character_classes {N q : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hqN : q ∈ N.primeFactors) (hq8 : q%8=5) (he : Odd (N.factorization q)) :
    ∃ p ∈ N.primeFactors.erase q, ∃ r ∈ N.primeFactors.erase q, p ≠ r ∧
      sigmaEdge N p q ∧ IsSquare (p : ZMod q) ∧ sigmaEdge N q r ∧ ¬ IsSquare (r : ZMod q) := by
  obtain ⟨r,hr,hr4,hd,er,_⟩ := exists_oneway_sigmaEdge_of_euler_five_mod_eight hN ho hqN hq8 he
  have hrq : r ≠ q := by omega
  have hrem := Finset.mem_erase.mpr ⟨hrq,hr⟩
  obtain ⟨p,hp,v,hv,ep⟩ := exists_sigmaEdge_leaving hN _ (Finset.erase_ssubset hqN) ⟨r,hrem⟩
  have hvq : v = q := by
    obtain ⟨hvN,hvn⟩ := Finset.mem_sdiff.mp hv
    exact Classical.byContradiction (fun hvq => hvn (Finset.mem_erase.mpr ⟨hvq,hvN⟩))
  subst v
  obtain ⟨s,_,_,_,hother⟩ := euler_exponents ho hN
  have hsq : q = s := by
    by_contra hn
    have := Nat.odd_iff.mp he
    have := Nat.even_iff.mp (hother q hn)
    omega
  have hq := Nat.prime_of_mem_primeFactors hqN
  have hpos := isSquare_of_dvd_sigma_even (Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp hp).2) hq
    (hother p (hsq ▸ (Finset.mem_erase.mp hp).1)) ep.2.2
  have hneg := nonsquare_of_dvd_succ hq (Nat.prime_of_mem_primeFactors hr) (by omega) hr4 hd
  exact ⟨p,hp,r,hrem,fun h => hneg (h ▸ hpos),ep,hpos,er,hneg⟩

end OddPerfect
