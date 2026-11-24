module

public import OddPerfect.ExceptionalLength
import Mathlib.FieldTheory.Finite.Basic

public section
namespace OddPerfect
open Finset ArithmeticFunction

/-- A nonresidue of the prime exponent forces a divisor of the auxiliary
root when the exponent reduces to one modulo the residue-field group order. -/
theorem dvd_root_of_exceptional_nonresidue {q s w y r : ℕ} (hr : r.Prime) (hro : Odd r)
    (hs : 0<s) (hper : r-1∣s-1) (hn : ¬IsSquare (s:ZMod r))
    (hq : q+1=2*s*w^2) (hy : q^s+1=2*y^2) : r∣w := by
  let : Fact r.Prime := ⟨hr⟩
  obtain ⟨k,hk⟩ := hper
  have he : s=1+(r-1)*k := by omega
  have hp : (q:ZMod r)^s=q := by
    by_cases hz : (q:ZMod r)=0
    · simp [hz,zero_pow hs.ne']
    rw [he,pow_add,pow_one,pow_mul,ZMod.pow_card_sub_one_eq_one hz,one_pow,mul_one]
  have hq' : (q:ZMod r)+1=2*s*w^2 := by simpa using congrArg (fun n : ℕ => (n:ZMod r)) hq
  have hy' : (q:ZMod r)^s+1=2*y^2 := by simpa using congrArg (fun n : ℕ => (n:ZMod r)) hy
  rw [hp] at hy'
  have htwo : (2:ZMod r) ≠ 0 := by
    intro H
    have hd : r∣2 := (ZMod.natCast_eq_zero_iff 2 r).mp H
    exact hro.not_two_dvd_nat (((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hd) ▸ dvd_rfl)
  have hz : (s:ZMod r)*w^2=y^2 := by
    apply mul_left_cancel₀ htwo
    simpa [mul_assoc] using hq'.symm.trans hy'
  by_contra hnot
  have hw : (w:ZMod r)≠0 := fun H => hnot ((ZMod.natCast_eq_zero_iff _ _).mp H)
  apply hn
  refine ⟨(y:ZMod r)/w,?_⟩
  rw [div_mul_div_comm]
  exact (eq_div_iff (mul_ne_zero hw hw)).mpr (by simpa [pow_two,mul_assoc] using hz)

/-- In a putative prime-times-square Euler index the product of any selected
nonresidue primes has its square dividing the full odd perfect number. -/
theorem exceptional_nonresidue_product_sq_dvd
    {N q a m l t : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (ha : 1<a) (hqm : ¬q∣m) (hform : N=q^a*m^2)
    (hl : l=1 ∨ l.Prime) (hs : sigma 1 (m^2)/q^a=l*t^2)
    (R : Finset ℕ) (hR : ∀ r∈R, r.Prime ∧ Odd r ∧ r-1∣(a+1)/2-1 ∧ ¬IsSquare (((a+1)/2:ℕ):ZMod r)) :
    (∏ r∈R,r)^2 ∣ N := by
  let d := (a+1)/2
  obtain ⟨hd,_,hq16,w,hw⟩ := prime_mul_square_index_forces_exceptional_prime_length hN ho hq hq4 ha4 ha hqm hform hl hs
  have hB : IsSquare ((q^d+1)/2) := Classical.byContradiction
    (fun h => euler_index_ne_prime_mul_square_of_second_block hN ho hq hq4 ha4 ha hqm hform h l t hl hs)
  obtain ⟨y,hy⟩ := hB
  have hdouble : q+1=2*d*w^2 := by rw [mul_assoc,←hw]; omega
  have hpodd : q^d%2=1 := by simpa [Nat.ModEq] using (show q ≡ 1 [MOD 2] from (by change q%2=1; omega)).pow d
  have hsquare : q^d+1=2*y^2 := by rw [pow_two]; omega
  have hw0 : w≠0 := by rintro rfl; simp at hdouble
  have hsub : R⊆w.primeFactors := by
    intro r hr
    obtain ⟨hrp,hro,hlen,hns⟩ := hR r hr
    exact Nat.mem_primeFactors.mpr ⟨hrp,dvd_root_of_exceptional_nonresidue hrp hro hd.pos hlen hns hdouble hsquare,hw0⟩
  have hprod : (∏ r∈R,r)∣w := (prod_dvd_prod_of_subset R w.primeFactors id hsub).trans (Nat.prod_primeFactors_dvd w)
  obtain ⟨i,_,_,hright,_⟩ := exists_component_index hN hq hform (fun h => hqm (hq.dvd_of_dvd_pow h))
  have hdv : 2*w^2∣q+1 := by rw [hdouble]; exact ⟨d,by ring⟩
  have hdv' := hdv.trans (succ_dvd_sigma_prime_pow hq (Nat.odd_iff.mpr (by omega : a%2=1)))
  have hret : 2*w^2∣2*m^2 := hright ▸ dvd_mul_of_dvd_left hdv' i
  exact (pow_dvd_pow_of_dvd hprod 2).trans (((Nat.dvd_of_mul_dvd_mul_left (by decide : 0<(2:ℕ))) hret).trans
    (hform ▸ dvd_mul_left _ _))

/-- An abundant product of forced prime squares rules out the proposed index
for every Euler prime and every size of the number. -/
theorem euler_index_exclusion_of_abundant_nonresidues
    {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (ha : 1<a) (hqm : ¬q∣m) (hform : N=q^a*m^2)
    (R : Finset ℕ) (hR : ∀ r∈R, r.Prime ∧ Odd r ∧ r-1∣(a+1)/2-1 ∧ ¬IsSquare (((a+1)/2:ℕ):ZMod r))
    (hab : ((∏ r∈R,r)^2).Abundant) (l t : ℕ) (hl : l=1 ∨ l.Prime) :
    sigma 1 (m^2)/q^a≠l*t^2 := by
  intro heq
  have hdiv := exceptional_nonresidue_product_sq_dvd hN ho hq hq4 ha4 ha hqm hform hl heq R hR
  exact (Nat.perfect_iff_not_abundant_and_not_deficient hN.2.ne).mp hN |>.1 (hab.of_dvd hdiv hN.2.ne')

private def five_forced_primes : Finset ℕ := {3,5,17,23,89}

private theorem five_forced_abundant : ((∏ r∈five_forced_primes,r)^2).Abundant := by
  rw [Nat.abundant_iff_sum_divisors,←sigma_one_apply]
  have hprod : (∏ r∈five_forced_primes,r)^2=3^2*(5^2*(17^2*(23^2*89^2))) := by decide
  rw [hprod]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by decide : (3^2).Coprime (5^2*(17^2*(23^2*89^2)))),
    isMultiplicative_sigma.map_mul_of_coprime (by decide : (5^2).Coprime (17^2*(23^2*89^2))),
    isMultiplicative_sigma.map_mul_of_coprime (by decide : (17^2).Coprime (23^2*89^2)),
    isMultiplicative_sigma.map_mul_of_coprime (by decide : (23^2).Coprime (89^2))]
  rw [sigma_one_apply_prime_pow Nat.prime_three,sigma_one_apply_prime_pow (by decide : Nat.Prime 5),
    sigma_one_apply_prime_pow (by decide : Nat.Prime 17),sigma_one_apply_prime_pow (by decide : Nat.Prime 23),
    sigma_one_apply_prime_pow (by decide : Nat.Prime 89)]
  decide

private theorem nonresidue_data {r : ℕ} (hr : r∈five_forced_primes) :
    r.Prime ∧ Odd r ∧ r∣91869360 ∧ r-1∣91869360 ∧ r-1∣23057-1 ∧ ¬IsSquare ((23057:ℕ):ZMod r) := by
  rcases (show r=3 ∨ r=5 ∨ r=17 ∨ r=23 ∨ r=89 by simpa [five_forced_primes] using hr) with
    rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- One entire residue class of Euler half-lengths is excluded for a square
or prime-times-square index, without an upper bound on the Euler prime. -/
theorem euler_index_exclusion_half_length_23057
    {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (ha : 1<a) (hqm : ¬q∣m) (hform : N=q^a*m^2)
    (hres : ((a+1)/2)%91869360=23057) (l t : ℕ) (hl : l=1 ∨ l.Prime) :
    sigma 1 (m^2)/q^a≠l*t^2 := by
  apply euler_index_exclusion_of_abundant_nonresidues hN ho hq hq4 ha4 ha hqm hform
    five_forced_primes _ five_forced_abundant l t hl
  intro r hr
  obtain ⟨hp,hro,hrM,hpM,hlen,hz⟩ := nonresidue_data hr
  let d := (a+1)/2
  have hmod : d ≡ 23057 [MOD 91869360] := hres
  have hrmod := hmod.of_dvd hrM
  have hpred := hmod.of_dvd hpM
  have h1 : 1 ≡ 23057 [MOD r-1] := (Nat.modEq_iff_dvd' (by decide : 1≤23057)).mpr hlen
  have hcon : 1 ≡ d [MOD r-1] := h1.trans hpred.symm
  have hz' : (d:ZMod r)=(23057:ℕ) := (ZMod.natCast_eq_natCast_iff' ..).mpr hrmod
  refine ⟨hp,hro,(Nat.modEq_iff_dvd' (by dsimp [d]; omega : 1≤d)).mp hcon,?_⟩
  change ¬IsSquare (d:ZMod r)
  rwa [hz']

end OddPerfect
