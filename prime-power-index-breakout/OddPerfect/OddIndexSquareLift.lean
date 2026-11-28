module

public import OddPerfect.OddPrimePowerReturn
public import OddPerfect.GeometricSquareClass
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.LinearCombination

public section
namespace OddPerfect
open Finset ArithmeticFunction

private theorem pow_one_add_of_square_zero {R : Type*} [CommRing R] {u : R} (hu : u^2=0) (n : ℕ) :
    (1+u)^n=1+(n:R)*u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,ih,Nat.cast_succ]
    linear_combination (n:R)*hu

private theorem twice_geometric_linear {R : Type*} [CommRing R] {u : R} (hu : u^2=0) (n : ℕ) :
    2*(∑ j∈range n, (1+u)^j)=2*(n:R)+((n:R)^2-n)*u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ,mul_add,ih,pow_one_add_of_square_zero hu,Nat.cast_succ]
    ring

private theorem zero_product_mod_sq {a b d : ℕ} (ha : d∣a) (hb : d∣b) :
    (a:ZMod (d^2))*b=0 := by
  rw [←Nat.cast_mul]
  apply (ZMod.natCast_eq_zero_iff (a*b) _).mpr
  simpa [pow_two] using Nat.mul_dvd_mul ha hb

/-- The first-order term in a repunit determines its base modulo d²
when its length is minus one modulo d and its value is minus one modulo d². -/
theorem geometric_minus_one_sq_lift {p n d : ℕ} (hp : 1≤p) (ho : Odd d)
    (hpd : d∣p-1) (hnd : d∣n+1) (hval : d^2∣geometricBlock p n+1) :
    d^2∣p+n := by
  let R := ZMod (d^2)
  let u : R := (p:R)-1
  have hu : u=((p-1:ℕ):R) := by simp [u,Nat.cast_sub hp]
  have hu2 : u^2=0 := by rw [pow_two,hu]; exact zero_product_mod_sq hpd hpd
  have hnu : ((n:R)+1)*u=0 := by rw [hu]; simpa using zero_product_mod_sq hnd hpd
  have hpone : (p:R)=1+u := by rw [hu,Nat.cast_sub hp]; simp
  have hg : ((geometricBlock p n:ℕ):R)=(∑ j∈range n,(1+u)^j) := by simp [geometricBlock,hpone]
  have hpw : ((geometricBlock p n:ℕ):R) = -1 := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa using (ZMod.natCast_eq_zero_iff _ _).mpr hval
  have hsum := twice_geometric_linear hu2 n
  rw [←hg,hpw] at hsum
  have hy : (2:R)*((p:R)+n)=0 := by
    rw [hpone]
    linear_combination -hsum - ((n:R)-2)*hnu
  have hdiv : d^2 ∣ 2*(p+n) := (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using hy)
  exact ho.pow.coprime_two_right.dvd_of_dvd_mul_left hdiv

/-- A first-order expansion of a repunit perfect power at an odd
divisor shared by its base minus one, its length plus one and its root
plus one. No prime hypothesis is needed for the expansion. -/
theorem half_length_sq_dvd_base_add_geometric_length {p q n d : ℕ} (hp : 1≤p) (ho : Odd d)
    (hpd : d∣p-1) (hnd : d∣n+1) (hqd : d∣q+1) (hpow : geometricBlock p n=q^d) :
    d^2∣p+n := by
  let R := ZMod (d^2)
  let v : R := (q:R)+1
  have hv2 : v^2=0 := by rw [pow_two]; simpa [v] using zero_product_mod_sq hqd hqd
  have hdv : (d:R)*v=0 := by simpa [v] using zero_product_mod_sq (dvd_refl d) hqd
  have hqp : (q:R)^d = -1 := by
    have hvneg : (-v)^2=0 := by simpa using hv2
    have hqeq : (q:R)= -(1+(-v)) := by dsimp only [v]; ring
    rw [hqeq,ho.neg_pow,pow_one_add_of_square_zero hvneg,mul_neg,hdv]
    simp
  apply geometric_minus_one_sq_lift hp ho hpd hnd
  rw [hpow]
  exact (ZMod.natCast_eq_zero_iff _ _).mp (by simp [hqp])

/-- For an odd prime-power Euler index at exponent j the feedback
half-length d occurs twice in p+j+2. -/
theorem odd_prime_power_index_half_length_sq_dvd {N q a m p j : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1)
    (hqm : ¬q∣m) (hform : N=q^a*m^2) (hp : p.Prime) (hj : Odd j)
    (hi : sigma 1 (m^2)/q^a=p^j) : ((a+1)/2)^2∣p+(j+2) := by
  obtain ⟨hd,hd8,hdj,hdp,_,hret⟩ :=
    odd_prime_power_euler_index_return hN ho hq hq4 ha4 hqm hform hp hj hi
  obtain ⟨ha,_,_,_,_,_⟩ := odd_prime_power_euler_index_constraints hN ho hq hq4 ha4 hqm hform hp hj hi
  obtain ⟨k,hk⟩ := hj
  have hshape : sigma 1 (m^2)/q^a=p*(p^k)^2 := by rw [hi,show j=k*2+1 by omega,pow_succ,pow_mul,mul_comm]
  obtain ⟨_,_,hq16,w,hw⟩ := prime_mul_square_index_forces_exceptional_prime_length
    hN ho hq hq4 ha4 ha hqm hform (Or.inr hp) hshape
  let d := (a+1)/2
  have hqd : d∣q+1 := by
    refine ⟨2*w^2,?_⟩
    calc q+1 = 2*((q+1)/2) := by omega
         _ = _ := by rw [hw]; dsimp [d]; ring
  have hG : geometricBlock p (j+2)=q^d := by
    rw [sigma_one_apply_prime_pow hp] at hret
    exact hret
  exact half_length_sq_dvd_base_add_geometric_length hp.one_le
    (Nat.odd_iff.mpr (by omega)) hdp hdj hqd hG

end OddPerfect
