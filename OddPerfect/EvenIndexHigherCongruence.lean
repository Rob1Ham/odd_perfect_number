module

public import OddPerfect.EvenIndexTruncation
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.LinearCombination

public section
namespace OddPerfect
open ArithmeticFunction Finset ReturnLift

/-- All orders of the cofactor radical lift. Both truncations are
nonnegative integers, and the two sides have opposite parity for k>0. -/
theorem even_index_radical_higher_congruence {q p s u k : ℕ} (hp : p.Prime) (hpo : Odd p)
    (hs : Odd s) (hk : k≤2*u) (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2)
    (hσs : sigma 1 (s^2)=p^(2*u)) :
    let P := s.primeFactors.prod id
    let v := sourceMultiplicity s p
    2^k*P+truncatedSum s.primeFactors v k 1 p ≡ truncatedSum s.primeFactors v k 0 p [MOD p^(k+1)] := by
  let R := ZMod (p^(k+1))
  let x : R := p
  let P := s.primeFactors.prod id
  let S := s.primeFactors
  let v := sourceMultiplicity s p
  let D := ∏ r ∈ S,(1+((r-1:ℕ):R)*x^(v r))
  let H := ∑ a ∈ range (k+1),x^a*2^(k-a)
  have hx : x^(k+1)=0 := by change (p:ZMod (p^(k+1)))^(k+1)=0; rw [←Nat.cast_pow,ZMod.natCast_self]
  have hxn : x^(2*u+1)=0 := by rw [show 2*u+1=k+1+(2*u-k) by omega,pow_add,hx,zero_mul]
  have hq : (q:R)*(x-1)=x^(2*u+1)-1 := by
    rw [←hσq,sigma_one_apply_prime_pow hp,Nat.cast_sum]
    simpa only [Nat.cast_pow] using geom_sum_mul x (2*u+1)
  have hQ := congrArg (fun n:ℕ => (n:R)) hplus
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hQ
  have hD := congrArg (fun n:ℕ => (n:R)) (even_index_cofactor_radical_identity hp hs hσq hplus hσs)
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_prod,Nat.cast_add,Nat.cast_one] at hD
  have hP : (P : R) = ∏ i ∈ S, ((id i : ℕ) : R) := Nat.cast_prod _ _
  rw [← hP] at hD
  change (s:R)^2*(P:R)=D at hD
  have balance : (P:R)*(2-x)=2*(1-x)*D := by
    rw [hxn] at hq
    rw [←hD]
    linear_combination (P:R)*hq+(P:R)*(1-x)*hQ
  have hH : H*(2-x)=2*2^k := by
    have h := geom_sum₂_mul x (2:R) (k+1)
    simp only [Nat.add_sub_cancel,hx,zero_sub,pow_succ] at h
    change _*(2-x)=_
    dsimp only [H]
    linear_combination -h
  have h0 := cast_truncatedSum p k 0 S v
  have h1 := cast_truncatedSum p k 1 S v
  change (truncatedSum S v k 0 p:R)=x^0*(D*H) at h0
  change (truncatedSum S v k 1 p:R)=x^1*(D*H) at h1
  have hmod : 2*(2^k*P+truncatedSum S v k 1 p) ≡ 2*truncatedSum S v k 0 p [MOD p^(k+1)] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    push_cast
    change (2:R)*(2^k*(P:R)+(truncatedSum S v k 1 p:R))=2*(truncatedSum S v k 0 p:R)
    rw [h0,h1,pow_zero,one_mul,pow_one]
    linear_combination H*balance-(P:R)*hH
  exact Nat.ModEq.cancel_left_of_coprime (Nat.coprime_two_right.mpr hpo.pow) hmod

end OddPerfect
