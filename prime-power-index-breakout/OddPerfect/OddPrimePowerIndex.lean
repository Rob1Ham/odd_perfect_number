module

public import OddPerfect.ExceptionalIndexResidue
public import OddPerfect.IndexPowerLength
import Mathlib.Algebra.Order.Ring.Abs

public section
namespace OddPerfect
open ArithmeticFunction Finset

private theorem odd_power_one_mod_eight {p j : ℕ} (hpo : Odd p) (hjo : Odd j)
    (hpj : p^j%8=1) : p%8=1 := by
  have hp2 := Nat.odd_iff.mp hpo
  have hp8 : p%8=1 ∨ p%8=3 ∨ p%8=5 ∨ p%8=7 := by omega
  have hsq : p^2 ≡ 1 [MOD 8] := by
    change p^2%8=1
    rw [pow_two,Nat.mul_mod]
    rcases hp8 with h|h|h|h <;> simp [h]
  obtain ⟨k,hk⟩ := hjo
  have hpow : p^j ≡ p [MOD 8] := by
    simpa only [show j=2*k+1 by omega,pow_succ,pow_mul,one_pow,one_mul] using
      (show p^(2*k+1) ≡ 1*p [MOD 8] by simpa only [pow_succ,pow_mul,one_pow] using (hsq.pow k).mul_right p)
  exact hpow.symm.trans (show p^j ≡ 1 [MOD 8] from hpj)

private theorem sigma_four_block {p : ℕ} (hp : p.Prime) (hp8 : p%8=1) (k : ℕ) :
    sigma 1 (p^(4*k)) ≡ 4*k+1 [MOD 16] := by
  have hp16 : p%16=1 ∨ p%16=9 := by omega
  have h2 : p^2 ≡ 1 [MOD 16] := by
    change p^2%16=1
    rw [pow_two,Nat.mul_mod]
    rcases hp16 with h|h <;> simp [h]
  have h3 : p^3 ≡ p [MOD 16] := by simpa only [pow_succ p 2,one_mul] using h2.mul_right p
  have hblock : 1+p+p^2+p^3 ≡ 4 [MOD 16] := by
    calc 1+p+p^2+p^3 ≡ 1+p+1+p [MOD 16] := ((Nat.ModEq.refl _).add h2).add h3
         _ ≡ 4 [MOD 16] := by change (1+p+1+p)%16=4; omega
  have hp4 (v : ℕ) : p^(4*v) ≡ 1 [MOD 16] := by
    simpa only [show 4*v=2*(2*v) by omega,pow_mul,one_pow] using
      (show (p^2)^(2*v) ≡ 1^(2*v) [MOD 16] from h2.pow _)
  have hsum (v : ℕ) : (∑ i ∈ range (4*v),p^i) ≡ 4*v [MOD 16] := by
    induction v with
    | zero => simp [Nat.ModEq]
    | succ v ih =>
      rw [Nat.mul_succ]
      have hstep : (∑ i ∈ range (4*v+4),p^i) =
          (∑ i ∈ range (4*v),p^i) + p^(4*v)*(1+p+p^2+p^3) := by
        simp only [Finset.sum_range_succ,pow_succ]
        ring
      rw [hstep]
      simpa only [one_mul] using ih.add ((hp4 v).mul hblock)
  rw [sigma_one_apply_prime_pow hp,Finset.sum_range_succ]
  exact (hsum k).add (hp4 k)

/-- If an Euler index equals an odd power of one prime, its cofactor
exponent at that prime is exactly one larger than the index exponent.
Its successor is prime, and the component exponent is divisible by sixteen. -/
theorem odd_prime_power_euler_index_constraints {N q a m p j : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1)
    (hqm : ¬q ∣ m) (hform : N=q^a*m^2) (hp : p.Prime) (hj : Odd j)
    (hi : sigma 1 (m^2)/q^a=p^j) :
    1<a ∧ p%8=1 ∧ 2*m.factorization p=j+1 ∧ (j+2).Prime ∧ 16 ∣ j+1 ∧
      ∃ β : ℕ, 0<β ∧ sigma 1 (p^(j+1))=q^β := by
  obtain ⟨i,hio,_,hl,hr⟩ := (euler_component_index_bound hN ho hq hq4 ha4 hqm hform).2
  have heqi : i=p^j := by simpa only [hl,Nat.mul_div_cancel_left _ (Nat.pow_pos hq.pos)] using hi
  subst i
  have hpo := hio.of_dvd_nat (dvd_pow_self p hj.pos.ne')
  have hm : Odd m := ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2≠0)) _)
  have ha : 1<a := by
    by_contra! h
    have ha1 : a=1 := by omega
    rw [ha1,pow_one] at hl hr
    have := Nat.even_iff.mp (even_prime_power_index_at_euler_exponent_one hq hm.pos hp hpo hj.pos hl hr)
    have := Nat.odd_iff.mp hj
    omega
  obtain ⟨k,hk⟩ := hj
  have hshape : sigma 1 (m^2)/q^a=p*(p^k)^2 := by rw [hi,show j=k*2+1 by omega,pow_succ,pow_mul,mul_comm]
  obtain ⟨hd,hd8,hq16,_⟩ := prime_mul_square_index_forces_exceptional_prime_length
    hN ho hq hq4 ha4 ha hqm hform (Or.inr hp) hshape
  let d := (a+1)/2
  have hdo : Odd d := Nat.odd_iff.mpr (by change (a+1)/2%2=1; omega)
  have hcount : (a+1).divisors.card=4 := by
    have htwo : a+1=2*d := by dsimp [d]; omega
    rw [htwo,(Nat.coprime_two_right.mpr hdo).symm.card_divisors_mul,
      show (2:ℕ).divisors.card=2 by decide,hd.divisors]
    simp [hd.ne_one.symm]
  have hres := prime_mul_square_euler_index_one_mod_eight hN ho hq hq4 ha4 ha hqm hform p (p^k) (Or.inr hp) hshape
  rw [hi] at hres
  have hp8 := odd_power_one_mod_eight hpo ⟨k,hk⟩ hres
  obtain ⟨hle,hge,hprime,β,hβ,hpure⟩ := prime_power_index_component_constraints
    hq (Nat.odd_iff.mpr (by omega)) hm.pos hp hpo (by omega : 0<j) hl hr
  rw [hcount] at hge
  have heq : 2*m.factorization p=j+1 := by omega
  rw [heq] at hprime hpure
  have hq8 : q ≡ 1 [MOD 8] := by change q%8=1; omega
  have hqS : q ≡ 1 [MOD 16] := hq16
  have h8 := (sigma_modEq_of_one hp (show p ≡ 1 [MOD 8] from hp8) (j+1)).symm
  rw [hpure] at h8
  have hj8 : j+1+1 ≡ 1 [MOD 8] := by simpa only [one_pow] using h8.trans (hq8.pow β)
  change (j+1+1)%8=1 at hj8
  obtain ⟨v,hv⟩ : 4 ∣ j+1 := by omega
  have h16 := (sigma_four_block hp hp8 v).symm
  rw [←hv,hpure] at h16
  have hj16 : j+1+1 ≡ 1 [MOD 16] := by simpa only [one_pow] using h16.trans (hqS.pow β)
  change (j+1+1)%16=1 at hj16
  exact ⟨ha,hp8,heq,hprime,by omega,β,hβ,hpure⟩

end OddPerfect
