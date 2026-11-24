module

public import OddPerfect.ExceptionalIndexResidue
public import OddPerfect.Hirakawa
import all OddPerfect.EulerSquareClass
import all OddPerfect.GeometricSquareClass
import all OddPerfect.ChenLuo
import Mathlib.FieldTheory.Finite.Basic

public section
namespace OddPerfect
open ArithmeticFunction

/-- If the squarefree part of an Euler index consists of one prime l, the
Euler prime has exact order (a+1)/2 modulo l, and l is 1 modulo eight times that half-length. -/
theorem prime_mul_square_euler_index_order {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1)
    (ha : 1<a) (hqm : ¬ q∣m) (hform : N=q^a*m^2) (hl : l=1 ∨ l.Prime) (hs : sigma 1 (m^2)/q^a=l*t^2) :
    let d := (a+1)/2
    l.Prime ∧ orderOf (q:ZMod l)=d ∧ l ≡ 1 [MOD 8*d] := by
  let d := (a+1)/2
  obtain ⟨hd,hd8,hq16,w,hw⟩ := prime_mul_square_index_forces_exceptional_prime_length hN ho hq hq4 ha4 ha hqm hform hl hs
  have hlp : l.Prime := hl.resolve_left (by
    rintro rfl
    exact euler_index_not_square_of_exponent_gt_one hN ho hq hq4 ha4 ha hqm hform ⟨t,by simpa [pow_two] using hs⟩)
  have hm := (ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _)).pos
  obtain ⟨i,hi,hleft,hright,_⟩ := exists_component_index hN hq hform (fun h => hqm (hq.dvd_of_dvd_pow h))
  have hshape := hs
  rw [hleft,Nat.mul_div_cancel_left i (pow_pos hq.pos _)] at hshape
  let A := geometricBlock q d
  let B := (q^d+1)/2
  obtain ⟨hb,hc,_,_,_⟩ := euler_half_blocks hq hq4 ha4 hright
  change m^2=A*B*i at hb
  change A.Coprime B at hc
  have hn : ¬IsSquare A := geometricBlock_not_square_of_prime_one_mod_four hq hq4 hd.one_lt
  obtain ⟨r,hr,hv⟩ := exists_odd_valuation_of_nonsquare hn
  have hrdiv : r∣A := Nat.dvd_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hv.pos.ne')
  have hrI := odd_valuation_transfer hm.ne' hb hv (prime_not_dvd_other hr hc hrdiv)
  have ht : t≠0 := by rintro rfl; simp at hshape; omega
  have hrl : r=l := by
    by_contra hne
    have hdiv : ¬r∣l := fun h => hne ((Nat.prime_dvd_prime_iff_eq hr hlp).mp h)
    rw [hshape,Nat.factorization_mul hlp.ne_zero (pow_ne_zero _ ht),Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hdiv,zero_add,Nat.factorization_pow,Finsupp.smul_apply,
      smul_eq_mul,Nat.odd_iff] at hrI
    omega
  subst r
  let : Fact l.Prime := ⟨hlp⟩
  have hpow := pow_eq_one_of_dvd_block hrdiv
  have hqsucc : d∣q+1 := by
    have h2 : q+1=2*d*w^2 := by rw [mul_assoc,←hw]; omega
    rw [h2]
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have hld : l≠d := by
    intro hh
    have hq1 := hpow
    change (q:ZMod l)^d=1 at hq1
    rw [←hh,ZMod.pow_card] at hq1
    have hz := (ZMod.natCast_eq_zero_iff (q+1) l).mpr (hh ▸ hqsucc)
    rw [Nat.cast_add,Nat.cast_one,hq1] at hz
    have htwo : l∣2 := (ZMod.natCast_eq_zero_iff 2 l).mp (by norm_num at hz ⊢; exact hz)
    have hh2 := (Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).mp htwo
    omega
  have hqne : (q:ZMod l)≠1 := by
    intro hh
    have hz := cast_geometricBlock_zero hrdiv
    simp [hh] at hz
    exact hld ((Nat.prime_dvd_prime_iff_eq hlp hd).mp ((ZMod.natCast_eq_zero_iff _ _).mp hz))
  have horder : orderOf (q:ZMod l)=d :=
    ((Nat.dvd_prime hd).mp (orderOf_dvd_iff_pow_eq_one.mpr hpow)).resolve_left (fun hh => hqne (orderOf_eq_one_iff.mp hh))
  have h0 : (q:ZMod l)≠0 := by
    intro hh
    change (q:ZMod l)^d=1 at hpow
    rw [hh,zero_pow (show d≠0 from hd.ne_zero)] at hpow
    exact zero_ne_one hpow
  have hlen : d∣l-1 := horder ▸ ZMod.orderOf_dvd_card_sub_one h0
  have hI8 := prime_mul_square_euler_index_one_mod_eight hN ho hq hq4 ha4 ha hqm hform l t hl hs
  rw [hs] at hI8
  have htodd := (Nat.odd_iff.mpr (show (l*t^2)%2=1 by omega)).of_dvd_nat
    (dvd_mul_of_dvd_right (dvd_pow_self t (by decide : 2≠0)) l)
  have hres := (square_mod_eight htodd).mul_left l
  have hl8 : l%8=1 := by
    change l*t^2%8=l*1%8 at hres
    simpa using hres.symm.trans hI8
  have h8 : 8∣l-1 := (Nat.modEq_iff_dvd' hlp.one_le).mp (show (1:ℕ) ≡ l [MOD 8] from (show l ≡ 1 [MOD 8] from hl8).symm)
  have hdo : Odd d := Nat.odd_iff.mpr (by change d%8=1 at hd8; omega)
  have hcop : Nat.Coprime 8 d := hdo.coprime_two_left.pow_left 3
  exact ⟨hlp,horder,((Nat.modEq_iff_dvd' hlp.one_le).mpr (hcop.mul_dvd_of_dvd_of_dvd h8 hlen)).symm⟩

end OddPerfect
