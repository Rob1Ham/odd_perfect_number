module

public import OddPerfect.OddPrimePowerIndex
public import OddPerfect.GeometricNonSquare
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Order.Ring.Abs

public section
namespace OddPerfect
open ArithmeticFunction

/-- In a return between two primes at Euler length twice an odd prime,
the odd outgoing exponent equals that half-length if it is below the full
length. This also fixes both the order and a residue of the geometric length. -/
theorem pure_return_at_twice_prime_length {q a p e d β : ℕ}
    (hq : q.Prime) (hp : p.Prime) (hpo : Odd p) (hp4 : p%4=1)
    (hd : d.Prime) (hdo : Odd d) (hlen : a+1=2*d) (hplus : d ∣ q+1)
    (he : 0<e) (hβ : 0<β) (hbound : β≤a) (hσ : sigma 1 (p^e)=q^β)
    (hback : p ∣ sigma 1 (q^a)) :
    β=d ∧ orderOf (q : ZMod p)=d ∧ d ∣ p-1 ∧ d ∣ e+2 := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact d.Prime := ⟨hd⟩
  have hβo : Odd β := (Nat.even_or_odd β).resolve_left (by
    rintro ⟨c,hc⟩
    exact sigma_prime_pow_not_square_of_one_mod_four hp hp4 he
      ⟨q^c,by rw [hσ,hc,pow_add]⟩)
  have hself : q^β ≡ 1 [MOD p] := by
    rw [←hσ]
    simpa [Nat.ModEq,Nat.mod_eq_of_lt hp.one_lt] using sigma_prime_pow_mod_self hp e
  have hpow : (q:ZMod p)^β=1 := by
    simpa only [Nat.cast_pow,Nat.cast_one] using (ZMod.natCast_eq_natCast_iff _ _ p).mpr hself
  have hnonzero : (q:ZMod p)≠0 := by intro hz; rw [hz,zero_pow hβ.ne'] at hpow; exact zero_ne_one hpow
  have hone : (q:ZMod p)≠1 := by
    intro h
    rw [sigma_one_apply,dvd_sum_divisors_prime_pow_iff hq hp,ite_eq_left h,hlen] at hback
    have hpd := (Nat.coprime_two_right.mpr hpo).dvd_of_dvd_mul_left hback
    have heq := (Nat.prime_dvd_prime_iff_eq hp hd).mp hpd
    have hplusp : p ∣ q+1 := heq ▸ hplus
    have hc : q ≡ 1 [MOD p] := (ZMod.natCast_eq_natCast_iff q 1 p).mp (by simpa using h)
    have hp2 : p ∣ 2 := ((hc.add_right 1).dvd_iff dvd_rfl).mp hplusp
    exact hpo.not_two_dvd_nat (((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2) ▸ dvd_rfl)
  let o := orderOf (q:ZMod p)
  have hoβ : o ∣ β := orderOf_dvd_of_pow_eq_one hpow
  have hoo := hβo.of_dvd_nat hoβ
  rw [sigma_one_apply,dvd_sum_divisors_prime_pow_iff hq hp,ite_eq_right hone,hlen] at hback
  have hod : o ∣ d := (Nat.coprime_two_right.mpr hoo).dvd_of_dvd_mul_left hback
  have hoeq := (Nat.dvd_prime hd).mp hod |>.resolve_left (fun h => hone (orderOf_eq_one_iff.mp h))
  have hdpred := ZMod.orderOf_dvd_card_sub_one hnonzero
  change o ∣ p-1 at hdpred
  rw [hoeq] at hoβ hdpred
  have hβd : β=d := by
    obtain ⟨c,hc⟩ := hoβ
    have hc1 : c≤1 := by
      by_contra! h
      have := Nat.mul_le_mul_left d (show 2≤c by omega)
      omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc1 with hc0|hc'
    · rw [hc0,mul_zero] at hc; omega
    · simpa [hc'] using hc
  have hp1 : p ≡ 1 [MOD d] := ((Nat.modEq_iff_dvd' hp.one_le).mpr hdpred).symm
  have hqm : (q:ZMod d) = -1 := by
    have hz := (ZMod.natCast_eq_zero_iff (q+1) d).mpr hplus
    simpa [Nat.cast_add,eq_neg_iff_add_eq_zero] using hz
  have hret := (sigma_modEq_of_one hp hp1 e).symm
  rw [hσ,hβd] at hret
  have hneg : ((e+1:ℕ):ZMod d) = -1 := by
    have hz := (ZMod.natCast_eq_natCast_iff _ _ d).mpr hret
    rwa [Nat.cast_pow,hqm,hdo.neg_one_pow] at hz
  refine ⟨hβd,hoeq,hdpred,(ZMod.natCast_eq_zero_iff (e+2) d).mp ?_⟩
  change (((e+1)+1:ℕ):ZMod d)=0
  rw [Nat.cast_add,Nat.cast_one,hneg,neg_add_cancel]

/-- The exceptional odd prime-power index forces one specific feedback
equation. Its index exponent plus three contains the prime Euler half-length. -/
theorem odd_prime_power_euler_index_return {N q a m p j : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1)
    (hqm : ¬q ∣ m) (hform : N=q^a*m^2) (hp : p.Prime) (hj : Odd j)
    (hi : sigma 1 (m^2)/q^a=p^j) :
    let d := (a+1)/2
    d.Prime ∧ d%8=1 ∧ d ∣ j+3 ∧ d ∣ p-1 ∧ orderOf (q:ZMod p)=d ∧
      sigma 1 (p^(j+1))=q^d := by
  obtain ⟨ha,hp8,he,_,_,β,hβ,hσ⟩ :=
    odd_prime_power_euler_index_constraints hN ho hq hq4 ha4 hqm hform hp hj hi
  obtain ⟨k,hk⟩ := hj
  have hshape : sigma 1 (m^2)/q^a=p*(p^k)^2 := by rw [hi,show j=k*2+1 by omega,pow_succ,pow_mul,mul_comm]
  obtain ⟨hd,hd8,hq16,w,hw⟩ := prime_mul_square_index_forces_exceptional_prime_length
    hN ho hq hq4 ha4 ha hqm hform (Or.inr hp) hshape
  let d := (a+1)/2
  have hplus : d ∣ q+1 := by
    refine ⟨2*w^2,?_⟩
    calc q+1 = 2*((q+1)/2) := by omega
         _ = _ := by rw [hw]; dsimp [d]; ring
  have hm : Odd m := ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2≠0)) _)
  obtain ⟨i,_,hl,hr,_⟩ := exists_component_index hN hq hform (fun h => hqm (hq.dvd_of_dvd_pow h))
  have heqi : i=p^j := by simpa only [hl,Nat.mul_div_cancel_left _ (Nat.pow_pos hq.pos)] using hi
  subst i
  have hpo : Odd p := Nat.odd_iff.mpr (by omega)
  have hv := index_prime_return_valuation hp hpo hq hm.pos (Nat.pow_pos hp.pos) hr
  rw [hp.factorization_pow,Finsupp.single_eq_same,he] at hv
  have hback : p ∣ sigma 1 (q^a) := by
    by_contra h
    rw [Nat.factorization_eq_zero_of_not_dvd h] at hv
    omega
  have hsub := cofactor_component_sum_dvd_index_product hm.pos hp he (by omega : 0<j+1) hl
  have hself : ¬p ∣ sigma 1 (p^(j+1)) := by rw [Nat.dvd_iff_mod_eq_zero,sigma_prime_pow_mod_self hp]; decide
  have hβa := ((hp.coprime_iff_not_dvd.mpr hself).symm.pow_right j).dvd_of_dvd_mul_right hsub
  rw [hσ,Nat.pow_dvd_pow_iff_le_right hq.one_lt] at hβa
  obtain ⟨hβd,hoq,hdp,hdj⟩ := pure_return_at_twice_prime_length hq hp hpo (by omega) hd
    (Nat.odd_iff.mpr (by omega))
    (by omega) hplus (by omega : 0<j+1) hβ hβa hσ hback
  exact ⟨hd,hd8,hdj,hdp,hoq,hβd ▸ hσ⟩

end OddPerfect
