module

public import OddPerfect.EvenIndexRoots
public import OddPerfect.OddPrimePowerReturn
import Mathlib.Algebra.Order.Ring.Abs

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- A positive Nagell–Ljunggren solution with odd prime base, odd prime
length, prime-power right-hand base and odd prime right-hand exponent. -/
@[expose] def HasOddPrimeRepunitPower : Prop :=
  ∃ x n v c l : ℕ, x.Prime ∧ Odd x ∧ n.Prime ∧ 2<n ∧ v.Prime ∧
    0<c ∧ l.Prime ∧ Odd l ∧ geometricBlock x n=(v^c)^l

/-- The single-copy sources form a subset of the prime divisors of u+1.
Thus some cofactor source in an even prime-power index must itself be a
nontrivial odd perfect power, even without a lower bound on the support. -/
theorem exists_nontrivial_repunit_power_of_even_index {q p s u : ℕ}
    (hp : p.Prime) (hs : Odd s) (hu : 0<u) (hσq : sigma 1 (p^(2*u))=q)
    (hplus : q+1=2*s^2) (hσs : sigma 1 (s^2)=p^(2*u)) : HasOddPrimeRepunitPower := by
  let f (r : ℕ) := sigma 1 (r^(2*s.factorization r))
  let v (r : ℕ) := (f r).factorization p
  obtain ⟨hsum,hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  change ∑ r ∈ s.primeFactors,v r=2*u at hsum
  have hsource : ∃ r ∈ s.primeFactors, v r≠1 := by
    by_contra! hone
    have hcard : s.primeFactors.card=2*u := by
      simpa only [Finset.sum_congr rfl hone,Finset.sum_const,smul_eq_mul,mul_one] using hsum
    have hsub : s.primeFactors ⊆ Finset.Icc 2 (u+1) := by
      intro r hr
      have hrp := Nat.prime_of_mem_primeFactors hr
      have hrs := Nat.dvd_of_mem_primeFactors hr
      have hro := hs.of_dvd_nat hrs
      obtain ⟨_,hout⟩ := hparts r hr
      change f r=p^(v r) at hout
      rw [hone r hr,pow_one] at hout
      have hp1 : p ≡ 1 [MOD r] := by
        change sigma 1 (r^(2*s.factorization r))=p at hout
        rw [←hout]
        simpa [Nat.ModEq,Nat.mod_eq_of_lt hrp.one_lt] using sigma_prime_pow_mod_self hrp (2*s.factorization r)
      have hmod := sigma_modEq_of_one hp hp1 (2*u)
      rw [hσq] at hmod
      have hqp : r ∣ q+1 := hplus ▸ dvd_mul_of_dvd_right (dvd_pow hrs (by decide : 2≠0)) _
      have hdiv : r ∣ 2*(u+1) := (by omega : 2*u+1+1=2*(u+1)) ▸ ((hmod.add_right 1).dvd_iff dvd_rfl).mp hqp
      exact Finset.mem_Icc.mpr ⟨hrp.two_le,Nat.le_of_dvd (by omega)
        ((Nat.coprime_two_right.mpr hro).dvd_of_dvd_mul_left hdiv)⟩
    have hrd := Finset.card_le_card hsub
    rw [hcard,Nat.card_Icc] at hrd
    omega
  obtain ⟨r,hr,hne⟩ := hsource
  obtain ⟨hvo,hout⟩ := hparts r hr
  change Odd (v r) at hvo
  change f r=p^(v r) at hout
  obtain ⟨l,hl,hld⟩ := Nat.exists_prime_and_dvd hne
  have hlo := hvo.of_dvd_nat hld
  obtain ⟨c,hc⟩ := hld
  have hcpos : 0<c := by by_contra! h; rw [show c=0 by omega,mul_zero] at hc; have := hvo.pos; omega
  obtain ⟨hrp,hrs,_⟩ := Nat.mem_primeFactors.mp hr
  have hro := hs.of_dvd_nat hrs
  let e := 2*s.factorization r
  have he := (hrp.dvd_iff_one_le_factorization hs.pos.ne').mp hrs
  have hepos : 0<e := by dsimp [e]; omega
  change sigma 1 (r^e)=p^(v r) at hout
  have hprime := prime_length_of_pure_even_component hrp hro hp hepos ⟨s.factorization r,by simp [e,two_mul]⟩ hout.dvd
  refine ⟨r,e+1,p,c,l,hrp,hro,hprime,by dsimp [e]; omega,hp,hcpos,hl,hlo,?_⟩
  calc geometricBlock r (e+1)=sigma 1 (r^e) := (sigma_one_apply_prime_pow hrp).symm
       _ = p^(v r) := hout
       _ = (p^c)^l := by rw [hc,pow_mul']

/-- A prime-power index of any exact component would give a positive
solution of the Nagell–Ljunggren equation outside the three standard
positive solutions. -/
theorem odd_prime_repunit_power_of_prime_power_component {N q a b i p j : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0<a)
    (hform : N=q^a*b) (hqb : ¬q ∣ b) (hl : sigma 1 b=q^a*i)
    (hr : sigma 1 (q^a)*i=2*b) (hp : p.Prime) (hj : 0<j) (hi : i=p^j) :
    HasOddPrimeRepunitPower := by
  subst i
  have hj1 : j≠1 := by
    rintro rfl
    simp only [pow_one] at hl hr
    exact component_index_not_prime hN ho hq ha hform hqb hl hr hp
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b _)
  have hp2 : p≠2 := by
    rintro rfl
    have h4 : 4 ∣ 2*b := hr ▸ (pow_dvd_pow 2 (by omega : 2≤j)).trans (dvd_mul_left _ _)
    have := hbo.not_two_dvd_nat
    omega
  have hpo := hp.odd_of_ne_two hp2
  obtain ⟨m,hq4,ha4,hqm,rfl⟩ := euler_form_of_odd_component_index hN ho hq ha hform hqb hl hr hpo.pow
  have hmo := ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2≠0)) _)
  have heq : sigma 1 (m^2)/q^a=p^j := by rw [hl,Nat.mul_div_cancel_left _ (Nat.pow_pos hq.pos)]
  rcases Nat.even_or_odd j with ⟨u,hu⟩|hodd
  · have hj2 : j=2*u := by omega
    have hup : 0<u := by omega
    rw [hj2] at hl hr
    obtain ⟨ha1,_⟩ := even_prime_power_index_eq_selected_sigma hN ho hq ha hform hqb hl hr hp hup rfl
    rw [ha1,pow_one] at hl hr
    obtain ⟨s,hso,_,_,hσq,hplus,hσs⟩ := even_prime_power_cofactor_split hq hp hmo hpo hup hl hr
    exact exists_nontrivial_repunit_power_of_even_index hp hso hup hσq hplus hσs
  · obtain ⟨_,_,_,hjp,_,_⟩ := odd_prime_power_euler_index_constraints hN ho hq hq4 ha4 hqm hform hp hodd heq
    obtain ⟨hd,hd8,_,_,_,hσ⟩ := odd_prime_power_euler_index_return hN ho hq hq4 ha4 hqm hform hp hodd heq
    refine ⟨p,j+2,q,1,(a+1)/2,hp,hpo,hjp,by omega,hq,by decide,hd,Nat.odd_iff.mpr (by omega),?_⟩
    rw [pow_one,←hσ,sigma_one_apply_prime_pow hp]
    rfl

/-- Conditional reduction to the classical positive-solution
classification. The classification itself is an explicit hypothesis. -/
theorem no_prime_power_component_index_of_nagell_ljunggren_classification
    (hclass : ∀ x n y l : ℕ, 1<x → 2<n → 1<y → 1<l → geometricBlock x n=y^l →
      (x=3 ∧ n=5 ∧ y=11 ∧ l=2) ∨ (x=7 ∧ n=4 ∧ y=20 ∧ l=2) ∨ (x=18 ∧ n=3 ∧ y=7 ∧ l=3))
    {N q a b i p j : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0<a)
    (hform : N=q^a*b) (hqb : ¬q ∣ b) (hl : sigma 1 b=q^a*i)
    (hr : sigma 1 (q^a)*i=2*b) (hp : p.Prime) (hj : 0<j) : i≠p^j := by
  intro hi
  obtain ⟨x,n,v,c,l,hx,hxo,_,hn,hv,hc,hL,hlo,heq⟩ :=
    odd_prime_repunit_power_of_prime_power_component hN ho hq ha hform hqb hl hr hp hj hi
  have hlist := hclass x n (v^c) l hx.one_lt hn (one_lt_pow₀ hv.one_lt hc.ne') hL.one_lt heq
  have := Nat.odd_iff.mp hxo
  have := Nat.odd_iff.mp hlo
  rcases hlist with h | h | h <;> omega

end OddPerfect
