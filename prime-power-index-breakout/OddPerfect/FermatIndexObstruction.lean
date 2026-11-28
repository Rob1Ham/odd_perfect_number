module

public import OddPerfect.AlternatingPell
public import OddPerfect.FermatIndexSquareClass
public import OddPerfect.ChenChenIndex
public import OddPerfect.LengthMatching
import all OddPerfect.EulerSquareClass
import all OddPerfect.GeometricSquareClass
import Mathlib.Algebra.Order.Ring.Abs

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- For an odd exponent, a square half-sum forces its exponent to be
coprime to the predecessor of the base. -/
theorem coprime_exponent_pred_of_square_half_sum {q d : ℕ}
    (hq : 1<q) (hq8 : q%8=1) (hd : Odd d) (hs : IsSquare ((q^d+1)/2)) :
    d.Coprime (q-1) := by
  apply Nat.coprime_of_dvd
  intro r hr hrd hrq
  have hro := hd.of_dvd_nat hrd
  obtain ⟨k,hk⟩ := hrd
  have hkpos : k≠0 := by rintro rfl; rw [mul_zero] at hk; have := hd.pos; omega
  have hpow : q^d=(q^k)^r := by rw [hk,mul_comm r k,pow_mul]
  rw [hpow] at hs
  let x := q^k
  have hx : 1<x := one_lt_pow₀ hq hkpos
  have hx8 : x%8=1 := by
    simpa [x,Nat.ModEq] using (show q ≡ 1 [MOD 8] from hq8).pow k
  have hq1 : q ≡ 1 [MOD r] := ((Nat.modEq_iff_dvd' hq.le).mpr hrq).symm
  have hx1 : x ≡ 1 [MOD r] := by simpa [x] using hq1.pow k
  have hnot : ¬r ∣ x+1 := by
    intro h
    have h2 := ((hx1.add_right 1).dvd_iff dvd_rfl).mp h
    exact hro.not_two_dvd_nat (((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2) ▸ dvd_rfl)
  exact half_sum_not_square_of_alternatingBlock hx8 hr hro
    (alternatingBlock_not_square hx hr.one_lt hro) (Or.inr hnot) hs

/-- Above Euler exponent one, at least one prime with odd index valuation
does not divide the Euler prime's predecessor. -/
theorem odd_valuation_index_prime_not_dvd_euler_pred {q a m i : ℕ}
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (ha : 1<a) (hm : 0<m)
    (hright : sigma 1 (q^a)*i=2*m^2) :
    ∃ p : ℕ, p.Prime ∧ Odd (i.factorization p) ∧ ¬p ∣ q-1 := by
  let d := (a+1)/2
  let A := geometricBlock q d
  let B := (q^d+1)/2
  have hdo : Odd d := Nat.odd_iff.mpr (by dsimp [d]; omega)
  have hd1 : 1<d := by dsimp [d]; omega
  obtain ⟨hbal,hcop,_,hB,hB4⟩ := euler_half_blocks hq hq4 ha4 hright
  change m^2=A*B*i at hbal
  change A.Coprime B at hcop
  change 2*B=q^d+1 at hB
  change B%4=((q+1)/2)%4 at hB4
  have hbo : Odd B := Nat.odd_iff.mpr (by omega)
  have hn := geometricBlock_not_square_of_prime_one_mod_four hq hq4 hd1
  obtain ⟨r,hr,hv⟩ := exists_odd_valuation_of_nonsquare hn
  change Odd (A.factorization r) at hv
  have hAr : r ∣ A := Nat.dvd_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hv.pos.ne')
  have hri := odd_valuation_transfer hm.ne' hbal hv (prime_not_dvd_other hr hcop hAr)
  by_cases hdiv : r ∣ q-1
  · have hq1 : q ≡ 1 [MOD r] := ((Nat.modEq_iff_dvd' hq.one_le).mpr hdiv).symm
    have hcz : (q:ZMod r)=1 := by simpa using (ZMod.natCast_eq_natCast_iff q 1 r).mpr hq1
    have hzero := cast_geometricBlock_zero hAr
    simp [hcz] at hzero
    have hrd := (ZMod.natCast_eq_zero_iff d r).mp hzero
    have hns : ¬IsSquare B := by
      intro hs
      have hq16 : q%16=1 := by
        by_contra h
        exact half_pow_succ_not_square_of_mod_sixteen hq4 hdo h hs
      have hc := coprime_exponent_pred_of_square_half_sum hq.one_lt (by omega) hdo hs
      exact hr.not_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd hrd hdiv)
    obtain ⟨p,hp,hvB⟩ := exists_odd_valuation_of_nonsquare hns
    have hpb : p ∣ B := Nat.dvd_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hvB.pos.ne')
    have him := odd_valuation_transfer hm.ne' (show m^2=B*A*i by rw [mul_comm B A,hbal]) hvB
      (prime_not_dvd_other hp hcop.symm hpb)
    refine ⟨p,hp,him,?_⟩
    intro h
    have hqP : q ≡ 1 [MOD p] := ((Nat.modEq_iff_dvd' hq.one_le).mpr h).symm
    have h2 := (((hqP.pow d).add_right 1).dvd_iff dvd_rfl).mp (show p ∣ q^d+1 from hB ▸ hpb.trans (dvd_mul_left _ _))
    simp only [one_pow] at h2
    exact (hbo.of_dvd_nat hpb).not_two_dvd_nat (((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2) ▸ dvd_rfl)
  · exact ⟨r,hr,hri,hdiv⟩

/-- Each prime factor of the Euler half-length divides the predecessor
of an odd-valuation index prime. An odd length factor prevents that
predecessor from being a power of two. -/
theorem half_length_prime_forces_nonfermat_index_prime {N q a m i l : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1)
    (hqm : ¬q ∣ m) (hform : N=q^a*m^2) (hl : l.Prime) (hd : l ∣ (a+1)/2)
    (hi : sigma 1 (m^2)/q^a=i) :
    ∃ p ∈ i.primeFactors, Odd (i.factorization p) ∧ l ∣ p-1 ∧ ∀ k : ℕ, p-1≠2^k := by
  let d := (a+1)/2
  have hlo := (show Odd d from Nat.odd_iff.mpr (by dsimp [d]; omega)).of_dvd_nat hd
  have H := euler_half_length_dvd_large_index_predecessors hN ho hq hq4 ha4 hqm hform
  rw [hi] at H
  obtain ⟨p,hp,hpred⟩ := (hl.prime.dvd_finsetProd_iff _).mp
    ((hd.trans (dvd_mul_right d (neutralLengthPart q d))).trans H)
  have hv := mem_oddValuationPrimes.mp (Finset.mem_filter.mp hp).1
  refine ⟨p,Finsupp.mem_support_iff.mpr hv.pos.ne',hv,hpred,?_⟩
  intro k hk
  rw [hk] at hpred
  exact hlo.not_two_dvd_nat (((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow hpred)) ▸ dvd_rfl)

/-- The index of every exact component with odd index contains some
prime whose predecessor is not a power of two. This includes every
Euler component index, independently of its prime multiplicities. -/
theorem exists_nonfermat_prime_of_odd_component_index {N q a b i : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0<a)
    (hform : N=q^a*b) (hqb : ¬q ∣ b) (hl : sigma 1 b=q^a*i)
    (hr : sigma 1 (q^a)*i=2*b) (hio : Odd i) :
    ∃ p ∈ i.primeFactors, ∀ k : ℕ, p-1≠2^k := by
  by_contra! hall
  obtain ⟨m,hq4,ha4,hqm,rfl⟩ := euler_form_of_odd_component_index hN ho hq ha hform hqb hl hr hio
  have hao : Odd a := Nat.odd_iff.mpr (by omega)
  have hcount := prime_count_le_length_of_fermat_supported_index ho hq hao hqm hform hl hr hall
  have := five_le_distinct_prime_factor_count ho hN
  obtain ⟨l,hL,hd⟩ := Nat.exists_prime_and_dvd (show (a+1)/2≠1 by omega)
  have hi : sigma 1 (m^2)/q^a=i := by rw [hl,Nat.mul_div_cancel_left _ (Nat.pow_pos hq.pos)]
  obtain ⟨p,hp,_,_,hnot⟩ := half_length_prime_forces_nonfermat_index_prime hN ho hq hq4 ha4 hqm hform hL hd hi
  obtain ⟨k,hk⟩ := hall p hp
  exact hnot k hk

/-- No positive power of a prime with power-of-two predecessor can be
the index of any exact component of an odd perfect number. -/
theorem component_index_ne_fermat_prime_power {N q a b i p j k : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0<a)
    (hform : N=q^a*b) (hqb : ¬q ∣ b) (hl : sigma 1 b=q^a*i)
    (hr : sigma 1 (q^a)*i=2*b) (hp : p.Prime) (hj : 0<j) (hk : p-1=2^k) :
    i≠p^j := by
  intro hi
  have hj1 : j≠1 := by
    rintro rfl
    rw [pow_one] at hi
    exact component_index_not_prime hN ho hq ha hform hqb hl hr (hi ▸ hp)
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b _)
  have hp2 : p≠2 := by
    rintro rfl
    have h4 : 4 ∣ 2*b := hr ▸ hi ▸ (pow_dvd_pow 2 (by omega : 2≤j)).trans (dvd_mul_left _ _)
    have := hbo.not_two_dvd_nat
    omega
  have hio : Odd i := hi ▸ (hp.odd_of_ne_two hp2).pow
  obtain ⟨r,hr,hrk⟩ := exists_nonfermat_prime_of_odd_component_index hN ho hq ha hform hqb hl hr hio
  rw [hi,Nat.primeFactors_pow p hj.ne',hp.primeFactors,Finset.mem_singleton] at hr
  exact hrk k (hr ▸ hk)

end OddPerfect
