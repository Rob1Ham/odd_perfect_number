module

public import OddPerfect.IndexSieveCore
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.FieldTheory.Finite.Basic

public section

namespace OddPerfect.IndexSieve

open ArithmeticFunction Finset

/-- Candidate lengths contributed by a fixed index prime. The least positive
period is checked by modular exponentiation over its finite range. -/
@[expose] def feedingLengths (p r : ℕ) : Finset ℕ :=
  if p%r = 1 then {r}
  else (Finset.Icc 2 r).filter fun d : ℕ => Odd d ∧ p^d%r=1 ∧
    ∀ j : Fin d, 0 < (j:ℕ) → p^(j:ℕ)%r ≠ 1

/-- A pure source uses its actual index valuation and the half-divisor bound.
An impure source contributes a geometric block at one of its feeding lengths. -/
@[expose] def blockLengths (i p H : ℕ) : Finset ℕ :=
  (((Finset.Icc (max 2 (i.factorization p)) (i.factorization p+H)).filter Even).image (·+1)) ∪
  i.primeFactors.biUnion (feedingLengths p)

/-- Every index-prime divisor of a component sum supplies one of the listed
lengths as a divisor of the component length. -/
theorem exists_feeding_length {p r e : ℕ} (hp : p.Prime) (hr : r.Prime) (he : Even e)
    (hd : r ∣ sigma 1 (p^e)) : ∃ d ∈ feedingLengths p r, 0<d ∧ d ∣ e+1 := by
  let : Fact r.Prime := ⟨hr⟩
  rw [sigma_one_apply,dvd_sum_divisors_prime_pow_iff hp hr] at hd
  have cast_one : (p : ZMod r)=1 ↔ p%r=1 := by
    simpa only [Nat.cast_one,Nat.mod_eq_of_lt hr.one_lt] using ZMod.natCast_eq_natCast_iff' p 1 r
  by_cases hp1 : p%r=1
  · simp only [cast_one.mpr hp1,ite_true] at hd
    exact ⟨r,by simp [feedingLengths,hp1],hr.pos,hd⟩
  · have hn := mt cast_one.mp hp1
    simp only [hn,ite_false] at hd
    let d := orderOf (p : ZMod r)
    have hpos : 0<d := Nat.pos_of_dvd_of_pos hd (by omega)
    have hd1 : d ≠ 1 := fun h => hn (orderOf_eq_one_iff.mp h)
    have hnz : (p : ZMod r) ≠ 0 := by intro h; rw [h,orderOf_zero,zero_dvd_iff] at hd; omega
    have hle := Nat.le_of_dvd (by have := hr.one_lt; omega : 0<r-1) (ZMod.orderOf_dvd_card_sub_one hnz)
    change d ≤ r-1 at hle
    have hmod (j : ℕ) : (p : ZMod r)^j=1 ↔ p^j%r=1 := by
      simpa only [Nat.cast_pow,Nat.cast_one,Nat.mod_eq_of_lt hr.one_lt] using ZMod.natCast_eq_natCast_iff' (p^j) 1 r
    have hleast := (orderOf_eq_iff hpos).mp (rfl : orderOf (p : ZMod r)=d)
    refine ⟨d,?_,hpos,hd⟩
    simp only [feedingLengths,hp1,ite_false,Finset.mem_filter,Finset.mem_Icc]
    refine ⟨⟨by omega,by omega⟩,(show Odd (e+1) from Nat.odd_iff.mpr (by have := Nat.even_iff.mp he; omega)).of_dvd_nat hd,(hmod d).mp hleast.1,?_⟩
    intro j hj h
    exact hleast.2 j j.isLt hj ((hmod j).mpr h)

/-- At each index prime a computed candidate block divides the outgoing
Euler product. This bounds the finite search without bounding the Euler prime. -/
theorem exists_block {q a m i p H : ℕ} (hq : q.Prime) (ha : Odd a) (hm : 0<m)
    (hio : Odd i) (hpI : p ∈ i.primeFactors) (hH : (a+1).divisors.card/2 ≤ H)
    (hl : sigma 1 (m^2)=q^a*i) (hr : sigma 1 (q^a)*i=2*m^2) :
    ∃ d ∈ blockLengths i p H, 0<d ∧ (∑ j ∈ Finset.range d, p^j) ∣ q^a*i := by
  let e := 2*m.factorization p
  have hp := Nat.prime_of_mem_primeFactors hpI
  have hpi := Nat.dvd_of_mem_primeFactors hpI
  have hpo := hio.of_dvd_nat hpi
  have hv := index_prime_return_valuation hp hpo hq hm hio.pos hr
  have hcp := (hp.dvd_iff_one_le_factorization hio.pos.ne').mp hpi
  have he : 0<e := by dsimp [e]; omega
  have heven : Even e := ⟨m.factorization p,by simp [e,two_mul]⟩
  have hout := cofactor_component_sum_dvd_index_product hm hp (e:=e) rfl he hl
  by_cases hcop : (sigma 1 (p^e)).Coprime i
  · obtain ⟨β,_,hβ⟩ := (Nat.dvd_prime_pow hq).mp (hcop.dvd_of_dvd_mul_right hout)
    have hbound := twice_pure_exponent_excess_le_length_divisors hp hpo hq ha hm hio.pos he hβ hr
    refine ⟨e+1,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_,?_⟩,heven⟩,rfl⟩),by omega,?_⟩
    · have := Nat.even_iff.mp heven
      apply max_le <;> dsimp [e] at * <;> omega
    · dsimp [e]; omega
    · simpa only [← sigma_one_apply_prime_pow hp] using hout
  · obtain ⟨r,hpr,hrσ,hri⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    obtain ⟨d,hd,hdpos,hdlen⟩ := exists_feeding_length hp hpr heven hrσ
    refine ⟨d,Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r,Nat.mem_primeFactors.mpr ⟨hpr,hri,hio.pos.ne'⟩,hd⟩),hdpos,?_⟩
    have hblock := (sigma_dvd_of_length_dvd hp hdpos hdlen).trans hout
    rwa [sigma_one_apply_prime_pow hp,show d-1+1=d by omega] at hblock

end OddPerfect.IndexSieve
