module

public import OddPerfect.ChenChenIndex
public import OddPerfect.OddGeometricSquares
public import OddPerfect.IndexPowerLength
import Mathlib.Algebra.Order.Ring.Abs

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- An even power leaves a cofactor with prime-power divisor sum. The
neighbouring Euler prime is exactly twice the cofactor square minus one. -/
theorem even_prime_power_cofactor_split {q p m u : ℕ} (hq : q.Prime) (hp : p.Prime)
    (hm : Odd m) (hpo : Odd p) (hu : 0<u)
    (hl : sigma 1 (m^2)=q*p^(2*u)) (hr : sigma 1 q*p^(2*u)=2*m^2) :
    ∃ s : ℕ, Odd s ∧ p.Coprime s ∧ m=p^u*s ∧ sigma 1 (p^(2*u))=q ∧
      q+1=2*s^2 ∧ sigma 1 (s^2)=p^(2*u) := by
  obtain ⟨he,hσ⟩ := prime_power_index_data_at_one hq hm.pos hp hpo (by omega : 0<2*u) hl hr
  have huval : m.factorization p=u := by omega
  let s := ordCompl[p] m
  have hc : p.Coprime s := Nat.coprime_ordCompl hp hm.pos.ne'
  have hms := (Nat.ordProj_mul_ordCompl_eq_self m p).symm
  change m=p^(m.factorization p)*s at hms
  rw [huval] at hms
  have hso : Odd s := hm.of_dvd_nat (hms ▸ dvd_mul_left s _)
  have hsquare : m^2=p^(2*u)*s^2 := by rw [hms,mul_pow,←pow_mul,Nat.mul_comm u 2]
  have hσq : sigma 1 q=q+1 := by
    rw [←pow_one q,sigma_one_apply_prime_pow hq]
    simp only [sum_range_succ,sum_range_zero,pow_zero,pow_one,zero_add]
    omega
  rw [hσq,hsquare] at hr
  have hplus : q+1=2*s^2 := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hp.pos)
    (show p^(2*u)*(q+1)=p^(2*u)*(2*s^2) by simpa only [mul_assoc,mul_comm,mul_left_comm] using hr)
  rw [hsquare,isMultiplicative_sigma.map_mul_of_coprime ((hc.pow_left _).pow_right 2),hσ] at hl
  exact ⟨s,hso,hc,hms,hσ,hplus,Nat.eq_of_mul_eq_mul_left hq.pos hl⟩

/-- A prime-power divisor sum of even exponent is one modulo the successor
of its base, by pairing its nonconstant terms. -/
theorem sigma_even_power_mod_succ {p : ℕ} (hp : p.Prime) (k : ℕ) :
    sigma 1 (p^(2*k)) ≡ 1 [MOD p+1] := by
  rw [sigma_one_apply_prime_pow hp,sum_range_succ']
  simp only [pow_succ',←Finset.mul_sum,pow_zero]
  simpa only [mul_zero,zero_add] using ((succ_dvd_sum_even p k).modEq_zero_nat.mul_left p).add_right 1

/-- Every source in the remaining cofactor sends an odd power of the
index prime. The unique geometric-square exception would require 3|s
and p=11, contradicting the value of q+1 modulo three. -/
theorem even_index_source_odd_power {q p s u r : ℕ} (hp : p.Prime) (hs : Odd s)
    (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2) (hσs : sigma 1 (s^2)=p^(2*u))
    (hr : r ∈ s.primeFactors) :
    ∃ β : ℕ, Odd β ∧ sigma 1 (r^(2*s.factorization r))=p^β := by
  obtain ⟨hrp,hrs,_⟩ := Nat.mem_primeFactors.mp hr
  have he := (hrp.dvd_iff_one_le_factorization hs.pos.ne').mp hrs
  let e := 2*s.factorization r
  have hepos : 0<e := by dsimp [e]; omega
  have heven : Even e := ⟨s.factorization r,by simp [e,two_mul]⟩
  have hleft : sigma 1 (s^2)=p^(2*u)*1 := by simpa using hσs
  have hdiv : sigma 1 (r^e) ∣ p^(2*u) := by
    simpa only [mul_one] using cofactor_component_sum_dvd_index_product hs.pos hrp (e:=e) rfl hepos hleft
  obtain ⟨β,_,heq⟩ := (Nat.dvd_prime_pow hp).mp hdiv
  refine ⟨β,(Nat.even_or_odd β).resolve_left ?_,heq⟩
  rintro ⟨k,hk⟩
  have hsq : IsSquare (sigma 1 (r^e)) := ⟨p^k,by rw [heq,hk,pow_add]⟩
  obtain ⟨hr3,he4⟩ := (sigma_prime_pow_isSquare_iff_of_even hrp hepos heven).mp hsq
  have hβpos : 0<β := by
    by_contra! h
    rw [show β=0 by omega,pow_zero] at heq
    have := self_lt_sigma_of_one_lt (one_lt_pow₀ hrp.one_lt hepos.ne')
    have := one_lt_pow₀ hrp.one_lt hepos.ne'
    omega
  have hsmall : (121:ℕ)=p^β := by
    rw [←heq,hr3,he4,sigma_one_apply_prime_pow Nat.prime_three]
    decide
  have hpd : p ∣ (11:ℕ)^2 := (by decide : (11:ℕ)^2=121) ▸ (hsmall ▸ dvd_pow_self p hβpos.ne')
  have hp11 := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11)).mp (hp.dvd_of_dvd_pow hpd)
  have hq3 := (sigma_even_power_mod_succ hp u)
  rw [hσq,hp11] at hq3
  have hq1 := hq3.of_dvd (by decide : 3 ∣ 11+1)
  change q%3=1 at hq1
  have hs3 : 3 ∣ q+1 := hplus ▸ dvd_mul_of_dvd_right (dvd_pow (hr3 ▸ hrs) (by decide : 2≠0)) _
  omega

/-- If the index prime is three modulo four, every prime in the remaining
cofactor must be one modulo four. -/
theorem even_index_sources_one_mod_four {q p s u r : ℕ} (hp : p.Prime) (hp3 : p%4=3)
    (hs : Odd s) (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2)
    (hσs : sigma 1 (s^2)=p^(2*u)) (hr : r ∈ s.primeFactors) : r%4=1 := by
  obtain ⟨β,hβ,hout⟩ := even_index_source_odd_power hp hs hσq hplus hσs hr
  have hro := Nat.odd_iff.mp (hs.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr))
  by_contra! h
  have h4 : 4 ∣ r+1 := by omega
  have hg := (sigma_even_power_mod_succ (Nat.prime_of_mem_primeFactors hr) (s.factorization r)).of_dvd h4
  rw [hout] at hg
  have hp2 : p^2 ≡ 1 [MOD 4] := by change p^2%4=1; rw [pow_two,Nat.mul_mod,hp3]
  obtain ⟨k,hk⟩ := hβ
  have hb : p^β ≡ p [MOD 4] := by
    simpa only [show β=2*k+1 by omega,pow_succ,pow_mul,one_pow,one_mul] using
      (show p^(2*k+1) ≡ 1*p [MOD 4] by simpa only [pow_succ,pow_mul,one_pow] using (hp2.pow k).mul_right p)
  have hv := hb.symm.trans hg
  change p%4=1 at hv
  omega

end OddPerfect
