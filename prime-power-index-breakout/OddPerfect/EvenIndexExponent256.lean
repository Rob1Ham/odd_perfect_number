module

public import OddPerfect.EvenIndexCostTables
public import OddPerfect.EvenIndexThreeModFour
public import OddPerfect.OddIndexExponentScreen
import Mathlib.Algebra.Order.Ring.Abs

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- With nonexceptional sources charged to their return multiplicities,
none of the four remaining multiples of sixteen can reach abundancy two. -/
theorem small_even_index_cost_contradiction {N q p s u : ℕ}
    (hN : N.Perfect) (hq : q.Prime) (hp : p.Prime) (hpo : Odd p)
    (hs : Odd s) (hu : 0<u) (hcop : p.Coprime s) (hqm : ¬q∣p^u*s)
    (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2)
    (hσs : sigma 1 (s^2)=p^(2*u)) (hform : N=q*(p^u*s)^2)
    (hj : 2*u=96 ∨ 2*u=112 ∨ 2*u=192 ∨ 2*u=240) : False := by
  let E := indexCostExceptions (2*u)
  let K := indexCost (2*u)
  have hp61 := sixty_one_le_small_even_index_base hp hpo hq hu (by omega) (.inr hj) hσq hplus
  have hq3721 : 3721≤q := by
    have h := self_lt_sigma_of_one_lt (one_lt_pow₀ hp.one_lt (by omega : 2*u≠0))
    rw [hσq] at h
    exact ((Nat.pow_le_pow_left hp61 2).trans (Nat.pow_le_pow_right hp.pos (by omega : 2≤2*u))).trans h.le
  have hE : ∀ r ∈ E, 1<r := by
    dsimp only [E]
    rcases hj with h|h|h|h <;> rw [h] <;> decide +kernel
  have hk : 0<K := by
    dsimp [K,indexCost]
    split_ifs <;> decide
  have env := even_index_abundancy_envelope hp hs hσq hplus hσs hk E hE (fun r hr he β hv hout hle =>
    low_even_index_source_cost hp hs hr he hv hle hj hσq hplus hout)
  have hqn : q ∉ (p^u*s).primeFactors := fun h => hqm (Nat.dvd_of_mem_primeFactors h)
  have hpn : p ∉ s.primeFactors := fun h => (hp.coprime_iff_not_dvd.mp hcop) (Nat.dvd_of_mem_primeFactors h)
  have hm : p^u*s≠0 := mul_ne_zero (pow_ne_zero _ hp.ne_zero) hs.pos.ne'
  have hNprod : (∏ r ∈ N.primeFactors,primeAbundancyLimit r) =
      primeAbundancyLimit p*primeAbundancyLimit q*(∏ r ∈ s.primeFactors,primeAbundancyLimit r) := by
    rw [hform,Nat.primeFactors_mul hq.ne_zero (pow_ne_zero 2 hm),Nat.primeFactors_pow _ (by decide : 2≠0),
      hq.primeFactors,Finset.singleton_union,Finset.prod_insert hqn,
      Nat.primeFactors_mul (pow_ne_zero _ hp.ne_zero) hs.pos.ne',Nat.primeFactors_pow p hu.ne',hp.primeFactors,
      Finset.singleton_union,Finset.prod_insert hpn]
    ring
  have non (r : ℕ) : 0≤primeAbundancyLimit r := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have pq := mul_le_mul (primeAbundancyLimit_antitone (by decide : 1<61) hp61)
    (primeAbundancyLimit_antitone (by decide : 1<3721) hq3721) (non q) (non 61)
  have total := mul_le_mul pq env (Finset.prod_nonneg (fun r _ => non r)) (mul_nonneg (non _) (non _))
  rw [←hNprod] at total
  exact (two_lt_prod_primeAbundancyLimit hN).not_ge (total.trans (low_even_index_envelope_values hj).le)

/-- Every prime-power index of any exact component of an odd perfect
number has exponent at least 256. -/
theorem component_prime_power_index_exponent_ge_256 {N q a b i p j : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0<a)
    (hform : N=q^a*b) (hqb : ¬q∣b) (hl : sigma 1 b=q^a*i) (hr : sigma 1 (q^a)*i=2*b)
    (hp : p.Prime) (hj : 0<j) (hi : i=p^j) : 256≤j := by
  by_contra! hcut
  have he := (Nat.even_or_odd j).resolve_right (fun h =>
    IndexObstruction.component_index_ne_odd_prime_power_below_36207 hN ho hq ha hform hqb hl hr hp h (by omega) hi)
  obtain ⟨u,hu'⟩ := he
  have hj2 : j=2*u := by omega
  have hu : 0<u := by omega
  have h66 := component_prime_power_index_exponent_ge_sixty_six hN ho hq ha hform hqb hl hr hp hj hi
  rw [hj2] at hi
  obtain ⟨ha1,hσq⟩ := even_prime_power_index_eq_selected_sigma hN ho hq ha hform hqb hl hr hp hu hi
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b _)
  have hp2 : p≠2 := by
    rintro rfl
    have h4 : 4 ∣ 2*b := hr ▸ hi ▸ (pow_dvd_pow 2 (by omega : 2≤2*u)).trans (dvd_mul_left _ _)
    have := hbo.not_two_dvd_nat
    omega
  have hpo := hp.odd_of_ne_two hp2
  obtain ⟨m,_,_,hqm,rfl⟩ := euler_form_of_odd_component_index hN ho hq ha hform hqb hl hr (hi ▸ hpo.pow)
  have hmo := ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2≠0)) _)
  rw [ha1,pow_one] at hform hl hr
  rw [hi] at hl hr
  obtain ⟨s,hs,hcop,hms,_,hplus,hσs⟩ := even_prime_power_cofactor_split hq hp hmo hpo hu hl hr
  by_cases h1 : p%4=1
  · have h16 := sixteen_dvd_even_index_exponent_of_one_mod_four hp h1 hs hσq hplus
    have hlen := prime_length_of_prime_sigma hp (by omega : 0<2*u) (hσq ▸ hq)
    have cert : ∀v : Fin 256, 66≤v.val → 16 ∣ v.val → (v.val+1).Prime →
        v.val=96 ∨ v.val=112 ∨ v.val=192 ∨ v.val=240 := by decide +kernel
    have H := cert ⟨2*u,by omega⟩ (by change 66≤2*u; omega) h16 hlen
    exact small_even_index_cost_contradiction hN hq hp hpo hs hu hcop (hms ▸ hqm) hσq hplus hσs (hms ▸ hform) H
  · have h3 : p%4=3 := by have := Nat.odd_iff.mp hpo; omega
    have := even_index_exponent_ge_256_of_three_mod_four hN hq hp hpo h3 hs hu hσq hplus hσs (hms ▸ hform)
    omega

end OddPerfect
