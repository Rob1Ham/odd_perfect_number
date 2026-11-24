module

public import OddPerfect.EvenIndexRadicalLift
import Mathlib.Algebra.Order.Ring.Abs

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- Complete cofactor data at an even prime-power index, including the
minimum number of distinct returning primes. -/
theorem even_prime_power_component_cofactor_data {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0<a)
    (hform : N=q^a*b) (hqb : ¬q ∣ b) (hl : sigma 1 b=q^a*i)
    (hr : sigma 1 (q^a)*i=2*b) (hp : p.Prime) (hu : 0<u) (hi : i=p^(2*u)) :
    Odd p ∧ ∃ s, Odd s ∧ p.Coprime s ∧ ¬q∣p^u*s ∧ N=q*(p^u*s)^2 ∧
      sigma 1 (p^(2*u))=q ∧ q+1=2*s^2 ∧ sigma 1 (s^2)=p^(2*u) ∧ 4≤s.primeFactors.card := by
  obtain ⟨ha1,hσ⟩ := even_prime_power_index_eq_selected_sigma hN ho hq ha hform hqb hl hr hp hu hi
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
  have hn := prime_count_of_even_index_split hq hp hmo hs hu hqm hcop hform hms
  have hmin := five_le_distinct_prime_factor_count ho hN
  have hpar := Nat.even_iff.mp (even_index_cofactor_prime_count hp hs hσ hplus hσs).1
  exact ⟨hpo,s,hs,hcop,hms ▸ hqm,hms ▸ hform,hσ,hplus,hσs,by omega⟩

/-- The first lift at an exact component yields a quadratic upper
bound for its index prime with a coefficient depending only on u. -/
theorem even_prime_power_component_quadratic_base_bound {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0<a)
    (hform : N=q^a*b) (hqb : ¬q ∣ b) (hl : sigma 1 b=q^a*i)
    (hr : sigma 1 (q^a)*i=2*b) (hp : p.Prime) (hu : 0<u) (hi : i=p^(2*u)) :
    p≤2*u ∨ p^2≤2*((u+1)*4^(2*u-4)-1)+p := by
  obtain ⟨hpo,s,hs,_,_,_,hσ,hplus,hσs,hw⟩ := even_prime_power_component_cofactor_data hN ho hq ha hform hqb hl hr hp hu hi
  rcases even_index_base_le_or_square_le_radical hp hpo hs hu hσ hplus hσs with h|h
  · exact .inl h
  · have hlim := (even_index_cofactor_radical_le hp hs hσ hplus hσs).trans
      (Nat.mul_le_mul_left (u+1) (Nat.pow_le_pow_right (by decide : 0<4) (by omega : 2*u-s.primeFactors.card≤2*u-4)))
    exact .inr (by omega)

end OddPerfect
