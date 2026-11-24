module

public import OddPerfect.FermatIndexValuation
public import OddPerfect.SemiprimeLocal
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- No Euler index is the cube of a prime whose predecessor is a power of two. -/
theorem euler_component_index_ne_fermat_prime_cube {N q a m i p k : ℕ} (hN : Nat.Perfect N)
    (ho : Odd N) (hq : q.Prime) (ha4 : a%4=1) (hqm : ¬ q ∣ m) (hform : N=q^a*m^2)
    (hp : p.Prime) (hpo : Odd p) (hk : p-1=2^k)
    (hleft : sigma 1 (m^2)=q^a*i) (hright : sigma 1 (q^a)*i=2*m^2) : i ≠ p^3 := by
  rintro rfl
  have ha : Odd a := Nat.odd_iff.mpr (by omega)
  have hm := (ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left _ _))).pos
  have hpF : (p^3).primeFactors = {p} := by rw [Nat.primeFactors_pow _ (by decide : 3 ≠ 0), hp.primeFactors]
  have hpS : ∀ u ∈ (p^3).primeFactors, ∃ d : ℕ, u-1=2^d := by simpa [hpF] using (show ∃ d : ℕ, p-1=2^d from ⟨k,hk⟩)
  have ⟨hqpred,hvp⟩ := fermat_supported_index_valuation hq hm (hpo.pow (n:=3)) (by simp [hpF] : p ∈ (p^3).primeFactors) hpS hleft hright
  rw [hp.factorization_pow, Finsupp.single_eq_same] at hvp
  have hdL := (hp.dvd_iff_one_le_factorization (by omega : a+1 ≠ 0)).mpr
    (by omega : 1 ≤ (a+1).factorization p)
  have hw := euler_index_weight_bounds (B:=4) (T:=3) hN ho hq ha hqm hform hleft hright
    (by simp [hpF, cardFactors_apply_prime_pow hp]) (by decide)
  have hN6 : N.primeFactors.card ≤ 6 := by omega
  have hτ : (a+1).divisors.card ≤ 6 := hw.1.trans hN6
  by_cases hp3 : p = 3
  · subst p
    have hsmall : (a+1).factorization 3 ≤ 2 := by
      by_contra! h
      have hd27 := (hp.pow_dvd_iff_le_factorization (by omega : a+1 ≠ 0)).mpr h
      have hd54 : 54 ∣ a+1 := (by decide : Nat.Coprime 2 27).mul_dvd_of_dvd_of_dvd (by omega) hd27
      have hc := Finset.card_le_card (Nat.divisors_subset_of_dvd (by omega : a+1 ≠ 0) hd54)
      have h54 : (54:ℕ).divisors.card=8 := by decide
      omega
    have hout := cofactor_component_sum_dvd_index_product hm hp
      (by omega : 2*m.factorization 3=4) (by decide) hleft
    have h11 : 11 ∣ sigma 1 (3^4) := by rw [sigma_one_apply_prime_pow hp]; decide
    obtain h | h := (show Nat.Prime 11 by decide).dvd_mul.mp (h11.trans hout)
    · have hq11 := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 11) hq).mp ((by decide : Nat.Prime 11).dvd_of_dvd_pow h)
      subst q
      exact (by decide : ¬ 3 ∣ 11-1) hqpred
    · exact (by decide : ¬ 11 ∣ 3^3) h
  · have h3N : 3 ∣ N := by
      by_contra h
      have := eight_le_distinct_prime_factor_count_of_three_free ho hN h
      omega
    have hpg : 3 < p := by have := hp.two_le; have := Nat.odd_iff.mp hpo; omega
    have hqg := Nat.le_of_dvd (by have := hq.one_lt; omega : 0<q-1) hqpred
    have h3p : Nat.Prime 3 := by decide
    have h3m : 3 ∣ m := h3p.dvd_of_dvd_pow ((h3p.dvd_mul.mp (hform ▸ h3N)).resolve_left
      (fun h => by have := (Nat.prime_dvd_prime_iff_eq h3p hq).mp (h3p.dvd_of_dvd_pow h); omega))
    let e := 2*m.factorization 3
    have hepos : 0 < e := by have := (h3p.dvd_iff_one_le_factorization hm.ne').mp h3m; dsimp [e]; omega
    have heven : Even e := ⟨m.factorization 3, by simp [e,two_mul]⟩
    have hout := cofactor_component_sum_dvd_index_product hm h3p (e:=e) rfl hepos hleft
    have hnout : ¬ p ∣ sigma 1 (3^e) := by
      intro hd
      have h := (exceptional_prime_power_index_component h3p heven hepos hp hk hq
        (by simpa [Nat.mul_comm] using hout) hd).2.1
      have hcon := (ZMod.natCast_eq_natCast_iff 3 1 p).mp (by simpa using h)
      change 3%p = 1%p at hcon
      rw [Nat.mod_eq_of_lt hpg, Nat.mod_eq_of_lt hp.one_lt] at hcon
      omega
    have hcop := (hp.coprime_iff_not_dvd.mpr hnout).symm.pow_right 3
    obtain ⟨β,_,hβ⟩ := (Nat.dvd_prime_pow hq).mp (hcop.dvd_of_dvd_mul_right hout)
    have h3pow : 3^e ∣ m^2 := by
      have hv : (m^2).factorization 3=e := by simp [e,Nat.factorization_pow]
      rw [← hv]; exact Nat.ordProj_dvd _ _
    have hback : 3^e ∣ sigma 1 (q^a) :=
      (((h3p.coprime_iff_not_dvd.mpr (fun h => hp3 ((Nat.prime_dvd_prime_iff_eq h3p hp).mp h).symm)).pow_left e).pow_right 3).dvd_of_dvd_mul_right
        (hright ▸ h3pow.trans (dvd_mul_left _ _))
    have h3len := reciprocal_component_length h3p (by decide) hq hepos hβ hback
    have he2 : 2 ≤ e := by have := Nat.even_iff.mp heven; omega
    have h3L := (dvd_pow_self 3 (by omega : e-1 ≠ 0)).trans h3len
    rcases euler_length_cases_of_divisor_count_le_six ha4 hτ with h2 | ⟨l,j,hl,_,_,hL⟩
    · omega
    · have hlpd (u : ℕ) (hu : u.Prime) (huo : Odd u) (huL : u ∣ a+1) : u=l :=
        (Nat.prime_dvd_prime_iff_eq hu hl).mp (hu.dvd_of_dvd_pow
          ((Nat.coprime_two_right.mpr huo).dvd_of_dvd_mul_left (hL ▸ huL)))
      exact hp3 ((hlpd p hp hpo hdL).trans (hlpd 3 h3p (by decide) h3L).symm)

end OddPerfect
