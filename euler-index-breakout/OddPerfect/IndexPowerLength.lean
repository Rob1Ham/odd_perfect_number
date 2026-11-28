module

public import OddPerfect.IndexSieveCore
import OddPerfect.Cuts
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.FieldTheory.Finite.Basic

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- If the divisor sum of a positive even power of an odd prime is a
power of one prime, the length must be prime. A proper nontrivial length
would require a second primitive prime divisor. -/
theorem prime_length_of_pure_even_component {p q e β : ℕ} (hp : p.Prime) (hpo : Odd p)
    (hq : q.Prime) (he : 0<e) (heven : Even e) (hs : sigma 1 (p^e) ∣ q^β) :
    (e+1).Prime := by
  have ord (n : ℕ) (hn : 0<n) (hnE : Even n) (hd : sigma 1 (p^n) ∣ q^β) :
      orderOf (p : ZMod q) = n+1 := by
    obtain ⟨r,hr,_,hord,_⟩ := component_length_is_order_at_index_or_euler (i:=1)
      hp hpo hq hnE hn one_ne_zero (by simpa using hd)
    have hrq : r=q := by simpa using hr
    subst r
    exact hord
  obtain ⟨l,hl,hld⟩ := Nat.exists_prime_and_dvd (by omega : e+1≠1)
  have hLo : Odd (e+1) := Nat.odd_iff.mpr (by have := Nat.even_iff.mp heven; omega)
  have hlo := Nat.odd_iff.mp (hLo.of_dvd_nat hld)
  have hle : Even (l-1) := Nat.even_iff.mpr (by omega)
  have hfull := ord e he heven hs
  have hpart := ord (l-1) (by have := hl.one_lt; omega) hle ((sigma_dvd_of_length_dvd hp hl.pos hld).trans hs)
  rwa [show e+1=l by omega]

/-- At a single-prime index the component of that prime is pure. Its true
exponent lies in a bounded interval, is even, and has prime successor. -/
theorem prime_power_index_component_constraints {q a m p j : ℕ} (hq : q.Prime)
    (ha : Odd a) (hm : 0<m) (hp : p.Prime) (hpo : Odd p) (hj : 0<j)
    (hl : sigma 1 (m^2)=q^a*p^j) (hr : sigma 1 (q^a)*p^j=2*m^2) :
    let e := 2*m.factorization p
    j≤e ∧ e≤j+(a+1).divisors.card/2 ∧ (e+1).Prime ∧
      ∃ β : ℕ, 0<β ∧ sigma 1 (p^e)=q^β := by
  let e := 2*m.factorization p
  have hv := index_prime_return_valuation hp hpo hq hm (Nat.pow_pos hp.pos) hr
  rw [hp.factorization_pow,Finsupp.single_eq_same] at hv
  have he : 0<e := by dsimp [e]; omega
  have hd := cofactor_component_sum_dvd_index_product hm hp (e:=e) rfl he hl
  have hn : ¬p ∣ sigma 1 (p^e) := by rw [Nat.dvd_iff_mod_eq_zero,sigma_prime_pow_mod_self hp]; decide
  have hcop := (hp.coprime_iff_not_dvd.mpr hn).symm.pow_right j
  obtain ⟨β,_,hβ⟩ := (Nat.dvd_prime_pow hq).mp (hcop.dvd_of_dvd_mul_right hd)
  have hqβ : 0<β := by
    by_contra! h
    rw [show β=0 by omega,pow_zero] at hβ
    have hbig := self_lt_sigma_of_one_lt (one_lt_pow₀ hp.one_lt he.ne')
    have := one_lt_pow₀ hp.one_lt he.ne'
    omega
  have hE : Even e := ⟨m.factorization p,by simp [e,two_mul]⟩
  have hbound := twice_pure_exponent_excess_le_length_divisors hp hpo hq ha hm (Nat.pow_pos hp.pos) he hβ hr
  rw [hp.factorization_pow,Finsupp.single_eq_same] at hbound
  exact ⟨by omega,by omega,prime_length_of_pure_even_component hp hpo hq he hE (hβ.dvd),β,hqβ,hβ⟩

/-- Chen and Chen's local seventh-power case. The first permissible
cofactor exponent at the index prime is ten because nine is composite. -/
theorem seventh_power_index_component_exponent_ge_ten {q a m p : ℕ} (hq : q.Prime)
    (ha : Odd a) (hm : 0<m) (hp : p.Prime) (hpo : Odd p)
    (hl : sigma 1 (m^2)=q^a*p^7) (hr : sigma 1 (q^a)*p^7=2*m^2) :
    10≤2*m.factorization p := by
  obtain ⟨he,_,hlen,_⟩ := prime_power_index_component_constraints hq ha hm hp hpo (by decide : 0<7) hl hr
  have hn : 2*m.factorization p + 1≠9 := fun h => (by decide : ¬Nat.Prime 9) (h ▸ hlen)
  omega

end OddPerfect
