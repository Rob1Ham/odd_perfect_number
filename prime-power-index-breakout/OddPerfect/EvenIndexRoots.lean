module

public import OddPerfect.EvenPrimePowerParity
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.LinearCombination

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- A return to an odd cofactor prime occurs at a common root of two
explicit polynomials modulo that prime. -/
theorem even_index_source_root_equations {q p s u r β : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hrs : r ∣ s) (hσ : sigma 1 (p^(2*u))=q)
    (hplus : q+1=2*s^2) (hout : sigma 1 (r^(2*s.factorization r))=p^β) :
    let x : ZMod r := p
    x^β=1 ∧ x^(2*u+1)+x=2 ∧
      ((x=1) → r ∣ 2*u+2) := by
  have hqp : r ∣ q+1 := hplus ▸ dvd_mul_of_dvd_right (dvd_pow hrs (by decide : 2≠0)) _
  have hneg : (q:ZMod r) = -1 := by
    simpa [Nat.cast_add,eq_neg_iff_add_eq_zero] using (ZMod.natCast_eq_zero_iff (q+1) r).mpr hqp
  have hpow : p^β ≡ 1 [MOD r] := by
    rw [←hout]
    simpa [Nat.ModEq,Nat.mod_eq_of_lt hr.one_lt] using sigma_prime_pow_mod_self hr (2*s.factorization r)
  refine ⟨by simpa only [Nat.cast_pow,Nat.cast_one] using (ZMod.natCast_eq_natCast_iff _ _ r).mpr hpow,?_,?_⟩
  · have heq : (∑ v ∈ range (2*u+1),(p:ZMod r)^v) = (q:ZMod r) := by
      rw [sigma_one_apply_prime_pow hp] at hσ
      simpa using congrArg (fun n:ℕ => (n:ZMod r)) hσ
    have hgeom := geom_sum_mul (p:ZMod r) (2*u+1)
    rw [heq,hneg] at hgeom
    linear_combination -hgeom
  · intro h
    have hp1 : p ≡ 1 [MOD r] := (ZMod.natCast_eq_natCast_iff p 1 r).mp (by simpa using h)
    have hres := sigma_modEq_of_one hp hp1 (2*u)
    rw [hσ] at hres
    exact ((hres.add_right 1).dvd_iff dvd_rfl).mp hqp

end OddPerfect
