module

public import OddPerfect.IndexSieveResiduals
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect.IndexSieve

open ArithmeticFunction Finset
open scoped NumberTheorySymbols

/-- The Euler return equation makes twice the index a nonzero square
at the Euler prime. This persists as a Jacobi-symbol condition at every
power of that prime, including every feasible source residual. -/
theorem twice_index_jacobi_at_euler_power {q a m i : ℕ} (hq : q.Prime) (hqo : Odd q)
    (hqm : ¬q ∣ m) (hr : sigma 1 (q^a)*i=2*m^2) (j : ℕ) :
    J(2*(i:ℤ) | q^j)=1 := by
  have hs : sigma 1 (q^a) ≡ 1 [MOD q] := by
    simpa [Nat.ModEq,Nat.mod_eq_of_lt hq.one_lt] using sigma_prime_pow_mod_self hq a
  have hi : i ≡ 2*m^2 [MOD q] := by simpa only [hr,one_mul] using (hs.mul_right i).symm
  have hi2 : 2*i ≡ (2*m)^2 [MOD q] := by
    rw [show (2*m)^2=2*(2*m^2) by ring]
    exact hi.mul_left _
  have hz : J(2*(i:ℤ) | q)=J((2*(m:ℤ))^2 | q) := by
    apply jacobiSym.mod_left'
    exact_mod_cast hi2
  have hc : q.Coprime (2*m) := (Nat.coprime_two_right.mpr hqo).mul_right (hq.coprime_iff_not_dvd.mpr hqm)
  have hcop : (2*(m:ℤ)).gcd q=1 := by
    rw [show (2*(m:ℤ))=((2*m:ℕ):ℤ) by push_cast; rfl,Int.gcd_natCast_natCast]
    exact hc.symm
  rw [jacobiSym.pow_right,hz,jacobiSym.sq_one' hcop,one_pow]

/-- Reciprocity transfers the source-residual check to a symbol with the
small fixed index in its denominator. -/
theorem jacobi_residual_at_index {q a m i j R : ℕ} (hq : q.Prime) (hq4 : q%4=1)
    (hqm : ¬q ∣ m) (hi : Odd i) (hr : sigma 1 (q^a)*i=2*m^2) (hR : R=q^j) :
    J(2 | R)*J((R:ℤ) | i)=1 := by
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  have hcon : q ≡ 1 [MOD 4] := hq4
  have hR4 : R%4=1 := by simpa [hR,Nat.ModEq] using hcon.pow j
  rw [←jacobiSym.quadratic_reciprocity_one_mod_four' hi hR4,←jacobiSym.mul_left,hR]
  exact twice_index_jacobi_at_euler_power hq hqo hqm hr j

end OddPerfect.IndexSieve
