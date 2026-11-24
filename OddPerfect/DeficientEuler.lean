module

public import OddPerfect.DeficientSupport
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect
open ArithmeticFunction

/-- The deficient divisor can be recovered from the real divisor sum and
the odd multiplier, even when that multiplier is composite. -/
theorem TothPair.deficientPerfectWith_index {n x : ℕ} (h : TothPair n x)
    (hx : Odd x) (h1 : 1<x) : DeficientPerfectWith n (sigma 1 n/x) := by
  obtain ⟨d,t,hd,hn,ht⟩ := h.deficientDivisor hx h1
  have hsum := hd.2
  have he : sigma 1 n = x*d := by nlinarith [congrArg (d*·) ht]
  simpa only [he, Nat.mul_div_cancel_left d h.2.1] using hd

/-- The Euler index is the deficient divisor of the square cofactor at
Euler exponent one. Thus classification of odd deficient-perfect numbers
constrains this whole exponent branch. -/
theorem exponent_one_cofactor_deficientPerfect {N q m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hqm : ¬q ∣ m) (hform : N=q*m^2) :
    DeficientPerfectWith (m^2) (sigma 1 (m^2)/q) := by
  have hqodd := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m^2) : q∣N)
  have hmodd := ho.of_dvd_nat (hform ▸ dvd_mul_left (m^2) q : m^2∣N)
  have hc : (m^2).Coprime q := (hq.coprime_iff_not_dvd.mpr (fun h => hqm (hq.dvd_of_dvd_pow h))).symm
  have hp : (m^2*q).Perfect := by rwa [mul_comm,← hform]
  exact (tothPair_of_linear_euler hmodd hq hc hp).deficientPerfectWith_index hqodd hq.one_lt

end OddPerfect
