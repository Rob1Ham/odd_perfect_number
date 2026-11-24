module

public import OddPerfect.ExponentOneSize
public import OddPerfect.SizeBound50

public section
namespace OddPerfect
open ArithmeticFunction

/-- The absolute size certificate forces a sixteen-digit scale for the
Euler index when the Euler exponent is one. -/
theorem euler_exponent_one_index_gt_three_mul_ten_pow_16 {N q m : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hqm : ¬q ∣ m) (hform : N=q*m^2) :
    3*10^16 < sigma 1 (m^2)/q :=
  exponent_one_index_gt_of_size hN ho hq hqm hform
    ((by decide : 2*(3*(10:ℕ)^16)^3 ≤ 10^50).trans (ten_pow_fifty_lt_of_odd_perfect ho hN).le)

end OddPerfect
