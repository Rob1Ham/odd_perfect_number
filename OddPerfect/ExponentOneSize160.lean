module

public import OddPerfect.ExponentOneSize
public import OddPerfect.SizeBound160

public section

namespace OddPerfect

open ArithmeticFunction

/-- The checked absolute size bound implies an index exceeding ten to the
fifty-third power when the Euler exponent is one. -/
theorem euler_exponent_one_index_gt_ten_pow_53 {N q m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hqm : ¬q ∣ m) (hform : N=q*m^2) : 10^53 < sigma 1 (m^2)/q :=
  exponent_one_index_gt_of_size hN ho hq hqm hform
    ((by decide : 2*((10:ℕ)^53)^3 ≤ 10^160).trans (ten_pow_one_sixty_lt_of_odd_perfect ho hN).le)

end OddPerfect
