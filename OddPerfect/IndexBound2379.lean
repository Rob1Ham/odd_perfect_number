module

public import OddPerfect.IndexRangeTables

public section

namespace OddPerfect

open ArithmeticFunction

/-- The exact-length and shared-multiplicity tests give the Euler-index
bound 2,379, with the corresponding strict prime-power size inequality. -/
theorem euler_component_index_ge_2379 {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (hqm : ¬q ∣ m) (hform : N=q^a*m^2) :
    2379*q^a < 2*m^2 ∧ 2379 ≤ sigma 1 (m^2)/q^a :=
  IndexSieve.euler_component_index_ge_of_cover hN ho hq hq4 ha4 hqm hform
    (euler_component_index_ge_343 hN ho hq hq4 ha4 hqm hform).2
    (by decide) (by decide) IndexSieve.covers_343_2379

end OddPerfect
