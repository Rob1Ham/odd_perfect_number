module

public import OddPerfect.SixthPowerChain
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixPrime47_47 : Nat.Prime 47 :=
  by norm_num

end OddPerfect.SixthPowerChain
