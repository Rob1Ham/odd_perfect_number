module

public import OddPerfect.SixthLeast47.Primes
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem no_sixth_free_min_47 {N : ℕ} (H : Hyp N 47) (hd : 47∣N) : False := by
  apply root_split H sixPrime47_47 hd
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=37) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=11) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

end OddPerfect.SixthPowerChain
