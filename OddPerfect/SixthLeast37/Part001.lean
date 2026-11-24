module

public import OddPerfect.SixthLeast37.Primes
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem no_sixth_free_min_37 {N : ℕ} (H : Hyp N 37) (hd : 37∣N) : False := by
  apply root_split H sixPrime37_37 hd
  intro j
  fin_cases j
  · exact closed_smaller (q:=19) (by decide) (by decide) (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=11) (by decide) (by decide) (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

end OddPerfect.SixthPowerChain
