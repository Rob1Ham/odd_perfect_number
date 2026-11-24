module

public import OddPerfect.SixthLeast43.Primes
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixCase43_0 : Closed 43 ⟨3418801,3500201,4,1⟩ := by
  apply closed_split (p:=3500201) sixPrime43_3500201 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_smaller (q:=13) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=5) (by decide) (by decide) (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

theorem no_sixth_free_min_43 {N : ℕ} (H : Hyp N 43) (hd : 43∣N) : False := by
  apply root_split H sixPrime43_43 hd
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase43_0
  · exact closed_impossible (by decide +kernel)

end OddPerfect.SixthPowerChain
