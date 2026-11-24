module

public import OddPerfect.SixthLeast19.Primes
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixCase19_0 : Closed 19 ⟨130321,137561,4,1⟩ := by
  apply closed_split (p:=151) sixPrime19_151 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=5) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem no_sixth_free_min_19 {N : ℕ} (H : Hyp N 19) (hd : 19∣N) : False := by
  apply root_split H (by norm_num) hd
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase19_0
  · exact closed_impossible (by decide +kernel)

end OddPerfect.SixthPowerChain
