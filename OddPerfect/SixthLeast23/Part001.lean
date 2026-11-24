module

public import OddPerfect.SixthLeast23.Primes
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixCase23_0 : Closed 23 ⟨279841,292561,4,1⟩ := by
  apply closed_split (p:=292561) sixPrime23_292561 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_smaller (q:=19) (by decide) (by decide) (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=5) (by decide) (by decide) (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

theorem no_sixth_free_min_23 {N : ℕ} (H : Hyp N 23) (hd : 23∣N) : False := by
  apply root_split H (by norm_num) hd
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=7) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase23_0
  · exact closed_impossible (by decide +kernel)

end OddPerfect.SixthPowerChain
