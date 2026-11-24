module

public import OddPerfect.SixthLeast13.Primes
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixCase13_0 : Closed 13 ⟨27342744282841,29622183904043,6,2⟩ := by
  apply closed_split (p:=433) sixPrime13_433 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_smaller (q:=7) (by decide) (by decide) (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=11) (by decide) (by decide) (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

theorem sixCase13_1 : Closed 13 ⟨28561,30941,4,1⟩ := by
  apply closed_split (p:=30941) sixPrime13_30941 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact sixCase13_0
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=5) (by decide) (by decide) (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

theorem no_sixth_free_min_13 {N : ℕ} (H : Hyp N 13) (hd : 13∣N) : False := by
  apply root_split H (by norm_num) hd
  intro j
  fin_cases j
  · exact closed_smaller (q:=7) (by decide) (by decide) (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase13_1
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

end OddPerfect.SixthPowerChain
