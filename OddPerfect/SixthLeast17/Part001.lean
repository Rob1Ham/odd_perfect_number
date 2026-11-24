module

public import OddPerfect.SixthLeast17.Primes
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixCase17_0 : Closed 17 ⟨2567150586289,2735954221307,6,2⟩ := by
  apply closed_split (p:=1051) sixPrime17_1051 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=5) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase17_1 : Closed 17 ⟨289,307,2,1⟩ := by
  apply closed_split (p:=307) sixPrime17_307 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase17_0
  · exact closed_impossible (by decide +kernel)

theorem sixCase17_2 : Closed 17 ⟨7411737061,7875053822,5,2⟩ := by
  apply closed_split (p:=44371) sixPrime17_44371 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=5) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase17_3 : Closed 17 ⟨83521,88741,4,1⟩ := by
  apply closed_split (p:=88741) sixPrime17_88741 (by decide +kernel)
  intro j
  fin_cases j
  · exact sixCase17_2
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=5) (by decide) (by decide) (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

theorem no_sixth_free_min_17 {N : ℕ} (H : Hyp N 17) (hd : 17∣N) : False := by
  apply root_split H (by norm_num) hd
  intro j
  fin_cases j
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact sixCase17_1
  · exact closed_impossible (by decide +kernel)
  · exact sixCase17_3
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

end OddPerfect.SixthPowerChain
