module

public import OddPerfect.SixthLeast7.Primes
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixCase7_0 : Closed 7 ⟨789002118148171186284376867201,942699944790356626070377774009,12,4⟩ := by
  apply closed_split (p:=28411) sixPrime7_28411 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=5) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase7_1 : Closed 7 ⟨64400939055106801,76946237469237403,10,3⟩ := by
  apply closed_split (p:=3500201) sixPrime7_3500201 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact sixCase7_0
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=5) (by decide) (by decide) (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

theorem sixCase7_2 : Closed 7 ⟨18837288001,21983376803,6,2⟩ := by
  apply closed_split (p:=43) sixPrime7_43 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase7_1
  · exact closed_impossible (by decide +kernel)

theorem sixCase7_3 : Closed 7 ⟨2401,2801,4,1⟩ := by
  apply closed_split (p:=2801) sixPrime7_2801 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact sixCase7_2
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=5) (by decide) (by decide) (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

theorem no_sixth_free_min_7 {N : ℕ} (H : Hyp N 7) (hd : 7∣N) : False := by
  apply root_split H (by norm_num) hd
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase7_3
  · exact closed_impossible (by decide +kernel)

end OddPerfect.SixthPowerChain
