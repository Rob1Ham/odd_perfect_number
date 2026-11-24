module

public import OddPerfect.SixthLeast29.Primes
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixCase29_0 : Closed 29 ⟨518112331021,536617049222,5,2⟩ := by
  apply closed_split (p:=7793) sixPrime29_7793 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=7) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=11) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase29_1 : Closed 29 ⟨707281,732541,4,1⟩ := by
  apply closed_split (p:=732541) sixPrime29_732541 (by decide +kernel)
  intro j
  fin_cases j
  · exact sixCase29_0
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=5) (by decide) (by decide) (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

theorem no_sixth_free_min_29 {N : ℕ} (H : Hyp N 29) (hd : 29∣N) : False := by
  apply root_split H (by norm_num) hd
  intro j
  fin_cases j
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_smaller (q:=13) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase29_1
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

end OddPerfect.SixthPowerChain
