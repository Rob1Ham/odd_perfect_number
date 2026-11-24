module

public import OddPerfect.SixthLeast41.Primes
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixCase41_0 : Closed 41 ⟨14815244502616321,15194223751350803,6,2⟩ := by
  apply closed_split (p:=6101) sixPrime41_6101 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_smaller (q:=7) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=5) (by decide) (by decide) (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

theorem sixCase41_1 : Closed 41 ⟨1681,1723,2,1⟩ := by
  apply closed_split (p:=1723) sixPrime41_1723 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase41_0
  · exact closed_impossible (by decide +kernel)

theorem no_sixth_free_min_41 {N : ℕ} (H : Hyp N 41) (hd : 41∣N) : False := by
  apply root_split H sixPrime41_41 hd
  intro j
  fin_cases j
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact sixCase41_1
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=5) (by decide) (by decide) (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

end OddPerfect.SixthPowerChain
