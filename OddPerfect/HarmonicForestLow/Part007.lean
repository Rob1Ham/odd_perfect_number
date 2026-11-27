module

public import OddPerfect.HarmonicForestLow.Part006
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicForestLow

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf99_0 : PrimeBank := .leaf [2, 3]
theorem leaf99_0_valid : leaf99_0.Certified := by
  simp only [leaf99_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by simp⟩

@[expose] def pool99 : PrimeBank := leaf99_0
theorem pool99_valid : pool99.Certified := leaf99_0_valid

theorem covered99 : Range 99 101 :=
  scan_sound pool99 pool99_valid 2 99 [3] []
    (by decide) (by decide +kernel)

theorem segment99 : Range 99 101 := covered99

theorem through101 : Range 3 101 := (range_join through99 segment99)

end OddPerfect.HarmonicChain.HarmonicForestLow
