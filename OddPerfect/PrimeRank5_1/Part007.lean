module

public import OddPerfect.PrimeRank5_1.Part006
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_144 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,2,0⟩, ⟨false,29,57,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 53 57 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,2,0⟩, ⟨false,29,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_145 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,2,2⟩, ⟨false,59,113,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_146 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,59,73,2,0⟩, ⟨false,263,525,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 523 525 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,59,73,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_147 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,59,65,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 61 65 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,59,61,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_148 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,67,73,2,0⟩, ⟨false,541,1081,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1069 1081 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,67,73,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_149 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,67,69,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 67 69 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,67,67,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_150 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,71,73,2,0⟩, ⟨false,1087,2173,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2161 2173 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,71,73,2,0⟩, ⟨false,1087,2161,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_151 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,71,71,2,0⟩, ⟨false,2179,4357,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_152 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,73,73,2,0⟩, ⟨false,2179,2489,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2477 2489 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,73,73,2,0⟩, ⟨false,2179,2477,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_153 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,4⟩, ⟨false,73,73,2,0⟩, ⟨false,2503,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 3221 rank5_1_prime3221 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_154 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,73,73,2,2⟩, ⟨false,2503,2687,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 1801 rank5_1_prime1801 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_155 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,73,73,4,0⟩, ⟨false,2503,2591,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_156 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,73,73,4,0⟩, ⟨false,2593,2611,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2609 2611 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,73,73,4,0⟩, ⟨false,2593,2609,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_157 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,73,73,4,0⟩, ⟨false,2617,2623,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2621 2623 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,73,73,4,0⟩, ⟨false,2617,2621,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_158 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,73,73,4,0⟩, ⟨false,2625,2633,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2633 2625 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,73,73,4,0⟩, ⟨false,2633,2633,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_159 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,73,73,4,0⟩, ⟨false,2613,2633,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2617 2613 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,73,73,4,0⟩, ⟨false,2617,2633,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 2623 rank5_1_157 rank5_1_158

theorem rank5_1_160 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,73,73,4,0⟩, ⟨false,2593,2639,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2633 2639 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,73,73,4,0⟩, ⟨false,2593,2633,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 2611 rank5_1_156 rank5_1_159

theorem rank5_1_161 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,73,73,4,0⟩, ⟨false,2641,2687,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2647 2641 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,73,73,4,0⟩, ⟨false,2647,2687,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_162 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,73,73,4,0⟩, ⟨false,2593,2687,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2639 rank5_1_160 rank5_1_161

theorem rank5_1_163 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,73,73,4,0⟩, ⟨false,2503,2687,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2591 rank5_1_155 rank5_1_162

theorem rank5_1_164 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,73,73,2,0⟩, ⟨false,2503,2687,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .exponent 2 rank5_1_154 rank5_1_163

theorem rank5_1_165 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,73,73,2,0⟩, ⟨false,2689,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_166 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,73,73,2,0⟩, ⟨false,2503,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2687 rank5_1_164 rank5_1_165

theorem rank5_1_167 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,73,73,2,0⟩, ⟨false,2491,2903,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2503 2491 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,73,73,2,0⟩, ⟨false,2503,2903,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_1_153 rank5_1_166

end OddPerfect.SpoofBox
