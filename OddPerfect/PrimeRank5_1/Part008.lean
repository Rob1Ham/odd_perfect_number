module

public import OddPerfect.PrimeRank5_1.Part007
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_168 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,73,73,2,0⟩, ⟨false,2179,2905,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2903 2905 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,73,73,2,0⟩, ⟨false,2179,2903,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 2489 rank5_1_152 rank5_1_167

theorem rank5_1_169 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,73,73,2,0⟩, ⟨false,2907,4357,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2909 2907 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,73,73,2,0⟩, ⟨false,2909,4357,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_170 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,73,73,2,0⟩, ⟨false,2179,4357,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2905 rank5_1_168 rank5_1_169

theorem rank5_1_171 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,71,73,2,0⟩, ⟨false,2179,4357,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 71 rank5_1_151 rank5_1_170

theorem rank5_1_172 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,71,71,2,0⟩, ⟨false,4363,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_173 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,73,73,2,0⟩, ⟨false,4363,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_174 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,71,73,2,0⟩, ⟨false,4359,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4363 4359 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,71,73,2,0⟩, ⟨false,4363,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 71 rank5_1_172 rank5_1_173

theorem rank5_1_175 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,71,73,2,0⟩, ⟨false,2175,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2179 2175 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,71,73,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 4357 rank5_1_171 rank5_1_174

theorem rank5_1_176 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,71,73,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2173 rank5_1_150 rank5_1_175

theorem rank5_1_177 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,67,73,2,0⟩, ⟨false,1083,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1087 1083 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,67,73,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 69 rank5_1_149 rank5_1_176

theorem rank5_1_178 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,67,73,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1081 rank5_1_148 rank5_1_177

theorem rank5_1_179 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,59,73,2,0⟩, ⟨false,527,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 541 527 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,59,73,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 65 rank5_1_147 rank5_1_178

theorem rank5_1_180 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,59,77,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 73 77 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,59,73,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 525 rank5_1_146 rank5_1_179

theorem rank5_1_181 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,83,2,0⟩, ⟨false,263,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_182 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,89,89,2,0⟩, ⟨false,263,299,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 293 299 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,89,89,2,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_183 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,89,89,2,0⟩, ⟨false,307,325,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 317 325 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,89,89,2,0⟩, ⟨false,307,317,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_184 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,89,89,2,0⟩, ⟨false,331,339,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 337 339 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,89,89,2,0⟩, ⟨false,331,337,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_185 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,4⟩, ⟨false,89,89,2,0⟩, ⟨false,347,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 3221 rank5_1_prime3221 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_186 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,89,89,2,2⟩, ⟨false,347,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 8011 rank5_1_prime8011 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_187 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,89,89,4,0⟩, ⟨false,347,347,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_188 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,89,89,4,0⟩, ⟨false,349,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_189 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,89,89,4,0⟩, ⟨false,347,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 347 rank5_1_187 rank5_1_188

theorem rank5_1_190 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,89,89,2,0⟩, ⟨false,347,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .exponent 2 rank5_1_186 rank5_1_189

theorem rank5_1_191 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,89,89,2,0⟩, ⟨false,341,349,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 347 341 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,89,89,2,0⟩, ⟨false,347,349,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_1_185 rank5_1_190

end OddPerfect.SpoofBox
