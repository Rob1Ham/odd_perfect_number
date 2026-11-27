module

public import OddPerfect.PrimeRank5_3.Part011
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_3_264 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,229,269,1,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_265 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,229,245,1,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 241 245 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,229,241,1,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_266 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,257,269,1,0⟩, ⟨false,2179,4357,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_267 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨true,257,269,1,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_268 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,257,261,1,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 257 261 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,257,257,1,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 43 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_269 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4363,5813,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_270 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4363,4647,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 4643 4647 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4363,4643,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_271 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4649,4805,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 4801 4805 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4649,4801,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_272 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,4⟩, ⟨true,269,269,1,1⟩, ⟨false,4813,4973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_273 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4813,4973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_274 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4813,4973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_275 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4813,4891,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 4889 4891 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4813,4889,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_276 : PrimeCovered (#v[⟨false,3,3,14,14⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4903,4919,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_277 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4903,4909,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_278 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4911,4919,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4919 4911 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4919,4919,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_279 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4903,4919,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 4909 rank5_3_277 rank5_3_278

theorem rank5_3_280 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4903,4919,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 14 rank5_3_276 rank5_3_279

theorem rank5_3_281 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4921,4937,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4931 4921 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4931,4937,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_282 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4903,4937,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 4919 rank5_3_280 rank5_3_281

theorem rank5_3_283 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4939,4973,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4943 4939 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4943,4973,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_284 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4893,4973,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4903 4893 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4903,4973,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 4937 rank5_3_282 rank5_3_283

theorem rank5_3_285 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4813,4973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 4891 rank5_3_275 rank5_3_284

theorem rank5_3_286 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4813,4973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_3_274 rank5_3_285

theorem rank5_3_287 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4813,4973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_3_273 rank5_3_286

end OddPerfect.SpoofBox
