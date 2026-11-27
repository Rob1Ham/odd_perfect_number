module

public import OddPerfect.PrimeRank5_3.Part012
import OddPerfect.PrimeRank5_3.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_3_288 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4807,4973,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4813 4807 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4813,4973,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_3_272 rank5_3_287

theorem rank5_3_289 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4649,4973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 4805 rank5_3_271 rank5_3_288

theorem rank5_3_290 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4363,4983,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 4973 4983 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4363,4973,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 4647 rank5_3_270 rank5_3_289

theorem rank5_3_291 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4985,5813,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4987 4985 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4987,5813,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_292 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4363,5813,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 4983 rank5_3_290 rank5_3_291

theorem rank5_3_293 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4363,5815,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5813 5815 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4363,5813,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_3_269 rank5_3_292

theorem rank5_3_294 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,1,1⟩, ⟨false,5817,8719,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5821 5817 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,1,1⟩, ⟨false,5821,8719,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_295 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,1,1⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 5815 rank5_3_293 rank5_3_294

theorem rank5_3_296 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,5,0⟩, ⟨false,4363,5813,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_297 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,5,0⟩, ⟨false,4363,4983,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 4973 4983 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,5,0⟩, ⟨false,4363,4973,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_298 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,5,0⟩, ⟨false,4987,5161,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5153 5161 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,5,0⟩, ⟨false,4987,5153,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_299 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,4⟩, ⟨true,269,269,5,0⟩, ⟨false,5167,5351,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_300 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5167,5351,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_301 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5167,5351,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_302 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5167,5257,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5237 5257 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5167,5237,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_303 : PrimeCovered (#v[⟨false,3,3,14,14⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5261,5281,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_304 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5261,5269,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5261 5269 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5261,5261,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_305 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,10⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5273,5281,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 12207031 rank5_3_prime12207031 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_306 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5273,5275,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5273 5275 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5273,5273,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_307 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5277,5281,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5279 5277 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5279,5281,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_308 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5273,5281,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 5275 rank5_3_306 rank5_3_307

theorem rank5_3_309 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5271,5281,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5273 5271 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5273,5281,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 10 rank5_3_305 rank5_3_308

theorem rank5_3_310 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5261,5281,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 5269 rank5_3_304 rank5_3_309

theorem rank5_3_311 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5261,5281,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 14 rank5_3_303 rank5_3_310

end OddPerfect.SpoofBox
