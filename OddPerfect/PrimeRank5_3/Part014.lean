module

public import OddPerfect.PrimeRank5_3.Part013
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_3_312 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5283,5303,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5297 5283 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5297,5303,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_313 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5261,5305,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5303 5305 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5261,5303,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 5281 rank5_3_311 rank5_3_312

theorem rank5_3_314 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5307,5351,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5309 5307 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5309,5351,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_315 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5259,5351,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5261 5259 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5261,5351,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 5305 rank5_3_313 rank5_3_314

theorem rank5_3_316 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5167,5351,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 5257 rank5_3_302 rank5_3_315

theorem rank5_3_317 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5167,5351,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_3_301 rank5_3_316

theorem rank5_3_318 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5167,5351,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_3_300 rank5_3_317

theorem rank5_3_319 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5163,5351,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5167 5163 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5167,5351,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_3_299 rank5_3_318

theorem rank5_3_320 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,5,0⟩, ⟨false,4987,5367,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5351 5367 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,5,0⟩, ⟨false,4987,5351,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 5161 rank5_3_298 rank5_3_319

theorem rank5_3_321 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5369,5813,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5381 5369 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5381,5813,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_322 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,5,0⟩, ⟨false,4985,5813,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4987 4985 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,5,0⟩, ⟨false,4987,5813,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 5367 rank5_3_320 rank5_3_321

theorem rank5_3_323 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,5,0⟩, ⟨false,4363,5813,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 4983 rank5_3_297 rank5_3_322

theorem rank5_3_324 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,5,0⟩, ⟨false,4363,5815,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5813 5815 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,5,0⟩, ⟨false,4363,5813,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_3_296 rank5_3_323

theorem rank5_3_325 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5817,8719,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5821 5817 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,5,0⟩, ⟨false,5821,8719,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_326 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,5,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 5815 rank5_3_324 rank5_3_325

theorem rank5_3_327 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,265,269,1,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 269 265 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,1,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .exponent 1 rank5_3_295 rank5_3_326

theorem rank5_3_328 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,257,269,1,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 261 rank5_3_268 rank5_3_327

theorem rank5_3_329 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,257,269,1,0⟩, ⟨false,4363,8725,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 8719 8725 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,257,269,1,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_3_267 rank5_3_328

theorem rank5_3_330 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨true,257,261,1,0⟩, ⟨false,19531,19531,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 257 261 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨true,257,257,1,0⟩, ⟨false,19531,19531,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 43 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_331 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨true,265,269,1,0⟩, ⟨false,19531,19531,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 269 265 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,1,0⟩, ⟨false,19531,19531,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_332 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨true,257,269,1,0⟩, ⟨false,8731,0,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 1 4 19531 (by norm_num) (Nat.odd_iff.mpr (by decide)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨true,257,269,1,0⟩, ⟨false,19531,19531,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 261 rank5_3_330 rank5_3_331

theorem rank5_3_333 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,257,261,1,0⟩, ⟨false,8731,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 257 261 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,257,257,1,0⟩, ⟨false,8731,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 43 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_334 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,265,269,1,0⟩, ⟨false,8731,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 269 265 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,269,269,1,0⟩, ⟨false,8731,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_335 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,257,269,1,0⟩, ⟨false,8731,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 261 rank5_3_333 rank5_3_334

end OddPerfect.SpoofBox
