module

public import OddPerfect.PrimeRank5_4.Part013
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_312 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,103,2,0⟩, ⟨true,1397,1433,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1409 1397 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,103,2,0⟩, ⟨true,1409,1433,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_313 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,103,2,0⟩, ⟨true,1361,1433,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1393 rank5_4_311 rank5_4_312

theorem rank5_4_314 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,103,2,0⟩, ⟨true,1337,1433,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1361 1337 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,103,2,0⟩, ⟨true,1361,1433,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_4_310 rank5_4_313

theorem rank5_4_315 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,103,2,0⟩, ⟨true,1249,1433,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1333 rank5_4_309 rank5_4_314

theorem rank5_4_316 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,103,2,0⟩, ⟨true,1241,1433,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1249 1241 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,103,2,0⟩, ⟨true,1249,1433,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_4_308 rank5_4_315

theorem rank5_4_317 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,103,2,0⟩, ⟨true,1093,1449,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1433 1449 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,103,2,0⟩, ⟨true,1093,1433,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1237 rank5_4_307 rank5_4_316

theorem rank5_4_318 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,103,2,0⟩, ⟨true,1453,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_319 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,105,2,0⟩, ⟨true,1093,2161,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 103 105 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,103,2,0⟩, ⟨true,1093,2161,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1449 rank5_4_317 rank5_4_318

theorem rank5_4_320 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,109,2,0⟩, ⟨true,1093,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_321 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,109,2,0⟩, ⟨true,1093,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 105 rank5_4_319 rank5_4_320

theorem rank5_4_322 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,109,2,0⟩, ⟨true,1093,2185,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2161 2185 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,109,2,0⟩, ⟨true,1093,2161,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_4_306 rank5_4_321

theorem rank5_4_323 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,109,2,0⟩, ⟨true,2189,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2213 2189 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,109,2,0⟩, ⟨true,2213,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_324 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,109,2,0⟩, ⟨true,1093,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2185 rank5_4_322 rank5_4_323

theorem rank5_4_325 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,109,2,0⟩, ⟨true,1085,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1093 1085 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,109,2,0⟩, ⟨true,1093,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 101 rank5_4_305 rank5_4_324

theorem rank5_4_326 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,109,2,0⟩, ⟨true,541,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1081 rank5_4_234 rank5_4_325

theorem rank5_4_327 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,2,0⟩, ⟨false,95,109,2,0⟩, ⟨true,541,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 97 95 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,2,0⟩, ⟨false,97,109,2,0⟩, ⟨true,541,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 2 rank5_4_203 rank5_4_326

theorem rank5_4_328 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,2,0⟩, ⟨false,83,109,2,0⟩, ⟨true,541,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 93 rank5_4_202 rank5_4_327

theorem rank5_4_329 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,2,0⟩, ⟨false,83,109,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 537 rank5_4_201 rank5_4_328

theorem rank5_4_330 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨false,83,109,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 4 rank5_4_200 rank5_4_329

theorem rank5_4_331 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,4⟩, ⟨false,19,19,2,0⟩, ⟨false,113,163,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_332 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,2,2⟩, ⟨false,127,127,2,0⟩, ⟨true,269,353,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_333 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,2,2⟩, ⟨false,127,127,2,0⟩, ⟨true,357,521,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 373 357 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,2,2⟩, ⟨false,127,127,2,0⟩, ⟨true,373,521,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_334 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,2,2⟩, ⟨false,113,131,2,0⟩, ⟨true,269,521,1,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 2 3 127 (by norm_num) (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,2,2⟩, ⟨false,127,127,2,0⟩, ⟨true,269,521,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 353 rank5_4_332 rank5_4_333

theorem rank5_4_335 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,113,121,2,0⟩, ⟨true,269,353,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 113 121 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,113,113,2,0⟩, ⟨true,269,353,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
