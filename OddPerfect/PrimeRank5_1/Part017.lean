module

public import OddPerfect.PrimeRank5_1.Part016
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_384 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,101,103,2,0⟩, ⟨false,4359,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4363 4359 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,101,103,2,0⟩, ⟨false,4363,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 8725 rank5_1_364 rank5_1_383

theorem rank5_1_385 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,101,103,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 4357 rank5_1_361 rank5_1_384

theorem rank5_1_386 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,97,103,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 99 rank5_1_336 rank5_1_385

theorem rank5_1_387 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,97,103,2,0⟩, ⟨false,2175,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2179 2175 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,97,103,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_1_335 rank5_1_386

theorem rank5_1_388 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,97,103,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2173 rank5_1_334 rank5_1_387

theorem rank5_1_389 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,113,2,0⟩, ⟨false,1087,2161,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_390 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,107,2,0⟩, ⟨false,1087,1237,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_391 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,109,109,2,0⟩, ⟨false,1087,1157,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1153 1157 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,109,109,2,0⟩, ⟨false,1087,1153,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_392 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,4⟩, ⟨false,109,109,2,0⟩, ⟨false,1163,1237,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 3221 rank5_1_prime3221 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_393 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,109,109,2,0⟩, ⟨false,1163,1237,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_394 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,109,109,2,0⟩, ⟨false,1163,1197,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1193 1197 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,109,109,2,0⟩, ⟨false,1163,1193,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_395 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,109,109,2,0⟩, ⟨false,1199,1237,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1201 1199 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,109,109,2,0⟩, ⟨false,1201,1237,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_396 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,109,109,2,0⟩, ⟨false,1163,1237,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1197 rank5_1_394 rank5_1_395

theorem rank5_1_397 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,109,109,2,0⟩, ⟨false,1163,1237,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_1_393 rank5_1_396

theorem rank5_1_398 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,109,109,2,0⟩, ⟨false,1159,1237,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1163 1159 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,109,109,2,0⟩, ⟨false,1163,1237,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_1_392 rank5_1_397

theorem rank5_1_399 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,109,109,2,0⟩, ⟨false,1087,1237,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1157 rank5_1_391 rank5_1_398

theorem rank5_1_400 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,109,2,0⟩, ⟨false,1087,1237,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 107 rank5_1_390 rank5_1_399

theorem rank5_1_401 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,107,2,0⟩, ⟨false,1249,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_402 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,109,109,2,0⟩, ⟨false,1249,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_403 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,109,2,0⟩, ⟨false,1239,1439,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1249 1239 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,109,2,0⟩, ⟨false,1249,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 107 rank5_1_401 rank5_1_402

theorem rank5_1_404 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,109,2,0⟩, ⟨false,1087,1445,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1439 1445 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,109,2,0⟩, ⟨false,1087,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1237 rank5_1_400 rank5_1_403

theorem rank5_1_405 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,4⟩, ⟨false,107,107,2,0⟩, ⟨false,1447,1571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 3221 rank5_1_prime3221 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_406 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,107,107,2,0⟩, ⟨false,1447,1571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_407 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,107,107,2,0⟩, ⟨false,1447,1505,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1499 1505 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,107,107,2,0⟩, ⟨false,1447,1499,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
