module

public import OddPerfect.PrimeRank5_3.Part018
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_3_432 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,349,353,1,0⟩, ⟨false,953,997,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 973 rank5_3_430 rank5_3_431

theorem rank5_3_433 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,349,353,1,0⟩, ⟨false,951,997,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 953 951 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,349,353,1,0⟩, ⟨false,953,997,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_3_427 rank5_3_432

theorem rank5_3_434 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,345,353,1,0⟩, ⟨false,907,997,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 349 345 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,349,353,1,0⟩, ⟨false,907,997,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 949 rank5_3_426 rank5_3_433

theorem rank5_3_435 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,337,353,1,0⟩, ⟨false,907,997,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 341 rank5_3_419 rank5_3_434

theorem rank5_3_436 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,337,353,1,0⟩, ⟨false,907,1003,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 997 1003 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,337,353,1,0⟩, ⟨false,907,997,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_3_418 rank5_3_435

theorem rank5_3_437 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨true,337,353,1,0⟩, ⟨false,1009,1123,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_438 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,337,341,1,0⟩, ⟨false,1009,1123,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 337 341 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,337,337,1,0⟩, ⟨false,1009,1123,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 13 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_439 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,345,353,1,0⟩, ⟨false,1009,1123,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 349 345 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,349,353,1,0⟩, ⟨false,1009,1123,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_440 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,337,353,1,0⟩, ⟨false,1009,1123,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 341 rank5_3_438 rank5_3_439

theorem rank5_3_441 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,337,353,1,0⟩, ⟨false,1005,1123,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1009 1005 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,337,353,1,0⟩, ⟨false,1009,1123,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_3_437 rank5_3_440

theorem rank5_3_442 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,333,353,1,0⟩, ⟨false,907,1123,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 337 333 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,337,353,1,0⟩, ⟨false,907,1123,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1003 rank5_3_436 rank5_3_441

theorem rank5_3_443 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,353,1,0⟩, ⟨false,901,1123,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 907 901 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,353,1,0⟩, ⟨false,907,1123,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 329 rank5_3_417 rank5_3_442

theorem rank5_3_444 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,353,1,0⟩, ⟨false,751,1123,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 899 rank5_3_416 rank5_3_443

theorem rank5_3_445 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,353,1,0⟩, ⟨false,751,1123,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 309 rank5_3_415 rank5_3_444

theorem rank5_3_446 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,353,1,0⟩, ⟨false,751,1123,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 8 rank5_3_414 rank5_3_445

theorem rank5_3_447 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,365,1,0⟩, ⟨false,563,1123,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 353 365 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,353,1,0⟩, ⟨false,563,1123,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 749 rank5_3_413 rank5_3_446

theorem rank5_3_448 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,433,1,0⟩, ⟨false,563,743,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_449 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,397,1,0⟩, ⟨false,563,631,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_450 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨true,401,433,1,0⟩, ⟨false,563,631,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_451 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,433,1,0⟩, ⟨false,563,595,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 593 595 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,433,1,0⟩, ⟨false,563,593,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_452 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,413,1,0⟩, ⟨false,599,631,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 409 413 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,409,1,0⟩, ⟨false,599,631,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_453 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,421,433,1,0⟩, ⟨false,599,631,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_454 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,421,433,1,0⟩, ⟨false,599,613,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_455 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,421,425,1,0⟩, ⟨false,617,631,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 421 425 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,421,421,1,0⟩, ⟨false,617,631,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 211 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

end OddPerfect.SpoofBox
