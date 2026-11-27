module

public import OddPerfect.PrimeRank5_1.Part060
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_1440 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,433,2,0⟩, ⟨false,641,659,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 425 rank5_1_1438 rank5_1_1439

theorem rank5_1_1441 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,433,2,0⟩, ⟨false,639,659,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 641 639 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,433,2,0⟩, ⟨false,641,659,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1431 rank5_1_1440

theorem rank5_1_1442 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,437,2,0⟩, ⟨false,617,659,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 433 437 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,433,2,0⟩, ⟨false,617,659,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 637 rank5_1_1430 rank5_1_1441

theorem rank5_1_1443 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,439,457,2,0⟩, ⟨false,617,659,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1444 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,457,2,0⟩, ⟨false,617,659,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 437 rank5_1_1442 rank5_1_1443

theorem rank5_1_1445 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,457,2,0⟩, ⟨false,661,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1446 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,459,2,0⟩, ⟨false,617,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 457 459 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,457,2,0⟩, ⟨false,617,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 659 rank5_1_1444 rank5_1_1445

theorem rank5_1_1447 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,509,2,0⟩, ⟨false,617,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1448 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,509,2,0⟩, ⟨false,615,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 617 615 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,509,2,0⟩, ⟨false,617,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 459 rank5_1_1446 rank5_1_1447

theorem rank5_1_1449 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,509,2,0⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 613 rank5_1_1423 rank5_1_1448

theorem rank5_1_1450 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,509,2,0⟩, ⟨false,541,717,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 709 717 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,509,2,0⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_1_1378 rank5_1_1449

theorem rank5_1_1451 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,509,2,0⟩, ⟨false,719,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1452 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,413,509,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 419 413 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,509,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 717 rank5_1_1450 rank5_1_1451

theorem rank5_1_1453 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,509,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 411 rank5_1_1377 rank5_1_1452

theorem rank5_1_1454 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,509,2,0⟩, ⟨false,541,1081,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1069 1081 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,509,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 5 rank5_1_1258 rank5_1_1453

theorem rank5_1_1455 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,509,2,0⟩, ⟨false,1083,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1087 1083 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,509,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1456 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,4,0⟩, ⟨false,343,509,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 347 343 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,509,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1081 rank5_1_1454 rank5_1_1455

theorem rank5_1_1457 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,509,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 341 rank5_1_1257 rank5_1_1456

theorem rank5_1_1458 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,257,509,2,0⟩, ⟨false,527,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 541 527 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,257,509,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 2 rank5_1_900 rank5_1_1457

theorem rank5_1_1459 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,257,513,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 509 513 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,257,509,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 525 rank5_1_873 rank5_1_1458

theorem rank5_1_1460 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,515,0,2,0⟩, ⟨false,515,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 521 515 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,521,0,2,0⟩, ⟨false,515,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 4 523 522 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,521,0,2,0⟩, ⟨false,523,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1461 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,257,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 513 rank5_1_1459 rank5_1_1460

theorem rank5_1_1462 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,257,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1463 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,19,2,0⟩, ⟨false,257,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 17 rank5_1_1461 rank5_1_1462

end OddPerfect.SpoofBox
