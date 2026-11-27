module

public import OddPerfect.PrimeRank5_1.Part059
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_1416 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,479,2,0⟩, ⟨false,557,571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 469 rank5_1_1414 rank5_1_1415

theorem rank5_1_1417 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,479,2,0⟩, ⟨false,557,571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1407 rank5_1_1416

theorem rank5_1_1418 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,483,2,0⟩, ⟨false,541,571,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 479 483 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,479,2,0⟩, ⟨false,541,571,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 555 rank5_1_1406 rank5_1_1417

theorem rank5_1_1419 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,485,509,2,0⟩, ⟨false,541,571,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 487 485 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,487,509,2,0⟩, ⟨false,541,571,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1420 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,509,2,0⟩, ⟨false,541,573,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 571 573 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,509,2,0⟩, ⟨false,541,571,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 483 rank5_1_1418 rank5_1_1419

theorem rank5_1_1421 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,509,2,0⟩, ⟨false,575,613,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 577 575 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,509,2,0⟩, ⟨false,577,613,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1422 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,509,2,0⟩, ⟨false,541,613,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 573 rank5_1_1420 rank5_1_1421

theorem rank5_1_1423 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,509,2,0⟩, ⟨false,541,613,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 459 rank5_1_1403 rank5_1_1422

theorem rank5_1_1424 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,433,2,0⟩, ⟨false,617,631,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1425 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,425,2,0⟩, ⟨false,617,631,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 421 425 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,421,2,0⟩, ⟨false,617,631,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1426 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,431,433,2,0⟩, ⟨false,617,623,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 619 623 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,431,433,2,0⟩, ⟨false,617,619,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1427 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,431,433,2,0⟩, ⟨false,625,631,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 631 625 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,431,433,2,0⟩, ⟨false,631,631,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1428 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,427,433,2,0⟩, ⟨false,617,631,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 431 427 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,431,433,2,0⟩, ⟨false,617,631,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 623 rank5_1_1426 rank5_1_1427

theorem rank5_1_1429 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,433,2,0⟩, ⟨false,617,631,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 425 rank5_1_1425 rank5_1_1428

theorem rank5_1_1430 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,433,2,0⟩, ⟨false,617,637,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 631 637 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,433,2,0⟩, ⟨false,617,631,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1424 rank5_1_1429

theorem rank5_1_1431 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,433,2,0⟩, ⟨false,641,659,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1432 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,421,2,0⟩, ⟨false,641,649,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 647 649 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,421,2,0⟩, ⟨false,641,647,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1433 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,419,2,0⟩, ⟨false,653,653,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1434 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,421,421,2,0⟩, ⟨false,653,653,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1435 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,421,2,0⟩, ⟨false,653,655,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 653 655 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,421,2,0⟩, ⟨false,653,653,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 419 rank5_1_1433 rank5_1_1434

theorem rank5_1_1436 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,421,2,0⟩, ⟨false,657,659,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 659 657 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,421,2,0⟩, ⟨false,659,659,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1437 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,421,2,0⟩, ⟨false,651,659,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 653 651 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,421,2,0⟩, ⟨false,653,659,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 655 rank5_1_1435 rank5_1_1436

theorem rank5_1_1438 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,425,2,0⟩, ⟨false,641,659,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 421 425 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,421,2,0⟩, ⟨false,641,659,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 649 rank5_1_1432 rank5_1_1437

theorem rank5_1_1439 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,427,433,2,0⟩, ⟨false,641,659,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 431 427 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,431,433,2,0⟩, ⟨false,641,659,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
