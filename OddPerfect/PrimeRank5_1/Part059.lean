module

public import OddPerfect.PrimeRank5_1.Part058
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_1392 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,439,439,2,0⟩, ⟨false,607,609,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 607 609 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,439,439,2,0⟩, ⟨false,607,607,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1393 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,439,439,2,0⟩, ⟨false,611,613,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 613 611 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,439,439,2,0⟩, ⟨false,613,613,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1394 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,439,439,2,0⟩, ⟨false,607,613,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 609 rank5_1_1392 rank5_1_1393

theorem rank5_1_1395 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,441,443,2,0⟩, ⟨false,607,613,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 443 441 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,443,443,2,0⟩, ⟨false,607,613,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1396 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,439,443,2,0⟩, ⟨false,607,613,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 439 rank5_1_1394 rank5_1_1395

theorem rank5_1_1397 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,439,447,2,0⟩, ⟨false,599,613,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 443 447 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,439,443,2,0⟩, ⟨false,599,613,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 605 rank5_1_1391 rank5_1_1396

theorem rank5_1_1398 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,449,457,2,0⟩, ⟨false,599,613,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1399 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,439,457,2,0⟩, ⟨false,599,613,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 447 rank5_1_1397 rank5_1_1398

theorem rank5_1_1400 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,439,457,2,0⟩, ⟨false,595,613,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 599 595 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,439,457,2,0⟩, ⟨false,599,613,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1390 rank5_1_1399

theorem rank5_1_1401 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,439,457,2,0⟩, ⟨false,577,613,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 593 rank5_1_1389 rank5_1_1400

theorem rank5_1_1402 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,457,2,0⟩, ⟨false,575,613,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 577 575 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,457,2,0⟩, ⟨false,577,613,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 437 rank5_1_1380 rank5_1_1401

theorem rank5_1_1403 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,459,2,0⟩, ⟨false,541,613,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 457 459 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,457,2,0⟩, ⟨false,541,613,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 573 rank5_1_1379 rank5_1_1402

theorem rank5_1_1404 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,479,2,0⟩, ⟨false,541,547,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1405 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,479,2,0⟩, ⟨false,541,547,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1406 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,479,2,0⟩, ⟨false,541,555,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 547 555 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,479,2,0⟩, ⟨false,541,547,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1404 rank5_1_1405

theorem rank5_1_1407 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,479,2,0⟩, ⟨false,557,571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1408 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,467,2,0⟩, ⟨false,557,563,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1409 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,4⟩, ⟨false,461,463,2,0⟩, ⟨false,569,571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_1_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1410 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,461,463,2,0⟩, ⟨false,569,571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1411 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,463,2,0⟩, ⟨false,569,571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 4 rank5_1_1409 rank5_1_1410

theorem rank5_1_1412 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,465,467,2,0⟩, ⟨false,569,571,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 467 465 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,467,467,2,0⟩, ⟨false,569,571,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1413 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,467,2,0⟩, ⟨false,565,571,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 569 565 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,467,2,0⟩, ⟨false,569,571,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 463 rank5_1_1411 rank5_1_1412

theorem rank5_1_1414 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,469,2,0⟩, ⟨false,557,571,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 467 469 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,467,2,0⟩, ⟨false,557,571,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 563 rank5_1_1408 rank5_1_1413

theorem rank5_1_1415 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,471,479,2,0⟩, ⟨false,557,571,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 479 471 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,479,479,2,0⟩, ⟨false,557,571,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
