module

public import OddPerfect.PrimeRank5_2.Part019
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_456 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,257,257,2,2⟩, ⟨false,62129,65761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 61 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_457 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,257,257,4,0⟩, ⟨false,62129,63893,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 63863 63893 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,257,257,4,0⟩, ⟨false,62129,63863,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_458 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,5⟩, ⟨false,257,257,4,0⟩, ⟨false,63901,65761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_459 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,9,0⟩, ⟨false,257,257,4,0⟩, ⟨false,63901,64817,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_460 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,10⟩, ⟨true,17,17,9,0⟩, ⟨false,257,257,4,0⟩, ⟨false,64849,65761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 12207031 rank5_2_prime12207031 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_461 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,9,0⟩, ⟨false,257,257,4,0⟩, ⟨false,64849,65301,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 65293 65301 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,9,0⟩, ⟨false,257,257,4,0⟩, ⟨false,64849,65293,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_462 : PrimeCovered (#v[⟨false,3,3,16,16⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,9,0⟩, ⟨false,257,257,4,0⟩, ⟨false,65309,65761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 1871 rank5_2_prime1871 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_463 : PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,9,0⟩, ⟨false,257,257,4,0⟩, ⟨false,65309,65533,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 65521 65533 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,9,0⟩, ⟨false,257,257,4,0⟩, ⟨false,65309,65521,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_464 : PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,9,0⟩, ⟨false,257,257,4,0⟩, ⟨false,65535,65761,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 65537 65535 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,9,0⟩, ⟨false,257,257,4,0⟩, ⟨false,65537,65761,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_465 : PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,9,0⟩, ⟨false,257,257,4,0⟩, ⟨false,65309,65761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 65533 rank5_2_463 rank5_2_464

theorem rank5_2_466 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,9,0⟩, ⟨false,257,257,4,0⟩, ⟨false,65303,65761,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 65309 65303 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,9,0⟩, ⟨false,257,257,4,0⟩, ⟨false,65309,65761,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 16 rank5_2_462 rank5_2_465

theorem rank5_2_467 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,9,0⟩, ⟨false,257,257,4,0⟩, ⟨false,64849,65761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 65301 rank5_2_461 rank5_2_466

theorem rank5_2_468 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,9,0⟩, ⟨false,257,257,4,0⟩, ⟨false,64819,65761,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 64849 64819 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,9,0⟩, ⟨false,257,257,4,0⟩, ⟨false,64849,65761,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 10 rank5_2_460 rank5_2_467

theorem rank5_2_469 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,9,0⟩, ⟨false,257,257,4,0⟩, ⟨false,63901,65761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 64817 rank5_2_459 rank5_2_468

theorem rank5_2_470 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,257,257,4,0⟩, ⟨false,63895,65761,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 63901 63895 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,257,257,4,0⟩, ⟨false,63901,65761,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 5 rank5_2_458 rank5_2_469

theorem rank5_2_471 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,257,257,4,0⟩, ⟨false,62129,65761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 63893 rank5_2_457 rank5_2_470

theorem rank5_2_472 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,257,257,2,0⟩, ⟨false,62129,65761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .exponent 2 rank5_2_456 rank5_2_471

theorem rank5_2_473 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,257,257,2,0⟩, ⟨false,62129,65775,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 65761 65775 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,257,257,2,0⟩, ⟨false,62129,65761,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 14 rank5_2_455 rank5_2_472

theorem rank5_2_474 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,257,257,2,0⟩, ⟨false,65777,69877,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_475 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,257,257,2,0⟩, ⟨false,62125,69877,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 62129 62125 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,257,257,2,0⟩, ⟨false,62129,69877,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 65775 rank5_2_473 rank5_2_474

theorem rank5_2_476 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,257,257,2,0⟩, ⟨false,55905,69877,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 55921 55905 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,257,257,2,0⟩, ⟨false,55921,69877,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 62123 rank5_2_454 rank5_2_475

theorem rank5_2_477 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,257,257,2,0⟩, ⟨false,46589,69877,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 55903 rank5_2_453 rank5_2_476

theorem rank5_2_478 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,257,257,2,0⟩, ⟨false,46589,69877,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_2_452 rank5_2_477

theorem rank5_2_479 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,257,257,2,0⟩, ⟨false,46587,69877,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 46589 46587 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,257,257,2,0⟩, ⟨false,46589,69877,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 12 rank5_2_451 rank5_2_478

end OddPerfect.SpoofBox
