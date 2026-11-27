module

public import OddPerfect.PrimeRank5_1.Part021
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_504 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,127,139,2,0⟩, ⟨false,431,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 131 rank5_1_502 rank5_1_503

theorem rank5_1_505 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,127,139,2,0⟩, ⟨false,423,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 431 423 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,127,139,2,0⟩, ⟨false,431,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_1_487 rank5_1_504

theorem rank5_1_506 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,127,139,2,0⟩, ⟨false,351,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 353 351 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,127,139,2,0⟩, ⟨false,353,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 421 rank5_1_486 rank5_1_505

theorem rank5_1_507 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,127,143,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 139 143 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,127,139,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 349 rank5_1_447 rank5_1_506

theorem rank5_1_508 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,149,167,2,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_509 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,149,151,2,0⟩, ⟨false,263,277,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_510 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,157,157,2,0⟩, ⟨false,263,269,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_511 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,4⟩, ⟨false,157,157,2,0⟩, ⟨false,271,277,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 3221 rank5_1_prime3221 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_512 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,157,157,2,0⟩, ⟨false,271,277,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_513 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,157,157,2,0⟩, ⟨false,271,273,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 271 273 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,157,157,2,0⟩, ⟨false,271,271,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_514 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,157,157,2,0⟩, ⟨false,275,277,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 277 275 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,157,157,2,0⟩, ⟨false,277,277,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_515 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,157,157,2,0⟩, ⟨false,271,277,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 273 rank5_1_513 rank5_1_514

theorem rank5_1_516 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,157,157,2,0⟩, ⟨false,271,277,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_1_512 rank5_1_515

theorem rank5_1_517 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,157,157,2,0⟩, ⟨false,271,277,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 4 rank5_1_511 rank5_1_516

theorem rank5_1_518 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,153,157,2,0⟩, ⟨false,263,277,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 157 153 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,157,157,2,0⟩, ⟨false,263,277,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 269 rank5_1_510 rank5_1_517

theorem rank5_1_519 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,149,157,2,0⟩, ⟨false,263,277,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 151 rank5_1_509 rank5_1_518

theorem rank5_1_520 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,149,151,2,0⟩, ⟨false,281,293,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_521 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,153,157,2,0⟩, ⟨false,281,293,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 157 153 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,157,157,2,0⟩, ⟨false,281,293,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_522 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,149,157,2,0⟩, ⟨false,279,293,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 281 279 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,149,157,2,0⟩, ⟨false,281,293,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 151 rank5_1_520 rank5_1_521

theorem rank5_1_523 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,149,157,2,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 277 rank5_1_519 rank5_1_522

theorem rank5_1_524 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,159,167,2,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 163 159 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,163,167,2,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_525 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,149,167,2,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 157 rank5_1_523 rank5_1_524

theorem rank5_1_526 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,149,167,2,0⟩, ⟨false,263,299,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 293 299 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,149,167,2,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_1_508 rank5_1_525

theorem rank5_1_527 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,149,167,2,0⟩, ⟨false,301,349,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 307 301 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,149,167,2,0⟩, ⟨false,307,349,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
