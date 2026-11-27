module

public import OddPerfect.PrimeRank5_4.Part041
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_984 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,401,409,2,0⟩, ⟨true,717,733,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 733 717 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,401,409,2,0⟩, ⟨true,733,733,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 367 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_985 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,401,409,2,0⟩, ⟨true,701,733,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 713 rank5_4_983 rank5_4_984

theorem rank5_4_986 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,399,409,2,0⟩, ⟨true,701,733,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 401 399 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,401,409,2,0⟩, ⟨true,701,733,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_4_978 rank5_4_985

theorem rank5_4_987 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,409,2,0⟩, ⟨true,701,745,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 733 745 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,409,2,0⟩, ⟨true,701,733,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 397 rank5_4_977 rank5_4_986

theorem rank5_4_988 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,409,2,0⟩, ⟨true,749,797,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 757 749 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,409,2,0⟩, ⟨true,757,797,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_989 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,409,2,0⟩, ⟨true,701,797,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 745 rank5_4_987 rank5_4_988

theorem rank5_4_990 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,415,2,0⟩, ⟨true,701,797,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 409 415 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,409,2,0⟩, ⟨true,701,797,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_4_972 rank5_4_989

theorem rank5_4_991 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,417,449,2,0⟩, ⟨true,701,797,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 419 417 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,449,2,0⟩, ⟨true,701,797,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_992 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,449,2,0⟩, ⟨true,701,797,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 415 rank5_4_990 rank5_4_991

theorem rank5_4_993 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,449,2,0⟩, ⟨true,801,929,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 809 801 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,449,2,0⟩, ⟨true,809,929,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_994 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,449,2,0⟩, ⟨true,701,929,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 797 rank5_4_992 rank5_4_993

theorem rank5_4_995 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,449,2,0⟩, ⟨true,933,1381,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 937 933 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,449,2,0⟩, ⟨true,937,1381,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_996 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,387,449,2,0⟩, ⟨true,701,1381,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 389 387 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,449,2,0⟩, ⟨true,701,1381,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 929 rank5_4_994 rank5_4_995

theorem rank5_4_997 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,449,2,0⟩, ⟨true,701,1381,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 385 rank5_4_971 rank5_4_996

theorem rank5_4_998 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,449,2,0⟩, ⟨true,701,1401,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1381 1401 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,449,2,0⟩, ⟨true,701,1381,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_4_872 rank5_4_997

theorem rank5_4_999 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,449,2,0⟩, ⟨true,1405,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1409 1405 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,449,2,0⟩, ⟨true,1409,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_1000 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,449,2,0⟩, ⟨true,701,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1401 rank5_4_998 rank5_4_999

theorem rank5_4_1001 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,451,673,2,0⟩, ⟨true,701,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 457 451 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,673,2,0⟩, ⟨true,701,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_1002 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,673,2,0⟩, ⟨true,701,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 449 rank5_4_1000 rank5_4_1001

theorem rank5_4_1003 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,673,2,0⟩, ⟨true,349,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 697 rank5_4_871 rank5_4_1002

theorem rank5_4_1004 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,675,0,2,0⟩, ⟨true,677,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 677 675 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,677,0,2,0⟩, ⟨true,677,0,1,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 4 701 678 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,677,0,2,0⟩, ⟨true,701,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_1005 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,0,2,0⟩, ⟨true,349,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 673 rank5_4_1003 rank5_4_1004

theorem rank5_4_1006 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨false,337,0,2,0⟩, ⟨true,349,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 2 rank5_4_766 rank5_4_1005

theorem rank5_4_1007 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,335,0,2,0⟩, ⟨true,337,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 337 335 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,337,0,2,0⟩, ⟨true,337,0,1,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 4 349 338 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,337,0,2,0⟩, ⟨true,349,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 4 rank5_4_765 rank5_4_1006

end OddPerfect.SpoofBox
