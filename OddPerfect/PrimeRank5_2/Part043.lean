module

public import OddPerfect.PrimeRank5_2.Part042
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_1008 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,351,373,2,0⟩, ⟨false,1087,1327,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 353 351 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,373,2,0⟩, ⟨false,1087,1327,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1009 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,373,2,0⟩, ⟨false,1079,1327,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1087 1079 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,373,2,0⟩, ⟨false,1087,1327,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 349 rank5_2_1007 rank5_2_1008

theorem rank5_2_1010 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,373,2,0⟩, ⟨false,897,1327,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 907 897 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,373,2,0⟩, ⟨false,907,1327,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1077 rank5_2_984 rank5_2_1009

theorem rank5_2_1011 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,377,2,0⟩, ⟨false,677,1327,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 373 377 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,373,2,0⟩, ⟨false,677,1327,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 895 rank5_2_931 rank5_2_1010

theorem rank5_2_1012 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,5,0⟩, ⟨false,379,401,2,0⟩, ⟨false,677,761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_2_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_1013 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,389,2,0⟩, ⟨false,677,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1014 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,397,401,2,0⟩, ⟨false,677,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_1015 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,397,401,2,0⟩, ⟨false,677,691,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1016 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,397,397,2,0⟩, ⟨false,701,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1017 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,401,401,2,0⟩, ⟨false,701,703,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 701 703 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,401,401,2,0⟩, ⟨false,701,701,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1018 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,401,401,2,0⟩, ⟨false,705,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 709 705 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,401,401,2,0⟩, ⟨false,709,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1019 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,399,401,2,0⟩, ⟨false,701,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 401 399 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,401,401,2,0⟩, ⟨false,701,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 703 rank5_2_1017 rank5_2_1018

theorem rank5_2_1020 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,397,401,2,0⟩, ⟨false,693,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 701 693 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,397,401,2,0⟩, ⟨false,701,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 397 rank5_2_1016 rank5_2_1019

theorem rank5_2_1021 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,397,401,2,0⟩, ⟨false,677,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 691 rank5_2_1015 rank5_2_1020

theorem rank5_2_1022 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,391,401,2,0⟩, ⟨false,677,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 397 391 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,397,401,2,0⟩, ⟨false,677,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_2_1014 rank5_2_1021

theorem rank5_2_1023 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,401,2,0⟩, ⟨false,677,715,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 709 715 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,401,2,0⟩, ⟨false,677,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 389 rank5_2_1013 rank5_2_1022

theorem rank5_2_1024 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,389,2,0⟩, ⟨false,719,761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_1025 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,389,2,0⟩, ⟨false,719,739,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1026 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,383,2,0⟩, ⟨false,743,761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1027 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,389,389,2,0⟩, ⟨false,743,745,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 743 745 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,389,389,2,0⟩, ⟨false,743,743,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1028 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,389,389,2,0⟩, ⟨false,747,751,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 751 747 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,389,389,2,0⟩, ⟨false,751,751,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1029 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,389,389,2,0⟩, ⟨false,743,751,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 745 rank5_2_1027 rank5_2_1028

theorem rank5_2_1030 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,389,389,2,0⟩, ⟨false,753,761,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 757 753 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,389,389,2,0⟩, ⟨false,757,761,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1031 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,385,389,2,0⟩, ⟨false,743,761,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 389 385 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,389,389,2,0⟩, ⟨false,743,761,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 751 rank5_2_1029 rank5_2_1030

end OddPerfect.SpoofBox
