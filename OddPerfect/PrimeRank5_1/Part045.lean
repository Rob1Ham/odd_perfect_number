module

public import OddPerfect.PrimeRank5_1.Part044
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_1056 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨false,34939,46585,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 46573 46585 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨false,34939,46573,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1057 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,4⟩, ⟨false,257,257,2,0⟩, ⟨false,46589,69877,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_1_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1058 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨false,46589,69877,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_1_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1059 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨false,46589,55903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1060 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨false,55921,62123,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 62119 62123 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨false,55921,62119,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1061 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,9⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨false,62129,65761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1062 : PrimeCovered (#v[⟨false,3,3,14,14⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨false,62129,65761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1063 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,2⟩, ⟨false,62129,65761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 61 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1064 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨false,62129,63893,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 63863 63893 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨false,62129,63863,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1065 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨false,63901,64817,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1066 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨false,64849,65301,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 65293 65301 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨false,64849,65293,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1067 : PrimeCovered (#v[⟨false,3,3,16,16⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨false,65309,65761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 1871 rank5_1_prime1871 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1068 : PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨false,65309,65533,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 65521 65533 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨false,65309,65521,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1069 : PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨false,65535,65761,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 65537 65535 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨false,65537,65761,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1070 : PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨false,65309,65761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 65533 rank5_1_1068 rank5_1_1069

theorem rank5_1_1071 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨false,65303,65761,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 65309 65303 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨false,65309,65761,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 16 rank5_1_1067 rank5_1_1070

theorem rank5_1_1072 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨false,64819,65761,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 64849 64819 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨false,64849,65761,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 65301 rank5_1_1066 rank5_1_1071

theorem rank5_1_1073 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨false,63895,65761,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 63901 63895 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨false,63901,65761,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 64817 rank5_1_1065 rank5_1_1072

theorem rank5_1_1074 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨false,62129,65761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 63893 rank5_1_1064 rank5_1_1073

theorem rank5_1_1075 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨false,62129,65761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .exponent 2 rank5_1_1063 rank5_1_1074

theorem rank5_1_1076 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨false,62129,65761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 14 rank5_1_1062 rank5_1_1075

theorem rank5_1_1077 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨false,62129,65775,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 65761 65775 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨false,62129,65761,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 9 rank5_1_1061 rank5_1_1076

theorem rank5_1_1078 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨false,65777,69877,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1079 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨false,62125,69877,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 62129 62125 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨false,62129,69877,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 65775 rank5_1_1077 rank5_1_1078

end OddPerfect.SpoofBox
