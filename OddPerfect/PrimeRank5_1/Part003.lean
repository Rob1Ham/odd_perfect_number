module

public import OddPerfect.PrimeRank5_1.Part002
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_48 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,301,349,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 307 301 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,307,349,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 325 rank5_1_46 rank5_1_47

theorem rank5_1_49 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,263,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 299 rank5_1_37 rank5_1_48

theorem rank5_1_50 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,263,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 5 rank5_1_36 rank5_1_49

theorem rank5_1_51 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,351,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 353 351 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,353,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_52 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,4,0⟩, ⟨false,51,53,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 53 51 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 349 rank5_1_50 rank5_1_51

theorem rank5_1_53 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,53,2,0⟩, ⟨false,263,525,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 523 525 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,53,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 49 rank5_1_35 rank5_1_52

theorem rank5_1_54 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨false,541,1081,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1069 1081 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_55 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,5⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_56 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨false,1087,1237,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_57 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,2⟩, ⟨false,1249,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 37 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_58 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,4,0⟩, ⟨false,1249,1337,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1327 1337 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,4,0⟩, ⟨false,1249,1327,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_59 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,4⟩, ⟨false,47,47,4,0⟩, ⟨false,1361,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 30941 rank5_1_prime30941 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_60 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,6,0⟩, ⟨false,47,47,4,0⟩, ⟨false,1361,1369,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1367 1369 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,6,0⟩, ⟨false,47,47,4,0⟩, ⟨false,1361,1367,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_61 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,6,0⟩, ⟨false,47,47,4,0⟩, ⟨false,1371,1381,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1373 1371 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,6,0⟩, ⟨false,47,47,4,0⟩, ⟨false,1373,1381,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_62 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,6,0⟩, ⟨false,47,47,4,0⟩, ⟨false,1361,1397,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1381 1397 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,6,0⟩, ⟨false,47,47,4,0⟩, ⟨false,1361,1381,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1369 rank5_1_60 rank5_1_61

theorem rank5_1_63 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,6,0⟩, ⟨false,47,47,4,0⟩, ⟨false,1399,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_64 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,6,0⟩, ⟨false,47,47,4,0⟩, ⟨false,1361,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1397 rank5_1_62 rank5_1_63

theorem rank5_1_65 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,4,0⟩, ⟨false,1339,1439,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1361 1339 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,4,0⟩, ⟨false,1361,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_1_59 rank5_1_64

theorem rank5_1_66 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,4,0⟩, ⟨false,1249,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1337 rank5_1_58 rank5_1_65

theorem rank5_1_67 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨false,1239,1439,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1249 1239 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨false,1249,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .exponent 2 rank5_1_57 rank5_1_66

theorem rank5_1_68 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨false,1087,1445,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1439 1445 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨false,1087,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1237 rank5_1_56 rank5_1_67

theorem rank5_1_69 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨false,1447,2161,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_70 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨false,1087,2173,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2161 2173 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨false,1087,2161,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1445 rank5_1_68 rank5_1_69

theorem rank5_1_71 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨false,2175,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2179 2175 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
