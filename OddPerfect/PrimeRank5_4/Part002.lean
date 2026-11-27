module

public import OddPerfect.PrimeRank5_4.Part001
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_24 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨true,333,353,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 337 333 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨true,337,353,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_25 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨true,309,353,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 313 309 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨true,313,353,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 329 rank5_4_23 rank5_4_24

theorem rank5_4_26 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨true,269,353,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 305 rank5_4_14 rank5_4_25

theorem rank5_4_27 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨true,357,521,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 373 357 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨true,373,521,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_28 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,51,53,2,0⟩, ⟨true,269,521,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 53 51 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨true,269,521,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 353 rank5_4_26 rank5_4_27

theorem rank5_4_29 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,53,2,0⟩, ⟨true,269,537,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 521 537 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,53,2,0⟩, ⟨true,269,521,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 49 rank5_4_13 rank5_4_28

theorem rank5_4_30 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨true,541,1081,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1069 1081 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨true,541,1069,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_31 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨true,1093,1237,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_32 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,6⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨true,1249,1433,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_4_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_33 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,2⟩, ⟨true,1249,1433,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 37 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_34 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,4,0⟩, ⟨true,1249,1333,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1321 1333 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,4,0⟩, ⟨true,1249,1321,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_35 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,4,4⟩, ⟨false,47,47,4,0⟩, ⟨true,1361,1433,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 30941 rank5_4_prime30941 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_36 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,6,0⟩, ⟨false,47,47,4,0⟩, ⟨true,1361,1369,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1361 1369 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,6,0⟩, ⟨false,47,47,4,0⟩, ⟨true,1361,1361,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 227 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_37 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,6,0⟩, ⟨false,47,47,4,0⟩, ⟨true,1373,1381,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_38 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,6,0⟩, ⟨false,47,47,4,0⟩, ⟨true,1361,1393,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1381 1393 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,6,0⟩, ⟨false,47,47,4,0⟩, ⟨true,1361,1381,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1369 rank5_4_36 rank5_4_37

theorem rank5_4_39 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,6,0⟩, ⟨false,47,47,4,0⟩, ⟨true,1397,1433,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1409 1397 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,6,0⟩, ⟨false,47,47,4,0⟩, ⟨true,1409,1433,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_40 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,6,0⟩, ⟨false,47,47,4,0⟩, ⟨true,1361,1433,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1393 rank5_4_38 rank5_4_39

theorem rank5_4_41 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,4,0⟩, ⟨true,1337,1433,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1361 1337 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,4,0⟩, ⟨true,1361,1433,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_4_35 rank5_4_40

theorem rank5_4_42 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,4,0⟩, ⟨true,1249,1433,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1333 rank5_4_34 rank5_4_41

theorem rank5_4_43 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨true,1249,1433,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .exponent 2 rank5_4_33 rank5_4_42

theorem rank5_4_44 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨true,1241,1433,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1249 1241 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨true,1249,1433,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_4_32 rank5_4_43

theorem rank5_4_45 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨true,1093,1449,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1433 1449 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨true,1093,1433,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1237 rank5_4_31 rank5_4_44

theorem rank5_4_46 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨true,1453,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_47 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨true,1093,2185,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2161 2185 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨true,1093,2161,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1449 rank5_4_45 rank5_4_46

end OddPerfect.SpoofBox
