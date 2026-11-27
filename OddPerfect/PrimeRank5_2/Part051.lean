module

public import OddPerfect.PrimeRank5_2.Part050
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_1200 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,29,41,1,0⟩, ⟨false,31,41,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 37 40 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,29,37,1,0⟩, ⟨false,31,41,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 35 rank5_2_1144 rank5_2_1199

theorem rank5_2_1201 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,29,53,1,0⟩, ⟨false,43,61,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1202 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,29,53,1,0⟩, ⟨false,31,61,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 41 rank5_2_1200 rank5_2_1201

theorem rank5_2_1203 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,29,53,1,0⟩, ⟨false,63,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 67 63 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,29,53,1,0⟩, ⟨false,67,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1204 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,29,57,1,0⟩, ⟨false,31,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 53 57 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,29,53,1,0⟩, ⟨false,31,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 61 rank5_2_1202 rank5_2_1203

theorem rank5_2_1205 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,61,0,1,0⟩, ⟨false,61,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 67 62 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,61,0,1,0⟩, ⟨false,67,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1206 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,29,0,1,0⟩, ⟨false,31,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 57 rank5_2_1204 rank5_2_1205

theorem rank5_2_1207 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨true,29,0,1,0⟩, ⟨false,31,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 4 rank5_2_1143 rank5_2_1206

theorem rank5_2_1208 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,31,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 2 rank5_2_1142 rank5_2_1207

theorem rank5_2_1209 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,31,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1210 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,29,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 31 30 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,31,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .base 5 rank5_2_1208 rank5_2_1209

theorem rank5_2_1211 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,9,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,17,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 1 7 9 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,17,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 25 rank5_2_1141 rank5_2_1210

theorem rank5_2_1212 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,11,0,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,17,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1213 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,0,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,17,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .base 9 rank5_2_1211 rank5_2_1212

theorem rank5_2_1214 : PrimeCovered (#v[⟨false,3,3,2,0⟩, ⟨false,3,0,2,0⟩, ⟨true,5,0,1,0⟩, ⟨false,3,0,2,0⟩, ⟨false,258,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 1 5 4 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,0⟩, ⟨false,5,0,2,0⟩, ⟨true,5,0,1,0⟩, ⟨false,3,0,2,0⟩, ⟨false,258,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 2 13 6 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,0⟩, ⟨false,5,0,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,3,0,2,0⟩, ⟨false,258,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 17 14 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,0⟩, ⟨false,5,0,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,17,0,2,0⟩, ⟨false,258,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 4 263 258 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,0⟩, ⟨false,5,0,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,17,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 2 rank5_2_2 rank5_2_1213

theorem closed_prime_5_2 : PrimeCovered (primeInitial (2 : Fin 5)) := rank5_2_1214

end OddPerfect.SpoofBox
