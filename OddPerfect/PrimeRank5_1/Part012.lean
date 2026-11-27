module

public import OddPerfect.PrimeRank5_1.Part011
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_264 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,43,43,2,0⟩, ⟨false,719,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_265 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,43,43,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 717 rank5_1_263 rank5_1_264

theorem rank5_1_266 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,43,2,0⟩, ⟨false,541,1081,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1069 1081 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,43,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 41 rank5_1_244 rank5_1_265

theorem rank5_1_267 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,2,0⟩, ⟨false,1087,2161,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 757 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_268 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,2,0⟩, ⟨false,1087,1445,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1439 1445 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,2,0⟩, ⟨false,1087,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_269 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,2,2⟩, ⟨false,1447,2161,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 3 4 1723 rank5_1_prime1723 (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,2,2⟩, ⟨false,1723,1723,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_270 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1447,1577,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1571 1577 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1447,1571,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_271 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1579,1733,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_272 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,4⟩, ⟨false,41,41,4,0⟩, ⟨false,1579,1637,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 30941 rank5_1_prime30941 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_273 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,6,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1579,1591,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1583 1591 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,6,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1579,1583,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_274 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,6,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1597,1607,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_1_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_275 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,6,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1597,1597,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_276 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,6,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1599,1601,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1601 1599 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,6,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1601,1601,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_277 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,6,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1597,1601,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1597 rank5_1_275 rank5_1_276

theorem rank5_1_278 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,6,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1603,1607,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1607 1603 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,6,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1607,1607,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_279 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,6,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1597,1607,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1601 rank5_1_277 rank5_1_278

theorem rank5_1_280 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,6,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1593,1607,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1597 1593 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,6,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1597,1607,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 12 rank5_1_274 rank5_1_279

theorem rank5_1_281 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,6,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1579,1607,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1591 rank5_1_273 rank5_1_280

theorem rank5_1_282 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,6,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1609,1637,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_283 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,6,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1579,1637,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1607 rank5_1_281 rank5_1_282

theorem rank5_1_284 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1579,1651,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1637 1651 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1579,1637,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_1_272 rank5_1_283

theorem rank5_1_285 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1653,1733,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1657 1653 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1657,1733,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_286 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1579,1733,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1651 rank5_1_284 rank5_1_285

theorem rank5_1_287 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1579,1733,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_1_271 rank5_1_286

end OddPerfect.SpoofBox
