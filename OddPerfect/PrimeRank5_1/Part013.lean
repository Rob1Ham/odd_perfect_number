module

public import OddPerfect.PrimeRank5_1.Part012
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_288 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1447,1733,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1577 rank5_1_270 rank5_1_287

theorem rank5_1_289 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1735,2161,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1741 1735 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1741,2161,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_290 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,4,0⟩, ⟨false,1447,2161,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1733 rank5_1_288 rank5_1_289

theorem rank5_1_291 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,2,0⟩, ⟨false,1447,2161,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .exponent 2 rank5_1_269 rank5_1_290

theorem rank5_1_292 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,2,0⟩, ⟨false,1087,2161,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1445 rank5_1_268 rank5_1_291

theorem rank5_1_293 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,2,0⟩, ⟨false,1087,2173,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2161 2173 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,2,0⟩, ⟨false,1087,2161,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_1_267 rank5_1_292

theorem rank5_1_294 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,2,0⟩, ⟨false,2175,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2179 2175 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_295 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2173 rank5_1_293 rank5_1_294

theorem rank5_1_296 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,43,43,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_297 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,43,2,0⟩, ⟨false,1083,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1087 1083 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,43,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 41 rank5_1_295 rank5_1_296

theorem rank5_1_298 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,43,2,0⟩, ⟨false,527,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 541 527 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,43,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1081 rank5_1_266 rank5_1_297

theorem rank5_1_299 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,45,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 43 45 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,43,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 525 rank5_1_243 rank5_1_298

theorem rank5_1_300 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,47,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_301 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 45 rank5_1_299 rank5_1_300

theorem rank5_1_302 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,2,0⟩, ⟨false,41,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 2 rank5_1_242 rank5_1_301

theorem rank5_1_303 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,2,0⟩, ⟨false,41,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 6 rank5_1_241 rank5_1_302

theorem rank5_1_304 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,13,2,0⟩, ⟨false,39,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 41 39 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,13,2,0⟩, ⟨false,41,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 11 rank5_1_240 rank5_1_303

theorem rank5_1_305 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,13,2,0⟩, ⟨false,29,57,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 53 57 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,13,2,0⟩, ⟨false,29,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 37 rank5_1_239 rank5_1_304

theorem rank5_1_306 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,2,2⟩, ⟨false,59,113,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 7 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_1_307 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,59,77,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 73 77 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,59,73,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_308 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,91,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 89 91 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,89,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_309 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,97,103,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_310 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,105,113,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 107 105 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,113,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_311 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,93,113,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 97 93 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,97,113,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 103 rank5_1_309 rank5_1_310

end OddPerfect.SpoofBox
