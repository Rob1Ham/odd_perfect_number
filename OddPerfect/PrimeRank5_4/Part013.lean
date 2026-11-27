module

public import OddPerfect.PrimeRank5_4.Part012
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_288 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,4,0⟩, ⟨true,8893,9473,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_4_268 rank5_4_287

theorem rank5_4_289 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,4,0⟩, ⟨true,9477,10141,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 9497 9477 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,4,0⟩, ⟨true,9497,10141,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_290 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,4,0⟩, ⟨true,8893,10141,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 9473 rank5_4_288 rank5_4_289

theorem rank5_4_291 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,8893,10153,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 10141 10153 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,8893,10141,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .exponent 2 rank5_4_267 rank5_4_290

theorem rank5_4_292 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,10157,11833,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 10169 10157 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,10169,11833,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_293 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,8893,11849,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 11833 11849 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,8893,11833,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 10153 rank5_4_291 rank5_4_292

theorem rank5_4_294 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,11853,17761,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 11897 11853 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,11897,17761,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_295 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,8893,17761,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 11849 rank5_4_293 rank5_4_294

theorem rank5_4_296 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,8893,17785,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 17761 17785 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,8893,17761,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_4_266 rank5_4_295

theorem rank5_4_297 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,17789,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_298 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,8893,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 17785 rank5_4_296 rank5_4_297

theorem rank5_4_299 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,8885,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 8893 8885 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,8893,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_4_265 rank5_4_298

theorem rank5_4_300 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,4441,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 8881 rank5_4_264 rank5_4_299

theorem rank5_4_301 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,99,101,2,0⟩, ⟨true,4441,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 101 99 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨true,4441,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_302 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,101,2,0⟩, ⟨true,4429,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4441 4429 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,101,2,0⟩, ⟨true,4441,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 97 rank5_4_300 rank5_4_301

theorem rank5_4_303 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,101,2,0⟩, ⟨true,2213,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 4425 rank5_4_257 rank5_4_302

theorem rank5_4_304 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,101,2,0⟩, ⟨true,2189,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2213 2189 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,101,2,0⟩, ⟨true,2213,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_4_254 rank5_4_303

theorem rank5_4_305 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,101,2,0⟩, ⟨true,1093,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2185 rank5_4_253 rank5_4_304

theorem rank5_4_306 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,109,2,0⟩, ⟨true,1093,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_307 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,103,2,0⟩, ⟨true,1093,1237,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_308 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,19,19,4,0⟩, ⟨false,103,103,2,0⟩, ⟨true,1249,1433,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_4_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_309 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,103,2,0⟩, ⟨true,1249,1333,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1321 1333 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,103,2,0⟩, ⟨true,1249,1321,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_310 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,103,2,0⟩, ⟨true,1361,1433,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_311 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,103,2,0⟩, ⟨true,1361,1393,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1381 1393 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,103,2,0⟩, ⟨true,1361,1381,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
