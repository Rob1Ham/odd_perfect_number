module

public import OddPerfect.PrimeRank5_4.Part011
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_264 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,4441,8881,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 8861 8881 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,4441,8861,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_4_258 rank5_4_263

theorem rank5_4_265 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,8893,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_4_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_266 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,8893,17761,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_267 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,2⟩, ⟨true,8893,10141,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 3169 rank5_4_prime3169 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_268 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,4,0⟩, ⟨true,8893,9473,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_4_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_269 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,4,0⟩, ⟨true,8893,9473,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 31 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_270 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,4,0⟩, ⟨true,8893,9173,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_271 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,19,19,4,4⟩, ⟨false,97,97,4,0⟩, ⟨true,9181,9473,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 151 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_272 : PrimeCovered (#v[⟨false,3,3,14,14⟩, ⟨false,5,5,10,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨true,9181,9221,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_273 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨true,9181,9197,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 9181 9197 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨true,9181,9181,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 4591 rank5_4_prime4591 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_274 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,10⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨true,9209,9221,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 12207031 rank5_4_prime12207031 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_275 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨true,9209,9213,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 9209 9213 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨true,9209,9209,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 307 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_276 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨true,9217,9221,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 9221 9217 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨true,9221,9221,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 29 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_277 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨true,9209,9221,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 9213 rank5_4_275 rank5_4_276

theorem rank5_4_278 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨true,9201,9221,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 9209 9201 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨true,9209,9221,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 10 rank5_4_274 rank5_4_277

theorem rank5_4_279 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨true,9181,9221,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 9197 rank5_4_273 rank5_4_278

theorem rank5_4_280 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨true,9181,9233,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 9221 9233 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨true,9181,9221,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 14 rank5_4_272 rank5_4_279

theorem rank5_4_281 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨true,9237,9293,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 9241 9237 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨true,9241,9293,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_282 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨true,9181,9321,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 9293 9321 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨true,9181,9293,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 9233 rank5_4_280 rank5_4_281

theorem rank5_4_283 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨true,9325,9473,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 9337 9325 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨true,9337,9473,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_284 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨true,9181,9473,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 9321 rank5_4_282 rank5_4_283

theorem rank5_4_285 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,4,0⟩, ⟨true,9177,9473,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 9181 9177 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,4,0⟩, ⟨true,9181,9473,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_4_271 rank5_4_284

theorem rank5_4_286 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,4,0⟩, ⟨true,8893,9473,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 9173 rank5_4_270 rank5_4_285

theorem rank5_4_287 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,4,0⟩, ⟨true,8893,9473,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_4_269 rank5_4_286

end OddPerfect.SpoofBox
