module

public import OddPerfect.PrimeRank5_2.Part011
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_264 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,223,257,2,0⟩, ⟨false,263,299,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 293 299 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,223,257,2,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_2_250 rank5_2_263

theorem rank5_2_265 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,223,257,2,0⟩, ⟨false,307,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_266 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,223,233,2,0⟩, ⟨false,307,325,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 317 325 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,223,233,2,0⟩, ⟨false,307,317,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_267 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,1,1⟩, ⟨false,223,233,2,0⟩, ⟨false,331,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_2_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_268 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,223,227,2,0⟩, ⟨false,331,339,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 337 339 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,223,227,2,0⟩, ⟨false,331,337,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_269 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,223,227,2,0⟩, ⟨false,347,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_270 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,223,223,2,0⟩, ⟨false,347,347,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_2_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_271 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨true,17,17,1,1⟩, ⟨false,223,223,2,0⟩, ⟨false,347,347,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_272 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,223,223,2,0⟩, ⟨false,347,347,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_273 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,223,223,2,0⟩, ⟨false,347,347,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_2_271 rank5_2_272

theorem rank5_2_274 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,223,223,2,0⟩, ⟨false,347,347,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_2_270 rank5_2_273

theorem rank5_2_275 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,223,223,2,0⟩, ⟨false,349,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_276 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,223,223,2,0⟩, ⟨false,347,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 347 rank5_2_274 rank5_2_275

theorem rank5_2_277 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,225,227,2,0⟩, ⟨false,347,349,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 227 225 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,227,227,2,0⟩, ⟨false,347,349,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_278 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,223,227,2,0⟩, ⟨false,347,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 223 rank5_2_276 rank5_2_277

theorem rank5_2_279 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,223,227,2,0⟩, ⟨false,341,349,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 347 341 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,223,227,2,0⟩, ⟨false,347,349,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_2_269 rank5_2_278

theorem rank5_2_280 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,223,227,2,0⟩, ⟨false,331,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 339 rank5_2_268 rank5_2_279

theorem rank5_2_281 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,229,233,2,0⟩, ⟨false,331,337,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_282 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,229,229,2,0⟩, ⟨false,331,333,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 331 333 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,229,229,2,0⟩, ⟨false,331,331,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_283 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,229,229,2,0⟩, ⟨false,335,337,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 337 335 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,229,229,2,0⟩, ⟨false,337,337,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_284 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,229,229,2,0⟩, ⟨false,331,337,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 333 rank5_2_282 rank5_2_283

theorem rank5_2_285 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,231,233,2,0⟩, ⟨false,331,337,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 233 231 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,233,233,2,0⟩, ⟨false,331,337,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_286 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,229,233,2,0⟩, ⟨false,331,337,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 229 rank5_2_284 rank5_2_285

theorem rank5_2_287 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,229,233,2,0⟩, ⟨false,331,339,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 337 339 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,229,233,2,0⟩, ⟨false,331,337,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_2_281 rank5_2_286

end OddPerfect.SpoofBox
