module

public import OddPerfect.PrimeRank5_3.Part010
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_3_240 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨true,277,541,1,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 307 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_241 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_242 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,281,1,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_243 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,285,293,1,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 293 285 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,293,293,1,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_244 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 281 rank5_3_242 rank5_3_243

theorem rank5_3_245 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,309,1,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 293 309 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_3_241 rank5_3_244

theorem rank5_3_246 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,353,1,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_247 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,365,1,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 353 365 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,353,1,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 309 rank5_3_245 rank5_3_246

theorem rank5_3_248 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,369,541,1,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 373 369 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,541,1,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_249 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,541,1,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 365 rank5_3_247 rank5_3_248

theorem rank5_3_250 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨true,277,553,1,0⟩, ⟨false,281,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 541 553 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨true,277,541,1,0⟩, ⟨false,281,0,2,0⟩] : Vector Slot 5)
  apply covered_force_base _ 0 4 1093 (by norm_num) (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨true,277,541,1,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 2 rank5_3_240 rank5_3_249

theorem rank5_3_251 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨true,557,0,1,0⟩, ⟨false,557,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 563 558 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨true,557,0,1,0⟩, ⟨false,563,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_252 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨true,277,0,1,0⟩, ⟨false,281,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 553 rank5_3_250 rank5_3_251

theorem rank5_3_253 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨true,277,0,1,0⟩, ⟨false,281,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 4 rank5_3_239 rank5_3_252

theorem rank5_3_254 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨true,277,0,1,0⟩, ⟨false,281,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_255 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨true,277,0,1,0⟩, ⟨false,277,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 281 278 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨true,277,0,1,0⟩, ⟨false,281,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 17 rank5_3_253 rank5_3_254

theorem rank5_3_256 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨true,137,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 273 rank5_3_238 rank5_3_255

theorem rank5_3_257 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,4⟩, ⟨false,17,17,2,0⟩, ⟨true,137,269,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_258 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨true,137,269,1,0⟩, ⟨false,263,525,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 523 525 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨true,137,269,1,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_259 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨true,137,181,1,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_260 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨true,193,269,1,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 307 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_261 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,193,269,1,0⟩, ⟨false,541,1081,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1069 1081 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,193,269,1,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_262 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,193,221,1,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 197 221 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,193,197,1,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_263 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,229,269,1,0⟩, ⟨false,1087,2173,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2161 2173 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,229,269,1,0⟩, ⟨false,1087,2161,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
