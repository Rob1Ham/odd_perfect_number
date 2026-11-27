module

public import OddPerfect.PrimeRank5_4.Part010
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_240 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨true,1741,1913,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_241 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨true,1741,1821,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1801 1821 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨true,1741,1801,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_242 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,2⟩, ⟨true,1861,1913,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 10303 rank5_4_prime10303 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_243 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,4,0⟩, ⟨true,1861,1913,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_244 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨true,1825,1913,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1861 1825 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨true,1861,1913,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .exponent 2 rank5_4_242 rank5_4_243

theorem rank5_4_245 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨true,1741,1913,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1821 rank5_4_241 rank5_4_244

theorem rank5_4_246 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨true,1741,1925,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1913 1925 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨true,1741,1913,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_4_240 rank5_4_245

theorem rank5_4_247 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨true,1929,2161,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1933 1929 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨true,1933,2161,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_248 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨true,1741,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1925 rank5_4_246 rank5_4_247

theorem rank5_4_249 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨true,1741,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 6 rank5_4_239 rank5_4_248

theorem rank5_4_250 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,99,101,2,0⟩, ⟨true,1453,2161,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 101 99 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨true,1453,2161,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1737 rank5_4_238 rank5_4_249

theorem rank5_4_251 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,101,2,0⟩, ⟨true,1453,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 97 rank5_4_237 rank5_4_250

theorem rank5_4_252 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,101,2,0⟩, ⟨true,1093,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1449 rank5_4_236 rank5_4_251

theorem rank5_4_253 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,101,2,0⟩, ⟨true,1093,2185,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2161 2185 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,101,2,0⟩, ⟨true,1093,2161,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_4_235 rank5_4_252

theorem rank5_4_254 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,101,2,0⟩, ⟨true,2213,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_255 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,2213,4421,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_256 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,99,101,2,0⟩, ⟨true,2213,4421,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 101 99 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨true,2213,4421,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_257 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,101,2,0⟩, ⟨true,2213,4425,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 4421 4425 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,101,2,0⟩, ⟨true,2213,4421,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 97 rank5_4_255 rank5_4_256

theorem rank5_4_258 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,4441,8861,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_4_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_259 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,4441,5913,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5897 5913 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,4441,5897,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_260 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,5953,8861,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_261 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,5953,8861,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_262 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,5917,8861,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5953 5917 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,5953,8861,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_4_260 rank5_4_261

theorem rank5_4_263 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,4441,8861,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 5913 rank5_4_259 rank5_4_262

end OddPerfect.SpoofBox
