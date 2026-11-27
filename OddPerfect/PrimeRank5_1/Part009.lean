module

public import OddPerfect.PrimeRank5_1.Part008
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_192 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,89,89,2,0⟩, ⟨false,327,349,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 331 327 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,89,89,2,0⟩, ⟨false,331,349,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 339 rank5_1_184 rank5_1_191

theorem rank5_1_193 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,89,89,2,0⟩, ⟨false,301,349,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 307 301 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,89,89,2,0⟩, ⟨false,307,349,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 325 rank5_1_183 rank5_1_192

theorem rank5_1_194 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,85,89,2,0⟩, ⟨false,263,349,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 89 85 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,89,89,2,0⟩, ⟨false,263,349,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 299 rank5_1_182 rank5_1_193

theorem rank5_1_195 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,89,2,0⟩, ⟨false,263,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 83 rank5_1_181 rank5_1_194

theorem rank5_1_196 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,83,2,0⟩, ⟨false,353,421,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_197 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,79,2,0⟩, ⟨false,431,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_198 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,83,83,2,0⟩, ⟨false,431,471,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 467 471 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,83,83,2,0⟩, ⟨false,431,467,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_199 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,4⟩, ⟨false,83,83,2,0⟩, ⟨false,479,499,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 3221 rank5_1_prime3221 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_200 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,83,83,2,0⟩, ⟨false,479,487,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_201 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,83,83,2,0⟩, ⟨false,489,499,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 491 489 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,83,83,2,0⟩, ⟨false,491,499,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_202 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,83,83,2,0⟩, ⟨false,479,499,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 487 rank5_1_200 rank5_1_201

theorem rank5_1_203 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,83,83,2,0⟩, ⟨false,479,499,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 4 rank5_1_199 rank5_1_202

theorem rank5_1_204 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,83,83,2,0⟩, ⟨false,501,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 503 501 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,83,83,2,0⟩, ⟨false,503,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_205 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,83,83,2,0⟩, ⟨false,473,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 479 473 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,83,83,2,0⟩, ⟨false,479,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 499 rank5_1_203 rank5_1_204

theorem rank5_1_206 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,81,83,2,0⟩, ⟨false,431,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 83 81 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,83,83,2,0⟩, ⟨false,431,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 471 rank5_1_198 rank5_1_205

theorem rank5_1_207 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,83,2,0⟩, ⟨false,423,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 431 423 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,83,2,0⟩, ⟨false,431,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 79 rank5_1_197 rank5_1_206

theorem rank5_1_208 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,83,2,0⟩, ⟨false,353,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 421 rank5_1_196 rank5_1_207

theorem rank5_1_209 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,85,89,2,0⟩, ⟨false,353,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 89 85 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,89,89,2,0⟩, ⟨false,353,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_210 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,89,2,0⟩, ⟨false,351,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 353 351 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,89,2,0⟩, ⟨false,353,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 83 rank5_1_208 rank5_1_209

theorem rank5_1_211 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,89,2,0⟩, ⟨false,263,525,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 523 525 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,89,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 349 rank5_1_195 rank5_1_210

theorem rank5_1_212 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,79,2,0⟩, ⟨false,541,613,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_213 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,79,2,0⟩, ⟨false,617,659,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_214 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,79,2,0⟩, ⟨false,661,683,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_215 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,4⟩, ⟨false,79,79,2,0⟩, ⟨false,691,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 3221 rank5_1_prime3221 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end OddPerfect.SpoofBox
