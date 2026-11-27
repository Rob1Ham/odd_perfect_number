module

public import OddPerfect.PrimeRank5_2.Part008
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_192 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,1⟩, ⟨false,107,157,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 4 rank5_2_18 rank5_2_191

theorem rank5_2_193 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,1⟩, ⟨false,79,157,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 105 rank5_2_17 rank5_2_192

theorem rank5_2_194 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,1⟩, ⟨false,79,157,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 6 rank5_2_16 rank5_2_193

theorem rank5_2_195 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,1⟩, ⟨false,163,325,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 317 325 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,1⟩, ⟨false,163,317,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_force_base _ 0 4 1093 rank5_2_prime1093 (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,1⟩, ⟨false,163,317,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_196 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,1⟩, ⟨false,327,0,2,0⟩, ⟨false,327,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 331 327 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,1⟩, ⟨false,331,0,2,0⟩, ⟨false,327,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 4 337 332 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,1⟩, ⟨false,331,0,2,0⟩, ⟨false,337,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_197 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,1⟩, ⟨false,163,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 325 rank5_2_195 rank5_2_196

theorem rank5_2_198 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,4⟩, ⟨true,17,17,1,1⟩, ⟨false,163,317,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_199 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,163,211,2,0⟩, ⟨false,263,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_200 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,163,183,2,0⟩, ⟨false,353,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 181 183 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,163,181,2,0⟩, ⟨false,353,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_201 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,191,211,2,0⟩, ⟨false,353,421,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_202 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,191,199,2,0⟩, ⟨false,353,421,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_203 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,211,211,2,0⟩, ⟨false,353,367,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_204 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,1,1⟩, ⟨false,211,211,2,0⟩, ⟨false,373,383,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_2_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_205 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,211,211,2,0⟩, ⟨false,373,383,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_206 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,211,211,2,0⟩, ⟨false,373,377,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 373 377 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,211,211,2,0⟩, ⟨false,373,373,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_207 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,211,211,2,0⟩, ⟨false,379,379,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_208 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,211,211,2,0⟩, ⟨false,381,383,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 383 381 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,211,211,2,0⟩, ⟨false,383,383,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_209 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,211,211,2,0⟩, ⟨false,379,383,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 379 rank5_2_207 rank5_2_208

theorem rank5_2_210 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,211,211,2,0⟩, ⟨false,373,383,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 377 rank5_2_206 rank5_2_209

theorem rank5_2_211 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,211,211,2,0⟩, ⟨false,373,383,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_2_205 rank5_2_210

theorem rank5_2_212 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,211,211,2,0⟩, ⟨false,369,383,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 373 369 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,211,211,2,0⟩, ⟨false,373,383,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_2_204 rank5_2_211

theorem rank5_2_213 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,211,211,2,0⟩, ⟨false,353,383,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 367 rank5_2_203 rank5_2_212

theorem rank5_2_214 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,211,211,2,0⟩, ⟨false,385,421,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 389 385 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,211,211,2,0⟩, ⟨false,389,421,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_215 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,201,211,2,0⟩, ⟨false,353,421,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 211 201 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,211,211,2,0⟩, ⟨false,353,421,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 383 rank5_2_213 rank5_2_214

end OddPerfect.SpoofBox
