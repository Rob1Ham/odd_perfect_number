module

public import OddPerfect.PrimeRank5_3.Part008
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_3_192 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨true,113,113,1,1⟩, ⟨false,595,613,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 599 595 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨true,113,113,1,1⟩, ⟨false,599,613,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_3_188 rank5_3_191

theorem rank5_3_193 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨true,113,113,1,1⟩, ⟨false,577,613,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 593 rank5_3_187 rank5_3_192

theorem rank5_3_194 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,113,113,1,1⟩, ⟨false,575,613,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 577 575 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,113,113,1,1⟩, ⟨false,577,613,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_3_186 rank5_3_193

theorem rank5_3_195 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,113,113,1,1⟩, ⟨false,541,613,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 573 rank5_3_185 rank5_3_194

theorem rank5_3_196 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,113,113,5,0⟩, ⟨false,541,613,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_197 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,113,113,1,0⟩, ⟨false,541,613,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .exponent 1 rank5_3_195 rank5_3_196

theorem rank5_3_198 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,109,113,1,0⟩, ⟨false,541,613,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 109 rank5_3_184 rank5_3_197

theorem rank5_3_199 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,109,109,1,0⟩, ⟨false,617,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_200 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,113,113,1,1⟩, ⟨false,617,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_201 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,19,19,4,0⟩, ⟨true,113,113,5,0⟩, ⟨false,617,659,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_202 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨true,113,113,5,0⟩, ⟨false,617,631,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_203 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨true,113,113,5,0⟩, ⟨false,617,631,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_204 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨true,113,113,5,0⟩, ⟨false,617,637,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 631 637 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨true,113,113,5,0⟩, ⟨false,617,631,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_3_202 rank5_3_203

theorem rank5_3_205 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨true,113,113,5,0⟩, ⟨false,639,659,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 641 639 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨true,113,113,5,0⟩, ⟨false,641,659,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_206 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨true,113,113,5,0⟩, ⟨false,617,659,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 637 rank5_3_204 rank5_3_205

theorem rank5_3_207 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,113,113,5,0⟩, ⟨false,617,659,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 6 rank5_3_201 rank5_3_206

theorem rank5_3_208 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,113,113,5,0⟩, ⟨false,661,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_209 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,113,113,5,0⟩, ⟨false,617,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 659 rank5_3_207 rank5_3_208

theorem rank5_3_210 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,113,113,1,0⟩, ⟨false,617,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .exponent 1 rank5_3_200 rank5_3_209

theorem rank5_3_211 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,109,113,1,0⟩, ⟨false,615,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 617 615 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,109,113,1,0⟩, ⟨false,617,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 109 rank5_3_199 rank5_3_210

theorem rank5_3_212 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,109,113,1,0⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 613 rank5_3_198 rank5_3_211

theorem rank5_3_213 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,109,113,1,0⟩, ⟨false,541,717,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 709 717 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,109,113,1,0⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_3_183 rank5_3_212

theorem rank5_3_214 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,109,113,1,0⟩, ⟨false,719,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_215 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,109,109,1,0⟩, ⟨false,719,859,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end OddPerfect.SpoofBox
