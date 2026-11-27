module

public import OddPerfect.PrimeRank5_4.Part009
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_216 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,109,109,2,0⟩, ⟨true,797,857,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 825 rank5_4_214 rank5_4_215

theorem rank5_4_217 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,109,109,2,0⟩, ⟨true,797,857,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_4_211 rank5_4_216

theorem rank5_4_218 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,109,2,0⟩, ⟨true,793,857,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 797 793 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,109,2,0⟩, ⟨true,797,857,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 107 rank5_4_210 rank5_4_217

theorem rank5_4_219 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,109,2,0⟩, ⟨true,733,857,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 789 rank5_4_209 rank5_4_218

theorem rank5_4_220 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,109,2,0⟩, ⟨true,733,869,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 857 869 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,109,2,0⟩, ⟨true,733,857,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_4_208 rank5_4_219

theorem rank5_4_221 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,19,19,4,0⟩, ⟨false,107,109,2,0⟩, ⟨true,877,1069,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_4_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_222 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,107,2,0⟩, ⟨true,877,913,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 881 913 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,107,2,0⟩, ⟨true,877,881,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_223 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,107,2,0⟩, ⟨true,917,953,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 929 917 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,107,2,0⟩, ⟨true,929,953,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_224 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,107,2,0⟩, ⟨true,877,953,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 913 rank5_4_222 rank5_4_223

theorem rank5_4_225 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,109,109,2,0⟩, ⟨true,877,953,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_226 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,109,2,0⟩, ⟨true,877,961,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 953 961 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,109,2,0⟩, ⟨true,877,953,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 107 rank5_4_224 rank5_4_225

theorem rank5_4_227 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,109,2,0⟩, ⟨true,965,1069,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 977 965 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,109,2,0⟩, ⟨true,977,1069,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_228 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,109,2,0⟩, ⟨true,877,1069,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 961 rank5_4_226 rank5_4_227

theorem rank5_4_229 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,109,2,0⟩, ⟨true,873,1069,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 877 873 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,109,2,0⟩, ⟨true,877,1069,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_4_221 rank5_4_228

theorem rank5_4_230 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,109,2,0⟩, ⟨true,733,1069,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 869 rank5_4_220 rank5_4_229

theorem rank5_4_231 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,109,2,0⟩, ⟨true,733,1069,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 105 rank5_4_207 rank5_4_230

theorem rank5_4_232 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,109,2,0⟩, ⟨true,721,1069,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 733 721 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,109,2,0⟩, ⟨true,733,1069,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_4_206 rank5_4_231

theorem rank5_4_233 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,109,2,0⟩, ⟨true,541,1069,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 717 rank5_4_205 rank5_4_232

theorem rank5_4_234 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,109,2,0⟩, ⟨true,541,1081,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1069 1081 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,109,2,0⟩, ⟨true,541,1069,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 101 rank5_4_204 rank5_4_233

theorem rank5_4_235 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,101,2,0⟩, ⟨true,1093,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_236 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,101,2,0⟩, ⟨true,1093,1449,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1433 1449 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,101,2,0⟩, ⟨true,1093,1433,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_237 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,1453,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_238 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨true,1453,1737,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1733 1737 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨true,1453,1733,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_239 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨true,1741,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_4_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end OddPerfect.SpoofBox
