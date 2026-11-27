module

public import OddPerfect.PrimeRank5_2.Part012
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_288 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,229,233,2,0⟩, ⟨false,341,349,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 347 341 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,229,233,2,0⟩, ⟨false,347,349,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_289 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,229,233,2,0⟩, ⟨false,331,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 339 rank5_2_287 rank5_2_288

theorem rank5_2_290 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,223,233,2,0⟩, ⟨false,331,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 227 rank5_2_280 rank5_2_289

theorem rank5_2_291 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,223,233,2,0⟩, ⟨false,327,349,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 331 327 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,223,233,2,0⟩, ⟨false,331,349,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_2_267 rank5_2_290

theorem rank5_2_292 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,223,237,2,0⟩, ⟨false,307,349,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 233 237 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,223,233,2,0⟩, ⟨false,307,349,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 325 rank5_2_266 rank5_2_291

theorem rank5_2_293 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,1,1⟩, ⟨false,239,241,2,0⟩, ⟨false,307,317,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_2_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_294 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,239,241,2,0⟩, ⟨false,307,311,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_295 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,239,241,2,0⟩, ⟨false,307,307,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_296 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,239,239,2,0⟩, ⟨false,311,311,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_297 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,241,241,2,0⟩, ⟨false,311,311,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_298 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,239,241,2,0⟩, ⟨false,309,311,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 311 309 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,239,241,2,0⟩, ⟨false,311,311,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 239 rank5_2_296 rank5_2_297

theorem rank5_2_299 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,239,241,2,0⟩, ⟨false,307,311,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 307 rank5_2_295 rank5_2_298

theorem rank5_2_300 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,239,241,2,0⟩, ⟨false,307,311,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_2_294 rank5_2_299

theorem rank5_2_301 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,239,241,2,0⟩, ⟨false,313,317,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_302 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,239,239,2,0⟩, ⟨false,313,313,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_303 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,241,241,2,0⟩, ⟨false,313,313,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_304 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,239,241,2,0⟩, ⟨false,313,313,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 239 rank5_2_302 rank5_2_303

theorem rank5_2_305 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,239,241,2,0⟩, ⟨false,315,317,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 317 315 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,239,241,2,0⟩, ⟨false,317,317,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_306 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,239,241,2,0⟩, ⟨false,313,317,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 313 rank5_2_304 rank5_2_305

theorem rank5_2_307 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,239,241,2,0⟩, ⟨false,313,317,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_2_301 rank5_2_306

theorem rank5_2_308 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,239,241,2,0⟩, ⟨false,307,317,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 311 rank5_2_300 rank5_2_307

theorem rank5_2_309 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,239,247,2,0⟩, ⟨false,307,317,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 241 247 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,239,241,2,0⟩, ⟨false,307,317,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_2_293 rank5_2_308

theorem rank5_2_310 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,249,257,2,0⟩, ⟨false,307,317,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 251 249 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,251,257,2,0⟩, ⟨false,307,317,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_311 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,239,257,2,0⟩, ⟨false,307,325,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 317 325 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,239,257,2,0⟩, ⟨false,307,317,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 247 rank5_2_309 rank5_2_310

end OddPerfect.SpoofBox
