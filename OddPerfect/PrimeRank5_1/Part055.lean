module

public import OddPerfect.PrimeRank5_1.Part054
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_1296 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,373,2,0⟩, ⟨false,809,813,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 811 813 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,373,2,0⟩, ⟨false,809,811,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1297 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,373,2,0⟩, ⟨false,815,821,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 821 815 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,373,2,0⟩, ⟨false,821,821,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1298 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,371,373,2,0⟩, ⟨false,809,821,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 373 371 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,373,2,0⟩, ⟨false,809,821,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 813 rank5_1_1296 rank5_1_1297

theorem rank5_1_1299 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,367,373,2,0⟩, ⟨false,805,821,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 809 805 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,367,373,2,0⟩, ⟨false,809,821,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 369 rank5_1_1295 rank5_1_1298

theorem rank5_1_1300 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,367,373,2,0⟩, ⟨false,787,821,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 803 rank5_1_1294 rank5_1_1299

theorem rank5_1_1301 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,367,373,2,0⟩, ⟨false,787,821,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1293 rank5_1_1300

theorem rank5_1_1302 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,367,373,2,0⟩, ⟨false,823,859,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1303 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,367,369,2,0⟩, ⟨false,823,839,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 367 369 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,367,367,2,0⟩, ⟨false,823,839,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1304 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,371,373,2,0⟩, ⟨false,823,839,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 373 371 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,373,2,0⟩, ⟨false,823,839,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1305 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,367,373,2,0⟩, ⟨false,823,839,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 369 rank5_1_1303 rank5_1_1304

theorem rank5_1_1306 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,367,373,2,0⟩, ⟨false,841,859,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 853 841 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,367,373,2,0⟩, ⟨false,853,859,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1307 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,367,373,2,0⟩, ⟨false,823,859,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 839 rank5_1_1305 rank5_1_1306

theorem rank5_1_1308 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,367,373,2,0⟩, ⟨false,823,859,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1302 rank5_1_1307

theorem rank5_1_1309 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,361,373,2,0⟩, ⟨false,787,859,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 367 361 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,367,373,2,0⟩, ⟨false,787,859,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 821 rank5_1_1301 rank5_1_1308

theorem rank5_1_1310 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,373,2,0⟩, ⟨false,783,859,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 787 783 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,373,2,0⟩, ⟨false,787,859,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 359 rank5_1_1292 rank5_1_1309

theorem rank5_1_1311 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,375,2,0⟩, ⟨false,719,859,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 373 375 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,373,2,0⟩, ⟨false,719,859,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 781 rank5_1_1291 rank5_1_1310

theorem rank5_1_1312 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,389,2,0⟩, ⟨false,719,745,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 743 745 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,389,2,0⟩, ⟨false,719,743,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1313 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,389,2,0⟩, ⟨false,751,773,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1314 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,383,2,0⟩, ⟨false,751,761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1315 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,379,2,0⟩, ⟨false,769,773,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1316 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,4⟩, ⟨false,383,383,2,0⟩, ⟨false,769,773,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_1_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1317 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,383,383,2,0⟩, ⟨false,769,773,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_1_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1318 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,383,383,2,0⟩, ⟨false,769,769,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1319 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,383,383,2,0⟩, ⟨false,771,773,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 773 771 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,383,383,2,0⟩, ⟨false,773,773,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
