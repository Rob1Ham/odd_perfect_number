module

public import OddPerfect.PrimeRank5_1.Part051
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_1224 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,313,2,0⟩, ⟨false,1579,1733,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1225 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,303,313,2,0⟩, ⟨false,1447,1733,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 307 303 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,313,2,0⟩, ⟨false,1447,1733,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1577 rank5_1_1223 rank5_1_1224

theorem rank5_1_1226 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,313,2,0⟩, ⟨false,1447,1733,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 301 rank5_1_1214 rank5_1_1225

theorem rank5_1_1227 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1741,1927,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1913 1927 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1741,1913,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1228 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1931,2161,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1229 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1931,1983,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1979 1983 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1931,1979,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1230 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1987,2011,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1231 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,4⟩, ⟨false,293,293,2,0⟩, ⟨false,2017,2039,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_1_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1232 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2017,2039,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_1_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1233 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2017,2021,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2017 2021 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2017,2017,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1234 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2023,2027,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2027 2023 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2027,2027,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1235 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2017,2027,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2021 rank5_1_1233 rank5_1_1234

theorem rank5_1_1236 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2029,2039,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1237 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2017,2039,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2027 rank5_1_1235 rank5_1_1236

theorem rank5_1_1238 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2017,2039,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_1_1232 rank5_1_1237

theorem rank5_1_1239 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2013,2039,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2017 2013 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2017,2039,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_1_1231 rank5_1_1238

theorem rank5_1_1240 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1985,2039,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1987 1985 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1987,2039,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 2011 rank5_1_1230 rank5_1_1239

theorem rank5_1_1241 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1931,2039,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1983 rank5_1_1229 rank5_1_1240

theorem rank5_1_1242 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2041,2161,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2053 2041 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2053,2161,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1243 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1931,2161,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2039 rank5_1_1241 rank5_1_1242

theorem rank5_1_1244 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1929,2161,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1931 1929 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1931,2161,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1228 rank5_1_1243

theorem rank5_1_1245 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,301,2,0⟩, ⟨false,1741,2161,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 293 301 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1741,2161,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1927 rank5_1_1227 rank5_1_1244

theorem rank5_1_1246 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,303,313,2,0⟩, ⟨false,1741,2161,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 307 303 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,313,2,0⟩, ⟨false,1741,2161,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1247 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,313,2,0⟩, ⟨false,1735,2161,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1741 1735 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,313,2,0⟩, ⟨false,1741,2161,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 301 rank5_1_1245 rank5_1_1246

end OddPerfect.SpoofBox
