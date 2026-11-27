module

public import OddPerfect.PrimeRank5_2.Part006
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_144 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,151,2,0⟩, ⟨false,1087,1237,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_145 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,1,1⟩, ⟨false,149,151,2,0⟩, ⟨false,1249,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_2_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_146 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,151,2,0⟩, ⟨false,1249,1337,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1327 1337 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,151,2,0⟩, ⟨false,1249,1327,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_147 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,151,2,0⟩, ⟨false,1361,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_148 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,149,2,0⟩, ⟨false,1361,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_149 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,151,151,2,0⟩, ⟨false,1361,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_150 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,151,2,0⟩, ⟨false,1361,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 149 rank5_2_148 rank5_2_149

theorem rank5_2_151 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,151,2,0⟩, ⟨false,1339,1439,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1361 1339 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,151,2,0⟩, ⟨false,1361,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_2_147 rank5_2_150

theorem rank5_2_152 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,151,2,0⟩, ⟨false,1249,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1337 rank5_2_146 rank5_2_151

theorem rank5_2_153 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,151,2,0⟩, ⟨false,1239,1439,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1249 1239 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,151,2,0⟩, ⟨false,1249,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_2_145 rank5_2_152

theorem rank5_2_154 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,151,2,0⟩, ⟨false,1087,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1237 rank5_2_144 rank5_2_153

theorem rank5_2_155 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,153,157,2,0⟩, ⟨false,1087,1439,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 157 153 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,0⟩, ⟨false,1087,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_156 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,157,2,0⟩, ⟨false,1087,1445,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1439 1445 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,157,2,0⟩, ⟨false,1087,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 151 rank5_2_154 rank5_2_155

theorem rank5_2_157 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,1,1⟩, ⟨false,149,151,2,0⟩, ⟨false,1447,1733,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_2_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_158 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,151,2,0⟩, ⟨false,1447,1571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_159 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,149,2,0⟩, ⟨false,1447,1505,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1499 1505 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,149,2,0⟩, ⟨false,1447,1499,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_160 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,149,2,0⟩, ⟨false,1511,1539,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1531 1539 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,149,2,0⟩, ⟨false,1511,1531,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_161 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,149,2,0⟩, ⟨false,1543,1553,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_2_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_162 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨true,17,17,1,1⟩, ⟨false,149,149,2,0⟩, ⟨false,1543,1553,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_163 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,149,2,2⟩, ⟨false,1543,1553,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_164 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,149,4,0⟩, ⟨false,1543,1547,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1543 1547 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,149,4,0⟩, ⟨false,1543,1543,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_165 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,149,4,0⟩, ⟨false,1549,1553,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_166 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,149,4,0⟩, ⟨false,1543,1553,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1547 rank5_2_164 rank5_2_165

theorem rank5_2_167 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,149,2,0⟩, ⟨false,1543,1553,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .exponent 2 rank5_2_163 rank5_2_166

end OddPerfect.SpoofBox
