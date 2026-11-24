module

public import OddPerfect.TothTrillion.Part11
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case220 : Closed 1000000 15 403 167 := by
  apply closed_split (a:=173) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<167) h)
    have hnum : 1000000 < 15*167^3 := by decide +kernel
    omega
  interval_cases e
  · exact case219
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case221 : Closed 1000000 15 403 163 := by
  apply closed_split (a:=167) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<163) h)
    have hnum : 1000000 < 15*163^3 := by decide +kernel
    omega
  interval_cases e
  · exact case220
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case222 : Closed 1000000 15 403 157 := by
  apply closed_split (a:=163) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<157) h)
    have hnum : 1000000 < 15*157^3 := by decide +kernel
    omega
  interval_cases e
  · exact case221
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case223 : Closed 1000000 15 403 151 := by
  apply closed_split (a:=157) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<151) h)
    have hnum : 1000000 < 15*151^3 := by decide +kernel
    omega
  interval_cases e
  · exact case222
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case224 : Closed 1000000 15 403 149 := by
  apply closed_split (a:=151) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<149) h)
    have hnum : 1000000 < 15*149^3 := by decide +kernel
    omega
  interval_cases e
  · exact case223
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case225 : Closed 1000000 15 403 139 := by
  apply closed_split (a:=149) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<139) h)
    have hnum : 1000000 < 15*139^3 := by decide +kernel
    omega
  interval_cases e
  · exact case224
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case226 : Closed 1000000 15 403 137 := by
  apply closed_split (a:=139) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<137) h)
    have hnum : 1000000 < 15*137^3 := by decide +kernel
    omega
  interval_cases e
  · exact case225
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case227 : Closed 1000000 15 403 131 := by
  apply closed_split (a:=137) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<131) h)
    have hnum : 1000000 < 15*131^3 := by decide +kernel
    omega
  interval_cases e
  · exact case226
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case228 : Closed 1000000 15 403 127 := by
  apply closed_split (a:=131) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<127) h)
    have hnum : 1000000 < 15*127^3 := by decide +kernel
    omega
  interval_cases e
  · exact case227
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case229 : Closed 1000000 15 403 113 := by
  apply closed_split (a:=127) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<113) h)
    have hnum : 1000000 < 15*113^3 := by decide +kernel
    omega
  interval_cases e
  · exact case228
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case230 : Closed 1000000 15 403 109 := by
  apply closed_split (a:=113) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<109) h)
    have hnum : 1000000 < 15*109^3 := by decide +kernel
    omega
  interval_cases e
  · exact case229
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case231 : Closed 1000000 15 403 107 := by
  apply closed_split (a:=109) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<107) h)
    have hnum : 1000000 < 15*107^3 := by decide +kernel
    omega
  interval_cases e
  · exact case230
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case232 : Closed 1000000 15 403 103 := by
  apply closed_split (a:=107) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<103) h)
    have hnum : 1000000 < 15*103^3 := by decide +kernel
    omega
  interval_cases e
  · exact case231
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case233 : Closed 1000000 15 403 101 := by
  apply closed_split (a:=103) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<101) h)
    have hnum : 1000000 < 15*101^3 := by decide +kernel
    omega
  interval_cases e
  · exact case232
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case234 : Closed 1000000 15 403 97 := by
  apply closed_split (a:=101) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<97) h)
    have hnum : 1000000 < 15*97^3 := by decide +kernel
    omega
  interval_cases e
  · exact case233
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case235 : Closed 1000000 15 403 89 := by
  apply closed_split (a:=97) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<89) h)
    have hnum : 1000000 < 15*89^3 := by decide +kernel
    omega
  interval_cases e
  · exact case234
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case236 : Closed 1000000 15 403 83 := by
  apply closed_split (a:=89) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<83) h)
    have hnum : 1000000 < 15*83^3 := by decide +kernel
    omega
  interval_cases e
  · exact case235
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case237 : Closed 1000000 15 403 79 := by
  apply closed_split (a:=83) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<79) h)
    have hnum : 1000000 < 15*79^3 := by decide +kernel
    omega
  interval_cases e
  · exact case236
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case238 : Closed 1000000 15 403 73 := by
  apply closed_split (a:=79) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<73) h)
    have hnum : 1000000 < 15*73^3 := by decide +kernel
    omega
  interval_cases e
  · exact case237
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case239 : Closed 1000000 15 403 71 := by
  apply closed_split (a:=73) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<71) h)
    have hnum : 1000000 < 15*71^3 := by decide +kernel
    omega
  interval_cases e
  · exact case238
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
