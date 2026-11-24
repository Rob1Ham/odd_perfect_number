module

public import OddPerfect.TothTrillion.Part10
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case200 : Closed 1000000 1029 1784341 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1029 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 1029*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact case199
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case201 : Closed 1000000 1029 1784341 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1029 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 1029*11^3 := by decide +kernel
    omega
  interval_cases e
  · exact case200
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case202 : Closed 1000000 7203 87432813 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 7203 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 7203*11^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case203 : Closed 1000000 3 13 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 7 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 3*7^7 := by decide +kernel
    omega
  interval_cases e
  · exact case124
  · exact case182
  · exact case195
  · exact case201
  · exact case202
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case204 : Closed 1000000 15 403 257 := by
  apply closed_split (a:=263) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<257) h)
    have hnum : 1000000 < 15*257^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case205 : Closed 1000000 15 403 251 := by
  apply closed_split (a:=257) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<251) h)
    have hnum : 1000000 < 15*251^3 := by decide +kernel
    omega
  interval_cases e
  · exact case204
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case206 : Closed 1000000 15 403 241 := by
  apply closed_split (a:=251) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<241) h)
    have hnum : 1000000 < 15*241^3 := by decide +kernel
    omega
  interval_cases e
  · exact case205
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case207 : Closed 1000000 15 403 239 := by
  apply closed_split (a:=241) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<239) h)
    have hnum : 1000000 < 15*239^3 := by decide +kernel
    omega
  interval_cases e
  · exact case206
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case208 : Closed 1000000 15 403 233 := by
  apply closed_split (a:=239) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<233) h)
    have hnum : 1000000 < 15*233^3 := by decide +kernel
    omega
  interval_cases e
  · exact case207
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case209 : Closed 1000000 15 403 229 := by
  apply closed_split (a:=233) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<229) h)
    have hnum : 1000000 < 15*229^3 := by decide +kernel
    omega
  interval_cases e
  · exact case208
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case210 : Closed 1000000 15 403 227 := by
  apply closed_split (a:=229) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<227) h)
    have hnum : 1000000 < 15*227^3 := by decide +kernel
    omega
  interval_cases e
  · exact case209
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case211 : Closed 1000000 15 403 223 := by
  apply closed_split (a:=227) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<223) h)
    have hnum : 1000000 < 15*223^3 := by decide +kernel
    omega
  interval_cases e
  · exact case210
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case212 : Closed 1000000 15 403 211 := by
  apply closed_split (a:=223) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<211) h)
    have hnum : 1000000 < 15*211^3 := by decide +kernel
    omega
  interval_cases e
  · exact case211
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case213 : Closed 1000000 15 403 199 := by
  apply closed_split (a:=211) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<199) h)
    have hnum : 1000000 < 15*199^3 := by decide +kernel
    omega
  interval_cases e
  · exact case212
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case214 : Closed 1000000 15 403 197 := by
  apply closed_split (a:=199) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<197) h)
    have hnum : 1000000 < 15*197^3 := by decide +kernel
    omega
  interval_cases e
  · exact case213
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case215 : Closed 1000000 15 403 193 := by
  apply closed_split (a:=197) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<193) h)
    have hnum : 1000000 < 15*193^3 := by decide +kernel
    omega
  interval_cases e
  · exact case214
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case216 : Closed 1000000 15 403 191 := by
  apply closed_split (a:=193) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<191) h)
    have hnum : 1000000 < 15*191^3 := by decide +kernel
    omega
  interval_cases e
  · exact case215
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case217 : Closed 1000000 15 403 181 := by
  apply closed_split (a:=191) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<181) h)
    have hnum : 1000000 < 15*181^3 := by decide +kernel
    omega
  interval_cases e
  · exact case216
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case218 : Closed 1000000 15 403 179 := by
  apply closed_split (a:=181) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<179) h)
    have hnum : 1000000 < 15*179^3 := by decide +kernel
    omega
  interval_cases e
  · exact case217
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case219 : Closed 1000000 15 403 173 := by
  apply closed_split (a:=179) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<173) h)
    have hnum : 1000000 < 15*173^3 := by decide +kernel
    omega
  interval_cases e
  · exact case218
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
