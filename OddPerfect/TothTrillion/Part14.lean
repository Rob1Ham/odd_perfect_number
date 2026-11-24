module

public import OddPerfect.TothTrillion.Part13
import Mathlib.Tactic.IntervalCases
import OddPerfect.TothIntervals
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case260 : Closed 1000000 345 222859 47 := by
  apply closed_split (a:=53) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 345 (Nat.pow_le_pow_right (by decide : 0<47) h)
    have hnum : 1000000 < 345*47^3 := by decide +kernel
    omega
  interval_cases e
  · exact case259
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case261 : Closed 1000000 345 222859 43 := by
  apply closed_split (a:=47) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 345 (Nat.pow_le_pow_right (by decide : 0<43) h)
    have hnum : 1000000 < 345*43^3 := by decide +kernel
    omega
  interval_cases e
  · exact case260
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case262 : Closed 1000000 345 222859 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 345 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 345*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact case261
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case263 : Closed 1000000 345 222859 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 345 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 345*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case262
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case264 : Closed 1000000 345 222859 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 345 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 345*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case263
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case265 : Closed 1000000 345 222859 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 345 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 345*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case264
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case266 : Closed 1000000 15 403 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 15*23^4 := by decide +kernel
    omega
  interval_cases e
  · exact case258
  · exact case265
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case267 : Closed 1000000 285 153543 59 := by
  apply closed_split (a:=61) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 285 (Nat.pow_le_pow_right (by decide : 0<59) h)
    have hnum : 1000000 < 285*59^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime_range 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case268 : Closed 1000000 285 153543 53 := by
  apply closed_split (a:=59) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 285 (Nat.pow_le_pow_right (by decide : 0<53) h)
    have hnum : 1000000 < 285*53^3 := by decide +kernel
    omega
  interval_cases e
  · exact case267
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case269 : Closed 1000000 285 153543 47 := by
  apply closed_split (a:=53) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 285 (Nat.pow_le_pow_right (by decide : 0<47) h)
    have hnum : 1000000 < 285*47^3 := by decide +kernel
    omega
  interval_cases e
  · exact case268
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case270 : Closed 1000000 285 153543 43 := by
  apply closed_split (a:=47) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 285 (Nat.pow_le_pow_right (by decide : 0<43) h)
    have hnum : 1000000 < 285*43^3 := by decide +kernel
    omega
  interval_cases e
  · exact case269
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case271 : Closed 1000000 285 153543 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 285 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 285*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact case270
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case272 : Closed 1000000 285 153543 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 285 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 285*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case271
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case273 : Closed 1000000 285 153543 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 285 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 285*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case272
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case274 : Closed 1000000 285 153543 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 285 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 285*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case273
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case275 : Closed 1000000 285 153543 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 285 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 285*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case274
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case276 : Closed 1000000 15 403 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 15*19^4 := by decide +kernel
    omega
  interval_cases e
  · exact case266
  · exact case275
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case277 : Closed 1000000 255 123721 61 := by
  apply closed_split (a:=67) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 255 (Nat.pow_le_pow_right (by decide : 0<61) h)
    have hnum : 1000000 < 255*61^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime_range 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case278 : Closed 1000000 255 123721 59 := by
  apply closed_split (a:=61) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 255 (Nat.pow_le_pow_right (by decide : 0<59) h)
    have hnum : 1000000 < 255*59^3 := by decide +kernel
    omega
  interval_cases e
  · exact case277
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case279 : Closed 1000000 255 123721 53 := by
  apply closed_split (a:=59) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 255 (Nat.pow_le_pow_right (by decide : 0<53) h)
    have hnum : 1000000 < 255*53^3 := by decide +kernel
    omega
  interval_cases e
  · exact case278
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
