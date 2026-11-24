module

public import OddPerfect.TothTrillion.Part14
import Mathlib.Tactic.IntervalCases
import OddPerfect.TothIntervals
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case280 : Closed 1000000 255 123721 47 := by
  apply closed_split (a:=53) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 255 (Nat.pow_le_pow_right (by decide : 0<47) h)
    have hnum : 1000000 < 255*47^3 := by decide +kernel
    omega
  interval_cases e
  · exact case279
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case281 : Closed 1000000 255 123721 43 := by
  apply closed_split (a:=47) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 255 (Nat.pow_le_pow_right (by decide : 0<43) h)
    have hnum : 1000000 < 255*43^3 := by decide +kernel
    omega
  interval_cases e
  · exact case280
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case282 : Closed 1000000 255 123721 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 255 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 255*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact case281
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case283 : Closed 1000000 255 123721 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 255 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 255*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case282
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case284 : Closed 1000000 255 123721 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 255 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 255*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case283
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case285 : Closed 1000000 255 123721 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 255 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 255*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case284
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case286 : Closed 1000000 255 123721 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 255 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 255*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case285
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case287 : Closed 1000000 255 123721 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 255 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 255*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case286
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case288 : Closed 1000000 15 403 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 15*17^4 := by decide +kernel
    omega
  interval_cases e
  · exact case276
  · exact case287
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case289 : Closed 1000000 195 73749 71 := by
  apply closed_split (a:=73) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 195 (Nat.pow_le_pow_right (by decide : 0<71) h)
    have hnum : 1000000 < 195*71^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime_range 8 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case290 : Closed 1000000 195 73749 67 := by
  apply closed_split (a:=71) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 195 (Nat.pow_le_pow_right (by decide : 0<67) h)
    have hnum : 1000000 < 195*67^3 := by decide +kernel
    omega
  interval_cases e
  · exact case289
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case291 : Closed 1000000 195 73749 61 := by
  apply closed_split (a:=67) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 195 (Nat.pow_le_pow_right (by decide : 0<61) h)
    have hnum : 1000000 < 195*61^3 := by decide +kernel
    omega
  interval_cases e
  · exact case290
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case292 : Closed 1000000 195 73749 59 := by
  apply closed_split (a:=61) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 195 (Nat.pow_le_pow_right (by decide : 0<59) h)
    have hnum : 1000000 < 195*59^3 := by decide +kernel
    omega
  interval_cases e
  · exact case291
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case293 : Closed 1000000 195 73749 53 := by
  apply closed_split (a:=59) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 195 (Nat.pow_le_pow_right (by decide : 0<53) h)
    have hnum : 1000000 < 195*53^3 := by decide +kernel
    omega
  interval_cases e
  · exact case292
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case294 : Closed 1000000 195 73749 47 := by
  apply closed_split (a:=53) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 195 (Nat.pow_le_pow_right (by decide : 0<47) h)
    have hnum : 1000000 < 195*47^3 := by decide +kernel
    omega
  interval_cases e
  · exact case293
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case295 : Closed 1000000 195 73749 43 := by
  apply closed_split (a:=47) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 195 (Nat.pow_le_pow_right (by decide : 0<43) h)
    have hnum : 1000000 < 195*43^3 := by decide +kernel
    omega
  interval_cases e
  · exact case294
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case296 : Closed 1000000 195 73749 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 195 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 195*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact case295
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case297 : Closed 1000000 195 73749 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 195 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 195*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case296
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case298 : Closed 1000000 195 73749 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 195 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 195*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case297
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case299 : Closed 1000000 195 73749 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 195 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 195*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case298
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
