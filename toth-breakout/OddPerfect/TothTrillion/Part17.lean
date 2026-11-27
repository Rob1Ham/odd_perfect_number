module

public import OddPerfect.TothTrillion.Part16
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case320 : Closed 1000000 165 53599 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 165 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 165*17^4 := by decide +kernel
    omega
  interval_cases e
  · exact case319
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case321 : Closed 1000000 165 53599 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 165 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 165*13^4 := by decide +kernel
    omega
  interval_cases e
  · exact case320
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case322 : Closed 1000000 1815 6490315 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1815 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 1815*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case323 : Closed 1000000 1815 6490315 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1815 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 1815*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case322
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case324 : Closed 1000000 1815 6490315 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1815 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 1815*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case323
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case325 : Closed 1000000 1815 6490315 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1815 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 1815*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact case324
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case326 : Closed 1000000 15 403 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 15*11^5 := by decide +kernel
    omega
  interval_cases e
  · exact case305
  · exact case321
  · exact case325
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case327 : Closed 1000000 15 403 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 6 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 15*7^6 := by decide +kernel
    omega
  interval_cases e
  · exact case326
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case328 : Closed 1000000 75 10153 67 := by
  apply closed_split (a:=71) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 75 (Nat.pow_le_pow_right (by decide : 0<67) h)
    have hnum : 1000000 < 75*67^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case329 : Closed 1000000 75 10153 61 := by
  apply closed_split (a:=67) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 75 (Nat.pow_le_pow_right (by decide : 0<61) h)
    have hnum : 1000000 < 75*61^3 := by decide +kernel
    omega
  interval_cases e
  · exact case328
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case330 : Closed 1000000 75 10153 59 := by
  apply closed_split (a:=61) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 75 (Nat.pow_le_pow_right (by decide : 0<59) h)
    have hnum : 1000000 < 75*59^3 := by decide +kernel
    omega
  interval_cases e
  · exact case329
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case331 : Closed 1000000 75 10153 53 := by
  apply closed_split (a:=59) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 75 (Nat.pow_le_pow_right (by decide : 0<53) h)
    have hnum : 1000000 < 75*53^3 := by decide +kernel
    omega
  interval_cases e
  · exact case330
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case332 : Closed 1000000 75 10153 47 := by
  apply closed_split (a:=53) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 75 (Nat.pow_le_pow_right (by decide : 0<47) h)
    have hnum : 1000000 < 75*47^3 := by decide +kernel
    omega
  interval_cases e
  · exact case331
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case333 : Closed 1000000 75 10153 43 := by
  apply closed_split (a:=47) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 75 (Nat.pow_le_pow_right (by decide : 0<43) h)
    have hnum : 1000000 < 75*43^3 := by decide +kernel
    omega
  interval_cases e
  · exact case332
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case334 : Closed 1000000 75 10153 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 75 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 75*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact case333
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case335 : Closed 1000000 75 10153 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 75 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 75*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case334
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case336 : Closed 1000000 75 10153 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 75 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 75*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case335
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case337 : Closed 1000000 75 10153 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 75 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 75*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case336
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case338 : Closed 1000000 75 10153 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 75 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 75*23^4 := by decide +kernel
    omega
  interval_cases e
  · exact case337
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case339 : Closed 1000000 1425 3868293 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1425 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 1425*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
