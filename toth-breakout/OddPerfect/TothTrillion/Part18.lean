module

public import OddPerfect.TothTrillion.Part17
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case340 : Closed 1000000 75 10153 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 75 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 75*19^4 := by decide +kernel
    omega
  interval_cases e
  · exact case338
  · exact case339
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case341 : Closed 1000000 1275 3116971 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1275 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 1275*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case342 : Closed 1000000 1275 3116971 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1275 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 1275*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case341
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case343 : Closed 1000000 75 10153 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 75 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 75*17^4 := by decide +kernel
    omega
  interval_cases e
  · exact case340
  · exact case342
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case344 : Closed 1000000 975 1857999 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 975 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 975*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case345 : Closed 1000000 975 1857999 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 975 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 975*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case344
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case346 : Closed 1000000 975 1857999 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 975 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 975*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case345
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case347 : Closed 1000000 975 1857999 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 975 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 975*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case346
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case348 : Closed 1000000 975 1857999 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 975 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 975*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case347
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case349 : Closed 1000000 75 10153 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 75 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 75*13^4 := by decide +kernel
    omega
  interval_cases e
  · exact case343
  · exact case348
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case350 : Closed 1000000 825 1350349 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 825 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 825*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case351 : Closed 1000000 825 1350349 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 825 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 825*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case350
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case352 : Closed 1000000 825 1350349 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 825 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 825*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case351
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case353 : Closed 1000000 825 1350349 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 825 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 825*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case352
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case354 : Closed 1000000 825 1350349 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 825 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 825*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case353
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case355 : Closed 1000000 825 1350349 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 825 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 825*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact case354
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case356 : Closed 1000000 75 10153 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 75 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 75*11^4 := by decide +kernel
    omega
  interval_cases e
  · exact case349
  · exact case355
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case357 : Closed 1000000 75 10153 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 75 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 75*7^5 := by decide +kernel
    omega
  interval_cases e
  · exact case356
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case358 : Closed 1000000 375 253903 47 := by
  apply closed_split (a:=53) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 375 (Nat.pow_le_pow_right (by decide : 0<47) h)
    have hnum : 1000000 < 375*47^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case359 : Closed 1000000 375 253903 43 := by
  apply closed_split (a:=47) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 375 (Nat.pow_le_pow_right (by decide : 0<43) h)
    have hnum : 1000000 < 375*43^3 := by decide +kernel
    omega
  interval_cases e
  · exact case358
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
