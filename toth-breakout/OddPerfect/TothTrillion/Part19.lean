module

public import OddPerfect.TothTrillion.Part18
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case360 : Closed 1000000 375 253903 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 375 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 375*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact case359
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case361 : Closed 1000000 375 253903 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 375 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 375*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case360
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case362 : Closed 1000000 375 253903 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 375 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 375*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case361
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case363 : Closed 1000000 375 253903 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 375 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 375*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case362
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case364 : Closed 1000000 375 253903 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 375 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 375*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case363
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case365 : Closed 1000000 375 253903 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 375 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 375*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case364
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case366 : Closed 1000000 375 253903 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 375 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 375*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case365
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case367 : Closed 1000000 375 253903 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 375 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 375*13^4 := by decide +kernel
    omega
  interval_cases e
  · exact case366
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case368 : Closed 1000000 4125 33769099 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 4125 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 4125*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case369 : Closed 1000000 375 253903 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 375 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 375*11^4 := by decide +kernel
    omega
  interval_cases e
  · exact case367
  · exact case368
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case370 : Closed 1000000 375 253903 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 375 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 375*7^5 := by decide +kernel
    omega
  interval_cases e
  · exact case369
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case371 : Closed 1000000 1875 6347653 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1875 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 1875*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case372 : Closed 1000000 1875 6347653 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1875 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 1875*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case371
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case373 : Closed 1000000 1875 6347653 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1875 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 1875*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case372
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case374 : Closed 1000000 1875 6347653 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1875 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 1875*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact case373
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case375 : Closed 1000000 1875 6347653 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1875 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 1875*11^3 := by decide +kernel
    omega
  interval_cases e
  · exact case374
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case376 : Closed 1000000 1875 6347653 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1875 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 1875*7^4 := by decide +kernel
    omega
  interval_cases e
  · exact case375
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case377 : Closed 1000000 9375 158691403 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 9375 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 9375*7^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case378 : Closed 1000000 3 13 5 := by
  apply closed_split (a:=7) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 8 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by decide : 0<5) h)
    have hnum : 1000000 < 3*5^8 := by decide +kernel
    omega
  interval_cases e
  · exact case203
  · exact case327
  · exact case357
  · exact case370
  · exact case376
  · exact case377
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case379 : Closed 1000000 207 66913 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 207 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 207*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
