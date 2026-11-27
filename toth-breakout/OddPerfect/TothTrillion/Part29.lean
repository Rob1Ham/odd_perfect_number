module

public import OddPerfect.TothTrillion.Part28
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case560 : Closed 1000000 513 416433 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 513 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 513*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case559
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case561 : Closed 1000000 513 416433 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 513 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 513*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case560
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case562 : Closed 1000000 27 1093 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 27 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 27*19^4 := by decide +kernel
    omega
  interval_cases e
  · exact case557
  · exact case561
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case563 : Closed 1000000 459 335551 43 := by
  apply closed_split (a:=47) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 459 (Nat.pow_le_pow_right (by decide : 0<43) h)
    have hnum : 1000000 < 459*43^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case564 : Closed 1000000 459 335551 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 459 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 459*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact case563
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case565 : Closed 1000000 459 335551 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 459 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 459*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case564
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case566 : Closed 1000000 459 335551 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 459 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 459*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case565
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case567 : Closed 1000000 459 335551 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 459 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 459*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case566
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case568 : Closed 1000000 459 335551 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 459 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 459*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case567
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case569 : Closed 1000000 459 335551 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 459 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 459*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case568
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case570 : Closed 1000000 27 1093 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 27 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 27*17^4 := by decide +kernel
    omega
  interval_cases e
  · exact case562
  · exact case569
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case571 : Closed 1000000 351 200019 53 := by
  apply closed_split (a:=59) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 351 (Nat.pow_le_pow_right (by decide : 0<53) h)
    have hnum : 1000000 < 351*53^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case572 : Closed 1000000 351 200019 47 := by
  apply closed_split (a:=53) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 351 (Nat.pow_le_pow_right (by decide : 0<47) h)
    have hnum : 1000000 < 351*47^3 := by decide +kernel
    omega
  interval_cases e
  · exact case571
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case573 : Closed 1000000 351 200019 43 := by
  apply closed_split (a:=47) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 351 (Nat.pow_le_pow_right (by decide : 0<43) h)
    have hnum : 1000000 < 351*43^3 := by decide +kernel
    omega
  interval_cases e
  · exact case572
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case574 : Closed 1000000 351 200019 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 351 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 351*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact case573
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case575 : Closed 1000000 351 200019 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 351 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 351*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case574
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case576 : Closed 1000000 351 200019 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 351 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 351*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case575
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case577 : Closed 1000000 351 200019 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 351 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 351*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case576
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case578 : Closed 1000000 351 200019 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 351 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 351*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case577
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case579 : Closed 1000000 351 200019 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 351 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 351*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case578
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
