module

public import OddPerfect.TothTrillion.Part29
import Mathlib.Tactic.IntervalCases
import OddPerfect.TothIntervals
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case580 : Closed 1000000 351 200019 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 351 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 351*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case579
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case581 : Closed 1000000 27 1093 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 27 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 27*13^5 := by decide +kernel
    omega
  interval_cases e
  · exact case570
  · exact case580
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case582 : Closed 1000000 297 145369 53 := by
  apply closed_split (a:=59) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 297 (Nat.pow_le_pow_right (by decide : 0<53) h)
    have hnum : 1000000 < 297*53^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime_range 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case583 : Closed 1000000 297 145369 47 := by
  apply closed_split (a:=53) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 297 (Nat.pow_le_pow_right (by decide : 0<47) h)
    have hnum : 1000000 < 297*47^3 := by decide +kernel
    omega
  interval_cases e
  · exact case582
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case584 : Closed 1000000 297 145369 43 := by
  apply closed_split (a:=47) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 297 (Nat.pow_le_pow_right (by decide : 0<43) h)
    have hnum : 1000000 < 297*43^3 := by decide +kernel
    omega
  interval_cases e
  · exact case583
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case585 : Closed 1000000 297 145369 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 297 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 297*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact case584
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case586 : Closed 1000000 297 145369 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 297 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 297*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case585
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case587 : Closed 1000000 297 145369 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 297 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 297*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case586
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case588 : Closed 1000000 297 145369 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 297 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 297*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case587
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case589 : Closed 1000000 297 145369 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 297 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 297*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case588
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case590 : Closed 1000000 297 145369 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 297 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 297*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case589
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case591 : Closed 1000000 297 145369 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 297 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 297*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case590
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case592 : Closed 1000000 297 145369 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 297 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 297*13^4 := by decide +kernel
    omega
  interval_cases e
  · exact case591
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case593 : Closed 1000000 3267 17602765 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3267 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 3267*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case594 : Closed 1000000 3267 17602765 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3267 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 3267*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact case593
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case595 : Closed 1000000 27 1093 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 27 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 27*11^5 := by decide +kernel
    omega
  interval_cases e
  · exact case581
  · exact case592
  · exact case594
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case596 : Closed 1000000 189 62301 61 := by
  apply closed_split (a:=67) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 189 (Nat.pow_le_pow_right (by decide : 0<61) h)
    have hnum : 1000000 < 189*61^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case597 : Closed 1000000 189 62301 59 := by
  apply closed_split (a:=61) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 189 (Nat.pow_le_pow_right (by decide : 0<59) h)
    have hnum : 1000000 < 189*59^3 := by decide +kernel
    omega
  interval_cases e
  · exact case596
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case598 : Closed 1000000 189 62301 53 := by
  apply closed_split (a:=59) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 189 (Nat.pow_le_pow_right (by decide : 0<53) h)
    have hnum : 1000000 < 189*53^3 := by decide +kernel
    omega
  interval_cases e
  · exact case597
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case599 : Closed 1000000 189 62301 47 := by
  apply closed_split (a:=53) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 189 (Nat.pow_le_pow_right (by decide : 0<47) h)
    have hnum : 1000000 < 189*47^3 := by decide +kernel
    omega
  interval_cases e
  · exact case598
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
