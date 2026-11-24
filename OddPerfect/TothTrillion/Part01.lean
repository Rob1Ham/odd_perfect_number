module

public import OddPerfect.TothCover
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case0 : Closed 1000000 7 57 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 7 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 7*11^5 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=4) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=3) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case1 : Closed 1000000 49 2801 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 49 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 49*11^5 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=3) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case2 : Closed 1000000 1 1 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 8 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 1*7^8 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=5) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact case0
  · exact case1
  · exact closed_interval (k:=3) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case3 : Closed 1000000 5 31 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 5 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 5*13^5 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=4) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=3) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case4 : Closed 1000000 55 4123 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 55 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 55*13^4 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=3) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case5 : Closed 1000000 5 31 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 6 := by
    by_contra! h
    have := Nat.mul_le_mul_left 5 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 5*11^6 := by decide +kernel
    omega
  interval_cases e
  · exact case3
  · exact case4
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case6 : Closed 1000000 35 1767 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 35 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 35*19^4 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=3) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case7 : Closed 1000000 595 542469 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 595 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 595*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case8 : Closed 1000000 595 542469 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 595 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 595*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case7
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case9 : Closed 1000000 35 1767 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 35 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 35*17^4 := by decide +kernel
    omega
  interval_cases e
  · exact case6
  · exact case8
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case10 : Closed 1000000 455 323361 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 455 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 455*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case11 : Closed 1000000 455 323361 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 455 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 455*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case10
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case12 : Closed 1000000 455 323361 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 455 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 455*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case11
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case13 : Closed 1000000 455 323361 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 455 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 455*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case12
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case14 : Closed 1000000 455 323361 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 455 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 455*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case13
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case15 : Closed 1000000 35 1767 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 35 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 35*13^5 := by decide +kernel
    omega
  interval_cases e
  · exact case9
  · exact case14
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case16 : Closed 1000000 385 235011 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 385 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 385*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case17 : Closed 1000000 385 235011 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 385 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 385*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case16
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case18 : Closed 1000000 385 235011 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 385 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 385*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case17
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case19 : Closed 1000000 385 235011 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 385 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 385*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case18
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
