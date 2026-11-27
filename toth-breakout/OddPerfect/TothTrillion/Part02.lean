module

public import OddPerfect.TothTrillion.Part01
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case20 : Closed 1000000 385 235011 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 385 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 385*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case19
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case21 : Closed 1000000 385 235011 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 385 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 385*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case20
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case22 : Closed 1000000 385 235011 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 385 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 385*13^4 := by decide +kernel
    omega
  interval_cases e
  · exact case21
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case23 : Closed 1000000 4235 28457535 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 4235 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 4235*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case24 : Closed 1000000 35 1767 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 35 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 35*11^5 := by decide +kernel
    omega
  interval_cases e
  · exact case15
  · exact case22
  · exact case23
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case25 : Closed 1000000 3185 15890073 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3185 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 3185*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case26 : Closed 1000000 245 86831 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 245 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 245*13^4 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact case25
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case27 : Closed 1000000 2695 11548523 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2695 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 2695*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case28 : Closed 1000000 2695 11548523 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2695 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 2695*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case27
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case29 : Closed 1000000 2695 11548523 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2695 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 2695*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact case28
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case30 : Closed 1000000 245 86831 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 245 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 245*11^4 := by decide +kernel
    omega
  interval_cases e
  · exact case26
  · exact case29
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case31 : Closed 1000000 1715 4254967 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1715 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 1715*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case32 : Closed 1000000 1715 4254967 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1715 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 1715*11^3 := by decide +kernel
    omega
  interval_cases e
  · exact case31
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case33 : Closed 1000000 5 31 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 7 := by
    by_contra! h
    have := Nat.mul_le_mul_left 5 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 5*7^7 := by decide +kernel
    omega
  interval_cases e
  · exact case5
  · exact case24
  · exact case30
  · exact case32
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case34 : Closed 1000000 25 781 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 25 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 25*13^5 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=3) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case35 : Closed 1000000 275 103873 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 275 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 275*13^4 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case36 : Closed 1000000 25 781 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 25 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 25*11^5 := by decide +kernel
    omega
  interval_cases e
  · exact case34
  · exact case35
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case37 : Closed 1000000 175 44517 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 175 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 175*17^4 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case38 : Closed 1000000 2275 8146611 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2275 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 2275*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case39 : Closed 1000000 2275 8146611 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2275 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 2275*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case38
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
