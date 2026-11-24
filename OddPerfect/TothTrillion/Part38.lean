module

public import OddPerfect.TothTrillion.Part37
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case740 : Closed 1000000 729 797161 5 := by
  apply closed_split (a:=7) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 729 (Nat.pow_le_pow_right (by decide : 0<5) h)
    have hnum : 1000000 < 729*5^5 := by decide +kernel
    omega
  interval_cases e
  · exact case735
  · exact case738
  · exact case739
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case741 : Closed 1000000 2187 7174453 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2187 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 2187*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case742 : Closed 1000000 2187 7174453 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2187 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 2187*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case741
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case743 : Closed 1000000 2187 7174453 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2187 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 2187*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact case742
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case744 : Closed 1000000 2187 7174453 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2187 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 2187*11^3 := by decide +kernel
    omega
  interval_cases e
  · exact case743
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case745 : Closed 1000000 2187 7174453 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2187 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 2187*7^4 := by decide +kernel
    omega
  interval_cases e
  · exact case744
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case746 : Closed 1000000 10935 222408043 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 10935 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 10935*7^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case747 : Closed 1000000 2187 7174453 5 := by
  apply closed_split (a:=7) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2187 (Nat.pow_le_pow_right (by decide : 0<5) h)
    have hnum : 1000000 < 2187*5^4 := by decide +kernel
    omega
  interval_cases e
  · exact case745
  · exact case746
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case748 : Closed 1000000 6561 64570081 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 6561 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 6561*11^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case749 : Closed 1000000 6561 64570081 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 6561 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 6561*7^3 := by decide +kernel
    omega
  interval_cases e
  · exact case748
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case750 : Closed 1000000 6561 64570081 5 := by
  apply closed_split (a:=7) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 6561 (Nat.pow_le_pow_right (by decide : 0<5) h)
    have hnum : 1000000 < 6561*5^4 := by decide +kernel
    omega
  interval_cases e
  · exact case749
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case751 : Closed 1000000 19683 581130733 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 19683 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 19683*7^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case752 : Closed 1000000 19683 581130733 5 := by
  apply closed_split (a:=7) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 19683 (Nat.pow_le_pow_right (by decide : 0<5) h)
    have hnum : 1000000 < 19683*5^3 := by decide +kernel
    omega
  interval_cases e
  · exact case751
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case753 : Closed 1000000 1 1 3 := by
  apply closed_split (a:=5) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 13 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1 (Nat.pow_le_pow_right (by decide : 0<3) h)
    have hnum : 1000000 < 1*3^13 := by decide +kernel
    omega
  interval_cases e
  · exact case57
  · exact case378
  · exact case554
  · exact case656
  · exact case705
  · exact case728
  · exact case740
  · exact case747
  · exact case750
  · exact case752
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
