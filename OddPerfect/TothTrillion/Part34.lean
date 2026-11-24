module

public import OddPerfect.TothTrillion.Part33
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case660 : Closed 1000000 1377 3021187 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1377 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 1377*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case661 : Closed 1000000 1377 3021187 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1377 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 1377*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case660
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case662 : Closed 1000000 81 9841 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 81 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 81*17^4 := by decide +kernel
    omega
  interval_cases e
  · exact case659
  · exact case661
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case663 : Closed 1000000 1053 1800903 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1053 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 1053*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case664 : Closed 1000000 1053 1800903 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1053 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 1053*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case663
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case665 : Closed 1000000 1053 1800903 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1053 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 1053*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case664
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case666 : Closed 1000000 1053 1800903 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1053 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 1053*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case665
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case667 : Closed 1000000 81 9841 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 81 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 81*13^4 := by decide +kernel
    omega
  interval_cases e
  · exact case662
  · exact case666
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case668 : Closed 1000000 891 1308853 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 891 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 891*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case669 : Closed 1000000 891 1308853 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 891 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 891*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case668
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case670 : Closed 1000000 891 1308853 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 891 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 891*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case669
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case671 : Closed 1000000 891 1308853 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 891 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 891*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case670
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case672 : Closed 1000000 891 1308853 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 891 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 891*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case671
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case673 : Closed 1000000 891 1308853 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 891 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 891*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact case672
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case674 : Closed 1000000 81 9841 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 81 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 81*11^4 := by decide +kernel
    omega
  interval_cases e
  · exact case667
  · exact case673
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case675 : Closed 1000000 567 560937 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 567 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 567*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case676 : Closed 1000000 567 560937 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 567 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 567*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case675
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case677 : Closed 1000000 567 560937 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 567 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 567*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case676
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case678 : Closed 1000000 567 560937 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 567 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 567*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case677
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case679 : Closed 1000000 567 560937 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 567 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 567*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case678
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
