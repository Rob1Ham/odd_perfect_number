module

public import OddPerfect.TothTrillion.Part06
import Mathlib.Tactic.IntervalCases
import OddPerfect.TothIntervals
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case120 : Closed 1000000 363 209365 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 363 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 363*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case119
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case121 : Closed 1000000 363 209365 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 363 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 363*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case120
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case122 : Closed 1000000 363 209365 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 363 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 363*13^4 := by decide +kernel
    omega
  interval_cases e
  · exact case121
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case123 : Closed 1000000 3993 25333321 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3993 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 3993*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case124 : Closed 1000000 3 13 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 6 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 3*11^6 := by decide +kernel
    omega
  interval_cases e
  · exact case90
  · exact case114
  · exact case122
  · exact case123
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case125 : Closed 1000000 651 735813 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 651 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 651*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case126 : Closed 1000000 21 741 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 21 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 21*31^4 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact case125
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case127 : Closed 1000000 609 645411 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 609 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 609*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case128 : Closed 1000000 609 645411 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 609 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 609*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case127
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case129 : Closed 1000000 21 741 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 21 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 21*29^4 := by decide +kernel
    omega
  interval_cases e
  · exact case126
  · exact case128
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case130 : Closed 1000000 483 409773 43 := by
  apply closed_split (a:=47) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 483 (Nat.pow_le_pow_right (by decide : 0<43) h)
    have hnum : 1000000 < 483*43^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case131 : Closed 1000000 483 409773 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 483 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 483*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact case130
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case132 : Closed 1000000 483 409773 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 483 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 483*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case131
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case133 : Closed 1000000 483 409773 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 483 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 483*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case132
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case134 : Closed 1000000 483 409773 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 483 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 483*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case133
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case135 : Closed 1000000 21 741 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 21 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 21*23^4 := by decide +kernel
    omega
  interval_cases e
  · exact case129
  · exact case134
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case136 : Closed 1000000 399 282321 47 := by
  apply closed_split (a:=53) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 399 (Nat.pow_le_pow_right (by decide : 0<47) h)
    have hnum : 1000000 < 399*47^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime_range 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case137 : Closed 1000000 399 282321 43 := by
  apply closed_split (a:=47) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 399 (Nat.pow_le_pow_right (by decide : 0<43) h)
    have hnum : 1000000 < 399*43^3 := by decide +kernel
    omega
  interval_cases e
  · exact case136
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case138 : Closed 1000000 399 282321 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 399 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 399*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact case137
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case139 : Closed 1000000 399 282321 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 399 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 399*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case138
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
