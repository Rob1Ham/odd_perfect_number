module

public import OddPerfect.TothTrillion.Part07
import Mathlib.Tactic.IntervalCases
import OddPerfect.TothIntervals
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case140 : Closed 1000000 399 282321 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 399 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 399*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case139
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case141 : Closed 1000000 399 282321 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 399 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 399*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case140
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case142 : Closed 1000000 399 282321 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 399 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 399*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case141
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case143 : Closed 1000000 21 741 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 21 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 21*19^4 := by decide +kernel
    omega
  interval_cases e
  · exact case135
  · exact case142
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case144 : Closed 1000000 357 227487 47 := by
  apply closed_split (a:=53) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 357 (Nat.pow_le_pow_right (by decide : 0<47) h)
    have hnum : 1000000 < 357*47^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime_range 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case145 : Closed 1000000 357 227487 43 := by
  apply closed_split (a:=47) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 357 (Nat.pow_le_pow_right (by decide : 0<43) h)
    have hnum : 1000000 < 357*43^3 := by decide +kernel
    omega
  interval_cases e
  · exact case144
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case146 : Closed 1000000 357 227487 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 357 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 357*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact case145
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case147 : Closed 1000000 357 227487 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 357 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 357*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case146
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case148 : Closed 1000000 357 227487 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 357 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 357*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case147
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case149 : Closed 1000000 357 227487 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 357 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 357*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case148
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case150 : Closed 1000000 357 227487 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 357 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 357*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case149
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case151 : Closed 1000000 357 227487 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 357 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 357*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case150
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case152 : Closed 1000000 21 741 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 21 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 21*17^4 := by decide +kernel
    omega
  interval_cases e
  · exact case143
  · exact case151
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case153 : Closed 1000000 273 135603 59 := by
  apply closed_split (a:=61) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 273 (Nat.pow_le_pow_right (by decide : 0<59) h)
    have hnum : 1000000 < 273*59^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case154 : Closed 1000000 273 135603 53 := by
  apply closed_split (a:=59) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 273 (Nat.pow_le_pow_right (by decide : 0<53) h)
    have hnum : 1000000 < 273*53^3 := by decide +kernel
    omega
  interval_cases e
  · exact case153
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case155 : Closed 1000000 273 135603 47 := by
  apply closed_split (a:=53) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 273 (Nat.pow_le_pow_right (by decide : 0<47) h)
    have hnum : 1000000 < 273*47^3 := by decide +kernel
    omega
  interval_cases e
  · exact case154
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case156 : Closed 1000000 273 135603 43 := by
  apply closed_split (a:=47) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 273 (Nat.pow_le_pow_right (by decide : 0<43) h)
    have hnum : 1000000 < 273*43^3 := by decide +kernel
    omega
  interval_cases e
  · exact case155
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case157 : Closed 1000000 273 135603 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 273 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 273*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact case156
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case158 : Closed 1000000 273 135603 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 273 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 273*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case157
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case159 : Closed 1000000 273 135603 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 273 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 273*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case158
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
