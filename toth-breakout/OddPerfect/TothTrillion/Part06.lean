module

public import OddPerfect.TothTrillion.Part05
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case100 : Closed 1000000 33 1729 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 33 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 33*19^4 := by decide +kernel
    omega
  interval_cases e
  · exact case98
  · exact case99
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case101 : Closed 1000000 561 530803 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 561 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 561*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case102 : Closed 1000000 561 530803 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 561 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 561*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case101
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case103 : Closed 1000000 561 530803 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 561 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 561*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case102
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case104 : Closed 1000000 561 530803 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 561 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 561*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case103
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case105 : Closed 1000000 33 1729 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 33 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 33*17^4 := by decide +kernel
    omega
  interval_cases e
  · exact case100
  · exact case104
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case106 : Closed 1000000 429 316407 43 := by
  apply closed_split (a:=47) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 429 (Nat.pow_le_pow_right (by decide : 0<43) h)
    have hnum : 1000000 < 429*43^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case107 : Closed 1000000 429 316407 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 429 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 429*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact case106
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case108 : Closed 1000000 429 316407 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 429 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 429*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case107
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case109 : Closed 1000000 429 316407 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 429 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 429*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case108
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case110 : Closed 1000000 429 316407 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 429 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 429*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case109
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case111 : Closed 1000000 429 316407 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 429 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 429*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case110
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case112 : Closed 1000000 429 316407 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 429 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 429*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case111
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case113 : Closed 1000000 429 316407 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 429 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 429*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case112
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case114 : Closed 1000000 33 1729 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 33 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 33*13^5 := by decide +kernel
    omega
  interval_cases e
  · exact case105
  · exact case113
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case115 : Closed 1000000 363 209365 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 363 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 363*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case116 : Closed 1000000 363 209365 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 363 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 363*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case115
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case117 : Closed 1000000 363 209365 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 363 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 363*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case116
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case118 : Closed 1000000 363 209365 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 363 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 363*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case117
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case119 : Closed 1000000 363 209365 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 363 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 363*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case118
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
