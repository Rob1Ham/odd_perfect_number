module

public import OddPerfect.TothTrillion.Part04
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case80 : Closed 1000000 663 730353 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 663 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 663*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case79
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case81 : Closed 1000000 663 730353 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 663 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 663*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case80
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case82 : Closed 1000000 663 730353 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 663 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 663*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case81
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case83 : Closed 1000000 663 730353 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 663 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 663*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case82
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case84 : Closed 1000000 39 2379 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 39 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 39*17^4 := by decide +kernel
    omega
  interval_cases e
  · exact case78
  · exact case83
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case85 : Closed 1000000 507 402233 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 507 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 507*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case86 : Closed 1000000 507 402233 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 507 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 507*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case85
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case87 : Closed 1000000 507 402233 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 507 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 507*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case86
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case88 : Closed 1000000 507 402233 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 507 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 507*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case87
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case89 : Closed 1000000 507 402233 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 507 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 507*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case88
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case90 : Closed 1000000 3 13 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 3*13^5 := by decide +kernel
    omega
  interval_cases e
  · exact case69
  · exact case84
  · exact case89
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case91 : Closed 1000000 33 1729 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 33 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 33*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case92 : Closed 1000000 33 1729 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 33 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 33*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case91
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case93 : Closed 1000000 33 1729 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 33 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 33*31^4 := by decide +kernel
    omega
  interval_cases e
  · exact case92
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case94 : Closed 1000000 957 1505959 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 957 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 957*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case95 : Closed 1000000 33 1729 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 33 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 33*29^4 := by decide +kernel
    omega
  interval_cases e
  · exact case93
  · exact case94
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case96 : Closed 1000000 759 956137 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 759 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 759*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case97 : Closed 1000000 759 956137 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 759 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 759*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case96
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case98 : Closed 1000000 33 1729 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 33 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 33*23^4 := by decide +kernel
    omega
  interval_cases e
  · exact case95
  · exact case97
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case99 : Closed 1000000 627 658749 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 627 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 627*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
