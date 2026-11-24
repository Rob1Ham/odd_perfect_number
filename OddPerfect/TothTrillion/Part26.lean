module

public import OddPerfect.TothTrillion.Part25
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case500 : Closed 1000000 45 3751 83 := by
  apply closed_split (a:=89) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<83) h)
    have hnum : 1000000 < 45*83^3 := by decide +kernel
    omega
  interval_cases e
  · exact case499
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case501 : Closed 1000000 45 3751 79 := by
  apply closed_split (a:=83) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<79) h)
    have hnum : 1000000 < 45*79^3 := by decide +kernel
    omega
  interval_cases e
  · exact case500
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case502 : Closed 1000000 45 3751 73 := by
  apply closed_split (a:=79) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<73) h)
    have hnum : 1000000 < 45*73^3 := by decide +kernel
    omega
  interval_cases e
  · exact case501
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case503 : Closed 1000000 45 3751 71 := by
  apply closed_split (a:=73) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<71) h)
    have hnum : 1000000 < 45*71^3 := by decide +kernel
    omega
  interval_cases e
  · exact case502
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case504 : Closed 1000000 45 3751 67 := by
  apply closed_split (a:=71) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<67) h)
    have hnum : 1000000 < 45*67^3 := by decide +kernel
    omega
  interval_cases e
  · exact case503
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case505 : Closed 1000000 45 3751 61 := by
  apply closed_split (a:=67) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<61) h)
    have hnum : 1000000 < 45*61^3 := by decide +kernel
    omega
  interval_cases e
  · exact case504
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case506 : Closed 1000000 45 3751 59 := by
  apply closed_split (a:=61) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<59) h)
    have hnum : 1000000 < 45*59^3 := by decide +kernel
    omega
  interval_cases e
  · exact case505
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case507 : Closed 1000000 45 3751 53 := by
  apply closed_split (a:=59) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<53) h)
    have hnum : 1000000 < 45*53^3 := by decide +kernel
    omega
  interval_cases e
  · exact case506
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case508 : Closed 1000000 45 3751 47 := by
  apply closed_split (a:=53) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<47) h)
    have hnum : 1000000 < 45*47^3 := by decide +kernel
    omega
  interval_cases e
  · exact case507
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case509 : Closed 1000000 45 3751 43 := by
  apply closed_split (a:=47) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<43) h)
    have hnum : 1000000 < 45*43^3 := by decide +kernel
    omega
  interval_cases e
  · exact case508
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case510 : Closed 1000000 45 3751 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 45*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact case509
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case511 : Closed 1000000 45 3751 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 45*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case510
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case512 : Closed 1000000 45 3751 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 45*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case511
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case513 : Closed 1000000 45 3751 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 45*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case512
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case514 : Closed 1000000 1035 2074303 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1035 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 1035*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case515 : Closed 1000000 1035 2074303 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1035 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 1035*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case514
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case516 : Closed 1000000 45 3751 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 45*23^4 := by decide +kernel
    omega
  interval_cases e
  · exact case513
  · exact case515
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case517 : Closed 1000000 855 1429131 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 855 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 855*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case518 : Closed 1000000 855 1429131 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 855 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 855*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case517
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case519 : Closed 1000000 855 1429131 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 855 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 855*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case518
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
