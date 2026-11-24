module

public import OddPerfect.TothTrillion.Part23
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case460 : Closed 1000000 819 1262151 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 819 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 819*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case459
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case461 : Closed 1000000 819 1262151 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 819 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 819*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case460
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case462 : Closed 1000000 819 1262151 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 819 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 819*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case461
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case463 : Closed 1000000 63 6897 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 63 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 63*13^4 := by decide +kernel
    omega
  interval_cases e
  · exact case457
  · exact case462
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case464 : Closed 1000000 693 917301 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 693 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 693*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case465 : Closed 1000000 693 917301 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 693 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 693*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case464
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case466 : Closed 1000000 693 917301 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 693 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 693*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case465
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case467 : Closed 1000000 693 917301 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 693 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 693*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case466
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case468 : Closed 1000000 693 917301 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 693 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 693*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case467
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case469 : Closed 1000000 693 917301 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 693 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 693*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case468
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case470 : Closed 1000000 693 917301 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 693 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 693*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact case469
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case471 : Closed 1000000 63 6897 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 63 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 63*11^5 := by decide +kernel
    omega
  interval_cases e
  · exact case463
  · exact case470
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case472 : Closed 1000000 441 338921 47 := by
  apply closed_split (a:=53) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 441 (Nat.pow_le_pow_right (by decide : 0<47) h)
    have hnum : 1000000 < 441*47^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case473 : Closed 1000000 441 338921 43 := by
  apply closed_split (a:=47) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 441 (Nat.pow_le_pow_right (by decide : 0<43) h)
    have hnum : 1000000 < 441*43^3 := by decide +kernel
    omega
  interval_cases e
  · exact case472
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case474 : Closed 1000000 441 338921 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 441 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 441*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact case473
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case475 : Closed 1000000 441 338921 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 441 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 441*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case474
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case476 : Closed 1000000 441 338921 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 441 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 441*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case475
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case477 : Closed 1000000 441 338921 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 441 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 441*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case476
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case478 : Closed 1000000 441 338921 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 441 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 441*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case477
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case479 : Closed 1000000 441 338921 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 441 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 441*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case478
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
