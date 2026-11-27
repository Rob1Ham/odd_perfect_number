module

public import OddPerfect.TothTrillion.Part21
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case420 : Closed 1000000 99 16093 59 := by
  apply closed_split (a:=61) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 99 (Nat.pow_le_pow_right (by decide : 0<59) h)
    have hnum : 1000000 < 99*59^3 := by decide +kernel
    omega
  interval_cases e
  · exact case419
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case421 : Closed 1000000 99 16093 53 := by
  apply closed_split (a:=59) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 99 (Nat.pow_le_pow_right (by decide : 0<53) h)
    have hnum : 1000000 < 99*53^3 := by decide +kernel
    omega
  interval_cases e
  · exact case420
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case422 : Closed 1000000 99 16093 47 := by
  apply closed_split (a:=53) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 99 (Nat.pow_le_pow_right (by decide : 0<47) h)
    have hnum : 1000000 < 99*47^3 := by decide +kernel
    omega
  interval_cases e
  · exact case421
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case423 : Closed 1000000 99 16093 43 := by
  apply closed_split (a:=47) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 99 (Nat.pow_le_pow_right (by decide : 0<43) h)
    have hnum : 1000000 < 99*43^3 := by decide +kernel
    omega
  interval_cases e
  · exact case422
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case424 : Closed 1000000 99 16093 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 99 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 99*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact case423
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case425 : Closed 1000000 99 16093 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 99 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 99*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case424
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case426 : Closed 1000000 99 16093 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 99 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 99*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case425
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case427 : Closed 1000000 99 16093 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 99 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 99*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case426
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case428 : Closed 1000000 99 16093 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 99 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 99*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case427
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case429 : Closed 1000000 1881 6131433 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1881 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 1881*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case430 : Closed 1000000 99 16093 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 99 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 99*19^4 := by decide +kernel
    omega
  interval_cases e
  · exact case428
  · exact case429
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case431 : Closed 1000000 1683 4940551 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1683 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 1683*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case432 : Closed 1000000 1683 4940551 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1683 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 1683*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case431
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case433 : Closed 1000000 99 16093 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 99 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 99*17^4 := by decide +kernel
    omega
  interval_cases e
  · exact case430
  · exact case432
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case434 : Closed 1000000 1287 2945019 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1287 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 1287*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case435 : Closed 1000000 1287 2945019 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1287 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 1287*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case434
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case436 : Closed 1000000 1287 2945019 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1287 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 1287*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case435
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case437 : Closed 1000000 99 16093 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 99 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 99*13^4 := by decide +kernel
    omega
  interval_cases e
  · exact case433
  · exact case436
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case438 : Closed 1000000 1089 1948705 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1089 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 1089*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case439 : Closed 1000000 1089 1948705 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1089 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 1089*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case438
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
