module

public import OddPerfect.TothTrillion.Part22
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case440 : Closed 1000000 1089 1948705 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1089 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 1089*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case439
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case441 : Closed 1000000 1089 1948705 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1089 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 1089*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case440
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case442 : Closed 1000000 1089 1948705 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1089 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 1089*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact case441
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case443 : Closed 1000000 9 121 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 9 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 9*11^5 := by decide +kernel
    omega
  interval_cases e
  · exact case411
  · exact case437
  · exact case442
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case444 : Closed 1000000 63 6897 53 := by
  apply closed_split (a:=59) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 63 (Nat.pow_le_pow_right (by decide : 0<53) h)
    have hnum : 1000000 < 63*53^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case445 : Closed 1000000 63 6897 47 := by
  apply closed_split (a:=53) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 63 (Nat.pow_le_pow_right (by decide : 0<47) h)
    have hnum : 1000000 < 63*47^3 := by decide +kernel
    omega
  interval_cases e
  · exact case444
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case446 : Closed 1000000 63 6897 43 := by
  apply closed_split (a:=47) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 63 (Nat.pow_le_pow_right (by decide : 0<43) h)
    have hnum : 1000000 < 63*43^3 := by decide +kernel
    omega
  interval_cases e
  · exact case445
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case447 : Closed 1000000 63 6897 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 63 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 63*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact case446
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case448 : Closed 1000000 63 6897 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 63 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 63*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case447
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case449 : Closed 1000000 63 6897 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 63 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 63*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case448
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case450 : Closed 1000000 63 6897 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 63 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 63*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case449
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case451 : Closed 1000000 63 6897 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 63 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 63*23^4 := by decide +kernel
    omega
  interval_cases e
  · exact case450
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case452 : Closed 1000000 1197 2627757 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1197 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 1197*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case453 : Closed 1000000 63 6897 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 63 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 63*19^4 := by decide +kernel
    omega
  interval_cases e
  · exact case451
  · exact case452
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case454 : Closed 1000000 1071 2117379 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1071 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 1071*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case455 : Closed 1000000 1071 2117379 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1071 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 1071*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case454
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case456 : Closed 1000000 1071 2117379 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1071 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 1071*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case455
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case457 : Closed 1000000 63 6897 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 63 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 63*17^4 := by decide +kernel
    omega
  interval_cases e
  · exact case453
  · exact case456
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case458 : Closed 1000000 819 1262151 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 819 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 819*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case459 : Closed 1000000 819 1262151 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 819 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 819*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case458
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
