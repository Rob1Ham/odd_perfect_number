module

public import OddPerfect.TothTrillion.Part19
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case380 : Closed 1000000 207 66913 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 207 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 207*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case379
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case381 : Closed 1000000 9 121 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 9 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 9*23^4 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=3) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact case380
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case382 : Closed 1000000 171 46101 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 171 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 171*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case383 : Closed 1000000 171 46101 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 171 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 171*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case382
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case384 : Closed 1000000 171 46101 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 171 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 171*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case383
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case385 : Closed 1000000 9 121 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 9 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 9*19^4 := by decide +kernel
    omega
  interval_cases e
  · exact case381
  · exact case384
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case386 : Closed 1000000 153 37147 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 153 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 153*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case387 : Closed 1000000 153 37147 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 153 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 153*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case386
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case388 : Closed 1000000 153 37147 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 153 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 153*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case387
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case389 : Closed 1000000 153 37147 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 153 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 153*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case388
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case390 : Closed 1000000 153 37147 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 153 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 153*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case389
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case391 : Closed 1000000 153 37147 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 153 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 153*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case390
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case392 : Closed 1000000 2601 10737661 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2601 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 2601*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case393 : Closed 1000000 9 121 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 9 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 9*17^5 := by decide +kernel
    omega
  interval_cases e
  · exact case385
  · exact case391
  · exact case392
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case394 : Closed 1000000 117 22143 67 := by
  apply closed_split (a:=71) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 117 (Nat.pow_le_pow_right (by decide : 0<67) h)
    have hnum : 1000000 < 117*67^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case395 : Closed 1000000 117 22143 61 := by
  apply closed_split (a:=67) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 117 (Nat.pow_le_pow_right (by decide : 0<61) h)
    have hnum : 1000000 < 117*61^3 := by decide +kernel
    omega
  interval_cases e
  · exact case394
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case396 : Closed 1000000 117 22143 59 := by
  apply closed_split (a:=61) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 117 (Nat.pow_le_pow_right (by decide : 0<59) h)
    have hnum : 1000000 < 117*59^3 := by decide +kernel
    omega
  interval_cases e
  · exact case395
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case397 : Closed 1000000 117 22143 53 := by
  apply closed_split (a:=59) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 117 (Nat.pow_le_pow_right (by decide : 0<53) h)
    have hnum : 1000000 < 117*53^3 := by decide +kernel
    omega
  interval_cases e
  · exact case396
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case398 : Closed 1000000 117 22143 47 := by
  apply closed_split (a:=53) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 117 (Nat.pow_le_pow_right (by decide : 0<47) h)
    have hnum : 1000000 < 117*47^3 := by decide +kernel
    omega
  interval_cases e
  · exact case397
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case399 : Closed 1000000 117 22143 43 := by
  apply closed_split (a:=47) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 117 (Nat.pow_le_pow_right (by decide : 0<43) h)
    have hnum : 1000000 < 117*43^3 := by decide +kernel
    omega
  interval_cases e
  · exact case398
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
