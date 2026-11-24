module

public import OddPerfect.TothTrillion.Part24
import Mathlib.Tactic.IntervalCases
import OddPerfect.TothIntervals
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case480 : Closed 1000000 441 338921 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 441 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 441*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case479
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case481 : Closed 1000000 441 338921 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 441 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 441*13^4 := by decide +kernel
    omega
  interval_cases e
  · exact case480
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case482 : Closed 1000000 4851 45076493 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 4851 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 4851*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case483 : Closed 1000000 441 338921 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 441 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 441*11^4 := by decide +kernel
    omega
  interval_cases e
  · exact case481
  · exact case482
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case484 : Closed 1000000 3087 16608097 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3087 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 3087*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case485 : Closed 1000000 3087 16608097 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3087 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 3087*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact case484
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case486 : Closed 1000000 3087 16608097 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3087 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 3087*11^3 := by decide +kernel
    omega
  interval_cases e
  · exact case485
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case487 : Closed 1000000 9 121 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 6 := by
    by_contra! h
    have := Nat.mul_le_mul_left 9 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 9*7^6 := by decide +kernel
    omega
  interval_cases e
  · exact case443
  · exact case471
  · exact case483
  · exact case486
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case488 : Closed 1000000 45 3751 149 := by
  apply closed_split (a:=151) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<149) h)
    have hnum : 1000000 < 45*149^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime_range 10 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case489 : Closed 1000000 45 3751 139 := by
  apply closed_split (a:=149) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<139) h)
    have hnum : 1000000 < 45*139^3 := by decide +kernel
    omega
  interval_cases e
  · exact case488
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case490 : Closed 1000000 45 3751 137 := by
  apply closed_split (a:=139) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<137) h)
    have hnum : 1000000 < 45*137^3 := by decide +kernel
    omega
  interval_cases e
  · exact case489
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case491 : Closed 1000000 45 3751 131 := by
  apply closed_split (a:=137) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<131) h)
    have hnum : 1000000 < 45*131^3 := by decide +kernel
    omega
  interval_cases e
  · exact case490
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case492 : Closed 1000000 45 3751 127 := by
  apply closed_split (a:=131) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<127) h)
    have hnum : 1000000 < 45*127^3 := by decide +kernel
    omega
  interval_cases e
  · exact case491
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case493 : Closed 1000000 45 3751 113 := by
  apply closed_split (a:=127) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<113) h)
    have hnum : 1000000 < 45*113^3 := by decide +kernel
    omega
  interval_cases e
  · exact case492
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case494 : Closed 1000000 45 3751 109 := by
  apply closed_split (a:=113) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<109) h)
    have hnum : 1000000 < 45*109^3 := by decide +kernel
    omega
  interval_cases e
  · exact case493
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case495 : Closed 1000000 45 3751 107 := by
  apply closed_split (a:=109) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<107) h)
    have hnum : 1000000 < 45*107^3 := by decide +kernel
    omega
  interval_cases e
  · exact case494
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case496 : Closed 1000000 45 3751 103 := by
  apply closed_split (a:=107) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<103) h)
    have hnum : 1000000 < 45*103^3 := by decide +kernel
    omega
  interval_cases e
  · exact case495
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case497 : Closed 1000000 45 3751 101 := by
  apply closed_split (a:=103) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<101) h)
    have hnum : 1000000 < 45*101^3 := by decide +kernel
    omega
  interval_cases e
  · exact case496
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case498 : Closed 1000000 45 3751 97 := by
  apply closed_split (a:=101) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<97) h)
    have hnum : 1000000 < 45*97^3 := by decide +kernel
    omega
  interval_cases e
  · exact case497
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case499 : Closed 1000000 45 3751 89 := by
  apply closed_split (a:=97) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<89) h)
    have hnum : 1000000 < 45*89^3 := by decide +kernel
    omega
  interval_cases e
  · exact case498
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
