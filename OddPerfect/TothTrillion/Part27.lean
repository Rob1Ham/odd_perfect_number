module

public import OddPerfect.TothTrillion.Part26
import Mathlib.Tactic.IntervalCases
import OddPerfect.TothIntervals
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case520 : Closed 1000000 45 3751 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 45*19^4 := by decide +kernel
    omega
  interval_cases e
  · exact case516
  · exact case519
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case521 : Closed 1000000 765 1151557 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 765 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 765*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case522 : Closed 1000000 765 1151557 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 765 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 765*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case521
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case523 : Closed 1000000 765 1151557 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 765 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 765*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case522
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case524 : Closed 1000000 765 1151557 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 765 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 765*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case523
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case525 : Closed 1000000 45 3751 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 45*17^4 := by decide +kernel
    omega
  interval_cases e
  · exact case520
  · exact case524
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case526 : Closed 1000000 45 3751 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 45*13^4 := by decide +kernel
    omega
  interval_cases e
  · exact case525
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case527 : Closed 1000000 45 3751 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 45*11^5 := by decide +kernel
    omega
  interval_cases e
  · exact case526
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case528 : Closed 1000000 45 3751 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 6 := by
    by_contra! h
    have := Nat.mul_le_mul_left 45 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 45*7^6 := by decide +kernel
    omega
  interval_cases e
  · exact case527
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case529 : Closed 1000000 225 94501 61 := by
  apply closed_split (a:=67) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 225 (Nat.pow_le_pow_right (by decide : 0<61) h)
    have hnum : 1000000 < 225*61^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime_range 8 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case530 : Closed 1000000 225 94501 59 := by
  apply closed_split (a:=61) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 225 (Nat.pow_le_pow_right (by decide : 0<59) h)
    have hnum : 1000000 < 225*59^3 := by decide +kernel
    omega
  interval_cases e
  · exact case529
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case531 : Closed 1000000 225 94501 53 := by
  apply closed_split (a:=59) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 225 (Nat.pow_le_pow_right (by decide : 0<53) h)
    have hnum : 1000000 < 225*53^3 := by decide +kernel
    omega
  interval_cases e
  · exact case530
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case532 : Closed 1000000 225 94501 47 := by
  apply closed_split (a:=53) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 225 (Nat.pow_le_pow_right (by decide : 0<47) h)
    have hnum : 1000000 < 225*47^3 := by decide +kernel
    omega
  interval_cases e
  · exact case531
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case533 : Closed 1000000 225 94501 43 := by
  apply closed_split (a:=47) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 225 (Nat.pow_le_pow_right (by decide : 0<43) h)
    have hnum : 1000000 < 225*43^3 := by decide +kernel
    omega
  interval_cases e
  · exact case532
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case534 : Closed 1000000 225 94501 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 225 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 225*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact case533
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case535 : Closed 1000000 225 94501 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 225 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 225*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case534
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case536 : Closed 1000000 225 94501 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 225 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 225*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case535
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case537 : Closed 1000000 225 94501 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 225 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 225*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case536
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case538 : Closed 1000000 225 94501 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 225 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 225*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case537
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case539 : Closed 1000000 225 94501 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 225 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 225*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case538
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
