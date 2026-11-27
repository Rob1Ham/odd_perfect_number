module

public import OddPerfect.TothTrillion.Part30
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case600 : Closed 1000000 189 62301 43 := by
  apply closed_split (a:=47) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 189 (Nat.pow_le_pow_right (by decide : 0<43) h)
    have hnum : 1000000 < 189*43^3 := by decide +kernel
    omega
  interval_cases e
  · exact case599
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case601 : Closed 1000000 189 62301 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 189 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 189*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact case600
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case602 : Closed 1000000 189 62301 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 189 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 189*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case601
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case603 : Closed 1000000 189 62301 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 189 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 189*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case602
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case604 : Closed 1000000 189 62301 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 189 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 189*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case603
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case605 : Closed 1000000 189 62301 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 189 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 189*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case604
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case606 : Closed 1000000 189 62301 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 189 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 189*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case605
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case607 : Closed 1000000 189 62301 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 189 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 189*17^4 := by decide +kernel
    omega
  interval_cases e
  · exact case606
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case608 : Closed 1000000 2457 11401083 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2457 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 2457*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case609 : Closed 1000000 2457 11401083 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2457 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 2457*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case608
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case610 : Closed 1000000 189 62301 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 189 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 189*13^4 := by decide +kernel
    omega
  interval_cases e
  · exact case607
  · exact case609
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case611 : Closed 1000000 2079 8286033 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2079 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 2079*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case612 : Closed 1000000 2079 8286033 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2079 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 2079*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case611
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case613 : Closed 1000000 2079 8286033 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2079 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 2079*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact case612
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case614 : Closed 1000000 189 62301 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 189 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 189*11^4 := by decide +kernel
    omega
  interval_cases e
  · exact case610
  · exact case613
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case615 : Closed 1000000 1323 3061493 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1323 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 1323*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case616 : Closed 1000000 1323 3061493 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1323 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 1323*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case615
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case617 : Closed 1000000 1323 3061493 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1323 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 1323*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case616
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case618 : Closed 1000000 1323 3061493 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1323 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 1323*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact case617
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case619 : Closed 1000000 1323 3061493 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1323 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 1323*11^3 := by decide +kernel
    omega
  interval_cases e
  · exact case618
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
