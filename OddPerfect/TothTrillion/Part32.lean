module

public import OddPerfect.TothTrillion.Part31
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case620 : Closed 1000000 27 1093 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 6 := by
    by_contra! h
    have := Nat.mul_le_mul_left 27 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 27*7^6 := by decide +kernel
    omega
  interval_cases e
  · exact case595
  · exact case614
  · exact case619
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case621 : Closed 1000000 135 33883 83 := by
  apply closed_split (a:=89) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 135 (Nat.pow_le_pow_right (by decide : 0<83) h)
    have hnum : 1000000 < 135*83^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case622 : Closed 1000000 135 33883 79 := by
  apply closed_split (a:=83) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 135 (Nat.pow_le_pow_right (by decide : 0<79) h)
    have hnum : 1000000 < 135*79^3 := by decide +kernel
    omega
  interval_cases e
  · exact case621
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case623 : Closed 1000000 135 33883 73 := by
  apply closed_split (a:=79) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 135 (Nat.pow_le_pow_right (by decide : 0<73) h)
    have hnum : 1000000 < 135*73^3 := by decide +kernel
    omega
  interval_cases e
  · exact case622
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case624 : Closed 1000000 135 33883 71 := by
  apply closed_split (a:=73) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 135 (Nat.pow_le_pow_right (by decide : 0<71) h)
    have hnum : 1000000 < 135*71^3 := by decide +kernel
    omega
  interval_cases e
  · exact case623
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case625 : Closed 1000000 135 33883 67 := by
  apply closed_split (a:=71) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 135 (Nat.pow_le_pow_right (by decide : 0<67) h)
    have hnum : 1000000 < 135*67^3 := by decide +kernel
    omega
  interval_cases e
  · exact case624
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case626 : Closed 1000000 135 33883 61 := by
  apply closed_split (a:=67) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 135 (Nat.pow_le_pow_right (by decide : 0<61) h)
    have hnum : 1000000 < 135*61^3 := by decide +kernel
    omega
  interval_cases e
  · exact case625
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case627 : Closed 1000000 135 33883 59 := by
  apply closed_split (a:=61) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 135 (Nat.pow_le_pow_right (by decide : 0<59) h)
    have hnum : 1000000 < 135*59^3 := by decide +kernel
    omega
  interval_cases e
  · exact case626
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case628 : Closed 1000000 135 33883 53 := by
  apply closed_split (a:=59) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 135 (Nat.pow_le_pow_right (by decide : 0<53) h)
    have hnum : 1000000 < 135*53^3 := by decide +kernel
    omega
  interval_cases e
  · exact case627
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case629 : Closed 1000000 135 33883 47 := by
  apply closed_split (a:=53) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 135 (Nat.pow_le_pow_right (by decide : 0<47) h)
    have hnum : 1000000 < 135*47^3 := by decide +kernel
    omega
  interval_cases e
  · exact case628
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case630 : Closed 1000000 135 33883 43 := by
  apply closed_split (a:=47) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 135 (Nat.pow_le_pow_right (by decide : 0<43) h)
    have hnum : 1000000 < 135*43^3 := by decide +kernel
    omega
  interval_cases e
  · exact case629
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case631 : Closed 1000000 135 33883 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 135 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 135*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact case630
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case632 : Closed 1000000 135 33883 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 135 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 135*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case631
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case633 : Closed 1000000 135 33883 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 135 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 135*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case632
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case634 : Closed 1000000 135 33883 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 135 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 135*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case633
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case635 : Closed 1000000 135 33883 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 135 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 135*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case634
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case636 : Closed 1000000 135 33883 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 135 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 135*19^4 := by decide +kernel
    omega
  interval_cases e
  · exact case635
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case637 : Closed 1000000 2295 10402081 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2295 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 2295*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case638 : Closed 1000000 135 33883 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 135 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 135*17^4 := by decide +kernel
    omega
  interval_cases e
  · exact case636
  · exact case637
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case639 : Closed 1000000 135 33883 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 135 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 135*13^4 := by decide +kernel
    omega
  interval_cases e
  · exact case638
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
