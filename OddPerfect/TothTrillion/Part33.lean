module

public import OddPerfect.TothTrillion.Part32
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case640 : Closed 1000000 135 33883 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 135 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 135*11^4 := by decide +kernel
    omega
  interval_cases e
  · exact case639
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case641 : Closed 1000000 135 33883 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 135 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 135*7^5 := by decide +kernel
    omega
  interval_cases e
  · exact case640
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case642 : Closed 1000000 675 853633 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 675 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 675*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case643 : Closed 1000000 675 853633 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 675 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 675*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case642
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case644 : Closed 1000000 675 853633 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 675 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 675*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case643
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case645 : Closed 1000000 675 853633 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 675 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 675*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case644
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case646 : Closed 1000000 675 853633 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 675 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 675*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case645
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case647 : Closed 1000000 675 853633 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 675 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 675*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case646
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case648 : Closed 1000000 675 853633 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 675 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 675*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact case647
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case649 : Closed 1000000 675 853633 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 675 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 675*11^4 := by decide +kernel
    omega
  interval_cases e
  · exact case648
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case650 : Closed 1000000 675 853633 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 675 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 675*7^4 := by decide +kernel
    omega
  interval_cases e
  · exact case649
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case651 : Closed 1000000 3375 21347383 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3375 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 3375*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case652 : Closed 1000000 3375 21347383 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3375 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 3375*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact case651
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case653 : Closed 1000000 3375 21347383 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3375 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 3375*11^3 := by decide +kernel
    omega
  interval_cases e
  · exact case652
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case654 : Closed 1000000 3375 21347383 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3375 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 3375*7^3 := by decide +kernel
    omega
  interval_cases e
  · exact case653
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case655 : Closed 1000000 16875 533691133 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 16875 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 16875*7^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case656 : Closed 1000000 27 1093 5 := by
  apply closed_split (a:=7) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 7 := by
    by_contra! h
    have := Nat.mul_le_mul_left 27 (Nat.pow_le_pow_right (by decide : 0<5) h)
    have hnum : 1000000 < 27*5^7 := by decide +kernel
    omega
  interval_cases e
  · exact case620
  · exact case641
  · exact case650
  · exact case654
  · exact case655
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case657 : Closed 1000000 81 9841 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 81 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 81*23^4 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case658 : Closed 1000000 1539 3749421 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1539 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 1539*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case659 : Closed 1000000 81 9841 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 81 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 81*19^4 := by decide +kernel
    omega
  interval_cases e
  · exact case657
  · exact case658
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
