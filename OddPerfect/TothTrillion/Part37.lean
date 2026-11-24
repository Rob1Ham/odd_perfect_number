module

public import OddPerfect.TothTrillion.Part36
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case720 : Closed 1000000 1215 2745763 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1215 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 1215*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case721 : Closed 1000000 1215 2745763 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1215 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 1215*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case720
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case722 : Closed 1000000 1215 2745763 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1215 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 1215*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case721
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case723 : Closed 1000000 1215 2745763 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1215 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 1215*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact case722
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case724 : Closed 1000000 1215 2745763 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1215 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 1215*11^3 := by decide +kernel
    omega
  interval_cases e
  · exact case723
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case725 : Closed 1000000 1215 2745763 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1215 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 1215*7^4 := by decide +kernel
    omega
  interval_cases e
  · exact case724
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case726 : Closed 1000000 6075 69175513 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 6075 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 6075*11^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case727 : Closed 1000000 6075 69175513 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 6075 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 6075*7^3 := by decide +kernel
    omega
  interval_cases e
  · exact case726
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case728 : Closed 1000000 243 88573 5 := by
  apply closed_split (a:=7) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 6 := by
    by_contra! h
    have := Nat.mul_le_mul_left 243 (Nat.pow_le_pow_right (by decide : 0<5) h)
    have hnum : 1000000 < 243*5^6 := by decide +kernel
    omega
  interval_cases e
  · exact case719
  · exact case725
  · exact case727
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case729 : Closed 1000000 729 797161 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 729 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 729*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case730 : Closed 1000000 729 797161 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 729 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 729*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case729
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case731 : Closed 1000000 729 797161 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 729 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 729*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact case730
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case732 : Closed 1000000 729 797161 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 729 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 729*11^4 := by decide +kernel
    omega
  interval_cases e
  · exact case731
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case733 : Closed 1000000 5103 45438177 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 5103 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 5103*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case734 : Closed 1000000 5103 45438177 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 5103 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 5103*11^3 := by decide +kernel
    omega
  interval_cases e
  · exact case733
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case735 : Closed 1000000 729 797161 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 729 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 729*7^4 := by decide +kernel
    omega
  interval_cases e
  · exact case732
  · exact case734
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case736 : Closed 1000000 3645 24711991 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3645 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 3645*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case737 : Closed 1000000 3645 24711991 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3645 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 3645*11^3 := by decide +kernel
    omega
  interval_cases e
  · exact case736
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case738 : Closed 1000000 3645 24711991 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3645 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 3645*7^3 := by decide +kernel
    omega
  interval_cases e
  · exact case737
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case739 : Closed 1000000 18225 622582741 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 18225 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 18225*7^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
