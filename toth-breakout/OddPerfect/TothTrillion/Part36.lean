module

public import OddPerfect.TothTrillion.Part35
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case700 : Closed 1000000 2025 7685821 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2025 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 2025*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case699
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case701 : Closed 1000000 2025 7685821 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2025 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 2025*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact case700
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case702 : Closed 1000000 2025 7685821 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2025 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 2025*11^3 := by decide +kernel
    omega
  interval_cases e
  · exact case701
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case703 : Closed 1000000 2025 7685821 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2025 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 2025*7^4 := by decide +kernel
    omega
  interval_cases e
  · exact case702
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case704 : Closed 1000000 10125 192204571 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 10125 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 10125*7^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case705 : Closed 1000000 81 9841 5 := by
  apply closed_split (a:=7) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 6 := by
    by_contra! h
    have := Nat.mul_le_mul_left 81 (Nat.pow_le_pow_right (by decide : 0<5) h)
    have hnum : 1000000 < 81*5^6 := by decide +kernel
    omega
  interval_cases e
  · exact case686
  · exact case698
  · exact case703
  · exact case704
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case706 : Closed 1000000 243 88573 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 243 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 243*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case707 : Closed 1000000 243 88573 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 243 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 243*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case706
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case708 : Closed 1000000 3159 16208859 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3159 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 3159*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case709 : Closed 1000000 243 88573 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 243 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 243*13^4 := by decide +kernel
    omega
  interval_cases e
  · exact case707
  · exact case708
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case710 : Closed 1000000 2673 11780209 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2673 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 2673*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case711 : Closed 1000000 2673 11780209 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2673 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 2673*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case710
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case712 : Closed 1000000 2673 11780209 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2673 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 2673*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact case711
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case713 : Closed 1000000 243 88573 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 243 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 243*11^4 := by decide +kernel
    omega
  interval_cases e
  · exact case709
  · exact case712
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case714 : Closed 1000000 1701 5048661 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1701 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 1701*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case715 : Closed 1000000 1701 5048661 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1701 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 1701*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case714
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case716 : Closed 1000000 1701 5048661 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1701 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 1701*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case715
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case717 : Closed 1000000 1701 5048661 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1701 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 1701*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact case716
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case718 : Closed 1000000 1701 5048661 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1701 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 1701*11^3 := by decide +kernel
    omega
  interval_cases e
  · exact case717
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case719 : Closed 1000000 243 88573 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 243 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 243*7^5 := by decide +kernel
    omega
  interval_cases e
  · exact case713
  · exact case718
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
