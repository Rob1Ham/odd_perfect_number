module

public import OddPerfect.TothTrillion.Part34
import Mathlib.Tactic.IntervalCases
import OddPerfect.TothIntervals
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case680 : Closed 1000000 567 560937 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 567 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 567*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case679
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case681 : Closed 1000000 567 560937 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 567 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 567*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case680
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case682 : Closed 1000000 567 560937 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 567 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 567*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact case681
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case683 : Closed 1000000 567 560937 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 567 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 567*11^4 := by decide +kernel
    omega
  interval_cases e
  · exact case682
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case684 : Closed 1000000 3969 27564641 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3969 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 3969*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case685 : Closed 1000000 3969 27564641 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3969 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 3969*11^3 := by decide +kernel
    omega
  interval_cases e
  · exact case684
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case686 : Closed 1000000 81 9841 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 81 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 81*7^5 := by decide +kernel
    omega
  interval_cases e
  · exact case674
  · exact case683
  · exact case685
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case687 : Closed 1000000 405 305071 47 := by
  apply closed_split (a:=53) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 405 (Nat.pow_le_pow_right (by decide : 0<47) h)
    have hnum : 1000000 < 405*47^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime_range 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case688 : Closed 1000000 405 305071 43 := by
  apply closed_split (a:=47) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 405 (Nat.pow_le_pow_right (by decide : 0<43) h)
    have hnum : 1000000 < 405*43^3 := by decide +kernel
    omega
  interval_cases e
  · exact case687
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case689 : Closed 1000000 405 305071 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 405 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 405*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact case688
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case690 : Closed 1000000 405 305071 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 405 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 405*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case689
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case691 : Closed 1000000 405 305071 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 405 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 405*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case690
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case692 : Closed 1000000 405 305071 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 405 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 405*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case691
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case693 : Closed 1000000 405 305071 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 405 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 405*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case692
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case694 : Closed 1000000 405 305071 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 405 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 405*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case693
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case695 : Closed 1000000 405 305071 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 405 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 405*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case694
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case696 : Closed 1000000 405 305071 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 405 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 405*13^4 := by decide +kernel
    omega
  interval_cases e
  · exact case695
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case697 : Closed 1000000 405 305071 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 405 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 405*11^4 := by decide +kernel
    omega
  interval_cases e
  · exact case696
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case698 : Closed 1000000 405 305071 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 405 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 405*7^5 := by decide +kernel
    omega
  interval_cases e
  · exact case697
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case699 : Closed 1000000 2025 7685821 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2025 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 2025*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
