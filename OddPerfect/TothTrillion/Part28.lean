module

public import OddPerfect.TothTrillion.Part27
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case540 : Closed 1000000 225 94501 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 225 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 225*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case539
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case541 : Closed 1000000 225 94501 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 225 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 225*13^4 := by decide +kernel
    omega
  interval_cases e
  · exact case540
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case542 : Closed 1000000 225 94501 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 225 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 225*11^4 := by decide +kernel
    omega
  interval_cases e
  · exact case541
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case543 : Closed 1000000 225 94501 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 225 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 225*7^5 := by decide +kernel
    omega
  interval_cases e
  · exact case542
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case544 : Closed 1000000 1125 2363251 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1125 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 1125*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case545 : Closed 1000000 1125 2363251 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1125 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 1125*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case544
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case546 : Closed 1000000 1125 2363251 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1125 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 1125*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case545
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case547 : Closed 1000000 1125 2363251 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1125 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 1125*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case546
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case548 : Closed 1000000 1125 2363251 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1125 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 1125*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact case547
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case549 : Closed 1000000 1125 2363251 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1125 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 1125*11^3 := by decide +kernel
    omega
  interval_cases e
  · exact case548
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case550 : Closed 1000000 1125 2363251 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1125 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 1125*7^4 := by decide +kernel
    omega
  interval_cases e
  · exact case549
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case551 : Closed 1000000 5625 59082001 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 5625 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 5625*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case552 : Closed 1000000 5625 59082001 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 5625 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 5625*11^3 := by decide +kernel
    omega
  interval_cases e
  · exact case551
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case553 : Closed 1000000 5625 59082001 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 5625 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 5625*7^3 := by decide +kernel
    omega
  interval_cases e
  · exact case552
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case554 : Closed 1000000 9 121 5 := by
  apply closed_split (a:=7) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 8 := by
    by_contra! h
    have := Nat.mul_le_mul_left 9 (Nat.pow_le_pow_right (by decide : 0<5) h)
    have hnum : 1000000 < 9*5^8 := by decide +kernel
    omega
  interval_cases e
  · exact case487
  · exact case528
  · exact case543
  · exact case550
  · exact case553
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case555 : Closed 1000000 621 604429 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 621 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 621*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case556 : Closed 1000000 621 604429 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 621 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 621*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case555
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case557 : Closed 1000000 27 1093 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 27 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 27*23^4 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=3) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact case556
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case558 : Closed 1000000 513 416433 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 513 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 513*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case559 : Closed 1000000 513 416433 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 513 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 513*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case558
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
