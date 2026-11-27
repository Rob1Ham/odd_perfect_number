module

public import OddPerfect.TothTrillion.Part02
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case40 : Closed 1000000 175 44517 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 175 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 175*13^4 := by decide +kernel
    omega
  interval_cases e
  · exact case37
  · exact case39
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case41 : Closed 1000000 1925 5920761 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1925 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 1925*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case42 : Closed 1000000 1925 5920761 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1925 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 1925*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case41
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case43 : Closed 1000000 1925 5920761 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1925 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 1925*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact case42
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case44 : Closed 1000000 175 44517 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 175 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 175*11^4 := by decide +kernel
    omega
  interval_cases e
  · exact case40
  · exact case43
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case45 : Closed 1000000 1225 2187581 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1225 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 1225*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case46 : Closed 1000000 1225 2187581 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1225 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 1225*11^3 := by decide +kernel
    omega
  interval_cases e
  · exact case45
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case47 : Closed 1000000 25 781 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 6 := by
    by_contra! h
    have := Nat.mul_le_mul_left 25 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 25*7^6 := by decide +kernel
    omega
  interval_cases e
  · exact case36
  · exact case44
  · exact case46
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case48 : Closed 1000000 875 1113267 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 875 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 875*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case49 : Closed 1000000 875 1113267 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 875 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 875*11^3 := by decide +kernel
    omega
  interval_cases e
  · exact case48
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case50 : Closed 1000000 6125 54706331 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 6125 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 6125*11^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case51 : Closed 1000000 125 19531 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 125 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 125*7^5 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=3) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact case49
  · exact case50
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case52 : Closed 1000000 4375 27832017 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 4375 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 4375*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case53 : Closed 1000000 4375 27832017 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 4375 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 4375*11^3 := by decide +kernel
    omega
  interval_cases e
  · exact case52
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case54 : Closed 1000000 625 488281 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 625 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 625*7^4 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=3) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact case53
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case55 : Closed 1000000 3125 12207031 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3125 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 3125*7^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case56 : Closed 1000000 15625 305175781 7 := by
  apply closed_split (a:=11) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15625 (Nat.pow_le_pow_right (by decide : 0<7) h)
    have hnum : 1000000 < 15625*7^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case57 : Closed 1000000 1 1 5 := by
  apply closed_split (a:=7) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 9 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1 (Nat.pow_le_pow_right (by decide : 0<5) h)
    have hnum : 1000000 < 1*5^9 := by decide +kernel
    omega
  interval_cases e
  · exact case2
  · exact case33
  · exact case47
  · exact case51
  · exact case54
  · exact case55
  · exact case56
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case58 : Closed 1000000 3 13 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 3*23^5 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=3) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case59 : Closed 1000000 57 4953 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 57 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 57*23^4 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
