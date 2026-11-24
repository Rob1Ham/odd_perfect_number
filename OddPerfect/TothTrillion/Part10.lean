module

public import OddPerfect.TothTrillion.Part09
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case180 : Closed 1000000 2541 11933805 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2541 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 2541*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case179
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case181 : Closed 1000000 2541 11933805 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2541 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 2541*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact case180
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case182 : Closed 1000000 21 741 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 21 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 21*11^5 := by decide +kernel
    omega
  interval_cases e
  · exact case164
  · exact case178
  · exact case181
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case183 : Closed 1000000 147 36413 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 147 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 147*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case184 : Closed 1000000 147 36413 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 147 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 147*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case183
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case185 : Closed 1000000 147 36413 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 147 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 147*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case184
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case186 : Closed 1000000 2499 11178791 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2499 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 2499*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case187 : Closed 1000000 147 36413 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 147 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 147*17^4 := by decide +kernel
    omega
  interval_cases e
  · exact case185
  · exact case186
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case188 : Closed 1000000 1911 6663579 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1911 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 1911*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case189 : Closed 1000000 1911 6663579 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1911 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 1911*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case188
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case190 : Closed 1000000 147 36413 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 147 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 147*13^4 := by decide +kernel
    omega
  interval_cases e
  · exact case187
  · exact case189
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case191 : Closed 1000000 1617 4842929 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1617 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 1617*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case192 : Closed 1000000 1617 4842929 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1617 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 1617*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case191
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case193 : Closed 1000000 1617 4842929 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1617 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 1617*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case192
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case194 : Closed 1000000 1617 4842929 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1617 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 1617*13^3 := by decide +kernel
    omega
  interval_cases e
  · exact case193
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case195 : Closed 1000000 147 36413 11 := by
  apply closed_split (a:=13) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 147 (Nat.pow_le_pow_right (by decide : 0<11) h)
    have hnum : 1000000 < 147*11^4 := by decide +kernel
    omega
  interval_cases e
  · exact case190
  · exact case194
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case196 : Closed 1000000 1029 1784341 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1029 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 1029*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case197 : Closed 1000000 1029 1784341 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1029 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 1029*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case196
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case198 : Closed 1000000 1029 1784341 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1029 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 1029*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case197
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case199 : Closed 1000000 1029 1784341 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1029 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 1029*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case198
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
