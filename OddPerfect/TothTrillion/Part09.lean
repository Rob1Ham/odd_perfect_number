module

public import OddPerfect.TothTrillion.Part08
import Mathlib.Tactic.IntervalCases
import OddPerfect.TothIntervals
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case160 : Closed 1000000 273 135603 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 273 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 273*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case159
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case161 : Closed 1000000 273 135603 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 273 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 273*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case160
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case162 : Closed 1000000 273 135603 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 273 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 273*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case161
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case163 : Closed 1000000 273 135603 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 273 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 273*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case162
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case164 : Closed 1000000 21 741 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 21 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 21*13^5 := by decide +kernel
    omega
  interval_cases e
  · exact case152
  · exact case163
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case165 : Closed 1000000 231 98553 61 := by
  apply closed_split (a:=67) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 231 (Nat.pow_le_pow_right (by decide : 0<61) h)
    have hnum : 1000000 < 231*61^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime_range 8 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case166 : Closed 1000000 231 98553 59 := by
  apply closed_split (a:=61) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 231 (Nat.pow_le_pow_right (by decide : 0<59) h)
    have hnum : 1000000 < 231*59^3 := by decide +kernel
    omega
  interval_cases e
  · exact case165
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case167 : Closed 1000000 231 98553 53 := by
  apply closed_split (a:=59) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 231 (Nat.pow_le_pow_right (by decide : 0<53) h)
    have hnum : 1000000 < 231*53^3 := by decide +kernel
    omega
  interval_cases e
  · exact case166
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case168 : Closed 1000000 231 98553 47 := by
  apply closed_split (a:=53) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 231 (Nat.pow_le_pow_right (by decide : 0<47) h)
    have hnum : 1000000 < 231*47^3 := by decide +kernel
    omega
  interval_cases e
  · exact case167
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case169 : Closed 1000000 231 98553 43 := by
  apply closed_split (a:=47) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 231 (Nat.pow_le_pow_right (by decide : 0<43) h)
    have hnum : 1000000 < 231*43^3 := by decide +kernel
    omega
  interval_cases e
  · exact case168
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case170 : Closed 1000000 231 98553 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 231 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 231*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact case169
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case171 : Closed 1000000 231 98553 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 231 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 231*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case170
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case172 : Closed 1000000 231 98553 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 231 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 231*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case171
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case173 : Closed 1000000 231 98553 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 231 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 231*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case172
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case174 : Closed 1000000 231 98553 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 231 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 231*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case173
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case175 : Closed 1000000 231 98553 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 231 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 231*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case174
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case176 : Closed 1000000 231 98553 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 231 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 231*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case175
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case177 : Closed 1000000 3003 18035199 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3003 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 3003*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case178 : Closed 1000000 231 98553 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 231 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 231*13^4 := by decide +kernel
    omega
  interval_cases e
  · exact case176
  · exact case177
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case179 : Closed 1000000 2541 11933805 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2541 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 2541*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
