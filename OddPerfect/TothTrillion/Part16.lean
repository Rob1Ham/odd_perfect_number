module

public import OddPerfect.TothTrillion.Part15
import Mathlib.Tactic.IntervalCases
import OddPerfect.TothIntervals
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case300 : Closed 1000000 195 73749 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 195 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 195*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case299
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case301 : Closed 1000000 195 73749 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 195 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 195*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case300
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case302 : Closed 1000000 195 73749 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 195 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 195*17^4 := by decide +kernel
    omega
  interval_cases e
  · exact case301
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case303 : Closed 1000000 2535 12469223 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2535 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 2535*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case304 : Closed 1000000 2535 12469223 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 2535 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 2535*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case303
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case305 : Closed 1000000 15 403 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 15 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 15*13^5 := by decide +kernel
    omega
  interval_cases e
  · exact case288
  · exact case302
  · exact case304
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case306 : Closed 1000000 165 53599 73 := by
  apply closed_split (a:=79) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 165 (Nat.pow_le_pow_right (by decide : 0<73) h)
    have hnum : 1000000 < 165*73^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime_range 8 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case307 : Closed 1000000 165 53599 71 := by
  apply closed_split (a:=73) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 165 (Nat.pow_le_pow_right (by decide : 0<71) h)
    have hnum : 1000000 < 165*71^3 := by decide +kernel
    omega
  interval_cases e
  · exact case306
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case308 : Closed 1000000 165 53599 67 := by
  apply closed_split (a:=71) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 165 (Nat.pow_le_pow_right (by decide : 0<67) h)
    have hnum : 1000000 < 165*67^3 := by decide +kernel
    omega
  interval_cases e
  · exact case307
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case309 : Closed 1000000 165 53599 61 := by
  apply closed_split (a:=67) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 165 (Nat.pow_le_pow_right (by decide : 0<61) h)
    have hnum : 1000000 < 165*61^3 := by decide +kernel
    omega
  interval_cases e
  · exact case308
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case310 : Closed 1000000 165 53599 59 := by
  apply closed_split (a:=61) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 165 (Nat.pow_le_pow_right (by decide : 0<59) h)
    have hnum : 1000000 < 165*59^3 := by decide +kernel
    omega
  interval_cases e
  · exact case309
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case311 : Closed 1000000 165 53599 53 := by
  apply closed_split (a:=59) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 165 (Nat.pow_le_pow_right (by decide : 0<53) h)
    have hnum : 1000000 < 165*53^3 := by decide +kernel
    omega
  interval_cases e
  · exact case310
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case312 : Closed 1000000 165 53599 47 := by
  apply closed_split (a:=53) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 165 (Nat.pow_le_pow_right (by decide : 0<47) h)
    have hnum : 1000000 < 165*47^3 := by decide +kernel
    omega
  interval_cases e
  · exact case311
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case313 : Closed 1000000 165 53599 43 := by
  apply closed_split (a:=47) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 165 (Nat.pow_le_pow_right (by decide : 0<43) h)
    have hnum : 1000000 < 165*43^3 := by decide +kernel
    omega
  interval_cases e
  · exact case312
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case314 : Closed 1000000 165 53599 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 165 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 165*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact case313
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case315 : Closed 1000000 165 53599 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 165 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 165*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case314
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case316 : Closed 1000000 165 53599 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 165 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 165*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case315
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case317 : Closed 1000000 165 53599 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 165 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 165*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case316
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case318 : Closed 1000000 165 53599 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 165 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 165*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case317
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

theorem case319 : Closed 1000000 165 53599 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 165 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 165*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case318
  · exact closed_abundant (by decide +kernel) (by decide +kernel)
  · exact closed_abundant (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
