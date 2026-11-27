module

public import OddPerfect.TothTrillion.Part20
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case400 : Closed 1000000 117 22143 41 := by
  apply closed_split (a:=43) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 117 (Nat.pow_le_pow_right (by decide : 0<41) h)
    have hnum : 1000000 < 117*41^3 := by decide +kernel
    omega
  interval_cases e
  · exact case399
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case401 : Closed 1000000 117 22143 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 117 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 117*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact case400
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case402 : Closed 1000000 117 22143 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 117 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 117*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact case401
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case403 : Closed 1000000 117 22143 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 117 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 117*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case402
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case404 : Closed 1000000 117 22143 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 117 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 117*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case403
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case405 : Closed 1000000 117 22143 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 117 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 117*19^4 := by decide +kernel
    omega
  interval_cases e
  · exact case404
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case406 : Closed 1000000 1989 6797901 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1989 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 1989*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case407 : Closed 1000000 117 22143 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 117 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 117*17^4 := by decide +kernel
    omega
  interval_cases e
  · exact case405
  · exact case406
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case408 : Closed 1000000 1521 3743861 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1521 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 1521*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case409 : Closed 1000000 1521 3743861 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1521 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 1521*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case408
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case410 : Closed 1000000 1521 3743861 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1521 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 1521*17^3 := by decide +kernel
    omega
  interval_cases e
  · exact case409
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case411 : Closed 1000000 9 121 13 := by
  apply closed_split (a:=17) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 9 (Nat.pow_le_pow_right (by decide : 0<13) h)
    have hnum : 1000000 < 9*13^5 := by decide +kernel
    omega
  interval_cases e
  · exact case393
  · exact case407
  · exact case410
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case412 : Closed 1000000 99 16093 97 := by
  apply closed_split (a:=101) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 99 (Nat.pow_le_pow_right (by decide : 0<97) h)
    have hnum : 1000000 < 99*97^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case413 : Closed 1000000 99 16093 89 := by
  apply closed_split (a:=97) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 99 (Nat.pow_le_pow_right (by decide : 0<89) h)
    have hnum : 1000000 < 99*89^3 := by decide +kernel
    omega
  interval_cases e
  · exact case412
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case414 : Closed 1000000 99 16093 83 := by
  apply closed_split (a:=89) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 99 (Nat.pow_le_pow_right (by decide : 0<83) h)
    have hnum : 1000000 < 99*83^3 := by decide +kernel
    omega
  interval_cases e
  · exact case413
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case415 : Closed 1000000 99 16093 79 := by
  apply closed_split (a:=83) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 99 (Nat.pow_le_pow_right (by decide : 0<79) h)
    have hnum : 1000000 < 99*79^3 := by decide +kernel
    omega
  interval_cases e
  · exact case414
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case416 : Closed 1000000 99 16093 73 := by
  apply closed_split (a:=79) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 99 (Nat.pow_le_pow_right (by decide : 0<73) h)
    have hnum : 1000000 < 99*73^3 := by decide +kernel
    omega
  interval_cases e
  · exact case415
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case417 : Closed 1000000 99 16093 71 := by
  apply closed_split (a:=73) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 99 (Nat.pow_le_pow_right (by decide : 0<71) h)
    have hnum : 1000000 < 99*71^3 := by decide +kernel
    omega
  interval_cases e
  · exact case416
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case418 : Closed 1000000 99 16093 67 := by
  apply closed_split (a:=71) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 99 (Nat.pow_le_pow_right (by decide : 0<67) h)
    have hnum : 1000000 < 99*67^3 := by decide +kernel
    omega
  interval_cases e
  · exact case417
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case419 : Closed 1000000 99 16093 61 := by
  apply closed_split (a:=67) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 99 (Nat.pow_le_pow_right (by decide : 0<61) h)
    have hnum : 1000000 < 99*61^3 := by decide +kernel
    omega
  interval_cases e
  · exact case418
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
