module

public import OddPerfect.TothTrillion.Part03
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.Toth

theorem case60 : Closed 1000000 3 13 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 3*19^5 := by decide +kernel
    omega
  interval_cases e
  · exact case58
  · exact case59
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case61 : Closed 1000000 1173 2207023 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 1173 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 1173*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case62 : Closed 1000000 51 3991 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 51 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 51*23^4 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact case61
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case63 : Closed 1000000 969 1520571 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 969 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 969*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case64 : Closed 1000000 969 1520571 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 969 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 969*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case63
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case65 : Closed 1000000 969 1520571 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 969 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 969*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case64
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case66 : Closed 1000000 51 3991 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 51 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 51*19^4 := by decide +kernel
    omega
  interval_cases e
  · exact case62
  · exact case65
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case67 : Closed 1000000 867 1153633 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 867 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 867*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case68 : Closed 1000000 867 1153633 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 867 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 867*19^3 := by decide +kernel
    omega
  interval_cases e
  · exact case67
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case69 : Closed 1000000 3 13 17 := by
  apply closed_split (a:=19) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 5 := by
    by_contra! h
    have := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by decide : 0<17) h)
    have hnum : 1000000 < 3*17^5 := by decide +kernel
    omega
  interval_cases e
  · exact case60
  · exact case66
  · exact case68
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case70 : Closed 1000000 39 2379 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 39 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 39*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_interval (k:=2) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case71 : Closed 1000000 39 2379 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 39 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 39*29^4 := by decide +kernel
    omega
  interval_cases e
  · exact case70
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case72 : Closed 1000000 897 1315587 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 897 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 897*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case73 : Closed 1000000 897 1315587 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 897 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 897*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case72
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case74 : Closed 1000000 39 2379 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 39 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 39*23^4 := by decide +kernel
    omega
  interval_cases e
  · exact case71
  · exact case73
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case75 : Closed 1000000 741 906399 31 := by
  apply closed_split (a:=37) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 741 (Nat.pow_le_pow_right (by decide : 0<31) h)
    have hnum : 1000000 < 741*31^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case76 : Closed 1000000 741 906399 29 := by
  apply closed_split (a:=31) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 741 (Nat.pow_le_pow_right (by decide : 0<29) h)
    have hnum : 1000000 < 741*29^3 := by decide +kernel
    omega
  interval_cases e
  · exact case75
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case77 : Closed 1000000 741 906399 23 := by
  apply closed_split (a:=29) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 741 (Nat.pow_le_pow_right (by decide : 0<23) h)
    have hnum : 1000000 < 741*23^3 := by decide +kernel
    omega
  interval_cases e
  · exact case76
  · exact closed_interval (k:=1) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case78 : Closed 1000000 39 2379 19 := by
  apply closed_split (a:=23) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 4 := by
    by_contra! h
    have := Nat.mul_le_mul_left 39 (Nat.pow_le_pow_right (by decide : 0<19) h)
    have hnum : 1000000 < 39*19^4 := by decide +kernel
    omega
  interval_cases e
  · exact case74
  · exact case77
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

theorem case79 : Closed 1000000 663 730353 37 := by
  apply closed_split (a:=41) (by norm_num) (by decide +kernel)
  intro e he
  have ht : e < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left 663 (Nat.pow_le_pow_right (by decide : 0<37) h)
    have hnum : 1000000 < 663*37^3 := by decide +kernel
    omega
  interval_cases e
  · exact closed_last_prime (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)
  · exact closed_root_only (by decide +kernel) (by decide +kernel)

end OddPerfect.Toth
