module

public import OddPerfect.BrentSeeds
public import OddPerfect.SizeIndex300

public section

namespace OddPerfect

/-- A prime-index certificate for the 1991 bound of Brent, Cohen and te Riele. -/
theorem ten_pow_three_hundred_lt_of_odd_perfect {N : ℕ} (ho : Odd N) (hN : N.Perfect) : 10^300 < N := by
  by_contra! hx
  have avoid1 : Nat.Coprime 1 N := Nat.coprime_one_left N
  by_cases h127 : 127 ∣ N
  · exact IndexComponent.Size300.exclude_127 ho hN h127 avoid1 hx
  have avoid127 : Nat.Coprime 127 N := avoid1.mul_left ((by decide : Nat.Prime 127).coprime_iff_not_dvd.mpr h127)
  by_cases h19 : 19 ∣ N
  · exact IndexComponent.Size300.exclude_19 ho hN h19 avoid127 hx
  have avoid2413 : Nat.Coprime 2413 N := avoid127.mul_left ((by decide : Nat.Prime 19).coprime_iff_not_dvd.mpr h19)
  by_cases h7 : 7 ∣ N
  · exact IndexComponent.Size300.exclude_7 ho hN h7 avoid2413 hx
  have avoid16891 : Nat.Coprime 16891 N := avoid2413.mul_left ((by decide : Nat.Prime 7).coprime_iff_not_dvd.mpr h7)
  by_cases h11 : 11 ∣ N
  · exact IndexComponent.Size300.exclude_11 ho hN h11 avoid16891 hx
  have avoid185801 : Nat.Coprime 185801 N := avoid16891.mul_left ((by decide : Nat.Prime 11).coprime_iff_not_dvd.mpr h11)
  by_cases h31 : 31 ∣ N
  · exact IndexComponent.Size300.exclude_31 ho hN h31 avoid185801 hx
  have avoid5759831 : Nat.Coprime 5759831 N := avoid185801.mul_left ((by decide : Nat.Prime 31).coprime_iff_not_dvd.mpr h31)
  by_cases h13 : 13 ∣ N
  · exact IndexComponent.Size300.exclude_13 ho hN h13 avoid5759831 hx
  have avoid74877803 : Nat.Coprime 74877803 N := avoid5759831.mul_left ((by decide : Nat.Prime 13).coprime_iff_not_dvd.mpr h13)
  by_cases h3 : 3 ∣ N
  · exact IndexComponent.Size300.exclude_3 ho hN h3 avoid74877803 hx
  have avoid224633409 : Nat.Coprime 224633409 N := avoid74877803.mul_left ((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr h3)
  by_cases h5 : 5 ∣ N
  · exact IndexComponent.Size300.exclude_5 ho hN h5 avoid224633409 hx
  have avoidAll : Nat.Coprime 1123167045 N := avoid224633409.mul_left
    ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr h5)
  exact (by decide +kernel : ¬ (10:ℕ)^536 < 10^300) ((brent_seed_free_size ho hN avoidAll).trans_le hx)

end OddPerfect
