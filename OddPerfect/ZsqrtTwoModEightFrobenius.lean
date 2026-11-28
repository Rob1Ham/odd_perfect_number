module

public import OddPerfect.ZsqrtTwoFermatDescent
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# 2-Adic & Mod-`(8 * d)` Frobenius Laws in `ℤ√2` (`OddPerfect.ZsqrtTwoModEightFrobenius`)

Extends the `ℤ√2` Frobenius descent of `OddPerfect.ZsqrtTwoFermatDescent` with 2-adic
eighth-power triviality and exact coordinate divisibility/coprimality on `q ^ d + 1 = 2 * y ^ 2`:

1. `zsqrtTwo_pow_eight_modEq_one_of_norm_modEq_one` and `zsqrtTwo_pow_eight_modEq_one`:
   proves `(α ^ 8).re ≡ 1 [ZMOD 8] ∧ (α ^ 8).im ≡ 0 [ZMOD 8]` whenever
   `α.norm ≡ 1 [ZMOD 16] ∨ α.norm ≡ -1 [ZMOD 16]`, and the sharper mod-`16` identity
   `Even α.im ∧ (α ^ 8).re ≡ 1 [ZMOD 16] ∧ (α ^ 8).im ≡ 0 [ZMOD 16]` when
   `α.norm ≡ 1 [ZMOD 16]`.
2. `zsqrtTwo_pow_modEq_self_mod_eight_mul_prime` and
   `zsqrtTwo_pow_modEq_self_mod_sixteen_mul_prime`: combines the 2-adic eighth-power law
   with `zsqrtTwo_pow_modEq_self_of_prime_mod_eight_eq_one` to obtain
   `α ^ d ≡ α [ZMOD 8 * d]` (and `α ^ d ≡ α [ZMOD 16 * d]` when `α.norm ≡ 1 [ZMOD 16]`).
3. `zsqrtTwo_fermat_coordinate_divisibility_and_mod_eight_d` and
   `exceptional_euler_zsqrtTwo_mod_eight_d_profile`: establishes exact coordinate divisibility
   `α.re ∣ (α ^ d).re`, `α.im ∣ (α ^ d).im`, `IsCoprime α.re α.im`, and mod-`(8 * d)` / mod-`16`
   pinning on the exceptional Euler-index branch.
-/

public section

namespace OddPerfect

open ArithmeticFunction

/-! ## 1. 2-Adic Eighth-Power Triviality in `ℤ√2` -/

private lemma zsqrtTwo_mul_modEq {m : ℤ} {x x' y y' : ℤ√2}
    (hx : x.re ≡ x'.re [ZMOD m] ∧ x.im ≡ x'.im [ZMOD m])
    (hy : y.re ≡ y'.re [ZMOD m] ∧ y.im ≡ y'.im [ZMOD m]) :
    (x * y).re ≡ (x' * y').re [ZMOD m] ∧ (x * y).im ≡ (x' * y').im [ZMOD m] := by
  refine ⟨?_, ?_⟩
  · simp only [Zsqrtd.re_mul]
    exact (hx.1.mul hy.1).add (((Int.ModEq.refl 2).mul hx.2).mul hy.2)
  · simp only [Zsqrtd.im_mul]
    exact (hx.1.mul hy.2).add (hx.2.mul hy.1)

private lemma zsqrtTwo_pow_modEq_one {m : ℤ} {z : ℤ√2}
    (hz : z.re ≡ 1 [ZMOD m] ∧ z.im ≡ 0 [ZMOD m]) (k : ℕ) :
    (z ^ k).re ≡ 1 [ZMOD m] ∧ (z ^ k).im ≡ 0 [ZMOD m] := by
  have hz' : z.re ≡ (1 : ℤ√2).re [ZMOD m] ∧ z.im ≡ (1 : ℤ√2).im [ZMOD m] := hz
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have ih' : (z ^ k).re ≡ (1 : ℤ√2).re [ZMOD m] ∧ (z ^ k).im ≡ (1 : ℤ√2).im [ZMOD m] := ih
    simpa using zsqrtTwo_mul_modEq ih' hz'

private lemma odd_sq_modEq_one_mod_eight {n : ℤ} (hn : n % 2 = 1) : n ^ 2 ≡ 1 [ZMOD 8] := by
  have h8 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
  rcases h8 with h | h | h | h <;>
    · rw [Int.ModEq, sq, Int.mul_emod, h]
      norm_num

private lemma even_sq_emod_eight {n : ℤ} (hn : n % 2 = 0) :
    n ^ 2 % 8 = 0 ∨ n ^ 2 % 8 = 4 := by
  have h4 : n % 4 = 0 ∨ n % 4 = 2 := by omega
  rcases h4 with h | h
  · left
    have h8 : n % 8 = 0 ∨ n % 8 = 4 := by omega
    rcases h8 with h' | h' <;> simp [sq, Int.mul_emod, h']
  · right
    have h8 : n % 8 = 2 ∨ n % 8 = 6 := by omega
    rcases h8 with h' | h' <;> simp [sq, Int.mul_emod, h']

private lemma sq_emod_eight (n : ℤ) : n ^ 2 % 8 = 0 ∨ n ^ 2 % 8 = 1 ∨ n ^ 2 % 8 = 4 := by
  have h8 : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨
      n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by omega
  rcases h8 with h | h | h | h | h | h | h | h <;>
    simp [sq, Int.mul_emod, h]

private lemma zsqrtTwo_sq (a b : ℤ) :
    (⟨a, b⟩ : ℤ√2) ^ 2 = ⟨a ^ 2 + 2 * b ^ 2, 2 * a * b⟩ := by
  ext <;> simp [pow_two] <;> ring

private lemma zsqrtTwo_pow_eight_of_sq_mod_sixteen (a c t : ℤ)
    (ha2 : a ^ 2 = 1 + 8 * c ^ 2 + 16 * t) :
    ((⟨a, c + c⟩ : ℤ√2) ^ 8).re ≡ 1 [ZMOD 16] ∧
    ((⟨a, c + c⟩ : ℤ√2) ^ 8).im ≡ 0 [ZMOD 16] := by
  set u : ℤ := c ^ 2 + t
  set v : ℤ := a * c
  have h2 : (⟨a, c + c⟩ : ℤ√2) ^ 2 = ⟨1 + 16 * u, 4 * v⟩ := by
    rw [zsqrtTwo_sq]
    ext
    · change a ^ 2 + 2 * (c + c) ^ 2 = 1 + 16 * (c ^ 2 + t)
      rw [ha2]
      ring
    · change 2 * a * (c + c) = 4 * (a * c)
      ring
  set x : ℤ := 2 * u + 16 * u ^ 2 + 2 * v ^ 2
  set y : ℤ := 8 * u * v
  have h4 : (⟨a, c + c⟩ : ℤ√2) ^ 4 = ⟨1 + 16 * x, 8 * v + 16 * y⟩ := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, h2, zsqrtTwo_sq]
    ext
    · change (1 + 16 * u) ^ 2 + 2 * (4 * v) ^ 2 = 1 + 16 * x
      dsimp [x]
      ring
    · change 2 * (1 + 16 * u) * (4 * v) = 8 * v + 16 * y
      dsimp [y]
      ring
  have h8 : (⟨a, c + c⟩ : ℤ√2) ^ 8 =
      ⟨1 + 16 * (2 * x + 16 * x ^ 2 + 8 * v ^ 2 + 32 * v * y + 32 * y ^ 2),
        16 * ((1 + 16 * x) * (v + 2 * y))⟩ := by
    rw [show (8 : ℕ) = 4 * 2 by rfl, pow_mul, h4, zsqrtTwo_sq]
    ext
    · change (1 + 16 * x) ^ 2 + 2 * (8 * v + 16 * y) ^ 2 = _
      ring
    · change 2 * (1 + 16 * x) * (8 * v + 16 * y) = _
      ring
  refine ⟨?_, ?_⟩
  · rw [h8, Int.modEq_iff_dvd]
    exact ⟨-(2 * x + 16 * x ^ 2 + 8 * v ^ 2 + 32 * v * y + 32 * y ^ 2), by ring⟩
  · rw [h8, Int.modEq_zero_iff_dvd]
    exact ⟨(1 + 16 * x) * (v + 2 * y), rfl⟩

/-- If `α : ℤ√2` satisfies `α.norm ≡ 1 [ZMOD 16]`, then `α.im` is even and
`α ^ 8 ≡ 1 [ZMOD 16]` coordinatewise. -/
theorem zsqrtTwo_pow_eight_modEq_one_of_norm_modEq_one {α : ℤ√2}
    (hnorm : α.norm ≡ 1 [ZMOD 16]) :
    Even α.im ∧ (α ^ 8).re ≡ 1 [ZMOD 16] ∧ (α ^ 8).im ≡ 0 [ZMOD 16] := by
  rcases α with ⟨a, b⟩
  have hnorm_eq : (⟨a, b⟩ : ℤ√2).norm = a ^ 2 - 2 * b ^ 2 := by
    simp [Zsqrtd.norm_def]
    ring
  have hnorm' : a ^ 2 - 2 * b ^ 2 ≡ 1 [ZMOD 16] := by rwa [← hnorm_eq]
  have hb_even : Even b := by
    have h8 : (a ^ 2 - 2 * b ^ 2) % 8 = 1 := by
      have := Int.ModEq.of_dvd (by decide : (8 : ℤ) ∣ 16) hnorm'
      simpa [Int.ModEq] using this
    by_contra hb_odd
    have hb_mod : b % 2 = 1 := Int.odd_iff.mp (Int.not_even_iff_odd.mp hb_odd)
    have hb_sq : b ^ 2 % 8 = 1 := odd_sq_modEq_one_mod_eight hb_mod
    have ha_sq := sq_emod_eight a
    omega
  obtain ⟨c, rfl⟩ := hb_even
  obtain ⟨t, ht⟩ := Int.modEq_iff_add_fac.mp hnorm'.symm
  have ha2 : a ^ 2 = 1 + 8 * c ^ 2 + 16 * t := by linarith
  exact ⟨⟨c, rfl⟩, zsqrtTwo_pow_eight_of_sq_mod_sixteen a c t ha2⟩

/-- If `α : ℤ√2` satisfies `α.norm ≡ -1 [ZMOD 8]`, then `α ^ 8 ≡ 1 [ZMOD 8]` coordinatewise. -/
theorem zsqrtTwo_pow_eight_modEq_one_of_norm_modEq_neg_one {α : ℤ√2}
    (hnorm : α.norm ≡ -1 [ZMOD 8]) :
    (α ^ 8).re ≡ 1 [ZMOD 8] ∧ (α ^ 8).im ≡ 0 [ZMOD 8] := by
  rcases α with ⟨a, b⟩
  have hnorm_eq : (⟨a, b⟩ : ℤ√2).norm = a ^ 2 - 2 * b ^ 2 := by
    simp [Zsqrtd.norm_def]
    ring
  have hnorm' : (a ^ 2 - 2 * b ^ 2) % 8 = 7 := by
    have : (a ^ 2 - 2 * b ^ 2) % 8 = (-1 : ℤ) % 8 := by
      rw [← hnorm_eq]
      exact hnorm
    omega
  have ha_sq := sq_emod_eight a
  have hb_mod : b % 2 = 1 := by
    by_contra hb_even
    have hbe : b % 2 = 0 := by omega
    have hb4 := even_sq_emod_eight hbe
    rcases ha_sq with ha0 | ha1 | ha4 <;> rcases hb4 with hb0 | hb4 <;> omega
  have ha_mod : a % 2 = 1 := by
    have hbs1 : b ^ 2 % 8 = 1 := odd_sq_modEq_one_mod_eight hb_mod
    by_contra ha_even
    have hae : a % 2 = 0 := by omega
    have ha4 := even_sq_emod_eight hae
    rcases ha4 with ha0 | ha4 <;> omega
  obtain ⟨s, hs⟩ := Int.modEq_iff_add_fac.mp (odd_sq_modEq_one_mod_eight ha_mod).symm
  obtain ⟨t, ht⟩ := Int.modEq_iff_add_fac.mp (odd_sq_modEq_one_mod_eight hb_mod).symm
  have hab_mod : a * b % 2 = 1 := by
    rw [Int.mul_emod, ha_mod, hb_mod]
    norm_num
  obtain ⟨w, hw⟩ : ∃ w : ℤ, a * b = 1 + 2 * w := by
    refine ⟨(a * b - 1) / 2, ?_⟩
    omega
  set u : ℤ := s + 2 * t
  have h2 : (⟨a, b⟩ : ℤ√2) ^ 2 = ⟨3 + 8 * u, 2 + 4 * w⟩ := by
    rw [zsqrtTwo_sq]
    ext
    · change a ^ 2 + 2 * b ^ 2 = 3 + 8 * (s + 2 * t)
      rw [hs, ht]
      ring
    · change 2 * a * b = 2 + 4 * w
      rw [mul_assoc, hw]
      ring
  set p : ℤ := 2 + 6 * u + 8 * u ^ 2 + 4 * w + 4 * w ^ 2
  set q' : ℤ := 1 + 3 * w + 4 * u + 8 * u * w
  have h4 : (⟨a, b⟩ : ℤ√2) ^ 4 = ⟨1 + 8 * p, 4 + 8 * q'⟩ := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, h2, zsqrtTwo_sq]
    ext
    · change (3 + 8 * u) ^ 2 + 2 * (2 + 4 * w) ^ 2 = 1 + 8 * p
      dsimp [p]
      ring
    · change 2 * (3 + 8 * u) * (2 + 4 * w) = 4 + 8 * q'
      dsimp [q']
      ring
  have h8 : (⟨a, b⟩ : ℤ√2) ^ 8 =
      ⟨1 + 8 * (2 * p + 8 * p ^ 2 + 4 + 16 * q' + 16 * q' ^ 2),
        8 * ((1 + 8 * p) * (1 + 2 * q'))⟩ := by
    rw [show (8 : ℕ) = 4 * 2 by rfl, pow_mul, h4, zsqrtTwo_sq]
    ext
    · change (1 + 8 * p) ^ 2 + 2 * (4 + 8 * q') ^ 2 = _
      ring
    · change 2 * (1 + 8 * p) * (4 + 8 * q') = _
      ring
  refine ⟨?_, ?_⟩
  · rw [h8, Int.modEq_iff_dvd]
    exact ⟨-(2 * p + 8 * p ^ 2 + 4 + 16 * q' + 16 * q' ^ 2), by ring⟩
  · rw [h8, Int.modEq_zero_iff_dvd]
    exact ⟨(1 + 8 * p) * (1 + 2 * q'), rfl⟩

/-- If `α : ℤ√2` satisfies `α.norm ≡ ±1 [ZMOD 16]`, then `α ^ 8 ≡ 1 [ZMOD 8]` coordinatewise. -/
theorem zsqrtTwo_pow_eight_modEq_one {α : ℤ√2}
    (hnorm : α.norm ≡ 1 [ZMOD 16] ∨ α.norm ≡ -1 [ZMOD 16]) :
    (α ^ 8).re ≡ 1 [ZMOD 8] ∧ (α ^ 8).im ≡ 0 [ZMOD 8] := by
  rcases hnorm with h1 | hm1
  · obtain ⟨_, hre, him⟩ := zsqrtTwo_pow_eight_modEq_one_of_norm_modEq_one h1
    exact ⟨hre.of_dvd (by decide : (8 : ℤ) ∣ 16), him.of_dvd (by decide : (8 : ℤ) ∣ 16)⟩
  · exact zsqrtTwo_pow_eight_modEq_one_of_norm_modEq_neg_one
      (hm1.of_dvd (by decide : (8 : ℤ) ∣ 16))

/-! ## 2. Combined Mod-`(8 * d)` & Mod-`(16 * d)` Frobenius Laws -/

private lemma zsqrtTwo_pow_modEq_self_of_pow_eight {m : ℤ} {d : ℕ} (hd8 : d % 8 = 1)
    {α : ℤ√2} (h8 : (α ^ 8).re ≡ 1 [ZMOD m] ∧ (α ^ 8).im ≡ 0 [ZMOD m]) :
    (α ^ d).re ≡ α.re [ZMOD m] ∧ (α ^ d).im ≡ α.im [ZMOD m] := by
  have hd_eq : d = 8 * (d / 8) + 1 := by omega
  have hpow : ((α ^ 8) ^ (d / 8)).re ≡ (1 : ℤ√2).re [ZMOD m] ∧
      ((α ^ 8) ^ (d / 8)).im ≡ (1 : ℤ√2).im [ZMOD m] :=
    zsqrtTwo_pow_modEq_one h8 (d / 8)
  have hmul := zsqrtTwo_mul_modEq (y := α) (y' := α) hpow ⟨Int.ModEq.rfl, Int.ModEq.rfl⟩
  have h1mul : (1 : ℤ√2) * α = α := one_mul α
  have heq : (α ^ 8) ^ (d / 8) * α = α ^ d := by
    rw [← pow_mul, ← pow_succ, ← hd_eq]
  rw [heq] at hmul
  simpa [h1mul] using hmul

/-- For `d % 8 = 1` and `α.norm ≡ ±1 [ZMOD 16]`, `α ^ d ≡ α [ZMOD 8]` coordinatewise. -/
theorem zsqrtTwo_pow_modEq_self_mod_eight {d : ℕ} (hd8 : d % 8 = 1) {α : ℤ√2}
    (hnorm : α.norm ≡ 1 [ZMOD 16] ∨ α.norm ≡ -1 [ZMOD 16]) :
    (α ^ d).re ≡ α.re [ZMOD 8] ∧ (α ^ d).im ≡ α.im [ZMOD 8] :=
  zsqrtTwo_pow_modEq_self_of_pow_eight hd8 (zsqrtTwo_pow_eight_modEq_one hnorm)

/-- For `d % 8 = 1` and `α.norm ≡ 1 [ZMOD 16]`, `α ^ d ≡ α [ZMOD 16]` coordinatewise. -/
theorem zsqrtTwo_pow_modEq_self_mod_sixteen {d : ℕ} (hd8 : d % 8 = 1) {α : ℤ√2}
    (hnorm : α.norm ≡ 1 [ZMOD 16]) :
    (α ^ d).re ≡ α.re [ZMOD 16] ∧ (α ^ d).im ≡ α.im [ZMOD 16] :=
  zsqrtTwo_pow_modEq_self_of_pow_eight hd8 (zsqrtTwo_pow_eight_modEq_one_of_norm_modEq_one hnorm).2

private lemma nat_coprime_eight_of_mod_eight {d : ℕ} (hd8 : d % 8 = 1) : Nat.Coprime 8 d := by
  have hd_odd : Nat.Coprime 2 d := Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega))
  simpa [show (8 : ℕ) = 2 ^ 3 by norm_num] using hd_odd.pow_left 3

private lemma nat_coprime_sixteen_of_mod_eight {d : ℕ} (hd8 : d % 8 = 1) : Nat.Coprime 16 d := by
  have hd_odd : Nat.Coprime 2 d := Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega))
  simpa [show (16 : ℕ) = 2 ^ 4 by norm_num] using hd_odd.pow_left 4

/-- Combined mod-`(8 * d)` Frobenius law in `ℤ√2` for primes `d ≡ 1 [MOD 8]` when
`α.norm ≡ ±1 [ZMOD 16]`. -/
theorem zsqrtTwo_pow_modEq_self_mod_eight_mul_prime {d : ℕ}
    (hd_prime : d.Prime) (hd8 : d % 8 = 1) {α : ℤ√2}
    (hnorm : α.norm ≡ 1 [ZMOD 16] ∨ α.norm ≡ -1 [ZMOD 16]) :
    (α ^ d).re ≡ α.re [ZMOD 8 * (d : ℤ)] ∧ (α ^ d).im ≡ α.im [ZMOD 8 * (d : ℤ)] := by
  obtain ⟨h8_re, h8_im⟩ := zsqrtTwo_pow_modEq_self_mod_eight hd8 hnorm
  obtain ⟨hd_re, hd_im⟩ := zsqrtTwo_pow_modEq_self_of_prime_mod_eight_eq_one hd_prime hd8 α
  have hcop : ((8 : ℤ).natAbs).Coprime ((d : ℤ).natAbs) := by
    simpa using nat_coprime_eight_of_mod_eight hd8
  exact ⟨(Int.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h8_re, hd_re⟩,
    (Int.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h8_im, hd_im⟩⟩

/-- Combined mod-`(16 * d)` Frobenius law in `ℤ√2` for primes `d ≡ 1 [MOD 8]` when
`α.norm ≡ 1 [ZMOD 16]`. -/
theorem zsqrtTwo_pow_modEq_self_mod_sixteen_mul_prime {d : ℕ}
    (hd_prime : d.Prime) (hd8 : d % 8 = 1) {α : ℤ√2}
    (hnorm : α.norm ≡ 1 [ZMOD 16]) :
    Even α.im ∧
      (α ^ d).re ≡ α.re [ZMOD 16 * (d : ℤ)] ∧ (α ^ d).im ≡ α.im [ZMOD 16 * (d : ℤ)] := by
  have hev := (zsqrtTwo_pow_eight_modEq_one_of_norm_modEq_one hnorm).1
  obtain ⟨h16_re, h16_im⟩ := zsqrtTwo_pow_modEq_self_mod_sixteen hd8 hnorm
  obtain ⟨hd_re, hd_im⟩ := zsqrtTwo_pow_modEq_self_of_prime_mod_eight_eq_one hd_prime hd8 α
  have hcop : ((16 : ℤ).natAbs).Coprime ((d : ℤ).natAbs) := by
    simpa using nat_coprime_sixteen_of_mod_eight hd8
  exact ⟨hev,
    (Int.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h16_re, hd_re⟩,
    (Int.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h16_im, hd_im⟩⟩

/-! ## 3. Exact Coordinate Divisibility, Coprimality, & Mod-`(8 * d)` Pinning -/

/-- For odd `d`, `α.re ∣ (α ^ d).re` and `α.im ∣ (α ^ d).im` for every `α : ℤ√2`. -/
theorem zsqrtTwo_coord_dvd_pow_of_odd {d : ℕ} (hd_odd : Odd d) (α : ℤ√2) :
    α.re ∣ (α ^ d).re ∧ α.im ∣ (α ^ d).im := by
  obtain ⟨j, rfl⟩ := hd_odd
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, pow_add]
    refine ⟨?_, ?_⟩
    · rw [Zsqrtd.re_mul, pow_two, Zsqrtd.re_mul, Zsqrtd.im_mul]
      refine dvd_add (dvd_mul_of_dvd_left ih.1 _) ?_
      have ha : α.re ∣ α.re * α.im + α.im * α.re := ⟨2 * α.im, by ring⟩
      exact dvd_mul_of_dvd_right ha _
    · rw [Zsqrtd.im_mul, pow_two, Zsqrtd.re_mul, Zsqrtd.im_mul]
      refine dvd_add ?_ (dvd_mul_of_dvd_left ih.2 _)
      have hb : α.im ∣ α.re * α.im + α.im * α.re := ⟨2 * α.re, by ring⟩
      exact dvd_mul_of_dvd_right hb _

/-- Exact coordinate representation, divisibility, and Bezout coprimality for any solution
`1 + y√2 = silverUnit ^ k * α ^ d` with `d` odd. -/
theorem zsqrtTwo_fermat_coordinate_divisibility {d y : ℕ} (hd_odd : Odd d)
    (k : ℤ) (α : ℤ√2)
    (hz : (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d) :
    let u_k : ℤ√2 := ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2)
    α ^ d = ⟨u_k.re + 2 * u_k.im * (y : ℤ), u_k.re * (y : ℤ) + u_k.im⟩ ∧
    α.re ∣ u_k.re + 2 * u_k.im * (y : ℤ) ∧
    α.im ∣ u_k.re * (y : ℤ) + u_k.im ∧
    IsCoprime (α ^ d).re (α ^ d).im ∧
    IsCoprime α.re α.im := by
  intro u_k
  have hpow : α ^ d = u_k * ⟨1, (y : ℤ)⟩ := by
    calc
      α ^ d = ((silverUnit ^ (-k) * silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d := by simp
      _ = u_k * (((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d) := by
        rw [Units.val_mul, mul_assoc]
      _ = u_k * ⟨1, (y : ℤ)⟩ := by rw [← hz]
  have hcoord : α ^ d = ⟨u_k.re + 2 * u_k.im * (y : ℤ), u_k.re * (y : ℤ) + u_k.im⟩ := by
    rw [hpow]
    ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]
  obtain ⟨hdvd_re, hdvd_im⟩ := zsqrtTwo_coord_dvd_pow_of_odd hd_odd α
  have hdvd_re' : α.re ∣ u_k.re + 2 * u_k.im * (y : ℤ) := by
    simpa [hcoord] using hdvd_re
  have hdvd_im' : α.im ∣ u_k.re * (y : ℤ) + u_k.im := by
    simpa [hcoord] using hdvd_im
  have hun : IsUnit u_k.norm :=
    (Zsqrtd.isUnit_iff_norm_isUnit u_k).mp (silverUnit ^ (-k) : (ℤ√2)ˣ).isUnit
  have hcop_pow : IsCoprime (α ^ d).re (α ^ d).im := by
    have hbez : u_k.re * (α ^ d).re - 2 * u_k.im * (α ^ d).im = u_k.norm := by
      rw [hcoord]
      simp [Zsqrtd.norm_def]
      ring
    rcases Int.isUnit_iff.mp hun with h1 | hm1
    · refine ⟨u_k.re, -(2 * u_k.im), ?_⟩
      linarith
    · refine ⟨-u_k.re, 2 * u_k.im, ?_⟩
      linarith
  have hcop_α : IsCoprime α.re α.im :=
    (hcop_pow.of_isCoprime_of_dvd_left hdvd_re).of_isCoprime_of_dvd_right hdvd_im
  exact ⟨hcoord, hdvd_re', hdvd_im', hcop_pow, hcop_α⟩

/-- Coordinate divisibility, coprimality, and mod-`(8 * d)` pinning for `1 + y√2 = silverUnit ^ k * α ^ d`
when `d` is prime with `d % 8 = 1` and `α.norm ≡ ±1 [ZMOD 16]`. -/
theorem zsqrtTwo_fermat_coordinate_divisibility_and_mod_eight_d {d y : ℕ}
    (hd_prime : d.Prime) (hd8 : d % 8 = 1) (k : ℤ) (α : ℤ√2)
    (hnorm : α.norm ≡ 1 [ZMOD 16] ∨ α.norm ≡ -1 [ZMOD 16])
    (hz : (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d) :
    let u_k : ℤ√2 := ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2)
    α ^ d = ⟨u_k.re + 2 * u_k.im * (y : ℤ), u_k.re * (y : ℤ) + u_k.im⟩ ∧
    α.re ∣ u_k.re + 2 * u_k.im * (y : ℤ) ∧
    α.im ∣ u_k.re * (y : ℤ) + u_k.im ∧
    IsCoprime (α ^ d).re (α ^ d).im ∧
    IsCoprime α.re α.im ∧
    α.re ≡ u_k.re + 2 * u_k.im * (y : ℤ) [ZMOD 8 * (d : ℤ)] ∧
    α.im ≡ u_k.re * (y : ℤ) + u_k.im [ZMOD 8 * (d : ℤ)] ∧
    α.re ≡ u_k.re + 2 * u_k.im * (y : ℤ) [ZMOD 8] ∧
    α.im ≡ u_k.re * (y : ℤ) + u_k.im [ZMOD 8] := by
  intro u_k
  have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
  obtain ⟨hcoord, hdvd_re, hdvd_im, hcop_pow, hcop_α⟩ :=
    zsqrtTwo_fermat_coordinate_divisibility hd_odd k α hz
  obtain ⟨hfrob_re, hfrob_im⟩ :=
    zsqrtTwo_pow_modEq_self_mod_eight_mul_prime hd_prime hd8 hnorm
  have hmod_re : α.re ≡ u_k.re + 2 * u_k.im * (y : ℤ) [ZMOD 8 * (d : ℤ)] := by
    have h := hfrob_re.symm
    rw [hcoord] at h
    exact h
  have hmod_im : α.im ≡ u_k.re * (y : ℤ) + u_k.im [ZMOD 8 * (d : ℤ)] := by
    have h := hfrob_im.symm
    rw [hcoord] at h
    exact h
  refine ⟨hcoord, hdvd_re, hdvd_im, hcop_pow, hcop_α, hmod_re, hmod_im,
    hmod_re.of_mul_right (d : ℤ), hmod_im.of_mul_right (d : ℤ)⟩

/-- Exceptional Euler-index `ℤ√2` mod-`(8 * d)` and mod-`16` Frobenius profile on
`sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`). -/
theorem exceptional_euler_zsqrtTwo_mod_eight_d_profile {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    ∃ (y : ℕ) (k : ℤ) (α : ℤ√2),
      let u_k : ℤ√2 := ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2)
      0 < y ∧ d ∣ y ∧ q ^ d + 1 = 2 * y ^ 2 ∧
      1 ≤ |k| ∧ 2 * |k| ≤ (d : ℤ) - 1 ∧
      (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d ∧
      α.norm = (if Even k then -(q : ℤ) else (q : ℤ)) ∧
      IsCoprime α.re α.im ∧
      α.re ∣ u_k.re + 2 * u_k.im * (y : ℤ) ∧
      α.im ∣ u_k.re * (y : ℤ) + u_k.im ∧
      α.re ≡ u_k.re [ZMOD (d : ℤ)] ∧
      α.im ≡ u_k.im [ZMOD (d : ℤ)] ∧
      α.re ≡ u_k.re + 2 * u_k.im * (y : ℤ) [ZMOD 8] ∧
      α.im ≡ u_k.re * (y : ℤ) + u_k.im [ZMOD 8] ∧
      (Odd k → Even α.im ∧ α.re ≡ u_k.re + 2 * u_k.im * (y : ℤ) [ZMOD 16]) := by
  intro d
  obtain ⟨hd, _, hd8, hq16, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, hre_d, him_d⟩ :=
    exceptional_euler_zsqrtTwo_frobenius_descent hN ho hq hq4 ha4 ha hqm hform hl hi
  change d.Prime at hd
  change d % 8 = 1 at hd8
  have hq_mod : (q : ℤ) ≡ 1 [ZMOD 16] := by
    rw [Int.ModEq]
    exact_mod_cast hq16
  have hnorm_mod : α.norm ≡ 1 [ZMOD 16] ∨ α.norm ≡ -1 [ZMOD 16] := by
    rw [hnorm]
    split_ifs
    · exact Or.inr hq_mod.neg
    · exact Or.inl hq_mod
  obtain ⟨hcoord, hdvd_re, hdvd_im, _, hcop_α, _, _, hre8, him8⟩ :=
    zsqrtTwo_fermat_coordinate_divisibility_and_mod_eight_d hd hd8 k α hnorm_mod hz_eq
  refine ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, hcop_α,
    hdvd_re, hdvd_im, hre_d, him_d, hre8, him8, ?_⟩
  intro hk_odd
  have hnot_even : ¬ Even k := Int.not_even_iff_odd.mpr hk_odd
  have hnorm1 : α.norm ≡ 1 [ZMOD 16] := by
    rw [hnorm, ite_eq_right_iff.mpr (fun h => absurd h hnot_even)]
    exact hq_mod
  obtain ⟨hev_im, h16_re, _⟩ :=
    zsqrtTwo_pow_modEq_self_mod_sixteen_mul_prime hd hd8 hnorm1
  refine ⟨hev_im, ?_⟩
  have hre16 : α.re ≡ (α ^ d).re [ZMOD 16] := (h16_re.of_mul_right (d : ℤ)).symm
  rw [hcoord] at hre16
  exact hre16

end OddPerfect
