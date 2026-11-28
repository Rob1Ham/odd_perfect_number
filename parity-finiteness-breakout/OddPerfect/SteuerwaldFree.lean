module

public import OddPerfect.Thirteen
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Steuerwald's contradiction when 3 is absent and all non-special exponents are two. -/

public section

namespace OddPerfect

/-- A prime divisor of the third cyclotomic polynomial at a natural number is 3
or is congruent to one modulo 3. -/
theorem prime_dvd_sq_add_self_add_one {q r : ℕ} (hr : r.Prime)
    (hd : r ∣ q ^ 2 + q + 1) : r = 3 ∨ r % 3 = 1 := by
  let : Fact r.Prime := ⟨hr⟩
  let x : ZMod r := q
  have hx : x ^ 2 + x + 1 = 0 := by
    simpa [x] using (ZMod.natCast_eq_zero_iff _ _).2 hd
  by_cases h1 : x = 1
  · have hz : (3 : ZMod r) = 0 := by
      calc (3 : ZMod r) = 1 ^ 2 + 1 + 1 := by ring
           _ = 0 := h1 ▸ hx
    have h3 : r ∣ 3 := (ZMod.natCast_eq_zero_iff 3 r).1 hz
    exact Or.inl ((Nat.dvd_prime (by decide : Nat.Prime 3)).1 h3 |>.resolve_left hr.ne_one)
  have h0 : x ≠ 0 := by
    rintro h
    simp [h] at hx
  have hcube : x ^ 3 = 1 := by
    calc x ^ 3 = (x - 1) * (x ^ 2 + x + 1) + 1 := by ring
         _ = 1 := by rw [hx]; ring
  have horder : orderOf x = 3 :=
    ((Nat.dvd_prime (by decide : Nat.Prime 3)).1 (orderOf_dvd_of_pow_eq_one hcube)).resolve_left
      (fun h => h1 (orderOf_eq_one_iff.mp h))
  have hmod := ZMod.orderOf_dvd_card_sub_one h0
  rw [horder] at hmod
  have := hr.two_le
  exact Or.inr (by omega)

/-- A prime of the half-successor of p cannot at the same time have its
third cyclotomic value divisible by p. This is §III of Steuerwald's argument. -/
private theorem not_dvd_sq_add_self_add_one_of_dvd_half_succ {q p : ℕ}
    (hq : q.Prime) (hqodd : Odd q) (hpodd : Odd p) (hqhalf : q ∣ (p + 1) / 2) :
    ¬ p ∣ q ^ 2 + q + 1 := by
  rintro ⟨y, hy⟩
  have hppos := hpodd.pos
  have hpbound := Nat.le_of_dvd (show 0 < (p + 1) / 2 by omega) hqhalf
  have hqp : q ∣ p + 1 := by
    have h := dvd_mul_of_dvd_right hqhalf 2
    rwa [show 2 * ((p + 1) / 2) = p + 1 by have := Nat.odd_iff.mp hpodd; omega] at h
  have hqy : q ∣ y + 1 := by
    apply (Nat.dvd_add_left (Nat.dvd_mul_right q (q + 1))).mp
    rw [show y + 1 + q * (q + 1) = (p + 1) * y by nlinarith [hy]]
    exact dvd_mul_of_dvd_left hqp _
  have hsumodd : Odd (q ^ 2 + q + 1) :=
    ((hqodd.pow.add_odd hqodd).add_odd (by decide : Odd 1))
  have hyodd := hsumodd.of_dvd_nat (hy ▸ Nat.dvd_mul_left y p)
  have h2y : 2 ∣ y + 1 := by have := Nat.odd_iff.mp hyodd; omega
  have h2qy : q * 2 ∣ y + 1 := hqodd.coprime_two_right.mul_dvd_of_dvd_of_dvd hqy h2y
  have hybound := Nat.le_of_dvd (Nat.zero_lt_succ y) h2qy
  have hq2 := hq.two_le
  have hlarge := Nat.mul_le_mul (show q + 1 ≤ p by omega) (show q + 1 ≤ y by omega)
  nlinarith

/-- In a 3-free odd perfect number, the exponents other than the Euler exponent
cannot all equal two. -/
theorem steuerwald_three_free {N p : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hp : p.Prime) (hp4 : p % 4 = 1) (he : N.factorization p % 4 = 1)
    (hsq : ∀ q : ℕ, q.Prime → q ∣ N → q ≠ p → N.factorization q = 2)
    (hfree : ¬ 3 ∣ N) : False := by
  have hn := hN.2.ne'
  have exactPower {r e : ℕ} (hr : r.Prime) (h : N.factorization r = e) :
      r ^ e ∣ N ∧ ¬ r ^ (e + 1) ∣ N := by
    simp [hr.pow_dvd_iff_le_factorization hn, h]
  have squareSum {r : ℕ} (hr : r.Prime) (hrN : r ∣ N) (hrp : r ≠ p) :
      r ^ 2 + r + 1 ∣ N := by
    obtain ⟨hpow, hnext⟩ := exactPower hr (hsq r hr hrN hrp)
    obtain ⟨b, hb, hcop⟩ := exists_coprime_cofactor_of_exact_prime_pow hr hpow hnext
    have hro := hodd.of_dvd_nat hrN
    apply odd_dvd_perfect_of_dvd_sum_divisors hN hb hcop
      ((hro.pow.add_odd hro).add_odd (by decide : Odd 1))
    rw [Nat.sum_divisors_prime_pow (f := fun x => x) hr]
    simp [Finset.sum_range_succ, add_assoc, add_comm, add_left_comm]
  have hplt := hp.two_le
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  have hhalfgt : 1 < (p + 1) / 2 := by omega
  have hhalfodd : Odd ((p + 1) / 2) := Nat.odd_iff.mpr (by omega)
  obtain ⟨q, hq, hqhalf⟩ := Nat.exists_prime_and_dvd hhalfgt.ne'
  have hqodd := hhalfodd.of_dvd_nat hqhalf
  have hqp : q ≠ p := by have := Nat.le_of_dvd (by omega : 0 < (p + 1) / 2) hqhalf; omega
  have hqsucc : q ∣ p + 1 := by
    have h := dvd_mul_of_dvd_right hqhalf 2
    rwa [show 2 * ((p + 1) / 2) = p + 1 by omega] at h
  have hqN : q ∣ N := by
    obtain ⟨hpow, hnext⟩ := exactPower hp rfl
    apply dvd_perfect_of_exact_prime_pow hN hp hpow hnext hq hqodd
    rw [Nat.sum_divisors_prime_pow (f := fun x => x) hp]
    have hblock : q ∣ ∑ i ∈ Finset.range 2, p ^ i := by
      simpa [Finset.sum_range_succ, add_comm] using hqsucc
    rw [dvd_geom_sum_iff_remainder hblock, show (N.factorization p + 1) % 2 = 0 by omega]
    simp
  have hsum := squareSum hq hqN hqp
  have hqpos := hq.pos
  obtain ⟨r, hr, hrq⟩ := Nat.exists_prime_and_dvd
    (show q ^ 2 + q + 1 ≠ 1 by nlinarith)
  have hrN := hrq.trans hsum
  have hrp : r = p := by
    by_contra h
    rcases prime_dvd_sq_add_self_add_one hr hrq with rfl | hr1
    · exact hfree hrN
    · apply hfree
      apply Dvd.dvd.trans _ (squareSum hr hrN h)
      have hc : r ≡ 1 [MOD 3] := hr1
      exact Nat.dvd_of_mod_eq_zero (((hc.pow 2).add hc).add (Nat.ModEq.refl 1))
  exact not_dvd_sq_add_self_add_one_of_dvd_half_succ hq hqodd hpodd hqhalf (hrp ▸ hrq)

end OddPerfect
