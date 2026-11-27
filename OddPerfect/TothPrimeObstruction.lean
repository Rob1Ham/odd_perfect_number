module

public import OddPerfect.DeficientPerfect
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect
open ArithmeticFunction

/-- In a coprime splitting of a Tóth cofactor the two divisor sums multiply to the
multiplier times the deficient divisor. -/
theorem TothPair.sigma_split_eq {n x a b : ℕ} (h : TothPair n x)
    (hx : Odd x) (h1 : 1 < x) (hn : n = a * b) (hab : a.Coprime b) :
    sigma 1 a * sigma 1 b = x * (sigma 1 n / x) := by
  obtain ⟨d, t, hd, hnt, hxt⟩ := h.deficientDivisor hx h1
  have hsig : sigma 1 n = x * d := by
    have hsum := hd.2
    nlinarith [congrArg (d * ·) hxt]
  calc
    sigma 1 a * sigma 1 b = sigma 1 n := by
      rw [hn, isMultiplicative_sigma.map_mul_of_coprime hab]
    _ = x * (sigma 1 n / x) := by rw [hsig, Nat.mul_div_cancel_left _ h.2.1]

/-- A coprime split for which neither divisor sum fits in the deficient divisor supplies
the explicit proper factor gcd(x, σ(a)) of the multiplier. The blocks may have any rank. -/
theorem TothPair.proper_factor_of_sigma_split {n x a b : ℕ} (h : TothPair n x)
    (hx : Odd x) (h1 : 1 < x) (hn : n = a * b) (hab : a.Coprime b)
    (ha : ¬ sigma 1 a ∣ sigma 1 n / x) (hb : ¬ sigma 1 b ∣ sigma 1 n / x) :
    1 < x.gcd (sigma 1 a) ∧ x.gcd (sigma 1 a) < x ∧ x.gcd (sigma 1 a) ∣ x := by
  have hsplit := h.sigma_split_eq hx h1 hn hab
  have hleft : sigma 1 a ∣ x * (sigma 1 n / x) := hsplit ▸ dvd_mul_right _ _
  have hne_one : x.gcd (sigma 1 a) ≠ 1 := by
    intro hg
    have hc : (sigma 1 a).Coprime x := (show x.Coprime (sigma 1 a) from hg).symm
    exact ha (hc.dvd_of_dvd_mul_left hleft)
  have hdiv := Nat.gcd_dvd_left x (sigma 1 a)
  have hle := Nat.le_of_dvd h.2.1 hdiv
  have hne_x : x.gcd (sigma 1 a) ≠ x := by
    intro hg
    have hxa := Nat.gcd_dvd_right x (sigma 1 a)
    rw [hg] at hxa
    obtain ⟨k, hk⟩ := hxa
    rw [hk, Nat.mul_assoc] at hsplit
    have he := Nat.eq_of_mul_eq_mul_left h.2.1 hsplit
    exact hb ⟨k, by simpa [Nat.mul_comm] using he.symm⟩
  have hpos := Nat.gcd_pos_of_pos_left (sigma 1 a) h.2.1
  exact ⟨by omega, by omega, hdiv⟩

/-- In the linear Euler branch every coprime factorization of the square cofactor has
at least one block whose complete divisor sum divides the Euler component index. -/
theorem linear_euler_sigma_split {N q m a b : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hm : m ^ 2 = a * b) (hab : a.Coprime b) :
    sigma 1 a ∣ sigma 1 (m ^ 2) / q ∨ sigma 1 b ∣ sigma 1 (m ^ 2) / q := by
  have hqodd := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2) : q ∣ N)
  have hmodd := ho.of_dvd_nat (hform ▸ dvd_mul_left (m ^ 2) q : m ^ 2 ∣ N)
  have hc : (m ^ 2).Coprime q :=
    (hq.coprime_iff_not_dvd.mpr (fun h => hqm (hq.dvd_of_dvd_pow h))).symm
  have hp : (m ^ 2 * q).Perfect := by rwa [mul_comm, ← hform]
  have hpair := tothPair_of_linear_euler hmodd hq hc hp
  by_contra! h
  obtain ⟨hlo, hhi, hd⟩ := hpair.proper_factor_of_sigma_split hqodd hq.one_lt hm hab h.1 h.2
  rcases hq.eq_one_or_self_of_dvd _ hd with he | he <;> omega

end OddPerfect
