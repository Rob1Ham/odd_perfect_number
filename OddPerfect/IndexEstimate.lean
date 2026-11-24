module

public import OddPerfect.EulerIndex
import Mathlib.Tactic.Linarith

public section

namespace OddPerfect

open ArithmeticFunction

private theorem pow_succ_eq_sigma_mul_add_one {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    p ^ (e+1) = sigma 1 (p^e) * (p-1) + 1 := by
  have hg : sigma 1 (p^e) * (p-1) = p ^ (e+1) - 1 := by
    rw [sigma_one_apply_prime_pow hp]
    exact geom_sum_mul_of_one_le (by have := hp.one_lt; omega) _
  have := Nat.pow_pos hp.pos (n := e+1)
  omega

private theorem prime_pow_lt_sigma {p e : ℕ} (hp : Nat.Prime p) (he : 0 < e) :
    p ^ e < sigma 1 (p ^ e) := by
  rw [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]
  have := Finset.sum_pos' (s := Finset.range e) (f := fun j => p ^ j)
    (fun _ _ => Nat.zero_le _) ⟨0, Finset.mem_range.mpr he, by simp⟩
  omega

/-- With just one exceptional outgoing component, multiplication by its base
places a multiple of its `q`-part inside a linear expression. -/
theorem exceptional_part_dvd_linear_bound {r e i U q a M : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hU : U ∣ q^a) (hσr : sigma 1 (r^e) = i*U)
    (hret : sigma 1 (q^a) * i = 2 * (r^e * M)) :
    U ∣ i*r + 2*M*(q-1) := by
  have hgeo := pow_succ_eq_sigma_mul_add_one hq a
  have hgr := pow_succ_eq_sigma_mul_add_one hr e
  have heq : (i*r) * q^(a+1) =
      i*r + 2*M*(q-1) + ((2*M*(q-1)) * (i*(r-1))) * U := by
    calc
      _ = (sigma 1 (q^a) * i) * ((q-1)*r) + i*r := by rw [hgeo]; ring
      _ = (2*M*(q-1)) * r^(e+1) + i*r := by rw [hret, pow_succ]; ring
      _ = _ := by rw [hgr, hσr]; ring
  apply (Nat.dvd_add_iff_left (dvd_mul_left U ((2*M*(q-1)) * (i*(r-1))))).mpr
  rw [← heq]
  exact (hU.trans (pow_dvd_pow q (by omega : a ≤ a+1))).trans (dvd_mul_left _ _)

private theorem growth_at_nine {a : ℕ} (ha : 9 ≤ a) :
    360 * (a + 1)^4 < 7^(a-1) := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ a ha ih =>
    rw [show a + 1 - 1 = (a-1) + 1 by omega, pow_succ 7 (a-1)]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ha
    nlinarith only [ih, Nat.zero_le (k^4), Nat.zero_le (k^3), Nat.zero_le (k^2), Nat.zero_le k]

/-- The remaining square root of a small-index Euler candidate is at most six,
once it divides the Euler length and the exceptional base has been removed. -/
theorem small_index_root_le_six {r e i U q a v : ℕ} (hq : q.Prime) (hq7 : 7 ≤ q)
    (hr : r.Prime) (he : 2 ≤ e) (hi : 0 < i) (hi5 : i ≤ 5) (hv : 0 < v)
    (ha4 : a % 4 = 1) (hvlen : v ∣ a+1) (hU : U ∣ q^a)
    (hσr : sigma 1 (r^e) = i*U) (hret : sigma 1 (q^a) * i = 2 * (r^e * v^2)) :
    v ≤ 6 := by
  let M := v^2
  have hM : 0 < M := Nat.pow_pos hv
  have hqM : 1 ≤ q * M := Nat.mul_pos hq.pos hM
  have hlin := exceptional_part_dvd_linear_bound hq hr hU hσr hret
  change U ∣ i*r + 2*M*(q-1) at hlin
  have hUle := Nat.le_of_dvd (by have := Nat.mul_pos hi hr.pos; omega : 0 < i*r + 2*M*(q-1)) hlin
  have hMle : M * (q-1) ≤ q * M := by
    rw [Nat.mul_comm q]
    exact Nat.mul_le_mul_left _ (Nat.sub_le q 1)
  have hweak : U ≤ 5*r + 2*(q*M) := by
    have := Nat.mul_le_mul_right r hi5
    nlinarith
  have hrpower : r ^ 2 ≤ r ^ e := Nat.pow_le_pow_right hr.pos he
  have hrsig := prime_pow_lt_sigma hr (by omega : 0 < e)
  rw [hσr] at hrsig
  have hr2 : r ^ 2 < 25*r + 10*(q*M) := by
    have := Nat.mul_le_mul_right U hi5
    nlinarith
  have hrle : r ≤ 35 * (q*M) := by
    by_contra! h
    have hgt : 25 + 10*(q*M) < r := by omega
    have hmul := Nat.mul_lt_mul_of_pos_right hgt hr.pos
    have hqMr := Nat.mul_le_mul_left (q*M) (show 1 ≤ r from hr.pos)
    nlinarith
  have hUsmall : U ≤ 177 * (q*M) := by omega
  have hqa := prime_pow_lt_sigma hq (by omega : 0 < a)
  have hbound : q ^ a < 2 * (M*U) := by
    have hlt := Nat.mul_lt_mul_of_pos_left hrsig (by omega : 0 < 2*M)
    change sigma 1 (q^a) * i = 2 * (r^e * M) at hret
    have hs : sigma 1 (q^a) * i < (2 * (M*U)) * i := by nlinarith only [hret, hlt]
    exact hqa.trans (Nat.lt_of_mul_lt_mul_right hs)
  have hsmall : q ^ (a-1) < 360 * M^2 := by
    apply Nat.lt_of_mul_lt_mul_left (a := q)
    rw [← pow_succ', show a - 1 + 1 = a by omega]
    have := Nat.mul_le_mul_left M hUsmall
    nlinarith
  have hvle := Nat.le_of_dvd (by omega : 0 < a+1) hvlen
  have ha9 : a < 9 := by
    by_contra! h
    have hfast := (growth_at_nine h).trans_le (Nat.pow_le_pow_left hq7 (a-1))
    have hpoly := Nat.pow_le_pow_left hvle 4
    dsimp [M] at hsmall
    nlinarith
  omega

end OddPerfect
