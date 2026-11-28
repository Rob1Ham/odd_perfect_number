module

public import OddPerfect.Reciprocal
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith

public section

namespace OddPerfect

open ArithmeticFunction

/-- If each component of the odd square feeds only `q`, and the reverse sum contains
the square, then the square root divides the length of the sum at `q`. -/
theorem root_dvd_length_of_reciprocal_square {m q a β : ℕ} (hm : Odd m) (hq : Nat.Prime q)
    (hout : sigma 1 (m ^ 2) = q ^ β) (hback : m ^ 2 ∣ sigma 1 (q ^ a)) : m ∣ a + 1 := by
  apply (Nat.factorization_le_iff_dvd hm.pos.ne' (by omega : a + 1 ≠ 0)).mp
  intro p
  by_cases hmem : p ∈ m.primeFactors
  · obtain ⟨hp, hpm, _⟩ := Nat.mem_primeFactors.mp hmem
    have hm2 : m ^ 2 ≠ 0 := pow_ne_zero _ hm.pos.ne'
    have hmem2 : p ∈ (m ^ 2).primeFactors := Nat.mem_primeFactors.mpr
      ⟨hp, hpm.trans (dvd_pow_self _ (by decide : 2 ≠ 0)), hm2⟩
    let l := (m ^ 2).factorization p
    have hl : l = 2 * m.factorization p := by simp [l, Nat.factorization_pow]
    have he : 0 < m.factorization p := (hp.dvd_iff_one_le_factorization hm.pos.ne').mp hpm
    have hpow : sigma 1 (p ^ l) ∣ q ^ β := by
      rw [← hout, isMultiplicative_sigma.multiplicative_factorization _ hm2]
      exact Finset.dvd_prod_of_mem _ hmem2
    obtain ⟨β, _, hβ⟩ := (Nat.dvd_prime_pow hq).mp hpow
    have hrec := reciprocal_component_length hp (hm.of_dvd_nat hpm) hq (by omega : 0 < l)
      hβ ((Nat.ordProj_dvd (m ^ 2) p).trans hback)
    have hbound := (hp.pow_dvd_iff_le_factorization (by omega : a + 1 ≠ 0)).mp hrec
    omega
  · rw [Finsupp.notMem_support_iff.mp hmem]
    exact Nat.zero_le _

private theorem component_lt_sigma {q a : ℕ} (hq : Nat.Prime q) (ha : 0 < a) :
    q ^ a < sigma 1 (q ^ a) := by
  rw [sigma_one_apply_prime_pow hq, Finset.sum_range_succ]
  have hsum : 0 < ∑ j ∈ Finset.range a, q ^ j :=
    Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨0, Finset.mem_range.mpr ha, by simp⟩
  omega

private theorem two_sq_lt_five_pow {a : ℕ} (ha : 2 ≤ a) : 2 * (a + 1) ^ 2 < 5 ^ a := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ a ha ih =>
    rw [pow_succ 5 a]
    nlinarith

/-- The simultaneous equalities proposed by Suryanarayana cannot hold for the odd
Euler square and special prime power. -/
theorem not_euler_index_one {m q a : ℕ} (hm : Odd m) (hq : Nat.Prime q)
    (hq4 : q % 4 = 1) (ha : 0 < a) (hout : sigma 1 (m ^ 2) = q ^ a) :
    sigma 1 (q ^ a) ≠ 2 * m ^ 2 := by
  intro hback
  have hmdiv := root_dvd_length_of_reciprocal_square hm hq hout
    (hback ▸ dvd_mul_left _ _)
  have hle := Nat.le_of_dvd (by omega : 0 < a + 1) hmdiv
  have hs := Nat.mul_self_le_mul_self hle
  have hq5 : 5 ≤ q := by have := hq.two_le; omega
  have hlt := component_lt_sigma hq ha
  rw [hback] at hlt
  have ha1 : a = 1 := by
    by_contra h
    have hfast := (two_sq_lt_five_pow (by omega : 2 ≤ a)).trans_le (Nat.pow_le_pow_left hq5 a)
    nlinarith
  subst a
  have hmo := Nat.odd_iff.mp hm
  have hm1 : m = 1 := by omega
  simp [hm1] at hout
  omega

/-- Every Euler component has odd index at least three. In particular its size
satisfies the strict inequality `3 * q^a < 2 * m²`. -/
theorem euler_component_index_bound {N q a m : ℕ} (hN : Nat.Perfect N) (ho : Odd N)
    (hq : Nat.Prime q) (hq4 : q % 4 = 1) (ha4 : a % 4 = 1) (hqm : ¬ q ∣ m)
    (hform : N = q ^ a * m ^ 2) :
    3 * q ^ a < 2 * m ^ 2 ∧
    ∃ i : ℕ, Odd i ∧ 3 ≤ i ∧ sigma 1 (m ^ 2) = q ^ a * i ∧
      sigma 1 (q ^ a) * i = 2 * m ^ 2 := by
  have hm : Odd m := ho.of_dvd_nat (hform ▸
    (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left _ _))
  obtain ⟨i, hi, hleft, hright, _⟩ := exists_component_index hN hq hform
    (fun hd => hqm (hq.dvd_of_dvd_pow hd))
  have hv := sigma_modEq_of_one hq (show q ≡ 1 [MOD 4] from hq4) a
  change sigma 1 (q ^ a) % 4 = (a + 1) % 4 at hv
  obtain ⟨t, ht⟩ : 2 ∣ sigma 1 (q ^ a) := by omega
  have hidiv : i ∣ m ^ 2 := by
    refine ⟨t, ?_⟩
    apply Nat.mul_left_cancel (by decide : 0 < 2)
    rw [← hright, ht]
    ac_rfl
  have hodd : Odd i := hm.pow.of_dvd_nat hidiv
  have hi1 : i ≠ 1 := by
    rintro rfl
    simp only [Nat.mul_one] at hleft hright
    exact not_euler_index_one hm hq hq4 (by omega) hleft hright
  have h3 : 3 ≤ i := by have := Nat.odd_iff.mp hodd; omega
  refine ⟨?_, i, hodd, h3, hleft, hright⟩
  calc
    3 * q ^ a < 3 * sigma 1 (q ^ a) :=
      Nat.mul_lt_mul_of_pos_left (component_lt_sigma hq (by omega)) (by decide)
    _ ≤ sigma 1 (q ^ a) * i := by rw [Nat.mul_comm 3]; exact Nat.mul_le_mul_left _ h3
    _ = _ := hright

end OddPerfect
