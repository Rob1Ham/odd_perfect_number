module

public import OddPerfect.Touchard
public import Mathlib.NumberTheory.Multiplicity

/-!
Dris and Luca, *A note on odd perfect numbers*, Fibonacci Quarterly 54 (2016),
291–296, §1 and Lemma 2.2. [Paper](https://www.fq.math.ca/Papers1/54-4/DrisLuca09122016.pdf)
-/

public section

namespace OddPerfect

open ArithmeticFunction

/-- An exact component `p^e` and cofactor `b` have a common positive index in the
two divisor-sum identities of Dris and Luca. This also applies to even perfect numbers. -/
theorem exists_component_index {N p e b : ℕ} (hN : Nat.Perfect N) (hp : Nat.Prime p)
    (hNb : N = p ^ e * b) (hpb : ¬ p ∣ b) :
    ∃ i : ℕ, 0 < i ∧ sigma 1 b = p ^ e * i ∧ sigma 1 (p ^ e) * i = 2 * b ∧ i ∣ 2 * N := by
  have hcop := (hp.coprime_iff_not_dvd.mpr hpb).pow_left e
  have hmul : sigma 1 (p ^ e) * sigma 1 b = 2 * N := by
    rw [← isMultiplicative_sigma.map_mul_of_coprime hcop, ← hNb, sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN
  obtain ⟨i, hi⟩ := sigma_exact_pow_dvd_twice_cofactor hN hp hNb hpb
  have hbe : sigma 1 b = p ^ e * i := by
    apply Nat.mul_left_cancel (sigma_pos _ _ (pow_ne_zero _ hp.ne_zero))
    calc
      _ = 2 * (p ^ e * b) := hmul.trans (congrArg (2 * ·) hNb)
      _ = (2 * b) * p ^ e := by ac_rfl
      _ = _ := by rw [hi]; ac_rfl
  have hb : b ≠ 0 := by rintro rfl; simp at hNb; exact hN.2.ne' hNb
  have hpos := sigma_pos 1 b hb
  rw [hbe] at hpos
  refine ⟨i, Nat.pos_of_ne_zero (by rintro rfl; simp at hpos), hbe, hi.symm, ?_⟩
  rw [← hmul, hbe]
  exact (dvd_mul_left i (p ^ e)).trans (dvd_mul_left _ _)

/-- The return depth `t` can differ from the outgoing exponent `l`. -/
theorem reciprocal_return_length {p q l a β t : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hq : Nat.Prime q) (hl : 0 < l) (hout : sigma 1 (p ^ l) = q ^ β)
    (hback : p ^ t ∣ sigma 1 (q ^ a)) : p ^ (t - 1) ∣ a + 1 := by
  cases l with
  | zero => omega
  | succ k =>
    let : Fact p.Prime := ⟨hp⟩
    have hsub : q ^ β - 1 = sigma 1 (p ^ k) * p := by
      rw [← hout, sigma_one_apply_prime_pow hp, Finset.sum_range_succ', sigma_one_apply_prime_pow hp]
      simp [pow_succ, Finset.sum_mul]
    have hnot (j : ℕ) : ¬ p ∣ sigma 1 (p ^ j) := by
      rw [Nat.dvd_iff_mod_eq_zero, sigma_prime_pow_mod_self hp]
      decide
    have hspos := sigma_pos 1 (p ^ k) (pow_ne_zero _ hp.ne_zero)
    have hx : 1 < q ^ β := by
      have := Nat.mul_pos hspos hp.pos
      omega
    have hval : (q ^ β - 1).factorization p = 1 := by
      rw [hsub, Nat.factorization_mul hspos.ne' hp.ne_zero, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (hnot k), hp.factorization_self, zero_add]
    have hpow : p ^ t ∣ q ^ (a + 1) - 1 := by
      rw [← geom_sum_mul_of_one_le (by have := hq.one_lt; omega : 1 ≤ q) (a + 1),
        ← sigma_one_apply_prime_pow hq]
      exact hback.trans (dvd_mul_right _ _)
    have hbig : p ^ t ∣ (q ^ β) ^ (a + 1) - 1 := by
      rw [← pow_mul]
      exact hpow.trans (Nat.pow_sub_one_dvd_pow_sub_one q (dvd_mul_left _ _))
    have hxy : p ∣ q ^ β - 1 := by rw [hsub]; exact dvd_mul_left _ _
    have hxnd : ¬ p ∣ q ^ β := hout ▸ hnot (k + 1)
    have hLTE := Nat.multiplicity_pow_sub_pow ho hx hxy hxnd (n := a + 1) (by omega)
    simp only [one_pow, Nat.multiplicity_eq_factorization hp, hval] at hLTE
    have hbig_pos : 1 < (q ^ β) ^ (a + 1) := one_lt_pow₀ hx (by omega)
    have hle := (hp.pow_dvd_iff_le_factorization (by omega : (q ^ β) ^ (a + 1) - 1 ≠ 0)).mp hbig
    apply (hp.pow_dvd_iff_le_factorization (by omega : a + 1 ≠ 0)).mpr
    omega

/-- Dris–Luca Lemma 2.2. A full return of `p^l` forces `p^(l−1) ∣ a+1`. -/
theorem reciprocal_component_length {p q l a β : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hq : Nat.Prime q) (hl : 0 < l) (hout : sigma 1 (p ^ l) = q ^ β)
    (hback : p ^ l ∣ sigma 1 (q ^ a)) : p ^ (l - 1) ∣ a + 1 :=
  reciprocal_return_length hp ho hq hl hout hback

end OddPerfect
