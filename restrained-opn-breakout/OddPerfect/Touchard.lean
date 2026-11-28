module

public import OddPerfect.Euler
public import OddPerfect.Forcing
import Mathlib.Algebra.Order.Ring.Abs

/-! # Divisibility in Euler's form and Touchard's congruences -/

public section

namespace OddPerfect

open ArithmeticFunction

/-- The prime-power divisor sum is one modulo its base prime. -/
theorem sigma_prime_pow_mod_self {p : ℕ} (hp : p.Prime) (a : ℕ) :
    sigma 1 (p ^ a) % p = 1 := by
  rw [sigma_one_apply_prime_pow hp, Finset.sum_range_succ']
  simp only [pow_zero, pow_succ, ← Finset.sum_mul]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hp.one_lt]

/-- Removing the full prime-power part leaves a cofactor divisible by its divisor
sum up to the factor two from perfection. -/
theorem sigma_exact_pow_dvd_twice_cofactor {N p a b : ℕ} (hN : Nat.Perfect N)
    (hp : p.Prime) (hNb : N = p ^ a * b) (hpb : ¬ p ∣ b) :
    sigma 1 (p ^ a) ∣ 2 * b := by
  have hcop := (hp.coprime_iff_not_dvd.mpr hpb).pow_left a
  have h := sum_divisors_dvd_two_mul hN hNb hcop
  rw [← sigma_one_apply, hNb, mul_left_comm] at h
  apply (hp.coprime_iff_not_dvd.mpr ?_).symm.pow_right a |>.dvd_of_dvd_mul_left h
  rw [Nat.dvd_iff_mod_eq_zero, sigma_prime_pow_mod_self hp]
  decide

/-- In Euler's form, half the divisor sum of the Euler prime power divides the square factor. -/
theorem half_sigma_euler_dvd_square {n q a m : ℕ} (hperf : Nat.Perfect n)
    (hq : q.Prime) (hqm : ¬ q ∣ m) (heq : n = q ^ a * m ^ 2) (hqodd : Odd q) (ha : Odd a) :
    sigma 1 (q ^ a) / 2 ∣ m ^ 2 := by
  have h := sigma_exact_pow_dvd_twice_cofactor hperf hq heq (fun h => hqm (hq.dvd_of_dvd_pow h))
  have hpar : sigma 1 (q ^ a) % 2 = (a + 1) % 2 :=
    sigma_modEq_of_one hq (Nat.odd_iff.mp hqodd) a
  have := Nat.odd_iff.mp ha
  apply Nat.dvd_of_mul_dvd_mul_left Nat.zero_lt_two
  rwa [show 2 * (sigma 1 (q ^ a) / 2) = sigma 1 (q ^ a) by omega]

private theorem sq_mod_four {m : ℕ} (h : Odd m) : m ^ 2 % 4 = 1 := by
  have := Nat.odd_iff.mp h
  have hm : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rw [pow_two, Nat.mul_mod]; rcases hm with h | h <;> simp [h]

/-- Every odd perfect number is one modulo four. -/
theorem odd_perfect_mod_four {n : ℕ} (ho : Odd n) (hN : Nat.Perfect n) : n % 4 = 1 := by
  obtain ⟨q, a, m, _, hq4, _, _, heq⟩ := euler_form ho hN
  have hmd : m ∣ n := by rw [heq, pow_two]; exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  have hqa : q ^ a % 4 = 1 := by simpa [Nat.ModEq] using (show q ≡ 1 [MOD 4] from hq4).pow a
  rw [heq, Nat.mul_mod, hqa, sq_mod_four (ho.of_dvd_nat hmd)]

/-- Touchard's 1953 congruences. Three is absent in the first case and divides
with even positive exponent in the second. -/
theorem touchard_congruence {n : ℕ} (ho : Odd n) (hN : Nat.Perfect n) :
    n % 12 = 1 ∨ n % 36 = 9 := by
  have hn4 := odd_perfect_mod_four ho hN
  obtain ⟨q, a, m, hp, hq4, ha4, hqm, heq⟩ := euler_form ho hN
  have h3 : Nat.Prime 3 := by decide
  have hq3 : ¬ 3 ∣ q := fun h => (by omega : q ≠ 3) <|
    ((hp.eq_one_or_self_of_dvd 3 h).resolve_left (by decide)).symm
  by_cases hd : 3 ∣ n
  · right
    have hm : 3 ∣ m := by
      rw [heq] at hd
      exact h3.dvd_of_dvd_pow ((h3.dvd_mul.mp hd).resolve_left (fun h => hq3 (h3.dvd_of_dvd_pow h)))
    obtain ⟨k, hk⟩ := hm
    have h9 : 9 ∣ n := by rw [heq, hk, mul_pow]; exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
    omega
  · left
    have hm : ¬ 3 ∣ m := fun h => hd <| heq ▸ dvd_mul_of_dvd_right (dvd_pow h (by decide : 2 ≠ 0)) _
    have hsum := sigma_exact_pow_dvd_twice_cofactor hN hp heq (fun h => hqm (hp.dvd_of_dvd_pow h))
    have hsucc := (succ_dvd_sigma_prime_pow hp (Nat.odd_iff.mpr (by omega : a % 2 = 1))).trans hsum
    have hnq : ¬ 3 ∣ q + 1 := by
      intro h
      exact hm (h3.dvd_of_dvd_pow ((h3.dvd_mul.mp (h.trans hsucc)).resolve_left (by decide)))
    have hq1 : q ≡ 1 [MOD 3] := by change q % 3 = 1; omega
    have hm1 : m ^ 2 % 3 = 1 := by
      have h12 : m % 3 = 1 ∨ m % 3 = 2 := by omega
      rw [pow_two, Nat.mul_mod]; rcases h12 with h | h <;> simp [h]
    have hn3 : n % 3 = 1 := by
      have hqa : q ^ a % 3 = 1 := by simpa [Nat.ModEq] using hq1.pow a
      rw [heq, Nat.mul_mod, hqa, hm1]
    omega

/-- At exact exponent `2*k` of any prime `p ≡ 3 (mod 4)`, one can remove both
`p^(2*k)` and its full divisor sum and still have a cofactor equal to one modulo four. -/
theorem exact_even_component_congruence {N p k : ℕ} (hN : Nat.Perfect N) (ho : Odd N)
    (hp : p.Prime) (hp4 : p % 4 = 3) (he : N.factorization p = 2 * k) :
    ∃ t : ℕ, N = (p ^ (2 * k) * sigma 1 (p ^ (2 * k))) * (4 * t + 1) := by
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  have hbase : p ^ 2 ≡ 1 [MOD 4] := sq_mod_four hpodd
  have hpow : p ^ (2 * k) % 4 = 1 := by
    rw [pow_mul]
    simpa [Nat.ModEq] using hbase.pow k
  have hlast : p ^ (2 * k + 1) % 4 = 3 := by rw [pow_succ, Nat.mul_mod, hpow, hp4]
  have hsum : 4 ∣ sigma 1 (p ^ (2 * k + 1)) :=
    (show 4 ∣ p + 1 by omega).trans (succ_dvd_sigma_prime_pow hp ⟨k, rfl⟩)
  rw [sigma_one_apply_prime_pow hp, Finset.sum_range_succ, ← sigma_one_apply_prime_pow hp] at hsum
  have hσ4 : sigma 1 (p ^ (2 * k)) % 4 = 1 := by omega
  have hσodd : Odd (sigma 1 (p ^ (2 * k))) := Nat.odd_iff.mpr (by omega)
  have hNeq : N = p ^ (2 * k) * ordCompl[p] N := by
    simpa only [he] using (Nat.ordProj_mul_ordCompl_eq_self N p).symm
  have hd := sigma_exact_pow_dvd_twice_cofactor hN hp hNeq (Nat.not_dvd_ordCompl hp hN.2.ne')
  obtain ⟨u, hu⟩ := hσodd.coprime_two_right.dvd_of_dvd_mul_left hd
  have hNu : N = (p ^ (2 * k) * sigma 1 (p ^ (2 * k))) * u := by
    calc N = p ^ (2 * k) * ordCompl[p] N := hNeq
      _ = _ := by rw [hu, mul_assoc]
  have hM4 : (p ^ (2 * k) * sigma 1 (p ^ (2 * k))) % 4 = 1 := by rw [Nat.mul_mod, hpow, hσ4]
  have hn4 := odd_perfect_mod_four ho hN
  rw [hNu, Nat.mul_mod, hM4] at hn4
  simp only [one_mul, Nat.mod_mod] at hn4
  exact ⟨u / 4, hNu.trans (congrArg (fun x => p ^ (2 * k) * sigma 1 (p ^ (2 * k)) * x)
    (show u = 4 * (u / 4) + 1 by omega))⟩

/-- Roberts's 2008 refinement of Touchard, split at the exact exponent of three. -/
theorem roberts_congruence {N : ℕ} (hN : Nat.Perfect N) (ho : Odd N) :
    N % 12 = 1 ∨ N % 468 = 117 ∨ N % 324 = 81 := by
  rcases touchard_congruence ho hN with h | h
  · exact Or.inl h
  right
  have p3 : Nat.Prime 3 := by decide
  have h9 : 3 ^ 2 ∣ N := by change 9 ∣ N; omega
  by_cases h27 : 27 ∣ N
  · right
    obtain ⟨p, _, hp4, _, hEven⟩ := euler_exponents ho hN
    have := Nat.even_iff.mp (hEven 3 (by omega))
    have h3le := (p3.pow_dvd_iff_le_factorization hN.2.ne' (k := 3)).mp h27
    have h81 : 81 ∣ N := (p3.pow_dvd_iff_le_factorization hN.2.ne' (k := 4)).mpr (by omega)
    omega
  · left
    have := thirteen_dvd_of_exact_nine hN h9 h27
    omega

end OddPerfect
