module

public import OddPerfect.Euler
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.BigOperators.ModEq

/-! # Chen and Luo's congruences for the square part of an odd perfect number -/

public section
namespace OddPerfect
open ArithmeticFunction Finset

private theorem square_mod_eight {x : ℕ} (hx : Odd x) : x^2 ≡ 1 [MOD 8] := by
  have := Nat.odd_iff.mp hx
  have hc : x%8=1 ∨ x%8=3 ∨ x%8=5 ∨ x%8=7 := by omega
  change x^2 % 8 = 1
  rw [pow_two, Nat.mul_mod]
  rcases hc with h | h | h | h <;> simp [h]

private theorem geom_mod_one {x : ℕ} (hx : x ≡ 1 [MOD 8]) (t : ℕ) :
    (∑ i ∈ range t, x^i) ≡ t [MOD 8] := by
  induction t with
  | zero => simp [Nat.ModEq]
  | succ t ih =>
    rw [sum_range_succ]
    exact ih.add (by simpa using hx.pow t)

private theorem geom_pairs (q t : ℕ) :
    (∑ i ∈ range (2*t), q^i) = (q+1) * ∑ i ∈ range t, (q^2)^i := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ, sum_range_succ, sum_range_succ, sum_range_succ, ih, ← pow_mul, pow_succ q (2*t)]
    ring

/-- For every odd prime and odd exponent, the halved component sum has a
closed residue modulo eight. -/
theorem half_sigma_prime_pow_mod_eight {q a : ℕ} (hq : q.Prime) (hqo : Odd q) (hao : Odd a) :
    sigma 1 (q^a) / 2 ≡ ((q+1)/2)*((a+1)/2) [MOD 8] := by
  have hq2 := Nat.odd_iff.mp hqo
  have ha2 := Nat.odd_iff.mp hao
  let t := (a+1)/2
  have hgeom : sigma 1 (q^a) = 2 * (((q+1)/2) * ∑ i ∈ range t, (q^2)^i) := by
    rw [sigma_one_apply_prime_pow hq, show a+1=2*t by dsimp [t]; omega, geom_pairs, ← mul_assoc]
    congr 1
    omega
  rw [hgeom, Nat.mul_div_cancel_left _ (by decide)]
  exact (geom_mod_one (square_mod_eight hqo) t).mul_left _

private theorem odd_pow_mod_eight {q a : ℕ} (hqo : Odd q) (hao : Odd a) : q^a ≡ q [MOD 8] := by
  obtain ⟨k,hk⟩ := hao
  have h := (square_mod_eight hqo).pow k
  simpa [show a = 2*k+1 by omega, pow_succ, pow_mul] using h.mul_right q

/-- A single formula gives the residue of the square-part divisor sum modulo eight
from the residues of the Euler prime and its exponent modulo sixteen. -/
theorem sigma_square_mod_eight_of_euler {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (hqm : ¬ q ∣ m) (hform : N = q^a*m^2) :
    sigma 1 (m^2) ≡ q * (((q+1)/2)*((a+1)/2)) [MOD 8] := by
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  have hao : Odd a := Nat.odd_iff.mpr (by omega)
  have hmo : Odd m := ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _)
  have hσ : sigma 1 N = 2*N := by
    rw [sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN
  rw [hform, isMultiplicative_sigma.map_mul_of_coprime ((hq.coprime_iff_not_dvd.mpr hqm).pow_left a |>.pow_right 2)] at hσ
  have htwo : 2 ∣ sigma 1 (q^a) := (show 2 ∣ q+1 by have := Nat.odd_iff.mp hqo; omega).trans (succ_dvd_sigma_prime_pow hq hao)
  have hhalf : sigma 1 (q^a)/2 * sigma 1 (m^2) = q^a*m^2 := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0<2)
    rw [← mul_assoc, Nat.mul_div_cancel' htwo]
    exact hσ
  let c := ((q+1)/2)*((a+1)/2)
  have hc : Odd c := (Nat.odd_iff.mpr (by omega : ((q+1)/2)%2=1)).mul (Nat.odd_iff.mpr (by omega : ((a+1)/2)%2=1))
  have hbase : c * sigma 1 (m^2) ≡ q [MOD 8] := by
    calc c * sigma 1 (m^2) ≡ (sigma 1 (q^a)/2) * sigma 1 (m^2) [MOD 8] :=
          (half_sigma_prime_pow_mod_eight hq hqo hao).symm.mul_right _
      _ = q^a*m^2 := hhalf
      _ ≡ q [MOD 8] := by simpa using (odd_pow_mod_eight hqo hao).mul (square_mod_eight hmo)
  calc sigma 1 (m^2) = 1*sigma 1 (m^2) := (one_mul _).symm
    _ ≡ c^2*sigma 1 (m^2) [MOD 8] := (square_mod_eight hc).symm.mul_right _
    _ = c*(c*sigma 1 (m^2)) := by rw [pow_two, mul_assoc]
    _ ≡ c*q [MOD 8] := hbase.mul_left c
    _ = q*c := mul_comm _ _

/-- Both biconditionals in Chen–Luo, Theorem 3.3. -/
theorem chen_luo_congruences {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (hqm : ¬ q ∣ m) (hform : N=q^a*m^2) :
    ((sigma 1 (m^2)) % 4 = 1 ↔ q%8 = a%8) ∧ ((sigma 1 (m^2)) % 4 = 3 ↔ q%8 = (a+4)%8) := by
  have h := (sigma_square_mod_eight_of_euler hN ho hq hq4 ha4 hqm hform).of_dvd (by decide : 4 ∣ 8)
  change sigma 1 (m^2) %4 = (q*(((q+1)/2)*((a+1)/2)))%4 at h
  rw [Nat.mul_mod, hq4, one_mul, Nat.mod_mod, Nat.mul_mod] at h
  have cases (x : ℕ) (hx : x%4=1) :
      (x%8=1 ∧ ((x+1)/2)%4=1) ∨ (x%8=5 ∧ ((x+1)/2)%4=3) := by omega
  rcases cases q hq4 with hq | hq <;> rcases cases a ha4 with ha | ha <;> rw [hq.2,ha.2] at h <;> omega

private theorem sigma_three_mod_four_even {p : ℕ} (hp : p.Prime) (hp3 : p%4=3) (k : ℕ) :
    sigma 1 (p^(2*k)) ≡ 1 [MOD 4] := by
  have hz : p+1 ≡ 0 [MOD 4] := by change (p+1)%4=0; omega
  have hs := (square_mod_eight (Nat.odd_iff.mpr (by omega : p%2=1))).of_dvd (by decide : 4 ∣ 8)
  rw [sigma_one_apply_prime_pow hp, sum_range_succ, geom_pairs]
  simpa [pow_mul] using (hz.mul_right (∑ i ∈ range k, (p^2)^i)).add (hs.pow k)

/-- The parity count in the remark following Chen–Luo Theorem 3.3. For any odd
square, only bases `1 mod 4` with odd exponent in its root contribute a minus sign. -/
theorem sigma_square_mod_four_factor_count {m : ℕ} (hm : Odd m) :
    sigma 1 (m^2) ≡ 3^((m.primeFactors.filter fun p => p%4=1 ∧ Odd (m.factorization p)).card) [MOD 4] := by
  let good := fun p : ℕ => p%4=1 ∧ Odd (m.factorization p)
  rw [isMultiplicative_sigma.multiplicative_factorization _ (pow_ne_zero _ hm.pos.ne')]
  change (∏ p ∈ (m^2).primeFactors, sigma 1 (p^((m^2).factorization p))) ≡ _ [MOD 4]
  rw [Nat.primeFactors_pow _ (by decide : 2 ≠ 0)]
  calc ∏ p ∈ m.primeFactors, sigma 1 (p^((m^2).factorization p)) ≡
       ∏ p ∈ m.primeFactors, (if good p then 3 else 1) [MOD 4] := by
        apply Nat.ModEq.prod
        intro p hp
        have hprime := Nat.prime_of_mem_primeFactors hp
        have hpo := Nat.odd_iff.mp (hm.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
        by_cases hp1 : p%4=1
        · have h := sigma_modEq_of_one hprime (show p ≡ 1 [MOD 4] from hp1) (2*m.factorization p)
          apply h.trans
          dsimp [good]
          split_ifs with hgood
          · have := Nat.odd_iff.mp hgood.2
            change (2*m.factorization p+1)%4=3
            omega
          · have hpar : ¬ Odd (m.factorization p) := fun H => hgood ⟨hp1,H⟩
            rw [Nat.odd_iff] at hpar
            change (2*m.factorization p+1)%4=1
            omega
        · simpa [good, hp1] using sigma_three_mod_four_even hprime (by omega) (m.factorization p)
    _ = _ := by rw [← Finset.prod_filter]; simp [good]

private theorem three_pow_mod_four_iff_odd (n : ℕ) : 3^n %4=3 ↔ Odd n := by
  have hp : (3:ℕ)^2 ≡ 1 [MOD 4] := by decide
  have h := hp.pow (n/2)
  rw [← pow_mul, one_pow] at h
  change 3^(2*(n/2)) %4=1 at h
  rcases Nat.even_or_odd n with he | ho
  · have := Nat.even_iff.mp he
    rw [show n=2*(n/2) by omega] at ⊢
    rw [h,Nat.odd_iff]; omega
  · have := Nat.odd_iff.mp ho
    have heq : n=2*(n/2)+1 := by omega
    rw [heq, pow_succ, Nat.mul_mod, h, Nat.odd_iff]
    omega

/-- The Euler prime and exponent differ by four modulo eight exactly when an
odd number of square-part primes meet the two component conditions. -/
theorem chen_luo_odd_factor_count {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (hqm : ¬ q ∣ m) (hform : N=q^a*m^2) :
    q%8=(a+4)%8 ↔ Odd ((m.primeFactors.filter fun p => p%4=1 ∧ Odd (m.factorization p)).card) := by
  have hm : Odd m := ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _)
  obtain ⟨_,h⟩ := chen_luo_congruences hN ho hq hq4 ha4 hqm hform
  rw [← h, ← three_pow_mod_four_iff_odd, show sigma 1 (m^2) %4 = _ from sigma_square_mod_four_factor_count hm]

/-- Corrected residue classes for the two values that are three modulo four.
This gives the biconditional form of Dris–San Diego's 2023 corrigendum. -/
theorem sigma_square_three_or_seven_mod_eight {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (hqm : ¬ q ∣ m) (hform : N=q^a*m^2) :
    (sigma 1 (m^2) %8=3 ↔ a%16=(q+4)%16) ∧ (sigma 1 (m^2) %8=7 ↔ a%16=(q+12)%16) := by
  have h := sigma_square_mod_eight_of_euler hN ho hq hq4 ha4 hqm hform
  change sigma 1 (m^2) %8 = (q*(((q+1)/2)*((a+1)/2)))%8 at h
  rw [Nat.mul_mod q _ 8,Nat.mul_mod ((q+1)/2) _ 8] at h
  have cases (x : ℕ) (hx : x%4=1) :
      (x%16=1 ∧ x%8=1 ∧ ((x+1)/2)%8=1) ∨ (x%16=5 ∧ x%8=5 ∧ ((x+1)/2)%8=3) ∨
      (x%16=9 ∧ x%8=1 ∧ ((x+1)/2)%8=5) ∨ (x%16=13 ∧ x%8=5 ∧ ((x+1)/2)%8=7) := by omega
  rcases cases q hq4 with H | H | H | H <;> rcases cases a ha4 with J | J | J | J <;>
    rw [H.2.1,H.2.2,J.2.2] at h <;> omega

end OddPerfect
