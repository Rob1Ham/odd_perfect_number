module

public import OddPerfect.SizeSeeds
public import OddPerfect.FormalParity
import OddPerfect.Cuts

/-! Divisor-sum forcing from prime divisors of component lengths, following Brent and Cohen. -/

public section

namespace OddPerfect.IndexComponent

open ArithmeticFunction Finset

/-- A divisor of the true component length gives a divisor of its geometric sum. -/
theorem sigma_dvd_of_length_dvd {p e v : ℕ} (hp : p.Prime) (h : e+1 ∣ v+1) :
    sigma 1 (p^e) ∣ sigma 1 (p^v) := by
  rw [sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hp,
    dvd_geom_sum_iff_remainder (dvd_refl (∑ i ∈ range (e+1), p^i)), Nat.mod_eq_zero_of_dvd h]
  simp

/-- The product of all selected sum divisors survives even when several of them
share a prime factor. The selected exponents need only have compatible lengths. -/
theorem sigma_dvd_of_component_lengths {D N : ℕ} (hN : N ≠ 0) (hd : D ∣ N)
    (h : ∀ p ∈ D.primeFactors, D.factorization p+1 ∣ N.factorization p+1) :
    sigma 1 D ∣ sigma 1 N := by
  have hD : D ≠ 0 := fun h => hN (zero_dvd_iff.mp (h ▸ hd))
  rw [isMultiplicative_sigma.multiplicative_factorization (sigma 1) hD,
    isMultiplicative_sigma.multiplicative_factorization (sigma 1) hN]
  refine (prod_dvd_prod_of_dvd _ _ (fun p hp => sigma_dvd_of_length_dvd
    (Nat.prime_of_mem_primeFactors hp) (h p hp))).trans ?_
  exact prod_dvd_prod_of_subset _ _ _ (Nat.primeFactors_mono hd hN)

private theorem div_gcd_two_dvd {A N : ℕ} (h : A ∣ 2*N) : A/A.gcd 2 ∣ N := by
  have hg := Nat.dvd_gcd (Nat.dvd_mul_right A N) h
  rw [Nat.gcd_mul_right] at hg
  exact (Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left A 2) (Nat.gcd_pos_of_pos_right A (by decide : 0<2))).2 hg

/-- The least common multiple joins the assigned prime powers and the odd part
of their divisor sum into a single lower bound for N. -/
theorem lcm_dvd_of_component_lengths {D N : ℕ} (hN : N.Perfect) (hd : D ∣ N)
    (h : ∀ p ∈ D.primeFactors, D.factorization p+1 ∣ N.factorization p+1) :
    D.lcm (sigma 1 D / (sigma 1 D).gcd 2) ∣ N := by
  have hv := sigma_dvd_of_component_lengths hN.2.ne' hd h
  rw [sigma_one_apply (n := N), (Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN] at hv
  exact Nat.lcm_dvd hd (div_gcd_two_dvd hv)

/-- Brent and Cohen's size bound for any positive selected even exponent,
including a divisor of a larger true exponent length. -/
theorem even_component_sq_lt {N p e : ℕ} (ho : Odd N) (hN : N.Perfect) (hp : p.Prime)
    (hd : p ∣ N) (he : 0 < e) (hpar : Even e) (hidx : e+1 ∣ N.factorization p+1) : p^(2*e) < N := by
  have hle : e ≤ N.factorization p := by have := Nat.le_of_dvd (Nat.succ_pos _) hidx; omega
  have hpow := (hp.pow_dvd_iff_le_factorization hN.2.ne').2 hle
  have hv : sigma 1 (p^e) ∣ 2*N := by
    have hfull := isMultiplicative_sigma.multiplicative_factorization (sigma 1) hN.2.ne'
    have hloc : sigma 1 (p^(N.factorization p)) ∣ sigma 1 N := by
      rw [hfull]
      exact dvd_prod_of_mem _ (Nat.mem_primeFactors.mpr ⟨hp, hd, hN.2.ne'⟩)
    have := (sigma_dvd_of_length_dvd hp hidx).trans hloc
    rwa [sigma_one_apply (n := N), (Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN] at this
  have hodd : Odd (sigma 1 (p^e)) := by
    rw [sigma_one_apply_prime_pow hp, Nat.odd_iff]
    have hm := geom_modEq_of_one (Nat.odd_iff.mp (ho.of_dvd_nat hd)) (e+1)
    change (∑ j ∈ range (e+1), p^j)%2 = (e+1)%2 at hm
    have := Nat.even_iff.mp hpar
    omega
  have hsum := hodd.coprime_two_right.dvd_of_dvd_mul_left hv
  have hcop : (p^e).Coprime (sigma 1 (p^e)) := by
    apply Nat.Coprime.pow_left _ (hp.coprime_iff_not_dvd.mpr ?_)
    rw [sigma_one_apply_prime_pow hp, geom_sum_succ]
    intro h
    exact hp.not_dvd_one ((Nat.dvd_add_iff_right (dvd_mul_right _ _)).mpr h)
  have hlo := Nat.le_of_dvd hN.2 (hcop.mul_dvd_of_dvd_of_dvd hpow hsum)
  have hgt := self_lt_sigma_of_one_lt (one_lt_pow₀ hp.one_lt he.ne')
  rw [Nat.mul_comm 2 e, pow_mul, pow_two]
  exact (Nat.mul_lt_mul_of_pos_left hgt (Nat.pow_pos hp.pos)).trans_le hlo

end OddPerfect.IndexComponent
