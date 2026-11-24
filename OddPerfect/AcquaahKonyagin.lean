module

public import OddPerfect.RankBounds
public import OddPerfect.FewPrimes

public section

namespace OddPerfect

open Finset ArithmeticFunction

private theorem pow_coprime_sigma {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (p ^ e).Coprime (sigma 1 (p ^ e)) := by
  apply Nat.Coprime.pow_left _ (hp.coprime_iff_not_dvd.mpr ?_)
  rw [sigma_one_apply_prime_pow hp, geom_sum_succ]
  intro hd
  exact hp.not_dvd_one ((Nat.dvd_add_iff_right (dvd_mul_right _ _)).mpr hd)

/-- Suppose q divides the divisor sum of p^e, writing that sum as qu.
Its full returning component divides (q+1)z. Then p^e is at most u²z. -/
private theorem component_le_return {p q e u z : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hu : 0 < u) (hz : 0 < z) (hout : sigma 1 (p ^ e) = q*u)
    (hback : p^e ∣ (q+1)*z) : p^e ≤ u^2*z := by
  by_cases hd : p ∣ q+1
  · have hdqu : p ∣ (q+1)*u := hd.trans (dvd_mul_right _ _)
    have hsum : q*u = p * (∑ j ∈ range e, p^j) + 1 := by
      rw [← hout, sigma_one_apply_prime_pow hp, geom_sum_succ]
    have hd1 : p ∣ (u+1) := by
      apply (Nat.dvd_add_iff_right (dvd_mul_right p (∑ j ∈ range e, p^j))).mpr
      convert hdqu using 1
      nlinarith only [hsum]
    have hpu := Nat.le_of_dvd (Nat.succ_pos u) hd1
    let d := (p-1)*u - 1
    have hdpos : 0 < d := by
      have := Nat.mul_le_mul (show 2 ≤ p-1 by omega) (show 1 ≤ u by omega)
      dsimp [d]; omega
    have hg := geom_sum_mul_add (p-1) (e+1)
    rw [Nat.sub_add_cancel hp.one_lt.le, ← sigma_one_apply_prime_pow hp, hout, pow_succ] at hg
    have href : (p^e * p)*z + d*z = ((q+1)*z)*((p-1)*u) := by
      have hd' : d + 1 = (p-1)*u := Nat.sub_add_cancel (Nat.mul_pos (by omega) hu)
      rw [← hg]
      nlinarith only [congrArg (fun x => x*z) hd']
    have hdv : p^e ∣ d*z := by
      apply (Nat.dvd_add_iff_right ((dvd_mul_right (p^e) p).trans (dvd_mul_right _ z))).mpr
      rw [href]
      exact hback.trans (dvd_mul_right _ _)
    have hdu : d ≤ u^2 := by
      exact (Nat.sub_le _ _).trans (by rw [pow_two]; exact Nat.mul_le_mul_right u (by omega))
    exact (Nat.le_of_dvd (Nat.mul_pos hdpos hz) hdv).trans (Nat.mul_le_mul_right z hdu)
  · have hc := (hp.coprime_iff_not_dvd.mpr hd).pow_left e
    have hle := Nat.le_of_dvd hz (hc.dvd_of_dvd_mul_left hback)
    exact hle.trans (Nat.le_mul_of_pos_left _ (pow_pos hu _))

/-- Acquaah and Konyagin's upper bound for every prime divisor of an odd
perfect number, in its integral form. -/
theorem prime_cube_lt_three_mul {N q : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hqN : q ∈ N.primeFactors) : q ^ 3 < 3 * N := by
  let P := N.primeFactors
  let S : Finset ℕ := {q}
  let e := N.factorization
  let g (p : ℕ) := sigma 1 (p ^ e p)
  have hq := Nat.prime_of_mem_primeFactors hqN
  have hsub : S ⊂ P := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨singleton_subset_iff.mpr hqN, ?_⟩
    intro hh
    have hc := four_le_distinct_prime_factor_count ho hN
    change 4 ≤ P.card at hc
    rw [← hh, card_singleton] at hc
    omega
  have hpos : 0 < e q := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hqN)
  by_cases he : e q = 1
  · obtain ⟨p, hp', v, hv, hedge⟩ := exists_sigmaEdge_entering hN S hsub (singleton_nonempty _)
    have hvq : v = q := mem_singleton.mp hv
    subst v
    have hpN := (mem_sdiff.mp hp').1
    have hp := Nat.prime_of_mem_primeFactors hpN
    have hpq : p ≠ q := fun h => (mem_sdiff.mp hp').2 (mem_singleton.mpr h)
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      have := (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hpN)).not_two_dvd_nat
      omega
    obtain ⟨u, hu⟩ := hedge.2.2
    change g p = q * u at hu
    let z := ((P.erase q).erase p).prod g
    have hgpos (j : ℕ) (hj : j ∈ P) : 0 < g j := by
      have hpp := Nat.prime_of_mem_primeFactors hj
      have hpos : 1 < j ^ e j := one_lt_pow₀ hpp.one_lt (Finsupp.mem_support_iff.mp hj)
      exact hpos.le.trans (self_lt_sigma_of_one_lt hpos).le
    have hz : 0 < z := prod_pos fun j hj => hgpos j (mem_of_mem_erase (mem_of_mem_erase hj))
    have hu0 : 0 < u := by have := hgpos p hpN; rw [hu] at this; exact Nat.pos_of_mul_pos_left this
    have hpeq := Finset.mul_prod_erase (P.erase q) g (mem_erase.mpr ⟨hpq,hpN⟩)
    have hfull : (q+1)*(q*u)*z = 2*N := by
      have hqg : g q = q+1 := by simp [g, he, sigma_one_apply_prime_pow hq, sum_range_succ, add_comm]
      change g p * z = (P.erase q).prod g at hpeq
      rw [← hu, ← hqg, mul_assoc, hpeq, mul_prod_erase P g hqN]
      rw [show P.prod g = sigma 1 N from (isMultiplicative_sigma.multiplicative_factorization _ hN.2.ne').symm,
        sigma_one_apply]
      exact (Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN
    have hR : p ^ e p ∣ 2*N := (hp.pow_dvd_iff_le_factorization hN.2.ne' |>.mpr le_rfl).trans
      (dvd_mul_left _ _)
    have hback : p ^ e p ∣ (q+1)*z := by
      have hmem : p ^ e p ∣ (q*u)*((q+1)*z) := by convert hR using 1; rw [← hfull]; ring
      have hc := pow_coprime_sigma hp (e p)
      change (p ^ e p).Coprime (g p) at hc
      rw [hu] at hc
      exact hc.dvd_of_dvd_mul_left hmem
    have hRcap := component_le_return hp hp3 hu0 hz hu hback
    have hlocal := two_mul_sigma_prime_pow_lt_three_mul hp hp3 (e p)
    change 2 * g p < 3 * p ^ e p at hlocal
    rw [hu] at hlocal
    have hsmall : 2*q < 3*u*z := by
      apply Nat.lt_of_mul_lt_mul_right (a := u)
      nlinarith only [hlocal, hRcap]
    have hfactor := Nat.mul_lt_mul_of_pos_right hsmall (Nat.mul_pos hq.pos hq.pos)
    nlinarith only [hfactor, hfull, Nat.zero_le (q*u*z)]
  · have hq2 : q ^ 2 ≤ q ^ e q := Nat.pow_le_pow_right hq.pos (by omega)
    have h := rank_cut_product_bound hN ho S hsub (singleton_nonempty _) (t := q)
      (fun p hp => (mem_singleton.mp hp).ge)
    simp only [S, prod_singleton] at h
    change 2 * q * q ^ e q < 3 * N at h
    have := Nat.mul_le_mul_left q hq2
    nlinarith only [this, h, Nat.zero_le (q*q^e q)]

end OddPerfect
