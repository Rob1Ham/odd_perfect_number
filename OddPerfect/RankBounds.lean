module

public import OddPerfect.Cuts
public import OddPerfect.Counts
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- All odd prime-power divisor sums have abundancy strictly below 3/2. -/
theorem two_mul_sigma_prime_pow_lt_three_mul {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) (e : ℕ) :
    2 * sigma 1 (p ^ e) < 3 * p ^ e := by
  have hh := geom_sum_mul_add (p - 1) (e+1)
  rw [Nat.sub_add_cancel hp.one_lt.le, ← sigma_one_apply_prime_pow hp, pow_succ] at hh
  have hle : p ^ e ≤ sigma 1 (p ^ e) := by
    rw [sigma_one_apply_prime_pow hp]
    exact single_le_sum (f := fun i => p ^ i) (fun i _ => Nat.zero_le _) (mem_range.mpr (Nat.lt_succ_self e))
  have hs := Nat.sub_add_cancel (by omega : 1 ≤ p)
  nlinarith [Nat.mul_le_mul_left (p - 3) hle, Nat.sub_add_cancel h3,
    congrArg (fun x => sigma 1 (p ^ e) * x) hs]

/-- Any proper nonempty group of full components receives an incoming edge
from a prime power of size greater than two thirds of its least prime. -/
theorem rank_cut_product_bound {N t : ℕ} (hN : N.Perfect) (ho : Odd N) (s : Finset ℕ)
    (hs : s ⊂ N.primeFactors) (hne : s.Nonempty) (ht : ∀ p ∈ s, t ≤ p) :
    2 * t * (∏ p ∈ s, p ^ N.factorization p) < 3 * N := by
  let c := N.primeFactors \ s
  let f := fun p => p ^ N.factorization p
  obtain ⟨u, hu, v, hvs, hedge⟩ := exists_sigmaEdge_entering hN s hs hne
  have hus := (mem_sdiff.mp hu).1
  have hp := Nat.prime_of_mem_primeFactors hus
  have hu3 : 3 ≤ u := by
    have := hp.two_le
    have := (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hus)).not_two_dvd_nat
    omega
  have hsize := two_mul_sigma_prime_pow_lt_three_mul hp hu3 (N.factorization u)
  have hsigpos : 0 < sigma 1 (f u) := by
    dsimp [f]
    rw [sigma_one_apply_prime_pow hp]
    exact Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨0, mem_range.mpr (Nat.zero_lt_succ _), by simp⟩
  have hval : v ≤ sigma 1 (f u) := Nat.le_of_dvd hsigpos hedge.2.2
  have hpos (q : ℕ) (hq : q ∈ N.primeFactors) : 0 < f q := pow_pos (Nat.prime_of_mem_primeFactors hq).pos _
  have hcpos := Finset.prod_pos (fun q (hq : q ∈ c) => hpos q (mem_sdiff.mp hq).1)
  have hdiv : f u ≤ c.prod f := Nat.le_of_dvd hcpos (dvd_prod_of_mem f hu)
  have hspos := Finset.prod_pos (fun q (hq : q ∈ s) => hpos q (hs.subset hq))
  have hsplit : c.prod f * s.prod f = N :=
    (prod_sdiff hs.subset).trans (Nat.prod_primeFactors_pow_factorization hN.2.ne').symm
  have hsmall : 2 * t < 3 * c.prod f := by
    change 2 * sigma 1 (f u) < 3 * f u at hsize
    have := ht v hvs
    omega
  calc
    _ < (3 * c.prod f) * s.prod f := Nat.mul_lt_mul_of_pos_right hsmall hspos
    _ = _ := by rw [mul_assoc, hsplit]

/-- Any selection of j true prime divisors, all at least t, bounds the
2j-th power of t. In particular one can take the j largest primes. -/
theorem prime_rank_bound {N t : ℕ} (hN : N.Perfect) (ho : Odd N) (s : Finset ℕ)
    (hs : s ⊆ N.primeFactors) (hne : s.Nonempty) (htpos : 0 < t) (ht : ∀ p ∈ s, t ≤ p) :
    2 * t ^ (2 * s.card) < 3 * N := by
  let f := fun p => p ^ N.factorization p
  have hprod : t ^ (∑ p ∈ s, N.factorization p) ≤ s.prod f := by
    rw [← prod_pow_eq_pow_sum]
    exact prod_le_prod₀ (fun p _ => Nat.zero_le _) (fun p hp => Nat.pow_le_pow_left (ht p hp) _)
  rcases eq_or_ne s N.primeFactors with rfl | hneS
  · have hsum : 2 * N.primeFactors.card ≤ ∑ p ∈ N.primeFactors, N.factorization p := by
      have h := steuerwald_prime_factor_count ho hN
      rw [← cardFactors_apply, cardFactors_eq_sum_factorization] at h
      change 2 * N.primeFactors.card + 1 ≤ ∑ p ∈ N.primeFactors, N.factorization p at h
      omega
    have hh := (Nat.pow_le_pow_right htpos hsum).trans hprod
    rw [show N.primeFactors.prod f = N from (Nat.prod_primeFactors_pow_factorization hN.2.ne').symm] at hh
    have := hN.2
    omega
  · have hsum : 2 * s.card ≤ (∑ p ∈ s, N.factorization p) + 1 := by
      obtain ⟨q, _, _, _, he⟩ := euler_exponents ho hN
      have hmin (p : ℕ) (hp : p ∈ s.erase q) : 2 ≤ N.factorization p := by
        obtain ⟨hpq, hm⟩ := mem_erase.mp hp
        have hpos : N.factorization p ≠ 0 := Finsupp.mem_support_iff.mp (hs hm)
        obtain ⟨j, hj⟩ := he p hpq
        omega
      have he2 : (s.erase q).card * 2 ≤ ∑ p ∈ s.erase q, N.factorization p := by
        simpa using sum_le_sum hmin
      by_cases hq : q ∈ s
      · have hpos : N.factorization q ≠ 0 := Finsupp.mem_support_iff.mp (hs hq)
        have hcard := card_erase_add_one hq
        have hadd := sum_erase_add s (fun p => N.factorization p) hq
        omega
      · rw [erase_eq_of_notMem hq] at he2
        omega
    have hbound : t ^ (2 * s.card) ≤ t * s.prod f := by
      calc
        _ ≤ t ^ ((∑ p ∈ s, N.factorization p) + 1) := Nat.pow_le_pow_right htpos hsum
        _ = t * t ^ (∑ p ∈ s, N.factorization p) := by rw [pow_succ, mul_comm]
        _ ≤ _ := Nat.mul_le_mul_left t hprod
    have hcut := rank_cut_product_bound hN ho s (Finset.ssubset_iff_subset_ne.mpr ⟨hs,hneS⟩) hne ht
    exact (Nat.mul_le_mul_left 2 hbound).trans_lt (by simpa only [← mul_assoc] using hcut)

end OddPerfect
