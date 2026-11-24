module

public import OddPerfect.Reciprocal
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction

/-- A prime index can account for one missing return factor. When the index
divides the returning length, the full square root still divides that length. -/
theorem root_dvd_length_of_prime_index_return {v i q a β : ℕ} (hv : Odd v)
    (hi : Nat.Prime i) (hq : Nat.Prime q) (hiLen : i ∣ a + 1)
    (hout : sigma 1 (v ^ 2) = q ^ β) (hback : v ^ 2 ∣ i * sigma 1 (q ^ a)) :
    v ∣ a + 1 := by
  apply (Nat.factorization_le_iff_dvd hv.pos.ne' (by omega : a + 1 ≠ 0)).mp
  intro p
  by_cases hmem : p ∈ v.primeFactors
  · obtain ⟨hp, hpv, _⟩ := Nat.mem_primeFactors.mp hmem
    have hv2 : v ^ 2 ≠ 0 := pow_ne_zero _ hv.pos.ne'
    have hmem2 : p ∈ (v ^ 2).primeFactors := Nat.mem_primeFactors.mpr
      ⟨hp, hpv.trans (dvd_pow_self _ (by decide : 2 ≠ 0)), hv2⟩
    let l := (v ^ 2).factorization p
    have hl : l = 2 * v.factorization p := by simp [l, Nat.factorization_pow]
    have he : 0 < v.factorization p := (hp.dvd_iff_one_le_factorization hv.pos.ne').mp hpv
    have hpow : sigma 1 (p ^ l) ∣ q ^ β := by
      rw [← hout, isMultiplicative_sigma.multiplicative_factorization _ hv2]
      exact Finset.dvd_prod_of_mem _ hmem2
    obtain ⟨d, _, hd⟩ := (Nat.dvd_prime_pow hq).mp hpow
    have ht : p^l ∣ i * sigma 1 (q ^ a) := (Nat.ordProj_dvd (v ^ 2) p).trans hback
    obtain rfl | hpi := eq_or_ne p i
    · by_cases h1 : v.factorization p = 1
      · rw [h1]
        exact (hp.dvd_iff_one_le_factorization (by omega : a + 1 ≠ 0)).mp hiLen
      · have hpart : p^(l-1) ∣ sigma 1 (q ^ a) := by
          apply Nat.dvd_of_mul_dvd_mul_left hp.pos
          rwa [← pow_succ', show l - 1 + 1 = l by omega]
        have hret := reciprocal_return_length hp (hv.of_dvd_nat hpv) hq (by omega : 0 < l) hd hpart
        have hval := (hp.pow_dvd_iff_le_factorization (by omega : a + 1 ≠ 0)).mp hret
        omega
    · have hcop : (p ^ l).Coprime i :=
        (hp.coprime_iff_not_dvd.mpr (fun h => hpi ((Nat.prime_dvd_prime_iff_eq hp hi).mp h))).pow_left l
      have hret := reciprocal_component_length hp (hv.of_dvd_nat hpv) hq (by omega : 0 < l)
        hd (hcop.dvd_of_dvd_mul_left ht)
      have hval := (hp.pow_dvd_iff_le_factorization (by omega : a + 1 ≠ 0)).mp hret
      omega
  · rw [Finsupp.notMem_support_iff.mp hmem]
    exact Nat.zero_le _

end OddPerfect
