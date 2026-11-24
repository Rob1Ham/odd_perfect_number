module

public import OddPerfect.AcquaahKonyagin
public import OddPerfect.ExponentOneIndex
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction

/-- At Euler exponent one the prime-size inequality bounds the whole
integer cubically in its index. -/
theorem exponent_one_size_lt_twice_index_cube {N q m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hqm : ¬q ∣ m) (hform : N=q*m^2) :
    let i := sigma 1 (m^2)/q
    q<2*i ∧ m^2≤ i^2 ∧ N<2*i^3 := by
  have hqN : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq,hform ▸ dvd_mul_right _ _,hN.2.ne'⟩
  have hqo := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hqN)
  have hq3 : 3≤q := by have := hq.two_le; have := Nat.odd_iff.mp hqo; omega
  have hcube := prime_cube_lt_three_mul hN ho hqN
  have hcancel : q*q^2<q*(3*m^2) := by simpa only [hform,pow_succ q 2,mul_assoc,mul_comm,mul_left_comm] using hcube
  have hsq := Nat.lt_of_mul_lt_mul_left hcancel
  have hq2 : ¬q ∣ m^2 := fun h => hqm (hq.dvd_of_dvd_pow h)
  obtain ⟨i,hi,hl,hr,_⟩ := exists_component_index (e:=1) hN hq (by simpa using hform) hq2
  simp only [pow_one] at hl
  rw [sigma_one_apply_prime_pow hq] at hr
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,pow_one,zero_add] at hr
  rw [show 1+q=q+1 by omega] at hr
  have hqi : q<2*i := by
    have hmul : (2*q)*q < (2*q)*(2*i) := by
      calc (2*q)*q = 2*q^2 := by ring
           _ < 3*((q+1)*i) := by rw [hr]; omega
           _ = (3*(q+1))*i := by ring
           _ ≤ (4*q)*i := Nat.mul_le_mul_right _ (by omega)
           _ = _ := by ring
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hm2 : m^2 ≤ i^2 := by
    have h := Nat.mul_le_mul_right i (show q+1≤2*i by omega)
    rw [hr] at h
    nlinarith
  have hn : N<2*i^3 := by
    calc N=q*m^2 := hform
         _ ≤ q*i^2 := Nat.mul_le_mul_left _ hm2
         _ < (2*i)*i^2 := Nat.mul_lt_mul_of_pos_right hqi (Nat.pow_pos hi)
         _ = _ := by ring
  simpa only [hl,Nat.mul_div_cancel_left i hq.pos] using (show q<2*i ∧ m^2≤ i^2 ∧ N<2*i^3 from ⟨hqi,hm2,hn⟩)

/-- An absolute size estimate at once gives an Euler-exponent-one index
bound, without counting or searching possible cofactor primes. -/
theorem exponent_one_index_gt_of_size {N q m b : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hqm : ¬q ∣ m) (hform : N=q*m^2) (hsize : 2*b^3≤N) :
    b<sigma 1 (m^2)/q := by
  have hn := (exponent_one_size_lt_twice_index_cube hN ho hq hqm hform).2.2
  by_contra! hx
  exact hn.not_ge ((Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hx 3)).trans hsize)

end OddPerfect
