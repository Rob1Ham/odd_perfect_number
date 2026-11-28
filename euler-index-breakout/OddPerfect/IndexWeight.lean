module

public import OddPerfect.IndexSupport
public import OddPerfect.IndexTwo
public import OddPerfect.FewPrimes
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- Across an Euler component, the distinct and total numbers of prime factors
of its index bound the size of the support outside the Euler length. -/
theorem euler_prime_count_le_index_union {N q a b i : ℕ} (hN : Nat.Perfect N)
    (ho : Odd N) (hq : Nat.Prime q) (hao : Odd a) (hform : N = q^a*b) (hqb : ¬ q ∣ b)
    (hleft : sigma 1 b = q^a*i) (hright : sigma 1 (q^a)*i = 2*b) :
    N.primeFactors.card ≤ ((a+1).primeFactors.erase 2 ∪ i.primeFactors).card + cardFactors i + 1 := by
  classical
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b (q^a))
  have hval : N.factorization q = a := by
    rw [hform, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) hbo.pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hqb, hq.factorization_pow, Finsupp.single_eq_same, add_zero]
  obtain ⟨s, _, _, _, hoth⟩ := euler_exponents ho hN
  have hqs : q = s := by
    by_contra h
    have := Nat.even_iff.mp (hoth q h)
    have := Nat.odd_iff.mp hao
    omega
  subst s
  obtain ⟨B, _, hBle, hcover⟩ := exists_component_index_cover ho hq hform hleft hright
  let L := (a+1).primeFactors.erase 2
  let T := L ∪ i.primeFactors ∪ B
  have hsub : N.primeFactors ⊆ insert q T := by
    intro p hp
    rcases eq_or_ne p q with rfl | hpq
    · exact Finset.mem_insert_self ..
    exact Finset.mem_insert_of_mem (hcover p hp hpq (hoth p hpq))
  have hcard := Finset.card_le_card hsub
  have hqCard := Finset.card_insert_le q T
  have huCard := Finset.card_union_le (L ∪ i.primeFactors) B
  change (insert q T).card ≤ ((L ∪ i.primeFactors) ∪ B).card + 1 at hqCard
  change N.primeFactors.card ≤ (L ∪ i.primeFactors).card + cardFactors i + 1
  omega

/-- A cardinality-only form of the Euler support estimate. -/
theorem euler_prime_count_le_length_and_index_factors {N q a b i : ℕ} (hN : Nat.Perfect N)
    (ho : Odd N) (hq : Nat.Prime q) (hao : Odd a) (hform : N = q^a*b) (hqb : ¬ q ∣ b)
    (hleft : sigma 1 b = q^a*i) (hright : sigma 1 (q^a)*i = 2*b) :
    N.primeFactors.card ≤ (a+1).primeFactors.card + i.primeFactors.card + cardFactors i := by
  let L := (a+1).primeFactors.erase 2
  have h2mem : 2 ∈ (a+1).primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_two, by have := Nat.odd_iff.mp hao; omega, by omega⟩
  have hL : L.card + 1 = (a+1).primeFactors.card := Finset.card_erase_add_one h2mem
  have h := euler_prime_count_le_index_union hN ho hq hao hform hqb hleft hright
  have hCard := Finset.card_union_le L i.primeFactors
  change N.primeFactors.card ≤ (L ∪ i.primeFactors).card + cardFactors i + 1 at h
  omega

private theorem two_pow_exceeds_plus_two {n : ℕ} (hn : 3 ≤ n) : n + 2 < 2^n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n _ ih => rw [pow_succ]; omega

/-- Each component length has at least three fewer distinct prime factors
than the whole odd perfect number. -/
theorem component_length_support_add_three_le {N q a b : ℕ} (hN : Nat.Perfect N)
    (ho : Odd N) (hq : Nat.Prime q) (ha : 0 < a) (hform : N = q^a*b) (hqb : ¬ q ∣ b) :
    (a+1).primeFactors.card + 3 ≤ N.primeFactors.card := by
  by_cases h : 3 ≤ (a+1).primeFactors.card
  · exact (two_pow_exceeds_plus_two h).trans_le
      (two_pow_component_length_support_le_prime_count hN ho hq ha hform hqb)
  · have := five_le_distinct_prime_factor_count ho hN
    omega

/-- No exact prime-power component of an odd perfect number has prime index. -/
theorem component_index_not_prime {N q a b i : ℕ} (hN : Nat.Perfect N)
    (ho : Odd N) (hq : Nat.Prime q) (ha : 0 < a) (hform : N = q^a*b) (hqb : ¬ q ∣ b)
    (hleft : sigma 1 b = q^a*i) (hright : sigma 1 (q^a)*i = 2*b) : ¬ i.Prime := by
  intro hi
  rcases component_index_parity_bound hN ho hq ha hform hqb hleft hright with
    ⟨hao, _, _⟩ | ⟨_, hi4, hi6⟩
  · have hbound := euler_prime_count_le_length_and_index_factors hN ho hq hao hform hqb hleft hright
    rw [hi.primeFactors, Finset.card_singleton, cardFactors_apply_prime hi] at hbound
    have := component_length_support_add_three_le hN ho hq ha hform hqb
    omega
  · have htwo : 2 ∣ i := by omega
    have heq := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hi).mp htwo
    omega

/-- Every component index admits a proper prime divisor. -/
theorem exists_proper_prime_dvd_component_index {N q a : ℕ} (hN : Nat.Perfect N)
    (ho : Odd N) (hq : Nat.Prime q) (ha : 0 < a) (hd : q^a ∣ N) (hex : ¬ q^(a+1) ∣ N) :
    ∃ r : ℕ, r.Prime ∧ r ∣ sigma 1 (N / q^a) / q^a ∧ r < sigma 1 (N / q^a) / q^a := by
  obtain ⟨b, hb⟩ := hd
  have hqb : ¬ q ∣ b := by
    intro h
    apply hex
    rw [hb, pow_succ]
    exact Nat.mul_dvd_mul_left _ h
  obtain ⟨i, hi, hleft, hright, _⟩ := exists_component_index hN hq hb hqb
  have hcomp := component_index_not_prime hN ho hq ha hb hqb hleft hright
  have hi3 : 3 ≤ i := by
    rcases component_index_parity_bound hN ho hq ha hb hqb hleft hright with h | h
    · exact h.2.2
    · exact (by omega : 3 ≤ 6).trans h.2.2
  obtain ⟨r, hr, hri⟩ := Nat.exists_prime_and_dvd (by omega : i ≠ 1)
  rw [hb, Nat.mul_div_cancel_left b (Nat.pow_pos hq.pos), hleft,
    Nat.mul_div_cancel_left i (Nat.pow_pos hq.pos)]
  refine ⟨r, hr, hri, lt_of_le_of_ne (Nat.le_of_dvd hi hri) ?_⟩
  rintro rfl
  exact hcomp hr

end OddPerfect
