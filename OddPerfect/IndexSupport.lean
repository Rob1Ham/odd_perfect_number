module

public import OddPerfect.Reciprocal
public import OddPerfect.CyclotomicOrders
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- Each distinct prime contributes a factor at least two to the divisor count. -/
theorem two_pow_prime_count_le_divisor_count {n : ℕ} (hn : n ≠ 0) :
    2 ^ n.primeFactors.card ≤ n.divisors.card := by
  rw [Nat.card_divisors hn, ← Finset.prod_const]
  apply Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _)
  intro p h
  obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp h
  have := (hp.dvd_iff_one_le_factorization hn).mp hd
  omega

/-- Taking the part coprime to a prime base commutes with finite products. -/
theorem ordCompl_finset_prod (q : ℕ) (s : Finset ℕ) (f : ℕ → ℕ) :
    ordCompl[q] (∏ p ∈ s, f p) = ∏ p ∈ s, ordCompl[q] (f p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hp ih => rw [Finset.prod_insert hp, Finset.prod_insert hp, Nat.ordCompl_mul, ih]

private theorem cardFactors_finset_prod {s : Finset ℕ} (f : ℕ → ℕ)
    (h : ∀ p ∈ s, 0 < f p) : cardFactors (∏ p ∈ s, f p) = ∑ p ∈ s, cardFactors (f p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    have hpos (p : ℕ) (hp : p ∈ s) : 0 < f p := h p (Finset.mem_insert_of_mem hp)
    rw [Finset.prod_insert hx, Finset.sum_insert hx,
      cardFactors_mul (h x (Finset.mem_insert_self ..)).ne' (Finset.prod_pos hpos).ne', ih hpos]

/-- Outside the selected prime, every even-exponent source either contributes
an odd prime to the length, divides the index, or belongs to a set whose
cardinality is bounded by the prime factors of the index with multiplicity. -/
theorem exists_component_index_cover {N q a b i : ℕ} (ho : Odd N) (hq : Nat.Prime q)
    (hform : N = q^a*b) (hleft : sigma 1 b = q^a*i) (hright : sigma 1 (q^a)*i = 2*b) :
    ∃ B : Finset ℕ, 2^B.card ≤ i ∧ B.card ≤ cardFactors i ∧
      ∀ p ∈ N.primeFactors, p ≠ q → Even (N.factorization p) →
        p ∈ (a+1).primeFactors.erase 2 ∪ i.primeFactors ∪ B := by
  classical
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b (q^a))
  have hi : i ≠ 0 := by
    rintro rfl
    simp only [Nat.mul_zero] at hright
    have := hbo.pos
    omega
  let f := fun p : ℕ => sigma 1 (p ^ b.factorization p)
  let u := fun p : ℕ => ordCompl[q] (f p)
  let bad := b.primeFactors.filter (fun p => 1 < u p)
  have hprod : ∏ p ∈ b.primeFactors, u p = ordCompl[q] i := by
    change ∏ p ∈ b.primeFactors, ordCompl[q] (f p) = _
    rw [← ordCompl_finset_prod]
    have hf := (isMultiplicative_sigma (k := 1)).multiplicative_factorization _ hbo.pos.ne'
    change sigma 1 b = ∏ p ∈ b.primeFactors, f p at hf
    rw [← hf, hleft, Nat.ordCompl_self_pow_mul i a hq]
  have hupos (p : ℕ) (h : p ∈ b.primeFactors) : 0 < u p :=
    Nat.ordCompl_pos _ (sigma_pos _ _ (pow_ne_zero _ (Nat.prime_of_mem_primeFactors h).ne_zero)).ne'
  have hpowbad : 2 ^ bad.card ≤ i := by
    calc
      2 ^ bad.card = ∏ _p ∈ bad, 2 := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ bad, u p := Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _)
        (fun _ h => (Finset.mem_filter.mp h).2)
      _ ≤ ∏ p ∈ b.primeFactors, u p := Finset.prod_le_prod_of_subset_of_one_le
        (Finset.filter_subset _ _) (fun p hp _ => hupos p hp)
      _ = ordCompl[q] i := hprod
      _ ≤ i := Nat.ordCompl_le _ _
  have hbadle : bad.card ≤ cardFactors i := by
    have hparts := congrArg cardFactors (Nat.ordProj_mul_ordCompl_eq_self i q)
    rw [cardFactors_mul (pow_ne_zero _ hq.ne_zero) (Nat.ordCompl_pos q hi).ne'] at hparts
    calc
      bad.card = ∑ _p ∈ bad, 1 := by simp
      _ ≤ ∑ p ∈ bad, cardFactors (u p) := Finset.sum_le_sum
        (fun p hp => cardFactors_pos_iff_one_lt.mpr (Finset.mem_filter.mp hp).2)
      _ ≤ ∑ p ∈ b.primeFactors, cardFactors (u p) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
      _ = cardFactors (ordCompl[q] i) := by rw [← hprod, cardFactors_finset_prod u hupos]
      _ ≤ cardFactors i := by omega
  refine ⟨bad, hpowbad, hbadle, ?_⟩
  intro p hpN hpq hpEven
  simp only [Finset.mem_union]
  obtain ⟨hp, hpn, _⟩ := Nat.mem_primeFactors.mp hpN
  have hpnd : ¬ p ∣ q^a := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h))
  have hpb := (hp.dvd_mul.mp (hform ▸ hpn)).resolve_left hpnd
  have hpB := Nat.mem_primeFactors.mpr ⟨hp, hpb, hbo.pos.ne'⟩
  by_cases hbad : p ∈ bad
  · exact Or.inr hbad
  by_cases hpi : p ∣ i
  · exact Or.inl (Or.inr (Nat.mem_primeFactors.mpr ⟨hp, hpi, hi⟩))
  have hp2 : p ≠ 2 := fun h => ho.not_two_dvd_nat (h ▸ hpn)
  refine Or.inl (Or.inl (Finset.mem_erase.mpr ⟨hp2, Nat.mem_primeFactors.mpr ⟨hp, ?_, by omega⟩⟩))
  have hu1 : u p = 1 := by
    have hn : ¬ 1 < u p := fun h => hbad (Finset.mem_filter.mpr ⟨hpB, h⟩)
    have := hupos p hpB
    omega
  have hpure : f p = q ^ (f p).factorization q := by
    have h := Nat.ordProj_mul_ordCompl_eq_self (f p) q
    change q ^ (f p).factorization q * u p = f p at h
    simpa [hu1] using h.symm
  let e := b.factorization p
  have hback : p^e ∣ sigma 1 (q^a) :=
    ((hp.coprime_iff_not_dvd.mpr hpi).pow_left e).dvd_of_dvd_mul_right
      (hright ▸ (Nat.ordProj_dvd b p).trans (dvd_mul_left _ _))
  have hpos : 0 < e := (hp.dvd_iff_one_le_factorization hbo.pos.ne').mp hpb
  have heq : N.factorization p = e := by
    rw [hform, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) hbo.pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpnd, zero_add]
  have heven := Nat.even_iff.mp hpEven
  have hrec := reciprocal_component_length hp (hbo.of_dvd_nat hpb) hq hpos hpure hback
  exact (dvd_pow_self p (by omega : e-1 ≠ 0)).trans hrec

/-- The number of prime bases is controlled by the support of the selected
length and the size of the index. -/
theorem prime_count_le_length_support_add_index {N q a b i : ℕ} (hN : Nat.Perfect N)
    (ho : Odd N) (hq : Nat.Prime q) (hform : N = q^a*b) (hleft : sigma 1 b = q^a*i)
    (hright : sigma 1 (q^a)*i = 2*b) :
    N.primeFactors.card ≤ (a+1).primeFactors.card + 2 * Nat.log 2 i + 2 := by
  obtain ⟨B, hpow, _, hcover⟩ := exists_component_index_cover ho hq hform hleft hright
  have hBle := Nat.le_log_of_pow_le (by decide : 1 < 2) hpow
  have hi : i ≠ 0 := by have := Nat.pow_pos (by decide : 0 < 2) (n := B.card); omega
  have hile : i.primeFactors.card ≤ Nat.log 2 i := Nat.le_log_of_pow_le (by decide)
    ((two_pow_prime_count_le_divisor_count hi).trans (Nat.card_divisors_le_self i))
  obtain ⟨s, _, _, _, hoth⟩ := euler_exponents ho hN
  let L := (a+1).primeFactors.erase 2
  let T := L ∪ i.primeFactors ∪ B
  have hsub : N.primeFactors ⊆ insert q (insert s T) := by
    intro p hp
    rcases eq_or_ne p q with rfl | hpq
    · exact Finset.mem_insert_self ..
    rcases eq_or_ne p s with rfl | hps
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hcover p hp hpq (hoth p hps)))
  have hcard := Finset.card_le_card hsub
  have hqCard := Finset.card_insert_le q (insert s T)
  have hsCard := Finset.card_insert_le s T
  have huCard := Finset.card_union_le (L ∪ i.primeFactors) B
  have htCard := Finset.card_union_le L i.primeFactors
  have hlen : L.card ≤ (a+1).primeFactors.card := Finset.card_le_card (Finset.erase_subset ..)
  change (insert s T).card ≤ (L ∪ i.primeFactors ∪ B).card + 1 at hsCard
  omega

/-- Distinct primes in the selected length generate distinct divisors, each
counted by the primitive-order bound. -/
theorem two_pow_component_length_support_le_prime_count {N q a b : ℕ} (hN : Nat.Perfect N)
    (ho : Odd N) (hq : Nat.Prime q) (ha : 0 < a) (hform : N = q^a*b) (hqb : ¬ q ∣ b) :
    2 ^ (a+1).primeFactors.card ≤ N.primeFactors.card := by
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b (q^a))
  have hmem := Nat.mem_primeFactors.mpr ⟨hq, hform ▸ (dvd_pow_self q ha.ne').trans
    (dvd_mul_right _ _), hN.2.ne'⟩
  have hval : N.factorization q = a := by
    rw [hform, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) hbo.pos.ne',
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hqb, hq.factorization_pow,
      Finsupp.single_eq_same, add_zero]
  have hdiv := component_length_divisor_count hN ho hmem
  rw [hval] at hdiv
  exact (two_pow_prime_count_le_divisor_count (by omega : a+1 ≠ 0)).trans hdiv

/-- The number of primes of an odd perfect number is bounded explicitly by
the logarithm of any one of its component indices. -/
theorem prime_count_le_of_component_index {N q a b i : ℕ} (hN : Nat.Perfect N)
    (ho : Odd N) (hq : Nat.Prime q) (ha : 0 < a) (hform : N = q^a*b) (hqb : ¬ q ∣ b)
    (hleft : sigma 1 b = q^a*i) (hright : sigma 1 (q^a)*i = 2*b) :
    N.primeFactors.card ≤ 4 * Nat.log 2 i + 4 := by
  have hcov := prime_count_le_length_support_add_index hN ho hq hform hleft hright
  have hpow := two_pow_component_length_support_le_prime_count hN ho hq ha hform hqb
  have linear (t : ℕ) : 2*t ≤ 2^t := by
    cases t with
    | zero => decide
    | succ t => simpa only [pow_succ'] using Nat.mul_le_mul_left 2 (Nat.lt_two_pow_self (n := t))
  have := linear (a+1).primeFactors.card
  omega

end OddPerfect
