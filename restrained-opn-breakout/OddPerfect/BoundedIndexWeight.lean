module

public import OddPerfect.BoundedIndex

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- Both the index support and its factors counted with multiplicity
control the support size, including at a non-Euler component. -/
theorem prime_count_le_of_component_index_factors {N q a b i : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (ha : 0<a) (hform : N=q^a*b) (hqb : ¬q ∣ b)
    (hl : sigma 1 b=q^a*i) (hr : sigma 1 (q^a)*i=2*b) :
    N.primeFactors.card≤2*(i.primeFactors.card+cardFactors i)+4 := by
  obtain ⟨B,_,hB,hcov⟩ := exists_component_index_cover ho hq hform hl hr
  obtain ⟨s,_,_,_,hother⟩ := euler_exponents ho hN
  let L := (a+1).primeFactors.erase 2
  let U := L ∪ i.primeFactors ∪ B
  have hsub : N.primeFactors ⊆ insert q (insert s U) := by
    intro p hp
    rcases eq_or_ne p q with rfl|hpq
    · exact Finset.mem_insert_self ..
    rcases eq_or_ne p s with rfl|hps
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hcov p hp hpq (hother p hps)))
  have hcard := Finset.card_le_card hsub
  have hqcard := Finset.card_insert_le q (insert s U)
  have hscard := Finset.card_insert_le s U
  have hu := Finset.card_union_le (L ∪ i.primeFactors) B
  have hL := Finset.card_union_le L i.primeFactors
  have hLc := Finset.card_le_card (Finset.erase_subset 2 (a+1).primeFactors)
  change (insert s U).card≤(L ∪ i.primeFactors ∪ B).card+1 at hscard
  change L.card≤(a+1).primeFactors.card at hLc
  have hpow := two_pow_component_length_support_le_prime_count hN ho hq ha hform hqb
  have hlin (t : ℕ) : 2*t ≤ 2^t := by
    cases t with
    | zero => decide
    | succ t => simpa only [pow_succ'] using Nat.mul_le_mul_left 2 (Nat.lt_two_pow_self (n:=t))
  have := hlin (a+1).primeFactors.card
  omega

/-- Only the number of prime factors of the index is bounded; their
values can vary freely. The bound supplied by Dickson is effective. -/
theorem le_of_bounded_component_index_factors {N q a K : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (ha : 0<a) (hd : q^a ∣ N) (hex : ¬q^(a+1) ∣ N)
    (hK : cardFactors (sigma 1 (N/q^a)/q^a) ≤ K) :
    let k := 4*K+4
    N ≤ (max 1 (productLabelBound (2*k) (2*k) 1))^k := by
  obtain ⟨b,hb⟩ := hd
  have hqb : ¬q ∣ b := fun h => hex (by rw [hb,pow_succ]; exact Nat.mul_dvd_mul_left _ h)
  obtain ⟨i,_,hl,hr,_⟩ := exists_component_index hN hq hb hqb
  rw [hb,Nat.mul_div_cancel_left b (Nat.pow_pos hq.pos),hl,Nat.mul_div_cancel_left i (Nat.pow_pos hq.pos)] at hK
  have h := prime_count_le_of_component_index_factors hN ho hq ha hb hqb hl hr
  have hdist : i.primeFactors.card≤cardFactors i := by
    rw [←cardDistinctFactors_eq_card_primeFactors,cardDistinctFactors_eq_length_dedup_primeFactorsList,cardFactors_apply]
    exact i.primeFactorsList.dedup_sublist.length_le
  exact le_of_bounded_prime_count ho hN (by omega : N.primeFactors.card≤4*K+4)

/-- For each factor-count budget only finitely many odd perfect numbers
can have even one exact component meeting that index budget. -/
theorem finite_of_bounded_component_index_factors (K : ℕ) :
    Set.Finite {N : ℕ | Odd N ∧ N.Perfect ∧ ∃ q a : ℕ, q.Prime ∧ 0<a ∧
      q^a ∣ N ∧ ¬q^(a+1) ∣ N ∧ cardFactors (sigma 1 (N/q^a)/q^a)≤K} := by
  let k := 4*K+4
  apply (Set.finite_le_nat ((max 1 (productLabelBound (2*k) (2*k) 1))^k)).subset
  rintro N ⟨ho,hN,q,a,hq,ha,hd,hex,hK⟩
  exact le_of_bounded_component_index_factors hN ho hq ha hd hex hK

end OddPerfect
