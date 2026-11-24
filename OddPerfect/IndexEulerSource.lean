module

public import OddPerfect.IndexSieveBudget
import OddPerfect.DrisLuca
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect.IndexSieve

open ArithmeticFunction Finset

/-- At least one index prime sends to the Euler prime. Otherwise every
component above the support of the index would spend only the index, while
their product of divisor sums strictly exceeds the index itself. -/
theorem exists_euler_source_at_index_prime {q a m i : ℕ} (hq : q.Prime) (hm : 0<m)
    (hio : Odd i) (hi : 1< i) (hl : sigma 1 (m^2)=q^a*i) (hr : sigma 1 (q^a)*i=2*m^2) :
    ∃ p ∈ i.primeFactors, q ∣ sigma 1 (p^(2*m.factorization p)) := by
  have him : i ∣ m^2 := (Nat.coprime_two_right.mpr hio).dvd_of_dvd_mul_left (hr ▸ dvd_mul_left _ _)
  have hm2 := pow_ne_zero 2 hm.ne'
  have hsub := Nat.primeFactors_mono him hm2
  let f (p : ℕ) := sigma 1 (p^((m^2).factorization p))
  have hd : (∏ p ∈ i.primeFactors,f p) ∣ q^a*i := by
    rw [←hl,(isMultiplicative_sigma (k:=1)).multiplicative_factorization _ hm2]
    exact prod_dvd_prod_of_subset _ _ f hsub
  have hnonempty : i.primeFactors.Nonempty := by
    obtain ⟨p,hp,hpi⟩ := Nat.exists_prime_and_dvd hi.ne'
    exact ⟨p,Nat.mem_primeFactors.mpr ⟨hp,hpi,hio.pos.ne'⟩⟩
  have heach (p : ℕ) (hp : p ∈ i.primeFactors) : p^(i.factorization p) < f p := by
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpos := hpp.factorization_pos_of_dvd hm2 (Nat.dvd_of_mem_primeFactors (hsub hp))
    have hmono := (Nat.factorization_le_iff_dvd hio.pos.ne' hm2).mpr him p
    exact (Nat.pow_le_pow_right hpp.pos hmono).trans_lt
      (self_lt_sigma_of_one_lt (one_lt_pow₀ hpp.one_lt hpos.ne'))
  have hgt : i < ∏ p ∈ i.primeFactors, f p := by
    calc i = ∏ p ∈ i.primeFactors, p^(i.factorization p) := Nat.prod_primeFactors_pow_factorization hio.pos.ne'
         _ < _ := prod_lt_prod_of_nonempty₀ (fun p hp => Nat.pow_pos (Nat.prime_of_mem_primeFactors hp).pos)
           heach hnonempty
  have hqd : q ∣ ∏ p ∈ i.primeFactors, f p := by
    by_contra hn
    have hc := (hq.coprime_iff_not_dvd.mpr hn).pow_left a
    exact hgt.not_ge (Nat.le_of_dvd hio.pos (hc.symm.dvd_of_dvd_mul_left hd))
  obtain ⟨p,hp,hpout⟩ := (hq.prime.dvd_finsetProd_iff _).mp hqd
  exact ⟨p,hp,by simpa [f,Nat.factorization_pow] using hpout⟩

/-- The sum of the distinct and total prime counts of an index bounds half
the divisor count of the Euler length, with no upper bound on the index. -/
theorem half_length_divisors_le_index_weight {N q a m i : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (ha : Odd a) (hqm : ¬q ∣ m) (hform : N=q^a*m^2)
    (hl : sigma 1 (m^2)=q^a*i) (hr : sigma 1 (q^a)*i=2*m^2) :
    (a+1).divisors.card/2 ≤ i.primeFactors.card+cardFactors i := by
  let B := i.primeFactors.card+cardFactors i
  have hT : (B+1)+B < 2^(B+1) := by rw [pow_succ]; have := B.lt_two_pow_self; omega
  have hcount := euler_index_weight_bounds (B:=B) hN ho hq ha hqm hform hl hr (Nat.le_refl B) hT
  change _ ≤ B
  omega

/-- A finite set of possible Euler primes computed entirely from the index:
for every index prime, take the prime support of each possible component
sum after its part in the index has been removed. -/
@[expose] def eulerPrimeCandidates (i : ℕ) : Finset ℕ :=
  i.primeFactors.biUnion fun p =>
    (fullLengths i p (i.primeFactors.card+cardFactors i)).biUnion fun d =>
      (residual (repunit p d) i).primeFactors

/-- From the Euler-form input alone, the Euler prime belongs to the finite
set computed using its index. -/
theorem euler_prime_mem_candidates {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (ha4 : a%4=1) (hqm : ¬q ∣ m) (hform : N=q^a*m^2) :
    q ∈ eulerPrimeCandidates (sigma 1 (m^2)/q^a) := by
  have ha : Odd a := Nat.odd_iff.mpr (by omega)
  have hqb : ¬q ∣ m^2 := fun h => hqm (hq.dvd_of_dvd_pow h)
  obtain ⟨i,hpos,hl,hr,_⟩ := exists_component_index hN hq hform hqb
  have hi := component_index_gt_five hN ho hq ha.pos hform hqb hl hr
  have hio : Odd i := by
    rcases component_index_parity_bound hN ho hq ha.pos hform hqb hl hr with h|h
    · exact h.2.1
    · have := Nat.even_iff.mp h.1; have := Nat.odd_iff.mp ha; omega
  have hm := (ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2≠0)).trans (dvd_mul_left _ _))).pos
  have hqo := ho.of_dvd_nat (hform ▸ (dvd_pow_self q ha.pos.ne').trans (dvd_mul_right _ _))
  have hqi : ¬q ∣ i := fun h => hqm (hq.dvd_of_dvd_pow ((Nat.coprime_two_right.mpr hqo).dvd_of_dvd_mul_left
    (hr ▸ h.trans (dvd_mul_left _ _))))
  obtain ⟨p,hp,hps⟩ := exists_euler_source_at_index_prime hq hm hio (by omega) hl hr
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpi := Nat.dvd_of_mem_primeFactors hp
  have hpo := hio.of_dvd_nat hpi
  have hpm := hpp.dvd_of_dvd_pow ((Nat.coprime_two_right.mpr hpo).dvd_of_dvd_mul_left
    (hr ▸ hpi.trans (dvd_mul_left _ _)))
  have hH := half_length_divisors_le_index_weight hN ho hq ha hqm hform hl hr
  have hlen := actual_length_mem hq ha hm hio hpp hpo hpm hH hl hr
  rw [hl,Nat.mul_div_cancel_left _ (Nat.pow_pos hq.pos)]
  refine Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_biUnion.mpr ⟨_,hlen,?_⟩⟩
  rw [repunit_eq_sigma hpp]
  let b := sigma 1 (p^(2*m.factorization p))
  have hb : 0<b := sigma_pos 1 _ (pow_ne_zero _ hpp.ne_zero)
  have hg := Nat.mul_div_cancel' (Nat.gcd_dvd_left b i)
  have hd : q ∣ b.gcd i * residual b i := by simpa only [residual,hg] using hps
  have hnq : ¬q ∣ b.gcd i := fun h => hqi (h.trans (Nat.gcd_dvd_right _ _))
  exact Nat.mem_primeFactors.mpr ⟨hq,(hq.dvd_mul.mp hd).resolve_left hnq,
    (Nat.div_pos (Nat.le_of_dvd hb (Nat.gcd_dvd_left _ _)) (Nat.gcd_pos_of_pos_right b hpos)).ne'⟩

end OddPerfect.IndexSieve
