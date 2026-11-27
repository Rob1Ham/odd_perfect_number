module

public import OddPerfect.DeficientPerfect
public import OddPerfect.SpoofFiniteness
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Basic.Finite.Prod

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- Append the linear formal base to the genuine prime components.  The
disjoint sum preserves the extra slot even if its base equals a prime of n. -/
theorem TothPair.radical_size_upper {n x k : ℕ} (h : TothPair n x) (hx : Odd x)
    (h1 : 1<x) (hk : n.primeFactors.card≤k) :
    (4*(k+1))*x^3*(n.primeFactors.prod id)^2*n ≤ (4*(k+1))^(4^(n.primeFactors.card+1)) := by
  let P := n.primeFactors.disjSum ({()} : Finset Unit)
  let b : ℕ ⊕ Unit → ℕ := Sum.elim id (fun _ => x)
  let e : ℕ ⊕ Unit → ℕ := Sum.elim n.factorization (fun _ => 1)
  have hn := h.1.pos.ne'
  have card : P.card = n.primeFactors.card+1 := by simp [P]
  have good (i) (hi : i∈P) : 1<b i ∧ Odd (b i) ∧ 0<e i := by
    cases i with
    | inl p =>
      have hm := inl_mem_disjSum.mp hi
      have dd := Nat.dvd_of_mem_primeFactors hm
      have pp := Nat.prime_of_mem_primeFactors hm
      exact ⟨pp.one_lt,h.1.of_dvd_nat dd,pp.factorization_pos_of_dvd hn dd⟩
    | inr u => exact ⟨h1,hx,(by decide : 0 < 1)⟩
  have sums : (∏ p ∈ n.primeFactors, ∑ j ∈ range (n.factorization p+1), p^j)=sigma 1 n := by
    apply Eq.trans _ (isMultiplicative_sigma.multiplicative_factorization _ hn).symm
    exact prod_congr rfl (fun p hp => (sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)).symm)
  have values := (Nat.prod_primeFactors_pow_factorization hn).symm
  have bal : formalSigma P b e = 2 * ∏ i ∈ P,b i^e i := by
    simp only [formalSigma,P,b,e,prod_disjSum,Sum.elim_inl,Sum.elim_inr,id_eq,
      prod_singleton,sums,values,pow_one]
    simpa [sum_range_succ,Nat.add_comm] using h.2.2
  have bound := formal_product_bound_of_bounded_factor_count P b e (k:=k+1)
    (by omega) (fun i hi => ⟨(good i hi).1,(good i hi).2.1⟩) (fun i hi => (good i hi).2.2) bal
  have trueLabels : (∏ p ∈ n.primeFactors,p^(n.factorization p+2)) =
      n*(n.primeFactors.prod id)^2 := by
    simp only [pow_add,prod_mul_distrib,Finset.prod_pow,values,id_eq]
  have labels : (∏ i ∈ P,b i^(e i+2)) = (n*(n.primeFactors.prod id)^2)*x^3 := by
    simp only [P,b,e,prod_disjSum,Sum.elim_inl,Sum.elim_inr,id_eq,prod_singleton]
    rw [trueLabels]
    rfl
  rw [card,labels] at bound
  simpa only [mul_comm,mul_assoc,mul_left_comm] using bound

/-- An explicit size bound when the number of distinct prime divisors is bounded. -/
theorem DeficientPerfectWith.le_of_bounded_prime_count {n d k : ℕ}
    (h : DeficientPerfectWith n d) (ho : Odd n) (hk : n.primeFactors.card≤k) :
    n ≤ (4*(k+1))^(4^(k+1)) := by
  obtain ⟨x,hx,h1,hpair,_⟩ := h.tothPair ho
  have hr : 0<n.primeFactors.prod id :=
    prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  have coeff : 0<(4*(k+1))*x^3*(n.primeFactors.prod id)^2 :=
    mul_pos (mul_pos (by omega) (pow_pos (by omega) _)) (pow_pos hr _)
  calc n ≤ ((4*(k+1))*x^3*(n.primeFactors.prod id)^2)*n := Nat.le_mul_of_pos_left n coeff
       _ ≤ _ := hpair.radical_size_upper hx h1 hk
       _ ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by decide) (by omega))

/-- Dutta–Saikia Conjecture 3.2, strengthened to at most k distinct primes
and with the deficient divisor recorded as a second coordinate. -/
theorem finite_odd_deficientPerfect_pairs_of_bounded_prime_count (k : ℕ) :
    Set.Finite {v : ℕ × ℕ | Odd v.1 ∧ v.1.primeFactors.card≤k ∧ DeficientPerfectWith v.1 v.2} := by
  let B := (4*(k+1))^(4^(k+1))
  apply ((Set.finite_le_nat B).prod (Set.finite_le_nat B)).subset
  rintro ⟨n,d⟩ ⟨ho,hk,h⟩
  have hn := h.le_of_bounded_prime_count ho hk
  exact ⟨hn,(Nat.mem_properDivisors.mp h.1).2.le.trans hn⟩

/-- The fixed-support conclusion also permits the divisor n itself as in
Dutta and Saikia's definition. The additional solution is (n,d)=(1,1). -/
theorem finite_odd_deficientPerfect_of_prime_count (k : ℕ) :
    Set.Finite {n : ℕ | Odd n ∧ n.primeFactors.card=k ∧
      ∃ d : ℕ, 0<d ∧ d∣n ∧ sigma 1 n+d=2*n} := by
  let B := (4*(k+1))^(4^(k+1))
  apply ((Set.finite_le_nat B).union (Set.finite_singleton 1)).subset
  rintro n ⟨ho,hk,d,_,hd,hs⟩
  by_cases small : d<n
  · exact Or.inl (DeficientPerfectWith.le_of_bounded_prime_count
      (show DeficientPerfectWith n d from ⟨Nat.mem_properDivisors.mpr ⟨hd,small⟩,hs⟩) ho hk.le)
  · have dn : d=n := le_antisymm (Nat.le_of_dvd ho.pos hd) (by omega)
    have val : sigma 1 n=n := by omega
    have pair : TothPair n 1 := ⟨ho,by decide,by simp [val,Nat.mul_comm]⟩
    exact Or.inr (Set.mem_singleton_iff.mpr (tothPair_one_iff.mp pair))

end OddPerfect
