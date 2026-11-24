module

public import OddPerfect.DeficientPerfect
public import OddPerfect.SpoofBelowFive
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect
open Finset ArithmeticFunction

/-- The true components of the cofactor and the single formal multiplier
are a positive odd spoof list, including when the multiplier repeats a base. -/
theorem TothPair.four_le_distinct_primes {n x : ℕ} (h : TothPair n x) (hx : Odd x) (h1 : 1<x) :
    4 ≤ n.primeFactors.card := by
  let X := n.primeFactors.toList.map (fun p => (p,n.factorization p))
  have nodd : Odd n := h.1
  have hn := nodd.pos.ne'
  have hv : listValue X = n := by
    simp only [listValue,X,List.map_map,Finset.prod_map_toList]
    exact (Nat.prod_primeFactors_pow_factorization hn).symm
  have hs : listFormalSigma X = sigma 1 n := by
    simp only [listFormalSigma,X,List.map_map,Finset.prod_map_toList]
    apply Eq.trans _ (isMultiplicative_sigma.multiplicative_factorization _ hn).symm
    exact prod_congr rfl (fun p hp => (sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)).symm)
  have valid : ∀ z ∈ (x,1)::X, 1<z.1 ∧ Odd z.1 ∧ 0<z.2 := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl|hz
    · exact ⟨h1,hx,(by decide : 0<1)⟩
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hz
    have hm := Finset.mem_toList.mp hp
    have hd := Nat.dvd_of_mem_primeFactors hm
    have hpr := Nat.prime_of_mem_primeFactors hm
    exact ⟨hpr.one_lt,nodd.of_dvd_nat hd,hpr.factorization_pos_of_dvd hn hd⟩
  have balance : listFormalSigma ((x,1)::X)=2*listValue ((x,1)::X) := by
    change (∑ j ∈ range (1+1), x^j)*listFormalSigma X = 2*(x^1*listValue X)
    simpa [sum_range_succ,hv,hs,Nat.add_comm,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using h.2.2
  simpa [X] using five_le_positive_odd_spoof_length valid balance

/-- Tang and Feng's exclusion of odd deficient-perfect numbers with three
distinct prime divisors, together with the smaller support sizes. -/
theorem four_le_distinct_primes_of_odd_deficientPerfect {n d : ℕ}
    (ho : Odd n) (h : DeficientPerfectWith n d) : 4 ≤ n.primeFactors.card := by
  obtain ⟨x,hx,h1,hpair,_⟩ := h.tothPair ho
  exact hpair.four_le_distinct_primes hx h1

end OddPerfect
