module

public import OddPerfect.DeficientReplay5.Part015
public import OddPerfect.DeficientReplay7.Part003
public import OddPerfect.DeficientReplay11.Part002
public import OddPerfect.DeficientReplay13.Part001
public import OddPerfect.DeficientReplay17.Part001
import Mathlib.Tactic.NormNum

public section

namespace OddPerfect
open DeficientSlots

/-- Sun–He and Yang–Togbé's four-prime classification, including the omitted divisor.
The cofactor and its four component exponents have no upper bounds. -/
theorem odd_deficientPerfect_four_iff {n d : ℕ} (ho : Odd n) (hc : n.primeFactors.card=4) :
    DeficientPerfectWith n d ↔ n=9018009 ∧ d=819 := by
  apply classification_of_covers _ ho hc
  intro p hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl
  · exact closedSecond5
  · exact closedSecond7
  · exact closedSecond11
  · exact closedSecond13
  · exact closedSecond17

/-- Classification of the odd deficient-perfect candidate set with at most four prime divisors. -/
theorem odd_deficientPerfect_four_set :
    {z : ℕ × ℕ | Odd z.1 ∧ z.1.primeFactors.card≤4 ∧ DeficientPerfectWith z.1 z.2}
      = {(9018009,819)} := by
  ext z
  obtain ⟨n,d⟩ := z
  simp only [Set.mem_ofPred_eq,Set.mem_singleton_iff,Prod.mk.injEq]
  constructor
  · rintro ⟨ho,hc,h⟩
    exact (odd_deficientPerfect_four_iff ho
      (le_antisymm hc (four_le_distinct_primes_of_odd_deficientPerfect ho h))).mp h
  · rintro ⟨rfl,rfl⟩
    have factors : (9018009:ℕ).primeFactors = {3,7,11,13} := by
      rw [show (9018009:ℕ) = 3^2 * (7^2 * (11^2 * 13^2)) by norm_num,
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_prime_pow (by decide) (by decide),
        Nat.primeFactors_prime_pow (by decide) (by decide),
        Nat.primeFactors_prime_pow (by decide) (by decide),
        Nat.primeFactors_prime_pow (by decide) (by decide)]
      decide
    exact ⟨⟨4509004, by norm_num⟩, by rw [factors]; decide, descartes_cofactor_deficientPerfect⟩

/-- The only nontrivial odd multiplier with a cofactor having at most four
distinct prime divisors is Descartes's composite multiplier. -/
theorem toth_odd_pair_four_iff {n x : ℕ} (hc : n.primeFactors.card≤4) (hx : Odd x) (h1 : 1<x) :
    TothPair n x ↔ n=9018009 ∧ x=22021 := by
  constructor
  · intro pair
    obtain ⟨d,t,h,ht,hx'⟩ := pair.deficientDivisor hx h1
    obtain ⟨rfl,rfl⟩ := (odd_deficientPerfect_four_iff pair.1
      (le_antisymm hc (pair.four_le_distinct_primes hx h1))).mp h
    exact ⟨rfl,by omega⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨descartes_singleCompositeSpoof.odd_left,by norm_num,descartes_singleCompositeSpoof.balance⟩

end OddPerfect
