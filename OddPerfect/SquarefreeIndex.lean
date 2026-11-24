module

public import OddPerfect.FermatIndexSupport
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- Every squarefree Euler index has a prime divisor outside the Euler length. -/
theorem exists_index_prime_not_dvd_length_of_squarefree {N q a m i : ℕ}
    (hN : Nat.Perfect N) (ho : Odd N) (hq : q.Prime) (ha : Odd a)
    (hqm : ¬ q ∣ m) (hform : N=q^a*m^2) (hleft : sigma 1 (m^2)=q^a*i)
    (hright : sigma 1 (q^a)*i=2*m^2) (hio : Odd i) (hsq : Squarefree i) :
    ∃ p ∈ i.primeFactors, ¬ p ∣ a+1 := by
  by_contra! hin
  let L := (a+1).primeFactors.erase 2
  have his : i.primeFactors ⊆ L := by
    intro p hpi
    have hpo := hio.of_dvd_nat (Nat.dvd_of_mem_primeFactors hpi)
    exact Finset.mem_erase.mpr ⟨fun h => hpo.not_two_dvd_nat (h ▸ dvd_rfl),
      Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hpi, hin p hpi, by omega⟩⟩
  have hqb : ¬ q ∣ m^2 := fun h => hqm (hq.dvd_of_dvd_pow h)
  have hw := euler_prime_count_le_index_union hN ho hq ha hform hqb hleft hright
  change N.primeFactors.card ≤ (L ∪ i.primeFactors).card + cardFactors i + 1 at hw
  rw [Finset.union_eq_left.mpr his] at hw
  have hiCard := (cardDistinctFactors_eq_cardFactors_iff_squarefree hio.pos.ne').mpr hsq
  rw [cardDistinctFactors_eq_card_primeFactors] at hiCard
  have h2 : 2 ∈ (a+1).primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_two, by have := Nat.odd_iff.mp ha; omega, by omega⟩
  have hL : L.card+1 = (a+1).primeFactors.card := Finset.card_erase_add_one h2
  have hs := Finset.card_le_card his
  have hp := two_pow_component_length_support_le_prime_count hN ho hq ha.pos hform hqb
  have linear (t : ℕ) : 2*t ≤ 2^t := by
    induction t with
    | zero => decide
    | succ t ih => cases t with
                   | zero => decide
                   | succ t => rw [pow_succ]; omega
  have := linear (a+1).primeFactors.card
  omega

/-- A squarefree Euler index must contain a prime whose predecessor has an
odd prime divisor. In particular it cannot be supported only on Fermat primes. -/
theorem squarefree_euler_index_has_nonfermat_prime {N q a m i : ℕ}
    (hN : Nat.Perfect N) (ho : Odd N) (hq : q.Prime) (ha : Odd a)
    (hqm : ¬ q ∣ m) (hform : N=q^a*m^2) (hleft : sigma 1 (m^2)=q^a*i)
    (hright : sigma 1 (q^a)*i=2*m^2) (hio : Odd i) (hsq : Squarefree i) :
    ∃ p ∈ i.primeFactors, ∀ k : ℕ, p-1 ≠ 2^k := by
  by_contra! h
  have hcover := squarefree_fermat_index_support_dvd_length ho hq hform hleft hright hio hsq h
  obtain ⟨p, hp, hout⟩ := exists_index_prime_not_dvd_length_of_squarefree hN ho hq ha hqm hform hleft hright hio hsq
  exact hout (Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase (hcover hp)))

end OddPerfect
