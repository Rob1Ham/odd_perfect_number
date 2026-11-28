module

public import OddPerfect.Euler
public import Mathlib.NumberTheory.FactorisationProperties
import Mathlib.Algebra.Order.Ring.Abs

/-! Near-perfect numbers with one redundant proper divisor, in the sense of
Pollack and Shevelev. -/

public section

namespace OddPerfect

open ArithmeticFunction

/-- Retain the redundant divisor in the near-perfect equation. -/
def NearPerfectWith (n d : ℕ) : Prop :=
  d ∈ n.properDivisors ∧ sigma 1 n = 2 * n + d

/-- For an odd integer, parity of the actual divisor sum distinguishes squares. -/
theorem odd_sigma_iff_square_of_odd {n : ℕ} (hn : Odd n) : Odd (sigma 1 n) ↔ IsSquare n := by
  let f := fun p => sigma 1 (p ^ n.factorization p)
  have hprod : sigma 1 n = n.primeFactors.prod f :=
    isMultiplicative_sigma.multiplicative_factorization _ hn.pos.ne'
  have parity (p : ℕ) (hp : p ∈ n.primeFactors) : Odd (f p) ↔ Even (n.factorization p) := by
    have h := sigma_modEq_of_one (Nat.prime_of_mem_primeFactors hp)
      (show p ≡ 1 [MOD 2] from Nat.odd_iff.mp (hn.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)))
      (n.factorization p)
    change f p % 2 = _ at h
    rw [Nat.odd_iff, Nat.even_iff]
    omega
  rw [hprod, Nat.isSquare_iff_even_factorization]
  constructor
  · intro h p _
    by_cases hp : p ∈ n.primeFactors
    · exact (parity p hp).mp (h.of_dvd_nat (Finset.dvd_prod_of_mem f hp))
    · have hz : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
      simp [hz]
  · intro h
    exact Finset.prod_induction f Odd (fun _ _ => Odd.mul) (by decide : Odd 1)
      (fun p hp => (parity p hp).mpr (h p (Nat.prime_of_mem_primeFactors hp)))

/-- Omitting d gives exactly the sum formulation in the original definition. -/
theorem nearPerfectWith_iff_erase {n d : ℕ} : NearPerfectWith n d ↔
    d ∈ n.properDivisors ∧ ∑ i ∈ n.properDivisors.erase d, i = n := by
  unfold NearPerfectWith
  apply and_congr_right
  intro hd
  have h := Finset.add_sum_erase n.properDivisors (fun i => i) hd
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  omega

theorem NearPerfectWith.abundant {n d : ℕ} (h : NearPerfectWith n d) : n.Abundant := by
  have hd := Nat.pos_of_mem_properDivisors h.1
  rw [Nat.abundant_iff_sum_divisors, ← sigma_one_apply, h.2]
  omega

theorem NearPerfectWith.isSquare_of_odd {n d : ℕ} (h : NearPerfectWith n d) (ho : Odd n) :
    IsSquare n := by
  have hd := ho.of_dvd_nat (Nat.mem_properDivisors.mp h.1).1
  apply (odd_sigma_iff_square_of_odd ho).mp
  rw [h.2, Nat.odd_iff]
  have := Nat.odd_iff.mp hd
  omega

theorem odd_perfect_not_square {n : ℕ} (ho : Odd n) (hp : n.Perfect) : ¬ IsSquare n := by
  intro hs
  have h := (odd_sigma_iff_square_of_odd ho).mpr hs
  rw [sigma_one_apply, (Nat.perfect_iff_sum_divisors_eq_two_mul hp.2).mp hp, Nat.odd_iff] at h
  omega

/-- Donovan Johnson's odd near-perfect example, with its redundant divisor. -/
theorem johnson_nearPerfect : Odd 173369889 ∧ NearPerfectWith 173369889 2751903 := by
  refine ⟨by decide, Nat.mem_properDivisors.mpr ⟨by decide, by decide⟩, ?_⟩
  let bases : Finset ℕ := {3, 7, 11, 19}
  let component := fun p : ℕ => p ^ (if p = 3 then 4 else 2)
  have hpow : 173369889 = bases.prod component := by decide
  have hσ : sigma 1 (bases.prod component) = ∏ p ∈ bases, sigma 1 (component p) :=
    ArithmeticFunction.IsMultiplicative.map_prod component isMultiplicative_sigma bases
      (fun i hi j hj hij => ((Nat.coprime_primes
        ((by decide : ∀ p ∈ bases, p.Prime) i hi)
        ((by decide : ∀ p ∈ bases, p.Prime) j hj)).mpr hij).pow _ _)
  exact ((congrArg (sigma 1) hpow).trans hσ).trans (by decide +kernel)

end OddPerfect
