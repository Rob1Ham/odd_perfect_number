module

public import OddPerfect.Spoof

/-! Three distinct ordinary sources congruent to one modulo three violate
the cube-free condition in a Descartes factorization. -/

public section

namespace DescartesSubmission

open ArithmeticFunction Finset

private theorem three_dvd_sigma_square {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    3 ∣ sigma 1 (p ^ 2) := by
  have h2 : p ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hmod]
  have hdiv : 3 ∣ 1 + p + p ^ 2 := by omega
  simpa [sigma_apply_prime_pow hp, sum_range_succ] using hdiv

/-- A cube-free Descartes factorization with exceptional square factor has at
most two ordinary source primes congruent to one modulo three when the
ordinary exponents are all two. -/
theorem capacity_of_exact {m w r : ℕ} (h : OddPerfect.SingleCompositeSpoof m w)
    (hw : w = r ^ 2) (hr : r.Prime)
    (hcf : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ m * w)
    (he : ∀ p ∈ m.primeFactors, m.factorization p = 2)
    {a b c : ℕ} (ha : a ∈ (m*w).primeFactors) (hb : b ∈ (m*w).primeFactors)
    (hc : c ∈ (m*w).primeFactors) (har : a ≠ r) (hbr : b ≠ r) (hcr : c ≠ r)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha3 : a % 3 = 1) (hb3 : b % 3 = 1) (hc3 : c % 3 = 1) : False := by
  have ordinary {p : ℕ} (hp : p ∈ (m*w).primeFactors) (hne : p ≠ r) :
      p ∈ m.primeFactors := by
    have hpp := Nat.prime_of_mem_primeFactors hp
    apply Nat.mem_primeFactors.mpr
    refine ⟨hpp, ?_, h.odd_left.pos.ne'⟩
    rcases hpp.dvd_mul.mp (Nat.dvd_of_mem_primeFactors hp) with hpm | hpw
    · exact hpm
    · rw [hw] at hpw
      exact (hne ((Nat.prime_dvd_prime_iff_eq hpp hr).mp (hpp.dvd_of_dvd_pow hpw))).elim
  have ham := ordinary ha har
  have hbm := ordinary hb hbr
  have hcm := ordinary hc hcr
  let f (p : ℕ) := sigma 1 (p ^ m.factorization p)
  have factor {p : ℕ} (hp : p ∈ m.primeFactors) (hmod : p % 3 = 1) : 3 ∣ f p := by
    simpa [f, he p hp] using three_dvd_sigma_square (Nat.prime_of_mem_primeFactors hp) hmod
  let T : Finset ℕ := {a, b, c}
  have hT : T ⊆ m.primeFactors := by
    intro p hp
    simp only [T, mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> assumption
  have h27 : 27 ∣ T.prod f := by
    have hprod := Nat.mul_dvd_mul (factor ham ha3) (Nat.mul_dvd_mul (factor hbm hb3) (factor hcm hc3))
    simpa [T, hab, hac, hbc] using hprod
  have hs : 27 ∣ sigma 1 m := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ h.odd_left.pos.ne']
    exact h27.trans (prod_dvd_prod_of_subset T m.primeFactors f hT)
  have htotal : 27 ∣ 2 * (m*w) := h.balance ▸ dvd_mul_of_dvd_left hs _
  exact hcf 3 (by decide) ((by decide : Nat.Coprime 27 2).dvd_of_dvd_mul_left htotal)

end DescartesSubmission
