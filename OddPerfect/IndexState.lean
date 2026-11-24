module

public import OddPerfect.IndexComponent

/-! Numeric states and induction invariants for partial prime-power components. -/

public section

namespace OddPerfect.IndexComponent

open ArithmeticFunction

structure State where
  component : ℕ
  divisorSum : ℕ
  special : ℕ

@[expose] def root : State := ⟨1, 1, 0⟩

@[expose] def State.extend (s : State) (p e : ℕ) : State :=
  ⟨s.component*p^e, s.divisorSum*SupportSieve.geomValue p (e+1), if e = 1 then p else s.special⟩

@[expose] def State.joined (s : State) : ℕ := s.component.lcm (s.divisorSum/s.divisorSum.gcd 2)

/-- Length divisibility replaces exact valuation equality. A recorded special
prime has a genuinely odd valuation in the full number. -/
structure Valid (s : State) (N : ℕ) : Prop where
  divides : s.component ∣ N
  sigma : sigma 1 s.component = s.divisorSum
  lengths : ∀ p ∈ s.component.primeFactors, s.component.factorization p+1 ∣ N.factorization p+1
  special : s.special ≠ 0 → Odd (N.factorization s.special)

theorem root_valid (N : ℕ) : Valid root N := by constructor <;> simp [root]

theorem joined_dvd {s : State} {N : ℕ} (h : Valid s N) (hN : N.Perfect) : s.joined ∣ N := by
  rw [State.joined, ← h.sigma]
  exact lcm_dvd_of_component_lengths hN h.divides h.lengths

/-- Introducing a new base at any compatible positive exponent preserves the
accumulated divisor sum and all the previous length divisibilities. -/
theorem extend_valid {s : State} {N p e : ℕ} (h : Valid s N) (hN : N ≠ 0)
    (hp : p.Prime) (hnew : ¬ p ∣ s.component) (hi : e+1 ∣ N.factorization p+1) :
    Valid (s.extend p e) N := by
  have hd : s.component ≠ 0 := fun he => hN (zero_dvd_iff.mp (he ▸ h.divides))
  have hle : e ≤ N.factorization p := by have := Nat.le_of_dvd (Nat.succ_pos _) hi; omega
  have hpow := (hp.pow_dvd_iff_le_factorization hN).2 hle
  have hc := (hp.coprime_iff_not_dvd.mpr hnew).symm.pow_right e
  have hg : SupportSieve.geomValue p (e+1) = sigma 1 (p^e) := by
    rw [sigma_one_apply_prime_pow hp, SupportSieve.geomValue, ← geom_sum_mul_of_one_le hp.one_le,
      Nat.mul_div_cancel _ (by have := hp.one_lt; omega)]
  constructor
  · exact hc.mul_dvd_of_dvd_of_dvd h.divides hpow
  · change sigma 1 (s.component*p^e) = s.divisorSum * SupportSieve.geomValue p (e+1)
    rw [isMultiplicative_sigma.map_mul_of_coprime hc, h.sigma, hg]
  · intro q hq
    change (s.component*p^e).factorization q+1 ∣ N.factorization q+1
    rw [Nat.factorization_mul hd (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply]
    by_cases heq : q = p
    · subst q
      rwa [Nat.factorization_eq_zero_of_not_dvd hnew, Nat.factorization_pow_self hp, Nat.zero_add]
    · have hq' := Nat.prime_of_mem_primeFactors hq
      have hqp : ¬ q ∣ p^e := fun hdiv => heq ((Nat.prime_dvd_prime_iff_eq hq' hp).mp (hq'.dvd_of_dvd_pow hdiv))
      have hdiv : q ∣ s.component*p^e := Nat.dvd_of_mem_primeFactors hq
      rw [Nat.factorization_eq_zero_of_not_dvd hqp, Nat.add_zero]
      exact h.lengths q (Nat.mem_primeFactors.mpr ⟨hq', (hq'.dvd_mul.mp hdiv).resolve_right hqp, hd⟩)
  · by_cases he : e = 1
    · subst e
      simp only [State.extend, ↓reduceIte]
      intro _
      rw [Nat.odd_iff]
      omega
    · simpa [State.extend, he] using h.special

@[expose] def State.automatic (s : State) (avoid X : ℕ) : Bool :=
  decide (X < s.joined ∨ ¬ avoid.Coprime s.joined ∨ 4 ∣ s.divisorSum ∨ 2*s.component < s.divisorSum)

theorem automatic_false {s : State} {N avoid X : ℕ} (h : Valid s N) (ho : Odd N) (hN : N.Perfect)
    (hav : avoid.Coprime N) (hx : N ≤ X) (test : s.automatic avoid X = true) : False := by
  have hv := joined_dvd h hN
  rcases of_decide_eq_true test with hbig | hbad | hfour | hab
  · exact hbig.not_ge ((Nat.le_of_dvd hN.2 hv).trans hx)
  · exact hbad (hav.coprime_dvd_right hv)
  · have hs := sigma_dvd_of_component_lengths hN.2.ne' h.divides h.lengths
    rw [h.sigma, sigma_one_apply (n := N), (Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN] at hs
    have := hfour.trans hs
    have := ho.not_two_dvd_nat
    omega
  · have hAb : s.component.Abundant := by
      rwa [Nat.abundant_iff_sum_divisors, ← sigma_one_apply, h.sigma]
    exact (Nat.perfect_iff_not_abundant_and_not_deficient hN.2.ne).mp hN |>.1
      (hAb.of_dvd h.divides hN.2.ne')

end OddPerfect.IndexComponent
