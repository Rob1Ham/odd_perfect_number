module

public import OddPerfect.GlobalAbundancyObstruction
public import OddPerfect.SixthPowerBounds
public import OddPerfect.SixthPowerFreeEuler

public section

namespace OddPerfect

open ArithmeticFunction

/-- The exponent of any prime component bounds the drop in the multiplicity of its index. -/
theorem componentIndex_cardFactors_add_exponent_le {N p : ℕ} (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) :
    cardFactors (componentIndex N p) + N.factorization p ≤ cardFactors N := by
  have he : N.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
  have hpow : 1 < ordProj[p] N := one_lt_pow₀ (Nat.prime_of_mem_primeFactors hp).one_lt he
  have hσ := cardFactors_pos_iff_one_lt.mpr (hpow.trans (self_lt_sigma_of_one_lt hpow))
  have hbalance := cardFactors_componentIndex_add_eq hN hp
  omega

/-- A prime sixth power supplies a six-factor drop at its own base. -/
theorem componentIndex_cardFactors_add_six_le_of_sixth_power {N p : ℕ} (hN : N.Perfect)
    (hp : p.Prime) (hd : p ^ 6 ∣ N) :
    cardFactors (componentIndex N p) + 6 ≤ cardFactors N := by
  have hm := Nat.mem_primeFactors.mpr
    ⟨hp, (dvd_pow_self p (by decide : 6 ≠ 0)).trans hd, hN.2.ne'⟩
  have he := (hp.pow_dvd_iff_le_factorization hN.2.ne').1 hd
  have hdrop := componentIndex_cardFactors_add_exponent_le hN hm
  omega

/-- Every odd perfect candidate has an index at least five prime factors below its total. -/
theorem exists_componentIndex_cardFactors_add_five_le {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 5 ≤ cardFactors N := by
  rcases sixth_power_or_large_support ho hN with ⟨p, hp, hd⟩ | ⟨_, hcount, _⟩
  · have hm := Nat.mem_primeFactors.mpr
      ⟨hp, (dvd_pow_self p (by decide : 6 ≠ 0)).trans hd, hN.2.ne'⟩
    have hdrop := componentIndex_cardFactors_add_six_le_of_sixth_power hN hp hd
    exact ⟨p, hm, by omega⟩
  · have h88 : 88 ≤ cardFactors N := by rw [cardFactors_apply]; omega
    obtain ⟨p, hp, hdrop, _⟩ :=
      exists_componentIndex_cardFactors_add_five_le_of_large_or_three_free ho hN (Or.inr h88)
    exact ⟨p, hp, hdrop⟩

/-- The candidate set previously bounded by `finite_of_all_componentIndex_near_full` is empty. -/
theorem all_componentIndex_near_full_eq_empty :
    {N : ℕ | Odd N ∧ N.Perfect ∧
      ∀ p ∈ N.primeFactors, cardFactors N < cardFactors (componentIndex N p) + 5} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro N ⟨ho, hN, hnear⟩
  obtain ⟨p, hp, hdrop⟩ := exists_componentIndex_cardFactors_add_five_le ho hN
  exact (hnear p hp).not_ge hdrop

/-- A six-factor drop is equivalent to a sixth power, or one of three divisor-sum counts
at exact exponents one, two, and four. The latter alternatives cover the sixth-power-free case. -/
theorem exists_componentIndex_cardFactors_add_six_le_iff {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    (∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 6 ≤ cardFactors N) ↔
      (∃ p : ℕ, p.Prime ∧ p ^ 6 ∣ N) ∨
      ∃ p ∈ N.primeFactors,
        (N.factorization p = 1 ∧ 6 ≤ cardFactors (sigma 1 (ordProj[p] N))) ∨
        (N.factorization p = 2 ∧ 5 ≤ cardFactors (sigma 1 (ordProj[p] N))) ∨
        (N.factorization p = 4 ∧ 3 ≤ cardFactors (sigma 1 (ordProj[p] N))) := by
  constructor
  · rintro ⟨p, hp, hdrop⟩
    by_cases h6 : ∃ r : ℕ, r.Prime ∧ r ^ 6 ∣ N
    · exact Or.inl h6
    have hfree : ∀ r : ℕ, r.Prime → ¬ r ^ 6 ∣ N := fun r hr hd => h6 ⟨r, hr, hd⟩
    obtain ⟨q, hq, _, heq, heven⟩ := euler_exponents ho hN
    have hbalance := cardFactors_componentIndex_add_eq hN hp
    refine Or.inr ⟨p, hp, ?_⟩
    by_cases hpq : p = q
    · subst p
      have h1 := sixth_power_free_euler_exponent_one ho hN hq heq hfree
      exact Or.inl ⟨h1, by omega⟩
    · have hprime := Nat.prime_of_mem_primeFactors hp
      have hlt := (hprime.pow_dvd_iff_le_factorization hN.2.ne').not.mp (hfree p hprime)
      have hpos : N.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
      obtain ⟨k, hk⟩ := heven p hpq
      omega
  · rintro (⟨p, hp, hd⟩ | ⟨p, hp, hcases⟩)
    · refine ⟨p, Nat.mem_primeFactors.mpr
        ⟨hp, (dvd_pow_self p (by decide : 6 ≠ 0)).trans hd, hN.2.ne'⟩, ?_⟩
      exact componentIndex_cardFactors_add_six_le_of_sixth_power hN hp hd
    · have hbalance := cardFactors_componentIndex_add_eq hN hp
      exact ⟨p, hp, by rcases hcases with h | h | h <;> omega⟩

/-- On the sparse side of the mod-five square-source bounds, the six-factor drop already holds. -/
theorem exists_componentIndex_cardFactors_add_six_le_of_few_square_sources {N : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hfew : ((squareSources N).filter (· % 5 = 1)).card < 92 ∨
      6 * ((squareSources N).filter (· % 5 = 1)).card ≤ N.primeFactors.card) :
    ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 6 ≤ cardFactors N := by
  apply (exists_componentIndex_cardFactors_add_six_le_iff ho hN).mpr
  left
  by_contra! hfree
  have hdensity := sixth_power_free_square_sources_one_mod_five ho hN hfree
  omega

end OddPerfect
