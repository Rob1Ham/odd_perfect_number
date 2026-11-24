module

public import OddPerfect.OchemIncidence
public import OddPerfect.Valuations

/-! Exponent counts and their linear combination in Ochem and Rao (2014), §3. -/

public section

namespace OddPerfect

open ArithmeticFunction

/-- The cardinality of square components congruent to one modulo 3 is bounded
by the exponent received at 3. This is inequality (4) in the paper. -/
theorem squareSourcesOne_card_le_three_exponent {N : ℕ} (hN : N.Perfect) :
    (squareSourcesOne N).card ≤ N.factorization 3 := by
  apply card_le_factorization_of_sigma_sources hN (by decide) (by decide)
  · exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  · intro q hq
    obtain ⟨hs, hmod⟩ := Finset.mem_filter.mp hq
    obtain ⟨hmem, _, htwo⟩ := Finset.mem_filter.mp hs
    rw [htwo, sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hmem)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]
    have hc : q ≡ 1 [MOD 3] := hmod
    exact Nat.dvd_of_mod_eq_zero (((Nat.ModEq.refl 1).add hc).add (hc.pow 2))

/-- The counting reduction for Theorem 1. The final hypothesis is the
incidence inequality from the last paragraph of §3. -/
theorem ochem_rao_cases_from_incidence {N p : ℕ} (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) (hp4 : p % 4 = 1) (he : N.factorization p % 4 = 1)
    (hev : ∀ q : ℕ, q ≠ p → Even (N.factorization q))
    (hinc : 2 * (squareSources N).card ≤ 1 + N.factorization p +
      3 * (squareSourcesOne N).card + (largeSources N p).card +
      ∑ q ∈ largeSources N p, N.factorization q) :
    (3 ∣ N → 18 * N.primeFactors.card + N.factorization 3 ≤ 7 * N.primeFactorsList.length + 33) ∧
    (¬ 3 ∣ N → 18 * N.primeFactors.card ≤ 7 * N.primeFactorsList.length + 15) := by
  let S := (N.primeFactors.erase p).erase 3
  have hpos {q : ℕ} (hq : q ∈ N.primeFactors) : 0 < N.factorization q :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hq)
  have hparts : S = squareSources N ∪ largeSources N p := by
    ext q
    simp only [S, Finset.mem_erase, squareSources, largeSources, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hq3, hqp, hq⟩
      obtain ⟨k, hk⟩ := hev q hqp
      have := hpos hq
      by_cases htwo : N.factorization q = 2
      · exact Or.inl ⟨hq, hq3, htwo⟩
      · exact Or.inr ⟨hq, hq3, hqp, by omega⟩
    · rintro (⟨hq, hq3, htwo⟩ | ⟨hq, hq3, hqp, _⟩)
      · exact ⟨hq3, fun h => by subst q; omega, hq⟩
      · exact ⟨hq3, hqp, hq⟩
  have hdis : Disjoint (squareSources N) (largeSources N p) := by
    apply Finset.disjoint_left.mpr
    intro q hs hl
    have htwo := (Finset.mem_filter.mp hs).2.2
    have hlarge := (Finset.mem_filter.mp hl).2.2.2
    omega
  have hcard : S.card = (squareSources N).card + (largeSources N p).card := by
    rw [hparts, Finset.card_union_of_disjoint hdis]
  have hsum : (∑ q ∈ S, N.factorization q) =
      2 * (squareSources N).card + ∑ q ∈ largeSources N p, N.factorization q := by
    rw [hparts, Finset.sum_union hdis]
    congr 1
    calc
      _ = ∑ _q ∈ squareSources N, (2 : ℕ) :=
        Finset.sum_congr rfl fun _ hq => (Finset.mem_filter.mp hq).2.2
      _ = _ := by simp [Nat.mul_comm]
  have hlarge : 4 * (largeSources N p).card ≤ ∑ q ∈ largeSources N p, N.factorization q := by
    calc
      _ = ∑ _q ∈ largeSources N p, (4 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun _ hq => (Finset.mem_filter.mp hq).2.2.2
  have htot : N.primeFactorsList.length =
      N.factorization p + ∑ q ∈ N.primeFactors.erase p, N.factorization q := by
    rw [← cardFactors_apply, cardFactors_eq_sum_factorization]
    exact (Finset.add_sum_erase N.primeFactors _ hp).symm
  have hpcount := Finset.card_erase_add_one hp
  have hbound := squareSourcesOne_card_le_three_exponent hN
  by_cases h3 : 3 ∈ N.primeFactors
  · have h3p : 3 ≠ p := by omega
    have h3mem := Finset.mem_erase.mpr ⟨h3p, h3⟩
    have h3card : S.card + 1 = (N.primeFactors.erase p).card := Finset.card_erase_add_one h3mem
    have h3sum : N.factorization 3 + (∑ q ∈ S, N.factorization q) =
        ∑ q ∈ N.primeFactors.erase p, N.factorization q :=
      Finset.add_sum_erase _ _ h3mem
    have := hpos h3
    obtain ⟨k, hk⟩ := hev 3 h3p
    exact ⟨fun _ => by omega, fun hd => (hd (Nat.dvd_of_mem_primeFactors h3)).elim⟩
  · have h3zero : N.factorization 3 = 0 := Finsupp.notMem_support_iff.mp h3
    have h3erase : S = N.primeFactors.erase p :=
      Finset.erase_eq_of_notMem fun h => h3 (Finset.mem_of_mem_erase h)
    rw [← h3erase] at htot hpcount
    exact ⟨fun hd => (h3 (Nat.mem_primeFactors.mpr ⟨by decide, hd, hN.2.ne'⟩)).elim,
      fun _ => by omega⟩

/-- Refined constants obtained by retaining the exact number of primes in
the two branches of the Ochem–Rao partition. -/
theorem ochem_rao_count_cases {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    (3 ∣ N → 18 * N.primeFactors.card + N.factorization 3 ≤ 7 * N.primeFactorsList.length + 33) ∧
    (¬ 3 ∣ N → 18 * N.primeFactors.card ≤ 7 * N.primeFactorsList.length + 15) := by
  obtain ⟨p, hp, hp4, he, hev⟩ := euler_exponents ho hN
  exact ochem_rao_cases_from_incidence hN hp hp4 he hev
    (ochem_rao_incidence ho hN hp hp4 he hev)

/-- Ochem and Rao (2014), Theorem 1, in integer form. -/
theorem ochem_rao_prime_factor_count {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    18 * N.primeFactors.card ≤ 7 * N.primeFactorsList.length + 31 := by
  obtain ⟨present, absent⟩ := ochem_rao_count_cases ho hN
  by_cases h3 : 3 ∣ N
  · have hge := (Nat.prime_three.dvd_iff_one_le_factorization ho.pos.ne').mp h3
    obtain ⟨p, _, hp4, _, he⟩ := euler_exponents ho hN
    obtain ⟨k, hk⟩ := he 3 (by omega)
    have := present h3
    omega
  · have := absent h3
    omega

end OddPerfect
