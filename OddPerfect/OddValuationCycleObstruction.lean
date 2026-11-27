module

public import OddPerfect.GlobalWave7Obstruction
public import OddPerfect.OddValuationGraph

/-!
# Odd-Valuation Cycle Obstruction on Sixth-Power-Free Odd Perfect Numbers

Formalizes:
1. `three_free_odd_sigma_cycle_or_euler_forty_eight`: On any `3`-free odd perfect number `N`,
   either `oddSigmaEdge N` has a directed cycle or the Euler prime `q` satisfies
   `N.factorization q = 1`, `q % 48 = 1`, `97 ≤ q`, and `IsSquare ((q + 1) / 2)`.
2. `sixth_power_free_min_prime_ge_53`: Every prime factor `r` of a sixth-power-free odd perfect
   number satisfies `53 ≤ r`.
3. `sixth_power_free_oddSigma_vacuum_and_routing`: On a sixth-power-free odd perfect number `N`,
   every prime `r ∈ S₅₀ ∪ Q₂₃` satisfies `oddSigmaSources N r = ∅` and admits no `oddSigmaEdge`
   cycle through `r`, while `oddSigmaEdge` out of `squareSources N` targets only `{q} ∪ Q₁₃` and
   `oddSigmaEdge` out of `largeSources N q` targets only `{q} ∪ S₅₁`.
4. `sixth_power_free_cycle_confinement_or_large_square_sink`: On a sixth-power-free odd perfect
   number `N`, every `oddSigmaEdge` cycle is confined to `insert q (S₅₁ ∪ Q₁₃)`, or else
   `N.factorization q = 1`, `q % 48 = 1`, `5617 ≤ q`, and `IsSquare ((q + 1) / 2)`.
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

private theorem sigma_one_prime_cyc {p : ℕ} (hp : p.Prime) : sigma 1 p = p + 1 := by
  rw [← pow_one p, sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

private theorem sigma_one_sq_cyc {p : ℕ} (hp : p.Prime) : sigma 1 (p ^ 2) = p ^ 2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

private theorem sigma_one_four_cyc {p : ℕ} (hp : p.Prime) :
    sigma 1 (p ^ 4) = p ^ 4 + p ^ 3 + p ^ 2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

private theorem sixth_power_free_cycle_invariants {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    ¬ 3 ∣ N ∧
    ¬ 5 ∣ N ∧
    N.factorization q = 1 ∧
    squareSourcesOne N = ∅ ∧
    (∀ s ∈ squareSources N, s.Prime ∧ s % 3 = 2 ∧ s ≠ 2 ∧ s ≠ 3 ∧ s ≠ 5 ∧ s ≠ q ∧
      N.factorization s = 2) ∧
    (∀ u ∈ largeSources N q, u.Prime ∧ u % 5 ≠ 1 ∧ u ≠ 2 ∧ u ≠ 3 ∧ u ≠ 5 ∧ u ≠ q ∧
      N.factorization u = 4) ∧
    N.primeFactors = insert q (squareSources N ∪ largeSources N q) ∧
    q ∉ squareSources N ∪ largeSources N q ∧
    Disjoint (squareSources N) (largeSources N q) := by
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have h5 : ¬ 5 ∣ N := sixth_power_free_five_not_dvd ho hN hfree
  have hq1 : N.factorization q = 1 := sixth_power_free_euler_exponent_one ho hN hq he hfree
  have hfour : ∀ r ∈ largeSources N q, N.factorization r = 4 :=
    (three_free_sixthPowerFree_forces_147_largeSources ho hN hq hq4 he hev h3 hfree).1
  have hS1_empty : squareSourcesOne N = ∅ := by
    have hb := squareSourcesOne_card_le_three_exponent hN
    have hz : N.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd h3
    exact Finset.card_eq_zero.mp (by omega)
  have hsq_prop : ∀ s ∈ squareSources N,
      s.Prime ∧ s % 3 = 2 ∧ s ≠ 2 ∧ s ≠ 3 ∧ s ≠ 5 ∧ s ≠ q ∧ N.factorization s = 2 := by
    intro s hs
    obtain ⟨hs_mem, hs_ne3, hs_exp⟩ := Finset.mem_filter.mp hs
    have hs_prime := Nat.prime_of_mem_primeFactors hs_mem
    have hs_dvd := Nat.dvd_of_mem_primeFactors hs_mem
    have hs_odd := ho.of_dvd_nat hs_dvd
    have hs_ne2 : s ≠ 2 := fun h => by subst s; exact (by decide : ¬ Odd 2) hs_odd
    have hs_ne5 : s ≠ 5 := fun h => h5 (h ▸ hs_dvd)
    have hs_neq : s ≠ q := fun h => by subst s; omega
    have hs_not1 : s % 3 ≠ 1 := by
      intro h1
      have hmem1 : s ∈ squareSourcesOne N := Finset.mem_filter.mpr ⟨hs, h1⟩
      simp [hS1_empty] at hmem1
    have hs_not0 : s % 3 ≠ 0 := fun h0 => h3 ((Nat.dvd_of_mod_eq_zero h0).trans hs_dvd)
    exact ⟨hs_prime, by omega, hs_ne2, hs_ne3, hs_ne5, hs_neq, hs_exp⟩
  have hlg_prop : ∀ u ∈ largeSources N q,
      u.Prime ∧ u % 5 ≠ 1 ∧ u ≠ 2 ∧ u ≠ 3 ∧ u ≠ 5 ∧ u ≠ q ∧ N.factorization u = 4 := by
    intro u hu
    obtain ⟨hu_mem, hu_ne3, hu_neq, _⟩ := Finset.mem_filter.mp hu
    have hu_exp := hfour u hu
    have hu_prime := Nat.prime_of_mem_primeFactors hu_mem
    have hu_dvd := Nat.dvd_of_mem_primeFactors hu_mem
    have hu_odd := ho.of_dvd_nat hu_dvd
    have hu_ne2 : u ≠ 2 := fun h => by subst u; exact (by decide : ¬ Odd 2) hu_odd
    have hu_ne5 : u ≠ 5 := fun h => h5 (h ▸ hu_dvd)
    have hu_not5 : u % 5 ≠ 1 := by
      intro hmod5
      have hmem5 : u ∈ quarticSourcesOne N q :=
        Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hu_neq, hu_mem⟩, hu_exp, hmod5⟩
      have hpos := Finset.card_pos.mpr ⟨u, hmem5⟩
      have hle := quarticSourcesOne_card_le_five_exponent (q := q) hN
      have hz : N.factorization 5 = 0 := Nat.factorization_eq_zero_of_not_dvd h5
      omega
    exact ⟨hu_prime, hu_not5, hu_ne2, hu_ne3, hu_ne5, hu_neq, hu_exp⟩
  have hparts : N.primeFactors = insert q (squareSources N ∪ largeSources N q) := by
    ext r
    simp only [Finset.mem_insert, Finset.mem_union, squareSources, largeSources, Finset.mem_filter]
    constructor
    · intro hr
      by_cases hrq : r = q
      · exact Or.inl hrq
      · right
        have hr_prime := Nat.prime_of_mem_primeFactors hr
        have hr3 : r ≠ 3 := fun h => h3 (h ▸ Nat.dvd_of_mem_primeFactors hr)
        have hr_pos : 0 < N.factorization r := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
        have hr_lt6 : ¬ 6 ≤ N.factorization r := fun hge =>
          hfree r hr_prime ((hr_prime.pow_dvd_iff_le_factorization hN.2.ne').2 hge)
        obtain ⟨k, hk⟩ := hev r hrq
        by_cases htwo : N.factorization r = 2
        · exact Or.inl ⟨hr, hr3, htwo⟩
        · exact Or.inr ⟨hr, hr3, hrq, by omega⟩
    · rintro (rfl | ⟨hr, _, _⟩ | ⟨hr, _, _, _⟩) <;> assumption
  have hq_notin : q ∉ squareSources N ∪ largeSources N q := by
    intro hmem
    rcases Finset.mem_union.mp hmem with hsq | hlg
    · have := (Finset.mem_filter.mp hsq).2.2
      omega
    · exact (Finset.mem_filter.mp hlg).2.2.1 rfl
  have hdisj : Disjoint (squareSources N) (largeSources N q) := by
    apply Finset.disjoint_left.mpr
    intro r hs hl
    have htwo := (Finset.mem_filter.mp hs).2.2
    have hlarge := (Finset.mem_filter.mp hl).2.2.2
    omega
  exact ⟨h3, h5, hq1, hS1_empty, hsq_prop, hlg_prop, hparts, hq_notin, hdisj⟩

/-- On any `3`-free odd perfect number `N`, either `oddSigmaEdge N` has a directed cycle or the
Euler prime `q` satisfies `N.factorization q = 1`, `q % 48 = 1`, `97 ≤ q`, and
`IsSquare ((q + 1) / 2)`. -/
theorem three_free_odd_sigma_cycle_or_euler_forty_eight {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) (h3 : ¬ 3 ∣ N) :
    (∃ p ∈ N.primeFactors, Relation.TransGen (oddSigmaEdge N) p p) ∨
    (∃ q ∈ N.primeFactors, N.factorization q = 1 ∧ q % 48 = 1 ∧ 97 ≤ q ∧ IsSquare ((q + 1) / 2)) := by
  rcases odd_sigma_cycle_or_exceptional_sink hN ho with hcyc | ⟨h34, _⟩ | ⟨q', hq', hq16, hqfac1, hsq⟩
  · exact Or.inl hcyc
  · exfalso
    rw [Nat.factorization_eq_zero_of_not_dvd h3] at h34
    omega
  · right
    obtain ⟨q, _, _, _, hev⟩ := euler_exponents ho hN
    have hqq : q' = q := by
      by_contra hne
      obtain ⟨k, hk⟩ := hev q' hne
      omega
    subst hqq
    have hq'4 : q' % 4 = 1 := by omega
    have hq'e4 : N.factorization q' % 4 = 1 := by omega
    obtain ⟨hq12, _⟩ := three_free_euler_prime_mod_twelve ho hN hq' hq'4 hq'e4 h3
    have hq48 : q' % 48 = 1 := by omega
    have hq_prime : q'.Prime := Nat.prime_of_mem_primeFactors hq'
    have hq97 : 97 ≤ q' := by
      by_contra! hlt
      have hcases : q' = 1 ∨ q' = 49 := by omega
      rcases hcases with rfl | rfl
      · exact (by decide : ¬ Nat.Prime 1) hq_prime
      · exact (by decide : ¬ Nat.Prime 49) hq_prime
    exact ⟨q', hq', hqfac1, hq48, hq97, hsq⟩

/-- Every prime factor `r` of a sixth-power-free odd perfect number satisfies `53 ≤ r`. -/
theorem sixth_power_free_min_prime_ge_53 {N r : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hr : r ∈ N.primeFactors) : 53 ≤ r := by
  by_contra! hlt
  obtain ⟨p, hp, hpow⟩ := prime_sixth_power_dvd_of_small_factor ho hN
    (Nat.prime_of_mem_primeFactors hr).two_le (Nat.dvd_of_mem_primeFactors hr) hlt
  exact hfree p hp hpow

/-- On a sixth-power-free odd perfect number `N`, every prime `r ∈ S₅₀ ∪ Q₂₃` has
`oddSigmaSources N r = ∅` and no directed `oddSigmaEdge` cycle through `r`, while
`oddSigmaEdge` out of `squareSources N` lands in `{q} ∪ Q₁₃` and `oddSigmaEdge` out of
`largeSources N q` lands in `{q} ∪ S₅₁`. -/
theorem sixth_power_free_oddSigma_vacuum_and_routing {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S₅₀ := (squareSources N).filter (· % 5 ≠ 1)
    let S₅₁ := (squareSources N).filter (· % 5 = 1)
    let Q₁₃ := oneModThreeLargeSources N q
    let Q₂₃ := twoModThreeLargeSources N q
    (∀ r ∈ S₅₀ ∪ Q₂₃, oddSigmaSources N r = ∅ ∧ ¬ Relation.TransGen (oddSigmaEdge N) r r) ∧
    (∀ s ∈ squareSources N, ∀ r, oddSigmaEdge N s r → r = q ∨ r ∈ Q₁₃) ∧
    (∀ u ∈ largeSources N q, ∀ r, oddSigmaEdge N u r → r = q ∨ r ∈ S₅₁) := by
  intro S₅₀ S₅₁ Q₁₃ Q₂₃
  obtain ⟨h3, _, hq1, _, hsq_prop, hlg_prop, hparts, _, _⟩ :=
    sixth_power_free_cycle_invariants ho hN hq hq4 he hev hfree
  have hvac := sixth_power_free_incoming_source_vacuum ho hN hq hq4 he hev hfree
  dsimp only at hvac
  obtain ⟨hvac_pt, _, _, _⟩ := hvac
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨hr_prime, _, _, _, _, _, hnot_sq, hnot_lg, _⟩ := hvac_pt r hr
    have hr_mem : r ∈ N.primeFactors := by
      rcases Finset.mem_union.mp hr with hrS | hrQ
      · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hrS).1).1
      · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hrQ).1).1
    have hr_neq : r ≠ q := by
      rcases Finset.mem_union.mp hr with hrS | hrQ
      · exact (hsq_prop r (Finset.mem_filter.mp hrS).1).2.2.2.2.2.1
      · exact (hlg_prop r (Finset.mem_filter.mp hrQ).1).2.2.2.2.2.1
    have hr_odd : Odd r := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr_mem)
    have hsub_q : oddSigmaSources N r ⊆ ({q} : Finset ℕ) := by
      intro p hp
      obtain ⟨hp_mem, hp_odd⟩ := Finset.mem_filter.mp hp
      have hr_dvd : r ∣ sigma 1 (p ^ N.factorization p) :=
        Nat.dvd_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hp_odd.pos.ne')
      rw [hparts] at hp_mem
      rcases Finset.mem_insert.mp hp_mem with rfl | hp_u
      · exact Finset.mem_singleton_self _
      · rcases Finset.mem_union.mp hp_u with hp_sq | hp_lg
        · rw [(hsq_prop p hp_sq).2.2.2.2.2.2] at hr_dvd
          exact absurd hr_dvd (hnot_sq p hp_sq)
        · rw [(hlg_prop p hp_lg).2.2.2.2.2.2] at hr_dvd
          exact absurd hr_dvd (hnot_lg p hp_lg)
    have hcard_le : (oddSigmaSources N r).card ≤ 1 :=
      (Finset.card_le_card hsub_q).trans_eq (Finset.card_singleton q)
    have heven_card : Even (oddSigmaSources N r).card :=
      (even_oddSigmaSources_iff hN hr_prime hr_odd).mpr (hev r hr_neq)
    have hcard_zero : (oddSigmaSources N r).card = 0 := by
      obtain ⟨k, hk⟩ := heven_card
      omega
    have hempty : oddSigmaSources N r = ∅ := Finset.card_eq_zero.mp hcard_zero
    refine ⟨hempty, ?_⟩
    intro hcyc
    have hex_in : ∃ p, oddSigmaEdge N p r := by
      cases hcyc with
      | single h1 => exact ⟨r, h1⟩
      | tail _ h2 => exact ⟨_, h2⟩
    obtain ⟨p, hp_edge⟩ := hex_in
    have hp_mem : p ∈ oddSigmaSources N r := Finset.mem_filter.mpr ⟨hp_edge.1, hp_edge.2.2⟩
    rw [hempty] at hp_mem
    exact Finset.notMem_empty p hp_mem
  · intro s hs r hsr
    by_cases hrq : r = q
    · exact Or.inl hrq
    · right
      have hr_mem : r ∈ N.primeFactors := hsr.2.1
      have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr_mem
      have hs_prime : s.Prime := (hsq_prop s hs).1
      have hs_exp : N.factorization s = 2 := (hsq_prop s hs).2.2.2.2.2.2
      have hr_dvd : r ∣ s ^ 2 + s + 1 := by
        have hd := Nat.dvd_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hsr.2.2.pos.ne')
        rwa [hs_exp, sigma_one_sq_cyc hs_prime] at hd
      have hr_ne3 : r ≠ 3 := fun h => h3 (h ▸ Nat.dvd_of_mem_primeFactors hr_mem)
      have hr_mod3 : r % 3 = 1 := (prime_dvd_sq_add_self_add_one hr_prime hr_dvd).resolve_left hr_ne3
      rw [hparts] at hr_mem
      rcases Finset.mem_insert.mp hr_mem with h_eq | hr_u
      · exact absurd h_eq hrq
      · rcases Finset.mem_union.mp hr_u with hr_sq | hr_lg
        · have hr_mod3_eq2 := (hsq_prop r hr_sq).2.1
          omega
        · exact Finset.mem_filter.mpr ⟨hr_lg, hr_mod3⟩
  · intro u hu r hur
    by_cases hrq : r = q
    · exact Or.inl hrq
    · right
      have hr_mem : r ∈ N.primeFactors := hur.2.1
      have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr_mem
      obtain ⟨hu_prime, hu5, hu2, _, _, _, hu_exp⟩ := hlg_prop u hu
      have hu_ge3 : 3 ≤ u := by
        have := hu_prime.two_le
        omega
      have hr_dvd : r ∣ normalizedQuarticSum u := by
        have hd := Nat.dvd_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hur.2.2.pos.ne')
        rw [hu_exp] at hd
        have hnorm_eq : normalizedQuarticSum u = sigma 1 (u ^ 4) := by
          rw [normalizedQuarticSum, ite_eq_right hu5, ← sigma_one_four_cyc hu_prime]
        exact hnorm_eq ▸ hd
      have hr_mod5 : r % 5 = 1 := (quartic_sigma_properties hu_prime hu_ge3).2.2.2 r hr_prime hr_dvd
      rw [hparts] at hr_mem
      rcases Finset.mem_insert.mp hr_mem with h_eq | hr_u
      · exact absurd h_eq hrq
      · rcases Finset.mem_union.mp hr_u with hr_sq | hr_lg
        · exact Finset.mem_filter.mpr ⟨hr_sq, hr_mod5⟩
        · exact absurd hr_mod5 (hlg_prop r hr_lg).2.1

/-- On a sixth-power-free odd perfect number `N`, every `oddSigmaEdge` cycle is confined to
`insert q (S₅₁ ∪ Q₁₃)`, or else `N.factorization q = 1`, `q % 48 = 1`, `5617 ≤ q`, and
`IsSquare ((q + 1) / 2)`. -/
theorem sixth_power_free_cycle_confinement_or_large_square_sink {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S₅₁ := (squareSources N).filter (· % 5 = 1)
    let Q₁₃ := oneModThreeLargeSources N q
    (∃ p ∈ insert q (S₅₁ ∪ Q₁₃), Relation.TransGen (oddSigmaEdge N) p p) ∨
    (N.factorization q = 1 ∧ q % 48 = 1 ∧ 5617 ≤ q ∧ IsSquare ((q + 1) / 2)) := by
  intro S₅₁ Q₁₃
  obtain ⟨h3, _, _, _, _, _, hparts, _, _⟩ :=
    sixth_power_free_cycle_invariants ho hN hq hq4 he hev hfree
  have hrout := sixth_power_free_oddSigma_vacuum_and_routing ho hN hq hq4 he hev hfree
  dsimp only at hrout
  obtain ⟨hvac, _, _⟩ := hrout
  rcases three_free_odd_sigma_cycle_or_euler_forty_eight ho hN h3 with
    ⟨p, hp_mem, hcyc⟩ | ⟨q', hq'_mem, hq'fac, hq'48, hq'97, hsq⟩
  · left
    refine ⟨p, ?_, hcyc⟩
    rw [hparts] at hp_mem
    rcases Finset.mem_insert.mp hp_mem with rfl | hp_u
    · exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      rcases Finset.mem_union.mp hp_u with hp_sq | hp_lg
      · by_cases hp5 : p % 5 = 1
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hp_sq, hp5⟩))
        · exfalso
          have hp_vac : p ∈ (squareSources N).filter (· % 5 ≠ 1) ∪ twoModThreeLargeSources N q :=
            Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hp_sq, hp5⟩))
          exact (hvac p hp_vac).2 hcyc
      · by_cases hp3 : p % 3 = 1
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hp_lg, hp3⟩))
        · exfalso
          have hp_vac : p ∈ (squareSources N).filter (· % 5 ≠ 1) ∪ twoModThreeLargeSources N q :=
            Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hp_lg, hp3⟩))
          exact (hvac p hp_vac).2 hcyc
  · right
    have hqq : q' = q := by
      by_contra hne
      obtain ⟨k, hk⟩ := hev q' hne
      omega
    subst hqq
    obtain ⟨y, hy⟩ := hsq
    have hy_ge7 : 7 ≤ y := by
      by_contra! hlt
      have : (q' + 1) / 2 ≥ 49 := by omega
      nlinarith
    set w := y.minFac
    have hw_prime : w.Prime := Nat.minFac_prime (by omega)
    have hw_dvd_y : w ∣ y := Nat.minFac_dvd y
    have hw_le_y : w ≤ y := Nat.le_of_dvd (by omega) hw_dvd_y
    have hw_dvd_half : w ∣ (q' + 1) / 2 := by
      rw [hy]
      exact hw_dvd_y.trans (dvd_mul_right y y)
    have hhalf_odd : Odd ((q' + 1) / 2) := Nat.odd_iff.mpr (by omega)
    have hw_odd : Odd w := hhalf_odd.of_dvd_nat hw_dvd_half
    have hq'_prime : q'.Prime := Nat.prime_of_mem_primeFactors hq'_mem
    have hnot_q2 : ¬ q' ^ 2 ∣ N := by
      rw [hq'_prime.pow_dvd_iff_le_factorization hN.2.ne']
      omega
    have hw_dvd_sig : w ∣ ∑ d ∈ (q' ^ 1).divisors, d := by
      rw [← sigma_one_apply, pow_one, sigma_one_prime_cyc hq'_prime]
      have hq'1_eq : q' + 1 = 2 * ((q' + 1) / 2) := by omega
      rw [hq'1_eq]
      exact hw_dvd_half.trans (dvd_mul_left _ _)
    have hw_dvd_N : w ∣ N :=
      dvd_perfect_of_exact_prime_pow hN hq'_prime
        (by simpa [pow_one] using Nat.dvd_of_mem_primeFactors hq'_mem)
        hnot_q2 hw_prime hw_odd hw_dvd_sig
    have hw_mem : w ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hw_prime, hw_dvd_N, hN.2.ne'⟩
    have hw_ge53 : 53 ≤ w := sixth_power_free_min_prime_ge_53 ho hN hfree hw_mem
    have hy_ge53 : 53 ≤ y := hw_ge53.trans hw_le_y
    have hhalf_ge : 2809 ≤ (q' + 1) / 2 := by
      rw [hy]
      nlinarith
    exact ⟨hq'fac, hq'48, by omega, ⟨y, hy⟩⟩

end OddPerfect
