module

public import OddPerfect.GlobalWave9Obstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sixth-Power-Free Prime–Composite Bipartite Split & No-Eight-Drop Pinch (`OddPerfect.SixthPowerFreePrimeCompositeSplit`)

Establishes the prime-vs-composite bipartite refinement on the active sixth-power-free cycle
classes `Q₁₃ := oneModThreeLargeSources N q` and `S₅₁ := (squareSources N).filter (· % 5 = 1)`:

1. `sixth_power_free_Q13_prime_and_S51_prime_injections`:
   - `Q₁₃_prime.card ≤ 1 + S₅₁_comp.card` (via the prime-to-composite chain
     `Φ₃(Φ₅(u))` being composite for `u ≥ 2`, `not_prime_sq_add_self_add_one_of_phi5`).
   - `S₅₁_prime.card ≤ 1 + Q₁₃.card` (via strict monotonicity of `s ↦ s^2 + s + 1` into
     `insert q Q₁₃`).
2. `sixth_power_free_prime_composite_bipartite_bound`:
   - `Q₁₃_prime.card + 3 * Q₁₃_comp.card + 2 * Q₂₃.card ≤ 2 * S₅₁.card + 2`
   - `3 * Q₁₃.card + 2 * Q₂₃.card + 2 * S₅₁_prime.card ≤ 4 * S₅₁.card + 4`
3. `sixth_power_free_no_eight_drop_pinch`:
   Under `∀ p ∈ N.primeFactors, cardFactors N < cardFactors (componentIndex N p) + 8`,
   - `Q₂₃.card ≤ 1 ∧ S₅₀.card ≤ 3 ∧ 2 * S₅₀.card + 4 * Q₂₃.card ≤ 6`
   - `147 ≤ Q₁₃.card ∧ 439 ≤ S₅₁.card + Q₁₃.card`
   - `∀ u ∈ Q₁₃, ¬ q ∣ sigma 1 (u ^ 4) → cardFactors (sigma 1 (u ^ 4)) = 1 ∨ cardFactors (sigma 1 (u ^ 4)) = 3`
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

private theorem sigma_one_sq_local {p : ℕ} (hp : p.Prime) : sigma 1 (p ^ 2) = p ^ 2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

private theorem sigma_one_four_local {p : ℕ} (hp : p.Prime) :
    sigma 1 (p ^ 4) = p ^ 4 + p ^ 3 + p ^ 2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

private theorem sigma_one_sq_inj_on_primes {a b : ℕ} (ha : a.Prime) (hb : b.Prime)
    (heq : sigma 1 (a ^ 2) = sigma 1 (b ^ 2)) : a = b := by
  rw [sigma_one_sq_local ha, sigma_one_sq_local hb] at heq
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · have h2 : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hlt (by decide)
    omega
  · rfl
  · have h2 : b ^ 2 < a ^ 2 := Nat.pow_lt_pow_left hgt (by decide)
    omega

private theorem sigma_one_four_inj_on_primes {a b : ℕ} (ha : a.Prime) (hb : b.Prime)
    (heq : sigma 1 (a ^ 4) = sigma 1 (b ^ 4)) : a = b := by
  rw [sigma_one_four_local ha, sigma_one_four_local hb] at heq
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · have h2 : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hlt (by decide)
    have h3 : a ^ 3 < b ^ 3 := Nat.pow_lt_pow_left hlt (by decide)
    have h4 : a ^ 4 < b ^ 4 := Nat.pow_lt_pow_left hlt (by decide)
    omega
  · rfl
  · have h2 : b ^ 2 < a ^ 2 := Nat.pow_lt_pow_left hgt (by decide)
    have h3 : b ^ 3 < a ^ 3 := Nat.pow_lt_pow_left hgt (by decide)
    have h4 : b ^ 4 < a ^ 4 := Nat.pow_lt_pow_left hgt (by decide)
    omega

/-- **Prime-to-Composite and Quadratic-to-Quartic Injections**: on a sixth-power-free odd perfect
number `N`,
1. `Q₁₃_prime` injects via `u ↦ sigma 1 (u ^ 4)` into `insert q S₅₁_comp` (since `Φ₃(Φ₅(u))` is
   composite for `2 ≤ u`), giving `Q₁₃_prime.card ≤ 1 + S₅₁_comp.card`;
2. `S₅₁_prime` injects via `s ↦ sigma 1 (s ^ 2)` into `insert q Q₁₃`, giving
   `S₅₁_prime.card ≤ 1 + Q₁₃.card`. -/
theorem sixth_power_free_Q13_prime_and_S51_prime_injections {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S := squareSources N
    let S₅₁ := S.filter (· % 5 = 1)
    let Q₁₃ := oneModThreeLargeSources N q
    let Q₁₃_prime := Q₁₃.filter (fun u => (sigma 1 (u ^ 4)).Prime)
    let S₅₁_prime := S₅₁.filter (fun s => (sigma 1 (s ^ 2)).Prime)
    let S₅₁_comp := S₅₁.filter (fun s => ¬ (sigma 1 (s ^ 2)).Prime)
    Q₁₃_prime.card ≤ 1 + S₅₁_comp.card ∧
    S₅₁_prime.card ≤ 1 + Q₁₃.card := by
  intro S S₅₁ Q₁₃ Q₁₃_prime S₅₁_prime S₅₁_comp
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have hq_prime := Nat.prime_of_mem_primeFactors hq
  have hS1_empty : squareSourcesOne N = ∅ := by
    have hb := squareSourcesOne_card_le_three_exponent hN
    have hz : N.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd h3
    exact Finset.card_eq_zero.mp (by omega)
  have hQ13_dich :=
    (sixth_power_free_quartic_cardFactors_mod_three_dichotomy ho hN hq hq4 he hev hfree).1
  constructor
  · have hinj : Q₁₃_prime.card ≤ (insert q S₅₁_comp).card := by
      refine Finset.card_le_card_of_injOn (fun u => sigma 1 (u ^ 4)) ?_ ?_
      · intro u hu
        obtain ⟨hu_Q13, hu_sig_prime⟩ := Finset.mem_filter.mp hu
        have hu_lg := (Finset.mem_filter.mp hu_Q13).1
        have hu_mem := (Finset.mem_filter.mp hu_lg).1
        have hu_prime := Nat.prime_of_mem_primeFactors hu_mem
        by_cases hwq : sigma 1 (u ^ 4) = q
        · dsimp only
          rw [hwq]
          exact Finset.mem_insert_self q S₅₁_comp
        · have hnq : ¬ q ∣ sigma 1 (u ^ 4) := by
            intro hdvd
            exact hwq ((Nat.dvd_prime hu_sig_prime).mp hdvd |>.resolve_left hq_prime.ne_one).symm
          have hw_prop := (hQ13_dich u hu_Q13 hnq).1
          have hw_mem : sigma 1 (u ^ 4) ∈ (sigma 1 (u ^ 4)).primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hu_sig_prime, dvd_rfl, hu_sig_prime.ne_zero⟩
          have hw_S51 : sigma 1 (u ^ 4) ∈ S₅₁ := (hw_prop (sigma 1 (u ^ 4)) hw_mem).1
          have hw_not_prime : ¬ (sigma 1 ((sigma 1 (u ^ 4)) ^ 2)).Prime := by
            rw [sigma_one_sq_local hu_sig_prime, sigma_one_four_local hu_prime]
            exact not_prime_sq_add_self_add_one_of_phi5 hu_prime.two_le
          exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hw_S51, hw_not_prime⟩)
      · intro u₁ hu₁ u₂ hu₂ heq
        have hu₁_prime := Nat.prime_of_mem_primeFactors
          (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hu₁).1).1).1
        have hu₂_prime := Nat.prime_of_mem_primeFactors
          (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hu₂).1).1).1
        exact sigma_one_four_inj_on_primes hu₁_prime hu₂_prime heq
    have hcard := Finset.card_insert_le q S₅₁_comp
    omega
  · have hinj : S₅₁_prime.card ≤ (insert q Q₁₃).card := by
      refine Finset.card_le_card_of_injOn (fun s => sigma 1 (s ^ 2)) ?_ ?_
      · intro s hs
        obtain ⟨hs_S51, hs_sig_prime⟩ := Finset.mem_filter.mp hs
        have hs_sq := (Finset.mem_filter.mp hs_S51).1
        obtain ⟨hs_mem, _, hs_exp⟩ := Finset.mem_filter.mp hs_sq
        have hs_prime := Nat.prime_of_mem_primeFactors hs_mem
        have hs_odd : Odd s := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hs_mem)
        have hw_odd : Odd (sigma 1 (s ^ 2)) := by
          rw [sigma_one_sq_local hs_prime]
          exact (hs_odd.pow.add_odd hs_odd).add_one
        have hw_N : sigma 1 (s ^ 2) ∣ N := by
          apply dvd_perfect_of_exact_prime_pow hN hs_prime (hs_exp ▸ Nat.ordProj_dvd N s)
            ((hs_prime.pow_dvd_iff_le_factorization hN.2.ne').not.mpr (by omega))
            hs_sig_prime hw_odd
          rw [← sigma_one_apply]
        by_cases hwq : sigma 1 (s ^ 2) = q
        · dsimp only
          rw [hwq]
          exact Finset.mem_insert_self q Q₁₃
        · have hw_mem : sigma 1 (s ^ 2) ∈ N.primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hs_sig_prime, hw_N, hN.2.ne'⟩
          have hw_ne3 : sigma 1 (s ^ 2) ≠ 3 := fun h => h3 (h ▸ hw_N)
          have hw_mod3 : sigma 1 (s ^ 2) % 3 = 1 := by
            have hdiv : sigma 1 (s ^ 2) ∣ s ^ 2 + s + 1 := by
              rw [sigma_one_sq_local hs_prime]
            rcases prime_dvd_sq_add_self_add_one hs_sig_prime hdiv with h3_eq | h1
            · exact (hw_ne3 h3_eq).elim
            · exact h1
          have hw_ge4 : 4 ≤ N.factorization (sigma 1 (s ^ 2)) := by
            obtain ⟨k, hk⟩ := hev (sigma 1 (s ^ 2)) hwq
            have hw_pos : 0 < N.factorization (sigma 1 (s ^ 2)) :=
              Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hw_mem)
            by_cases h2 : N.factorization (sigma 1 (s ^ 2)) = 2
            · exfalso
              have hmem1 : sigma 1 (s ^ 2) ∈ squareSourcesOne N :=
                Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hw_mem, hw_ne3, h2⟩, hw_mod3⟩
              simp [hS1_empty] at hmem1
            · omega
          have hw_lg : sigma 1 (s ^ 2) ∈ largeSources N q :=
            Finset.mem_filter.mpr ⟨hw_mem, hw_ne3, hwq, hw_ge4⟩
          exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hw_lg, hw_mod3⟩)
      · intro s₁ hs₁ s₂ hs₂ heq
        have hs₁_prime := Nat.prime_of_mem_primeFactors
          (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hs₁).1).1).1
        have hs₂_prime := Nat.prime_of_mem_primeFactors
          (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hs₂).1).1).1
        exact sigma_one_sq_inj_on_primes hs₁_prime hs₂_prime heq
    have hcard := Finset.card_insert_le q Q₁₃
    omega

/-- **Prime–Composite Bipartite Capacity Refinement**: on any sixth-power-free odd perfect number
`N`,
1. `Q₁₃_prime.card + 3 * Q₁₃_comp.card + 2 * Q₂₃.card ≤ 2 * S₅₁.card + 2`
2. `3 * Q₁₃.card + 2 * Q₂₃.card + 2 * S₅₁_prime.card ≤ 4 * S₅₁.card + 4` -/
theorem sixth_power_free_prime_composite_bipartite_bound {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S := squareSources N
    let S₅₁ := S.filter (· % 5 = 1)
    let Q₁₃ := oneModThreeLargeSources N q
    let Q₂₃ := twoModThreeLargeSources N q
    let Q₁₃_prime := Q₁₃.filter (fun u => (sigma 1 (u ^ 4)).Prime)
    let Q₁₃_comp := Q₁₃.filter (fun u => ¬ (sigma 1 (u ^ 4)).Prime)
    let S₅₁_prime := S₅₁.filter (fun s => (sigma 1 (s ^ 2)).Prime)
    Q₁₃_prime.card + 3 * Q₁₃_comp.card + 2 * Q₂₃.card ≤ 2 * S₅₁.card + 2 ∧
    3 * Q₁₃.card + 2 * Q₂₃.card + 2 * S₅₁_prime.card ≤ 4 * S₅₁.card + 4 := by
  intro S S₅₁ Q₁₃ Q₂₃ Q₁₃_prime Q₁₃_comp S₅₁_prime
  let S₅₁_comp := S₅₁.filter (fun s => ¬ (sigma 1 (s ^ 2)).Prime)
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have hq1 : N.factorization q = 1 := sixth_power_free_euler_exponent_one ho hN hq he hfree
  have hfour : ∀ r ∈ largeSources N q, N.factorization r = 4 :=
    (three_free_sixthPowerFree_forces_147_largeSources ho hN hq hq4 he hev h3 hfree).1
  have hq_prime := Nat.prime_of_mem_primeFactors hq
  have hq_odd : Odd q := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)
  obtain ⟨hQ13_dich, hQ23_dich⟩ :=
    sixth_power_free_quartic_cardFactors_mod_three_dichotomy ho hN hq hq4 he hev hfree
  have hid1 :=
    (sixth_power_free_bipartite_multiplicity_identities ho hN hq hq4 he hev hfree).1
  change (∑ u ∈ largeSources N q, cardFactors (sigma 1 (u ^ 4))) +
      (∑ p ∈ S₅₁, ((q + 1) / 2).factorization p) =
      2 * S₅₁.card + ∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization q at hid1
  have hq_sum_le1 : ∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization q ≤ 1 := by
    have hsum := factorization_eq_sum_sigma_factorizations hN hq_odd hq_prime
    have hsub : largeSources N q ⊆ N.primeFactors := Finset.filter_subset _ _
    have hle1 :
        ∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization q ≤
          ∑ r ∈ largeSources N q, (sigma 1 (r ^ N.factorization r)).factorization q := by
      refine Finset.sum_le_sum fun u hu => ?_
      rw [hfour u hu]
    have hle2 :
        ∑ r ∈ largeSources N q, (sigma 1 (r ^ N.factorization r)).factorization q ≤
          ∑ r ∈ N.primeFactors, (sigma 1 (r ^ N.factorization r)).factorization q :=
      Finset.sum_le_sum_of_subset hsub
    omega
  have htotal_upper : ∑ u ∈ largeSources N q, cardFactors (sigma 1 (u ^ 4)) ≤ 2 * S₅₁.card + 1 := by
    omega
  have hQ_parts : largeSources N q = Q₁₃ ∪ Q₂₃ := by
    ext r
    simp only [Q₁₃, Q₂₃, oneModThreeLargeSources, twoModThreeLargeSources,
      Finset.mem_union, Finset.mem_filter]
    by_cases h : r % 3 = 1 <;> tauto
  have hQ_disj : Disjoint Q₁₃ Q₂₃ := by
    apply Finset.disjoint_left.mpr
    intro r h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hQ13_parts : Q₁₃ = Q₁₃_prime ∪ Q₁₃_comp := by
    ext u
    simp only [Q₁₃_prime, Q₁₃_comp, Finset.mem_union, Finset.mem_filter]
    by_cases h : (sigma 1 (u ^ 4)).Prime <;> tauto
  have hQ13_disj : Disjoint Q₁₃_prime Q₁₃_comp := by
    apply Finset.disjoint_left.mpr
    intro u h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hQ13_card : Q₁₃.card = Q₁₃_prime.card + Q₁₃_comp.card := by
    rw [hQ13_parts, Finset.card_union_of_disjoint hQ13_disj]
  have hS51_parts : S₅₁ = S₅₁_prime ∪ S₅₁_comp := by
    ext s
    simp only [S₅₁_prime, S₅₁_comp, Finset.mem_union, Finset.mem_filter]
    by_cases h : (sigma 1 (s ^ 2)).Prime <;> tauto
  have hS51_disj : Disjoint S₅₁_prime S₅₁_comp := by
    apply Finset.disjoint_left.mpr
    intro s h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hS51_card : S₅₁.card = S₅₁_prime.card + S₅₁_comp.card := by
    rw [hS51_parts, Finset.card_union_of_disjoint hS51_disj]
  let Q₁₃_comp_q := Q₁₃_comp.filter (fun u => q ∣ sigma 1 (u ^ 4))
  let Q₁₃_comp_nq := Q₁₃_comp.filter (fun u => ¬ q ∣ sigma 1 (u ^ 4))
  have hQ13_comp_parts : Q₁₃_comp = Q₁₃_comp_q ∪ Q₁₃_comp_nq := by
    ext u
    simp only [Q₁₃_comp_q, Q₁₃_comp_nq, Finset.mem_union, Finset.mem_filter]
    by_cases h : q ∣ sigma 1 (u ^ 4) <;> tauto
  have hQ13_comp_disj : Disjoint Q₁₃_comp_q Q₁₃_comp_nq := by
    apply Finset.disjoint_left.mpr
    intro u h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hQ13_comp_card : Q₁₃_comp.card = Q₁₃_comp_q.card + Q₁₃_comp_nq.card := by
    rw [hQ13_comp_parts, Finset.card_union_of_disjoint hQ13_comp_disj]
  have hQ13_comp_q_le1 : Q₁₃_comp_q.card ≤ 1 := by
    have hle : Q₁₃_comp_q.card ≤ N.factorization q := by
      apply card_le_factorization_of_sigma_sources hN hq_odd hq_prime Q₁₃_comp_q
      · exact (Finset.filter_subset _ _).trans
          ((Finset.filter_subset _ _).trans
            ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _)))
      · intro u hu
        obtain ⟨hu_comp, hu_q⟩ := Finset.mem_filter.mp hu
        have hu_Q13 := (Finset.mem_filter.mp hu_comp).1
        have hu_lg := (Finset.mem_filter.mp hu_Q13).1
        rw [hfour u hu_lg]
        exact hu_q
    omega
  have hsum_split :
      (∑ u ∈ largeSources N q, cardFactors (sigma 1 (u ^ 4))) =
        (∑ u ∈ Q₁₃_prime, cardFactors (sigma 1 (u ^ 4))) +
          (∑ u ∈ Q₁₃_comp_q, cardFactors (sigma 1 (u ^ 4))) +
          (∑ u ∈ Q₁₃_comp_nq, cardFactors (sigma 1 (u ^ 4))) +
          ∑ u ∈ Q₂₃, cardFactors (sigma 1 (u ^ 4)) := by
    rw [hQ_parts, Finset.sum_union hQ_disj,
      hQ13_parts, Finset.sum_union hQ13_disj,
      hQ13_comp_parts, Finset.sum_union hQ13_comp_disj]
    ring
  have hlb_prime : Q₁₃_prime.card ≤ ∑ u ∈ Q₁₃_prime, cardFactors (sigma 1 (u ^ 4)) := by
    calc
      Q₁₃_prime.card = ∑ _u ∈ Q₁₃_prime, 1 := by simp [Finset.sum_const]
      _ ≤ ∑ u ∈ Q₁₃_prime, cardFactors (sigma 1 (u ^ 4)) := by
            refine Finset.sum_le_sum fun u hu => ?_
            rw [cardFactors_apply_prime (Finset.mem_filter.mp hu).2]
  have hlb_comp_q :
      2 * Q₁₃_comp_q.card ≤ ∑ u ∈ Q₁₃_comp_q, cardFactors (sigma 1 (u ^ 4)) := by
    calc
      2 * Q₁₃_comp_q.card = ∑ _u ∈ Q₁₃_comp_q, 2 := by simp [Finset.sum_const, Nat.mul_comm]
      _ ≤ ∑ u ∈ Q₁₃_comp_q, cardFactors (sigma 1 (u ^ 4)) := by
            refine Finset.sum_le_sum fun u hu => ?_
            obtain ⟨hu_comp, _⟩ := Finset.mem_filter.mp hu
            obtain ⟨hu_Q13, hu_not_prime⟩ := Finset.mem_filter.mp hu_comp
            have hu_lg := (Finset.mem_filter.mp hu_Q13).1
            have hu_prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hu_lg).1
            have hsig_gt1 : 1 < sigma 1 (u ^ 4) := by
              rw [sigma_one_four_local hu_prime]
              have := hu_prime.two_le
              omega
            have hpos : 0 < cardFactors (sigma 1 (u ^ 4)) :=
              cardFactors_pos_iff_one_lt.mpr hsig_gt1
            have hne1 : cardFactors (sigma 1 (u ^ 4)) ≠ 1 := fun h1 =>
              hu_not_prime (cardFactors_eq_one_iff_prime.mp h1)
            omega
  have hlb_comp_nq :
      3 * Q₁₃_comp_nq.card ≤ ∑ u ∈ Q₁₃_comp_nq, cardFactors (sigma 1 (u ^ 4)) := by
    calc
      3 * Q₁₃_comp_nq.card = ∑ _u ∈ Q₁₃_comp_nq, 3 := by simp [Finset.sum_const, Nat.mul_comm]
      _ ≤ ∑ u ∈ Q₁₃_comp_nq, cardFactors (sigma 1 (u ^ 4)) := by
            refine Finset.sum_le_sum fun u hu => ?_
            obtain ⟨hu_comp, hu_nq⟩ := Finset.mem_filter.mp hu
            obtain ⟨hu_Q13, hu_not_prime⟩ := Finset.mem_filter.mp hu_comp
            exact (hQ13_dich u hu_Q13 hu_nq).2.2.resolve_left hu_not_prime
  have hlb_Q23 : 2 * Q₂₃.card ≤ ∑ u ∈ Q₂₃, cardFactors (sigma 1 (u ^ 4)) := by
    calc
      2 * Q₂₃.card = ∑ _u ∈ Q₂₃, 2 := by simp [Finset.sum_const, Nat.mul_comm]
      _ ≤ ∑ u ∈ Q₂₃, cardFactors (sigma 1 (u ^ 4)) := by
            refine Finset.sum_le_sum fun u hu => (hQ23_dich u hu).2.2.2.2
  have hmain : Q₁₃_prime.card + 3 * Q₁₃_comp.card + 2 * Q₂₃.card ≤ 2 * S₅₁.card + 2 := by
    omega
  obtain ⟨hinj1, _⟩ :=
    sixth_power_free_Q13_prime_and_S51_prime_injections ho hN hq hq4 he hev hfree
  change Q₁₃_prime.card ≤ 1 + S₅₁_comp.card at hinj1
  exact ⟨hmain, by omega⟩

/-- **Sixth-Power-Free No-Eight-Drop Pinch**: on a sixth-power-free odd perfect number `N`
lacking an eight-factor component-index drop,
1. `Q₂₃.card ≤ 1 ∧ S₅₀.card ≤ 3 ∧ 2 * S₅₀.card + 4 * Q₂₃.card ≤ 6`
2. `147 ≤ Q₁₃.card ∧ 439 ≤ S₅₁.card + Q₁₃.card`
3. `∀ u ∈ Q₁₃, ¬ q ∣ sigma 1 (u ^ 4) → cardFactors (sigma 1 (u ^ 4)) = 1 ∨ cardFactors (sigma 1 (u ^ 4)) = 3`. -/
theorem sixth_power_free_no_eight_drop_pinch {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hno8 : ∀ p ∈ N.primeFactors, cardFactors N < cardFactors (componentIndex N p) + 8) :
    let S := squareSources N
    let S₅₁ := S.filter (· % 5 = 1)
    let S₅₀ := S.filter (· % 5 ≠ 1)
    let Q₁₃ := oneModThreeLargeSources N q
    let Q₂₃ := twoModThreeLargeSources N q
    (Q₂₃.card ≤ 1 ∧ S₅₀.card ≤ 3 ∧ 2 * S₅₀.card + 4 * Q₂₃.card ≤ 6) ∧
    (147 ≤ Q₁₃.card ∧ 439 ≤ S₅₁.card + Q₁₃.card) ∧
    (∀ u ∈ Q₁₃, ¬ q ∣ sigma 1 (u ^ 4) →
      cardFactors (sigma 1 (u ^ 4)) = 1 ∨ cardFactors (sigma 1 (u ^ 4)) = 3) := by
  intro S S₅₁ S₅₀ Q₁₃ Q₂₃
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have hfour : ∀ r ∈ largeSources N q, N.factorization r = 4 :=
    (three_free_sixthPowerFree_forces_147_largeSources ho hN hq hq4 he hev h3 hfree).1
  obtain ⟨hcap, hq1, _, _, _⟩ :=
    no_eight_factor_drop_profile ho hN hq hq4 he hev hno8
  obtain ⟨_, _, hvac_card, _⟩ :=
    sixth_power_free_incoming_source_vacuum ho hN hq hq4 he hev hfree
  change 1 + 2 * S₅₀.card + 4 * Q₂₃.card ≤ cardFactors (sigma 1 (ordProj[q] N)) at hvac_card
  have hq_cap : N.factorization q + cardFactors (sigma 1 (ordProj[q] N)) ≤ 8 := hcap q hq
  have hvac_le : 2 * S₅₀.card + 4 * Q₂₃.card ≤ 6 := by omega
  have hQ23_le1 : Q₂₃.card ≤ 1 := by omega
  have hS50_le3 : S₅₀.card ≤ 3 := by omega
  obtain ⟨hω_eq, _, hω_le⟩ :=
    sixth_power_free_omega_and_total_identities ho hN hq hq4 he hev hfree
  change N.primeFactors.card = 1 + S₅₁.card + S₅₀.card + Q₁₃.card + Q₂₃.card at hω_eq
  change N.primeFactors.card ≤ 3 * Q₁₃.card + Q₂₃.card + 2 at hω_le
  have h443 : 443 ≤ N.primeFactors.card :=
    ((sixth_power_or_large_support ho hN).resolve_left fun ⟨p, hp, hpow⟩ => hfree p hp hpow).1
  have hQ13_lb : 147 ≤ Q₁₃.card := by omega
  have hsum_lb : 439 ≤ S₅₁.card + Q₁₃.card := by omega
  have hQ13_dich :=
    (sixth_power_free_quartic_cardFactors_mod_three_dichotomy ho hN hq hq4 he hev hfree).1
  have h13 : ∀ u ∈ Q₁₃, ¬ q ∣ sigma 1 (u ^ 4) →
      cardFactors (sigma 1 (u ^ 4)) = 1 ∨ cardFactors (sigma 1 (u ^ 4)) = 3 := by
    intro u hu hnq
    have hu_lg := (Finset.mem_filter.mp hu).1
    have hu_mem := (Finset.mem_filter.mp hu_lg).1
    have hu_exp := hfour u hu_lg
    have hu_cap : N.factorization u + cardFactors (sigma 1 (ordProj[u] N)) ≤ 8 := hcap u hu_mem
    rw [hu_exp] at hu_cap
    obtain ⟨_, hodd, hbranch⟩ := hQ13_dich u hu hnq
    rcases hbranch with hp | h3_le
    · exact Or.inl (cardFactors_apply_prime hp)
    · right
      have hodd_val := Nat.odd_iff.mp hodd
      omega
  exact ⟨⟨hQ23_le1, hS50_le3, hvac_le⟩, ⟨hQ13_lb, hsum_lb⟩, h13⟩

end OddPerfect
