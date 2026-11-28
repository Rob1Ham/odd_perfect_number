module

public import OddPerfect.ZsqrtTwoSplitPrimeOrderSieve
public import OddPerfect.PadicPadeModTwoLenObstruction
public import OddPerfect.SixthPowerFreeDropExcessPinch
public import OddPerfect.LinearEulerCoprimeAbundancyPinch
public import OddPerfect.GlobalTier2WaveIObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Global Tier 2 Wave J Synthesis (`OddPerfect.GlobalTier2WaveJObstruction`)

Unifies all four Priority Wave J structural modules into cross-module global theorems with
100% preservation of every component invariant:
1. **Even Prime-Power Mod-`(2 * u + 1)` Padé Collapse & All-Primorial Repunit-Length Profile**
   (`even_prime_power_pade_mod_two_len_and_all_primorial_profile`):
   couples `(2 * u + 1) ∣ p - 2 → k_pade ≡ u ∨ u + 1 [ZMOD 2 * u + 1]`, `(u : ℤ) ≤ k_pade`,
   `(u : ℤ) * p ^ (u + 1) < padeSeqB u p`, `10 ^ 12 * u * p < 6 ^ u`, and `10 ^ 15 * p < 6 ^ u`
   with linear repunit-length caps across all five surviving primorial bases `r ∈ {3, 5, 7, 11, 13}`
   (`3 * l + 75 ≤ 5 * u`, `8 * l + 131 ≤ 9 * u` for `r ≥ 5`, `l + 15 ≤ u` for `r ≥ 7`).
2. **Tier 2 Wave J Master Profile** (`odd_perfect_tier2_waveJ_master_profile`):
   unifies global drop-sum cyclotomic slope lower bounds, sixth-power-free incoming-vacuum
   `indegAt` / `localRepeatAt` / `collisionExcess` / `1916`-drop partitions, coprime
   half-successor `σ(h ^ 2) + 3 ≤ 2 * h ^ 2` deficiency, `¬ 105 ∣ h`, strict `φ(h)` / `φ(u)`
   envelopes, exact `W = 1 ↔ ω(u) = 1` (`3 ≤ W ↔ 2 ≤ ω(u)`) equivalence (forcing `2 ≤ ω(u)`
   unconditionally on sixth-power-free `N`), and the all-`k` split-prime `ℤ√2` order sieve
   (`24` concrete split primes across `d ∈ {17, 73, 241}`).
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma align_waveJ_coprime_witnesses
    {N q h u W h' u' W' : ℕ}
    (hq_eq : q = 2 * h ^ 2 - 1) (hh_ge3 : 3 ≤ h) (hci : componentIndex N q = u ^ 2)
    (hW_def : W = sigma 1 (u ^ 2) / q)
    (hq_eq' : q = 2 * h' ^ 2 - 1) (hh_ge3' : 3 ≤ h') (hci' : componentIndex N q = u' ^ 2)
    (hW_def' : W' = sigma 1 (u' ^ 2) / q) :
    h' = h ∧ u' = u ∧ W' = W := by
  have hh2_eq : h' ^ 2 = h ^ 2 := by
    have h1 : 1 ≤ 2 * h ^ 2 := by nlinarith
    have h2 : 1 ≤ 2 * h' ^ 2 := by nlinarith
    omega
  have hh_eq : h' = h := Nat.pow_left_injective (by decide : 2 ≠ 0) hh2_eq
  have hu2_eq : u' ^ 2 = u ^ 2 := hci'.symm.trans hci
  have hu_eq : u' = u := Nat.pow_left_injective (by decide : 2 ≠ 0) hu2_eq
  have hW_eq : W' = W := by rw [hW_def', hW_def, hu_eq]
  exact ⟨hh_eq, hu_eq, hW_eq⟩

/-- **1. Even Prime-Power Mod-`(2 * u + 1)` Padé Collapse & All-Primorial Repunit Profile**:
Preserves every invariant from `even_prime_power_all_primorial_repunit_and_len_div_caps`,
`even_index_pade_quotient_mod_two_len_collapse`, and
`even_prime_power_pade_ten_pow_twelve_and_repunit_profile`. -/
theorem even_prime_power_pade_mod_two_len_and_all_primorial_profile
    {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    1154 ≤ u ∧ (2 * u + 1).Prime ∧
    239 ^ (u - 3) * p < 239 * 1393 ^ (u - 3) ∧
    10 ^ 12 * p < 6 ^ u ∧
    (p % 4 = 3 ∨ Even u → 2 * 10 ^ 12 * p < 6 ^ u) ∧
    (p ∣ 64 ^ u - 1 → 10 ^ 12 * p ^ 2 < 6 ^ u) ∧
    ((2 * u + 1) ∣ p - 2 →
      239 ^ (u - 3) * (u * p) < 239 * 1393 ^ (u - 3) ∧
      10 ^ 12 * u * p < 6 ^ u ∧
      10 ^ 15 * p < 6 ^ u) ∧
    (∃ r ∈ ({3, 5, 7, 11, 13} : Finset ℕ),
      r ^ 2 ∣ N ∧
      ∃ l : ℕ, l.Prime ∧ 2 < l ∧ geometricBlock r l = p ∧
        10 ^ 12 * r ^ (l - 1) < 6 ^ u ∧
        3 * l + 75 ≤ 5 * u ∧
        (r ∈ ({5, 7, 11, 13} : Finset ℕ) → 8 * l + 131 ≤ 9 * u) ∧
        (r ∈ ({7, 11, 13} : Finset ℕ) → l + 15 ≤ u)) ∧
    (∃ s : ℕ, Odd s ∧
      s < p ^ u ∧ p ^ u < 2 * s ∧
      let k_pade : ℤ := ((s : ℤ) * padeSeqB u p - padeSeqA u p) / (p : ℤ) ^ (2 * u + 1)
      (s : ℤ) * padeSeqB u p - padeSeqA u p = (p : ℤ) ^ (2 * u + 1) * k_pade ∧
      1 ≤ k_pade ∧
      (p % 4 = 3 → Even k_pade ∧ 2 ≤ k_pade) ∧
      (p % 4 = 1 → (Even k_pade ↔ Even u)) ∧
      ((p : ℤ) ∣ k_pade ↔ p ∣ 64 ^ u - 1) ∧
      2 ^ (u + 1) * k_pade ≡ (2 * (u : ℤ) + 1) * (s : ℤ) - 1 [ZMOD (p : ℤ) - 2] ∧
      ((2 * u + 1) ∣ p - 2 →
        (k_pade ≡ (u : ℤ) [ZMOD (2 * (u : ℤ) + 1)] ∨
          k_pade ≡ (u : ℤ) + 1 [ZMOD (2 * (u : ℤ) + 1)]) ∧
        (u : ℤ) ≤ k_pade ∧
        (u : ℤ) * (p : ℤ) ^ (u + 1) < padeSeqB u p)) := by
  obtain ⟨hu1154, hlen_prime, h239_1393, h10p, h2_10p, h10p2, _, _⟩ :=
    even_prime_power_pade_ten_pow_twelve_and_repunit_profile hN ho hq ha hform hqb hl hr hp hu hi
  obtain ⟨_, _, _, _, hrep_all⟩ :=
    even_prime_power_all_primorial_repunit_and_len_div_caps hN ho hq ha hform hqb hl hr hp hu hi
  obtain ⟨ha1, hσq⟩ :=
    even_prime_power_index_eq_selected_sigma hN ho hq ha hform hqb hl hr hp hu hi
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b _)
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h4 : 4 ∣ 2 * b := hr ▸ hi ▸ (pow_dvd_pow 2 (by omega : 2 ≤ 2 * u)).trans (dvd_mul_left _ _)
    have := hbo.not_two_dvd_nat
    omega
  have hpo : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨m, _, _, _, rfl⟩ :=
    euler_form_of_odd_component_index hN ho hq ha hform hqb hl hr (hi ▸ hpo.pow)
  have hmo := ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _)
  rw [ha1, pow_one] at hform hl hr
  rw [hi] at hl hr
  obtain ⟨s, hso, _, _, _, hplus, hσs⟩ :=
    even_prime_power_cofactor_split hq hp hmo hpo hu hl hr
  obtain ⟨_, _, hs_lt, hlt_2s⟩ := even_index_cofactor_archimedean_sandwich hp hpo hu hσq hplus
  obtain ⟨hmul, hk1, _, _, _⟩ :=
    even_index_pade_quotient_pos_and_quadratic_identity hp hpo hso hu hσq hplus hσs
  obtain ⟨hmod3, hmod1, _⟩ :=
    even_index_pade_quotient_parity_and_doubled_cap hp hpo hso hu hσq hplus hσs
  obtain ⟨hp_dvd_iff, _, hmod_sub2⟩ :=
    even_index_pade_quotient_mod_p_and_sub_two hp hpo hso hu hσq hplus hσs
  have hdiv_caps :
      (2 * u + 1) ∣ p - 2 →
        239 ^ (u - 3) * (u * p) < 239 * 1393 ^ (u - 3) ∧
        10 ^ 12 * u * p < 6 ^ u ∧
        10 ^ 15 * p < 6 ^ u := by
    intro hdiv
    obtain ⟨_, _, _, h239_up, h10_up, h10_15⟩ :=
      even_index_pade_quotient_mod_two_len_collapse hq hp hpo hso hu hσq hplus hσs hdiv
    exact ⟨h239_up, h10_up, h10_15⟩
  have hdiv_k :
      (2 * u + 1) ∣ p - 2 →
        (let k_pade : ℤ := ((s : ℤ) * padeSeqB u p - padeSeqA u p) / (p : ℤ) ^ (2 * u + 1)
         (k_pade ≡ (u : ℤ) [ZMOD (2 * (u : ℤ) + 1)] ∨
           k_pade ≡ (u : ℤ) + 1 [ZMOD (2 * (u : ℤ) + 1)]) ∧
         (u : ℤ) ≤ k_pade ∧
         (u : ℤ) * (p : ℤ) ^ (u + 1) < padeSeqB u p) := by
    intro hdiv
    obtain ⟨hk_mod, hu_le_k, huB, _, _, _⟩ :=
      even_index_pade_quotient_mod_two_len_collapse hq hp hpo hso hu hσq hplus hσs hdiv
    exact ⟨hk_mod, hu_le_k, huB⟩
  exact ⟨hu1154, hlen_prime, h239_1393, h10p, h2_10p, h10p2, hdiv_caps, hrep_all,
    ⟨s, hso, hs_lt, hlt_2s, hmul, hk1, hmod3, hmod1, hp_dvd_iff, hmod_sub2, hdiv_k⟩⟩

/-- **2. Tier 2 Wave J Master Profile**:
Unconditionally synthesizes all component theorems of Wave J with 100% invariant preservation. -/
theorem odd_perfect_tier2_waveJ_master_profile {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    ∃ q a m : ℕ,
      q.Prime ∧ q ∈ N.primeFactors ∧ q % 4 = 1 ∧ a % 4 = 1 ∧ 0 < a ∧ ¬ q ∣ m ∧
      N = q ^ a * m ^ 2 ∧
      (17 * N.primeFactors.card + 11 * (twoModThreeLargeSources N q).card ≤
        4 * (∑ p ∈ N.primeFactors, (cardFactors N - cardFactors (componentIndex N p))) + 35) ∧
      (¬ 3 ∣ N →
        13 * N.primeFactors.card + 8 * (twoModThreeLargeSources N q).card ≤
          3 * (∑ p ∈ N.primeFactors, (cardFactors N - cardFactors (componentIndex N p))) + 11) ∧
      ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
        let S₅₀ := (squareSources N).filter (· % 5 ≠ 1)
        let S₅₁ := (squareSources N).filter (· % 5 = 1)
        let Q₁₃ := oneModThreeLargeSources N q
        let Q₂₃ := twoModThreeLargeSources N q
        (indegAt N q q = 1 ∧ localRepeatAt N q q = 0) ∧
        (∀ r ∈ S₅₀, indegAt N q r = 1 ∧ localRepeatAt N q r = 1) ∧
        (∀ r ∈ Q₂₃, indegAt N q r = 1 ∧ localRepeatAt N q r = 3) ∧
        localRepeatExcess N q + collisionExcess N q =
          (squareSources N).card + 3 * (largeSources N q).card ∧
        S₅₀.card + 3 * Q₂₃.card ≤ localRepeatExcess N q ∧
        collisionExcess N q = ∑ r ∈ S₅₁ ∪ Q₁₃, (indegAt N q r - 1) ∧
        221 ≤ collisionExcess N q ∧
        collisionExcess N q ≤ S₅₁.card + 3 * Q₁₃.card ∧
        1916 ≤ ∑ p ∈ N.primeFactors, (cardFactors N - cardFactors (componentIndex N p)) ∧
        (∑ p ∈ N.primeFactors, (cardFactors N - cardFactors (componentIndex N p))) + 1 =
          3 * N.primeFactors.card + 4 * (largeSources N q).card ∧
        (∃ p ∈ N.primeFactors,
          3 * N.primeFactors.card + 4 * (largeSources N q).card ≤
            N.primeFactors.card * (cardFactors N - cardFactors (componentIndex N p)) + 1 ∧
          4 ≤ cardFactors N - cardFactors (componentIndex N p) ∧
          ((squareSources N).card + 2 ≤ 3 * (largeSources N q).card →
            5 ≤ cardFactors N - cardFactors (componentIndex N p)))) ∧
      (a = 1 → Nat.Coprime ((q + 1) / 2) (componentIndex N q) →
        ∃ h u W : ℕ,
          W = sigma 1 (u ^ 2) / q ∧
          Odd h ∧ Odd u ∧ Odd W ∧ 3 ≤ h ∧ 3 ≤ u ∧ 1 ≤ W ∧
          Nat.Coprime h u ∧ Nat.Coprime h W ∧
          m = h * u ∧ q = 2 * h ^ 2 - 1 ∧ componentIndex N q = u ^ 2 ∧
          u ^ 2 = W * sigma 1 (h ^ 2) ∧ sigma 1 (u ^ 2) = W * (2 * h ^ 2 - 1) ∧
          sigma 1 (h ^ 2) + 3 ≤ 2 * h ^ 2 ∧
          sigma 1 (h ^ 2) + 2 ≤ q ∧
          ¬ 105 ∣ h ∧
          (3 * h.primeFactors.card + 5) * h < 2 * (4 * h.primeFactors.card + 5) * h.totient ∧
          3 * h < 8 * h.totient ∧
          (¬ 3 ∣ N → 27 * h < 64 * h.totient) ∧
          (3 * u.primeFactors.card + 5) * u ^ 3 <
            (4 * u.primeFactors.card + 5) * W * (2 * h ^ 2 - 1) * u.totient ∧
          3 * u ^ 3 < 4 * W * (2 * h ^ 2 - 1) * u.totient ∧
          (¬ 3 ∣ N → 27 * u ^ 3 < 32 * W * (2 * h ^ 2 - 1) * u.totient) ∧
          (W = 1 ↔ u.primeFactors.card = 1) ∧
          (3 ≤ W ↔ 2 ≤ u.primeFactors.card) ∧
          (W = 1 →
            2 ≤ h.primeFactors.card ∧
            16 ≤ N.primeFactors.card ∧
            ∃ p e : ℕ,
              p.Prime ∧ 1154 ≤ e ∧ 13082761331670028 ≤ 2 * e ∧
              u = p ^ e ∧ componentIndex N q = p ^ (2 * e) ∧
              10 ^ 12 * p < 6 ^ e)) ∧
      ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) → Nat.Coprime ((q + 1) / 2) (componentIndex N q) →
        ∃ h u W : ℕ,
          W = sigma 1 (u ^ 2) / q ∧
          Odd h ∧ Odd u ∧ Odd W ∧
          59 ≤ h ∧ 6961 ≤ q ∧ 61 ≤ W ∧
          2 ≤ u.primeFactors.card ∧
          Nat.Coprime h u ∧ Nat.Coprime h W ∧
          N = q * (h * u) ^ 2 ∧ componentIndex N q = u ^ 2 ∧
          u ^ 2 = W * sigma 1 (h ^ 2) ∧ sigma 1 (u ^ 2) = W * (2 * h ^ 2 - 1) ∧
          sigma 1 (h ^ 2) + 3 ≤ 2 * h ^ 2 ∧
          ¬ 105 ∣ h ∧
          27 * h < 64 * h.totient ∧
          27 * u ^ 3 < 32 * W * (2 * h ^ 2 - 1) * u.totient ∧
          7259 ≤ 2 * u ^ 2 - sigma 1 (u ^ 2)) ∧
      (1 < a → ∀ l t : ℕ, l.Prime → sigma 1 (m ^ 2) / q ^ a = l * t ^ 2 →
        let d := (a + 1) / 2
        ∃ y w z : ℕ,
          0 < y ∧ 0 < w ∧ 0 < z ∧
          y = d * w * z ∧ q + 1 = 2 * d * w ^ 2 ∧ q ^ d + 1 = 2 * y ^ 2 ∧
          (∀ r : ℕ, r.Prime → (r % 8 = 1 ∨ r % 8 = 7) → d ∣ r - 1 →
            ¬ ((r : ℤ) ∣ (((silverUnit ^ ((r - 1) / d) : (ℤ√2)ˣ) : ℤ√2).re - 1) ∧
               (r : ℤ) ∣ (((silverUnit ^ ((r - 1) / d) : (ℤ√2)ˣ) : ℤ√2).im)) →
            ¬ r ∣ y ∧ ¬ r ∣ w ∧ ¬ r ∣ z) ∧
          (d = 17 → ∀ r ∈ ({103, 137, 409, 647, 919, 953, 1327, 1361} : Finset ℕ),
            ¬ r ∣ y ∧ ¬ r ∣ w ∧ ¬ r ∣ z) ∧
          (d = 73 → ∀ r ∈ ({439, 1607, 1753, 3359, 3943, 4673, 6863, 8761} : Finset ℕ),
            ¬ r ∣ y ∧ ¬ r ∣ w ∧ ¬ r ∣ z) ∧
          (d = 241 → ∀ r ∈ ({1447, 5303, 11087, 16871, 26993, 28439, 28921, 30367} : Finset ℕ),
            ¬ r ∣ y ∧ ¬ r ∣ w ∧ ¬ r ∣ z)) := by
  obtain ⟨q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    odd_perfect_tier2_waveI_master_profile ho hN
  have hm0 : m ≠ 0 := by
    intro hm
    rw [hm] at hform
    simp at hform
    exact hN.2.ne' hform
  have hfact_q : N.factorization q = a := by
    rw [hform, Nat.factorization_mul (pow_ne_zero a hq.ne_zero) (pow_ne_zero 2 hm0),
      Finsupp.add_apply, hq.factorization_pow, Finsupp.single_eq_same]
    have hqm2 : ¬ q ∣ m ^ 2 := fun hd => hqm (hq.dvd_of_dvd_pow hd)
    rw [Nat.factorization_eq_zero_of_not_dvd hqm2]
    omega
  have he_q : N.factorization q % 4 = 1 := by omega
  have hev_N : ∀ r : ℕ, r ≠ q → Even (N.factorization r) := by
    intro r hr_ne
    by_cases hr_prime : r.Prime
    · rw [hform, Nat.factorization_mul (pow_ne_zero a hq.ne_zero) (pow_ne_zero 2 hm0),
        Finsupp.add_apply, hq.factorization_pow, Finsupp.single_eq_of_ne hr_ne, zero_add,
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
      exact ⟨m.factorization r, by ring⟩
    · rw [Nat.factorization_eq_zero_of_not_prime N hr_prime]
      exact ⟨0, rfl⟩
  obtain ⟨hslope_17, hslope_13⟩ :=
    componentIndex_drop_sum_cyclotomic_slope_lower_bounds ho hN hq_mem hq4 he_q hev_N
  refine ⟨q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, hslope_17, hslope_13, ?_, ?_, ?_, ?_⟩
  · intro hfree
    obtain ⟨hq_vac, hS50_vac, hQ23_vac⟩ :=
      sixth_power_free_vacuum_indegAt_and_localRepeatAt ho hN hq_mem hq4 he_q hev_N hfree
    obtain ⟨hME_eq, hloc_le, hcol_eq, h221, hcol_le, h1916⟩ :=
      sixth_power_free_excess_and_drop_partition ho hN hq_mem hq4 he_q hev_N hfree
    obtain ⟨hsum_id, hpig⟩ :=
      sixth_power_free_pigeonhole_drop_with_largeSources_bonus ho hN hq_mem hq4 he_q hev_N hfree
    exact ⟨hq_vac, hS50_vac, hQ23_vac, hME_eq, hloc_le, hcol_eq, h221, hcol_le, h1916, hsum_id, hpig⟩
  · intro ha1 hcop
    have hform1 : N = q * m ^ 2 := by simpa [ha1] using hform
    obtain ⟨h, u, W, hW_def, hh_odd, hu_odd, hW_odd, hh_ge3, hu_ge3, hW_ge1,
      hcop_hu, hcop_hW, hm_eq, hq_eq, hci_sq_eq, hu2_eq, hsigu2_eq,
      hdef3, hdef2, h105⟩ :=
      linear_euler_coprime_half_succ_h_sq_deficient_bound ho hN hq hqm hform1 hcop
    obtain ⟨h₂, u₂, W₂, hW₂_def, _, _, _, hh₂_ge3, _, _, _, hq₂_eq, hci₂_eq, _,
      hh_env1, hh_env2, hh_env3, hu_env1, hu_env2, hu_env3⟩ :=
      linear_euler_coprime_half_succ_totient_envelopes ho hN hq hqm hform1 hcop
    obtain ⟨hh₂_eq, hu₂_eq, hW₂_eq⟩ :=
      align_waveJ_coprime_witnesses hq_eq hh_ge3 hci_sq_eq hW_def hq₂_eq hh₂_ge3 hci₂_eq hW₂_def
    obtain ⟨h₃, u₃, W₃, hW₃_def, _, _, _, hh₃_ge3, _, _, _, hq₃_eq, hci₃_eq, _, _,
      hW_iff_card1, hW3_iff_card2, hW1_lift⟩ :=
      linear_euler_coprime_half_succ_w_one_iff_prime_pow_u ho hN hq hqm hform1 hcop
    obtain ⟨hh₃_eq, hu₃_eq, hW₃_eq⟩ :=
      align_waveJ_coprime_witnesses hq_eq hh_ge3 hci_sq_eq hW_def hq₃_eq hh₃_ge3 hci₃_eq hW₃_def
    subst h₂; subst u₂; subst W₂
    subst h₃; subst u₃; subst W₃
    exact ⟨h, u, W, hW_def, hh_odd, hu_odd, hW_odd, hh_ge3, hu_ge3, hW_ge1,
      hcop_hu, hcop_hW, hm_eq, hq_eq, hci_sq_eq, hu2_eq, hsigu2_eq,
      hdef3, hdef2, h105, hh_env1, hh_env2, hh_env3, hu_env1, hu_env2, hu_env3,
      hW_iff_card1, hW3_iff_card2, hW1_lift⟩
  · intro hfree hcop
    exact sixth_power_free_coprime_half_succ_two_primes_in_u ho hN hq_mem hq4 he_q hev_N hfree hcop
  · intro ha_gt1 l t hl hi d
    exact exceptional_euler_split_prime_y_sieve hN ho hq hq4 ha4 ha_gt1 hqm hform hl hi

end OddPerfect
