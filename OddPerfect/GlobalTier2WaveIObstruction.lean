module

public import OddPerfect.ZsqrtTwoPellFermatQuotient
public import OddPerfect.PadicPadeHigherOrderContraction
public import OddPerfect.LinearEulerCoprimeWFactorObstruction
public import OddPerfect.LocalRepeatDropConservation
public import OddPerfect.GlobalTier2WaveHObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Global Tier 2 Wave I Synthesis (`OddPerfect.GlobalTier2WaveIObstruction`)

Unifies the four Priority Wave I structural advances into cross-module global theorems without
discarding any component invariants:
1. **Even Prime-Power `10 ^ 12` Padé Cap, `1393 / 239` Contraction & Primorial Repunit Profile**
   (`even_prime_power_pade_ten_pow_twelve_and_repunit_profile`):
   couples `1154 ≤ u`, `239 ^ (u - 3) * p < 239 * 1393 ^ (u - 3)`, `10 ^ 12 * p < 6 ^ u`
   (`2 * 10 ^ 12 * p < 6 ^ u` when `p % 4 = 3 ∨ Even u`, `10 ^ 12 * p ^ 2 < 6 ^ u` when
   `p ∣ 64 ^ u - 1`), `10 ^ 12 * r ^ (l - 1) < 6 ^ u` (`l + 15 ≤ u` whenever `r ∈ {7, 11, 13}`),
   and the full `(2 * u + 1)`-order Padé quotient profile `(s, k_pade)`.
2. **Tier 2 Wave I Master Profile** (`odd_perfect_tier2_waveI_master_profile`):
   unifies exact component-index drop identities (`componentIndex_drop_eq_exponent_add_oddComponentSigma`
   and `∑ p ∈ N.primeFactors, (Ω(N) - Ω(i_p)) = ω(N) + 2 * (M + E) + 1`), general `∀ D` uniform-drop
   bounds and `D = 4` rank caps, `7 ^ Δ` / `11 ^ Δ` local-repeat ramification bounds, the full
   inter-block odd-valuation `σ`-collision dichotomy and sixth-power-free `61 ≤ W` / `119 * W` /
   `7259` bounds, and the full all-`k` mod-`d ^ 2` Pell–Fermat quotient law on exceptional Euler
   indices.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- **1. Even Prime-Power `10 ^ 12` Padé Cap & Primorial Repunit-Length Profile**:
Preserves every invariant from `even_prime_power_primorial_repunit_length_cap`,
`even_index_prime_ten_pow_twelve_cap`, and `even_prime_power_pade_parity_and_order_profile`. -/
theorem even_prime_power_pade_ten_pow_twelve_and_repunit_profile
    {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    1154 ≤ u ∧ (2 * u + 1).Prime ∧
    239 ^ (u - 3) * p < 239 * 1393 ^ (u - 3) ∧
    10 ^ 12 * p < 6 ^ u ∧
    (p % 4 = 3 ∨ Even u → 2 * 10 ^ 12 * p < 6 ^ u) ∧
    (p ∣ 64 ^ u - 1 → 10 ^ 12 * p ^ 2 < 6 ^ u) ∧
    (∃ r ∈ ({3, 5, 7, 11, 13} : Finset ℕ),
      r ^ 2 ∣ N ∧
      ∃ l : ℕ, l.Prime ∧ 2 < l ∧ geometricBlock r l = p ∧
        10 ^ 12 * r ^ (l - 1) < 6 ^ u ∧
        (r ∈ ({7, 11, 13} : Finset ℕ) → l + 15 ≤ u)) ∧
    (∃ s : ℕ, Odd s ∧
      s < p ^ u ∧ p ^ u < 2 * s ∧
      let k_pade : ℤ := ((s : ℤ) * padeSeqB u p - padeSeqA u p) / (p : ℤ) ^ (2 * u + 1)
      (s : ℤ) * padeSeqB u p - padeSeqA u p = (p : ℤ) ^ (2 * u + 1) * k_pade ∧
      1 ≤ k_pade ∧
      (p % 4 = 3 → Even k_pade ∧ 2 ≤ k_pade) ∧
      (p % 4 = 1 → (Even k_pade ↔ Even u)) ∧
      ((p : ℤ) ∣ k_pade ↔ p ∣ 64 ^ u - 1) ∧
      2 ^ (u + 1) * k_pade ≡ (2 * (u : ℤ) + 1) * (s : ℤ) - 1 [ZMOD (p : ℤ) - 2]) := by
  obtain ⟨⟨hu1154, h10p, h2_10p, h10p2⟩, hrep⟩ :=
    even_prime_power_primorial_repunit_length_cap hN ho hq ha hform hqb hl hr hp hu hi
  obtain ⟨_, hlen_prime, _, _, _, hs_prof⟩ :=
    even_prime_power_pade_parity_and_order_profile hN ho hq ha hform hqb hl hr hp hu hi
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
  obtain ⟨s, hso, _, _, _, hplus, hσs⟩ := even_prime_power_cofactor_split hq hp hmo hpo hu hl hr
  obtain ⟨_, h239_1393, _, _, _⟩ :=
    even_index_prime_ten_pow_twelve_cap hp hpo hso hu hσq hplus hσs
  exact ⟨hu1154, hlen_prime, h239_1393, h10p, h2_10p, h10p2, hrep, hs_prof⟩

/-- **2. Tier 2 Wave I Master Profile**:
Unconditionally synthesizes all component theorems of Wave I with full invariant preservation. -/
theorem odd_perfect_tier2_waveI_master_profile {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    ∃ q a m : ℕ,
      q.Prime ∧ q ∈ N.primeFactors ∧ q % 4 = 1 ∧ a % 4 = 1 ∧ 0 < a ∧ ¬ q ∣ m ∧
      N = q ^ a * m ^ 2 ∧
      (cardFactors (componentIndex N q) + N.factorization q +
        cardFactors (oddComponentSigma N q q) = cardFactors N) ∧
      (∀ p ∈ N.primeFactors.erase q,
        cardFactors (componentIndex N p) + N.factorization p +
          cardFactors (oddComponentSigma N q p) = 1 + cardFactors N) ∧
      (∀ p ∈ N.primeFactors, cardFactors (componentIndex N p) ≤ cardFactors N) ∧
      (∑ p ∈ N.primeFactors, (cardFactors N - cardFactors (componentIndex N p))) =
        N.primeFactors.card + 2 * (localRepeatExcess N q + collisionExcess N q) + 1 ∧
      (∃ p ∈ N.primeFactors,
        N.primeFactors.card + 2 * (localRepeatExcess N q + collisionExcess N q) + 1 ≤
          N.primeFactors.card * (cardFactors N - cardFactors (componentIndex N p))) ∧
      (∀ D : ℕ,
        (∀ p ∈ N.primeFactors, cardFactors N - cardFactors (componentIndex N p) ≤ D) →
          2 * (localRepeatExcess N q + collisionExcess N q) + 1 ≤ (D - 1) * N.primeFactors.card) ∧
      ((∀ p ∈ N.primeFactors, cardFactors N - cardFactors (componentIndex N p) ≤ 4) →
        N.primeFactors.card ≤ 35 ∧ (¬ 3 ∣ N → N.primeFactors.card ≤ 11)) ∧
      (∀ p ∈ N.primeFactors.erase q, N.factorization p = 2 →
        (∏ r ∈ (oddComponentSigma N q p).primeFactors, r) *
          7 ^ (cardFactors (oddComponentSigma N q p) - (oddComponentSigma N q p).primeFactors.card) ≤
          oddComponentSigma N q p) ∧
      (∀ p ∈ N.primeFactors.erase q, N.factorization p = 4 →
        (∏ r ∈ (oddComponentSigma N q p).primeFactors, r) *
          11 ^ (cardFactors (oddComponentSigma N q p) - (oddComponentSigma N q p).primeFactors.card) ≤
          oddComponentSigma N q p) ∧
      (a = 1 → Nat.Coprime ((q + 1) / 2) (componentIndex N q) →
        ∃ h u W : ℕ,
          W = sigma 1 (u ^ 2) / q ∧
          Odd h ∧ Odd u ∧ Odd W ∧ 3 ≤ h ∧ 3 ≤ u ∧ 1 ≤ W ∧
          Nat.Coprime h u ∧ Nat.Coprime h W ∧
          m = h * u ∧ q = 2 * h ^ 2 - 1 ∧ componentIndex N q = u ^ 2 ∧
          u ^ 2 = W * sigma 1 (h ^ 2) ∧ sigma 1 (u ^ 2) = W * (2 * h ^ 2 - 1) ∧
          ((IsSquare (sigma 1 (h ^ 2)) ∧ IsSquare W ∧ 2 ≤ h.primeFactors.card) ∨
            (¬ IsSquare (sigma 1 (h ^ 2)) ∧ ¬ IsSquare W ∧
              ∃ s ∈ u.primeFactors,
                Odd ((sigma 1 (h ^ 2)).factorization s) ∧
                Odd (W.factorization s) ∧
                s ∣ W ∧ s ∣ sigma 1 (h ^ 2) ∧ s ∣ sigma 1 (u ^ 2) ∧
                3 ≤ s ∧ s ≤ W ∧
                ∃ p₁ ∈ h.primeFactors, ∃ p₂ ∈ u.primeFactors,
                  p₁ ≠ p₂ ∧
                  s ∣ sigma 1 (ordProj[p₁] (m ^ 2)) ∧
                  s ∣ sigma 1 (ordProj[p₂] (m ^ 2))))) ∧
      ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) → Nat.Coprime ((q + 1) / 2) (componentIndex N q) →
        ∃ h u W : ℕ,
          W = sigma 1 (u ^ 2) / q ∧
          Odd h ∧ Odd u ∧ Odd W ∧
          59 ≤ h ∧ 6961 ≤ q ∧ 61 ≤ W ∧
          Nat.Coprime h u ∧ Nat.Coprime h W ∧
          N = q * (h * u) ^ 2 ∧ componentIndex N q = u ^ 2 ∧
          u ^ 2 = W * sigma 1 (h ^ 2) ∧ sigma 1 (u ^ 2) = W * (2 * h ^ 2 - 1) ∧
          119 * W ≤ 2 * u ^ 2 - sigma 1 (u ^ 2) ∧
          7259 ≤ 2 * u ^ 2 - sigma 1 (u ^ 2) ∧
          ∃ s ∈ u.primeFactors, s ∣ W ∧ (s % 5 = 1 ∨ s % 3 = 1) ∧ 61 ≤ s) ∧
      (1 < a → ∀ l t : ℕ, l.Prime → sigma 1 (m ^ 2) / q ^ a = l * t ^ 2 →
        let d := (a + 1) / 2
        ∃ (y : ℕ) (k : ℤ) (α : ℤ√2),
          0 < y ∧ d ∣ y ∧ q ^ d + 1 = 2 * y ^ 2 ∧
          1 ≤ |k| ∧ 2 * |k| ≤ (d : ℤ) - 1 ∧
          (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d ∧
          α.norm = (if Even k then -(q : ℤ) else (q : ℤ)) ∧
          k * pellFermatQuotient d ≡ -((y / d : ℕ) : ℤ) [ZMOD (d : ℤ)] ∧
          ((q + 1 : ℕ) : ℤ) ≡ 2 * (d : ℤ) * (k * pellFermatQuotient d) ^ 2 [ZMOD (d : ℤ) ^ 2] ∧
          (d ∈ ({17, 41, 73, 89, 97, 113, 137, 193, 233, 241} : Finset ℕ) →
            ¬ d ^ 2 ∣ y ∧ ¬ d ^ 2 ∣ q + 1)) := by
  obtain ⟨q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, _, _, _, _, _, _, _, _, _⟩ :=
    odd_perfect_tier2_waveH_master_profile ho hN
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
  obtain ⟨hdrop_q, hdrop_p, hdrop_le⟩ :=
    componentIndex_drop_eq_exponent_add_oddComponentSigma ho hN hq_mem hq4 he_q hev_N
  have hdrop_sum := sum_componentIndex_drop_eq_primeFactors_add_two_mul_excess ho hN hq_mem hq4 he_q hev_N
  obtain ⟨hpig, hunifD, hcap4⟩ :=
    exists_componentIndex_drop_mul_ge_and_uniform_drop_cap ho hN hq_mem hq4 he_q hev_N
  obtain ⟨hram2, hram4⟩ :=
    localRepeat_quadratic_and_quartic_ramification_bounds ho hN hq_mem hq4 he_q hev_N
  refine ⟨q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform,
    hdrop_q, hdrop_p, hdrop_le, hdrop_sum, hpig, hunifD, hcap4, hram2, hram4, ?_, ?_, ?_⟩
  · intro ha1 hcop
    have hform1 : N = q * m ^ 2 := by simpa [ha1] using hform
    exact linear_euler_coprime_half_succ_square_or_block_collision ho hN hq hqm hform1 hcop
  · intro hfree hcop
    exact sixth_power_free_coprime_half_succ_w_ge_61 ho hN hq_mem hq4 he_q hev_N hfree hcop
  · intro ha_gt1 l t hl hi d
    exact exceptional_euler_pell_fermat_quotient_profile hN ho hq hq4 ha4 ha_gt1 hqm hform hl hi

end OddPerfect
