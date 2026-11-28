module

public import OddPerfect.ZsqrtTwoUnifiedSieveAndSecondBlockModSq
public import OddPerfect.PadicPadeExactSqrtTwoRatio
public import OddPerfect.DyadicMissingPrimeReciprocalObstruction
public import OddPerfect.LinearEulerCoprimeV0Obstruction
public import OddPerfect.GlobalTier2WaveKObstruction
import OddPerfect.TothSplitExistence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Global Tier 2 Wave L Synthesis (`OddPerfect.GlobalTier2WaveLObstruction`)

Unifies all four Priority Wave L structural modules into cross-module global theorems with
100% preservation of every component invariant:
1. **Even Prime-Power Exact `√2` Padé Ratio & Weighted `(10 ^ 600) ^ 2` Profile**
   (`even_prime_power_exact_sqrt_two_and_ten_pow_1200_master_profile`):
   couples `2 * padeSeqA u p ^ 2 < padeSeqB u p ^ 2`, simultaneous upper-Pell dominance
   `P * padeSeqA u p < Q * padeSeqB u p`, `140 * (p - 1) * k_pade * p ^ u < 99 * padeSeqB u p`,
   and `(10 ^ 600) ^ 2 * p * k_pade.natAbs < 6 ^ u` (`2 * (10 ^ 600) ^ 2 * p < 6 ^ u` when
   `p % 4 = 3 ∨ Even u`, `(10 ^ 600) ^ 2 * p ^ 2 < 6 ^ u` when `p ∣ 64 ^ u - 1`,
   `(10 ^ 600) ^ 2 * u * p < 6 ^ u` when `(2 * u + 1) ∣ p - 2`) with sublinear repunit bounds.
2. **Tier 2 Wave L Master Profile** (`odd_perfect_tier2_waveL_master_profile`):
   unifies the universal double-dyadic missing-prime obstruction (`∃ p ∈ [k₁, B₂], ¬ p ∣ N`)
   and single-dyadic `3 ∣ N` obstruction (`∃ p ∈ [5, 61], p.Prime ∧ ¬ p ∣ N`), the coprime
   half-successor `V₀` coprimality / `IsPrimePow u ↔ W = 1` / reverse `σ`-edge `s → r₀ → q`
   (`5041 ≤ r₀ ^ (2 * e₀)` on sixth-power-free `N`), and the second-block mod-`d ^ 2` law
   `z ^ 2 ≡ 1 + d * w ^ 2 [ZMOD d ^ 2]` with `2 * d ∣ r - 1` (`r ∈ z.primeFactors`), tightened
   `z.minFac` floors (`239`, `293`, `2411`), and `48` excluded primes across `d ∈ {17, 73, 241}`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- **1. Even Prime-Power Exact `√2` Padé Ratio & Weighted `(10 ^ 600) ^ 2` Profile**:
Preserves every invariant from `even_prime_power_exact_sqrt_two_and_weighted_pade_profile` and
`even_prime_power_pade_ten_pow_1200_and_sublinear_repunit_profile`. -/
theorem even_prime_power_exact_sqrt_two_and_ten_pow_1200_master_profile
    {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    6541380665835014 ≤ u ∧ (2 * u + 1).Prime ∧
    2 * padeSeqA u p ^ 2 < padeSeqB u p ^ 2 ∧
    (∀ P Q : ℤ, 0 < P → 0 < Q → 2 * Q ^ 2 - P ^ 2 = 1 →
      P * padeSeqA u p < Q * padeSeqB u p ∧
      P * padeSeqB (u + 1) p < (4 * Q + 3 * P) * (p : ℤ) * padeSeqB u p) ∧
    1393 * padeSeqA u p < 985 * padeSeqB u p ∧
    8119 * padeSeqA u p < 5741 * padeSeqB u p ∧
    1393 * padeSeqB (u + 1) p < 8119 * (p : ℤ) * padeSeqB u p ∧
    239 ^ (u - 3) * p < 239 * 1393 ^ (u - 3) ∧
    (10 ^ 600) ^ 2 * p < 6 ^ u ∧
    (p % 4 = 3 ∨ Even u → 2 * (10 ^ 600) ^ 2 * p < 6 ^ u) ∧
    (p ∣ 64 ^ u - 1 → (10 ^ 600) ^ 2 * p ^ 2 < 6 ^ u) ∧
    ((2 * u + 1) ∣ p - 2 →
      239 ^ (u - 3) * (u * p) < 239 * 1393 ^ (u - 3) ∧
      (10 ^ 600) ^ 2 * u * p < 6 ^ u ∧
      10 ^ 15 * p < 6 ^ u) ∧
    (∃ r ∈ ({3, 5, 7, 11, 13} : Finset ℕ),
      r ^ 2 ∣ N ∧
      ∃ l : ℕ, l.Prime ∧ 2 < l ∧ geometricBlock r l = p ∧
        239 ^ (u - 3) * r ^ (l - 1) < 239 * 1393 ^ (u - 3) ∧
        (10 ^ 600) ^ 2 * r ^ (l - 1) < 6 ^ u ∧
        3 * l + 75 ≤ 5 * u ∧
        (r ∈ ({5, 7, 11, 13} : Finset ℕ) → 8 * l + 131 ≤ 9 * u) ∧
        (r ∈ ({7, 11, 13} : Finset ℕ) →
          11 * l ≤ 10 * u + 11 ∧ l + 590000000000000 ≤ u) ∧
        (r ∈ ({11, 13} : Finset ℕ) →
          4 * l ≤ 3 * u + 4 ∧ l + 1635000000000000 ≤ u) ∧
        (r = 13 →
          10 * l ≤ 7 * u + 10 ∧ l + 1962000000000000 ≤ u)) ∧
    (∃ s : ℕ, Odd s ∧
      s < p ^ u ∧ p ^ u < 2 * s ∧
      let k_pade : ℤ := ((s : ℤ) * padeSeqB u p - padeSeqA u p) / (p : ℤ) ^ (2 * u + 1)
      (s : ℤ) * padeSeqB u p - padeSeqA u p = (p : ℤ) ^ (2 * u + 1) * k_pade ∧
      1 ≤ k_pade ∧
      2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2 < padeSeqB u p ^ 2 ∧
      (p : ℤ) ^ (u + 1) * k_pade < padeSeqB u p ∧
      140 * ((p : ℤ) - 1) * k_pade * (p : ℤ) ^ u < 99 * padeSeqB u p ∧
      239 ^ (u - 3) * (p * k_pade.natAbs) < 239 * 1393 ^ (u - 3) ∧
      (10 ^ 600) ^ 2 * p * k_pade.natAbs < 6 ^ u ∧
      (p % 4 = 3 → Even k_pade ∧ 2 ≤ k_pade) ∧
      (p % 4 = 1 → (Even k_pade ↔ Even u)) ∧
      ((p : ℤ) ∣ k_pade ↔ p ∣ 64 ^ u - 1) ∧
      2 ^ (u + 1) * k_pade ≡ (2 * (u : ℤ) + 1) * (s : ℤ) - 1 [ZMOD (p : ℤ) - 2] ∧
      ((2 * u + 1) ∣ p - 2 →
        (k_pade ≡ (u : ℤ) [ZMOD (2 * (u : ℤ) + 1)] ∨
          k_pade ≡ (u : ℤ) + 1 [ZMOD (2 * (u : ℤ) + 1)]) ∧
        (u : ℤ) ≤ k_pade ∧
        (u : ℤ) * (p : ℤ) ^ (u + 1) < padeSeqB u p)) := by
  obtain ⟨hu_ge, hlen_prime, h239_p, h1200_p, _, _, hdiv_caps, hrep_sub, _⟩ :=
    even_prime_power_pade_ten_pow_1200_and_sublinear_repunit_profile
      hN ho hq ha hform hqb hl hr hp hu hi
  obtain ⟨_, _, h2A2, hpell_all, hpar_1200, hmodp_1200, _, _⟩ :=
    even_prime_power_exact_sqrt_two_and_weighted_pade_profile
      hN ho hq ha hform hqb hl hr hp hu hi
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
  obtain ⟨_, _, h1393_A, h8119_A, h1393_B⟩ :=
    even_index_pade_sq_lt_half_sq_and_upper_pell hp hpo hso hu hσq hplus hσs
  obtain ⟨hmul, hk1, _, _, _⟩ :=
    even_index_pade_quotient_pos_and_quadratic_identity hp hpo hso hu hσq hplus hσs
  obtain ⟨hquad_lt, hpu1_k, h140_k, h239_k_fn⟩ :=
    even_index_pade_quotient_weighted_contraction hp hpo hso hu hσq hplus hσs
  have h239_pk := h239_k_fn (by omega)
  have hnum := ten_pow_1200_lt_six_pow_of_tridecuple_floor (u := u) (by omega)
  set k_pade : ℤ := ((s : ℤ) * padeSeqB u p - padeSeqA u p) / (p : ℤ) ^ (2 * u + 1)
  have h1200_pk : (10 ^ 600) ^ 2 * p * k_pade.natAbs < 6 ^ u := by
    have hmul_lt :
        239 ^ (u - 3) * ((10 ^ 600) ^ 2 * p * k_pade.natAbs) < 239 ^ (u - 3) * 6 ^ u := by
      calc
        239 ^ (u - 3) * ((10 ^ 600) ^ 2 * p * k_pade.natAbs)
            = (10 ^ 600) ^ 2 * (239 ^ (u - 3) * (p * k_pade.natAbs)) := by
                rw [mul_assoc ((10 ^ 600) ^ 2) p k_pade.natAbs, mul_left_comm]
        _ < (10 ^ 600) ^ 2 * (239 * 1393 ^ (u - 3)) :=
            Nat.mul_lt_mul_of_pos_left h239_pk (by positivity)
        _ < 239 ^ (u - 3) * 6 ^ u := hnum
    exact Nat.lt_of_mul_lt_mul_left hmul_lt
  obtain ⟨hmod3, hmod1, _⟩ :=
    even_index_pade_quotient_parity_and_doubled_cap hp hpo hso hu hσq hplus hσs
  obtain ⟨hp_dvd_iff, _, hmod_sub2⟩ :=
    even_index_pade_quotient_mod_p_and_sub_two hp hpo hso hu hσq hplus hσs
  have hdiv_k :
      (2 * u + 1) ∣ p - 2 →
        (k_pade ≡ (u : ℤ) [ZMOD (2 * (u : ℤ) + 1)] ∨
          k_pade ≡ (u : ℤ) + 1 [ZMOD (2 * (u : ℤ) + 1)]) ∧
        (u : ℤ) ≤ k_pade ∧
        (u : ℤ) * (p : ℤ) ^ (u + 1) < padeSeqB u p := by
    intro hdiv
    obtain ⟨hk_mod, hu_le_k, huB, _, _, _⟩ :=
      even_index_pade_quotient_mod_two_len_collapse hq hp hpo hso hu hσq hplus hσs hdiv
    exact ⟨hk_mod, hu_le_k, huB⟩
  exact ⟨hu_ge, hlen_prime, h2A2, hpell_all, h1393_A, h8119_A, h1393_B,
    h239_p, h1200_p, hpar_1200, hmodp_1200, hdiv_caps, hrep_sub,
    ⟨s, hso, hs_lt, hlt_2s, hmul, hk1, hquad_lt, hpu1_k, h140_k, h239_pk, h1200_pk,
      hmod3, hmod1, hp_dvd_iff, hmod_sub2, hdiv_k⟩⟩

/-- **2. Tier 2 Wave L Master Profile**:
Unconditionally synthesizes all component theorems of Wave L with 100% invariant preservation. -/
theorem odd_perfect_tier2_waveL_master_profile {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    (∀ k₁ : ℕ,
      let B₁ := 4 ^ (k₁.primesBelow.card + 1)
      let B₂ := 4 ^ ((B₁ + 1).primesBelow.card + 1)
      ∃ p : ℕ, p.Prime ∧ k₁ ≤ p ∧ p ≤ B₂ ∧ ¬ p ∣ N) ∧
    (3 ∣ N →
      (∀ k : ℕ, 4 ≤ k →
        ∃ p : ℕ, p.Prime ∧ k ≤ p ∧ p ≤ 4 ^ (k.primesBelow.card + 1) ∧ ¬ p ∣ N) ∧
      (∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ≤ 61 ∧ ¬ p ∣ N)) ∧
    ∃ q a m : ℕ,
      q.Prime ∧ q ∈ N.primeFactors ∧ q % 4 = 1 ∧ a % 4 = 1 ∧ 0 < a ∧ ¬ q ∣ m ∧
      N = q ^ a * m ^ 2 ∧
      (a = 1 → Nat.Coprime ((q + 1) / 2) (componentIndex N q) →
        ∃ h u W r₀ e₀ U₀ c₀_u V₀ : ℕ,
          W = sigma 1 (u ^ 2) / q ∧
          m = h * u ∧ q = 2 * h ^ 2 - 1 ∧ componentIndex N q = u ^ 2 ∧
          r₀.Prime ∧ r₀ ∈ u.primeFactors ∧ 0 < e₀ ∧
          e₀ = u.factorization r₀ ∧ U₀ = ordCompl[r₀] u ∧ u = r₀ ^ e₀ * U₀ ∧
          Nat.Coprime (r₀ ^ e₀) U₀ ∧
          sigma 1 (r₀ ^ (2 * e₀)) = q * c₀_u ∧
          W = c₀_u * sigma 1 (U₀ ^ 2) ∧ U₀ ^ 2 = c₀_u * V₀ ∧
          r₀ ^ (2 * e₀) * V₀ = sigma 1 (U₀ ^ 2) * sigma 1 (h ^ 2) ∧
          Nat.Coprime (r₀ ^ (2 * e₀)) V₀ ∧
          (IsPrimePow u ↔ W = 1) ∧
          (¬ IsPrimePow u ↔ 13 ≤ W) ∧
          (IsSquare c₀_u ↔ IsSquare V₀) ∧
          (c₀_u = 1 ↔ V₀ = U₀ ^ 2) ∧
          (13 ≤ W →
            ¬ (r₀ ^ (2 * e₀) ∣ sigma 1 (h ^ 2)) ∧
            r₀ ∣ sigma 1 (U₀ ^ 2) ∧
            ∃ s ∈ U₀.primeFactors, s ≠ r₀ ∧ r₀ ∣ sigma 1 (s ^ (2 * U₀.factorization s)))) ∧
      ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) → Nat.Coprime ((q + 1) / 2) (componentIndex N q) →
        ∃ h u W r₀ e₀ U₀ c₀_u V₀ : ℕ,
          W = sigma 1 (u ^ 2) / q ∧
          59 ≤ h ∧ 6961 ≤ q ∧ 71 ≤ U₀ ∧ 5113 ≤ W ∧
          ¬ IsPrimePow u ∧
          N = q * (h * u) ^ 2 ∧ componentIndex N q = u ^ 2 ∧
          u = r₀ ^ e₀ * U₀ ∧ W = c₀_u * sigma 1 (U₀ ^ 2) ∧ U₀ ^ 2 = c₀_u * V₀ ∧
          r₀ ^ (2 * e₀) * V₀ = sigma 1 (U₀ ^ 2) * sigma 1 (h ^ 2) ∧
          Nat.Coprime (r₀ ^ (2 * e₀)) V₀ ∧
          (r₀ % 5 = 1 ∨ r₀ % 3 = 1) ∧ 61 ≤ r₀ ∧ 5041 ≤ r₀ ^ (2 * e₀) ∧
          r₀ ∣ sigma 1 (U₀ ^ 2) ∧
          ∃ s ∈ U₀.primeFactors, s ≠ r₀ ∧ 61 ≤ s ∧ r₀ ∣ sigma 1 (s ^ (2 * U₀.factorization s))) ∧
      (1 < a → ∀ l t : ℕ, l.Prime → sigma 1 (m ^ 2) / q ^ a = l * t ^ 2 →
        let d := (a + 1) / 2
        ∃ y w z : ℕ,
          0 < y ∧ 0 < w ∧ 3 ≤ z ∧ Odd w ∧ Odd z ∧ Nat.Coprime w z ∧
          y = d * w * z ∧ q + 1 = 2 * d * w ^ 2 ∧ (q ^ d + 1) / (q + 1) = d * z ^ 2 ∧
          q ^ d + 1 = 2 * y ^ 2 ∧
          (z : ℤ) ^ 2 ≡ 1 + (d : ℤ) * (w : ℤ) ^ 2 [ZMOD (d : ℤ) ^ 2] ∧
          (d ∈ ({17, 41, 73, 89, 97, 113, 137, 193, 233, 241} : Finset ℕ) →
            ¬ (d : ℤ) ^ 2 ∣ (z : ℤ) ^ 2 - 1 ∧ ¬ d ^ 2 ∣ z - 1 ∧ ¬ d ^ 2 ∣ z + 1) ∧
          (∀ r ∈ z.primeFactors, 2 * d ∣ r - 1) ∧ 2 * d + 1 ≤ z.minFac ∧
          (d = 17 → 239 ≤ z.minFac ∧ 239 ≤ z ∧
            ∀ r ∈ ({67, 101, 103, 137, 373, 409, 509, 647, 883, 919, 953, 1019, 1291, 1327, 1361, 1427} : Finset ℕ),
              ¬ r ∣ y ∧ ¬ r ∣ w ∧ ¬ r ∣ z) ∧
          (d = 73 → 293 ≤ z.minFac ∧ 293 ≤ z ∧
            ∀ r ∈ ({439, 1021, 1459, 1607, 1753, 3359, 3943, 4673, 5693, 6131, 6277, 6863, 7883, 8467, 8761, 9781} : Finset ℕ),
              ¬ r ∣ y ∧ ¬ r ∣ w ∧ ¬ r ∣ z) ∧
          (d = 241 → 2411 ≤ z.minFac ∧ 2411 ≤ z ∧
            ∀ r ∈ ({1447, 3373, 5303, 7229, 9157, 11087, 16871, 18797, 22171, 26993, 28439, 28921, 30367, 33739, 45307, 47717} : Finset ℕ),
              ¬ r ∣ y ∧ ¬ r ∣ w ∧ ¬ r ∣ z)) := by
  have hdyadic_all : ∀ k₁ : ℕ,
      let B₁ := 4 ^ (k₁.primesBelow.card + 1)
      let B₂ := 4 ^ ((B₁ + 1).primesBelow.card + 1)
      ∃ p : ℕ, p.Prime ∧ k₁ ≤ p ∧ p ≤ B₂ ∧ ¬ p ∣ N :=
    fun k₁ => odd_perfect_omits_prime_in_every_double_dyadic_interval ho hN k₁
  have hdyadic_3 : 3 ∣ N →
      (∀ k : ℕ, 4 ≤ k →
        ∃ p : ℕ, p.Prime ∧ k ≤ p ∧ p ≤ 4 ^ (k.primesBelow.card + 1) ∧ ¬ p ∣ N) ∧
      (∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ≤ 61 ∧ ¬ p ∣ N) :=
    fun h3 => odd_perfect_three_dvd_omits_prime_in_single_dyadic_interval ho hN h3
  obtain ⟨q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, _, _, _, _⟩ :=
    odd_perfect_tier2_waveK_master_profile ho hN
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
  refine ⟨hdyadic_all, hdyadic_3, q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, ?_, ?_, ?_⟩
  · intro ha1 hcop
    have hform1 : N = q * m ^ 2 := by simpa [ha1] using hform
    obtain ⟨h₀, u₀, W₀, r₀_0, e₀_0, U₀_0, c₀_0, V₀_0,
      hW₀_def, hh₀_odd, hu₀_odd, _, _,
      hh₀_ge3, _, _, _, _, _,
      hcop_hu₀, _, hm₀_eq, hq₀_eq, hci₀_eq,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
      linear_euler_coprime_half_succ_unique_source_w_factorization ho hN hq hqm hform1 hcop
    obtain ⟨h, u, W, r₀, e₀, U₀, c₀_u, V₀,
      hW_def, hm_eq, hq_eq, hci_sq_eq,
      hr₀_prime, hr₀_u, he₀_pos, he₀_eq_u, hU₀_def, hu_split,
      hcop_pow_U₀, hsig_r₀_eq, hW_eq, hU₀2_eq, hbal_V₀,
      hcop_r₀_V₀, hpp_iff, hnpp_iff, hsq_iff, hc1_iff⟩ :=
      linear_euler_coprime_half_succ_v0_coprime_and_prime_pow_equiv ho hN hq hqm hform1 hcop
    obtain ⟨h₂, u₂, W₂, r₂, e₂, U₂, c₂, V₂,
      hW₂_def, hm₂_eq, _, hci₂_eq,
      hr₂_prime, hr₂_u, _, he₂_eq_u, hU₂_def, _,
      hsig_r₂_eq, _, _, _, hrev_edge⟩ :=
      linear_euler_coprime_half_succ_reverse_sigma_edge ho hN hq hqm hform1 hcop
    have hu_eq_u₀ : u = u₀ :=
      Nat.pow_left_injective (by decide : 2 ≠ 0) (hci_sq_eq.symm.trans hci₀_eq)
    have hh_eq_h₀ : h = h₀ := by
      have hmul : h * u₀ = h₀ * u₀ := by
        calc
          h * u₀ = h * u := by rw [hu_eq_u₀]
          _ = m := hm_eq.symm
          _ = h₀ * u₀ := hm₀_eq
      exact Nat.mul_right_cancel hu₀_odd.pos hmul
    have hu_odd : Odd u := hu_eq_u₀ ▸ hu₀_odd
    have hh_odd : Odd h := hh_eq_h₀ ▸ hh₀_odd
    have hcop_hu : Nat.Coprime h u := by rw [hh_eq_h₀, hu_eq_u₀]; exact hcop_hu₀
    have hu₂_eq : u₂ = u :=
      Nat.pow_left_injective (by decide : 2 ≠ 0) (hci₂_eq.symm.trans hci_sq_eq)
    have hh₂_eq : h₂ = h := by
      have hmul : h₂ * u = h * u := by
        calc
          h₂ * u = h₂ * u₂ := by rw [hu₂_eq]
          _ = m := hm₂_eq.symm
          _ = h * u := hm_eq
      exact Nat.mul_right_cancel hu_odd.pos hmul
    have hW₂_eq_W : W₂ = W := by rw [hW₂_def, hW_def, hu₂_eq]
    rw [hu₂_eq] at hr₂_u he₂_eq_u hU₂_def
    obtain ⟨_, _, _, _, _, _, _, huniq_src⟩ :=
      linear_euler_unique_q_source_and_bound ho hN hq hqm hform1
    have hr₀_m : r₀ ∈ m.primeFactors := by
      refine Nat.mem_primeFactors.mpr ⟨hr₀_prime, ?_, hm0⟩
      rw [hm_eq]
      exact (Nat.dvd_of_mem_primeFactors hr₀_u).trans (dvd_mul_left u h)
    have hr₀_ndvd_h : ¬ r₀ ∣ h := fun hd_h =>
      hr₀_prime.not_dvd_one (hcop_hu ▸ Nat.dvd_gcd hd_h (Nat.dvd_of_mem_primeFactors hr₀_u))
    have he₀_eq_m : e₀ = m.factorization r₀ := by
      rw [he₀_eq_u, hm_eq, Nat.factorization_mul hh_odd.pos.ne' hu_odd.pos.ne',
        Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hr₀_ndvd_h, zero_add]
    have hq_dvd_r₀ : q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)) := by
      rw [← he₀_eq_m, hsig_r₀_eq]
      exact dvd_mul_right q c₀_u
    have hr₂_m : r₂ ∈ m.primeFactors := by
      refine Nat.mem_primeFactors.mpr ⟨hr₂_prime, ?_, hm0⟩
      rw [hm_eq]
      exact (Nat.dvd_of_mem_primeFactors hr₂_u).trans (dvd_mul_left u h)
    have hr₂_ndvd_h : ¬ r₂ ∣ h := fun hd_h =>
      hr₂_prime.not_dvd_one (hcop_hu ▸ Nat.dvd_gcd hd_h (Nat.dvd_of_mem_primeFactors hr₂_u))
    have he₂_eq_m : e₂ = m.factorization r₂ := by
      rw [he₂_eq_u, hm_eq, Nat.factorization_mul hh_odd.pos.ne' hu_odd.pos.ne',
        Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hr₂_ndvd_h, zero_add]
    have hq_dvd_r₂ : q ∣ sigma 1 (r₂ ^ (2 * m.factorization r₂)) := by
      rw [← he₂_eq_m, hsig_r₂_eq]
      exact dvd_mul_right q c₂
    have hr₂_eq : r₂ = r₀ :=
      (huniq_src r₂ hr₂_m hq_dvd_r₂).trans (huniq_src r₀ hr₀_m hq_dvd_r₀).symm
    rw [hr₂_eq] at he₂_eq_u hU₂_def hrev_edge
    have he₂_eq : e₂ = e₀ := he₂_eq_u.trans he₀_eq_u.symm
    have hU₂_eq : U₂ = U₀ := hU₂_def.trans hU₀_def.symm
    rw [hW₂_eq_W, hh₂_eq, he₂_eq, hU₂_eq] at hrev_edge
    exact ⟨h, u, W, r₀, e₀, U₀, c₀_u, V₀,
      hW_def, hm_eq, hq_eq, hci_sq_eq,
      hr₀_prime, hr₀_u, he₀_pos, he₀_eq_u, hU₀_def, hu_split,
      hcop_pow_U₀, hsig_r₀_eq, hW_eq, hU₀2_eq, hbal_V₀,
      hcop_r₀_V₀, hpp_iff, hnpp_iff, hsq_iff, hc1_iff, hrev_edge⟩
  · intro hfree hcop
    exact sixth_power_free_coprime_half_succ_reverse_edge_r0_ge_61
      ho hN hq_mem hq4 he_q hev_N hfree hcop
  · intro ha_gt1 l t hl hi d
    exact exceptional_euler_second_block_mod_sq_and_z_minFac_sieve
      hN ho hq hq4 ha4 ha_gt1 hqm hform hl hi

end OddPerfect
