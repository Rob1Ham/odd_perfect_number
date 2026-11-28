module

public import OddPerfect.GlobalTier2WaveBObstruction
public import OddPerfect.LinearEulerIteratedPeeling
public import OddPerfect.ZsqrtTwoModEightFrobenius
public import OddPerfect.ChebyshevPrimeEnvelope
public import OddPerfect.PadicThirdOrderObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Tier 2 Priority Wave C Global Synthesis (`OddPerfect.GlobalTier2WaveCObstruction`)

Unifies the four Priority Wave C resolution modules:
1. `OddPerfect.LinearEulerIteratedPeeling`: unconditional `Nat.Coprime r₀ ((q + 1) / 2)` for
   `m.factorization r₀ = 1`, `S₅₁` sixth-power-free descent forcing, and finite-support
   termination `linear_euler_peeling_collision_or_cycle` across all `N = q * m ^ 2`.
2. `OddPerfect.ZsqrtTwoModEightFrobenius`: 2-adic + `d`-adic Frobenius law
   `α ^ d ≡ α [ZMOD 8 * d]` (`[ZMOD 16 * d]` when `Odd k`), coordinate divisibilities, and
   `IsCoprime α.re α.im` on `q ^ d + 1 = 2 * y ^ 2`.
3. `OddPerfect.ChebyshevPrimeEnvelope`: Chebyshev `θ`, `ψ`, `Nat.lcmUpto`, and `Nat.primeCounting`
   envelopes (`ω(N) + π(N.minFac - 1) ≤ π(P_max)` and `2 * rad(N) ≤ primorial P_max`).
4. `OddPerfect.PadicThirdOrderObstruction`: `(2 * u + 1).Prime`, divided cofactor congruence
   `128 * ((s - 1) / p) ≡ 32 + 28 * p + 25 * p ^ 2 [MOD p ^ 3]`, `p`-cancelled identity
   `2 * t_s * (s + 1) = (p + 1) * geometricBlock (p ^ 2) u`, and mod-3 exponent dichotomy on
   the quadratic-repunit branch `p = r_max ^ 2 + r_max + 1`.
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- Cross-coupled even prime-power index (`i = p ^ (2 * u)`) profile uniting
`EvenIndexPrimorialObstruction`, `PadicThirdOrderObstruction`, and `ChebyshevPrimeEnvelope`. -/
theorem even_prime_power_third_order_and_chebyshev_profile
    {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    (2 * u + 1).Prime ∧
    ((∃ r ∈ ({3, 5} : Finset ℕ),
        r ^ 2 ∣ N ∧ ∃ l : ℕ, l.Prime ∧ 2 < l ∧ geometricBlock r l = p) ∨
      (∃ r_max ∈ N.primeFactors,
        r_max % 3 = 2 ∧ p = r_max ^ 2 + r_max + 1 ∧ p % 3 = 1 ∧
        (¬ 3 ∣ N → q % 3 = 1 ∧ 3 ∣ u))) ∧
    ∃ s : ℕ, Odd s ∧
      let t_s := (s - 1) / p
      s = 1 + p * t_s ∧ ¬ p ∣ t_s ∧
      128 * t_s ≡ 32 + 28 * p + 25 * p ^ 2 [MOD p ^ 3] ∧
      2 * t_s * (s + 1) = (p + 1) * geometricBlock (p ^ 2) u := by
  obtain ⟨ha1, hσq⟩ :=
    even_prime_power_index_eq_selected_sigma hN ho hq ha hform hqb hl hr hp hu hi
  have hlen_prime : (2 * u + 1).Prime := even_index_length_prime hq hp hu hσq
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
  obtain ⟨s, hso, _, hms, _, hplus, hσs⟩ := even_prime_power_cofactor_split hq hp hmo hpo hu hl hr
  obtain ⟨hs_eq, hnotp, _, hmod3, _, hcoupled⟩ :=
    even_index_divided_cofactor_mod_p_cube_and_coupled_product hp hpo hso hu hσq hplus hσs
  obtain ⟨_, h35_or⟩ :=
    even_prime_power_component_forces_small_repunit_base
      hN ho hq (by decide : 0 < 1) (by simpa using hform) hqb
      (by simpa [hi] using hl) (by simpa [hi] using hr) hp hu rfl
  refine ⟨hlen_prime, ?_, ⟨s, hso, hs_eq, hnotp, hmod3, hcoupled⟩⟩
  rcases h35_or with h35 | ⟨r_max, hr_maxN, hrmod, hpeq, hpmod3⟩
  · exact Or.inl h35
  · right
    refine ⟨r_max, hr_maxN, hrmod, hpeq, hpmod3, ?_⟩
    intro h3N
    have hs3 : ¬ 3 ∣ s := by
      intro h3s
      have h3m : 3 ∣ m := h3s.trans (hms ▸ dvd_mul_left s _)
      have h3m2 : 3 ∣ m ^ 2 := h3m.trans (dvd_pow_self m (by decide : 2 ≠ 0))
      exact h3N (h3m2.trans (hform ▸ dvd_mul_left _ _))
    obtain ⟨_, _, _, hno3, _⟩ :=
      even_index_quadratic_repunit_mod_three_dichotomy hq hp hpo hso hu hσq hplus hσs hpmod3
    obtain ⟨hq3, _, h3u⟩ := hno3 hs3
    exact ⟨hq3, h3u⟩

/-- **Tier 2 Priority Wave C Master Profile**:
Unconditionally couples Chebyshev prime-counting/primorial support envelopes, linear-Euler
iterated cofactor-peeling collision/cycle termination (`a = 1`), and `ℤ√2` mod-`(8 * d)`
Frobenius coordinate divisibility (`1 < a`). -/
theorem odd_perfect_tier2_waveC_master_profile {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    (∃ hne : N.primeFactors.Nonempty,
      let P_max := N.primeFactors.max' hne
      let rad := ∏ p ∈ N.primeFactors, p
      N.primeFactors.card + 1 ≤ Nat.primeCounting P_max ∧
      N.primeFactors.card + Nat.primeCounting (N.minFac - 1) ≤ Nat.primeCounting P_max ∧
      2 * rad ≤ primorial P_max ∧
      Real.log 2 + Real.log (rad : ℝ) ≤ Chebyshev.theta (P_max : ℝ) ∧
      Chebyshev.theta (P_max : ℝ) ≤ Real.log 4 * (P_max : ℝ) ∧
      (5 ≤ N.minFac →
        ((N.minFac : ℝ) - 1) * Real.log 2 +
          ((N.minFac - 1 : ℕ) : ℝ) * Real.log 2 / Real.log ((N.minFac - 1 : ℕ) : ℝ) <
            (Nat.primeCounting P_max : ℝ))) ∧
    ∃ q a m : ℕ,
      q.Prime ∧ q % 4 = 1 ∧ a % 4 = 1 ∧ ¬ q ∣ m ∧ N = q ^ a * m ^ 2 ∧
      ((a = 1 ∧
          ((∃ r' : ℕ, r'.Prime ∧ ∃ p₁ ∈ m.primeFactors, ∃ p₂ ∈ m.primeFactors,
              p₁ ≠ p₂ ∧ r' ∣ sigma 1 (ordProj[p₁] (m ^ 2)) ∧
              r' ∣ sigma 1 (ordProj[p₂] (m ^ 2))) ∨
           (∃ p ∈ m.primeFactors, p ∣ (q + 1) / 2) ∨
           (∃ L : List ℕ, 2 ≤ L.length ∧ L.Nodup ∧ (∀ p ∈ L, p ∈ m.primeFactors) ∧
              (∀ i : ℕ, ∀ (hi : i + 1 < L.length),
                L[i + 1] ^ (2 * m.factorization L[i + 1]) ∣ sigma 1 (ordProj[L[i]] (m ^ 2))) ∧
              (∀ hL : L ≠ [], L.head hL ∣ sigma 1 (ordProj[L.getLast hL] (m ^ 2)))))) ∨
       (1 < a ∧ ∀ l t : ℕ, l.Prime → sigma 1 (m ^ 2) / q ^ a = l * t ^ 2 →
          ∃ (y : ℕ) (k : ℤ) (α : ℤ√2),
            let u_k : ℤ√2 := ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2)
            1 ≤ |k| ∧ 2 * |k| ≤ ((a + 1) / 2 : ℤ) - 1 ∧
            IsCoprime α.re α.im ∧
            α.re ∣ u_k.re + 2 * u_k.im * (y : ℤ) ∧
            α.im ∣ u_k.re * (y : ℤ) + u_k.im ∧
            α.re ≡ u_k.re [ZMOD ((a + 1) / 2 : ℤ)] ∧
            α.im ≡ u_k.im [ZMOD ((a + 1) / 2 : ℤ)] ∧
            α.re ≡ u_k.re + 2 * u_k.im * (y : ℤ) [ZMOD 8] ∧
            α.im ≡ u_k.re * (y : ℤ) + u_k.im [ZMOD 8])) := by
  obtain ⟨hne, hpi1, _, hprim, hθ1, hθ2⟩ := odd_perfect_support_chebyshev_and_pi_bounds ho hN
  obtain ⟨hne', _, _, hpi_gap, hmin5⟩ := odd_perfect_minFac_primeCounting_pinch ho hN
  have heq_max : N.primeFactors.max' hne' = N.primeFactors.max' hne := rfl
  rw [heq_max] at hpi_gap hmin5
  refine ⟨⟨hne, hpi1, hpi_gap, hprim, hθ1, hθ2, hmin5⟩, ?_⟩
  obtain ⟨q, a, m, hqp, hq4, ha4, hqm, hform⟩ := euler_form ho hN
  have ha_pos : 0 < a := by omega
  refine ⟨q, a, m, hqp, hq4, ha4, hqm, hform, ?_⟩
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt ha_pos) with ha1 | ha_gt1
  · left
    have ha1' : a = 1 := ha1.symm
    have hform1 : N = q * m ^ 2 := by simpa [ha1'] using hform
    exact ⟨ha1', linear_euler_peeling_collision_or_cycle ho hN hqp hqm hform1⟩
  · right
    refine ⟨ha_gt1, fun l t hlp hi => ?_⟩
    obtain ⟨y, k, α, _, _, _, hk1, h2k, _, _, hcop, hdvd_re, hdvd_im,
      hre_d, him_d, hre8, him8, _⟩ :=
      exceptional_euler_zsqrtTwo_mod_eight_d_profile hN ho hqp hq4 ha4 ha_gt1 hqm hform hlp hi
    exact ⟨y, k, α, hk1, h2k, hcop, hdvd_re, hdvd_im, hre_d, him_d, hre8, him8⟩

end OddPerfect
