module

public import OddPerfect.ZsqrtTwoInertPrimeOrderSieve
public import OddPerfect.PadicPadeSublinearRepunitBounds
public import OddPerfect.SixthPowerFreeQuarticCollisionPinch
public import OddPerfect.LinearEulerCoprimeUniqueSourceSplit
public import OddPerfect.GlobalTier2WaveJObstruction
import OddPerfect.TothSplitExistence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Global Tier 2 Wave K Synthesis (`OddPerfect.GlobalTier2WaveKObstruction`)

Unifies all four Priority Wave K structural modules into cross-module global theorems with
100% preservation of every component invariant:
1. **Even Prime-Power `(10 ^ 600) ^ 2` Padé & Sublinear Repunit-Length Profile**
   (`even_prime_power_pade_ten_pow_1200_and_sublinear_repunit_profile`):
   couples `6541380665835014 ≤ u`, `(10 ^ 600) ^ 2 * p < 6 ^ u`,
   `(2 * u + 1) ∣ p - 2 → (10 ^ 600) ^ 2 * u * p < 6 ^ u`, and sublinear repunit-length
   bounds (`11 * l ≤ 10 * u + 11` with `l + 590000000000000 ≤ u` for `r ∈ {7, 11, 13}`,
   `4 * l ≤ 3 * u + 4` with `l + 1635000000000000 ≤ u` for `r ∈ {11, 13}`,
   `10 * l ≤ 7 * u + 10` with `l + 1962000000000000 ≤ u` for `r = 13`) with the full
   `k_pade` congruence and divisibility profile.
2. **Tier 2 Wave K Master Profile** (`odd_perfect_tier2_waveK_master_profile`):
   unifies the sixth-power-free `S₅₁` collision/repeat split (`S₅₁_col` vs. `S₅₁_rep`),
   unconditional `80 ≤ |Q₁₃|` (`2 * ω(N) ≤ 11 * |Q₁₃| + 11`), half-rank bipartite pinch
   `S₅₀.card + S₅₁_rep.card + Q₂₃.card ≤ S₅₁_col.card + 5 * Q₁₃.card + 1`, the unique
   `q`-source factorization `u = r₀ ^ e₀ * U₀` (`W = c₀_u * σ(U₀ ^ 2)`, `U₀ ^ 2 = c₀_u * V₀`,
   `r₀ ^ (2 * e₀) * V₀ = σ(U₀ ^ 2) * σ(h ^ 2)`, `W = 1 ∨ 13 ≤ W`, and `5113 ≤ W` with
   `608447 ≤ 2 * u ^ 2 - σ(u ^ 2)` on sixth-power-free `N`), and the all-`k` inert-prime
   `ℤ√2` norm-`1` subgroup sieve (`24` concrete inert primes across `d ∈ {17, 73, 241}`).
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma align_waveK_coprime_witnesses
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

/-- **1. Even Prime-Power `(10 ^ 600) ^ 2` Padé & Sublinear Repunit Profile**:
Preserves every invariant from `even_prime_power_tridecuple_sublinear_repunit_profile` and
`even_prime_power_pade_mod_two_len_and_all_primorial_profile`. -/
theorem even_prime_power_pade_ten_pow_1200_and_sublinear_repunit_profile
    {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    6541380665835014 ≤ u ∧ (2 * u + 1).Prime ∧
    239 ^ (u - 3) * p < 239 * 1393 ^ (u - 3) ∧
    (10 ^ 600) ^ 2 * p < 6 ^ u ∧
    (p % 4 = 3 ∨ Even u → 2 * 10 ^ 12 * p < 6 ^ u) ∧
    (p ∣ 64 ^ u - 1 → 10 ^ 12 * p ^ 2 < 6 ^ u) ∧
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
      (p % 4 = 3 → Even k_pade ∧ 2 ≤ k_pade) ∧
      (p % 4 = 1 → (Even k_pade ↔ Even u)) ∧
      ((p : ℤ) ∣ k_pade ↔ p ∣ 64 ^ u - 1) ∧
      2 ^ (u + 1) * k_pade ≡ (2 * (u : ℤ) + 1) * (s : ℤ) - 1 [ZMOD (p : ℤ) - 2] ∧
      ((2 * u + 1) ∣ p - 2 →
        (k_pade ≡ (u : ℤ) [ZMOD (2 * (u : ℤ) + 1)] ∨
          k_pade ≡ (u : ℤ) + 1 [ZMOD (2 * (u : ℤ) + 1)]) ∧
        (u : ℤ) ≤ k_pade ∧
        (u : ℤ) * (p : ℤ) ^ (u + 1) < padeSeqB u p)) := by
  obtain ⟨_, hlen_prime, h239_p, _, h2_10p, h10p2, hdiv_old, _, hs_prof⟩ :=
    even_prime_power_pade_mod_two_len_and_all_primorial_profile
      hN ho hq ha hform hqb hl hr hp hu hi
  obtain ⟨hu_ge, _, h1200_p, hdiv_1200, hrep_sub⟩ :=
    even_prime_power_tridecuple_sublinear_repunit_profile
      hN ho hq ha hform hqb hl hr hp hu hi
  refine ⟨hu_ge, hlen_prime, h239_p, h1200_p, h2_10p, h10p2, ?_, hrep_sub, hs_prof⟩
  intro hdiv
  obtain ⟨h239_up, _, h10_15⟩ := hdiv_old hdiv
  exact ⟨h239_up, hdiv_1200 hdiv, h10_15⟩

/-- **2. Tier 2 Wave K Master Profile**:
Unconditionally synthesizes all component theorems of Wave K with 100% invariant preservation. -/
theorem odd_perfect_tier2_waveK_master_profile {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    ∃ q a m : ℕ,
      q.Prime ∧ q ∈ N.primeFactors ∧ q % 4 = 1 ∧ a % 4 = 1 ∧ 0 < a ∧ ¬ q ∣ m ∧
      N = q ^ a * m ^ 2 ∧
      ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
        let S₅₀ := (squareSources N).filter (· % 5 ≠ 1)
        let S₅₁ := (squareSources N).filter (· % 5 = 1)
        let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
        let S₅₁_rep := S₅₁.filter (fun r => indegAt N q r = 1)
        let Q₁₃ := oneModThreeLargeSources N q
        let Q₂₃ := twoModThreeLargeSources N q
        S₅₁ = S₅₁_col ∪ S₅₁_rep ∧
        Disjoint S₅₁_col S₅₁_rep ∧
        S₅₁.card = S₅₁_col.card + S₅₁_rep.card ∧
        collisionExcess N q = S₅₁_col.card + ∑ r ∈ Q₁₃, (indegAt N q r - 1) ∧
        localRepeatExcess N q =
          S₅₀.card + S₅₁_rep.card + 3 * Q₂₃.card + ∑ r ∈ Q₁₃, localRepeatAt N q r ∧
        221 ≤ S₅₁_col.card + 3 * Q₁₃.card ∧
        2 * Q₂₃.card ≤ 5 * Q₁₃.card + 7 ∧
        2 * N.primeFactors.card ≤ 11 * Q₁₃.card + 11 ∧
        80 ≤ Q₁₃.card ∧
        N.primeFactors.card ≤ 2 * S₅₁_col.card + 6 * Q₁₃.card + 2 ∧
        S₅₀.card + S₅₁_rep.card + Q₂₃.card ≤ S₅₁_col.card + 5 * Q₁₃.card + 1) ∧
      (a = 1 → Nat.Coprime ((q + 1) / 2) (componentIndex N q) →
        ∃ h u W r₀ e₀ U₀ c₀_u V₀ : ℕ,
          W = sigma 1 (u ^ 2) / q ∧
          Odd h ∧ Odd u ∧ Odd W ∧ Odd U₀ ∧
          3 ≤ h ∧ 3 ≤ u ∧ 1 ≤ W ∧ 1 ≤ U₀ ∧ 1 ≤ c₀_u ∧ 1 ≤ V₀ ∧
          Nat.Coprime h u ∧ Nat.Coprime h W ∧
          m = h * u ∧ q = 2 * h ^ 2 - 1 ∧ componentIndex N q = u ^ 2 ∧
          r₀.Prime ∧ r₀ ∈ u.primeFactors ∧ ¬ r₀ ∣ h ∧ 0 < e₀ ∧
          e₀ = u.factorization r₀ ∧ e₀ = m.factorization r₀ ∧
          U₀ = ordCompl[r₀] u ∧ u = r₀ ^ e₀ * U₀ ∧ Nat.Coprime (r₀ ^ e₀) U₀ ∧
          sigma 1 (r₀ ^ (2 * e₀)) = q * c₀_u ∧ ¬ q ∣ c₀_u ∧
          Nat.Coprime (r₀ ^ (2 * e₀)) c₀_u ∧
          W = c₀_u * sigma 1 (U₀ ^ 2) ∧
          c₀_u ∣ U₀ ^ 2 ∧ U₀ ^ 2 = c₀_u * V₀ ∧
          r₀ ^ (2 * e₀) * V₀ = sigma 1 (U₀ ^ 2) * sigma 1 (h ^ 2) ∧
          (W = 1 ↔ U₀ = 1) ∧
          (3 ≤ W ↔ 3 ≤ U₀) ∧
          (W = 1 ∨ 13 ≤ W) ∧
          (13 ≤ W → c₀_u * sigma 1 (h ^ 2) < r₀ ^ (2 * e₀) ∧ V₀ < sigma 1 (U₀ ^ 2))) ∧
      ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) → Nat.Coprime ((q + 1) / 2) (componentIndex N q) →
        ∃ h u W r₀ e₀ U₀ c₀_u V₀ : ℕ,
          W = sigma 1 (u ^ 2) / q ∧
          Odd h ∧ Odd u ∧ Odd W ∧ Odd U₀ ∧
          59 ≤ h ∧ 6961 ≤ q ∧ 71 ≤ U₀ ∧ 5113 ≤ W ∧
          2 ≤ u.primeFactors.card ∧
          Nat.Coprime h u ∧ Nat.Coprime h W ∧
          N = q * (h * u) ^ 2 ∧ componentIndex N q = u ^ 2 ∧
          u = r₀ ^ e₀ * U₀ ∧ W = c₀_u * sigma 1 (U₀ ^ 2) ∧ U₀ ^ 2 = c₀_u * V₀ ∧
          r₀ ^ (2 * e₀) * V₀ = sigma 1 (U₀ ^ 2) * sigma 1 (h ^ 2) ∧
          c₀_u * sigma 1 (h ^ 2) < r₀ ^ (2 * e₀) ∧
          608447 ≤ 2 * u ^ 2 - sigma 1 (u ^ 2)) ∧
      (1 < a → ∀ l t : ℕ, l.Prime → sigma 1 (m ^ 2) / q ^ a = l * t ^ 2 →
        let d := (a + 1) / 2
        ∃ y w z : ℕ,
          0 < y ∧ 0 < w ∧ 0 < z ∧
          y = d * w * z ∧ q + 1 = 2 * d * w ^ 2 ∧ q ^ d + 1 = 2 * y ^ 2 ∧
          (∀ r : ℕ, r.Prime → (r % 8 = 3 ∨ r % 8 = 5) → d ∣ r + 1 →
            ¬ (r : ℤ) ∣ (((silverUnit ^ ((r + 1) / d) : (ℤ√2)ˣ) : ℤ√2).im) →
            ¬ r ∣ y ∧ ¬ r ∣ w ∧ ¬ r ∣ z) ∧
          (d = 17 → ∀ r ∈ ({67, 101, 373, 509, 883, 1019, 1291, 1427} : Finset ℕ),
            ¬ r ∣ y ∧ ¬ r ∣ w ∧ ¬ r ∣ z) ∧
          (d = 73 → ∀ r ∈ ({1021, 1459, 5693, 6131, 6277, 7883, 8467, 9781} : Finset ℕ),
            ¬ r ∣ y ∧ ¬ r ∣ w ∧ ¬ r ∣ z) ∧
          (d = 241 → ∀ r ∈ ({3373, 7229, 9157, 18797, 22171, 33739, 45307, 47717} : Finset ℕ),
            ¬ r ∣ y ∧ ¬ r ∣ w ∧ ¬ r ∣ z)) := by
  obtain ⟨q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, _, _, _, _, _, _⟩ :=
    odd_perfect_tier2_waveJ_master_profile ho hN
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
  refine ⟨q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, ?_, ?_, ?_, ?_⟩
  · intro hfree
    obtain ⟨hS51_u, hS51_disj, hS51_card, hcol_eq, hloc_eq, h221⟩ :=
      sixth_power_free_S51_collision_repeat_split ho hN hq_mem hq4 he_q hev_N hfree
    obtain ⟨hQ23_bd, hω_11, h80⟩ :=
      sixth_power_free_oneModThreeLarge_ge_80 ho hN hq_mem hq4 he_q hev_N hfree
    obtain ⟨hω_ub, hpinch⟩ :=
      sixth_power_free_half_rank_bipartite_pinch ho hN hq_mem hq4 he_q hev_N hfree
    exact ⟨hS51_u, hS51_disj, hS51_card, hcol_eq, hloc_eq, h221,
      hQ23_bd, hω_11, h80, hω_ub, hpinch⟩
  · intro ha1 hcop
    have hform1 : N = q * m ^ 2 := by simpa [ha1] using hform
    obtain ⟨h, u, W, r₀, e₀, U₀, c₀_u, V₀,
      hW_def, hh_odd, hu_odd, hW_odd, hU₀_odd,
      hh_ge3, hu_ge3, hW_ge1, hU₀_ge1, hc₀_ge1, hV₀_ge1,
      hcop_hu, hcop_hW, hm_eq, hq_eq, hci_sq_eq,
      hr₀_prime, hr₀_u, hr₀_ndvd_h, he₀_pos,
      he₀_eq_u, he₀_eq_m, hU₀_def, hu_split, hcop_pow_U₀,
      hsig_r₀_eq, hq_ndvd_c₀, hcop_r₀_c₀, hW_eq,
      hc₀_dvd_U₀2, hU₀2_eq, hbal_V₀⟩ :=
      linear_euler_coprime_half_succ_unique_source_w_factorization ho hN hq hqm hform1 hcop
    obtain ⟨h₂, u₂, W₂, r₂, e₂, U₂, c₂, V₂,
      hW₂_def, hm₂_eq, hq₂_eq, hci₂_eq,
      hr₂_u, he₂_eq_u, hU₂_def, hsig_r₂_eq,
      hW₂_eq, hU₂2_eq, _,
      hW_iff_U1, hW3_iff_U3, hW_gap, hW13_imp⟩ :=
      linear_euler_coprime_half_succ_w_one_or_ge_thirteen ho hN hq hqm hform1 hcop
    have hh₂_ge3 : 3 ≤ h₂ := by
      have hu₂_eq' : u₂ = u :=
        Nat.pow_left_injective (by decide : 2 ≠ 0) (hci₂_eq.symm.trans hci_sq_eq)
      have hmul : h₂ * u = h * u := by
        calc
          h₂ * u = h₂ * u₂ := by rw [hu₂_eq']
          _ = m := hm₂_eq.symm
          _ = h * u := hm_eq
      have hh₂_eq' : h₂ = h := Nat.mul_right_cancel hu_odd.pos hmul
      omega
    obtain ⟨hh₂_eq, hu₂_eq, hW₂_eq_W⟩ :=
      align_waveK_coprime_witnesses hq_eq hh_ge3 hci_sq_eq hW_def
        hq₂_eq hh₂_ge3 hci₂_eq hW₂_def
    rw [hu₂_eq] at hr₂_u he₂_eq_u hU₂_def
    obtain ⟨_, r_src, hr_src_m, hq_dvd_src, _, _, _, huniq_src⟩ :=
      linear_euler_unique_q_source_and_bound ho hN hq hqm hform1
    have hr₀_m : r₀ ∈ m.primeFactors := by
      refine Nat.mem_primeFactors.mpr ⟨hr₀_prime, ?_, hm0⟩
      rw [hm_eq]
      exact (Nat.dvd_of_mem_primeFactors hr₀_u).trans (dvd_mul_left u h)
    have hq_dvd_r₀ : q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)) := by
      rw [← he₀_eq_m, hsig_r₀_eq]
      exact dvd_mul_right q c₀_u
    have hr₂_prime : r₂.Prime := Nat.prime_of_mem_primeFactors hr₂_u
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
    rw [hr₂_eq] at he₂_eq_u hU₂_def hsig_r₂_eq hW13_imp
    have he₂_eq : e₂ = e₀ := he₂_eq_u.trans he₀_eq_u.symm
    rw [he₂_eq] at hsig_r₂_eq hW13_imp
    have hU₂_eq : U₂ = U₀ := hU₂_def.trans hU₀_def.symm
    rw [hU₂_eq] at hU₂2_eq hW_iff_U1 hW3_iff_U3 hW13_imp
    have hc₂_eq : c₂ = c₀_u :=
      Nat.mul_left_cancel hq.pos (hsig_r₂_eq.symm.trans hsig_r₀_eq)
    rw [hc₂_eq] at hU₂2_eq hW13_imp
    have hV₂_eq : V₂ = V₀ :=
      Nat.mul_left_cancel hc₀_ge1 (hU₂2_eq.symm.trans hU₀2_eq)
    rw [hW₂_eq_W] at hW_iff_U1 hW3_iff_U3 hW_gap hW13_imp
    rw [hh₂_eq, hV₂_eq] at hW13_imp
    exact ⟨h, u, W, r₀, e₀, U₀, c₀_u, V₀,
      hW_def, hh_odd, hu_odd, hW_odd, hU₀_odd,
      hh_ge3, hu_ge3, hW_ge1, hU₀_ge1, hc₀_ge1, hV₀_ge1,
      hcop_hu, hcop_hW, hm_eq, hq_eq, hci_sq_eq,
      hr₀_prime, hr₀_u, hr₀_ndvd_h, he₀_pos,
      he₀_eq_u, he₀_eq_m, hU₀_def, hu_split, hcop_pow_U₀,
      hsig_r₀_eq, hq_ndvd_c₀, hcop_r₀_c₀, hW_eq,
      hc₀_dvd_U₀2, hU₀2_eq, hbal_V₀,
      hW_iff_U1, hW3_iff_U3, hW_gap, hW13_imp⟩
  · intro hfree hcop
    exact sixth_power_free_coprime_half_succ_w_ge_5113 ho hN hq_mem hq4 he_q hev_N hfree hcop
  · intro ha_gt1 l t hl hi d
    exact exceptional_euler_inert_prime_y_sieve hN ho hq hq4 ha4 ha_gt1 hqm hform hl hi

end OddPerfect
