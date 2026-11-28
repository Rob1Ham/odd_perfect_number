module

public import OddPerfect.LinearEulerCoprimeWFactorObstruction
public import OddPerfect.UniversalSigmaTotientObstruction
public import OddPerfect.PadicPadeHigherOrderContraction
public import OddPerfect.TridecupleRepunitObstruction
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Linear Euler Coprime Half-Successor Abundancy Pinch & `W = 1` Equivalence

Formalizes the universal deficiency pinch `sigma 1 (h ^ 2) + 3 ≤ 2 * h ^ 2`, strict
`φ(h)` / `φ(u)` totient envelopes, and the exact unconditional equivalence
`W = 1 ↔ u.primeFactors.card = 1` (`3 ≤ W ↔ 2 ≤ u.primeFactors.card`) on the coprime
half-successor branch `Nat.Coprime ((q + 1) / 2) (componentIndex N q)` of `N = q * m ^ 2`:

1. `linear_euler_coprime_half_succ_h_sq_deficient_bound`:
   Derives `sigma 1 (h ^ 2) + 3 ≤ 2 * h ^ 2`, `sigma 1 (h ^ 2) + 2 ≤ q`, and `¬ 105 ∣ h`.
2. `linear_euler_coprime_half_succ_totient_envelopes`:
   Derives strict `h.totient` and `u.totient` envelopes from `UniversalSigmaTotientObstruction`.
3. `linear_euler_coprime_half_succ_w_one_iff_prime_pow_u`:
   Proves `W = 1 ↔ u.primeFactors.card = 1`, `3 ≤ W ↔ 2 ≤ u.primeFactors.card`, and the
   tridecuple/Padé consequences when `W = 1`.
4. `sixth_power_free_coprime_half_succ_two_primes_in_u`:
   Combines `61 ≤ W` (`sixth_power_free_coprime_half_succ_w_ge_61`) with (1), (2), (3), and
   `¬ 3 ∣ N` to force `2 ≤ u.primeFactors.card`, `¬ 105 ∣ h`, and the `3`-free totient bounds.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma totient_sq_coprime (m : ℕ) : (m ^ 2).totient = m * m.totient := by
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · simp
  · have h := Nat.totient_gcd_mul_totient_mul m m
    rw [Nat.gcd_self, ← sq] at h
    have hphi_pos : 0 < m.totient := Nat.totient_pos.mpr hm_pos
    have h' : m.totient * (m ^ 2).totient = m.totient * (m * m.totient) := by
      rw [h]; ring
    exact Nat.mul_left_cancel hphi_pos h'

private lemma prime_pow_of_primeFactors_eq_singleton_pinch {n p : ℕ}
    (hn0 : n ≠ 0) (hp_sing : n.primeFactors = {p}) :
    p.Prime ∧ 0 < n.factorization p ∧ n = p ^ (n.factorization p) := by
  have hp_mem : p ∈ n.primeFactors := by rw [hp_sing]; exact Finset.mem_singleton_self p
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have he_pos : 0 < n.factorization p :=
    (hp_prime.dvd_iff_one_le_factorization hn0).mp (Nat.dvd_of_mem_primeFactors hp_mem)
  have hcompl_eq1 : ordCompl[p] n = 1 := by
    by_contra hne1
    obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd hne1
    have hr_mem : r ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hr_prime, hr_dvd.trans (Nat.ordCompl_dvd n p), hn0⟩
    rw [hp_sing, Finset.mem_singleton] at hr_mem
    exact Nat.not_dvd_ordCompl hp_prime hn0 (hr_mem ▸ hr_dvd)
  have hn_pow : n = p ^ (n.factorization p) := by
    have hmul := Nat.ordProj_mul_ordCompl_eq_self n p
    rw [hcompl_eq1, mul_one] at hmul
    exact hmul.symm
  exact ⟨hp_prime, he_pos, hn_pow⟩

private lemma coprime_half_succ_component_equations {N q m h u : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hm_eq : m = h * u) (hq_eq : q = 2 * h ^ 2 - 1) (hci_sq_eq : componentIndex N q = u ^ 2)
    (hh_ge3 : 3 ≤ h) :
    N = q ^ 1 * m ^ 2 ∧
    ¬ q ∣ m ^ 2 ∧
    sigma 1 (m ^ 2) = q ^ 1 * componentIndex N q ∧
    sigma 1 (q ^ 1) * componentIndex N q = 2 * m ^ 2 := by
  have hqm2 : ¬ q ∣ m ^ 2 := fun hd => hqm (hq.dvd_of_dvd_pow hd)
  have hform_pow : N = q ^ 1 * m ^ 2 := by simpa only [pow_one] using hform
  have hq_cop_m2 : q.Coprime (m ^ 2) := (hq.coprime_iff_not_dvd.mpr hqm).pow_right 2
  have hsig_N : sigma 1 N = 2 * N :=
    (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul ho.pos).mp hN)
  have hsig_q : sigma 1 q = q + 1 := by
    rw [← pow_one q, sigma_one_apply_prime_pow hq]
    simp [Finset.sum_range_succ]
    ring
  have hq1_eq : q + 1 = 2 * h ^ 2 := by
    have hh2_ge9 : 9 ≤ h ^ 2 := by nlinarith
    omega
  have hr_q : (q + 1) * componentIndex N q = 2 * m ^ 2 := by
    rw [hq1_eq, hci_sq_eq, hm_eq]
    ring
  have hl_q : sigma 1 (m ^ 2) = q * componentIndex N q := by
    have hmul : sigma 1 (q * m ^ 2) = sigma 1 q * sigma 1 (m ^ 2) :=
      isMultiplicative_sigma.map_mul_of_coprime hq_cop_m2
    have hsig_bal : (q + 1) * sigma 1 (m ^ 2) = 2 * (q * m ^ 2) := by
      rw [← hsig_q, ← hmul, ← hform, hsig_N, hform]
    have hq1_pos : 0 < q + 1 := Nat.succ_pos q
    apply Nat.mul_left_cancel hq1_pos
    calc
      (q + 1) * sigma 1 (m ^ 2) = 2 * (q * m ^ 2) := hsig_bal
      _ = q * (2 * m ^ 2) := by ring
      _ = q * ((q + 1) * componentIndex N q) := by rw [hr_q]
      _ = (q + 1) * (q * componentIndex N q) := by ring
  exact ⟨hform_pow, hqm2, by simpa only [pow_one] using hl_q,
    by simpa only [pow_one, hsig_q] using hr_q⟩

private lemma sigma_11025_eq : sigma 1 11025 = 22971 := by
  have h1 : (11025 : ℕ) = 3 ^ 2 * (5 ^ 2 * 7 ^ 2) := by norm_num
  have hcop1 : Nat.Coprime (3 ^ 2) (5 ^ 2 * 7 ^ 2) := by decide
  have hcop2 : Nat.Coprime (5 ^ 2) (7 ^ 2) := by decide
  rw [h1, isMultiplicative_sigma.map_mul_of_coprime hcop1,
    isMultiplicative_sigma.map_mul_of_coprime hcop2,
    sigma_one_apply_prime_pow (by decide : Nat.Prime 3),
    sigma_one_apply_prime_pow (by decide : Nat.Prime 5),
    sigma_one_apply_prime_pow (by decide : Nat.Prime 7)]
  norm_num [Finset.sum_range_succ]

private lemma sigma_mul_le_sigma_mul {d k : ℕ} (hk : 0 < k) :
    sigma 1 d * k ≤ sigma 1 (d * k) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have hdk_ne0 : d * k ≠ 0 := (Nat.mul_pos hd hk).ne'
    have himg : d.divisors.image (· * k) ⊆ (d * k).divisors := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_right (Nat.dvd_of_mem_divisors hx) k, hdk_ne0⟩
    have hinj : Function.Injective (· * k : ℕ → ℕ) := fun a b hab =>
      Nat.mul_right_cancel hk hab
    rw [sigma_one_apply, sigma_one_apply]
    calc
      (∑ x ∈ d.divisors, x) * k = ∑ x ∈ d.divisors, x * k := Finset.sum_mul d.divisors id k
      _ = ∑ y ∈ d.divisors.image (· * k), y :=
          (Finset.sum_image (f := id) fun _ _ _ _ h => hinj h).symm
      _ ≤ ∑ y ∈ (d * k).divisors, y := Finset.sum_le_sum_of_subset himg

/-- **1. Universal `h^2` Deficiency Pinch and `¬ 105 ∣ h`**:
On the coprime half-successor branch `Nat.Coprime ((q + 1) / 2) (componentIndex N q)` of `N = q * m ^ 2`,
`u ^ 2 < sigma 1 (u ^ 2)` forces `sigma 1 (h ^ 2) < q = 2 * h ^ 2 - 1`; since `sigma 1 (h ^ 2)` is odd,
this sharpens to `sigma 1 (h ^ 2) + 3 ≤ 2 * h ^ 2` and `sigma 1 (h ^ 2) + 2 ≤ q`, excluding `105 ∣ h`. -/
theorem linear_euler_coprime_half_succ_h_sq_deficient_bound {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hcop : Nat.Coprime ((q + 1) / 2) (componentIndex N q)) :
    ∃ h u W : ℕ,
      W = sigma 1 (u ^ 2) / q ∧
      Odd h ∧ Odd u ∧ Odd W ∧ 3 ≤ h ∧ 3 ≤ u ∧ 1 ≤ W ∧
      Nat.Coprime h u ∧ Nat.Coprime h W ∧
      m = h * u ∧ q = 2 * h ^ 2 - 1 ∧ componentIndex N q = u ^ 2 ∧
      u ^ 2 = W * sigma 1 (h ^ 2) ∧ sigma 1 (u ^ 2) = W * (2 * h ^ 2 - 1) ∧
      sigma 1 (h ^ 2) + 3 ≤ 2 * h ^ 2 ∧
      sigma 1 (h ^ 2) + 2 ≤ q ∧
      ¬ 105 ∣ h := by
  obtain ⟨h, u, W, hW_def, hh_odd, hu_odd, hW_odd, hh_ge3, hu_ge3, hW_ge1, hcop_hu, hcop_hW,
    hm_eq, hq_eq, hci_sq_eq, hu2_eq, hsigu2_eq, _, _, _, _, _, _, _⟩ :=
    linear_euler_coprime_half_succ_quotient_system ho hN hq hqm hform hcop
  have hu2_gt1 : 1 < u ^ 2 := by nlinarith
  have hu2_lt_sig : u ^ 2 < sigma 1 (u ^ 2) := self_lt_sigma_of_one_lt hu2_gt1
  have hsigh2_lt : sigma 1 (h ^ 2) < 2 * h ^ 2 - 1 := by
    have hmul : W * sigma 1 (h ^ 2) < W * (2 * h ^ 2 - 1) := by
      rw [← hu2_eq, ← hsigu2_eq]
      exact hu2_lt_sig
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hsigh2_odd : Odd (sigma 1 (h ^ 2)) :=
    (odd_sigma_iff_square_of_odd hh_odd.pow).mpr ⟨h, sq h⟩
  have hh2_pos : 1 ≤ h ^ 2 := by nlinarith
  have hdef3 : sigma 1 (h ^ 2) + 3 ≤ 2 * h ^ 2 := by
    obtain ⟨t, ht⟩ := hsigh2_odd
    omega
  have hdef2 : sigma 1 (h ^ 2) + 2 ≤ q := by
    obtain ⟨t, ht⟩ := hsigh2_odd
    omega
  have h105 : ¬ 105 ∣ h := by
    intro hd105
    obtain ⟨k, hk⟩ := hd105
    have hk_pos : 0 < k := by
      by_contra! hk0
      have hk_eq0 : k = 0 := by omega
      rw [hk_eq0, mul_zero] at hk
      omega
    have hk2_pos : 0 < k ^ 2 := pow_pos hk_pos 2
    have hh2_eq : h ^ 2 = 11025 * k ^ 2 := by rw [hk]; ring
    have hsig_lb : 22971 * k ^ 2 ≤ sigma 1 (h ^ 2) := by
      rw [hh2_eq, ← sigma_11025_eq]
      exact sigma_mul_le_sigma_mul hk2_pos
    have h2h2_eq : 2 * h ^ 2 = 22050 * k ^ 2 := by rw [hh2_eq]; ring
    nlinarith
  exact ⟨h, u, W, hW_def, hh_odd, hu_odd, hW_odd, hh_ge3, hu_ge3, hW_ge1, hcop_hu, hcop_hW,
    hm_eq, hq_eq, hci_sq_eq, hu2_eq, hsigu2_eq, hdef3, hdef2, h105⟩

/-- **2. Strict `φ(h)` and `φ(u)` Totient Envelopes**:
Applies `odd_sigma_mul_totient_strict_of_isSquare` and `odd_sigma_mul_totient_identities_and_bounds`
to both `h ^ 2` and `u ^ 2` on the coprime half-successor branch. -/
theorem linear_euler_coprime_half_succ_totient_envelopes {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hcop : Nat.Coprime ((q + 1) / 2) (componentIndex N q)) :
    ∃ h u W : ℕ,
      W = sigma 1 (u ^ 2) / q ∧
      Odd h ∧ Odd u ∧ Odd W ∧ 3 ≤ h ∧ 3 ≤ u ∧ 1 ≤ W ∧
      m = h * u ∧ q = 2 * h ^ 2 - 1 ∧ componentIndex N q = u ^ 2 ∧
      sigma 1 (h ^ 2) + 3 ≤ 2 * h ^ 2 ∧
      (3 * h.primeFactors.card + 5) * h < 2 * (4 * h.primeFactors.card + 5) * h.totient ∧
      3 * h < 8 * h.totient ∧
      (¬ 3 ∣ N → 27 * h < 64 * h.totient) ∧
      (3 * u.primeFactors.card + 5) * u ^ 3 <
        (4 * u.primeFactors.card + 5) * W * (2 * h ^ 2 - 1) * u.totient ∧
      3 * u ^ 3 < 4 * W * (2 * h ^ 2 - 1) * u.totient ∧
      (¬ 3 ∣ N → 27 * u ^ 3 < 32 * W * (2 * h ^ 2 - 1) * u.totient) := by
  obtain ⟨h, u, W, hW_def, hh_odd, hu_odd, hW_odd, hh_ge3, hu_ge3, hW_ge1, _, _,
    hm_eq, hq_eq, hci_sq_eq, _, hsigu2_eq, hdef3, _, _⟩ :=
    linear_euler_coprime_half_succ_h_sq_deficient_bound ho hN hq hqm hform hcop
  have hh_pos : 0 < h := by omega
  have hu_pos : 0 < u := by omega
  have hh2_odd : Odd (h ^ 2) := hh_odd.pow
  have hu2_odd : Odd (u ^ 2) := hu_odd.pow
  have hh2_gt1 : 1 < h ^ 2 := by nlinarith
  have hu2_gt1 : 1 < u ^ 2 := by nlinarith
  have hh2_pf : (h ^ 2).primeFactors = h.primeFactors := Nat.primeFactors_pow h (by decide : 2 ≠ 0)
  have hu2_pf : (u ^ 2).primeFactors = u.primeFactors := Nat.primeFactors_pow u (by decide : 2 ≠ 0)
  have hh2_tot : (h ^ 2).totient = h * h.totient := totient_sq_coprime h
  have hu2_tot : (u ^ 2).totient = u * u.totient := totient_sq_coprime u
  have hh_bounds := odd_sigma_mul_totient_identities_and_bounds hh2_odd hh2_gt1
  have hh_strict := odd_sigma_mul_totient_strict_of_isSquare hh2_odd hh2_gt1 ⟨h, sq h⟩
  have hu_bounds := odd_sigma_mul_totient_identities_and_bounds hu2_odd hu2_gt1
  have hu_strict := odd_sigma_mul_totient_strict_of_isSquare hu2_odd hu2_gt1 ⟨u, sq u⟩
  have hh_phi_pos : 0 < h.totient := Nat.totient_pos.mpr hh_pos
  have hsigh2_lt : sigma 1 (h ^ 2) < 2 * h ^ 2 := by omega
  have hh_env1 : (3 * h.primeFactors.card + 5) * h < 2 * (4 * h.primeFactors.card + 5) * h.totient := by
    have h0 := hh_strict.1
    rw [hh2_pf, hh2_tot] at h0
    have hmul : h ^ 3 * ((3 * h.primeFactors.card + 5) * h) <
        h ^ 3 * (2 * (4 * h.primeFactors.card + 5) * h.totient) := by
      calc
        h ^ 3 * ((3 * h.primeFactors.card + 5) * h)
            = (3 * h.primeFactors.card + 5) * (h ^ 2) ^ 2 := by ring
        _ < (4 * h.primeFactors.card + 5) * (sigma 1 (h ^ 2) * (h * h.totient)) := h0
        _ < (4 * h.primeFactors.card + 5) * ((2 * h ^ 2) * (h * h.totient)) := by
            have h1 : sigma 1 (h ^ 2) * (h * h.totient) < (2 * h ^ 2) * (h * h.totient) :=
              Nat.mul_lt_mul_of_pos_right hsigh2_lt (Nat.mul_pos hh_pos hh_phi_pos)
            exact Nat.mul_lt_mul_of_pos_left h1 (by omega)
        _ = h ^ 3 * (2 * (4 * h.primeFactors.card + 5) * h.totient) := by ring
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hh_env2 : 3 * h < 8 * h.totient := by
    have h0 := hh_bounds.2.2.2.2.1
    rw [hh2_tot] at h0
    have hmul : h ^ 3 * (3 * h) < h ^ 3 * (8 * h.totient) := by
      calc
        h ^ 3 * (3 * h) = 3 * (h ^ 2) ^ 2 := by ring
        _ < 4 * (sigma 1 (h ^ 2) * (h * h.totient)) := h0
        _ < 4 * ((2 * h ^ 2) * (h * h.totient)) := by
            have h1 : sigma 1 (h ^ 2) * (h * h.totient) < (2 * h ^ 2) * (h * h.totient) :=
              Nat.mul_lt_mul_of_pos_right hsigh2_lt (Nat.mul_pos hh_pos hh_phi_pos)
            exact Nat.mul_lt_mul_of_pos_left h1 (by decide)
        _ = h ^ 3 * (8 * h.totient) := by ring
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hh_env3 : ¬ 3 ∣ N → 27 * h < 64 * h.totient := by
    intro hn3
    have hn3_h2 : ¬ 3 ∣ h ^ 2 := fun hd => by
      apply hn3
      have hdiv : h ^ 2 ∣ N := by
        rw [hform, hm_eq, mul_pow]
        exact (dvd_mul_right (h ^ 2) (u ^ 2)).trans (dvd_mul_left _ q)
      exact hd.trans hdiv
    have h0 := hh_bounds.2.2.2.2.2 hn3_h2
    rw [hh2_tot] at h0
    have hmul : h ^ 3 * (27 * h) < h ^ 3 * (64 * h.totient) := by
      calc
        h ^ 3 * (27 * h) = 27 * (h ^ 2) ^ 2 := by ring
        _ < 32 * (sigma 1 (h ^ 2) * (h * h.totient)) := h0
        _ < 32 * ((2 * h ^ 2) * (h * h.totient)) := by
            have h1 : sigma 1 (h ^ 2) * (h * h.totient) < (2 * h ^ 2) * (h * h.totient) :=
              Nat.mul_lt_mul_of_pos_right hsigh2_lt (Nat.mul_pos hh_pos hh_phi_pos)
            exact Nat.mul_lt_mul_of_pos_left h1 (by decide)
        _ = h ^ 3 * (64 * h.totient) := by ring
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hu_env1 : (3 * u.primeFactors.card + 5) * u ^ 3 <
      (4 * u.primeFactors.card + 5) * W * (2 * h ^ 2 - 1) * u.totient := by
    have h0 := hu_strict.1
    rw [hu2_pf, hu2_tot, hsigu2_eq] at h0
    have hmul : u * ((3 * u.primeFactors.card + 5) * u ^ 3) <
        u * ((4 * u.primeFactors.card + 5) * W * (2 * h ^ 2 - 1) * u.totient) := by
      calc
        u * ((3 * u.primeFactors.card + 5) * u ^ 3)
            = (3 * u.primeFactors.card + 5) * (u ^ 2) ^ 2 := by ring
        _ < (4 * u.primeFactors.card + 5) * (W * (2 * h ^ 2 - 1) * (u * u.totient)) := h0
        _ = u * ((4 * u.primeFactors.card + 5) * W * (2 * h ^ 2 - 1) * u.totient) := by ring
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hu_env2 : 3 * u ^ 3 < 4 * W * (2 * h ^ 2 - 1) * u.totient := by
    have h0 := hu_bounds.2.2.2.2.1
    rw [hu2_tot, hsigu2_eq] at h0
    have hmul : u * (3 * u ^ 3) < u * (4 * W * (2 * h ^ 2 - 1) * u.totient) := by
      calc
        u * (3 * u ^ 3) = 3 * (u ^ 2) ^ 2 := by ring
        _ < 4 * (W * (2 * h ^ 2 - 1) * (u * u.totient)) := h0
        _ = u * (4 * W * (2 * h ^ 2 - 1) * u.totient) := by ring
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hu_env3 : ¬ 3 ∣ N → 27 * u ^ 3 < 32 * W * (2 * h ^ 2 - 1) * u.totient := by
    intro hn3
    have hn3_u2 : ¬ 3 ∣ u ^ 2 := fun hd => by
      apply hn3
      have hdiv : u ^ 2 ∣ N := by
        rw [hform, hm_eq, mul_pow]
        exact (dvd_mul_left (u ^ 2) (h ^ 2)).trans (dvd_mul_left _ q)
      exact hd.trans hdiv
    have h0 := hu_bounds.2.2.2.2.2 hn3_u2
    rw [hu2_tot, hsigu2_eq] at h0
    have hmul : u * (27 * u ^ 3) < u * (32 * W * (2 * h ^ 2 - 1) * u.totient) := by
      calc
        u * (27 * u ^ 3) = 27 * (u ^ 2) ^ 2 := by ring
        _ < 32 * (W * (2 * h ^ 2 - 1) * (u * u.totient)) := h0
        _ = u * (32 * W * (2 * h ^ 2 - 1) * u.totient) := by ring
    exact Nat.lt_of_mul_lt_mul_left hmul
  exact ⟨h, u, W, hW_def, hh_odd, hu_odd, hW_odd, hh_ge3, hu_ge3, hW_ge1,
    hm_eq, hq_eq, hci_sq_eq, hdef3, hh_env1, hh_env2, hh_env3, hu_env1, hu_env2, hu_env3⟩

/-- **3. Exact `W = 1 ↔ ω(u) = 1` Equivalence and Tridecuple/Padé Lift**:
Unconditionally on the coprime half-successor branch `Nat.Coprime ((q + 1) / 2) (componentIndex N q)`,
`W = 1 ↔ u.primeFactors.card = 1` (equivalently `3 ≤ W ↔ 2 ≤ u.primeFactors.card`), and `W = 1`
lifts to `2 ≤ h.primeFactors.card`, `16 ≤ N.primeFactors.card`, `1154 ≤ e`,
`13082761331670028 ≤ 2 * e`, and `10 ^ 12 * p < 6 ^ e`. -/
theorem linear_euler_coprime_half_succ_w_one_iff_prime_pow_u {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hcop : Nat.Coprime ((q + 1) / 2) (componentIndex N q)) :
    ∃ h u W : ℕ,
      W = sigma 1 (u ^ 2) / q ∧
      Odd h ∧ Odd u ∧ Odd W ∧ 3 ≤ h ∧ 3 ≤ u ∧ 1 ≤ W ∧
      m = h * u ∧ q = 2 * h ^ 2 - 1 ∧ componentIndex N q = u ^ 2 ∧
      u ^ 2 = W * sigma 1 (h ^ 2) ∧ sigma 1 (u ^ 2) = W * (2 * h ^ 2 - 1) ∧
      (W = 1 ↔ u.primeFactors.card = 1) ∧
      (3 ≤ W ↔ 2 ≤ u.primeFactors.card) ∧
      (W = 1 →
        2 ≤ h.primeFactors.card ∧
        16 ≤ N.primeFactors.card ∧
        ∃ p e : ℕ,
          p.Prime ∧ 1154 ≤ e ∧ 13082761331670028 ≤ 2 * e ∧
          u = p ^ e ∧ componentIndex N q = p ^ (2 * e) ∧
          10 ^ 12 * p < 6 ^ e) := by
  obtain ⟨h, u, W, hW_def, hh_odd, hu_odd, hW_odd, hh_ge3, hu_ge3, hW_ge1, _, _,
    hm_eq, hq_eq, hci_sq_eq, hu2_eq, hsigu2_eq, _, _, _, _, hW_iff_sig, _, hW1_imp⟩ :=
    linear_euler_coprime_half_succ_quotient_system ho hN hq hqm hform hcop
  have hu0 : u ≠ 0 := hu_odd.pos.ne'
  obtain ⟨hform_pow, hqm2, hl, hr⟩ :=
    coprime_half_succ_component_equations ho hN hq hqm hform hm_eq hq_eq hci_sq_eq hh_ge3
  have hW_iff_card1 : W = 1 ↔ u.primeFactors.card = 1 := by
    constructor
    · intro hW1
      obtain ⟨⟨p, e, hp_prime, he_pos, hu_pow, _⟩, _⟩ := hW1_imp hW1
      rw [hu_pow, Nat.primeFactors_prime_pow he_pos.ne' hp_prime, Finset.card_singleton]
    · intro hcard1
      obtain ⟨p, hp_sing⟩ := Finset.card_eq_one.mp hcard1
      obtain ⟨hp_prime, he_pos, hu_pow⟩ := prime_pow_of_primeFactors_eq_singleton_pinch hu0 hp_sing
      set e := u.factorization p
      have hci_pow : componentIndex N q = p ^ (2 * e) := by
        rw [hci_sq_eq, hu_pow, ← pow_mul, mul_comm]
      have hσ_q :=
        (even_prime_power_index_eq_selected_sigma hN ho hq (by decide : 0 < 1)
          hform_pow hqm2 hl hr hp_prime he_pos hci_pow).2
      have hσu2_q : sigma 1 (u ^ 2) = q := by
        rw [hu_pow, ← pow_mul, mul_comm]
        exact hσ_q
      exact hW_iff_sig.mpr hσu2_q
  have hW3_iff_card2 : 3 ≤ W ↔ 2 ≤ u.primeFactors.card := by
    have hW_ne1_iff : W ≠ 1 ↔ 3 ≤ W := by
      obtain ⟨k, hk⟩ := hW_odd
      omega
    have hu_pf_ge1 : 1 ≤ u.primeFactors.card := by
      have hu_ne1 : u ≠ 1 := by omega
      obtain ⟨r, hr⟩ := Nat.exists_prime_and_dvd hu_ne1
      exact Finset.card_pos.mpr ⟨r, Nat.mem_primeFactors.mpr ⟨hr.1, hr.2, hu0⟩⟩
    have hu_ne1_iff : u.primeFactors.card ≠ 1 ↔ 2 ≤ u.primeFactors.card := by omega
    rw [← hW_ne1_iff, ← hu_ne1_iff]
    exact not_congr hW_iff_card1
  have hW1_lift : W = 1 →
      2 ≤ h.primeFactors.card ∧
      16 ≤ N.primeFactors.card ∧
      ∃ p e : ℕ,
        p.Prime ∧ 1154 ≤ e ∧ 13082761331670028 ≤ 2 * e ∧
        u = p ^ e ∧ componentIndex N q = p ^ (2 * e) ∧
        10 ^ 12 * p < 6 ^ e := by
    intro hW1
    obtain ⟨⟨p, e, hp_prime, he_pos, hu_pow, hci_pow⟩, hh_pf_ge2⟩ := hW1_imp hW1
    obtain ⟨⟨he_ge1154, h10_p, _, _⟩, _⟩ :=
      even_prime_power_primorial_repunit_length_cap hN ho hq (by decide : 0 < 1)
        hform_pow hqm2 hl hr hp_prime he_pos hci_pow
    obtain ⟨_, hN_ge16⟩ :=
      even_prime_power_component_forces_thirteen_repunits_and_sixteen_primes hN ho hq
        (by decide : 0 < 1) hform_pow hqm2 hl hr hp_prime he_pos hci_pow
    obtain ⟨h2e_ge, _, _⟩ :=
      even_prime_power_component_size_gt_ten_pow_353234555955090756 hN ho hq
        (by decide : 0 < 1) hform_pow hqm2 hl hr hp_prime (by omega : 0 < 2 * e)
        (even_two_mul e) hci_pow
    exact ⟨hh_pf_ge2, hN_ge16, p, e, hp_prime, he_ge1154, h2e_ge, hu_pow, hci_pow, h10_p⟩
  exact ⟨h, u, W, hW_def, hh_odd, hu_odd, hW_odd, hh_ge3, hu_ge3, hW_ge1,
    hm_eq, hq_eq, hci_sq_eq, hu2_eq, hsigu2_eq, hW_iff_card1, hW3_iff_card2, hW1_lift⟩

private lemma align_coprime_half_succ_witnesses
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

/-- **4. Sixth-Power-Free Coprime Half-Successor Synthesis (`2 ≤ ω(u)`)**:
Combines `61 ≤ W` (`sixth_power_free_coprime_half_succ_w_ge_61`) with (1), (2), (3), and
`¬ 3 ∣ N` (`sixth_power_free_three_not_dvd`) to establish `2 ≤ u.primeFactors.card`, `¬ 105 ∣ h`,
`sigma 1 (h ^ 2) + 3 ≤ 2 * h ^ 2`, and the `3`-free totient envelopes for `h` and `u`. -/
theorem sixth_power_free_coprime_half_succ_two_primes_in_u {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hcop : Nat.Coprime ((q + 1) / 2) (componentIndex N q)) :
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
      7259 ≤ 2 * u ^ 2 - sigma 1 (u ^ 2) := by
  obtain ⟨h, u, W, hW_def, hh_odd, hu_odd, hW_odd, hh_ge59, hq_ge6961, hW_ge61,
    hcop_hu, hcop_hW, hform_hu, hci_sq_eq, hu2_eq, hsigu2_eq, _, h7259_le, _⟩ :=
    sixth_power_free_coprime_half_succ_w_ge_61 ho hN hq hq4 he hev hfree hcop
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hfac_q : N.factorization q = 1 :=
    sixth_power_free_euler_exponent_one ho hN hq he hfree
  have hqm : ¬ q ∣ h * u := by
    intro hqd
    have hq3_dvd : q ^ 3 ∣ N := by
      rw [hform_hu]
      have hq2_dvd : q ^ 2 ∣ (h * u) ^ 2 := pow_dvd_pow_of_dvd hqd 2
      have hmul : q * q ^ 2 ∣ q * (h * u) ^ 2 := Nat.mul_dvd_mul_left q hq2_dvd
      rwa [show q * q ^ 2 = q ^ 3 by ring] at hmul
    have hle : 3 ≤ N.factorization q :=
      (hq_prime.pow_dvd_iff_le_factorization hN.2.ne').mp hq3_dvd
    omega
  have hq_eq : q = 2 * h ^ 2 - 1 := by
    have hsig_N : sigma 1 N = 2 * N :=
      (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul ho.pos).mp hN)
    have hq_cop_m2 : q.Coprime ((h * u) ^ 2) := (hq_prime.coprime_iff_not_dvd.mpr hqm).pow_right 2
    have hsig_q : sigma 1 q = q + 1 := by
      rw [← pow_one q, sigma_one_apply_prime_pow hq_prime]
      simp [Finset.sum_range_succ]
      ring
    have hmul : sigma 1 (q * (h * u) ^ 2) = (q + 1) * sigma 1 ((h * u) ^ 2) := by
      rw [isMultiplicative_sigma.map_mul_of_coprime hq_cop_m2, hsig_q]
    have hsig_bal : (q + 1) * sigma 1 ((h * u) ^ 2) = 2 * (q * (h * u) ^ 2) := by
      rw [← hmul, ← hform_hu, hsig_N, hform_hu]
    have hsig_sq : sigma 1 ((h * u) ^ 2) = sigma 1 (h ^ 2) * sigma 1 (u ^ 2) := by
      rw [mul_pow, isMultiplicative_sigma.map_mul_of_coprime ((hcop_hu.pow_left 2).pow_right 2)]
    have hm_ne0 : h * u ≠ 0 := mul_ne_zero hh_odd.pos.ne' hu_odd.pos.ne'
    have hm2_ne0 : (h * u) ^ 2 ≠ 0 := pow_ne_zero 2 hm_ne0
    have hN_fac_q : N.factorization q = 1 := hfac_q
    have hord_q : ordProj[q] N = q := by rw [hN_fac_q, pow_one]
    have hcompl_q : ordCompl[q] N = (h * u) ^ 2 := by
      rw [hN_fac_q, pow_one, hform_hu, Nat.mul_div_cancel_left _ hq_prime.pos]
    have hci_eq : componentIndex N q = sigma 1 ((h * u) ^ 2) / q := by
      rw [componentIndex, hcompl_q, hord_q]
    have hq_cop_q1 : q.Coprime (q + 1) :=
      hq_prime.coprime_iff_not_dvd.mpr fun hd =>
        hq_prime.not_dvd_one ((Nat.dvd_add_right (dvd_refl q)).mp hd)
    have hq_dvd_m2 : q ∣ sigma 1 ((h * u) ^ 2) :=
      hq_cop_q1.dvd_of_dvd_mul_left ⟨2 * (h * u) ^ 2, by rw [hsig_bal]; ring⟩
    have hsig_m2_eq : sigma 1 ((h * u) ^ 2) = q * u ^ 2 := by
      rw [← hci_sq_eq, hci_eq]
      exact (Nat.mul_div_cancel' hq_dvd_m2).symm
    have hW_sig_pos : 0 < W * sigma 1 (h ^ 2) :=
      Nat.mul_pos (by omega) (sigma_pos 1 (h ^ 2) (pow_ne_zero 2 hh_odd.pos.ne'))
    have hprod_eq : (W * sigma 1 (h ^ 2)) * q = (W * sigma 1 (h ^ 2)) * (2 * h ^ 2 - 1) := by
      calc
        (W * sigma 1 (h ^ 2)) * q = q * (W * sigma 1 (h ^ 2)) := by ring
        _ = q * u ^ 2 := by rw [hu2_eq]
        _ = sigma 1 ((h * u) ^ 2) := hsig_m2_eq.symm
        _ = sigma 1 (h ^ 2) * sigma 1 (u ^ 2) := hsig_sq
        _ = sigma 1 (h ^ 2) * (W * (2 * h ^ 2 - 1)) := by rw [hsigu2_eq]
        _ = (W * sigma 1 (h ^ 2)) * (2 * h ^ 2 - 1) := by ring
    exact Nat.mul_left_cancel hW_sig_pos hprod_eq
  have hh_ge3 : 3 ≤ h := by omega
  have hnot3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  obtain ⟨h₁, u₁, W₁, hW₁_def, _, _, _, hh₁_ge3, _, _, _, _, _, hq₁_eq, hci₁_eq, _, _,
    hdef3₁, _, h105₁⟩ :=
    linear_euler_coprime_half_succ_h_sq_deficient_bound ho hN hq_prime hqm hform_hu hcop
  obtain ⟨hh₁_eq, _, _⟩ :=
    align_coprime_half_succ_witnesses hq_eq hh_ge3 hci_sq_eq hW_def hq₁_eq hh₁_ge3 hci₁_eq hW₁_def
  obtain ⟨h₂, u₂, W₂, hW₂_def, _, _, _, hh₂_ge3, _, _, _, hq₂_eq, hci₂_eq, _, _, _, hh_env3₂,
    _, _, hu_env3₂⟩ :=
    linear_euler_coprime_half_succ_totient_envelopes ho hN hq_prime hqm hform_hu hcop
  obtain ⟨hh₂_eq, hu₂_eq, hW₂_eq⟩ :=
    align_coprime_half_succ_witnesses hq_eq hh_ge3 hci_sq_eq hW_def hq₂_eq hh₂_ge3 hci₂_eq hW₂_def
  obtain ⟨h₃, u₃, W₃, hW₃_def, _, _, _, hh₃_ge3, _, _, _, hq₃_eq, hci₃_eq, _, _, _,
    hW3_iff_card2, _⟩ :=
    linear_euler_coprime_half_succ_w_one_iff_prime_pow_u ho hN hq_prime hqm hform_hu hcop
  obtain ⟨_, hu₃_eq, hW₃_eq⟩ :=
    align_coprime_half_succ_witnesses hq_eq hh_ge3 hci_sq_eq hW_def hq₃_eq hh₃_ge3 hci₃_eq hW₃_def
  rw [hh₁_eq] at hdef3₁ h105₁
  have hh_tot_bound : 27 * h < 64 * h.totient := by
    simpa only [hh₂_eq] using hh_env3₂ hnot3
  have hu_tot_bound : 27 * u ^ 3 < 32 * W * (2 * h ^ 2 - 1) * u.totient := by
    simpa only [hh₂_eq, hu₂_eq, hW₂_eq] using hu_env3₂ hnot3
  have hu_pf_ge2 : 2 ≤ u.primeFactors.card := by
    rw [← hu₃_eq]
    exact hW3_iff_card2.mp (by rw [hW₃_eq]; omega)
  exact ⟨h, u, W, hW_def, hh_odd, hu_odd, hW_odd, hh_ge59, hq_ge6961, hW_ge61, hu_pf_ge2,
    hcop_hu, hcop_hW, hform_hu, hci_sq_eq, hu2_eq, hsigu2_eq, hdef3₁, h105₁,
    hh_tot_bound, hu_tot_bound, h7259_le⟩

end OddPerfect
