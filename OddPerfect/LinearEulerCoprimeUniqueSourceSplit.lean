module

public import OddPerfect.LinearEulerCoprimeAbundancyPinch
import OddPerfect.TothSplitExistence
import OddPerfect.SixthPowerFreeEuler
import OddPerfect.OddValuationCycleObstruction
import OddPerfect.GlobalWave5Obstruction
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Linear Euler Coprime Half-Successor Unique `q`-Source Split & `W` Gap

Formalizes the exact unique `q`-source decomposition of `u` and `W` on the coprime
half-successor branch `Nat.Coprime ((q + 1) / 2) (componentIndex N q)` of a linear Euler
odd perfect number `N = q * m ^ 2`:

1. `linear_euler_coprime_half_succ_unique_source_w_factorization`:
   Factorizes `u = r₀ ^ e₀ * U₀` (`e₀ = u.factorization r₀ = m.factorization r₀`,
   `U₀ = ordCompl[r₀] u`) and `σ(r₀ ^ (2 * e₀)) = q * c₀_u`, deriving `W = c₀_u * σ(U₀ ^ 2)`,
   `c₀_u ∣ U₀ ^ 2` (`U₀ ^ 2 = c₀_u * V₀`), and `r₀ ^ (2 * e₀) * V₀ = σ(U₀ ^ 2) * σ(h ^ 2)`.
2. `linear_euler_coprime_half_succ_w_one_or_ge_thirteen`:
   Establishes `W = 1 ↔ U₀ = 1`, `3 ≤ W ↔ 3 ≤ U₀`, the unconditional gap `W = 1 ∨ 13 ≤ W`,
   and the contraction inequalities `c₀_u * σ(h ^ 2) < r₀ ^ (2 * e₀)` and `V₀ < σ(U₀ ^ 2)`
   whenever `13 ≤ W`.
3. `sixth_power_free_coprime_half_succ_w_ge_5113`:
   Specializes to sixth-power-free odd perfect numbers, combining `¬ 3 ∣ N`,
   `53 ≤ s`, `s % 5 = 1 ∨ s % 3 = 1`, and `¬ 3 ∣ σ(s ^ (2 * v_s(U₀)))` to force `71 ≤ U₀`,
   `5113 ≤ W`, and `608447 ≤ 2 * u ^ 2 - σ(u ^ 2)`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma sq_add_self_add_one_le_sigma_sq {h : ℕ} (hh : 3 ≤ h) :
    h ^ 2 + h + 1 ≤ sigma 1 (h ^ 2) := by
  have hh0 : h ≠ 0 := by omega
  have hh2_ne0 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh0
  have h1_mem : 1 ∈ (h ^ 2).divisors := Nat.mem_divisors.mpr ⟨one_dvd _, hh2_ne0⟩
  have hh_mem : h ∈ (h ^ 2).divisors :=
    Nat.mem_divisors.mpr ⟨dvd_pow_self h (by decide : 2 ≠ 0), hh2_ne0⟩
  have hh2_mem : h ^ 2 ∈ (h ^ 2).divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hh2_ne0⟩
  have hlt1 : 1 < h := by omega
  have hlt2 : h < h ^ 2 := by nlinarith
  have hsub : ({1, h, h ^ 2} : Finset ℕ) ⊆ (h ^ 2).divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact h1_mem
    · exact hh_mem
    · exact hh2_mem
  have hsum_le : ∑ d ∈ ({1, h, h ^ 2} : Finset ℕ), d ≤ sigma 1 (h ^ 2) := by
    rw [sigma_one_apply]
    exact Finset.sum_le_sum_of_subset hsub
  have h1_notin : (1 : ℕ) ∉ ({h, h ^ 2} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hh_notin : h ∉ ({h ^ 2} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    omega
  rw [Finset.sum_insert h1_notin, Finset.sum_insert hh_notin, Finset.sum_singleton] at hsum_le
  omega

private lemma align_coprime_half_succ_witnesses_split
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

private lemma sigma_prime_pow_coprime_base {p k : ℕ} (hp : p.Prime) :
    Nat.Coprime p (sigma 1 (p ^ k)) := by
  rw [sigma_one_apply_prime_pow hp, Finset.sum_range_succ']
  simp only [pow_zero]
  have hsum_dvd : p ∣ ∑ i ∈ Finset.range k, p ^ (i + 1) := by
    refine Finset.dvd_sum fun i _ => ?_
    rw [pow_succ']
    exact dvd_mul_right p (p ^ i)
  refine hp.coprime_iff_not_dvd.mpr fun hdiv => ?_
  exact hp.not_dvd_one ((Nat.dvd_add_right hsum_dvd).mp hdiv)

/-- **1. Exact Unique `q`-Source Decomposition of `u` and `W`**:
Factors `u = r₀ ^ e₀ * U₀` (`e₀ = u.factorization r₀ = m.factorization r₀`, `U₀ = ordCompl[r₀] u`)
and `σ(r₀ ^ (2 * e₀)) = q * c₀_u`, establishing `W = c₀_u * σ(U₀ ^ 2)`, `c₀_u ∣ U₀ ^ 2`
(`U₀ ^ 2 = c₀_u * V₀`), and `r₀ ^ (2 * e₀) * V₀ = σ(U₀ ^ 2) * σ(h ^ 2)`. -/
theorem linear_euler_coprime_half_succ_unique_source_w_factorization {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hcop : Nat.Coprime ((q + 1) / 2) (componentIndex N q)) :
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
      r₀ ^ (2 * e₀) * V₀ = sigma 1 (U₀ ^ 2) * sigma 1 (h ^ 2) := by
  obtain ⟨h, u, W, hW_def, hh_odd, hu_odd, hW_odd, hh_ge3, hu_ge3, hW_ge1, hcop_hu, hcop_hW,
    hm_eq, hq_eq, hci_sq_eq, hu2_eq, hsigu2_eq, _, _, _, _, _, _, _⟩ :=
    linear_euler_coprime_half_succ_quotient_system ho hN hq hqm hform hcop
  have hh0 : h ≠ 0 := hh_odd.pos.ne'
  have hu0 : u ≠ 0 := hu_odd.pos.ne'
  obtain ⟨_, r₀, hr₀_m, hq_dvd_r₀, hfac_q_r₀, _, hbound_r₀, _⟩ :=
    linear_euler_unique_q_source_and_bound ho hN hq hqm hform
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_m
  have hh_lt_r₀pow : h < r₀ ^ (m.factorization r₀) := by
    have hpow_sq : r₀ ^ (2 * m.factorization r₀) = (r₀ ^ (m.factorization r₀)) ^ 2 := by
      rw [← pow_mul, mul_comm]
    rw [hpow_sq, hq_eq] at hbound_r₀
    have h2h2_sub : 2 * h ^ 2 - 1 + 1 = 2 * h ^ 2 :=
      Nat.sub_add_cancel (by nlinarith only [hh_ge3])
    have hbound' : 4 * h ^ 2 < 3 * (r₀ ^ (m.factorization r₀)) ^ 2 + 2 := by
      linarith only [hbound_r₀, h2h2_sub]
    by_contra! hle
    have hsq_le : (r₀ ^ (m.factorization r₀)) ^ 2 ≤ h ^ 2 := Nat.pow_le_pow_left hle 2
    nlinarith only [hh_ge3, hbound', hsq_le]
  have hr₀_ndvd_h : ¬ r₀ ∣ h := by
    intro hdvd_h
    have hr₀_ndvd_u : ¬ r₀ ∣ u := fun hdvd_u =>
      hr₀_prime.not_dvd_one (hcop_hu ▸ Nat.dvd_gcd hdvd_h hdvd_u)
    have hm_fact : m.factorization r₀ = h.factorization r₀ := by
      rw [hm_eq, Nat.factorization_mul hh0 hu0, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hr₀_ndvd_u, add_zero]
    have hpow_dvd_h : r₀ ^ (m.factorization r₀) ∣ h := by
      rw [hm_fact]
      exact Nat.ordProj_dvd h r₀
    have hle : r₀ ^ (m.factorization r₀) ≤ h := Nat.le_of_dvd hh_odd.pos hpow_dvd_h
    omega
  have hr₀_u : r₀ ∈ u.primeFactors := by
    have hr₀_dvd_m : r₀ ∣ h * u := hm_eq ▸ Nat.dvd_of_mem_primeFactors hr₀_m
    have hr₀_dvd_u : r₀ ∣ u := (hr₀_prime.dvd_mul.mp hr₀_dvd_m).resolve_left hr₀_ndvd_h
    exact Nat.mem_primeFactors.mpr ⟨hr₀_prime, hr₀_dvd_u, hu0⟩
  set e₀ := u.factorization r₀
  have he₀_eq_m : e₀ = m.factorization r₀ := by
    dsimp [e₀]
    rw [hm_eq, Nat.factorization_mul hh0 hu0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hr₀_ndvd_h, zero_add]
  have he₀_pos : 0 < e₀ :=
    (hr₀_prime.dvd_iff_one_le_factorization hu0).mp (Nat.dvd_of_mem_primeFactors hr₀_u)
  set U₀ := ordCompl[r₀] u
  have hu_split : u = r₀ ^ e₀ * U₀ := (Nat.ordProj_mul_ordCompl_eq_self u r₀).symm
  have hU₀_odd : Odd U₀ := hu_odd.of_dvd_nat ⟨r₀ ^ e₀, by rw [mul_comm, ← hu_split]⟩
  have hU₀_ge1 : 1 ≤ U₀ := hU₀_odd.pos
  have hcop_pow_U₀ : Nat.Coprime (r₀ ^ e₀) U₀ :=
    (Nat.coprime_ordCompl hr₀_prime hu0).pow_left e₀
  rw [← he₀_eq_m] at hq_dvd_r₀ hfac_q_r₀
  set c₀_u := sigma 1 (r₀ ^ (2 * e₀)) / q
  have hsig_r₀_eq : sigma 1 (r₀ ^ (2 * e₀)) = q * c₀_u :=
    (Nat.mul_div_cancel' hq_dvd_r₀).symm
  have hsig_r₀_pos : 0 < sigma 1 (r₀ ^ (2 * e₀)) :=
    sigma_pos 1 (r₀ ^ (2 * e₀)) (pow_ne_zero _ hr₀_prime.ne_zero)
  have hc₀_ge1 : 1 ≤ c₀_u := by
    by_contra! hc0
    have hcz : c₀_u = 0 := Nat.lt_one_iff.mp hc0
    rw [hcz, mul_zero] at hsig_r₀_eq
    omega
  have hq_ndvd_c₀ : ¬ q ∣ c₀_u := by
    intro hqd
    have hq2_dvd : q ^ 2 ∣ sigma 1 (r₀ ^ (2 * e₀)) := by
      rw [hsig_r₀_eq, pow_two]
      exact Nat.mul_dvd_mul_left q hqd
    have hle2 : 2 ≤ (sigma 1 (r₀ ^ (2 * e₀))).factorization q :=
      (hq.pow_dvd_iff_le_factorization hsig_r₀_pos.ne').mp hq2_dvd
    omega
  have hcop_r₀_c₀ : Nat.Coprime (r₀ ^ (2 * e₀)) c₀_u := by
    have hcop_base_sig : Nat.Coprime r₀ (sigma 1 (r₀ ^ (2 * e₀))) :=
      sigma_prime_pow_coprime_base hr₀_prime
    have hc₀_dvd_sig : c₀_u ∣ sigma 1 (r₀ ^ (2 * e₀)) := ⟨q, by rw [hsig_r₀_eq, mul_comm]⟩
    exact (hcop_base_sig.coprime_dvd_right hc₀_dvd_sig).pow_left (2 * e₀)
  have hu2_split : u ^ 2 = r₀ ^ (2 * e₀) * U₀ ^ 2 := by
    rw [hu_split, mul_pow, ← pow_mul, mul_comm e₀ 2]
  have hcop_r₀2_U₀2 : Nat.Coprime (r₀ ^ (2 * e₀)) (U₀ ^ 2) := by
    have h1 : r₀ ^ (2 * e₀) = (r₀ ^ e₀) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [h1]
    exact (hcop_pow_U₀.pow_left 2).pow_right 2
  have hsigu2_eq_Wq : sigma 1 (u ^ 2) = q * W := by
    rw [hsigu2_eq, ← hq_eq, mul_comm]
  have hW_eq : W = c₀_u * sigma 1 (U₀ ^ 2) := by
    apply Nat.mul_left_cancel hq.pos
    calc
      q * W = sigma 1 (u ^ 2) := hsigu2_eq_Wq.symm
      _ = sigma 1 (r₀ ^ (2 * e₀) * U₀ ^ 2) := by rw [hu2_split]
      _ = sigma 1 (r₀ ^ (2 * e₀)) * sigma 1 (U₀ ^ 2) :=
          isMultiplicative_sigma.map_mul_of_coprime hcop_r₀2_U₀2
      _ = (q * c₀_u) * sigma 1 (U₀ ^ 2) := by rw [hsig_r₀_eq]
      _ = q * (c₀_u * sigma 1 (U₀ ^ 2)) := by ring
  have hbal_c₀ : r₀ ^ (2 * e₀) * U₀ ^ 2 = c₀_u * (sigma 1 (U₀ ^ 2) * sigma 1 (h ^ 2)) := by
    calc
      r₀ ^ (2 * e₀) * U₀ ^ 2 = u ^ 2 := hu2_split.symm
      _ = W * sigma 1 (h ^ 2) := hu2_eq
      _ = (c₀_u * sigma 1 (U₀ ^ 2)) * sigma 1 (h ^ 2) := by rw [hW_eq]
      _ = c₀_u * (sigma 1 (U₀ ^ 2) * sigma 1 (h ^ 2)) := by ring
  have hc₀_dvd_U₀2 : c₀_u ∣ U₀ ^ 2 :=
    hcop_r₀_c₀.symm.dvd_of_dvd_mul_left ⟨sigma 1 (U₀ ^ 2) * sigma 1 (h ^ 2), hbal_c₀⟩
  set V₀ := U₀ ^ 2 / c₀_u
  have hU₀2_eq : U₀ ^ 2 = c₀_u * V₀ := (Nat.mul_div_cancel' hc₀_dvd_U₀2).symm
  have hV₀_ge1 : 1 ≤ V₀ := by
    have hU₀2_pos : 0 < U₀ ^ 2 := pow_pos hU₀_ge1 2
    by_contra! hV0
    have hVz : V₀ = 0 := Nat.lt_one_iff.mp hV0
    rw [hVz, mul_zero] at hU₀2_eq
    omega
  have hbal_V₀ : r₀ ^ (2 * e₀) * V₀ = sigma 1 (U₀ ^ 2) * sigma 1 (h ^ 2) := by
    apply Nat.mul_left_cancel (by omega : 0 < c₀_u)
    calc
      c₀_u * (r₀ ^ (2 * e₀) * V₀) = r₀ ^ (2 * e₀) * (c₀_u * V₀) := by ring
      _ = r₀ ^ (2 * e₀) * U₀ ^ 2 := by rw [← hU₀2_eq]
      _ = c₀_u * (sigma 1 (U₀ ^ 2) * sigma 1 (h ^ 2)) := hbal_c₀
  exact ⟨h, u, W, r₀, e₀, U₀, c₀_u, V₀, hW_def, hh_odd, hu_odd, hW_odd, hU₀_odd,
    hh_ge3, hu_ge3, hW_ge1, hU₀_ge1, hc₀_ge1, hV₀_ge1, hcop_hu, hcop_hW, hm_eq, hq_eq,
    hci_sq_eq, hr₀_prime, hr₀_u, hr₀_ndvd_h, he₀_pos, rfl, he₀_eq_m, rfl, hu_split,
    hcop_pow_U₀, hsig_r₀_eq, hq_ndvd_c₀, hcop_r₀_c₀, hW_eq, hc₀_dvd_U₀2, hU₀2_eq, hbal_V₀⟩

/-- **2. Unconditional `W = 1 ∨ 13 ≤ W` Gap**:
Establishes `W = 1 ↔ U₀ = 1`, `3 ≤ W ↔ 3 ≤ U₀`, the unconditional dichotomy `W = 1 ∨ 13 ≤ W`,
and `c₀_u * σ(h ^ 2) < r₀ ^ (2 * e₀)` with `V₀ < σ(U₀ ^ 2)` when `13 ≤ W`. -/
theorem linear_euler_coprime_half_succ_w_one_or_ge_thirteen {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hcop : Nat.Coprime ((q + 1) / 2) (componentIndex N q)) :
    ∃ h u W r₀ e₀ U₀ c₀_u V₀ : ℕ,
      W = sigma 1 (u ^ 2) / q ∧
      m = h * u ∧ q = 2 * h ^ 2 - 1 ∧ componentIndex N q = u ^ 2 ∧
      r₀ ∈ u.primeFactors ∧ e₀ = u.factorization r₀ ∧ U₀ = ordCompl[r₀] u ∧
      sigma 1 (r₀ ^ (2 * e₀)) = q * c₀_u ∧
      W = c₀_u * sigma 1 (U₀ ^ 2) ∧ U₀ ^ 2 = c₀_u * V₀ ∧
      r₀ ^ (2 * e₀) * V₀ = sigma 1 (U₀ ^ 2) * sigma 1 (h ^ 2) ∧
      (W = 1 ↔ U₀ = 1) ∧
      (3 ≤ W ↔ 3 ≤ U₀) ∧
      (W = 1 ∨ 13 ≤ W) ∧
      (13 ≤ W → c₀_u * sigma 1 (h ^ 2) < r₀ ^ (2 * e₀) ∧ V₀ < sigma 1 (U₀ ^ 2)) := by
  obtain ⟨h, u, W, r₀, e₀, U₀, c₀_u, V₀, hW_def, _, _, hW_odd, hU₀_odd,
    hh_ge3, _, _, hU₀_ge1, hc₀_ge1, _, _, _, hm_eq, hq_eq, hci_sq_eq,
    hr₀_prime, hr₀_u, _, he₀_pos, he₀_eq_u, _, hU₀_def, hu_split, _,
    hsig_r₀_eq, _, _, hW_eq, _, hU₀2_eq, hbal_V₀⟩ :=
    linear_euler_coprime_half_succ_unique_source_w_factorization ho hN hq hqm hform hcop
  obtain ⟨h₁, u₁, W₁, hW₁_def, _, _, _, hh₁_ge3, _, _, _, hq₁_eq, hci₁_eq, _, _,
    hW₁_iff_card1, _, _⟩ :=
    linear_euler_coprime_half_succ_w_one_iff_prime_pow_u ho hN hq hqm hform hcop
  obtain ⟨_, hu₁_eq, hW₁_eq⟩ :=
    align_coprime_half_succ_witnesses_split hq_eq hh_ge3 hci_sq_eq hW_def
      hq₁_eq hh₁_ge3 hci₁_eq hW₁_def
  have hW_iff_card1 : W = 1 ↔ u.primeFactors.card = 1 := by
    simpa only [hu₁_eq, hW₁_eq] using hW₁_iff_card1
  have hW_iff_U₀1 : W = 1 ↔ U₀ = 1 := by
    constructor
    · intro hW1
      have hmul1 : c₀_u * sigma 1 (U₀ ^ 2) = 1 := hW_eq.symm.trans hW1
      have hsig_pos : 0 < sigma 1 (U₀ ^ 2) := sigma_pos 1 (U₀ ^ 2) (pow_ne_zero 2 hU₀_odd.pos.ne')
      have hsig1 : sigma 1 (U₀ ^ 2) = 1 := by nlinarith only [hmul1, hc₀_ge1, hsig_pos]
      by_contra hU₀_ne1
      have hU₀_gt1 : 1 < U₀ := Nat.lt_of_le_of_ne hU₀_ge1 (Ne.symm hU₀_ne1)
      have hU₀2_gt1 : 1 < U₀ ^ 2 := by nlinarith only [hU₀_gt1]
      have hlt := self_lt_sigma_of_one_lt hU₀2_gt1
      linarith only [hsig1, hlt, hU₀2_gt1]
    · intro hU₀1
      have hu_pow : u = r₀ ^ e₀ := by
        rw [hu_split, hU₀1, mul_one]
      have hcard1 : u.primeFactors.card = 1 := by
        rw [hu_pow, Nat.primeFactors_prime_pow he₀_pos.ne' hr₀_prime, Finset.card_singleton]
      exact hW_iff_card1.mpr hcard1
  have hW3_iff_U₀3 : 3 ≤ W ↔ 3 ≤ U₀ := by
    have hW_ne1 : W ≠ 1 ↔ 3 ≤ W := by
      obtain ⟨k, hk⟩ := hW_odd
      omega
    have hU₀_ne1 : U₀ ≠ 1 ↔ 3 ≤ U₀ := by
      obtain ⟨k, hk⟩ := hU₀_odd
      omega
    rw [← hW_ne1, ← hU₀_ne1]
    exact not_congr hW_iff_U₀1
  have hW_gap : W = 1 ∨ 13 ≤ W := by
    by_cases hW1 : W = 1
    · exact Or.inl hW1
    · right
      have hU₀_ge3 : 3 ≤ U₀ := hW3_iff_U₀3.mp (by obtain ⟨k, hk⟩ := hW_odd; omega)
      have hsig_ge13 : 13 ≤ sigma 1 (U₀ ^ 2) := by
        have h1 := sq_add_self_add_one_le_sigma_sq hU₀_ge3
        nlinarith only [hU₀_ge3, h1]
      have hsig_le_W : sigma 1 (U₀ ^ 2) ≤ W := by
        rw [hW_eq]
        exact Nat.le_mul_of_pos_left _ hc₀_ge1
      linarith only [hsig_ge13, hsig_le_W]
  have hW13_imp : 13 ≤ W → c₀_u * sigma 1 (h ^ 2) < r₀ ^ (2 * e₀) ∧ V₀ < sigma 1 (U₀ ^ 2) := by
    intro hW13
    have hU₀_ge3 : 3 ≤ U₀ := hW3_iff_U₀3.mp (by linarith only [hW13])
    have hU₀2_gt1 : 1 < U₀ ^ 2 := by nlinarith only [hU₀_ge3]
    have hU₀2_lt_sig : U₀ ^ 2 < sigma 1 (U₀ ^ 2) := self_lt_sigma_of_one_lt hU₀2_gt1
    have hr₀_pow_pos : 0 < r₀ ^ (2 * e₀) := pow_pos hr₀_prime.pos (2 * e₀)
    have hmul_eq : (c₀_u * sigma 1 (h ^ 2)) * sigma 1 (U₀ ^ 2) = r₀ ^ (2 * e₀) * U₀ ^ 2 := by
      calc
        (c₀_u * sigma 1 (h ^ 2)) * sigma 1 (U₀ ^ 2)
            = c₀_u * (sigma 1 (U₀ ^ 2) * sigma 1 (h ^ 2)) := by ring
        _ = c₀_u * (r₀ ^ (2 * e₀) * V₀) := by rw [← hbal_V₀]
        _ = r₀ ^ (2 * e₀) * (c₀_u * V₀) := by ring
        _ = r₀ ^ (2 * e₀) * U₀ ^ 2 := by rw [← hU₀2_eq]
    have hmul_lt : (c₀_u * sigma 1 (h ^ 2)) * sigma 1 (U₀ ^ 2) <
        r₀ ^ (2 * e₀) * sigma 1 (U₀ ^ 2) := by
      rw [hmul_eq]
      exact Nat.mul_lt_mul_of_pos_left hU₀2_lt_sig hr₀_pow_pos
    have hlt1 : c₀_u * sigma 1 (h ^ 2) < r₀ ^ (2 * e₀) :=
      Nat.lt_of_mul_lt_mul_right hmul_lt
    have hV₀_le : V₀ ≤ U₀ ^ 2 := by
      rw [hU₀2_eq]
      exact Nat.le_mul_of_pos_left _ hc₀_ge1
    have hlt2 : V₀ < sigma 1 (U₀ ^ 2) := lt_of_le_of_lt hV₀_le hU₀2_lt_sig
    exact ⟨hlt1, hlt2⟩
  exact ⟨h, u, W, r₀, e₀, U₀, c₀_u, V₀, hW_def, hm_eq, hq_eq, hci_sq_eq,
    hr₀_u, he₀_eq_u, hU₀_def, hsig_r₀_eq, hW_eq, hU₀2_eq, hbal_V₀,
    hW_iff_U₀1, hW3_iff_U₀3, hW_gap, hW13_imp⟩

/-- **3. Sixth-Power-Free `5113 ≤ W` & `608447 ≤ 2 * u ^ 2 - σ(u ^ 2)` Jump**:
On a sixth-power-free odd perfect number `N` in the coprime half-successor branch, any prime
factor `s ∣ U₀` satisfies `61 ≤ s` and `¬ 3 ∣ σ(s ^ (2 * v_s(U₀)))`, forcing `71 ≤ U₀`,
`5113 ≤ W`, and `608447 ≤ 2 * u ^ 2 - σ(u ^ 2)`. -/
theorem sixth_power_free_coprime_half_succ_w_ge_5113 {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hcop : Nat.Coprime ((q + 1) / 2) (componentIndex N q)) :
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
      608447 ≤ 2 * u ^ 2 - sigma 1 (u ^ 2) := by
  obtain ⟨h, u, W, hW_def, hh_odd, hu_odd, hW_odd, hh_ge59, hq_ge6961, hW_ge61, hu_pf_ge2,
    hcop_hu, hcop_hW, hform_hu, hci_sq_eq, hu2_eq, _, _, _, _, _, _⟩ :=
    sixth_power_free_coprime_half_succ_two_primes_in_u ho hN hq hq4 he hev hfree hcop
  obtain ⟨h₀, u₀, W₀, hW₀_def, _, _, _, _, _, _, _, _, _, hci₀_eq, _, _, h119_le, _, _⟩ :=
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
  obtain ⟨h₂, u₂, W₂, r₀, e₀, U₀, c₀_u, V₀, hW₂_def, hm₂_eq, _, hci₂_eq,
    _, he₀_def, hU₀_def, _, hW₂_eq, hU₀2_eq, hbal_V₀, hW₂_iff_U₀1, _, _, hW₂_13⟩ :=
    linear_euler_coprime_half_succ_w_one_or_ge_thirteen ho hN hq_prime hqm hform_hu hcop
  have hu₂_eq : u₂ = u :=
    Nat.pow_left_injective (by decide : 2 ≠ 0) (hci₂_eq.symm.trans hci_sq_eq)
  have hh₂_eq : h₂ = h := by
    have hmul : h₂ * u = h * u := by
      calc
        h₂ * u = h₂ * u₂ := by rw [hu₂_eq]
        _ = h * u := hm₂_eq.symm
    exact Nat.mul_right_cancel hu_odd.pos hmul
  have hW₂_eq' : W₂ = W := by rw [hW₂_def, hW_def, hu₂_eq]
  rw [hW₂_eq'] at hW₂_eq hW₂_iff_U₀1 hW₂_13
  rw [hh₂_eq] at hbal_V₀ hW₂_13
  have hu_split : u = r₀ ^ e₀ * U₀ := by
    rw [he₀_def, hU₀_def, hu₂_eq]
    exact (Nat.ordProj_mul_ordCompl_eq_self u r₀).symm
  have hU₀_odd : Odd U₀ := hu_odd.of_dvd_nat ⟨r₀ ^ e₀, by rw [mul_comm, ← hu_split]⟩
  have hc₀_ge1 : 1 ≤ c₀_u := by
    by_contra! hc0
    have hcz : c₀_u = 0 := Nat.lt_one_iff.mp hc0
    rw [hcz, zero_mul] at hW₂_eq
    omega
  have hc₀_lt : c₀_u * sigma 1 (h ^ 2) < r₀ ^ (2 * e₀) :=
    (hW₂_13 (by omega)).1
  have h119_W : 119 * W ≤ 2 * u ^ 2 - sigma 1 (u ^ 2) := by
    have hu₀_eq : u₀ = u :=
      Nat.pow_left_injective (by decide : 2 ≠ 0) (hci₀_eq.symm.trans hci_sq_eq)
    have hW₀_eq : W₀ = W := by rw [hW₀_def, hW_def, hu₀_eq]
    rwa [hu₀_eq, hW₀_eq] at h119_le
  have hU₀_ne1 : U₀ ≠ 1 := by
    intro h1
    have : W = 1 := hW₂_iff_U₀1.mpr h1
    omega
  obtain ⟨s, hs_prime, hs_dvd_U₀⟩ := Nat.exists_prime_and_dvd hU₀_ne1
  have hs_dvd_u : s ∣ u := hs_dvd_U₀.trans ⟨r₀ ^ e₀, by rw [hu_split, mul_comm]⟩
  have hs_dvd_u2 : s ∣ u ^ 2 := hs_dvd_u.trans (dvd_pow_self u (by decide : 2 ≠ 0))
  have hs_dvd_N : s ∣ N := by
    rw [hform_hu]
    exact (hs_dvd_u.trans (dvd_mul_left u h)).trans
      ((dvd_pow_self (h * u) (by decide : 2 ≠ 0)).trans (dvd_mul_left _ q))
  have hs_N : s ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hs_prime, hs_dvd_N, hN.2.ne'⟩
  have hs_ge53 : 53 ≤ s := sixth_power_free_min_prime_ge_53 ho hN hfree hs_N
  have hci_ne0 : componentIndex N q ≠ 0 := by
    rw [hci_sq_eq]
    exact pow_ne_zero 2 hu_odd.pos.ne'
  have hs_ci : s ∈ (componentIndex N q).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hs_prime, hci_sq_eq ▸ hs_dvd_u2, hci_ne0⟩
  have hs_mod : s % 5 = 1 ∨ s % 3 = 1 :=
    (sixth_power_free_euler_index_drop_and_support ho hN hq hq4 he hev hfree).2 s hs_ci
  have hs_ge61 : 61 ≤ s := by
    by_contra! hlt
    have hs_cases : s = 53 ∨ s = 54 ∨ s = 55 ∨ s = 56 ∨ s = 57 ∨ s = 58 ∨ s = 59 ∨ s = 60 := by
      omega
    rcases hs_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (by decide : ¬ (53 % 5 = 1 ∨ 53 % 3 = 1)) hs_mod
    · exact (by decide : ¬ Nat.Prime 54) hs_prime
    · exact (by decide : ¬ Nat.Prime 55) hs_prime
    · exact (by decide : ¬ Nat.Prime 56) hs_prime
    · exact (by decide : ¬ Nat.Prime 57) hs_prime
    · exact (by decide : ¬ Nat.Prime 58) hs_prime
    · exact (by decide : ¬ (59 % 5 = 1 ∨ 59 % 3 = 1)) hs_mod
    · exact (by decide : ¬ Nat.Prime 60) hs_prime
  have hnot3_N : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have hW_dvd_N : W ∣ N := by
    have hW_dvd_u2 : W ∣ u ^ 2 := ⟨sigma 1 (h ^ 2), hu2_eq⟩
    have hu2_dvd_N : u ^ 2 ∣ N := by
      rw [hform_hu, mul_pow]
      exact (dvd_mul_left (u ^ 2) (h ^ 2)).trans (dvd_mul_left _ q)
    exact hW_dvd_u2.trans hu2_dvd_N
  have hnot3_W : ¬ 3 ∣ W := fun h3 => hnot3_N (h3.trans hW_dvd_N)
  have hsig_dvd_W : sigma 1 (U₀ ^ 2) ∣ W := ⟨c₀_u, by rw [hW₂_eq, mul_comm]⟩
  have hnot3_sigU₀ : ¬ 3 ∣ sigma 1 (U₀ ^ 2) := fun h3 => hnot3_W (h3.trans hsig_dvd_W)
  have hU₀_ne0 : U₀ ≠ 0 := hU₀_odd.pos.ne'
  set k_s := U₀.factorization s
  have hk_s_ge1 : 1 ≤ k_s :=
    (hs_prime.dvd_iff_one_le_factorization hU₀_ne0).mp hs_dvd_U₀
  have hU₀2_split : U₀ ^ 2 = s ^ (2 * k_s) * (ordCompl[s] U₀) ^ 2 := by
    have h1 : U₀ = s ^ k_s * ordCompl[s] U₀ := (Nat.ordProj_mul_ordCompl_eq_self U₀ s).symm
    calc
      U₀ ^ 2 = (s ^ k_s * ordCompl[s] U₀) ^ 2 := by rw [← h1]
      _ = (s ^ k_s) ^ 2 * (ordCompl[s] U₀) ^ 2 := by rw [mul_pow]
      _ = s ^ (2 * k_s) * (ordCompl[s] U₀) ^ 2 := by rw [← pow_mul, mul_comm k_s 2]
  have hcop_s_compl : Nat.Coprime (s ^ (2 * k_s)) ((ordCompl[s] U₀) ^ 2) :=
    ((Nat.coprime_ordCompl hs_prime hU₀_ne0).pow_left (2 * k_s)).pow_right 2
  have hsig_s_dvd : sigma 1 (s ^ (2 * k_s)) ∣ sigma 1 (U₀ ^ 2) := by
    rw [hU₀2_split, isMultiplicative_sigma.map_mul_of_coprime hcop_s_compl]
    exact dvd_mul_right _ _
  have hnot3_sigs : ¬ 3 ∣ sigma 1 (s ^ (2 * k_s)) := fun h3 => hnot3_sigU₀ (h3.trans hsig_s_dvd)
  have hU₀_ge71 : 71 ≤ U₀ := by
    by_cases hs3 : s % 3 = 1
    · have hk_ge2 : 2 ≤ k_s := by
        by_contra! hk_lt2
        have hk1 : k_s = 1 := by omega
        have hsig_eq : sigma 1 (s ^ (2 * k_s)) = s ^ 2 + s + 1 := by
          rw [hk1, mul_one, sigma_one_apply_prime_pow hs_prime]
          simp [Finset.sum_range_succ]
          ring
        have h3_dvd : 3 ∣ sigma 1 (s ^ (2 * k_s)) := by
          rw [hsig_eq]
          obtain ⟨t, ht⟩ : ∃ t, s = 3 * t + 1 := ⟨s / 3, by omega⟩
          rw [ht]
          exact ⟨3 * t ^ 2 + 3 * t + 1, by ring⟩
        exact hnot3_sigs h3_dvd
      have hpow_dvd_U₀ : s ^ k_s ∣ U₀ := Nat.ordProj_dvd U₀ s
      have hs2_le_pow : s ^ 2 ≤ s ^ k_s := Nat.pow_le_pow_right hs_prime.pos hk_ge2
      have hpow_le_U₀ : s ^ k_s ≤ U₀ := Nat.le_of_dvd hU₀_odd.pos hpow_dvd_U₀
      have h61_sq : 61 ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hs_ge61 2
      linarith only [h61_sq, hs2_le_pow, hpow_le_U₀]
    · have hs_ge71 : 71 ≤ s := by
        by_contra! hlt
        have hs_cases : s = 61 ∨ s = 62 ∨ s = 63 ∨ s = 64 ∨ s = 65 ∨
            s = 66 ∨ s = 67 ∨ s = 68 ∨ s = 69 ∨ s = 70 := by omega
        rcases hs_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hs3 (by decide)
        · exact (by decide : ¬ Nat.Prime 62) hs_prime
        · exact (by decide : ¬ Nat.Prime 63) hs_prime
        · exact (by decide : ¬ Nat.Prime 64) hs_prime
        · exact (by decide : ¬ Nat.Prime 65) hs_prime
        · exact (by decide : ¬ Nat.Prime 66) hs_prime
        · exact hs3 (by decide)
        · exact (by decide : ¬ Nat.Prime 68) hs_prime
        · exact (by decide : ¬ Nat.Prime 69) hs_prime
        · exact (by decide : ¬ Nat.Prime 70) hs_prime
      exact hs_ge71.trans (Nat.le_of_dvd hU₀_odd.pos hs_dvd_U₀)
  have hW_ge5113 : 5113 ≤ W := by
    have h1 : U₀ ^ 2 + U₀ + 1 ≤ sigma 1 (U₀ ^ 2) :=
      sq_add_self_add_one_le_sigma_sq (by linarith only [hU₀_ge71])
    have hsig_ge : 5113 ≤ sigma 1 (U₀ ^ 2) := by nlinarith only [hU₀_ge71, h1]
    have hsig_le_W : sigma 1 (U₀ ^ 2) ≤ W := by
      rw [hW₂_eq]
      exact Nat.le_mul_of_pos_left _ hc₀_ge1
    linarith only [hsig_ge, hsig_le_W]
  have h608447_le : 608447 ≤ 2 * u ^ 2 - sigma 1 (u ^ 2) := by
    linarith only [hW_ge5113, h119_W]
  exact ⟨h, u, W, r₀, e₀, U₀, c₀_u, V₀, hW_def, hh_odd, hu_odd, hW_odd, hU₀_odd,
    hh_ge59, hq_ge6961, hU₀_ge71, hW_ge5113, hu_pf_ge2, hcop_hu, hcop_hW,
    hform_hu, hci_sq_eq, hu_split, hW₂_eq, hU₀2_eq, hbal_V₀, hc₀_lt, h608447_le⟩

end OddPerfect
