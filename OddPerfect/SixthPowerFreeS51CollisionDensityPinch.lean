module

public import OddPerfect.SixthPowerFreeQuarticCollisionPinch
import OddPerfect.OddGeometricSquares
import OddPerfect.TothSplitExistence
import OddPerfect.SixthPowerFreeEuler
import OddPerfect.OddValuationCycleObstruction
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sixth-Power-Free `S₅₁` Collision-Density Pinch (`OddPerfect.SixthPowerFreeS51CollisionDensityPinch`)

Formalizes the non-Euler odd-valuation target theorem, the hitting of `S₅₁_col` by every
non-`q`-hitting quartic prime `u ∈ largeSources N q`, and the resulting collision-density lower
bound `73 ≤ S₅₁_col.card`:

1. `sixth_power_free_non_euler_has_odd_valuation_target`:
   For every non-Euler prime `p ∈ N.primeFactors.erase q`, `σ(p^{v_p(N)})` is non-square and
   admits a prime factor `r ∈ N.primeFactors` of odd valuation in `σ(p^{v_p(N)})` with either
   `r = q` or `2 ≤ indegAt N q r`.
2. `sixth_power_free_largeSources_hit_S51_col`:
   Every `u ∈ largeSources N q` with `¬ q ∣ σ(u^4)` has a prime factor `r ∈ S₅₁_col` dividing
   `σ(u^4)`, and at most one `u ∈ largeSources N q` satisfies `q ∣ σ(u^4)`.
3. `sixth_power_free_S51_col_ge_73`:
   `(largeSources N q).card ≤ 2 * S₅₁_col.card + 1` and `73 ≤ S₅₁_col.card`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private theorem sigma_one_four_eq {p : ℕ} (hp : p.Prime) :
    sigma 1 (p ^ 4) = p ^ 4 + p ^ 3 + p ^ 2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

private theorem sixth_power_free_five_not_dvd_local {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    ¬ 5 ∣ N := by
  intro h5
  have h5_mem : 5 ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨by decide, h5, hN.2.ne'⟩
  have h53 : 53 ≤ 5 := sixth_power_free_min_prime_ge_53 ho hN hfree h5_mem
  omega

/-- **1. Non-Euler Odd-Valuation Target**:
In any sixth-power-free odd perfect number `N`, every non-Euler prime `p ∈ N.primeFactors.erase q`
has non-square `σ(p^{v_p(N)})` and admits a prime factor `r ∈ N.primeFactors` with odd valuation in
`σ(p^{v_p(N)})` and either `r = q` or `2 ≤ indegAt N q r`. -/
theorem sixth_power_free_non_euler_has_odd_valuation_target {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    ∀ p ∈ N.primeFactors.erase q,
      ¬ IsSquare (sigma 1 (p ^ N.factorization p)) ∧
      ∃ r ∈ N.primeFactors,
        Odd ((sigma 1 (p ^ N.factorization p)).factorization r) ∧
        (r = q ∨ 2 ≤ indegAt N q r) := by
  obtain ⟨hprops, hprod, hbi, _⟩ := prod_oddComponentSigma_eq_self ho hN hq hq4 he hev
  obtain ⟨hcons, _, _⟩ := factorization_eq_indegAt_add_localRepeatAt ho hN hq hq4 he hev
  have hc0 : ∀ x ∈ N.primeFactors, oddComponentSigma N q x ≠ 0 := fun x hx => by
    have := (hprops x hx).2.2
    omega
  intro p hp_erase
  obtain ⟨hpq, hp_mem⟩ := Finset.mem_erase.mp hp_erase
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hp53 : 53 ≤ p := sixth_power_free_min_prime_ge_53 ho hN hfree hp_mem
  have hp3 : p ≠ 3 := by omega
  have hp_pos : 0 < N.factorization p :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp_mem)
  have hp_even : Even (N.factorization p) := hev p hpq
  have hnot_sq : ¬ IsSquare (sigma 1 (p ^ N.factorization p)) := by
    rw [sigma_prime_pow_isSquare_iff_of_even hp_prime hp_pos hp_even]
    exact fun ⟨hp3', _⟩ => hp3 hp3'
  have hcomp_eq : oddComponentSigma N q p = sigma 1 (p ^ N.factorization p) := by
    unfold oddComponentSigma
    simp only [hpq, ite_false]
  have hMp_ne0 : sigma 1 (p ^ N.factorization p) ≠ 0 := by
    rw [← hcomp_eq]
    exact hc0 p hp_mem
  have hex_odd : ∃ r ∈ (sigma 1 (p ^ N.factorization p)).primeFactors,
      Odd ((sigma 1 (p ^ N.factorization p)).factorization r) := by
    by_contra! hall
    apply hnot_sq
    apply Nat.isSquare_iff_even_factorization.mpr
    intro r _
    by_cases hr_mem : r ∈ (sigma 1 (p ^ N.factorization p)).primeFactors
    · exact hall r hr_mem
    · rw [Finsupp.notMem_support_iff.mp hr_mem]
      exact Even.zero
  obtain ⟨r, hr_pf, hr_odd⟩ := hex_odd
  have hr_N : r ∈ N.primeFactors := by
    rw [← hbi]
    exact Finset.mem_biUnion.mpr ⟨p, hp_mem, hcomp_eq.symm ▸ hr_pf⟩
  refine ⟨hnot_sq, r, hr_N, hr_odd, ?_⟩
  by_cases hrq : r = q
  · exact Or.inl hrq
  · right
    by_contra! hlt2
    have hind1 : indegAt N q r = 1 := by
      have h1 := (hcons r hr_N).1
      omega
    let S_r := N.primeFactors.filter (fun x => r ∈ (oddComponentSigma N q x).primeFactors)
    have hp_Sr : p ∈ S_r := Finset.mem_filter.mpr ⟨hp_mem, hcomp_eq.symm ▸ hr_pf⟩
    have hSr_card : S_r.card = 1 := hind1
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hSr_card
    have hpa : p = a := Finset.mem_singleton.mp (ha ▸ hp_Sr)
    have hSr_eq : S_r = {p} := by rwa [← hpa] at ha
    have hother_zero : ∀ x ∈ N.primeFactors, x ≠ p →
        (oddComponentSigma N q x).factorization r = 0 := by
      intro x hx hxp
      have hx_not : x ∉ S_r := by
        rw [hSr_eq, Finset.mem_singleton]
        exact hxp
      have hr_not : r ∉ (oddComponentSigma N q x).primeFactors := fun h =>
        hx_not (Finset.mem_filter.mpr ⟨hx, h⟩)
      exact Finsupp.notMem_support_iff.mp hr_not
    have hN_fac : N.factorization r = (sigma 1 (p ^ N.factorization p)).factorization r := by
      conv_lhs => rw [← hprod]
      rw [Nat.factorization_prod_apply hc0]
      rw [← Finset.add_sum_erase N.primeFactors _ hp_mem]
      have hsum_zero : ∑ x ∈ N.primeFactors.erase p, (oddComponentSigma N q x).factorization r = 0 :=
        Finset.sum_eq_zero fun x hx =>
          let ⟨hxp, hx_mem⟩ := Finset.mem_erase.mp hx
          hother_zero x hx_mem hxp
      rw [hsum_zero, add_zero, hcomp_eq]
    have heven_r : Even ((sigma 1 (p ^ N.factorization p)).factorization r) := by
      rw [← hN_fac]
      exact hev r hrq
    exact (Nat.not_odd_iff_even.mpr heven_r) hr_odd

/-- **2. Quartic Primes Hit `S₅₁_col`**:
Every `u ∈ largeSources N q` not sending a factor of `q` into `σ(u^4)` has a prime factor
`r ∈ S₅₁_col` dividing `σ(u^4)`, and at most one `u ∈ largeSources N q` divides `σ(u^4)` by `q`. -/
theorem sixth_power_free_largeSources_hit_S51_col {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S₅₁ := (squareSources N).filter (· % 5 = 1)
    let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
    (∀ u ∈ largeSources N q, ¬ q ∣ sigma 1 (u ^ 4) →
      ∃ r ∈ S₅₁_col, r ∣ sigma 1 (u ^ 4)) ∧
    ((largeSources N q).filter (fun u => q ∣ sigma 1 (u ^ 4))).card ≤ 1 := by
  intro S₅₁ S₅₁_col
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have h5 : ¬ 5 ∣ N := sixth_power_free_five_not_dvd_local ho hN hfree
  have hq1 : N.factorization q = 1 := sixth_power_free_euler_exponent_one ho hN hq he hfree
  have hlg4 : ∀ u ∈ largeSources N q, N.factorization u = 4 :=
    (three_free_sixthPowerFree_forces_147_largeSources ho hN hq hq4 he hev h3 hfree).1
  obtain ⟨hprops, hprod, _, _⟩ := prod_oddComponentSigma_eq_self ho hN hq hq4 he hev
  obtain ⟨hcons, _, _⟩ := factorization_eq_indegAt_add_localRepeatAt ho hN hq hq4 he hev
  have htarget := sixth_power_free_non_euler_has_odd_valuation_target ho hN hq hq4 he hev hfree
  refine ⟨?_, ?_⟩
  · intro u hu hnq
    obtain ⟨hu_mem, _, hu_neq, _⟩ := Finset.mem_filter.mp hu
    have hu_prime : u.Prime := Nat.prime_of_mem_primeFactors hu_mem
    have hu4 : N.factorization u = 4 := hlg4 u hu
    obtain ⟨_, r, hr_N, hr_odd, hr_cases⟩ := htarget u (Finset.mem_erase.mpr ⟨hu_neq, hu_mem⟩)
    rw [hu4] at hr_odd
    have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr_N
    have hr53 : 53 ≤ r := sixth_power_free_min_prime_ge_53 ho hN hfree hr_N
    have hr_dvd_sig : r ∣ sigma 1 (u ^ 4) := by
      have hne0 : (sigma 1 (u ^ 4)).factorization r ≠ 0 := by
        intro h0
        rw [h0] at hr_odd
        exact (by decide : ¬ Odd 0) hr_odd
      exact Nat.dvd_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hne0)
    have hrq : r ≠ q := fun h => hnq (h ▸ hr_dvd_sig)
    have hind_ge2 : 2 ≤ indegAt N q r := hr_cases.resolve_left hrq
    have hr_mod5 : r % 5 = 1 := by
      have : Fact r.Prime := ⟨hr_prime⟩
      have hr_dvd_poly : r ∣ u ^ 4 + u ^ 3 + u ^ 2 + u + 1 := by
        rwa [← sigma_one_four_eq hu_prime]
      have hsum0 : (u : ZMod r) ^ 4 + (u : ZMod r) ^ 3 + (u : ZMod r) ^ 2 + (u : ZMod r) + 1 = 0 := by
        have hcast : ((u ^ 4 + u ^ 3 + u ^ 2 + u + 1 : ℕ) : ZMod r) = 0 :=
          (ZMod.natCast_eq_zero_iff _ r).mpr hr_dvd_poly
        push_cast at hcast
        exact hcast
      have hu5 : (u : ZMod r) ^ 5 = 1 := by
        have hdiff : (u : ZMod r) ^ 5 - 1 =
            ((u : ZMod r) - 1) *
              ((u : ZMod r) ^ 4 + (u : ZMod r) ^ 3 + (u : ZMod r) ^ 2 + (u : ZMod r) + 1) := by ring
        rw [hsum0, mul_zero] at hdiff
        exact sub_eq_zero.mp hdiff
      have hu_ne0 : (u : ZMod r) ≠ 0 := by
        intro hz
        rw [hz, zero_pow (by decide : 5 ≠ 0)] at hu5
        exact zero_ne_one hu5
      have hu_ne1 : (u : ZMod r) ≠ 1 := by
        intro h1
        rw [h1] at hsum0
        have h5z : ((5 : ℕ) : ZMod r) = 0 := by
          norm_num at hsum0 ⊢
          exact hsum0
        have hr5 : r ∣ 5 := (ZMod.natCast_eq_zero_iff 5 r).mp h5z
        have hr_le5 : r ≤ 5 := Nat.le_of_dvd (by decide) hr5
        omega
      have hord_dvd5 : orderOf (u : ZMod r) ∣ 5 := orderOf_dvd_of_pow_eq_one hu5
      have hord_ne1 : orderOf (u : ZMod r) ≠ 1 := by
        intro h1
        exact hu_ne1 (orderOf_eq_one_iff.mp h1)
      have hord5 : orderOf (u : ZMod r) = 5 :=
        ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp hord_dvd5).resolve_left hord_ne1
      have h5_dvd_pred : 5 ∣ r - 1 := by
        rw [← hord5]
        exact ZMod.orderOf_dvd_card_sub_one hu_ne0
      obtain ⟨k, hk⟩ := h5_dvd_pred
      omega
    have hr_exp2 : N.factorization r = 2 := by
      have hr_pos : 0 < N.factorization r :=
        Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr_N)
      have hr_lt6 : ¬ 6 ≤ N.factorization r := fun hge =>
        hfree r hr_prime ((hr_prime.pow_dvd_iff_le_factorization hN.2.ne').2 hge)
      obtain ⟨k, hk⟩ := hev r hrq
      rcases (show N.factorization r = 2 ∨ N.factorization r = 4 by omega) with h2 | h4
      · exact h2
      · exfalso
        have hcomp_r : oddComponentSigma N q r = sigma 1 (r ^ 4) := by
          unfold oddComponentSigma
          simp only [hrq, ite_false]
          rw [h4]
        have h5_sig : 5 ∣ sigma 1 (r ^ 4) := by
          rw [sigma_one_four_eq hr_prime]
          apply Nat.dvd_of_mod_eq_zero
          have : r % 5 = 1 := hr_mod5
          simp [Nat.add_mod, Nat.pow_mod, this]
        have hsig_dvd_N : sigma 1 (r ^ 4) ∣ N := by
          calc
            sigma 1 (r ^ 4) = oddComponentSigma N q r := hcomp_r.symm
            _ ∣ ∏ p ∈ N.primeFactors, oddComponentSigma N q p :=
              Finset.dvd_prod_of_mem (oddComponentSigma N q) hr_N
            _ = N := hprod
        exact h5 (h5_sig.trans hsig_dvd_N)
    have hr_sq : r ∈ squareSources N :=
      Finset.mem_filter.mpr ⟨hr_N, by omega, hr_exp2⟩
    have hr_S51 : r ∈ S₅₁ := Finset.mem_filter.mpr ⟨hr_sq, hr_mod5⟩
    have hind_le2 : indegAt N q r ≤ 2 := by
      have := (hcons r hr_N).2.2
      omega
    have hr_col : r ∈ S₅₁_col := Finset.mem_filter.mpr ⟨hr_S51, by omega⟩
    exact ⟨r, hr_col, hr_dvd_sig⟩
  · have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hord_sq : IsSquare (ordCompl[q] N) := by
      apply Nat.isSquare_iff_even_factorization.mpr
      intro r _
      rw [Nat.factorization_ordCompl]
      rcases eq_or_ne r q with rfl | hrq
      · simp
      · rw [Finsupp.erase_ne hrq]
        exact hev r hrq
    obtain ⟨m, hm_sq⟩ := hord_sq
    have hqm : ¬ q ∣ m := by
      intro hd
      apply Nat.not_dvd_ordCompl hq_prime hN.2.ne'
      rw [hm_sq]
      exact hd.mul_right m
    have hform : N = q * m ^ 2 := by
      have hmul := Nat.ordProj_mul_ordCompl_eq_self N q
      change q ^ N.factorization q * (N / q ^ N.factorization q) = N at hmul
      rw [hq1, pow_one] at hm_sq hmul
      rw [hm_sq, ← pow_two] at hmul
      exact hmul.symm
    obtain ⟨_, r₀, _, _, _, _, _, huniq⟩ :=
      linear_euler_unique_q_source_and_bound ho hN hq_prime hqm hform
    apply Finset.card_le_one.mpr
    intro u₁ hu₁ u₂ hu₂
    obtain ⟨hu₁_lg, hq_dvd₁⟩ := Finset.mem_filter.mp hu₁
    obtain ⟨hu₂_lg, hq_dvd₂⟩ := Finset.mem_filter.mp hu₂
    have helper : ∀ u ∈ largeSources N q, q ∣ sigma 1 (u ^ 4) → u = r₀ := by
      intro u hu hq_dvd
      obtain ⟨hu_mem, _, hu_neq, _⟩ := Finset.mem_filter.mp hu
      have hu_dvd_N : u ∣ N := Nat.dvd_of_mem_primeFactors hu_mem
      have hu_prime : u.Prime := Nat.prime_of_mem_primeFactors hu_mem
      have hu_dvd_m2 : u ∣ m ^ 2 := by
        rw [hform] at hu_dvd_N
        rcases hu_prime.dvd_mul.mp hu_dvd_N with huq | hum2
        · exfalso
          exact hu_neq ((Nat.prime_dvd_prime_iff_eq hu_prime hq_prime).mp huq)
        · exact hum2
      have hm0 : m ≠ 0 := by
        intro hm0
        rw [hm0, zero_pow (by decide : 2 ≠ 0), mul_zero] at hform
        exact hN.2.ne' hform
      have hu_m : u ∈ m.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hu_prime, hu_prime.dvd_of_dvd_pow hu_dvd_m2, hm0⟩
      have hu_exp : 2 * m.factorization u = 4 := by
        have hN_fac : N.factorization u = 4 := hlg4 u hu
        have hq_fac : (q : ℕ).factorization u = 0 := by
          rw [hq_prime.factorization]
          simp [Ne.symm hu_neq]
        have hm2_ne0 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
        rw [hform, Nat.factorization_mul hq_prime.ne_zero hm2_ne0, Finsupp.add_apply,
          hq_fac, zero_add, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hN_fac
        exact hN_fac
      rw [← hu_exp] at hq_dvd
      exact huniq u hu_m hq_dvd
    rw [helper u₁ hu₁_lg hq_dvd₁, helper u₂ hu₂_lg hq_dvd₂]

/-- **3. `S₅₁_col` Density Pinch (`73 ≤ S₅₁_col.card`)**:
Combines the unique `q`-source bound, `S₅₁_col` hitting, and `indegAt N q r = 2` double-counting
to prove `(largeSources N q).card ≤ 2 * S₅₁_col.card + 1` and `73 ≤ S₅₁_col.card`. -/
theorem sixth_power_free_S51_col_ge_73 {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S₅₁ := (squareSources N).filter (· % 5 = 1)
    let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
    (largeSources N q).card ≤ 2 * S₅₁_col.card + 1 ∧
    73 ≤ S₅₁_col.card := by
  intro S₅₁ S₅₁_col
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  obtain ⟨hlg4, h147, _⟩ :=
    three_free_sixthPowerFree_forces_147_largeSources ho hN hq hq4 he hev h3 hfree
  obtain ⟨hhit, hq_le1⟩ :=
    sixth_power_free_largeSources_hit_S51_col ho hN hq hq4 he hev hfree
  let Q := largeSources N q
  let Q_q := Q.filter (fun u => q ∣ sigma 1 (u ^ 4))
  let Q_nq := Q.filter (fun u => ¬ q ∣ sigma 1 (u ^ 4))
  have hq_le1' : Q_q.card ≤ 1 := hq_le1
  have h147' : 147 ≤ Q.card := h147
  have hpart : Q_q.card + Q_nq.card = Q.card :=
    Finset.card_filter_add_card_filter_not (s := Q) (p := fun u => q ∣ sigma 1 (u ^ 4))
  have hQ_nq_le : Q_nq.card ≤ ∑ u ∈ Q_nq, (S₅₁_col.filter (fun r => r ∣ sigma 1 (u ^ 4))).card := by
    calc
      Q_nq.card = ∑ _u ∈ Q_nq, 1 := by simp
      _ ≤ ∑ u ∈ Q_nq, (S₅₁_col.filter (fun r => r ∣ sigma 1 (u ^ 4))).card := by
        refine Finset.sum_le_sum fun u hu => ?_
        obtain ⟨hu_Q, hu_nq⟩ := Finset.mem_filter.mp hu
        obtain ⟨r, hr_col, hr_dvd⟩ := hhit u hu_Q hu_nq
        exact Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨hr_col, hr_dvd⟩⟩
  have hsum_Q_nq_le_Q :
      (∑ u ∈ Q_nq, (S₅₁_col.filter (fun r => r ∣ sigma 1 (u ^ 4))).card) ≤
        ∑ u ∈ Q, (S₅₁_col.filter (fun r => r ∣ sigma 1 (u ^ 4))).card := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ Q) ?_
    intro _ _ _
    exact Nat.zero_le _
  have hswap :
      (∑ u ∈ Q, (S₅₁_col.filter (fun r => r ∣ sigma 1 (u ^ 4))).card) =
        ∑ r ∈ S₅₁_col, (Q.filter (fun u => r ∣ sigma 1 (u ^ 4))).card := by
    have h1 : ∀ u ∈ Q, (S₅₁_col.filter (fun r => r ∣ sigma 1 (u ^ 4))).card =
        ∑ r ∈ S₅₁_col, if r ∣ sigma 1 (u ^ 4) then 1 else 0 := fun u _ => by
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    have h2 : ∀ r ∈ S₅₁_col, (Q.filter (fun u => r ∣ sigma 1 (u ^ 4))).card =
        ∑ u ∈ Q, if r ∣ sigma 1 (u ^ 4) then 1 else 0 := fun r _ => by
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_comm]
  have hr_cap : ∀ r ∈ S₅₁_col, (Q.filter (fun u => r ∣ sigma 1 (u ^ 4))).card ≤ 2 := by
    intro r hr_col
    obtain ⟨hr_S51, hr_ind2⟩ := Finset.mem_filter.mp hr_col
    have hr_sq : r ∈ squareSources N := (Finset.mem_filter.mp hr_S51).1
    have hr_N : r ∈ N.primeFactors := (Finset.mem_filter.mp hr_sq).1
    have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr_N
    have hsub : Q.filter (fun u => r ∣ sigma 1 (u ^ 4)) ⊆
        N.primeFactors.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors) := by
      intro u hu
      obtain ⟨hu_Q, hu_dvd⟩ := Finset.mem_filter.mp hu
      obtain ⟨hu_mem, _, hu_neq, _⟩ := Finset.mem_filter.mp hu_Q
      have hu4 : N.factorization u = 4 := hlg4 u hu_Q
      have hcomp_u : oddComponentSigma N q u = sigma 1 (u ^ 4) := by
        unfold oddComponentSigma
        simp only [hu_neq, ite_false]
        rw [hu4]
      have hsig_ne0 : sigma 1 (u ^ 4) ≠ 0 := by
        have hu_prime : u.Prime := Nat.prime_of_mem_primeFactors hu_mem
        rw [sigma_one_four_eq hu_prime]
        omega
      refine Finset.mem_filter.mpr ⟨hu_mem, ?_⟩
      rw [hcomp_u]
      exact Nat.mem_primeFactors.mpr ⟨hr_prime, hu_dvd, hsig_ne0⟩
    calc
      (Q.filter (fun u => r ∣ sigma 1 (u ^ 4))).card
          ≤ (N.primeFactors.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors)).card :=
        Finset.card_le_card hsub
      _ = indegAt N q r := rfl
      _ = 2 := hr_ind2
  have hQ_nq_bound : Q_nq.card ≤ 2 * S₅₁_col.card := by
    calc
      Q_nq.card ≤ ∑ u ∈ Q, (S₅₁_col.filter (fun r => r ∣ sigma 1 (u ^ 4))).card :=
        hQ_nq_le.trans hsum_Q_nq_le_Q
      _ = ∑ r ∈ S₅₁_col, (Q.filter (fun u => r ∣ sigma 1 (u ^ 4))).card := hswap
      _ ≤ ∑ _r ∈ S₅₁_col, 2 := Finset.sum_le_sum hr_cap
      _ = 2 * S₅₁_col.card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hQ_bound : Q.card ≤ 2 * S₅₁_col.card + 1 := by omega
  have h73 : 73 ≤ S₅₁_col.card := by omega
  exact ⟨hQ_bound, h73⟩

end OddPerfect
