module

public import OddPerfect.SixthPowerFreePrimeCompositeSplit
public import OddPerfect.OddValuationCycleObstruction
public import OddPerfect.PrimeByPrimeMultiplicityConservation
public import OddPerfect.ZelinskyCollisionDischarge
public import OddPerfect.SixthPowerFreeQuarticCollisionPinch
public import OddPerfect.SixthPowerFreeBipartiteSlackPinch
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Quartic Chain Baseline, Target Reuse, and Non-Cube Block Invariants

Formalizes:
1. Composed block definitions (`quarticFirstFactor`, `quarticSecondFactor`, `quarticPoly`),
   coprimality outside `31`, non-squareness, `two_odd_valuations`, and `two_edges_in_candidate`.
2. Qualifying quartic chains (`quarticChainSources`, `quarticChainIntermediates`), Euler-prime
   avoidance (`quartic_sigma_ne_euler_prime`), `S₅₁_col` factor forcing when `q ∣ σ(w^4)`, and
   the baseline bipartite incidence bound `4 * D ≥ 2 * k - 1`.
3. Target reuse modulo `t`, root caps (`≤ 2` and `≤ 6`), upward ordering `w < t`, absence of odd
   roots `< s^2 + s + 1`, and the `t = 73` (`w = 4153, 22639`) regression case via Lucas primality.
4. Elementary non-cube exclusions and exact `(e₁, e₂, e₃, e₄)` block invariants (`expCount`).
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-! ## 1. Composed Block Definitions & Core `two_edges_in_candidate` Arithmetic -/

@[expose] def quarticFirstFactor (w : ℕ) : ℕ := w ^ 2 - w + 1

@[expose] def quarticSecondFactor (w : ℕ) : ℕ :=
  w ^ 6 + 3 * w ^ 5 + 5 * w ^ 4 + 6 * w ^ 3 + 7 * w ^ 2 + 6 * w + 3

@[expose] def quarticPoly (w : ℕ) : ℕ := w ^ 4 + w ^ 3 + w ^ 2 + w + 1

theorem quartic_phi3_factor_product (w : ℕ) :
    (quarticPoly w) ^ 2 + quarticPoly w + 1 = quarticFirstFactor w * quarticSecondFactor w :=
  phi3_comp_phi5_factorization w

theorem quartic_factors_coprime {w : ℕ}
    (h31 : ¬ 31 ∣ quarticFirstFactor w * quarticSecondFactor w) :
    (quarticFirstFactor w).Coprime (quarticSecondFactor w) := by
  let Q := w ^ 4 + 4 * w ^ 3 + 8 * w ^ 2 + 10 * w + 9
  have hBezout : (25 + Q * (5 * w + 1)) * quarticFirstFactor w =
      (5 * w + 1) * quarticSecondFactor w + 31 := by
    dsimp [Q, quarticFirstFactor, quarticSecondFactor]
    zify [Nat.le_self_pow (by decide : 2 ≠ 0) w]
    ring
  apply Nat.coprime_of_dvd
  intro p hp hA hB
  have hD := hA.mul_left (25 + Q * (5 * w + 1))
  rw [hBezout] at hD
  have hp31 : p ∣ 31 := (Nat.dvd_add_right (hB.mul_left (5 * w + 1))).mp hD
  have heq := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 31)).mp hp31
  exact h31 (heq ▸ hA.trans (dvd_mul_right _ _))

theorem quarticFirstFactor_not_isSquare {w : ℕ} (hw : 19 ≤ w) :
    ¬ IsSquare (quarticFirstFactor w) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = 19 + k := Nat.exists_eq_add_of_le hw
  have hA : quarticFirstFactor (19 + k) = k ^ 2 + 37 * k + 343 := by
    unfold quarticFirstFactor
    rw [show (19 + k) ^ 2 = (19 + k) + (k ^ 2 + 37 * k + 342) by ring]
    omega
  rw [hA]
  rintro ⟨y, hy⟩
  exact Nat.not_exists_sq' (m := 18 + k) (n := k ^ 2 + 37 * k + 343)
    (by nlinarith) (by nlinarith) ⟨y, by simpa [pow_two] using hy.symm⟩

theorem quarticSecondFactor_not_isSquare {w : ℕ} (hw : 19 ≤ w) :
    ¬ IsSquare (quarticSecondFactor w) := by
  let P := 16 * w ^ 3 + 24 * w ^ 2 + 22 * w + 15
  have hlo : P ^ 2 < 256 * quarticSecondFactor w := by
    dsimp [P, quarticSecondFactor]
    ring_nf
    omega
  have hhi : 256 * quarticSecondFactor w < (P + 1) ^ 2 := by
    obtain ⟨k, hk⟩ : ∃ k, w = 19 + k := Nat.exists_eq_add_of_le hw
    dsimp [P, quarticSecondFactor]
    rw [hk]
    ring_nf
    omega
  rintro ⟨y, hy⟩
  exact Nat.not_exists_sq' hlo hhi ⟨16 * y, by rw [hy]; ring⟩

private theorem odd_factor_of_nonsquare_local {a : ℕ} (ha : ¬ IsSquare a) :
    ∃ p, p.Prime ∧ Odd (a.factorization p) := by
  by_contra! h
  exact ha (Nat.isSquare_iff_even_factorization.mpr h)

theorem two_odd_valuations {w s : ℕ} (hw : 19 ≤ w)
    (hs : s = w ^ 4 + w ^ 3 + w ^ 2 + w + 1) (h31 : ¬ 31 ∣ s ^ 2 + s + 1) :
    ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p ≠ r ∧
      Odd ((s ^ 2 + s + 1).factorization p) ∧ Odd ((s ^ 2 + s + 1).factorization r) := by
  have hprod : s ^ 2 + s + 1 = quarticFirstFactor w * quarticSecondFactor w :=
    hs ▸ quartic_phi3_factor_product w
  rw [hprod] at h31 ⊢
  have hcop := quartic_factors_coprime h31
  obtain ⟨p, hp, hpA⟩ := odd_factor_of_nonsquare_local (quarticFirstFactor_not_isSquare hw)
  obtain ⟨r, hr, hrB⟩ := odd_factor_of_nonsquare_local (quarticSecondFactor_not_isSquare hw)
  have hpd := Nat.dvd_of_mem_primeFactors (p := p) (n := quarticFirstFactor w)
    (Finsupp.mem_support_iff.mpr hpA.pos.ne')
  have hrd := Nat.dvd_of_mem_primeFactors (p := r) (n := quarticSecondFactor w)
    (Finsupp.mem_support_iff.mpr hrB.pos.ne')
  have hpB : ¬ p ∣ quarticSecondFactor w := fun hd =>
    hp.not_dvd_one (hcop ▸ Nat.dvd_gcd hpd hd)
  have hrA : ¬ r ∣ quarticFirstFactor w := fun hd =>
    hr.not_dvd_one (hcop ▸ Nat.dvd_gcd hd hrd)
  have hA0 : quarticFirstFactor w ≠ 0 := by unfold quarticFirstFactor; omega
  have hB0 : quarticSecondFactor w ≠ 0 := by unfold quarticSecondFactor; positivity
  simp only [Nat.factorization_mul hA0 hB0, Finsupp.add_apply]
  exact ⟨p, r, hp, hr, fun e => hpB (e ▸ hrd),
    by simpa [Nat.factorization_eq_zero_of_not_dvd hpB] using hpA,
    by simpa [Nat.factorization_eq_zero_of_not_dvd hrA] using hrB⟩

theorem two_edges_in_candidate {N w s : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hw : w ∈ N.primeFactors) (hs : s ∈ N.primeFactors) (he : N.factorization s = 2)
    (hchain : s = w ^ 4 + w ^ 3 + w ^ 2 + w + 1) :
    ∃ p r : ℕ, p ≠ r ∧ oddSigmaEdge N s p ∧ oddSigmaEdge N s r := by
  have hws := sixth_power_free_min_prime_ge_53 ho hN hfree hw
  have hsPrime := Nat.prime_of_mem_primeFactors hs
  have hsOdd := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hs)
  have hpoly : sigma 1 (s ^ 2) = s ^ 2 + s + 1 := by
    rw [sigma_one_apply_prime_pow hsPrime]
    simp [Finset.sum_range_succ]
    ring
  obtain ⟨b, hNb, hcop⟩ := exists_coprime_cofactor_of_exact_prime_pow hsPrime
    (he ▸ Nat.ordProj_dvd N s)
    ((hsPrime.pow_dvd_iff_le_factorization hN.2.ne').not.mpr (by omega : ¬ 2 + 1 ≤ N.factorization s))
  have hdiv : s ^ 2 + s + 1 ∣ N := by
    apply odd_dvd_perfect_of_dvd_sum_divisors hN hNb hcop ((hsOdd.pow.add_odd hsOdd).add_one)
    rw [← sigma_one_apply, hpoly]
  have h31 : ¬ 31 ∣ s ^ 2 + s + 1 := by
    intro hd
    have hx : 31 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, hd.trans hdiv, hN.2.ne'⟩
    have := sixth_power_free_min_prime_ge_53 ho hN hfree hx
    omega
  obtain ⟨p, r, hp, hr, hpr, hvp, hvr⟩ := two_odd_valuations (by omega : 19 ≤ w) hchain h31
  have edge (v : ℕ) (hv : Odd ((s ^ 2 + s + 1).factorization v)) : oddSigmaEdge N s v := by
    have hmem : v ∈ (s ^ 2 + s + 1).primeFactors := Finsupp.mem_support_iff.mpr hv.pos.ne'
    exact ⟨hs, Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hmem,
      (Nat.dvd_of_mem_primeFactors hmem).trans hdiv, hN.2.ne'⟩, by simpa [he, hpoly] using hv⟩
  exact ⟨p, r, hpr, edge p hvp, edge r hvr⟩

/-! ## 2. Qualifying Quartic Chains & Baseline `4 * D ≥ 2 * k - 1` -/

private theorem sigma_one_four_local {p : ℕ} (hp : p.Prime) :
    sigma 1 (p ^ 4) = p ^ 4 + p ^ 3 + p ^ 2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

private theorem sigma_one_sq_local {p : ℕ} (hp : p.Prime) :
    sigma 1 (p ^ 2) = p ^ 2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

theorem quartic_sigma_ne_euler_prime {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    ∀ w ∈ largeSources N q, sigma 1 (w ^ 4) ≠ q := by
  intro w hw heq
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  obtain ⟨hq12, _⟩ := three_free_euler_prime_mod_twelve ho hN hq hq4 he h3
  have hdich := sixth_power_free_quartic_cardFactors_mod_three_dichotomy ho hN hq hq4 he hev hfree
  by_cases hw3 : w % 3 = 1
  · have hw_prime : w.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hw).1
    have hsig_eq : sigma 1 (w ^ 4) = w ^ 4 + w ^ 3 + w ^ 2 + w + 1 := sigma_one_four_local hw_prime
    have hsig_mod3 : sigma 1 (w ^ 4) % 3 = 2 := by
      rw [hsig_eq]
      have hc : w ≡ 1 [MOD 3] := hw3
      have hp : w ^ 4 + w ^ 3 + w ^ 2 + w + 1 ≡
          1 ^ 4 + 1 ^ 3 + 1 ^ 2 + 1 + 1 [MOD 3] :=
        ((((hc.pow 4).add (hc.pow 3)).add (hc.pow 2)).add hc).add (Nat.ModEq.refl 1)
      change (w ^ 4 + w ^ 3 + w ^ 2 + w + 1) % 3 = (1 ^ 4 + 1 ^ 3 + 1 ^ 2 + 1 + 1) % 3 at hp
      omega
    rw [heq] at hsig_mod3
    omega
  · have hw_Q23 : w ∈ twoModThreeLargeSources N q := Finset.mem_filter.mpr ⟨hw, hw3⟩
    have hnq : ¬ q ∣ sigma 1 (w ^ 4) := (hdich.2 w hw_Q23).1
    exact hnq (heq ▸ dvd_rfl)

theorem quartic_oneModThree_euler_dvd_has_S51_col_factor {N q w : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hw : w ∈ oneModThreeLargeSources N q) (hqw : q ∣ sigma 1 (w ^ 4)) :
    2 ≤ cardFactors (sigma 1 (w ^ 4)) ∧
    ∃ s ∈ ((squareSources N).filter (· % 5 = 1)).filter (fun r => indegAt N q r = 2),
      Odd ((sigma 1 (w ^ 4)).factorization s) := by
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have h5 : ¬ 5 ∣ N := sixth_power_free_five_not_dvd ho hN hfree
  have hq1 : N.factorization q = 1 := sixth_power_free_euler_exponent_one ho hN hq he hfree
  obtain ⟨hq12, _⟩ := three_free_euler_prime_mod_twelve ho hN hq hq4 he h3
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hq_odd : Odd q := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)
  obtain ⟨hw_lg, hw3⟩ := Finset.mem_filter.mp hw
  obtain ⟨hw_mem, _, hw_neq, _⟩ := Finset.mem_filter.mp hw_lg
  have hw_prime : w.Prime := Nat.prime_of_mem_primeFactors hw_mem
  have hw4 : N.factorization w = 4 :=
    (three_free_sixthPowerFree_forces_147_largeSources ho hN hq hq4 he hev h3 hfree).1 w hw_lg
  have hsig_eq : sigma 1 (w ^ 4) = w ^ 4 + w ^ 3 + w ^ 2 + w + 1 := sigma_one_four_local hw_prime
  have hsig_pos : 0 < sigma 1 (w ^ 4) := by rw [hsig_eq]; positivity
  have hsig_ne0 : sigma 1 (w ^ 4) ≠ 0 := hsig_pos.ne'
  have hsig_mod3 : sigma 1 (w ^ 4) % 3 = 2 := by
    rw [hsig_eq]
    have hc : w ≡ 1 [MOD 3] := hw3
    have hp : w ^ 4 + w ^ 3 + w ^ 2 + w + 1 ≡
        1 ^ 4 + 1 ^ 3 + 1 ^ 2 + 1 + 1 [MOD 3] :=
      ((((hc.pow 4).add (hc.pow 3)).add (hc.pow 2)).add hc).add (Nat.ModEq.refl 1)
    change (w ^ 4 + w ^ 3 + w ^ 2 + w + 1) % 3 = (1 ^ 4 + 1 ^ 3 + 1 ^ 2 + 1 + 1) % 3 at hp
    omega
  have hq_fac_le1 : (sigma 1 (w ^ 4)).factorization q ≤ 1 := by
    have hsum := factorization_eq_sum_sigma_factorizations hN hq_odd hq_prime
    have hle := Finset.single_le_sum
      (f := fun p => (sigma 1 (p ^ N.factorization p)).factorization q)
      (fun _ _ => Nat.zero_le _) hw_mem
    rw [hw4] at hle
    omega
  have hq_fac_ge1 : 1 ≤ (sigma 1 (w ^ 4)).factorization q :=
    (hq_prime.dvd_iff_one_le_factorization hsig_ne0).mp hqw
  have hq_fac1 : (sigma 1 (w ^ 4)).factorization q = 1 := by omega
  let m := sigma 1 (w ^ 4) / q
  have hmul : sigma 1 (w ^ 4) = q * m := (Nat.mul_div_cancel' hqw).symm
  have hm_ne0 : m ≠ 0 := by
    intro hm0
    rw [hm0, mul_zero] at hmul
    exact hsig_ne0 hmul
  have hqm_fac : (sigma 1 (w ^ 4)).factorization = q.factorization + m.factorization := by
    rw [hmul, Nat.factorization_mul hq_prime.ne_zero hm_ne0]
  have hm_not_dvd_q : ¬ q ∣ m := by
    intro hdvd
    have hq2 : 2 ≤ (sigma 1 (w ^ 4)).factorization q := by
      rw [hqm_fac, Finsupp.add_apply, hq_prime.factorization_self]
      have := (hq_prime.dvd_iff_one_le_factorization hm_ne0).mp hdvd
      omega
    omega
  have hm_mod3 : m % 3 = 2 := by
    have hmod : (sigma 1 (w ^ 4)) % 3 = ((q % 3) * (m % 3)) % 3 := by
      rw [hmul, Nat.mul_mod]
    have hq3 : q % 3 = 1 := by omega
    rw [hsig_mod3, hq3] at hmod
    omega
  have hm_gt1 : 1 < m := by
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_ne0
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hm_pos) with hm1 | hmgt1
    · exfalso
      rw [← hm1] at hm_mod3
      omega
    · exact hmgt1
  have hcard_ge2 : 2 ≤ cardFactors (sigma 1 (w ^ 4)) := by
    rw [hmul, cardFactors_mul hq_prime.ne_zero hm_ne0, cardFactors_apply_prime hq_prime]
    have hpos : 0 < cardFactors m := cardFactors_pos_iff_one_lt.mpr hm_gt1
    omega
  have hm_not_sq : ¬ IsSquare m := by
    rintro ⟨y, hy⟩
    have hy_mod3 : (y * y) % 3 = m % 3 := by rw [← hy]
    rw [Nat.mul_mod, hm_mod3] at hy_mod3
    have hcases : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · simp [h0] at hy_mod3
    · simp [h1] at hy_mod3
    · simp [h2] at hy_mod3
  obtain ⟨s, hs_prime, hs_odd_m⟩ := odd_factor_of_nonsquare_local hm_not_sq
  have hs_dvd_m : s ∣ m :=
    Nat.dvd_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hs_odd_m.pos.ne')
  have hs_neq : s ≠ q := by
    intro hsq
    subst hsq
    exact hm_not_dvd_q hs_dvd_m
  have hs_fac_eq : (sigma 1 (w ^ 4)).factorization s = m.factorization s := by
    have hnot_q : ¬ s ∣ q := fun hd =>
      hs_neq (((Nat.dvd_prime hq_prime).mp hd).resolve_left hs_prime.ne_one)
    rw [hqm_fac, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hnot_q, zero_add]
  have hs_odd_sig : Odd ((sigma 1 (w ^ 4)).factorization s) := by
    rwa [hs_fac_eq]
  have hs_dvd_sig : s ∣ sigma 1 (w ^ 4) := hs_dvd_m.trans ⟨q, by rw [hmul]; ring⟩
  have hw_odd : Odd w := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hw_mem)
  have hsig_odd : Odd (sigma 1 (w ^ 4)) := by
    have hnorm : normalizedQuarticSum w = sigma 1 (w ^ 4) := by
      have hw5 : w % 5 ≠ 1 := by
        intro hmod5
        have hmem5 : w ∈ quarticSourcesOne N q :=
          Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hw_neq, hw_mem⟩, hw4, hmod5⟩
        have hpos := Finset.card_pos.mpr ⟨w, hmem5⟩
        have hle := quarticSourcesOne_card_le_five_exponent (q := q) hN
        have hz : N.factorization 5 = 0 := Nat.factorization_eq_zero_of_not_dvd h5
        omega
      rw [normalizedQuarticSum, ite_eq_right hw5, ← hsig_eq]
    have hmod4 := normalizedQuarticSum_mod_four hw_odd
    rw [hnorm] at hmod4
    exact Nat.odd_iff.mpr (by omega)
  have hs_odd : Odd s := hsig_odd.of_dvd_nat hs_dvd_sig
  have hs_N : s ∣ N := by
    apply dvd_perfect_of_exact_prime_pow hN hw_prime (hw4 ▸ Nat.ordProj_dvd N w)
      ((hw_prime.pow_dvd_iff_le_factorization hN.2.ne').not.mpr (by omega))
      hs_prime hs_odd
    rw [← sigma_one_apply]
    exact hs_dvd_sig
  have hs_mem_N : s ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hs_prime, hs_N, hN.2.ne'⟩
  have hs_mod5 : s % 5 = 1 := by
    have hw_ge3 : 3 ≤ w := by have := hw_prime.two_le; omega
    have hw5 : w % 5 ≠ 1 := by
      intro hmod5
      have hmem5 : w ∈ quarticSourcesOne N q :=
        Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hw_neq, hw_mem⟩, hw4, hmod5⟩
      have hpos := Finset.card_pos.mpr ⟨w, hmem5⟩
      have hle := quarticSourcesOne_card_le_five_exponent (q := q) hN
      have hz : N.factorization 5 = 0 := Nat.factorization_eq_zero_of_not_dvd h5
      omega
    have hnorm : normalizedQuarticSum w = sigma 1 (w ^ 4) := by
      rw [normalizedQuarticSum, ite_eq_right hw5, ← hsig_eq]
    exact (quartic_sigma_properties hw_prime hw_ge3).2.2.2 s hs_prime (hnorm ▸ hs_dvd_sig)
  have hs_N_fac_le2 : N.factorization s ≤ 2 := by
    have hs_pos : 0 < N.factorization s := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hs_mem_N)
    have hs_lt6 : ¬ 6 ≤ N.factorization s := fun hge =>
      hfree s hs_prime ((hs_prime.pow_dvd_iff_le_factorization hN.2.ne').2 hge)
    obtain ⟨k, hk⟩ := hev s hs_neq
    rcases (show N.factorization s = 2 ∨ N.factorization s = 4 by omega) with h2 | h4
    · omega
    · exfalso
      have h5_sig : 5 ∣ sigma 1 (s ^ 4) := by
        rw [sigma_one_four_local hs_prime]
        apply Nat.dvd_of_mod_eq_zero
        simp [Nat.add_mod, Nat.pow_mod, hs_mod5]
      have h5_N : 5 ∣ N := by
        apply dvd_perfect_of_exact_prime_pow hN hs_prime (h4 ▸ Nat.ordProj_dvd N s)
          ((hs_prime.pow_dvd_iff_le_factorization hN.2.ne').not.mpr (by omega))
          (by decide : Nat.Prime 5) (by decide : Odd 5)
        rw [← sigma_one_apply]
        exact h5_sig
      exact h5 h5_N
  have hs_exp2 : N.factorization s = 2 := by
    have hs_pos : 0 < N.factorization s := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hs_mem_N)
    obtain ⟨k, hk⟩ := hev s hs_neq
    omega
  have hs_ne3 : s ≠ 3 := fun h => h3 (h ▸ hs_N)
  have hs_sq : s ∈ squareSources N := Finset.mem_filter.mpr ⟨hs_mem_N, hs_ne3, hs_exp2⟩
  have hs_S51 : s ∈ (squareSources N).filter (· % 5 = 1) :=
    Finset.mem_filter.mpr ⟨hs_sq, hs_mod5⟩
  have hs_sig_le2 : (sigma 1 (w ^ 4)).factorization s ≤ 2 := by
    have hsum := factorization_eq_sum_sigma_factorizations hN hs_odd hs_prime
    have hle := Finset.single_le_sum
      (f := fun p => (sigma 1 (p ^ N.factorization p)).factorization s)
      (fun _ _ => Nat.zero_le _) hw_mem
    rw [hw4] at hle
    omega
  have hs_sig_eq1 : (sigma 1 (w ^ 4)).factorization s = 1 := by
    obtain ⟨k, hk⟩ := hs_odd_sig
    omega
  have hs_indeg2 : indegAt N q s = 2 := by
    have hmut := (euler_linear_and_exponent_two_mutual_exclusion ho hN hq hq4 he hev).2 s hs_mem_N hs_exp2
    rcases hmut with ⟨hi2, _, _⟩ | ⟨_, _, p, _, hs2_dvd_p, hnot_other⟩
    · exact hi2
    · exfalso
      have hcomp_w : oddComponentSigma N q w = sigma 1 (w ^ 4) := by
        unfold oddComponentSigma
        simp only [hw_neq, ite_false, hw4]
      have hwp : w = p := by
        by_contra hne
        exact hnot_other w hw_mem hne (hcomp_w.symm ▸ hs_dvd_sig)
      rw [← hwp, hcomp_w] at hs2_dvd_p
      have h2le : 2 ≤ (sigma 1 (w ^ 4)).factorization s :=
        (hs_prime.pow_dvd_iff_le_factorization hsig_ne0).mp hs2_dvd_p
      omega
  exact ⟨hcard_ge2, s, Finset.mem_filter.mpr ⟨hs_S51, hs_indeg2⟩, hs_odd_sig⟩

@[expose] def quarticChainSources (N q : ℕ) : Finset ℕ :=
  (largeSources N q).filter (fun w => (sigma 1 (w ^ 4)).Prime)

@[expose] def quarticChainIntermediates (N q : ℕ) : Finset ℕ :=
  (quarticChainSources N q).image (fun w => sigma 1 (w ^ 4))

theorem quarticChainSources_eq_oneModThree_prime_and_card {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    quarticChainSources N q = (oneModThreeLargeSources N q).filter (fun w => (sigma 1 (w ^ 4)).Prime) ∧
    (∀ w ∈ quarticChainSources N q, ¬ q ∣ sigma 1 (w ^ 4)) ∧
    quarticChainIntermediates N q ⊆
      ((squareSources N).filter (· % 5 = 1)).filter (fun r => indegAt N q r = 2) ∧
    (quarticChainIntermediates N q).card = (quarticChainSources N q).card := by
  have hdich := sixth_power_free_quartic_cardFactors_mod_three_dichotomy ho hN hq hq4 he hev hfree
  have hne_q := quartic_sigma_ne_euler_prime ho hN hq hq4 he hev hfree
  have hhit := (sixth_power_free_largeSources_hit_S51_col ho hN hq hq4 he hev hfree).1
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hpart1 :
      quarticChainSources N q =
        (oneModThreeLargeSources N q).filter (fun w => (sigma 1 (w ^ 4)).Prime) := by
    ext w
    simp only [quarticChainSources, oneModThreeLargeSources, Finset.mem_filter]
    constructor
    · rintro ⟨hw_lg, hw_prime⟩
      by_cases hw3 : w % 3 = 1
      · exact ⟨⟨hw_lg, hw3⟩, hw_prime⟩
      · exfalso
        exact (hdich.2 w (Finset.mem_filter.mpr ⟨hw_lg, hw3⟩)).2.2.2.1 hw_prime
    · rintro ⟨⟨hw_lg, _⟩, hw_prime⟩
      exact ⟨hw_lg, hw_prime⟩
  have hpart2 : ∀ w ∈ quarticChainSources N q, ¬ q ∣ sigma 1 (w ^ 4) := by
    intro w hw hdvd
    obtain ⟨hw_lg, hw_sig_prime⟩ := Finset.mem_filter.mp hw
    have heq := (Nat.dvd_prime hw_sig_prime).mp hdvd |>.resolve_left hq_prime.ne_one
    exact hne_q w hw_lg heq.symm
  have hpart3 :
      quarticChainIntermediates N q ⊆
        ((squareSources N).filter (· % 5 = 1)).filter (fun r => indegAt N q r = 2) := by
    intro s hs
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hs
    have hw_lg := (Finset.mem_filter.mp hw).1
    have hw_sig_prime := (Finset.mem_filter.mp hw).2
    obtain ⟨r, hr_col, hr_dvd⟩ := hhit w hw_lg (hpart2 w hw)
    have hr_S51 := (Finset.mem_filter.mp hr_col).1
    have hr_sq := (Finset.mem_filter.mp hr_S51).1
    have hr_prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr_sq).1
    have hr_eq : r = sigma 1 (w ^ 4) := (Nat.prime_dvd_prime_iff_eq hr_prime hw_sig_prime).mp hr_dvd
    rwa [← hr_eq]
  have hpart4 : (quarticChainIntermediates N q).card = (quarticChainSources N q).card := by
    unfold quarticChainIntermediates
    refine Finset.card_image_of_injOn ?_
    intro w₁ hw₁ w₂ hw₂ heq
    have hw₁_prime := Nat.prime_of_mem_primeFactors
      (Finset.mem_filter.mp (Finset.mem_filter.mp hw₁).1).1
    have hw₂_prime := Nat.prime_of_mem_primeFactors
      (Finset.mem_filter.mp (Finset.mem_filter.mp hw₂).1).1
    dsimp only at heq
    rw [sigma_one_four_local hw₁_prime, sigma_one_four_local hw₂_prime] at heq
    rcases lt_trichotomy w₁ w₂ with hlt | rfl | hgt
    · have h2 : w₁ ^ 2 < w₂ ^ 2 := Nat.pow_lt_pow_left hlt (by decide)
      have h3 : w₁ ^ 3 < w₂ ^ 3 := Nat.pow_lt_pow_left hlt (by decide)
      have h4 : w₁ ^ 4 < w₂ ^ 4 := Nat.pow_lt_pow_left hlt (by decide)
      omega
    · rfl
    · have h2 : w₂ ^ 2 < w₁ ^ 2 := Nat.pow_lt_pow_left hgt (by decide)
      have h3 : w₂ ^ 3 < w₁ ^ 3 := Nat.pow_lt_pow_left hgt (by decide)
      have h4 : w₂ ^ 4 < w₁ ^ 4 := Nat.pow_lt_pow_left hgt (by decide)
      omega
  exact ⟨hpart1, hpart2, hpart3, hpart4⟩

open Classical in
theorem quartic_chain_baseline_four_mul_targets_ge_two_mul_sub_one {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (K : Finset ℕ) (hK_sub : K ⊆ squareSources N)
    (hK_chain : ∀ s ∈ K, ∃ w ∈ N.primeFactors, N.factorization w = 4 ∧
      s = w ^ 4 + w ^ 3 + w ^ 2 + w + 1) :
    let incidences := (K ×ˢ (N.primeFactors.erase q)).filter (fun st => oddSigmaEdge N st.1 st.2)
    let targets := incidences.image Prod.snd
    targets ⊆ oneModThreeLargeSources N q ∧
    (∀ t ∈ targets, N.factorization t = 4) ∧
    (1 ≤ K.card → 2 * K.card - 1 ≤ incidences.card) ∧
    (1 ≤ K.card → 2 * K.card - 1 ≤ 4 * targets.card) := by
  intro incidences targets
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have hq1 : N.factorization q = 1 := sixth_power_free_euler_exponent_one ho hN hq he hfree
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hq_odd : Odd q := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)
  have hlg4 : ∀ u ∈ largeSources N q, N.factorization u = 4 :=
    (three_free_sixthPowerFree_forces_147_largeSources ho hN hq hq4 he hev h3 hfree).1
  have hrout := (sixth_power_free_oddSigma_vacuum_and_routing ho hN hq hq4 he hev hfree).2.1
  have htargets_sub : targets ⊆ oneModThreeLargeSources N q := by
    intro t ht
    obtain ⟨⟨s, t'⟩, hst, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hst_mem, hedge⟩ := Finset.mem_filter.mp hst
    obtain ⟨hsK, ht_erase⟩ := Finset.mem_product.mp hst_mem
    have htq : t' ≠ q := (Finset.mem_erase.mp ht_erase).1
    rcases hrout s (hK_sub hsK) t' hedge with rfl | ht_Q13
    · exact absurd rfl htq
    · exact ht_Q13
  have htargets_exp4 : ∀ t ∈ targets, N.factorization t = 4 := fun t ht =>
    hlg4 t (Finset.mem_filter.mp (htargets_sub ht)).1
  let allIncidences := (K ×ˢ N.primeFactors).filter (fun st => oddSigmaEdge N st.1 st.2)
  have hall_ge : 2 * K.card ≤ allIncidences.card := by
    have hfib : allIncidences.card =
        ∑ s ∈ K, (allIncidences.filter (fun st => st.1 = s)).card := by
      refine Finset.card_eq_sum_card_fiberwise fun st hst => ?_
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hst).1).1
    rw [hfib]
    calc
      2 * K.card = ∑ _s ∈ K, 2 := by simp [Finset.sum_const, Nat.mul_comm]
      _ ≤ ∑ s ∈ K, (allIncidences.filter (fun st => st.1 = s)).card := by
            refine Finset.sum_le_sum fun s hsK => ?_
            have hs_sq := hK_sub hsK
            obtain ⟨hs_mem, _, hs_exp2⟩ := Finset.mem_filter.mp hs_sq
            obtain ⟨w, hw_mem, _, hchain⟩ := hK_chain s hsK
            obtain ⟨p, r, hpr, hsp, hsr⟩ :=
              two_edges_in_candidate ho hN hfree hw_mem hs_mem hs_exp2 hchain
            have hsub2 : ({(s, p), (s, r)} : Finset (ℕ × ℕ)) ⊆
                allIncidences.filter (fun st => st.1 = s) := by
              intro st hst
              simp only [Finset.mem_insert, Finset.mem_singleton] at hst
              rcases hst with rfl | rfl
              · exact Finset.mem_filter.mpr
                  ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hsK, hsp.2.1⟩, hsp⟩, rfl⟩
              · exact Finset.mem_filter.mpr
                  ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hsK, hsr.2.1⟩, hsr⟩, rfl⟩
            have hne_pair : (s, p) ≠ (s, r) := fun h => hpr (congrArg Prod.snd h)
            have hcard2 : ({(s, p), (s, r)} : Finset (ℕ × ℕ)).card = 2 :=
              Finset.card_pair hne_pair
            exact hcard2 ▸ Finset.card_le_card hsub2
  let qIncidences := K.filter (fun s => oddSigmaEdge N s q)
  have hq_le1 : qIncidences.card ≤ 1 := by
    have hle : qIncidences.card ≤ N.factorization q := by
      apply card_le_factorization_of_sigma_sources hN hq_odd hq_prime qIncidences
      · exact (Finset.filter_subset _ _).trans
          (hK_sub.trans (Finset.filter_subset _ _))
      · intro s hs
        have hedge := (Finset.mem_filter.mp hs).2
        exact Nat.dvd_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hedge.2.2.pos.ne')
    omega
  have hall_le : allIncidences.card ≤ incidences.card + qIncidences.card := by
    have hsub : allIncidences ⊆ incidences ∪ qIncidences.image (fun s => (s, q)) := by
      intro ⟨s, t⟩ hst
      obtain ⟨hst_mem, hedge⟩ := Finset.mem_filter.mp hst
      obtain ⟨hsK, ht_mem⟩ := Finset.mem_product.mp hst_mem
      by_cases htq : t = q
      · subst htq
        exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨s, Finset.mem_filter.mpr ⟨hsK, hedge⟩, rfl⟩)
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨hsK, Finset.mem_erase.mpr ⟨htq, ht_mem⟩⟩, hedge⟩)
    calc
      allIncidences.card ≤ (incidences ∪ qIncidences.image (fun s => (s, q))).card :=
        Finset.card_le_card hsub
      _ ≤ incidences.card + (qIncidences.image (fun s => (s, q))).card :=
        Finset.card_union_le _ _
      _ ≤ incidences.card + qIncidences.card :=
        Nat.add_le_add_left Finset.card_image_le _
  have hinc_ge : 1 ≤ K.card → 2 * K.card - 1 ≤ incidences.card := by
    intro _
    omega
  have hinc_le_targets : incidences.card ≤ 4 * targets.card := by
    have hfib : incidences.card =
        ∑ t ∈ targets, (incidences.filter (fun st => st.2 = t)).card := by
      refine Finset.card_eq_sum_card_fiberwise fun st hst => ?_
      exact Finset.mem_image_of_mem _ hst
    rw [hfib]
    calc
      ∑ t ∈ targets, (incidences.filter (fun st => st.2 = t)).card
          ≤ ∑ _t ∈ targets, 4 := by
            refine Finset.sum_le_sum fun t ht => ?_
            have ht_Q13 := htargets_sub ht
            have ht_lg := (Finset.mem_filter.mp ht_Q13).1
            have ht_mem := (Finset.mem_filter.mp ht_lg).1
            have ht_prime := Nat.prime_of_mem_primeFactors ht_mem
            have ht_odd : Odd t := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors ht_mem)
            have ht_exp4 : N.factorization t = 4 := htargets_exp4 t ht
            let src_t := K.filter (fun s => oddSigmaEdge N s t)
            have hsrc_le : src_t.card ≤ N.factorization t := by
              apply card_le_factorization_of_sigma_sources hN ht_odd ht_prime src_t
              · exact (Finset.filter_subset _ _).trans
                  (hK_sub.trans (Finset.filter_subset _ _))
              · intro s hs
                have hedge := (Finset.mem_filter.mp hs).2
                exact Nat.dvd_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hedge.2.2.pos.ne')
            have hfib_le : (incidences.filter (fun st => st.2 = t)).card ≤ src_t.card := by
              refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
              · intro st hst
                obtain ⟨hst_inc, rfl⟩ := Finset.mem_filter.mp hst
                obtain ⟨hst_prod, hedge⟩ := Finset.mem_filter.mp hst_inc
                exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hst_prod).1, hedge⟩
              · intro ⟨s₁, t₁⟩ h1 ⟨s₂, t₂⟩ h2 heq
                have ht1 : t₁ = t := (Finset.mem_filter.mp h1).2
                have ht2 : t₂ = t := (Finset.mem_filter.mp h2).2
                dsimp only at heq
                ext <;> simp [heq, ht1, ht2]
            omega
      _ = 4 * targets.card := by simp [Finset.sum_const, Nat.mul_comm]
  have hbound : 1 ≤ K.card → 2 * K.card - 1 ≤ 4 * targets.card := by
    intro hK1
    exact (hinc_ge hK1).trans hinc_le_targets
  exact ⟨htargets_sub, htargets_exp4, hinc_ge, hbound⟩

open Classical in
theorem quarticChainIntermediates_baseline_bound {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let K := quarticChainIntermediates N q
    let incidences := (K ×ˢ (N.primeFactors.erase q)).filter (fun st => oddSigmaEdge N st.1 st.2)
    let targets := incidences.image Prod.snd
    targets ⊆ oneModThreeLargeSources N q ∧
    (∀ t ∈ targets, N.factorization t = 4) ∧
    (1 ≤ K.card → 2 * K.card - 1 ≤ incidences.card) ∧
    (1 ≤ K.card → 2 * K.card - 1 ≤ 4 * targets.card) := by
  intro K incidences targets
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have hlg4 : ∀ u ∈ largeSources N q, N.factorization u = 4 :=
    (three_free_sixthPowerFree_forces_147_largeSources ho hN hq hq4 he hev h3 hfree).1
  have hK_col := (quarticChainSources_eq_oneModThree_prime_and_card ho hN hq hq4 he hev hfree).2.2.1
  have hK_sub : K ⊆ squareSources N := fun s hs =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp (hK_col hs)).1).1
  have hK_chain : ∀ s ∈ K, ∃ w ∈ N.primeFactors, N.factorization w = 4 ∧
      s = w ^ 4 + w ^ 3 + w ^ 2 + w + 1 := by
    intro s hs
    obtain ⟨w, hw_src, rfl⟩ := Finset.mem_image.mp hs
    have hw_lg := (Finset.mem_filter.mp hw_src).1
    have hw_mem := (Finset.mem_filter.mp hw_lg).1
    have hw_prime := Nat.prime_of_mem_primeFactors hw_mem
    exact ⟨w, hw_mem, hlg4 w hw_lg, sigma_one_four_local hw_prime⟩
  exact quartic_chain_baseline_four_mul_targets_ge_two_mul_sub_one
    ho hN hq hq4 he hev hfree K hK_sub hK_chain

/-! ## 3. Target Reuse Modulo `t`, Upward Ordering `w < t`, & Regression Case -/

theorem dvd_quarticFirstFactor_mod_eq_or_add_mod_eq_one {t w₁ w₂ : ℕ} (ht : t.Prime)
    (h1 : t ∣ quarticFirstFactor w₁) (h2 : t ∣ quarticFirstFactor w₂) :
    w₁ % t = w₂ % t ∨ (w₁ + w₂) % t = 1 % t := by
  have hw₁_ne0 : w₁ ≠ 0 := by
    intro h0
    subst h0
    exact ht.not_dvd_one (by simpa [quarticFirstFactor] using h1)
  have hw₂_ne0 : w₂ ≠ 0 := by
    intro h0
    subst h0
    exact ht.not_dvd_one (by simpa [quarticFirstFactor] using h2)
  have : Fact t.Prime := ⟨ht⟩
  have cast_eq (w : ℕ) (hw0 : w ≠ 0) (hd : t ∣ quarticFirstFactor w) :
      (w : ZMod t) ^ 2 - (w : ZMod t) + 1 = 0 := by
    have hle : w ≤ w ^ 2 := Nat.le_self_pow (by decide : 2 ≠ 0) w
    have hz : ((quarticFirstFactor w : ℕ) : ZMod t) = 0 :=
      (ZMod.natCast_eq_zero_iff (quarticFirstFactor w) t).mpr hd
    dsimp [quarticFirstFactor] at hz
    rw [Nat.cast_add, Nat.cast_sub hle] at hz
    push_cast at hz
    exact hz
  have hz1 := cast_eq w₁ hw₁_ne0 h1
  have hz2 := cast_eq w₂ hw₂_ne0 h2
  have hprod : ((w₁ : ZMod t) - (w₂ : ZMod t)) * ((w₁ : ZMod t) + (w₂ : ZMod t) - 1) = 0 := by
    calc
      ((w₁ : ZMod t) - (w₂ : ZMod t)) * ((w₁ : ZMod t) + (w₂ : ZMod t) - 1)
          = ((w₁ : ZMod t) ^ 2 - (w₁ : ZMod t) + 1) - ((w₂ : ZMod t) ^ 2 - (w₂ : ZMod t) + 1) := by
            ring
      _ = 0 - 0 := by rw [hz1, hz2]
      _ = 0 := sub_zero 0
  rcases mul_eq_zero.mp hprod with hsub | hadd
  · left
    have heq : (w₁ : ZMod t) = (w₂ : ZMod t) := sub_eq_zero.mp hsub
    have hval := congrArg ZMod.val heq
    simpa [ZMod.val_natCast] using hval
  · right
    have heq : ((w₁ + w₂ : ℕ) : ZMod t) = ((1 : ℕ) : ZMod t) := by
      push_cast
      exact sub_eq_zero.mp hadd
    have hval := congrArg ZMod.val heq
    rwa [ZMod.val_natCast, ZMod.val_natCast] at hval

theorem card_range_dvd_quarticFirstFactor_le_two {t : ℕ} (ht : t.Prime) :
    ((Finset.range t).filter (fun w => t ∣ quarticFirstFactor w)).card ≤ 2 := by
  let S := (Finset.range t).filter (fun w => t ∣ quarticFirstFactor w)
  rcases S.eq_empty_or_nonempty with h_empty | ⟨w₀, hw₀⟩
  · change S.card ≤ 2
    rw [h_empty]
    simp
  · have ht1 : 1 < t := ht.one_lt
    have hw₀_lt : w₀ < t := Finset.mem_range.mp (Finset.mem_filter.mp hw₀).1
    have hw₀_dvd : t ∣ quarticFirstFactor w₀ := (Finset.mem_filter.mp hw₀).2
    let w₁ := (t + 1 - w₀) % t
    have hsub : S ⊆ {w₀, w₁} := by
      intro w hw
      have hw_lt : w < t := Finset.mem_range.mp (Finset.mem_filter.mp hw).1
      have hw_dvd : t ∣ quarticFirstFactor w := (Finset.mem_filter.mp hw).2
      have hmod := dvd_quarticFirstFactor_mod_eq_or_add_mod_eq_one ht hw_dvd hw₀_dvd
      have h1t : 1 % t = 1 := Nat.mod_eq_of_lt ht1
      rw [h1t, Nat.mod_eq_of_lt hw_lt, Nat.mod_eq_of_lt hw₀_lt] at hmod
      rcases hmod with rfl | hsum
      · exact Finset.mem_insert_self w _
      · apply Finset.mem_insert_of_mem
        rw [Finset.mem_singleton]
        have hw₀_ne0 : w₀ ≠ 0 := by
          intro h0
          subst h0
          exact ht.not_dvd_one (by simpa [quarticFirstFactor] using hw₀_dvd)
        have hq_le : (w + w₀) / t ≤ 1 :=
          Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega : w + w₀ < t * 2))
        have hdm := Nat.div_add_mod (w + w₀) t
        have hcase : w + w₀ = 1 ∨ w + w₀ = t + 1 := by
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq_le with hq0 | hq1
          · left
            rw [hq0, mul_zero, zero_add, hsum] at hdm
            exact hdm.symm
          · right
            rw [hq1, mul_one, hsum] at hdm
            exact hdm.symm
        rcases hcase with h1 | ht1'
        · have hw0 : w = 0 := by omega
          subst hw0
          exact absurd hw_dvd (by simpa [quarticFirstFactor] using ht.not_dvd_one)
        · dsimp [w₁]
          rw [show t + 1 - w₀ = w by omega, Nat.mod_eq_of_lt hw_lt]
    calc
      S.card ≤ ({w₀, w₁} : Finset ℕ).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two

theorem quarticFirstFactor_no_odd_roots_lt_of_sq_add_self_add_one_prime {s : ℕ}
    (hs : Odd s) (ht : (s ^ 2 + s + 1).Prime) :
    ((Finset.range (s ^ 2 + s + 1)).filter
      (fun w => Odd w ∧ (s ^ 2 + s + 1) ∣ quarticFirstFactor w)) = ∅ := by
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hs.pos) with hs1 | hs_gt1
  · have : s = 1 := hs1.symm
    subst this
    decide
  · have hs3 : 3 ≤ s := by
      obtain ⟨k, hk⟩ := hs
      omega
    let t := s ^ 2 + s + 1
    let r₁ := s + 1
    let r₂ := s ^ 2 + 1
    have hr₁_lt : r₁ < r₂ := by
      dsimp [r₁, r₂]
      nlinarith
    have hr₂_lt : r₂ < t := by dsimp [r₂, t]; omega
    have hr₁_dvd : t ∣ quarticFirstFactor r₁ := by
      have heq : quarticFirstFactor r₁ = t := by
        dsimp [quarticFirstFactor, r₁, t]
        zify [Nat.le_self_pow (by decide : 2 ≠ 0) (s + 1)]
        ring
      rw [heq]
    have hr₂_dvd : t ∣ quarticFirstFactor r₂ := by
      have heq : quarticFirstFactor r₂ = (s ^ 2 - s + 1) * t := by
        dsimp [quarticFirstFactor, r₂, t]
        zify [Nat.le_self_pow (by decide : 2 ≠ 0) s,
          (show s ^ 2 + 1 ≤ (s ^ 2 + 1) ^ 2 by nlinarith)]
        ring
      rw [heq]
      exact dvd_mul_left t _
    let S := (Finset.range t).filter (fun w => t ∣ quarticFirstFactor w)
    have hsub : {r₁, r₂} ⊆ S := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hr₁_dvd⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr₂_lt, hr₂_dvd⟩
    have hcard_pair : ({r₁, r₂} : Finset ℕ).card = 2 := Finset.card_pair hr₁_lt.ne
    have hcard_le2 : S.card ≤ 2 := card_range_dvd_quarticFirstFactor_le_two ht
    have hS_eq : ({r₁, r₂} : Finset ℕ) = S :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    rw [Finset.eq_empty_iff_forall_notMem]
    intro w hw
    obtain ⟨hw_range, hw_odd, hw_dvd⟩ := Finset.mem_filter.mp hw
    have hw_S : w ∈ S := Finset.mem_filter.mpr ⟨hw_range, hw_dvd⟩
    rw [← hS_eq] at hw_S
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw_S
    have hr₁_even : ¬ Odd r₁ := by
      obtain ⟨k, hk⟩ := hs
      rw [Nat.not_odd_iff_even]
      exact ⟨k + 1, by dsimp [r₁]; omega⟩
    have hr₂_even : ¬ Odd r₂ := by
      have hs_sq_odd : Odd (s ^ 2) := hs.pow
      obtain ⟨k, hk⟩ := hs_sq_odd
      rw [Nat.not_odd_iff_even]
      exact ⟨k + 1, by dsimp [r₂]; omega⟩
    rcases hw_S with rfl | rfl
    · exact hr₁_even hw_odd
    · exact hr₂_even hw_odd

theorem card_range_dvd_quarticSecondFactor_le_six {t : ℕ} (ht : t.Prime) :
    ((Finset.range t).filter (fun w => t ∣ quarticSecondFactor w)).card ≤ 6 := by
  let : Fact t.Prime := ⟨ht⟩
  let P : Polynomial (ZMod t) :=
    Polynomial.X ^ 6 + Polynomial.C 3 * Polynomial.X ^ 5 + Polynomial.C 5 * Polynomial.X ^ 4 +
      Polynomial.C 6 * Polynomial.X ^ 3 + Polynomial.C 7 * Polynomial.X ^ 2 +
      Polynomial.C 6 * Polynomial.X + Polynomial.C 3
  have hP_deg : P.natDegree ≤ 6 := by
    dsimp [P]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by simp))
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by
      exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)))
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by
      exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)))
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by
      exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)))
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by
      exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)))
    refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) (by
      exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)))
  have hP_ne0 : P ≠ 0 := by
    intro h0
    have hc := congrArg (fun Q : Polynomial (ZMod t) => Q.coeff 6) h0
    simp only [P, Polynomial.coeff_zero, Polynomial.coeff_add, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C] at hc
    norm_num at hc
  have hroots_le : P.roots.toFinset.card ≤ 6 :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' P).trans hP_deg)
  have hle : ((Finset.range t).filter (fun w => t ∣ quarticSecondFactor w)).card ≤
      P.roots.toFinset.card := by
    refine Finset.card_le_card_of_injOn (fun w : ℕ => (w : ZMod t)) ?_ ?_
    · intro w hw
      obtain ⟨_, hw_dvd⟩ := Finset.mem_filter.mp hw
      have hz : ((quarticSecondFactor w : ℕ) : ZMod t) = 0 :=
        (ZMod.natCast_eq_zero_iff (quarticSecondFactor w) t).mpr hw_dvd
      dsimp [quarticSecondFactor] at hz
      push_cast at hz
      have hroot : P.IsRoot (w : ZMod t) := by
        rw [Polynomial.IsRoot]
        simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_C]
        exact hz
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP_ne0).mpr hroot)
    · intro w₁ hw₁ w₂ hw₂ heq
      have h1 : w₁ < t := Finset.mem_range.mp (Finset.mem_filter.mp hw₁).1
      have h2 : w₂ < t := Finset.mem_range.mp (Finset.mem_filter.mp hw₂).1
      have hval := congrArg ZMod.val heq
      rwa [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at hval
  exact hle.trans hroots_le

private theorem pow_le_pow_of_primeFactors_le {M B : ℕ} (hM0 : M ≠ 0)
    (hB : ∀ p ∈ M.primeFactors, p ≤ B) :
    M ≤ B ^ cardFactors M := by
  have hprod : M = ∏ p ∈ M.primeFactors, p ^ M.factorization p :=
    Nat.prod_primeFactors_pow_factorization hM0
  have hcard : cardFactors M = ∑ p ∈ M.primeFactors, M.factorization p := by
    rw [cardFactors_eq_sum_factorization, Finsupp.sum]
    rfl
  calc
    M = ∏ p ∈ M.primeFactors, p ^ M.factorization p := hprod
    _ ≤ ∏ p ∈ M.primeFactors, B ^ M.factorization p := by
          refine Finset.prod_le_prod fun p hp => ?_
          exact Nat.pow_le_pow_left (hB p hp) _
    _ = B ^ (∑ p ∈ M.primeFactors, M.factorization p) := by
          rw [Finset.prod_pow_eq_pow_sum]
    _ = B ^ cardFactors M := by rw [hcard]

theorem quarticFirstFactor_exists_prime_gt_of_cardFactors_le_two {w : ℕ}
    (hw : 2 ≤ w) (hcard : cardFactors (quarticFirstFactor w) ≤ 2) :
    ∃ t ∈ (quarticFirstFactor w).primeFactors, w < t ∧ (quarticFirstFactor w).factorization t = 1 := by
  have hA_ne0 : quarticFirstFactor w ≠ 0 := by unfold quarticFirstFactor; omega
  have hcop : w.Coprime (quarticFirstFactor w) := by
    apply Nat.coprime_of_dvd
    intro p hp hpw hpA
    have hA_eq : quarticFirstFactor w = w * (w - 1) + 1 := by
      unfold quarticFirstFactor
      zify [Nat.le_self_pow (by decide : 2 ≠ 0) w, (by omega : 1 ≤ w)]
      ring
    rw [hA_eq] at hpA
    exact hp.not_dvd_one ((Nat.dvd_add_right (hpw.mul_right (w - 1))).mp hpA)
  have hex : ∃ t ∈ (quarticFirstFactor w).primeFactors, w < t := by
    by_contra! hall
    have hall_le : ∀ p ∈ (quarticFirstFactor w).primeFactors, p ≤ w - 1 := by
      intro p hp
      have hp_le := hall p hp
      have hp_ne : p ≠ w := fun h => by
        subst h
        have hp_prime := Nat.prime_of_mem_primeFactors hp
        have hp_dvd := Nat.dvd_of_mem_primeFactors hp
        exact hp_prime.not_dvd_one (hcop ▸ Nat.dvd_gcd dvd_rfl hp_dvd)
      omega
    have hle := pow_le_pow_of_primeFactors_le hA_ne0 hall_le
    have hpow : (w - 1) ^ cardFactors (quarticFirstFactor w) ≤ (w - 1) ^ 2 :=
      Nat.pow_le_pow_right (by omega) hcard
    have hA_lt : (w - 1) ^ 2 < quarticFirstFactor w := by
      unfold quarticFirstFactor
      zify [Nat.le_self_pow (by decide : 2 ≠ 0) w, (by omega : 1 ≤ w)]
      nlinarith
    omega
  obtain ⟨t, ht_mem, hwt⟩ := hex
  have ht_prime := Nat.prime_of_mem_primeFactors ht_mem
  have ht_pos : 1 ≤ (quarticFirstFactor w).factorization t :=
    (ht_prime.dvd_iff_one_le_factorization hA_ne0).mp (Nat.dvd_of_mem_primeFactors ht_mem)
  have ht_le1 : (quarticFirstFactor w).factorization t ≤ 1 := by
    by_contra! hgt1
    have ht2_dvd : t ^ 2 ∣ quarticFirstFactor w :=
      (ht_prime.pow_dvd_iff_le_factorization hA_ne0).mpr hgt1
    have hA_pos : 0 < quarticFirstFactor w := Nat.pos_of_ne_zero hA_ne0
    have ht2_le : t ^ 2 ≤ quarticFirstFactor w := Nat.le_of_dvd hA_pos ht2_dvd
    have hw1_le : (w + 1) ^ 2 ≤ t ^ 2 := Nat.pow_le_pow_left hwt 2
    have hlt : quarticFirstFactor w < (w + 1) ^ 2 := by
      unfold quarticFirstFactor
      have hle : w ≤ w ^ 2 := Nat.le_self_pow (by decide : 2 ≠ 0) w
      zify [hle]
      nlinarith
    omega
  exact ⟨t, ht_mem, hwt, by omega⟩

theorem quarticSecondFactor_exists_prime_gt_of_cardFactors_le_six {w : ℕ}
    (hw : 2 ≤ w) (hcard : cardFactors (quarticSecondFactor w) ≤ 6) :
    ∃ t ∈ (quarticSecondFactor w).primeFactors, w < t := by
  have hB_ne0 : quarticSecondFactor w ≠ 0 := by unfold quarticSecondFactor; positivity
  by_contra! hall
  have hle := pow_le_pow_of_primeFactors_le hB_ne0 hall
  have hpow : w ^ cardFactors (quarticSecondFactor w) ≤ w ^ 6 :=
    Nat.pow_le_pow_right (by omega) hcard
  have hlt : w ^ 6 < quarticSecondFactor w := by
    unfold quarticSecondFactor
    omega
  omega

private def powModAux : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 1
  | fuel + 1, a, n, m =>
    if n = 0 then 1 % m
    else
      let half := powModAux fuel a (n / 2) m
      let sq := (half * half) % m
      if n % 2 = 0 then sq else (sq * (a % m)) % m

private def powMod (a n m : ℕ) : ℕ := powModAux 64 a n m

private lemma powModAux_cast_zmod (fuel a n m : ℕ) [NeZero m] (hn : n < 2 ^ fuel) :
    ((powModAux fuel a n m : ℕ) : ZMod m) = (a : ZMod m) ^ n := by
  induction fuel generalizing n with
  | zero =>
    have hn0 : n = 0 := by simpa using hn
    subst hn0
    simp [powModAux]
  | succ fuel ih =>
    rw [powModAux]
    split_ifs with h0 hmod
    · subst h0
      simp [ZMod.natCast_mod]
    · have hlt : n / 2 < 2 ^ fuel := by
        rw [pow_succ'] at hn
        omega
      have hhalf := ih (n / 2) hlt
      have hn' : n = 2 * (n / 2) := by omega
      push_cast [ZMod.natCast_mod]
      rw [hhalf]
      conv_rhs => rw [hn', pow_mul', pow_two]
    · have hlt : n / 2 < 2 ^ fuel := by
        rw [pow_succ'] at hn
        omega
      have hhalf := ih (n / 2) hlt
      have hn' : n = 2 * (n / 2) + 1 := by omega
      push_cast [ZMod.natCast_mod]
      rw [hhalf]
      conv_rhs => rw [hn', pow_add, pow_one, pow_mul', pow_two]

private lemma powMod_cast_zmod (a n m : ℕ) [NeZero m] (hn : n < 2 ^ 64) :
    ((powMod a n m : ℕ) : ZMod m) = (a : ZMod m) ^ n :=
  powModAux_cast_zmod 64 a n m hn

private lemma zmod_pow_ne_one_of_powMod {a n m : ℕ} (hm : 1 < m) (hn : n < 2 ^ 64)
    (h1 : powMod a n m ≠ 1) (hlt : powMod a n m < m) :
    (a : ZMod m) ^ n ≠ 1 := by
  have : NeZero m := ⟨by omega⟩
  have : Fact (1 < m) := ⟨hm⟩
  rw [← powMod_cast_zmod a n m hn]
  intro heq
  have hval := congrArg ZMod.val heq
  rw [ZMod.val_natCast_of_lt hlt, ZMod.val_one] at hval
  exact h1 hval

private lemma prime_s1 : Nat.Prime 297544762954421 := by
  apply lucas_primality 297544762954421 ((2 : ℕ) : ZMod 297544762954421)
  · have : NeZero 297544762954421 := ⟨by decide⟩
    rw [show (297544762954421 - 1 : ℕ) = 297544762954420 by rfl,
      ← powMod_cast_zmod 2 297544762954420 297544762954421 (by norm_num)]
    have hval : powMod 2 297544762954420 297544762954421 = 1 := by decide +kernel
    rw [hval]
    norm_num
  · intro q hq hdvd
    have hfac : (297544762954421 - 1 : ℕ) = 2 ^ 2 * 5 * 31 * 67 * 4153 * 1724741 := by norm_num
    rw [hfac] at hdvd
    rcases hq.dvd_mul.mp hdvd with h | h
    · rcases hq.dvd_mul.mp h with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · rcases hq.dvd_mul.mp h with h | h
          · rcases hq.dvd_mul.mp h with h | h
            · have hq2 := (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp (hq.dvd_of_dvd_pow h)
              rcases hq2 with h1 | rfl
              · exact absurd h1 hq.ne_one
              · exact zmod_pow_ne_one_of_powMod (by norm_num) (by norm_num)
                  (by decide +kernel) (by decide +kernel)
            · have hq5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5)).mp h
              subst hq5
              exact zmod_pow_ne_one_of_powMod (by norm_num) (by norm_num)
                (by decide +kernel) (by decide +kernel)
          · have hq31 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 31)).mp h
            subst hq31
            exact zmod_pow_ne_one_of_powMod (by norm_num) (by norm_num)
              (by decide +kernel) (by decide +kernel)
        · have hq67 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 67)).mp h
          subst hq67
          exact zmod_pow_ne_one_of_powMod (by norm_num) (by norm_num)
            (by decide +kernel) (by decide +kernel)
      · have hq4153 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 4153)).mp h
        subst hq4153
        exact zmod_pow_ne_one_of_powMod (by norm_num) (by norm_num)
          (by decide +kernel) (by decide +kernel)
    · have hqbig := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 1724741)).mp h
      subst hqbig
      exact zmod_pow_ne_one_of_powMod (by norm_num) (by norm_num)
        (by decide +kernel) (by decide +kernel)

private lemma prime_s2 : Nat.Prime 262692783167161121 := by
  apply lucas_primality 262692783167161121 ((15 : ℕ) : ZMod 262692783167161121)
  · have : NeZero 262692783167161121 := ⟨by decide⟩
    rw [show (262692783167161121 - 1 : ℕ) = 262692783167161120 by rfl,
      ← powMod_cast_zmod 15 262692783167161120 262692783167161121 (by norm_num)]
    have hval : powMod 15 262692783167161120 262692783167161121 = 1 := by decide +kernel
    rw [hval]
    norm_num
  · intro q hq hdvd
    have hfac : (262692783167161121 - 1 : ℕ) = 2 ^ 5 * 5 * 109 * 283 * 22639 * 2351029 := by
      norm_num
    rw [hfac] at hdvd
    rcases hq.dvd_mul.mp hdvd with h | h
    · rcases hq.dvd_mul.mp h with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · rcases hq.dvd_mul.mp h with h | h
          · rcases hq.dvd_mul.mp h with h | h
            · have hq2 := (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp (hq.dvd_of_dvd_pow h)
              rcases hq2 with h1 | rfl
              · exact absurd h1 hq.ne_one
              · exact zmod_pow_ne_one_of_powMod (by norm_num) (by norm_num)
                  (by decide +kernel) (by decide +kernel)
            · have hq5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5)).mp h
              subst hq5
              exact zmod_pow_ne_one_of_powMod (by norm_num) (by norm_num)
                (by decide +kernel) (by decide +kernel)
          · have hq109 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 109)).mp h
            subst hq109
            exact zmod_pow_ne_one_of_powMod (by norm_num) (by norm_num)
              (by decide +kernel) (by decide +kernel)
        · have hq283 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 283)).mp h
          subst hq283
          exact zmod_pow_ne_one_of_powMod (by norm_num) (by norm_num)
            (by decide +kernel) (by decide +kernel)
      · have hq22639 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 22639)).mp h
        subst hq22639
        exact zmod_pow_ne_one_of_powMod (by norm_num) (by norm_num)
          (by decide +kernel) (by decide +kernel)
    · have hqbig := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2351029)).mp h
      subst hqbig
      exact zmod_pow_ne_one_of_powMod (by norm_num) (by norm_num)
        (by decide +kernel) (by decide +kernel)

theorem quartic_chain_regression_4153_22639_at_73 :
    let w₁ := 4153
    let w₂ := 22639
    let s₁ := quarticPoly w₁
    let s₂ := quarticPoly w₂
    w₁.Prime ∧ w₂.Prime ∧ Nat.Prime 73 ∧
    73 < w₁ ∧ 73 < w₂ ∧
    w₁ % 73 = 65 ∧ w₂ % 73 = 9 ∧ (w₁ + w₂) % 73 = 1 ∧
    s₁ = 297544762954421 ∧ s₂ = 262692783167161121 ∧
    s₁.Prime ∧ s₂.Prime ∧
    73 ∣ quarticFirstFactor w₁ ∧ 73 ∣ quarticFirstFactor w₂ ∧
    (s₁ ^ 2 + s₁ + 1) % (73 ^ 2) = 5183 ∧
    (s₂ ^ 2 + s₂ + 1) % (73 ^ 2) = 73 ∧
    (s₁ ^ 2 + s₁ + 1).factorization 73 = 1 ∧
    (s₂ ^ 2 + s₂ + 1).factorization 73 = 1 := by
  intro w₁ w₂ s₁ s₂
  have hw₁_prime : w₁.Prime := by norm_num [w₁]
  have hw₂_prime : w₂.Prime := by norm_num [w₂]
  have h73_prime : Nat.Prime 73 := by norm_num
  have hs₁_eq : s₁ = 297544762954421 := by norm_num [s₁, w₁, quarticPoly]
  have hs₂_eq : s₂ = 262692783167161121 := by norm_num [s₂, w₂, quarticPoly]
  have hs₁_prime : s₁.Prime := hs₁_eq ▸ prime_s1
  have hs₂_prime : s₂.Prime := hs₂_eq ▸ prime_s2
  have hdvd1 : 73 ∣ quarticFirstFactor w₁ := by norm_num [w₁, quarticFirstFactor]
  have hdvd2 : 73 ∣ quarticFirstFactor w₂ := by norm_num [w₂, quarticFirstFactor]
  have hmod1 : (s₁ ^ 2 + s₁ + 1) % (73 ^ 2) = 5183 := by norm_num [hs₁_eq]
  have hmod2 : (s₂ ^ 2 + s₂ + 1) % (73 ^ 2) = 73 := by norm_num [hs₂_eq]
  have hfac1 : (s₁ ^ 2 + s₁ + 1).factorization 73 = 1 := by
    have h73_dvd : 73 ∣ s₁ ^ 2 + s₁ + 1 := by
      have h1 : 73 ∣ 5183 := by decide
      rw [← hmod1] at h1
      exact Nat.dvd_of_mod_eq_zero (by omega)
    have hge1 : 1 ≤ (s₁ ^ 2 + s₁ + 1).factorization 73 :=
      (h73_prime.dvd_iff_one_le_factorization (by positivity)).mp h73_dvd
    have hnot2 : ¬ 73 ^ 2 ∣ s₁ ^ 2 + s₁ + 1 := by
      intro hd
      have := Nat.mod_eq_zero_of_dvd hd
      omega
    have hlt2 : ¬ 2 ≤ (s₁ ^ 2 + s₁ + 1).factorization 73 :=
      (h73_prime.pow_dvd_iff_le_factorization (by positivity)).not.mp hnot2
    omega
  have hfac2 : (s₂ ^ 2 + s₂ + 1).factorization 73 = 1 := by
    have h73_dvd : 73 ∣ s₂ ^ 2 + s₂ + 1 := by
      have h1 : 73 ∣ 73 := dvd_rfl
      rw [← hmod2] at h1
      exact Nat.dvd_of_mod_eq_zero (by omega)
    have hge1 : 1 ≤ (s₂ ^ 2 + s₂ + 1).factorization 73 :=
      (h73_prime.dvd_iff_one_le_factorization (by positivity)).mp h73_dvd
    have hnot2 : ¬ 73 ^ 2 ∣ s₂ ^ 2 + s₂ + 1 := by
      intro hd
      have := Nat.mod_eq_zero_of_dvd hd
      omega
    have hlt2 : ¬ 2 ≤ (s₂ ^ 2 + s₂ + 1).factorization 73 :=
      (h73_prime.pow_dvd_iff_le_factorization (by positivity)).not.mp hnot2
    omega
  exact ⟨hw₁_prime, hw₂_prime, h73_prime, by decide, by decide, by decide, by decide, by decide,
    hs₁_eq, hs₂_eq, hs₁_prime, hs₂_prime, hdvd1, hdvd2, hmod1, hmod2, hfac1, hfac2⟩

/-! ## 4. Elementary Non-Cube Exclusions & Exact `(e₁, e₂, e₃, e₄)` Block Invariants -/

theorem quarticSecondFactor_not_isCube {w : ℕ} (hw : 2 ≤ w) (y : ℕ) :
    quarticSecondFactor w ≠ y ^ 3 := by
  obtain ⟨k, rfl⟩ : ∃ k, w = 2 + k := Nat.exists_eq_add_of_le hw
  let L := (2 + k) ^ 2 + (2 + k)
  have hlo : L ^ 3 < quarticSecondFactor (2 + k) := by
    dsimp [L, quarticSecondFactor]
    ring_nf
    omega
  have hhi : quarticSecondFactor (2 + k) < (L + 1) ^ 3 := by
    dsimp [L, quarticSecondFactor]
    ring_nf
    omega
  intro heq
  rw [heq] at hlo hhi
  have hy_gt : L < y := by
    by_contra! hle
    have := Nat.pow_le_pow_left hle 3
    omega
  have hy_lt : y < L + 1 := by
    by_contra! hle
    have := Nat.pow_le_pow_left hle 3
    omega
  omega

theorem sq_add_self_add_one_ne_cube_of_two_mod_three {s : ℕ} (hs : s.Prime)
    (hs3 : s % 3 = 2) (y : ℕ) :
    s ^ 2 + s + 1 ≠ y ^ 3 := by
  intro heq
  have hs2 : 2 ≤ s := hs.two_le
  have hy2 : 2 ≤ y := by
    by_contra! hlt
    have : y ^ 3 ≤ 1 := Nat.pow_le_pow_left (by omega : y ≤ 1) 3
    nlinarith
  have hmul : s * (s + 1) = (y - 1) * (y ^ 2 + y + 1) := by
    zify [(by omega : 1 ≤ y)]
    have heqz : (s : ℤ) ^ 2 + s + 1 = (y : ℤ) ^ 3 := by exact_mod_cast heq
    nlinarith
  rcases hs.dvd_mul.mp (hmul ▸ dvd_mul_right s (s + 1)) with hd1 | hd2
  · have hpos : 0 < y - 1 := by omega
    have hle : s ≤ y - 1 := Nat.le_of_dvd hpos hd1
    have hsq : (s + 1) ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hcube : y ^ 2 ≤ y ^ 3 := by nlinarith
    nlinarith
  · have hmod := prime_dvd_sq_add_self_add_one hs hd2
    omega

theorem quarticFirstFactor_ne_cube_of_prime_ne_nineteen {w : ℕ} (hw : w.Prime)
    (hw19 : w ≠ 19) (y : ℕ) :
    quarticFirstFactor w ≠ y ^ 3 := by
  intro heq
  have hw2 : 2 ≤ w := hw.two_le
  have hy2 : 2 ≤ y := by
    by_contra! hlt
    have : y ^ 3 ≤ 1 := Nat.pow_le_pow_left (by omega : y ≤ 1) 3
    have hA3 : 3 ≤ quarticFirstFactor w := by
      unfold quarticFirstFactor
      have hle : w ≤ w ^ 2 := Nat.le_self_pow (by decide : 2 ≠ 0) w
      zify [hle]
      nlinarith
    omega
  have hmul : w * (w - 1) = (y - 1) * (y ^ 2 + y + 1) := by
    zify [(by omega : 1 ≤ w), (by omega : 1 ≤ y)]
    have heqz : (w : ℤ) ^ 2 - w + 1 = (y : ℤ) ^ 3 := by
      have hle : w ≤ w ^ 2 := Nat.le_self_pow (by decide : 2 ≠ 0) w
      have h' : w ^ 2 - w + 1 = y ^ 3 := heq
      zify [hle] at h'
      exact h'
    nlinarith
  rcases hw.dvd_mul.mp (hmul ▸ dvd_mul_right w (w - 1)) with hd1 | ⟨k, hk⟩
  · have hpos : 0 < y - 1 := by omega
    have hle : w ≤ y - 1 := Nat.le_of_dvd hpos hd1
    have hsq : (w + 1) ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hcube : y ^ 2 ≤ y ^ 3 := by nlinarith
    have hA_lt : quarticFirstFactor w < (w + 1) ^ 2 := by
      unfold quarticFirstFactor
      have hle_w : w ≤ w ^ 2 := Nat.le_self_pow (by decide : 2 ≠ 0) w
      zify [hle_w]
      nlinarith
    omega
  · have hk_pos : 1 ≤ k := by
      by_contra! hk0
      have hk_eq0 : k = 0 := by omega
      rw [hk_eq0, mul_zero] at hk
      nlinarith
    have hw_sub : w - 1 = (y - 1) * k := by
      have hmul' : w * (w - 1) = w * ((y - 1) * k) := by
        rw [hmul, hk]
        ring
      exact Nat.mul_left_cancel hw.pos hmul'
    have hw_eq : w = (y - 1) * k + 1 := by omega
    have hpoly_z : (y : ℤ) ^ 2 - ((k : ℤ) ^ 2 - 1) * y + ((k : ℤ) ^ 2 - k + 1) = 0 := by
      have h1 : (y : ℤ) ^ 2 + y + 1 = (w : ℤ) * k := by exact_mod_cast hk
      have h2 : (w : ℤ) = ((y : ℤ) - 1) * (k : ℤ) + 1 := by
        zify [(by omega : 1 ≤ y)] at hw_eq
        exact hw_eq
      rw [h2] at h1
      linarith
    rcases eq_or_lt_of_le hk_pos with rfl | hk_gt1
    · ring_nf at hpoly_z
      nlinarith
    · rcases eq_or_lt_of_le (by omega : 2 ≤ k) with rfl | hk_gt2
      · ring_nf at hpoly_z
        nlinarith
      · rcases eq_or_lt_of_le (by omega : 3 ≤ k) with rfl | hk_gt3
        · ring_nf at hpoly_z
          have hfac3 : ((y : ℤ) - 1) * ((y : ℤ) - 7) = 0 := by linarith
          rcases mul_eq_zero.mp hfac3 with h1 | h7
          · omega
          · have hy7 : y = 7 := by omega
            subst hy7
            have hw19_eq : w = 19 := by omega
            exact hw19 hw19_eq
        · have hk4 : 4 ≤ k := by omega
          by_cases hy_le : y ≤ k ^ 2 - 2
          · have hid : ((y : ℤ) - 1) * ((y : ℤ) - ((k : ℤ) ^ 2 - 2)) + (3 - (k : ℤ)) =
                (y : ℤ) ^ 2 - ((k : ℤ) ^ 2 - 1) * y + ((k : ℤ) ^ 2 - k + 1) := by ring
            rw [hpoly_z] at hid
            have hy_le_z : (y : ℤ) ≤ (k : ℤ) ^ 2 - 2 := by
              zify [(by nlinarith : 2 ≤ k ^ 2)] at hy_le
              exact hy_le
            have hy1_z : (1 : ℤ) ≤ (y : ℤ) - 1 := by omega
            have hprod_le : ((y : ℤ) - 1) * ((y : ℤ) - ((k : ℤ) ^ 2 - 2)) ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
            linarith
          · have hy_ge : (k : ℤ) ^ 2 - 1 ≤ (y : ℤ) := by
              have : k ^ 2 - 1 ≤ y := by omega
              zify [(by nlinarith : 1 ≤ k ^ 2)] at this
              exact this
            have h1 : (0 : ℤ) ≤ ((y : ℤ) - ((k : ℤ) ^ 2 - 1)) * (y : ℤ) :=
              mul_nonneg (by omega) (by omega)
            have h2 : (1 : ℤ) ≤ (k : ℤ) ^ 2 - (k : ℤ) + 1 := by nlinarith
            linarith

@[expose] def expCount (M j : ℕ) : ℕ :=
  (M.primeFactors.filter (fun r => M.factorization r = j)).card

theorem fourth_power_bounded_non_sq_non_cube_expCount {M : ℕ}
    (hM : 1 < M)
    (hle4 : ∀ r ∈ M.primeFactors, M.factorization r ≤ 4)
    (hnsq : ¬ IsSquare M)
    (hncube : ∀ y : ℕ, M ≠ y ^ 3) :
    M.primeFactors.card = expCount M 1 + expCount M 2 + expCount M 3 + expCount M 4 ∧
    cardFactors M = expCount M 1 + 2 * expCount M 2 + 3 * expCount M 3 + 4 * expCount M 4 ∧
    1 ≤ expCount M 1 + expCount M 3 ∧
    1 ≤ expCount M 1 + expCount M 2 + expCount M 4 ∧
    (2 ≤ cardFactors M → 2 ≤ M.primeFactors.card) ∧
    (cardFactors M ≤ 6 → expCount M 3 + expCount M 4 ≤ 1) := by
  have hM0 : M ≠ 0 := by omega
  let S (j : ℕ) := M.primeFactors.filter (fun r => M.factorization r = j)
  have hdisj : ∀ a b, a ≠ b → Disjoint (S a) (S b) := by
    intro a b hab
    apply Finset.disjoint_left.mpr
    intro r ha hb
    have h1 := (Finset.mem_filter.mp ha).2
    have h2 := (Finset.mem_filter.mp hb).2
    omega
  have hparts : M.primeFactors = S 1 ∪ S 2 ∪ S 3 ∪ S 4 := by
    ext r
    simp only [S, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hr
      have hpos : 0 < M.factorization r := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
      have hle := hle4 r hr
      rcases (show M.factorization r = 1 ∨ M.factorization r = 2 ∨
          M.factorization r = 3 ∨ M.factorization r = 4 by omega) with h | h | h | h
      · exact Or.inl (Or.inl (Or.inl ⟨hr, h⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨hr, h⟩))
      · exact Or.inl (Or.inr ⟨hr, h⟩)
      · exact Or.inr ⟨hr, h⟩
    · rintro (((⟨hr, _⟩ | ⟨hr, _⟩) | ⟨hr, _⟩) | ⟨hr, _⟩) <;> exact hr
  have hdisj12 : Disjoint (S 1) (S 2) := hdisj 1 2 (by decide)
  have hdisj123 : Disjoint (S 1 ∪ S 2) (S 3) :=
    Finset.disjoint_union_left.mpr ⟨hdisj 1 3 (by decide), hdisj 2 3 (by decide)⟩
  have hdisj1234 : Disjoint (S 1 ∪ S 2 ∪ S 3) (S 4) :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨hdisj 1 4 (by decide), hdisj 2 4 (by decide)⟩,
       hdisj 3 4 (by decide)⟩
  have hω : M.primeFactors.card = expCount M 1 + expCount M 2 + expCount M 3 + expCount M 4 := by
    conv_lhs => rw [hparts]
    rw [Finset.card_union_of_disjoint hdisj1234,
      Finset.card_union_of_disjoint hdisj123,
      Finset.card_union_of_disjoint hdisj12]
    rfl
  have hsum_fac : cardFactors M = ∑ r ∈ M.primeFactors, M.factorization r := by
    rw [cardFactors_eq_sum_factorization, Finsupp.sum]
    rfl
  have hsum_j : ∀ j : ℕ, ∑ r ∈ S j, M.factorization r = j * expCount M j := by
    intro j
    calc
      ∑ r ∈ S j, M.factorization r = ∑ _r ∈ S j, j :=
        Finset.sum_congr rfl fun r hr => (Finset.mem_filter.mp hr).2
      _ = j * expCount M j := by
        dsimp [S, expCount]
        simp [Finset.sum_const, Nat.mul_comm]
  have hΩ : cardFactors M =
      expCount M 1 + 2 * expCount M 2 + 3 * expCount M 3 + 4 * expCount M 4 := by
    rw [hsum_fac]
    conv_lhs => rw [hparts]
    rw [Finset.sum_union hdisj1234, Finset.sum_union hdisj123, Finset.sum_union hdisj12,
      hsum_j 1, hsum_j 2, hsum_j 3, hsum_j 4]
    ring
  have hodd_ex : 1 ≤ expCount M 1 + expCount M 3 := by
    obtain ⟨r, _, hr_odd⟩ := odd_factor_of_nonsquare_local hnsq
    have hr_mem : r ∈ M.primeFactors := Finsupp.mem_support_iff.mpr hr_odd.pos.ne'
    have hle := hle4 r hr_mem
    have hpos : 0 < M.factorization r := hr_odd.pos
    have hor : M.factorization r = 1 ∨ M.factorization r = 3 := by
      obtain ⟨k, hk⟩ := hr_odd
      omega
    rcases hor with h1 | h3
    · have hcard1 : 1 ≤ (S 1).card :=
        Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨hr_mem, h1⟩⟩
      change 1 ≤ expCount M 1 at hcard1
      omega
    · have hcard3 : 1 ≤ (S 3).card :=
        Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨hr_mem, h3⟩⟩
      change 1 ≤ expCount M 3 at hcard3
      omega
  have hnon3_ex : 1 ≤ expCount M 1 + expCount M 2 + expCount M 4 := by
    by_contra! h0
    have he1 : (S 1).card = 0 := by change expCount M 1 = 0; omega
    have he2 : (S 2).card = 0 := by change expCount M 2 = 0; omega
    have he4 : (S 4).card = 0 := by change expCount M 4 = 0; omega
    have hS1 : S 1 = ∅ := Finset.card_eq_zero.mp he1
    have hS2 : S 2 = ∅ := Finset.card_eq_zero.mp he2
    have hS4 : S 4 = ∅ := Finset.card_eq_zero.mp he4
    have hall3 : ∀ r ∈ M.primeFactors, M.factorization r = 3 := by
      intro r hr
      have hr' := hr
      rw [hparts, hS1, hS2, hS4] at hr'
      simp only [Finset.empty_union, Finset.union_empty] at hr'
      exact (Finset.mem_filter.mp hr').2
    have hcube : M = (∏ r ∈ M.primeFactors, r) ^ 3 := by
      calc
        M = ∏ r ∈ M.primeFactors, r ^ M.factorization r :=
          Nat.prod_primeFactors_pow_factorization hM0
        _ = ∏ r ∈ M.primeFactors, r ^ 3 := Finset.prod_congr rfl fun r hr => by rw [hall3 r hr]
        _ = (∏ r ∈ M.primeFactors, r) ^ 3 := by rw [Finset.prod_pow]
    exact hncube (∏ r ∈ M.primeFactors, r) hcube
  have htwo_pf : 2 ≤ cardFactors M → 2 ≤ M.primeFactors.card := by
    intro h2
    omega
  have hle6_34 : cardFactors M ≤ 6 → expCount M 3 + expCount M 4 ≤ 1 := by
    intro h6
    omega
  exact ⟨hω, hΩ, hodd_ex, hnon3_ex, htwo_pf, hle6_34⟩

end OddPerfect
