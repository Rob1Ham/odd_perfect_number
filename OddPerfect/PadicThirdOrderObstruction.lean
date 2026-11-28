module

public import OddPerfect.PadicEvenIndexObstruction
public import OddPerfect.EvenIndexPrimorialObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Third-Order p-adic & Quadratic-Repunit Obstructions (`OddPerfect.PadicThirdOrderObstruction`)

Develops third- and fourth-order `p`-adic cofactor congruences, prime-length repunit structure,
mod-`3` dichotomy for the quadratic-repunit branch (`p % 3 = 1`), and the `k = 3` radical
congruence modulo `p ^ 4` at any even prime-power component index `i = p ^ (2 * u)`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma modEq_cancel_mul_left_pow {p k a b : ℕ} (hp : 0 < p)
    (h : p * a ≡ p * b [MOD p ^ (k + 1)]) : a ≡ b [MOD p ^ k] := by
  rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd] at h ⊢
  have hmul : (p : ℤ) * (p : ℤ) ^ k ∣ (p : ℤ) * ((b : ℤ) - (a : ℤ)) := by
    have h1 : (p : ℤ) * (p : ℤ) ^ k = ((p ^ (k + 1) : ℕ) : ℤ) := by
      push_cast
      ring
    have h2 : (p : ℤ) * ((b : ℤ) - (a : ℤ)) = ((p * b : ℕ) : ℤ) - ((p * a : ℕ) : ℤ) := by
      push_cast
      ring
    rw [h1, h2]
    exact h
  exact (mul_dvd_mul_iff_left (by exact_mod_cast hp.ne_zero)).mp hmul

/-- Divided-cofactor congruences modulo `p ^ 2` and `p ^ 3`, cofactor successor congruence
modulo `p ^ 4`, and coupled geometric-block factorization for `t_s = (s - 1) / p`. -/
theorem even_index_divided_cofactor_mod_p_cube_and_coupled_product {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let t_s := (s - 1) / p
    s = 1 + p * t_s ∧ ¬ p ∣ t_s ∧
    32 * t_s ≡ 8 + 7 * p [MOD p ^ 2] ∧
    128 * t_s ≡ 32 + 28 * p + 25 * p ^ 2 [MOD p ^ 3] ∧
    128 * (s + 1) ≡ 256 + 32 * p + 28 * p ^ 2 + 25 * p ^ 3 [MOD p ^ 4] ∧
    2 * t_s * (s + 1) = (p + 1) * geometricBlock (p ^ 2) u := by
  intro t_s
  obtain ⟨hpdvd, hnp2, _, _⟩ :=
    even_index_exact_p_dvd_cofactor_pred hp hpo hs.pos hu hσq hplus hσs
  have hs1 : 1 ≤ s := hs.pos
  have hsub : s - 1 = p * t_s := (Nat.mul_div_cancel' hpdvd).symm
  have hs_eq : s = 1 + p * t_s := by omega
  have hnot_dvd_ts : ¬ p ∣ t_s := by
    intro hdvd
    apply hnp2
    rw [hsub, pow_two]
    exact Nat.mul_dvd_mul_left p hdvd
  obtain ⟨hmod3, hmod4⟩ :=
    even_index_cofactor_mod_p_cube_and_fourth hp hpo hs hu hσq hplus hσs
  have hts_mod2 : 32 * t_s ≡ 8 + 7 * p [MOD p ^ 2] := by
    apply modEq_cancel_mul_left_pow hp.pos
    have hl : p * (32 * t_s) = 32 * (s - 1) := by rw [hsub]; ring
    have hr : p * (8 + 7 * p) = 8 * p + 7 * p ^ 2 := by ring
    rwa [hl, hr]
  have hts_mod3 : 128 * t_s ≡ 32 + 28 * p + 25 * p ^ 2 [MOD p ^ 3] := by
    apply modEq_cancel_mul_left_pow hp.pos
    have hl : p * (128 * t_s) = 128 * (s - 1) := by rw [hsub]; ring
    have hr : p * (32 + 28 * p + 25 * p ^ 2) = 32 * p + 28 * p ^ 2 + 25 * p ^ 3 := by ring
    rwa [hl, hr]
  have hs_succ_mod4 : 128 * (s + 1) ≡ 256 + 32 * p + 28 * p ^ 2 + 25 * p ^ 3 [MOD p ^ 4] := by
    have hl : 128 * (s + 1) = 256 + 128 * (s - 1) := by omega
    have hr : 256 + 32 * p + 28 * p ^ 2 + 25 * p ^ 3 =
        256 + (32 * p + 28 * p ^ 2 + 25 * p ^ 3) := by ring
    rw [hl, hr]
    exact (Nat.ModEq.refl 256).add hmod4
  have hcoupled : 2 * t_s * (s + 1) = (p + 1) * geometricBlock (p ^ 2) u := by
    have hdiff := (coupled_repunit_diff_eq hp hu hσq hplus).2
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    calc
      p * (2 * t_s * (s + 1)) = 2 * (p * t_s) * (s + 1) := by ring
      _ = 2 * (s - 1) * (s + 1) := by rw [← hsub]
      _ = p * (p + 1) * geometricBlock (p ^ 2) u := hdiff
      _ = p * ((p + 1) * geometricBlock (p ^ 2) u) := by ring
  exact ⟨hs_eq, hnot_dvd_ts, hts_mod2, hts_mod3, hs_succ_mod4, hcoupled⟩

/-- Whenever `σ(p ^ (2 * u)) = q` is prime for `u > 0`, the repunit length `2 * u + 1`
is necessarily prime. -/
theorem even_index_length_prime {q p u : ℕ}
    (hq : q.Prime) (hp : p.Prime) (hu : 0 < u) (hσq : sigma 1 (p ^ (2 * u)) = q) :
    (2 * u + 1).Prime := by
  have hgt1 : ∀ {b n : ℕ}, 2 ≤ b → 2 ≤ n → 1 < geometricBlock b n := by
    intro b n hb hn
    have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range n := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
    have hsum : ∑ j ∈ ({0, 1} : Finset ℕ), b ^ j ≤ geometricBlock b n :=
      Finset.sum_le_sum_of_subset hsub
    have hval : ∑ j ∈ ({0, 1} : Finset ℕ), b ^ j = 1 + b := by
      rw [Finset.sum_pair (by decide)]
      simp
    omega
  by_contra hnot
  set n := 2 * u + 1
  have hn2 : 2 ≤ n := by omega
  set a := n.minFac
  have ha_prime : a.Prime := Nat.minFac_prime (by omega)
  have ha_dvd : a ∣ n := Nat.minFac_dvd n
  have ha_lt : a < n := lt_of_le_of_ne (Nat.minFac_le (by omega)) (fun h => hnot (h ▸ ha_prime))
  set b := n / a
  have hab : a * b = n := Nat.mul_div_cancel' ha_dvd
  have hb2 : 2 ≤ b := by
    by_contra! hb1
    have : a * b ≤ a * 1 := Nat.mul_le_mul_left a (by omega)
    omega
  have hq_fac : q = geometricBlock p a * geometricBlock (p ^ a) b := by
    rw [← hσq, sigma_one_apply_prime_pow hp]
    change geometricBlock p n = _
    rw [← hab, geometricBlock_mul p a b]
  have ha_block : 1 < geometricBlock p a := hgt1 hp.two_le ha_prime.two_le
  have hpa_ge2 : 2 ≤ p ^ a := by
    calc
      2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ a := Nat.pow_le_pow_right hp.pos ha_prime.one_le
  have hb_block : 1 < geometricBlock (p ^ a) b := hgt1 hpa_ge2 hb2
  have hdvd : geometricBlock p a ∣ q := ⟨geometricBlock (p ^ a) b, hq_fac⟩
  rcases hq.eq_one_or_self_of_dvd _ hdvd with h1 | hself
  · omega
  · have hlt : geometricBlock p a < geometricBlock p a * geometricBlock (p ^ a) b :=
      lt_mul_of_one_lt_right (by omega) hb_block
    omega

/-- In the quadratic-repunit branch (`p % 3 = 1`), `2 * u + 1 ≥ 5` is prime,
`q % 3 = (2 * u + 1) % 3`, and `3 ∣ s` splits cleanly between `u ≡ 0 [MOD 3]` (when `¬ 3 ∣ s`)
and `u ≡ 2 [MOD 3]` with `p ^ 3 ∣ σ(3 ^ (2 * v₃(s)))` whenever `3 ∉ S₁` (when `3 ∣ s`). -/
theorem even_index_quadratic_repunit_mod_three_dichotomy {q p s u : ℕ}
    (hq : q.Prime) (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) (hp3 : p % 3 = 1) :
    (2 * u + 1).Prime ∧ 5 ≤ 2 * u + 1 ∧
    q % 3 = (2 * u + 1) % 3 ∧
    (¬ 3 ∣ s → q % 3 = 1 ∧ u % 3 = 0 ∧ 3 ∣ u) ∧
    (3 ∣ s → q % 3 = 2 ∧ u % 3 = 2 ∧ 3 ∣ u + 1 ∧
      (3 ∉ s.primeFactors.filter (fun r => (sigma 1 (r ^ (2 * s.factorization r))).factorization p = 1) →
        p ^ 3 ∣ sigma 1 (3 ^ (2 * s.factorization 3)))) := by
  have hlen_prime : (2 * u + 1).Prime := even_index_length_prime hq hp hu hσq
  have hu_ge := (even_index_exponent_ge_6469693228 hp hpo hs hu hσq hplus hσs).1
  have hlen_ge5 : 5 ≤ 2 * u + 1 := by omega
  have hq_mod3 : q % 3 = (2 * u + 1) % 3 := by
    have hq_zmod : (q : ZMod 3) = ((2 * u + 1 : ℕ) : ZMod 3) := by
      rw [← hσq, sigma_one_apply_prime_pow hp, Nat.cast_sum]
      have hp_zmod : (p : ZMod 3) = 1 := by
        rw [← Nat.mod_add_div p 3, hp3]
        push_cast
        simp [show (3 : ZMod 3) = 0 by decide]
      simp [hp_zmod]
    exact (ZMod.natCast_eq_natCast_iff q (2 * u + 1) 3).mp hq_zmod
  have hnot3 : ¬ 3 ∣ s → q % 3 = 1 ∧ u % 3 = 0 ∧ 3 ∣ u := by
    intro hns
    have hs_mod : s % 3 = 1 ∨ s % 3 = 2 := by
      have : s % 3 ≠ 0 := fun h0 => hns (Nat.dvd_of_mod_eq_zero h0)
      omega
    have hq_eq1 : q % 3 = 1 := by
      have hplus3 := congrArg (· % 3) hplus
      rw [sq, Nat.add_mod, Nat.mul_mod, Nat.mul_mod s s 3] at hplus3
      rcases hs_mod with h | h <;> rw [h] at hplus3 <;> omega
    have hu_mod0 : u % 3 = 0 := by
      have hlen1 : (2 * u + 1) % 3 = 1 := by rw [← hq_mod3, hq_eq1]
      omega
    exact ⟨hq_eq1, hu_mod0, Nat.dvd_of_mod_eq_zero hu_mod0⟩
  have h3dvd : 3 ∣ s → q % 3 = 2 ∧ u % 3 = 2 ∧ 3 ∣ u + 1 ∧
      (3 ∉ s.primeFactors.filter (fun r => (sigma 1 (r ^ (2 * s.factorization r))).factorization p = 1) →
        p ^ 3 ∣ sigma 1 (3 ^ (2 * s.factorization 3))) := by
    intro hs3
    have hs_mod0 : s % 3 = 0 := Nat.mod_eq_zero_of_dvd hs3
    have hq_eq2 : q % 3 = 2 := by
      have hplus3 := congrArg (· % 3) hplus
      rw [sq, Nat.add_mod, Nat.mul_mod, Nat.mul_mod s s 3, hs_mod0] at hplus3
      omega
    have hu_mod2 : u % 3 = 2 := by
      have hlen2 : (2 * u + 1) % 3 = 2 := by rw [← hq_mod3, hq_eq2]
      omega
    have h3_u1 : 3 ∣ u + 1 := Nat.dvd_of_mod_eq_zero (by omega)
    refine ⟨hq_eq2, hu_mod2, h3_u1, fun hnot_mem => ?_⟩
    have h3_pf : 3 ∈ s.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨by decide, hs3, hs.pos.ne'⟩
    obtain ⟨_, hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
    obtain ⟨hodd_v3, hsig3⟩ := hparts 3 h3_pf
    dsimp only at hodd_v3 hsig3
    set v3 := (sigma 1 (3 ^ (2 * s.factorization 3))).factorization p
    have hv3_ne1 : v3 ≠ 1 := fun h1 =>
      hnot_mem (Finset.mem_filter.mpr ⟨h3_pf, h1⟩)
    have hv3_ge3 : 3 ≤ v3 := by
      have hmod2 : v3 % 2 = 1 := Nat.odd_iff.mp hodd_v3
      omega
    rw [hsig3]
    exact pow_dvd_pow p hv3_ge3
  exact ⟨hlen_prime, hlen_ge5, hq_mod3, hnot3, h3dvd⟩

/-- Instantiation of `even_index_radical_higher_congruence` at `k = 3`, giving a congruence
modulo `p ^ 4` for the truncated radical lift. -/
theorem even_index_radical_mod_p_fourth_congruence {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    8 * s.primeFactors.prod id + ReturnLift.truncatedSum s.primeFactors (sourceMultiplicity s p) 3 1 p ≡
      ReturnLift.truncatedSum s.primeFactors (sourceMultiplicity s p) 3 0 p [MOD p ^ 4] := by
  have h2u_ge := (even_index_exponent_ge_6469693228 hp hpo hs hu hσq hplus hσs).2.1
  have h3_le : 3 ≤ 2 * u := by omega
  simpa only [show (2 : ℕ) ^ 3 = 8 by decide, show (3 : ℕ) + 1 = 4 by decide] using
    even_index_radical_higher_congruence hp hpo hs h3_le hσq hplus hσs

end OddPerfect
