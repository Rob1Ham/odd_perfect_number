module

public import OddPerfect.GlobalWave11Obstruction
public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.NumberTheory.Padics.MahlerBasis
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.PadicNorm
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# p-adic Even-Index Obstruction (`OddPerfect.PadicEvenIndexObstruction`)

This module develops `p`-adic, Hensel-lifting, congruence, and Mahler-basis obstructions
for the even-index prime-power component equation `2 * (p - 1) * s ^ 2 = (p - 2) + p ^ (2 * u + 1)`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- Algebraic identity relating the index prime `p`, cofactor `s`, and exponent `2 * u + 1`
when `σ(p ^ (2 * u)) = q` and `q + 1 = 2 * s ^ 2`. -/
theorem even_index_twice_pred_mul_cofactor_sq {q p s u : ℕ}
    (hp : p.Prime) (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2) :
    2 * (p - 1) * s ^ 2 = (p - 2) + p ^ (2 * u + 1) := by
  have hgeom : q * (p - 1) = p ^ (2 * u + 1) - 1 := by
    rw [← hσq, sigma_one_apply_prime_pow hp]
    exact geom_sum_mul_of_one_le hp.one_le (2 * u + 1)
  have h1 : 1 ≤ p ^ (2 * u + 1) := Nat.one_le_pow _ _ hp.pos
  have h2 : 2 ≤ p := hp.two_le
  calc
    2 * (p - 1) * s ^ 2 = (p - 1) * (2 * s ^ 2) := by ring
    _ = (p - 1) * (q + 1) := by rw [hplus]
    _ = q * (p - 1) + (p - 1) := by ring
    _ = (p ^ (2 * u + 1) - 1) + (p - 1) := by rw [hgeom]
    _ = (p - 2) + p ^ (2 * u + 1) := by omega

private lemma intCast_prime_not_dvd_two_mul_pred {p : ℕ} (hp : p.Prime) (hpo : Odd p) :
    ¬ (p : ℤ) ∣ 2 * ((p : ℤ) - 1) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  intro hdvd
  rcases hpZ.dvd_or_dvd hdvd with h2 | hp1
  · have h2nat : p ∣ 2 := Int.natCast_dvd_natCast.mp h2
    have h2eq : p = 2 := (Nat.dvd_prime Nat.prime_two).mp h2nat |>.resolve_left hp.ne_one
    subst h2eq
    exact absurd hpo (by decide)
  · have h1 : (p : ℤ) ∣ 1 := by
      have : (p : ℤ) ∣ (p : ℤ) - ((p : ℤ) - 1) := dvd_sub dvd_rfl hp1
      simpa using this
    have h1nat : p ∣ 1 := Int.natCast_dvd_natCast.mp h1
    exact hp.not_dvd_one h1nat

private lemma intCast_prime_not_dvd_four_mul_pred {p : ℕ} (hp : p.Prime) (hpo : Odd p) :
    ¬ (p : ℤ) ∣ 4 * ((p : ℤ) - 1) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  intro hdvd
  rcases hpZ.dvd_or_dvd hdvd with h4 | hp1
  · have h4nat : p ∣ 4 := Int.natCast_dvd_natCast.mp h4
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h4nat)
    have h2' : p = 2 := (Nat.dvd_prime Nat.prime_two).mp h2 |>.resolve_left hp.ne_one
    subst h2'
    exact absurd hpo (by decide)
  · have h1 : (p : ℤ) ∣ 1 := by
      have : (p : ℤ) ∣ (p : ℤ) - ((p : ℤ) - 1) := dvd_sub dvd_rfl hp1
      simpa using this
    exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp h1)

/-- Existence and uniqueness of the Hensel root `σ_p ∈ ℤ_[p]` near `1` solving
`2 * (p - 1) * σ_p ^ 2 = p - 2` for any odd prime `p`. -/
theorem exists_unique_evenIndex_hensel_root {p : ℕ} [Fact p.Prime] (hpo : Odd p) :
    ∃ σ_p : ℤ_[p],
      2 * ((p : ℤ_[p]) - 1) * σ_p ^ 2 = (p : ℤ_[p]) - 2 ∧
      ‖σ_p - 1‖ < 1 ∧
      ∀ z : ℤ_[p], 2 * ((p : ℤ_[p]) - 1) * z ^ 2 = (p : ℤ_[p]) - 2 → ‖z - 1‖ < 1 → z = σ_p := by
  have hp : p.Prime := Fact.out
  let a2 : ℤ_[p] := 2 * ((p : ℤ_[p]) - 1)
  let a0 : ℤ_[p] := (p : ℤ_[p]) - 2
  let F : Polynomial ℤ_[p] := Polynomial.C a2 * Polynomial.X ^ 2 - Polynomial.C a0
  have hF_eval : ∀ z : ℤ_[p], F.aeval z = 2 * ((p : ℤ_[p]) - 1) * z ^ 2 - ((p : ℤ_[p]) - 2) := by
    intro z
    simp [F, a2, a0]
  have hF1 : F.aeval (1 : ℤ_[p]) = (p : ℤ_[p]) := by
    rw [hF_eval 1]
    ring
  have hd1 : F.derivative.aeval (1 : ℤ_[p]) = 4 * ((p : ℤ_[p]) - 1) := by
    simp [F, a2, a0]
    ring
  have hnorm_d1 : ‖F.derivative.aeval (1 : ℤ_[p])‖ = 1 := by
    rw [hd1]
    have hcast : (4 * ((p : ℤ_[p]) - 1) : ℤ_[p]) = ((4 * ((p : ℤ) - 1) : ℤ) : ℤ_[p]) := by
      push_cast
      ring
    rw [hcast]
    refine le_antisymm (PadicInt.norm_le_one _) ?_
    by_contra hlt
    rw [not_le] at hlt
    rw [PadicInt.norm_intCast_lt_one_iff] at hlt
    exact intCast_prime_not_dvd_four_mul_pred hp hpo hlt
  have hnorm_F1 : ‖F.aeval (1 : ℤ_[p])‖ < ‖F.derivative.aeval (1 : ℤ_[p])‖ ^ 2 := by
    rw [hF1, hnorm_d1, one_pow, PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  obtain ⟨σ_p, hσ_root, hσ_dist, _, hσ_uniq⟩ := hensels_lemma hnorm_F1
  refine ⟨σ_p, ?_, ?_, ?_⟩
  · rw [hF_eval σ_p, sub_eq_zero] at hσ_root
    exact hσ_root
  · rwa [hnorm_d1] at hσ_dist
  · intro z hz hz_dist
    apply hσ_uniq z
    · rw [hF_eval z, sub_eq_zero]
      exact hz
    · rwa [hnorm_d1]

/-- Exact `p`-adic distance and valuation between the cofactor `s` and the Hensel root `σ_p`,
together with exact `toZModPow` agreement through modulus `p ^ (2 * u + 1)` and separation
at modulus `p ^ (2 * u + 2)`. -/
theorem even_index_cofactor_padic_distance_to_hensel_root {q p s u : ℕ} [Fact p.Prime]
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    ∃ σ_p : ℤ_[p],
      2 * ((p : ℤ_[p]) - 1) * σ_p ^ 2 = (p : ℤ_[p]) - 2 ∧
      ‖σ_p - 1‖ < 1 ∧
      (s : ℤ_[p]) ≠ σ_p ∧
      ‖(s : ℤ_[p]) - σ_p‖ = (p : ℝ) ^ (-(2 * u + 1 : ℤ)) ∧
      ((s : ℤ_[p]) - σ_p).valuation = 2 * u + 1 ∧
      (∀ m ≤ 2 * u + 1, PadicInt.toZModPow m (s : ℤ_[p]) = PadicInt.toZModPow m σ_p) ∧
      PadicInt.toZModPow (2 * u + 2) (s : ℤ_[p]) ≠ PadicInt.toZModPow (2 * u + 2) σ_p := by
  obtain ⟨σ_p, hσ_eq, hσ_dist, _⟩ := exists_unique_evenIndex_hensel_root (p := p) hpo
  have hs_nat := even_index_twice_pred_mul_cofactor_sq hp hσq hplus
  have hs_padic : 2 * ((p : ℤ_[p]) - 1) * (s : ℤ_[p]) ^ 2 = ((p : ℤ_[p]) - 2) + (p : ℤ_[p]) ^ (2 * u + 1) := by
    have h2 : 2 ≤ p := hp.two_le
    have hcast := congrArg (Nat.cast (R := ℤ_[p])) hs_nat
    push_cast at hcast
    rw [Nat.cast_sub (by omega), Nat.cast_sub h2] at hcast
    push_cast at hcast
    exact hcast
  have hprod : 2 * ((p : ℤ_[p]) - 1) * ((s : ℤ_[p]) - σ_p) * ((s : ℤ_[p]) + σ_p) =
      (p : ℤ_[p]) ^ (2 * u + 1) := by
    calc
      2 * ((p : ℤ_[p]) - 1) * ((s : ℤ_[p]) - σ_p) * ((s : ℤ_[p]) + σ_p)
          = 2 * ((p : ℤ_[p]) - 1) * (s : ℤ_[p]) ^ 2 - 2 * ((p : ℤ_[p]) - 1) * σ_p ^ 2 := by ring
      _ = ((p : ℤ_[p]) - 2) + (p : ℤ_[p]) ^ (2 * u + 1) - ((p : ℤ_[p]) - 2) := by rw [hs_padic, hσ_eq]
      _ = (p : ℤ_[p]) ^ (2 * u + 1) := by ring
  have hsub_ne : (s : ℤ_[p]) - σ_p ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_mul] at hprod
    exact pow_ne_zero (2 * u + 1) (NeZero.ne (p : ℤ_[p])) hprod.symm
  have hs_ne : (s : ℤ_[p]) ≠ σ_p := sub_ne_zero.mp hsub_ne
  have hnorm_coeff : ‖2 * ((p : ℤ_[p]) - 1)‖ = 1 := by
    have hcast : (2 * ((p : ℤ_[p]) - 1) : ℤ_[p]) = ((2 * ((p : ℤ) - 1) : ℤ) : ℤ_[p]) := by
      push_cast
      ring
    rw [hcast]
    refine le_antisymm (PadicInt.norm_le_one _) ?_
    by_contra hlt
    rw [not_le, PadicInt.norm_intCast_lt_one_iff] at hlt
    exact intCast_prime_not_dvd_two_mul_pred hp hpo hlt
  have hpdvd : p ∣ s - 1 :=
    (even_index_exact_p_dvd_cofactor_pred hp hpo hs.pos hu hσq hplus hσs).1
  have hs_dist : ‖(s : ℤ_[p]) - 1‖ < 1 := by
    have hs1 : 1 ≤ s := hs.pos
    have hcast : ((s - 1 : ℕ) : ℤ_[p]) = (s : ℤ_[p]) - 1 := by
      rw [Nat.cast_sub hs1, Nat.cast_one]
    rw [← hcast, PadicInt.norm_natCast_lt_one_iff]
    exact hpdvd
  have hsum_small : ‖((s : ℤ_[p]) - 1) + (σ_p - 1)‖ < 1 :=
    PadicInt.norm_lt_one_add hs_dist hσ_dist
  have hnorm_two : ‖(2 : ℤ_[p])‖ = 1 := by
    rw [show (2 : ℤ_[p]) = ((2 : ℕ) : ℤ_[p]) by norm_num, PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.mpr (fun hd => by
      have : p = 2 := (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hp.ne_one
      subst this
      exact absurd hpo (by decide))
  have hnorm_sum : ‖(s : ℤ_[p]) + σ_p‖ = 1 := by
    have hsplit : (s : ℤ_[p]) + σ_p = (2 : ℤ_[p]) + (((s : ℤ_[p]) - 1) + (σ_p - 1)) := by ring
    rw [hsplit, PadicInt.norm_add_eq_max_of_ne (by rw [hnorm_two]; exact ne_of_gt hsum_small),
      hnorm_two, max_eq_left hsum_small.le]
  have hnorm_sub : ‖(s : ℤ_[p]) - σ_p‖ = (p : ℝ) ^ (-(2 * u + 1 : ℤ)) := by
    have hnorm_eq := congrArg norm hprod
    simp only [norm_mul, hnorm_coeff, one_mul, hnorm_sum, mul_one] at hnorm_eq
    rw [hnorm_eq, PadicInt.norm_p_pow]
    push_cast
    rfl
  have hval : ((s : ℤ_[p]) - σ_p).valuation = 2 * u + 1 := by
    have h1 := PadicInt.norm_eq_zpow_neg_valuation hsub_ne
    rw [hnorm_sub] at h1
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    have hp_ne_one : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
    have hz := (zpow_right_inj₀ hp_pos hp_ne_one).mp h1
    omega
  have hmem_iff : ∀ m : ℕ,
      PadicInt.toZModPow m (s : ℤ_[p]) = PadicInt.toZModPow m σ_p ↔ m ≤ 2 * u + 1 := by
    intro m
    rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
      PadicInt.mem_span_pow_iff_le_valuation _ hsub_ne, hval]
  refine ⟨σ_p, hσ_eq, hσ_dist, hs_ne, hnorm_sub, hval, ?_, ?_⟩
  · intro m hm
    exact (hmem_iff m).mpr hm
  · intro heq
    have hle := (hmem_iff (2 * u + 2)).mp heq
    omega

/-- Unconditional `p ^ 3` and `p ^ 4` congruences for the cofactor `s - 1`. -/
theorem even_index_cofactor_mod_p_cube_and_fourth {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    32 * (s - 1) ≡ 8 * p + 7 * p ^ 2 [MOD p ^ 3] ∧
    128 * (s - 1) ≡ 32 * p + 28 * p ^ 2 + 25 * p ^ 3 [MOD p ^ 4] := by
  have hexp := (even_index_exponent_ge_6469693228 hp hpo hs hu hσq hplus hσs).2.1
  have h4_le : 4 ≤ 2 * u + 1 := by omega
  have hs_nat := even_index_twice_pred_mul_cofactor_sq hp hσq hplus
  have hs_int : 2 * ((p : ℤ) - 1) * (s : ℤ) ^ 2 = ((p : ℤ) - 2) + (p : ℤ) ^ (2 * u + 1) := by
    have h2 : 2 ≤ p := hp.two_le
    zify [h2, (by omega : 1 ≤ p)] at hs_nat
    exact hs_nat
  let A : ℤ := 128 * (s : ℤ)
  let B : ℤ := 128 + 32 * (p : ℤ) + 28 * (p : ℤ) ^ 2 + 25 * (p : ℤ) ^ 3
  have hp4_dvd_A : (p : ℤ) ^ 4 ∣ 2 * ((p : ℤ) - 1) * A ^ 2 - 16384 * ((p : ℤ) - 2) := by
    have hid : 2 * ((p : ℤ) - 1) * A ^ 2 - 16384 * ((p : ℤ) - 2) = 16384 * (p : ℤ) ^ (2 * u + 1) := by
      dsimp [A]
      calc
        2 * ((p : ℤ) - 1) * (128 * (s : ℤ)) ^ 2 - 16384 * ((p : ℤ) - 2)
            = 16384 * (2 * ((p : ℤ) - 1) * (s : ℤ) ^ 2 - ((p : ℤ) - 2)) := by ring
        _ = 16384 * (p : ℤ) ^ (2 * u + 1) := by rw [hs_int]; ring
    rw [hid]
    exact dvd_mul_of_dvd_right (pow_dvd_pow (p : ℤ) h4_le) 16384
  have hp4_dvd_B : (p : ℤ) ^ 4 ∣ 2 * ((p : ℤ) - 1) * B ^ 2 - 16384 * ((p : ℤ) - 2) := by
    have hid : 2 * ((p : ℤ) - 1) * B ^ 2 - 16384 * ((p : ℤ) - 2) =
        (p : ℤ) ^ 4 * (1250 * (p : ℤ) ^ 3 + 1550 * (p : ℤ) ^ 2 + 1968 * (p : ℤ) + 11616) := by
      dsimp [B]
      ring
    rw [hid]
    exact dvd_mul_right _ _
  have hp4_dvd_prod : (p : ℤ) ^ 4 ∣ 2 * ((p : ℤ) - 1) * (A + B) * (A - B) := by
    have hdiff := dvd_sub hp4_dvd_A hp4_dvd_B
    have hfac : (2 * ((p : ℤ) - 1) * A ^ 2 - 16384 * ((p : ℤ) - 2)) -
        (2 * ((p : ℤ) - 1) * B ^ 2 - 16384 * ((p : ℤ) - 2)) =
        2 * ((p : ℤ) - 1) * (A + B) * (A - B) := by ring
    rwa [hfac] at hdiff
  have hpdvd : p ∣ s - 1 :=
    (even_index_exact_p_dvd_cofactor_pred hp hpo hs.pos hu hσq hplus hσs).1
  have hp_dvd_s1 : (p : ℤ) ∣ (s : ℤ) - 1 := by
    have h1 : 1 ≤ s := hs.pos
    have : ((s - 1 : ℕ) : ℤ) = (s : ℤ) - 1 := by rw [Nat.cast_sub h1, Nat.cast_one]
    rw [← this]
    exact Int.natCast_dvd_natCast.mpr hpdvd
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hnot_dvd_AB : ¬ (p : ℤ) ∣ A + B := by
    intro hdiv
    have hsum_id : A + B = 256 + 128 * ((s : ℤ) - 1) +
        (p : ℤ) * (32 + 28 * (p : ℤ) + 25 * (p : ℤ) ^ 2) := by
      dsimp [A, B]
      ring
    rw [hsum_id] at hdiv
    have hd256 : (p : ℤ) ∣ 256 := by
      have hd_tail : (p : ℤ) ∣ 128 * ((s : ℤ) - 1) +
          (p : ℤ) * (32 + 28 * (p : ℤ) + 25 * (p : ℤ) ^ 2) :=
        dvd_add (dvd_mul_of_dvd_right hp_dvd_s1 128) (dvd_mul_right _ _)
      have := dvd_sub hdiv hd_tail
      simpa using this
    have hd256nat : p ∣ 2 ^ 8 := by
      have := Int.natCast_dvd_natCast.mp hd256
      simpa using this
    have hd2 : p ∣ 2 := hp.dvd_of_dvd_pow hd256nat
    have h2 : p = 2 := (Nat.dvd_prime Nat.prime_two).mp hd2 |>.resolve_left hp.ne_one
    subst h2
    exact absurd hpo (by decide)
  have hnot_dvd_coeff : ¬ (p : ℤ) ∣ 2 * ((p : ℤ) - 1) * (A + B) := by
    intro hdiv
    rcases hpZ.dvd_or_dvd hdiv with h2p1 | hAB
    · exact intCast_prime_not_dvd_two_mul_pred hp hpo h2p1
    · exact hnot_dvd_AB hAB
  have hcop : IsCoprime ((p : ℤ) ^ 4) (2 * ((p : ℤ) - 1) * (A + B)) :=
    (hpZ.coprime_iff_not_dvd.mpr hnot_dvd_coeff).pow_left
  have hp4_dvd_sub : (p : ℤ) ^ 4 ∣ A - B := hcop.dvd_of_dvd_mul_left hp4_dvd_prod
  have hsub_id : A - B =
      ((128 * (s - 1) : ℕ) : ℤ) - ((32 * p + 28 * p ^ 2 + 25 * p ^ 3 : ℕ) : ℤ) := by
    have h1 : 1 ≤ s := hs.pos
    dsimp [A, B]
    push_cast [Nat.cast_sub h1]
    ring
  have hmod4 : 128 * (s - 1) ≡ 32 * p + 28 * p ^ 2 + 25 * p ^ 3 [MOD p ^ 4] := by
    rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd]
    have hp4_dvd_rev : (p : ℤ) ^ 4 ∣
        ((32 * p + 28 * p ^ 2 + 25 * p ^ 3 : ℕ) : ℤ) - ((128 * (s - 1) : ℕ) : ℤ) := by
      rw [← neg_sub, ← hsub_id]
      exact dvd_neg.mpr hp4_dvd_sub
    simpa [Nat.cast_pow] using hp4_dvd_rev
  have hp3_dvd_sub : (p : ℤ) ^ 3 ∣ A - B :=
    (pow_dvd_pow (p : ℤ) (by decide : 3 ≤ 4)).trans hp4_dvd_sub
  have hp3_dvd_mul4 : (p : ℤ) ^ 3 ∣
      4 * (((8 * p + 7 * p ^ 2 : ℕ) : ℤ) - ((32 * (s - 1) : ℕ) : ℤ)) := by
    have h1 : 1 ≤ s := hs.pos
    have hid : 4 * (((8 * p + 7 * p ^ 2 : ℕ) : ℤ) - ((32 * (s - 1) : ℕ) : ℤ)) =
        -(A - B) - 25 * (p : ℤ) ^ 3 := by
      dsimp [A, B]
      push_cast [Nat.cast_sub h1]
      ring
    rw [hid]
    exact dvd_sub (dvd_neg.mpr hp3_dvd_sub) (dvd_mul_left _ _)
  have hnot_dvd_4 : ¬ (p : ℤ) ∣ 4 := by
    intro h4
    have h4nat : p ∣ 2 ^ 2 := by simpa using Int.natCast_dvd_natCast.mp h4
    have hd2 : p ∣ 2 := hp.dvd_of_dvd_pow h4nat
    have h2 : p = 2 := (Nat.dvd_prime Nat.prime_two).mp hd2 |>.resolve_left hp.ne_one
    subst h2
    exact absurd hpo (by decide)
  have hcop4 : IsCoprime ((p : ℤ) ^ 3) 4 := (hpZ.coprime_iff_not_dvd.mpr hnot_dvd_4).pow_left
  have hmod3 : 32 * (s - 1) ≡ 8 * p + 7 * p ^ 2 [MOD p ^ 3] := by
    rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd]
    simpa [Nat.cast_pow] using hcop4.dvd_of_dvd_mul_left hp3_dvd_mul4
  exact ⟨hmod3, hmod4⟩

private lemma prime_dvd_factorial_le {p n : ℕ} (hp : p.Prime) (hdvd : p ∣ Nat.factorial n) :
    p ≤ n := by
  induction n with
  | zero => exact absurd hdvd hp.not_dvd_one
  | succ k ih =>
    rw [Nat.factorial_succ] at hdvd
    rcases hp.dvd_mul.mp hdvd with h | h
    · exact Nat.le_of_dvd (Nat.succ_pos k) h
    · exact (ih h).trans (Nat.le_succ k)

/-- For any prime `p` and `2 * j < p`, the `j`-th Mahler basis function evaluated at `2 * j`
equals the central binomial coefficient `(2 * j).choose j`, has `p`-adic norm `1`, and is a unit
in `ℤ_[p]`. -/
theorem mahler_central_binomial_norm_one {p : ℕ} [Fact p.Prime] (j : ℕ) (hj : 2 * j < p) :
    mahler j (2 * j : ℤ_[p]) = ((2 * j).choose j : ℤ_[p]) ∧
    ‖mahler j (2 * j : ℤ_[p])‖ = 1 ∧
    IsUnit (mahler j (2 * j : ℤ_[p])) := by
  have hp : p.Prime := Fact.out
  have hval : mahler j (2 * j : ℤ_[p]) = ((2 * j).choose j : ℤ_[p]) := by
    simpa [Nat.cast_mul, Nat.cast_ofNat] using mahler_natCast_eq (p := p) j (2 * j)
  have hnot_dvd : ¬ p ∣ (2 * j).choose j := by
    intro hdvd
    have hfact_eq : (2 * j).choose j * Nat.factorial j * Nat.factorial (2 * j - j) =
        Nat.factorial (2 * j) :=
      Nat.choose_mul_factorial_mul_factorial (by omega)
    have hp_dvd_fact : p ∣ Nat.factorial (2 * j) := by
      rw [← hfact_eq]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hdvd _) _
    have hp_le : p ≤ 2 * j := prime_dvd_factorial_le hp hp_dvd_fact
    omega
  have hnorm : ‖mahler j (2 * j : ℤ_[p])‖ = 1 := by
    rw [hval, PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.mpr hnot_dvd
  exact ⟨hval, hnorm, PadicInt.isUnit_iff.mpr hnorm⟩

end OddPerfect
