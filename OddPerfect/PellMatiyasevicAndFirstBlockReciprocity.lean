module

public import Mathlib.NumberTheory.PellMatiyasevic
public import OddPerfect.LegendreHomAndSecondBlockReciprocity
public import OddPerfect.ZsqrtTwoFermatDescent
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pell-Matiyasevic Representation & First-Block Quadratic Reciprocity
(`OddPerfect.PellMatiyasevicAndFirstBlockReciprocity`)

Integrates `Mathlib.NumberTheory.PellMatiyasevic` alongside
`OddPerfect.LegendreHomAndSecondBlockReciprocity` and `OddPerfect.ZsqrtTwoFermatDescent`
to establish two structural theorems:

1. `pellMatiyasevic_three_eq_silverUnit_even_pow`: links `Pell.xn a1 n` and `Pell.yn a1 n`
   (for `a = 3`, `d = 3 * 3 - 1 = 8`) with the even powers `(silverUnit ^ (2 * n) : ℤ√2)`
   in `ℤ√2`, alongside monotonicity and the Pell identity `x ^ 2 - 8 * y ^ 2 = 1`.
2. `exceptional_euler_first_and_second_block_reciprocity_profile`: on the exceptional
   Euler-index branch `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`,
   `d := (a + 1) / 2`), proves `¬ d ∣ geometricBlock q d` (so `l ≠ d` and `¬ d ∣ v`
   in `geometricBlock q d = l * v ^ 2`), unconditionally forces
   `legendreSym r (q : ℤ) = 1` and `legendreSym q (r : ℤ) = 1` for every prime factor
   `r ∈ (geometricBlock q d).primeFactors` (including `r = l`) and
   `jacobiSym (v : ℤ) q = 1`, `jacobiSym (q : ℤ) v = 1`, contrasting with `z` where
   `jacobiSym (q : ℤ) z = ZMod.χ₄ z`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- Links the `PellMatiyasevic` sequences `Pell.xn a1`, `Pell.yn a1` for `a = 3` (`a ^ 2 - 1 = 8`)
with the even powers of `silverUnit = 1 + √2` in `ℤ√2`. -/
theorem pellMatiyasevic_three_eq_silverUnit_even_pow :
    let a1 : 1 < 3 := by decide
    StrictMono (Pell.xn a1) ∧
    StrictMono (Pell.yn a1) ∧
    (∀ n : ℕ,
      n < Pell.xn a1 n ∧
      n ≤ Pell.yn a1 n ∧
      Pell.xn a1 n * Pell.xn a1 n - 8 * Pell.yn a1 n * Pell.yn a1 n = 1 ∧
      ((silverUnit ^ (2 * n) : (ℤ√2)ˣ) : ℤ√2).re = (Pell.xn a1 n : ℤ) ∧
      ((silverUnit ^ (2 * n) : (ℤ√2)ˣ) : ℤ√2).im = 2 * (Pell.yn a1 n : ℤ)) := by
  intro a1
  refine ⟨Pell.strictMono_x a1, Pell.strictMono_y a1, fun n => ?_⟩
  refine ⟨Pell.n_lt_xn a1 n, Pell.yn_ge_n a1 n, ?_, ?_⟩
  · simpa using Pell.pell_eq a1 n
  · induction n with
    | zero =>
      simp
    | succ n ih =>
      rcases ih with ⟨ih_re, ih_im⟩
      have hmul : ((silverUnit ^ (2 * (n + 1)) : (ℤ√2)ˣ) : ℤ√2) =
          ((silverUnit ^ (2 * n) : (ℤ√2)ˣ) : ℤ√2) * ⟨3, 2⟩ := by
        have hsq : ((silverUnit ^ 2 : (ℤ√2)ˣ) : ℤ√2) = ⟨3, 2⟩ := by
          ext <;> simp [silverUnit_val, pow_two]
        calc
          ((silverUnit ^ (2 * (n + 1)) : (ℤ√2)ˣ) : ℤ√2)
              = ((silverUnit ^ (2 * n + 2) : (ℤ√2)ˣ) : ℤ√2) := by ring_nf
          _ = (((silverUnit ^ (2 * n) * silverUnit ^ 2 : (ℤ√2)ˣ) : ℤ√2)) := by
            rw [pow_add]
          _ = ((silverUnit ^ (2 * n) : (ℤ√2)ˣ) : ℤ√2) * ((silverUnit ^ 2 : (ℤ√2)ˣ) : ℤ√2) := by
            simp
          _ = ((silverUnit ^ (2 * n) : (ℤ√2)ˣ) : ℤ√2) * ⟨3, 2⟩ := by rw [hsq]
      constructor
      · rw [hmul]
        change ((silverUnit ^ (2 * n) : (ℤ√2)ˣ) : ℤ√2).re * 3 +
            2 * ((silverUnit ^ (2 * n) : (ℤ√2)ˣ) : ℤ√2).im * 2 =
            (Pell.xn a1 (n + 1) : ℤ)
        rw [ih_re, ih_im, Pell.xn_succ]
        push_cast
        ring
      · rw [hmul]
        change ((silverUnit ^ (2 * n) : (ℤ√2)ˣ) : ℤ√2).re * 2 +
            ((silverUnit ^ (2 * n) : (ℤ√2)ˣ) : ℤ√2).im * 3 =
            2 * (Pell.yn a1 (n + 1) : ℤ)
        rw [ih_re, ih_im, Pell.yn_succ]
        push_cast
        ring

private lemma zmod_sum_range_neg_one_odd {R : Type*} [CommRing R] (k : ℕ) :
    (∑ j ∈ Finset.range (2 * k + 1), (-1 : R) ^ j) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1 + 1) + 1 by ring]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h1 : (-1 : R) ^ (2 * k + 1) = -1 := by
      rw [pow_add, pow_mul, pow_one]
      norm_num
    have h2 : (-1 : R) ^ (2 * k + 1 + 1) = 1 := by
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul]
      norm_num
    rw [h1, h2]
    ring

/-- On the exceptional Euler-index branch `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2`
(`a > 1`, `l.Prime`, `d := (a + 1) / 2`), proves `¬ d ∣ geometricBlock q d` (hence
`l ≠ d` and `¬ d ∣ v`) and shows every prime factor `r ∈ (geometricBlock q d).primeFactors`
satisfies `legendreSym r (q : ℤ) = 1` and `legendreSym q (r : ℤ) = 1` unconditionally,
yielding `jacobiSym (v : ℤ) q = 1` and `jacobiSym (q : ℤ) v = 1`. -/
theorem exceptional_euler_first_and_second_block_reciprocity_profile
    {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    ¬ d ∣ geometricBlock q d ∧
    l ≠ d ∧
    ∃ w z v : ℕ,
      0 < w ∧ 3 ≤ z ∧ Odd w ∧ Odd z ∧ Odd v ∧
      Nat.Coprime w z ∧ ¬ d ∣ z ∧ ¬ d ∣ v ∧
      q + 1 = 2 * d * w ^ 2 ∧
      (q ^ d + 1) / (q + 1) = d * z ^ 2 ∧
      geometricBlock q d = l * v ^ 2 ∧
      (haveI : Fact q.Prime := ⟨hq⟩
       haveI : Fact l.Prime := ⟨hl⟩
       legendreSym l (q : ℤ) = 1 ∧
       legendreSym q (l : ℤ) = 1 ∧
       (∀ r ∈ (geometricBlock q d).primeFactors,
         ∀ [Fact r.Prime],
           legendreSym r (q : ℤ) = 1 ∧
           legendreSym q (r : ℤ) = 1) ∧
       jacobiSym (v : ℤ) q = 1 ∧
       jacobiSym (q : ℤ) v = 1 ∧
       jacobiSym (z : ℤ) q = ZMod.χ₄ z ∧
       jacobiSym (q : ℤ) z = ZMod.χ₄ z) := by
  intro d
  obtain ⟨hd_prime, _, hd8, _, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  change d.Prime at hd_prime
  change d % 8 = 1 at hd8
  have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
  have hd_pos : 0 < d := hd_prime.pos
  have hd1 : 1 < d := hd_prime.one_lt
  obtain ⟨y, w, z, hy_pos, hw_pos, hz3, hw_odd, hz_odd, hcop, hdz, hy_dwz,
    hq1, hdiv, hpow, _, _, _, _, hjac_zq, hjac_qz, _, _⟩ :=
    exceptional_euler_second_block_jacobi_and_legendre_profile
      hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨w1, z1, v, _, _, hv_odd, hq1_1, hdiv_1, _, hgeom, _, _, _⟩ :=
    exceptional_euler_second_block_exact_square hN ho hq hq4 ha4 ha hqm hform hl hi
  have hw1_eq : w1 = w := by
    have hmul : 2 * d * w1 ^ 2 = 2 * d * w ^ 2 := hq1_1.symm.trans hq1
    have hsq : w1 ^ 2 = w ^ 2 := Nat.eq_of_mul_eq_mul_left (by omega) hmul
    exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hsq
  have hz1_eq : z1 = z := by
    have hmul : d * z1 ^ 2 = d * z ^ 2 := hdiv_1.symm.trans hdiv
    have hsq : z1 ^ 2 = z ^ 2 := Nat.eq_of_mul_eq_mul_left hd_pos hmul
    exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hsq
  have hndvd_geom : ¬ d ∣ geometricBlock q d := by
    intro hdvd
    have hq_zmod : (q : ZMod d) = -1 := by
      have h0 : ((q + 1 : ℕ) : ZMod d) = 0 := by
        rw [hq1]
        have : d ∣ 2 * d * w ^ 2 := ⟨2 * w ^ 2, by ring⟩
        exact (ZMod.natCast_eq_zero_iff (2 * d * w ^ 2) d).mpr this
      push_cast at h0
      exact eq_neg_of_add_eq_zero_left h0
    obtain ⟨k, hk⟩ := hd_odd
    have hgeom_zmod : ((geometricBlock q d : ℕ) : ZMod d) = 1 := by
      dsimp [geometricBlock]
      push_cast
      simp_rw [hq_zmod, hk]
      exact zmod_sum_range_neg_one_odd k
    have hzero : ((geometricBlock q d : ℕ) : ZMod d) = 0 :=
      (ZMod.natCast_eq_zero_iff (geometricBlock q d) d).mpr hdvd
    have : NeZero (1 : ZMod d) := by
      have : Fact (1 < d) := ⟨hd1⟩
      infer_instance
    have h10 : (1 : ZMod d) = 0 := hgeom_zmod.symm.trans hzero
    exact one_ne_zero h10
  have hl_ne_d : l ≠ d := by
    rintro rfl
    exact hndvd_geom ⟨v ^ 2, hgeom⟩
  have hdv : ¬ d ∣ v := by
    intro hdv
    exact hndvd_geom (by rw [hgeom]; exact dvd_mul_of_dvd_right (dvd_pow hdv (by decide : 2 ≠ 0)) l)
  have hgeom_odd : Odd (geometricBlock q d) := by
    rw [hgeom]
    have hcast : ((geometricBlock q d : ℕ) : ZMod 2) = 1 := by
      have hq2 : (q : ZMod 2) = 1 := by
        rw [← ZMod.natCast_mod, show q % 2 = 1 by omega, Nat.cast_one]
      have hd2 : (d : ZMod 2) = 1 := by
        rw [← ZMod.natCast_mod, Nat.odd_iff.mp hd_odd, Nat.cast_one]
      simp [geometricBlock, hq2, hd2]
    rw [Nat.odd_iff]
    have hm := (ZMod.natCast_eq_natCast_iff (geometricBlock q d) 1 2).mp (by simpa using hcast)
    simpa [Nat.ModEq, ← hgeom] using hm
  have hgeom_ne0 : geometricBlock q d ≠ 0 := hgeom_odd.pos.ne'
  have hv_ne0 : v ≠ 0 := hv_odd.pos.ne'
  have hrec_all :
      haveI : Fact q.Prime := ⟨hq⟩
      ∀ r ∈ (geometricBlock q d).primeFactors,
        ∀ [Fact r.Prime],
          legendreSym r (q : ℤ) = 1 ∧
          legendreSym q (r : ℤ) = 1 := by
    have : Fact q.Prime := ⟨hq⟩
    intro r hr hr_fact
    have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hr_dvd_geom : r ∣ geometricBlock q d := Nat.dvd_of_mem_primeFactors hr
    have hr_odd : Odd r := hgeom_odd.of_dvd_nat hr_dvd_geom
    have hr_ne2 : r ≠ 2 := by
      have hmod := Nat.odd_iff.mp hr_odd
      omega
    have hgeom_mul : ((q : ℤ) - 1) * (geometricBlock q d : ℤ) = (q : ℤ) ^ d - 1 := by
      dsimp [geometricBlock]
      push_cast
      rw [mul_comm, geom_sum_mul]
    have hr_dvd_qd_sub : r ∣ q ^ d - 1 := by
      have h1 : 1 ≤ q ^ d := Nat.one_le_pow d q hq.pos
      have hr_int : (r : ℤ) ∣ (q : ℤ) ^ d - 1 := by
        rw [← hgeom_mul]
        exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hr_dvd_geom) _
      have hr_sub : (r : ℤ) ∣ ((q ^ d - 1 : ℕ) : ℤ) := by
        simpa [Nat.cast_sub h1] using hr_int
      exact Int.natCast_dvd_natCast.mp hr_sub
    have hmod_qd : ((q : ℤ) ^ d) ≡ 1 [ZMOD (r : ℤ)] := by
      refine Int.modEq_iff_dvd.mpr ?_
      have h1 : 1 ≤ q ^ d := Nat.one_le_pow d q hq.pos
      obtain ⟨k, hk⟩ := hr_dvd_qd_sub
      refine ⟨-(k : ℤ), ?_⟩
      have hk_z : ((q ^ d - 1 : ℕ) : ℤ) = (r : ℤ) * (k : ℤ) := by exact_mod_cast hk
      rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one] at hk_z
      linarith
    have hq_ne0 : ((q : ℤ) : ZMod r) ≠ 0 := by
      intro h0
      have hr_dvd_q : r ∣ q := Int.natCast_dvd_natCast.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd q r).mp h0)
      have hr_dvd_qd : r ∣ q ^ d := dvd_pow hr_dvd_q hd_pos.ne'
      have h1 : 1 ≤ q ^ d := Nat.one_le_pow d q hq.pos
      have hr_dvd_1 : r ∣ 1 := (Nat.dvd_sub_iff_right h1 hr_dvd_qd).mp hr_dvd_qd_sub
      exact hr_prime.not_dvd_one hr_dvd_1
    have hpow_leg : (legendreSym r (q : ℤ)) ^ d = 1 := by
      calc
        (legendreSym r (q : ℤ)) ^ d
            = legendreSym r ((q : ℤ) ^ d) := by
              simpa using (map_pow (legendreSym.hom r) (q : ℤ) d).symm
        _ = legendreSym r (((q : ℤ) ^ d) % (r : ℤ)) := legendreSym.mod r ((q : ℤ) ^ d)
        _ = legendreSym r ((1 : ℤ) % (r : ℤ)) := by rw [hmod_qd.eq]
        _ = legendreSym r 1 := (legendreSym.mod r 1).symm
        _ = 1 := legendreSym.at_one r
    have hleg_rq : legendreSym r (q : ℤ) = 1 := by
      rcases legendreSym.eq_one_or_neg_one (p := r) hq_ne0 with h1 | hm1
      · exact h1
      · exfalso
        rw [hm1, hd_odd.neg_one_pow] at hpow_leg
        norm_num at hpow_leg
    have hleg_qr : legendreSym q (r : ℤ) = 1 := by
      have hrec : legendreSym r (q : ℤ) = legendreSym q (r : ℤ) :=
        legendreSym.quadratic_reciprocity_one_mod_four hq4 hr_ne2
      exact hrec.symm.trans hleg_rq
    exact ⟨hleg_rq, hleg_qr⟩
  have hl_mem : l ∈ (geometricBlock q d).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hl, ⟨v ^ 2, hgeom⟩, hgeom_ne0⟩
  have : Fact q.Prime := ⟨hq⟩
  have : Fact l.Prime := ⟨hl⟩
  obtain ⟨hleg_lq, hleg_ql⟩ := hrec_all l hl_mem
  have hjac_qv : jacobiSym (q : ℤ) v = 1 := by
    rw [jacobiSym]
    apply List.prod_eq_one
    intro x hx
    rw [List.mem_pmap] at hx
    rcases hx with ⟨p, hp, rfl⟩
    have pp : p.Prime := Nat.prime_of_mem_primeFactorsList hp
    have hp_dvd_v : p ∣ v := Nat.dvd_of_mem_primeFactorsList hp
    have hp_dvd_geom : p ∣ geometricBlock q d := by
      rw [hgeom]
      exact dvd_mul_of_dvd_right (dvd_pow hp_dvd_v (by decide : 2 ≠ 0)) l
    have hp_mem : p ∈ (geometricBlock q d).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨pp, hp_dvd_geom, hgeom_ne0⟩
    have : Fact p.Prime := ⟨pp⟩
    exact (hrec_all p hp_mem).1
  have hjac_vq : jacobiSym (v : ℤ) q = 1 :=
    (jacobiSym.quadratic_reciprocity_one_mod_four hq4 hv_odd).symm.trans hjac_qv
  refine ⟨hndvd_geom, hl_ne_d, w, z, v, hw_pos, hz3, hw_odd, hz_odd, hv_odd,
    hcop, hdz, hdv, hq1, hdiv, hgeom, hleg_lq, hleg_ql, hrec_all, hjac_vq, hjac_qv,
    hjac_zq, hjac_qz⟩

end OddPerfect
