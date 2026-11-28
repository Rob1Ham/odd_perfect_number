module

public import OddPerfect.ZsqrtTwoUnifiedSieveAndSecondBlockModSq
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Legendre Homomorphism & Second-Block Quadratic Reciprocity
(`OddPerfect.LegendreHomAndSecondBlockReciprocity`)

Proves exact Legendre and Jacobi reciprocity constraints on prime divisors `r ∣ z`
and on `z` itself for the second-block square decomposition
`q + 1 = 2 * d * w ^ 2`, `(q ^ d + 1) / (q + 1) = d * z ^ 2` with `q ≡ 1 [MOD 4]`:

1. `second_block_z_prime_legendre_reciprocity`: for every prime `r ∣ z`,
   `(q : ℤ) ^ d ≡ -1 [ZMOD r]` forces `legendreSym r (q : ℤ) = ZMod.χ₄ r`,
   and quadratic reciprocity (`q % 4 = 1`) yields
   `legendreSym q (r : ℤ) = ZMod.χ₄ r`, hence
   `legendreSym q (r : ℤ) = 1 ↔ r % 4 = 1` and `legendreSym q (r : ℤ) = -1 ↔ r % 4 = 3`.
2. `exceptional_euler_second_block_jacobi_and_legendre_profile`: lifts these
   prime-factor Legendre evaluations to `jacobiSym (z : ℤ) q = ZMod.χ₄ z` and
   `jacobiSym (q : ℤ) z = ZMod.χ₄ z` on `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- Every prime factor `r` of `z` in `q + 1 = 2 * d * w ^ 2`, `(q ^ d + 1) / (q + 1) = d * z ^ 2`
(with `q % 4 = 1` and `Odd d`, `Odd z`) satisfies `legendreSym r (q : ℤ) = ZMod.χ₄ r` and
`legendreSym q (r : ℤ) = ZMod.χ₄ r`, hence `legendreSym q (r : ℤ) = 1 ↔ r % 4 = 1` and
`legendreSym q (r : ℤ) = -1 ↔ r % 4 = 3`. -/
theorem second_block_z_prime_legendre_reciprocity {q d w z : ℕ}
    (hq : q.Prime) (hq4 : q % 4 = 1) (hd : d.Prime) (hd5 : 5 ≤ d) (hd_odd : Odd d)
    (hw : 0 < w) (hz_odd : Odd z)
    (hq1 : q + 1 = 2 * d * w ^ 2) (hdiv : (q ^ d + 1) / (q + 1) = d * z ^ 2)
    (hcop : Nat.Coprime w z) (hdz : ¬ d ∣ z) :
    haveI : Fact q.Prime := ⟨hq⟩
    ∀ r ∈ z.primeFactors,
      ∀ [Fact r.Prime],
        legendreSym r (q : ℤ) = ZMod.χ₄ r ∧
        legendreSym q (r : ℤ) = ZMod.χ₄ r ∧
        (legendreSym q (r : ℤ) = 1 ↔ r % 4 = 1) ∧
        (legendreSym q (r : ℤ) = -1 ↔ r % 4 = 3) := by
  have _ := hd5
  have _ := hw
  have _ := hq1
  have _ := hcop
  have _ := hdz
  have : Fact q.Prime := ⟨hq⟩
  intro r hr hr_fact
  have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr
  have hr_dvd_z : r ∣ z := Nat.dvd_of_mem_primeFactors hr
  have hr_odd : Odd r := hz_odd.of_dvd_nat hr_dvd_z
  have hr_ne2 : r ≠ 2 := by
    have hmod := Nat.odd_iff.mp hr_odd
    omega
  have hdvd_q1 : q + 1 ∣ q ^ d + 1 := by
    simpa using hd_odd.nat_add_dvd_pow_add_pow q 1
  have hmul_nat : (q + 1) * (d * z ^ 2) = q ^ d + 1 := by
    rw [← hdiv]
    exact Nat.mul_div_cancel' hdvd_q1
  have hr_dvd_qd1 : r ∣ q ^ d + 1 := by
    rw [← hmul_nat]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_pow hr_dvd_z (by decide : 2 ≠ 0)) d) _
  have hmod_qd : ((q : ℤ) ^ d) ≡ -1 [ZMOD (r : ℤ)] := by
    refine Int.modEq_iff_dvd.mpr ?_
    obtain ⟨k, hk⟩ := hr_dvd_qd1
    refine ⟨-(k : ℤ), ?_⟩
    have hk_z : ((q ^ d + 1 : ℕ) : ℤ) = (r : ℤ) * (k : ℤ) := by exact_mod_cast hk
    push_cast at hk_z
    linarith
  have hpow_leg : (legendreSym r (q : ℤ)) ^ d = ZMod.χ₄ r := by
    calc
      (legendreSym r (q : ℤ)) ^ d
          = legendreSym r ((q : ℤ) ^ d) := by
            simpa using (map_pow (legendreSym.hom r) (q : ℤ) d).symm
      _ = legendreSym r (((q : ℤ) ^ d) % (r : ℤ)) := legendreSym.mod r ((q : ℤ) ^ d)
      _ = legendreSym r ((-1 : ℤ) % (r : ℤ)) := by rw [hmod_qd.eq]
      _ = legendreSym r (-1) := (legendreSym.mod r (-1)).symm
      _ = ZMod.χ₄ r := legendreSym.at_neg_one hr_ne2
  have hq_ne0 : ((q : ℤ) : ZMod r) ≠ 0 := by
    intro h0
    have hr_dvd_q_z : (r : ℤ) ∣ (q : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd q r).mp h0
    have hr_dvd_q : r ∣ q := Int.natCast_dvd_natCast.mp hr_dvd_q_z
    have hr_dvd_qd : r ∣ q ^ d := dvd_pow hr_dvd_q hd.ne_zero
    have hr_dvd_1 : r ∣ 1 := (Nat.dvd_add_right hr_dvd_qd).mp hr_dvd_qd1
    exact hr_prime.not_dvd_one hr_dvd_1
  have hleg_rq : legendreSym r (q : ℤ) = ZMod.χ₄ r := by
    rcases legendreSym.eq_one_or_neg_one (p := r) hq_ne0 with h1 | hm1
    · rw [← hpow_leg, h1, one_pow]
    · rw [← hpow_leg, hm1, hd_odd.neg_one_pow]
  have hleg_qr : legendreSym q (r : ℤ) = ZMod.χ₄ r := by
    have hrec : legendreSym r (q : ℤ) = legendreSym q (r : ℤ) :=
      legendreSym.quadratic_reciprocity_one_mod_four hq4 hr_ne2
    exact hrec.symm.trans hleg_rq
  have hr4 : r % 4 = 1 ∨ r % 4 = 3 := by
    have hmod := Nat.odd_iff.mp hr_odd
    omega
  refine ⟨hleg_rq, hleg_qr, ?_, ?_⟩
  · constructor
    · intro h1
      rcases hr4 with hmod1 | hmod3
      · exact hmod1
      · rw [hleg_qr, ZMod.χ₄_nat_three_mod_four hmod3] at h1
        norm_num at h1
    · intro hmod1
      rw [hleg_qr, ZMod.χ₄_nat_one_mod_four hmod1]
  · constructor
    · intro hm1
      rcases hr4 with hmod1 | hmod3
      · rw [hleg_qr, ZMod.χ₄_nat_one_mod_four hmod1] at hm1
        norm_num at hm1
      · exact hmod3
    · intro hmod3
      rw [hleg_qr, ZMod.χ₄_nat_three_mod_four hmod3]

/-- Lifts the second-block `mod d ^ 2` and `z.minFac` profile on
`sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`, `d := (a + 1) / 2`) with the
prime-divisor Legendre reciprocity law and global Jacobi character `jacobiSym (q : ℤ) z = ZMod.χ₄ z`. -/
theorem exceptional_euler_second_block_jacobi_and_legendre_profile
    {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    ∃ y w z : ℕ,
      0 < y ∧ 0 < w ∧ 3 ≤ z ∧ Odd w ∧ Odd z ∧ Nat.Coprime w z ∧ ¬ d ∣ z ∧
      y = d * w * z ∧ q + 1 = 2 * d * w ^ 2 ∧ (q ^ d + 1) / (q + 1) = d * z ^ 2 ∧
      q ^ d + 1 = 2 * y ^ 2 ∧
      (z : ℤ) ^ 2 ≡ 1 + (d : ℤ) * (w : ℤ) ^ 2 [ZMOD (d : ℤ) ^ 2] ∧
      (∀ r ∈ z.primeFactors, 2 * d ∣ r - 1) ∧ 2 * d + 1 ≤ z.minFac ∧
      (haveI : Fact q.Prime := ⟨hq⟩
        ∀ r ∈ z.primeFactors,
          ∀ [Fact r.Prime],
            legendreSym r (q : ℤ) = ZMod.χ₄ r ∧
            legendreSym q (r : ℤ) = ZMod.χ₄ r ∧
            (legendreSym q (r : ℤ) = 1 ↔ r % 4 = 1) ∧
            (legendreSym q (r : ℤ) = -1 ↔ r % 4 = 3)) ∧
      jacobiSym (z : ℤ) q = ZMod.χ₄ z ∧
      jacobiSym (q : ℤ) z = ZMod.χ₄ z ∧
      (z % 4 = 1 → jacobiSym (q : ℤ) z = 1) ∧
      (z % 4 = 3 → jacobiSym (q : ℤ) z = -1) := by
  intro d
  obtain ⟨hd_prime, _, hd8, _, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  change d.Prime at hd_prime
  change d % 8 = 1 at hd8
  have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
  have hd5 : 5 ≤ d := by
    have := hd_prime.two_le
    omega
  obtain ⟨y, w, z, hy_pos, hw_pos, hz3, hw_odd, hz_odd, hcop, hy_dwz, hq1, hdiv, hpow,
    hmod_z2, _, hpf_dvd, hmin_ge, _⟩ :=
    exceptional_euler_second_block_mod_sq_and_z_minFac_sieve
      hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨w1, z1, _, _, _, _, hq1_1, hdiv_1, _, _, _, hdz_1, _⟩ :=
    exceptional_euler_second_block_exact_square hN ho hq hq4 ha4 ha hqm hform hl hi
  have hz1_eq : z1 = z := by
    have hmul : d * z1 ^ 2 = d * z ^ 2 := hdiv_1.symm.trans hdiv
    have hsq : z1 ^ 2 = z ^ 2 := Nat.eq_of_mul_eq_mul_left hd_prime.pos hmul
    exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hsq
  have hdz : ¬ d ∣ z := hz1_eq ▸ hdz_1
  have hrec :=
    second_block_z_prime_legendre_reciprocity
      hq hq4 hd_prime hd5 hd_odd hw_pos hz_odd hq1 hdiv hcop hdz
  have hjac_qz : jacobiSym (q : ℤ) z = ZMod.χ₄ z := by
    have hz_ne0 : z ≠ 0 := by omega
    conv_rhs =>
      rw [← Nat.prod_primeFactorsList hz_ne0, Nat.cast_list_prod]
    change jacobiSym (q : ℤ) z = ZMod.χ₄.toMonoidHom (z.primeFactorsList.map (Nat.cast : ℕ → ZMod 4)).prod
    rw [map_list_prod ZMod.χ₄.toMonoidHom, jacobiSym, List.map_map,
      ← List.pmap_eq_map fun _ => Nat.prime_of_mem_primeFactorsList]
    congr 1
    apply List.pmap_congr_left
    intro p hp pp _
    have hp_mem : p ∈ z.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨pp, Nat.dvd_of_mem_primeFactorsList hp, hz_ne0⟩
    have : Fact q.Prime := ⟨hq⟩
    have : Fact p.Prime := ⟨pp⟩
    exact (hrec p hp_mem).1
  have hjac_zq : jacobiSym (z : ℤ) q = ZMod.χ₄ z :=
    (jacobiSym.quadratic_reciprocity_one_mod_four hq4 hz_odd).symm.trans hjac_qz
  refine ⟨y, w, z, hy_pos, hw_pos, hz3, hw_odd, hz_odd, hcop, hdz, hy_dwz, hq1, hdiv, hpow,
    hmod_z2, hpf_dvd, hmin_ge, hrec, hjac_zq, hjac_qz, ?_, ?_⟩
  · intro hz1
    rw [hjac_qz, ZMod.χ₄_nat_one_mod_four hz1]
  · intro hz3_mod
    rw [hjac_qz, ZMod.χ₄_nat_three_mod_four hz3_mod]

end OddPerfect
