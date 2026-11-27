module

public import OddPerfect.EulerExceptionalObstruction
public import OddPerfect.PositiveHalfReturn
public import OddPerfect.GlobalObstruction
public import OddPerfect.ThreeModFourGraph
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact Second-Block Square & Closed-Graph Reciprocity (`OddPerfect.ExceptionalBlockSquare`)

Tightens the remaining prime-times-square Euler-index branch
`I = sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`, `d := (a + 1) / 2`) by proving:
1. `exceptional_euler_second_block_exact_square`: exact second-block cyclotomic square
   decomposition `(q ^ d + 1) / (q + 1) = d * z ^ 2` with `q ^ d + 1 = 2 * (d * w * z) ^ 2`,
   `Nat.Coprime w z`, `¬ d ∣ z`, and `z ^ 2 ≡ 1 [MOD 2 * w ^ 2]`.
2. `exceptional_euler_reciprocity_and_parity_profile`: closed-graph quadratic reciprocity and
   odd-valuation source/target parity invariants coupling `q`, `l`, `d`, `oddSigmaTargets`,
   `threeOddTargets`, and `oddSigmaSources`.
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset
open scoped NumberTheorySymbols

private lemma odd_geometricBlock {q d : ℕ} (hq : Odd q) (hd : Odd d) :
    Odd (geometricBlock q d) := by
  have hcast : ((geometricBlock q d : ℕ) : ZMod 2) = 1 := by
    have hq2 : (q : ZMod 2) = 1 := by
      rw [← ZMod.natCast_mod, Nat.odd_iff.mp hq, Nat.cast_one]
    have hd2 : (d : ZMod 2) = 1 := by
      rw [← ZMod.natCast_mod, Nat.odd_iff.mp hd, Nat.cast_one]
    simp [geometricBlock, hq2, hd2]
  rw [Nat.odd_iff]
  have hm := (ZMod.natCast_eq_natCast_iff (geometricBlock q d) 1 2).mp (by simpa using hcast)
  simpa [Nat.ModEq] using hm

private lemma second_block_quotient_congruence {q d w : ℕ}
    (hd_prime : d.Prime) (hd_odd : Odd d) (hq1 : q + 1 = 2 * d * w ^ 2) :
    ∃ K : ℤ, ((q ^ d + 1 : ℕ) : ℤ) =
      ((q + 1 : ℕ) : ℤ) * ((d : ℤ) + 2 * (d : ℤ) ^ 2 * (w : ℤ) ^ 2 * K) := by
  have hd3 : 3 ≤ d := by
    have h2 := hd_prime.two_le
    obtain ⟨k, hk⟩ := hd_odd
    omega
  let X : ℤ := (q + 1 : ℕ)
  have hX_eq : X = 2 * (d : ℤ) * (w : ℤ) ^ 2 := by
    dsimp [X]
    exact_mod_cast hq1
  have hq_eq : (q : ℤ) = X + (-1) := by
    dsimp [X]
    ring
  let f : ℕ → ℤ := fun j => X ^ j * (-1) ^ (d - j) * (d.choose j : ℤ)
  have hbin : ((q ^ d + 1 : ℕ) : ℤ) = (∑ j ∈ range (d + 1), f j) + 1 := by
    push_cast
    rw [hq_eq, add_pow]
  have hsplit1 : (∑ j ∈ range (d + 1), f j) = (∑ j ∈ range d, f (j + 1)) + f 0 :=
    Finset.sum_range_succ' f d
  have hf0 : f 0 + 1 = 0 := by
    simp [f, hd_odd.neg_one_pow]
  have hd_sub : d = (d - 1) + 1 := by omega
  have hsplit2 : (∑ j ∈ range d, f (j + 1)) = (∑ j ∈ range (d - 1), f (j + 2)) + f 1 := by
    conv_lhs => rw [hd_sub]
    exact Finset.sum_range_succ' (fun j => f (j + 1)) (d - 1)
  have hf1 : f 1 = X * (d : ℤ) := by
    dsimp [f]
    have hdeven : Even (d - 1) := by
      obtain ⟨k, hk⟩ := hd_odd
      exact ⟨k, by omega⟩
    rw [pow_one, Nat.choose_one_right, hdeven.neg_one_pow, mul_one]
  let M : ℤ := 2 * (d : ℤ) ^ 2 * (w : ℤ) ^ 2
  have hdvd_sum : X * M ∣ ∑ j ∈ range (d - 1), f (j + 2) := by
    apply Finset.dvd_sum
    intro j hj
    dsimp [f]
    by_cases hj0 : j = 0
    · subst j
      simp only [zero_add]
      have hd_choose : (d : ℤ) ∣ (d.choose 2 : ℤ) := by
        obtain ⟨k, hk⟩ := hd_odd
        have hch : d.choose 2 = d * k := by
          rw [Nat.choose_two_right, show d - 1 = 2 * k by omega, ← mul_assoc,
            Nat.mul_comm d 2, mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
        exact_mod_cast (⟨k, hch⟩ : d ∣ d.choose 2)
      obtain ⟨c, hc⟩ := hd_choose
      refine ⟨(-1) ^ (d - 2) * c, ?_⟩
      rw [pow_two, hc]
      have hX_mul : X * X = X * (2 * (d : ℤ) * (w : ℤ) ^ 2) := by rw [← hX_eq]
      calc
        X * X * (-1) ^ (d - 2) * ((d : ℤ) * c)
            = X * (2 * (d : ℤ) * (w : ℤ) ^ 2) * (-1) ^ (d - 2) * ((d : ℤ) * c) := by rw [hX_mul]
        _ = X * M * ((-1) ^ (d - 2) * c) := by dsimp [M]; ring
    · have hj_ge : 1 ≤ j := Nat.pos_of_ne_zero hj0
      have hpow : X ^ (j + 2) = X * (2 * (d : ℤ) * (w : ℤ) ^ 2) ^ 2 * X ^ (j - 1) := by
        rw [← hX_eq, show j + 2 = 1 + 2 + (j - 1) by omega, pow_add, pow_add, pow_one]
      refine ⟨2 * (w : ℤ) ^ 2 * X ^ (j - 1) * (-1) ^ (d - (j + 2)) * (d.choose (j + 2) : ℤ), ?_⟩
      rw [hpow]
      dsimp [M]
      ring
  obtain ⟨K, hK⟩ := hdvd_sum
  refine ⟨K, ?_⟩
  rw [hbin, hsplit1, add_assoc, hf0, add_zero, hsplit2, hf1, hK]
  dsimp [M, X]
  ring

/-- On the prime-times-square Euler-index branch `I = l * t ^ 2` with `a > 1`,
the second half-block admits the exact cyclotomic square decomposition
`(q ^ d + 1) / (q + 1) = d * z ^ 2` with `q ^ d + 1 = 2 * (d * w * z) ^ 2`,
`Nat.Coprime w z`, `¬ d ∣ z`, and `z ^ 2 ≡ 1 [MOD 2 * w ^ 2]`. -/
theorem exceptional_euler_second_block_exact_square {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    ∃ w z v : ℕ,
      Odd w ∧ Odd z ∧ Odd v ∧
      q + 1 = 2 * d * w ^ 2 ∧
      (q ^ d + 1) / (q + 1) = d * z ^ 2 ∧
      q ^ d + 1 = 2 * (d * w * z) ^ 2 ∧
      geometricBlock q d = l * v ^ 2 ∧
      Nat.Coprime w z ∧
      ¬ d ∣ z ∧
      z ^ 2 ≡ 1 [MOD 2 * w ^ 2] := by
  let d := (a + 1) / 2
  obtain ⟨hd_prime, hd8, hq16, _, _⟩ :=
    prime_mul_square_index_forces_exceptional_prime_length hN ho hq hq4 ha4 ha hqm hform (Or.inr hl) hi
  change d.Prime at hd_prime
  change d % 8 = 1 at hd8
  have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
  have hd_pos : 0 < d := hd_prime.pos
  have hq_odd : Odd q := Nat.odd_iff.mpr (by omega)
  obtain ⟨w, y, v, hq1, hqd1, hgeom⟩ :=
    prime_mul_square_euler_block_equations hN ho hq hq4 ha4 ha hqm hform hl hi
  change q + 1 = 2 * d * w ^ 2 at hq1
  change q ^ d + 1 = 2 * y ^ 2 at hqd1
  change geometricBlock q d = l * v ^ 2 at hgeom
  have hw_odd : Odd w := by
    have hmod : (2 * d * w ^ 2) % 4 = 2 := by rw [← hq1]; omega
    have hw_not_even : ¬ Even w := by
      rintro ⟨k, rfl⟩
      have : (2 * d * (k + k) ^ 2) % 4 = 0 := by
        have h4 : 2 * d * (k + k) ^ 2 = 4 * (2 * d * k ^ 2) := by ring
        rw [h4, Nat.mul_mod_right]
      omega
    exact (Nat.even_or_odd w).resolve_left hw_not_even
  have hv_odd : Odd v := by
    have hgeom_odd : Odd (geometricBlock q d) := odd_geometricBlock hq_odd hd_odd
    rw [hgeom] at hgeom_odd
    exact (hgeom_odd.of_dvd_nat (dvd_mul_left _ _)).of_dvd_nat (dvd_pow_self v (by decide : 2 ≠ 0))
  have hdvd_q1 : q + 1 ∣ q ^ d + 1 := by
    simpa only [one_pow] using hd_odd.nat_add_dvd_pow_add_pow q 1
  let Q := (q ^ d + 1) / (q + 1)
  have hQ_mul : (q + 1) * Q = q ^ d + 1 := Nat.mul_div_cancel' hdvd_q1
  obtain ⟨K, hK⟩ := second_block_quotient_congruence hd_prime hd_odd hq1
  have hQ_int : (Q : ℤ) = (d : ℤ) + 2 * (d : ℤ) ^ 2 * (w : ℤ) ^ 2 * K := by
    have hX_ne : ((q + 1 : ℕ) : ℤ) ≠ 0 := by positivity
    apply mul_left_cancel₀ hX_ne
    have hQ_mul_int : ((q + 1 : ℕ) : ℤ) * (Q : ℤ) = ((q ^ d + 1 : ℕ) : ℤ) := by
      exact_mod_cast hQ_mul
    rw [hQ_mul_int, hK]
  have hd_dvd_Q : d ∣ Q := by
    have hd_int : (d : ℤ) ∣ (Q : ℤ) := by
      rw [hQ_int]
      exact ⟨1 + 2 * (d : ℤ) * (w : ℤ) ^ 2 * K, by ring⟩
    exact_mod_cast hd_int
  let Z := Q / d
  have hQ_eq : Q = d * Z := (Nat.mul_div_cancel' hd_dvd_Q).symm
  have hZ_int : (Z : ℤ) = 1 + 2 * (d : ℤ) * (w : ℤ) ^ 2 * K := by
    have hd_ne : (d : ℤ) ≠ 0 := by positivity
    apply mul_left_cancel₀ hd_ne
    have hQ_eq_int : (d : ℤ) * (Z : ℤ) = (Q : ℤ) := by exact_mod_cast hQ_eq.symm
    rw [hQ_eq_int, hQ_int]
    ring
  have hy_eq_Q : y ^ 2 = d * w ^ 2 * Q := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
    calc
      2 * y ^ 2 = q ^ d + 1 := hqd1.symm
      _ = (q + 1) * Q := hQ_mul.symm
      _ = 2 * d * w ^ 2 * Q := by rw [hq1]
      _ = 2 * (d * w ^ 2 * Q) := by ring
  have hy_eq_Z : y ^ 2 = (d * w) ^ 2 * Z := by
    rw [hy_eq_Q, hQ_eq]
    ring
  have hdw_dvd_y : d * w ∣ y := by
    have hdw_ne : d * w ≠ 0 := Nat.mul_ne_zero hd_pos.ne' hw_odd.pos.ne'
    have hy_ne : y ≠ 0 := by rintro rfl; simp at hqd1
    apply (Nat.factorization_le_iff_dvd hdw_ne hy_ne).mp
    intro p
    have hle := (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hdw_ne) (pow_ne_zero 2 hy_ne)).mpr
      ⟨Z, hy_eq_Z⟩ p
    rw [Nat.factorization_pow, Nat.factorization_pow, Finsupp.smul_apply, Finsupp.smul_apply,
      smul_eq_mul, smul_eq_mul] at hle
    omega
  obtain ⟨z, hz_eq⟩ := hdw_dvd_y
  have hdw_pos : 0 < d * w := Nat.mul_pos hd_pos hw_odd.pos
  have hZ_eq : Z = z ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hdw_pos 2)
    calc
      (d * w) ^ 2 * Z = y ^ 2 := hy_eq_Z.symm
      _ = (d * w * z) ^ 2 := by rw [hz_eq]
      _ = (d * w) ^ 2 * z ^ 2 := by ring
  have hQ_final : Q = d * z ^ 2 := by rw [hQ_eq, hZ_eq]
  have hqd1_final : q ^ d + 1 = 2 * (d * w * z) ^ 2 := by rw [hqd1, hz_eq]
  have hZ_pos : 0 < Z := by
    have hQ_pos : 0 < Q := Nat.div_pos (by
      have : q ≤ q ^ d := Nat.le_self_pow hd_pos.ne' q
      omega) (by omega)
    rw [hQ_eq] at hQ_pos
    exact Nat.pos_of_mul_pos_left hQ_pos
  have hz_ge1 : 1 ≤ z ^ 2 := by omega
  have hmod_full : z ^ 2 ≡ 1 [MOD 2 * d * w ^ 2] := by
    apply Nat.ModEq.symm
    apply (Nat.modEq_iff_dvd' hz_ge1).mpr
    have h_int : ((2 * d * w ^ 2 : ℕ) : ℤ) ∣ ((z ^ 2 - 1 : ℕ) : ℤ) := by
      have hz2_int : (z : ℤ) ^ 2 = 1 + 2 * (d : ℤ) * (w : ℤ) ^ 2 * K := by
        rw [← Nat.cast_pow, ← hZ_eq, hZ_int]
      rw [Nat.cast_sub hz_ge1, Nat.cast_pow, Nat.cast_one, hz2_int]
      refine ⟨K, ?_⟩
      push_cast
      ring
    exact_mod_cast h_int
  have hmod_w : z ^ 2 ≡ 1 [MOD 2 * w ^ 2] :=
    hmod_full.of_dvd ⟨d, by ring⟩
  have hmod_d : z ^ 2 ≡ 1 [MOD d] :=
    hmod_full.of_dvd ⟨2 * w ^ 2, by ring⟩
  have hz_odd : Odd z := by
    have hz2_odd : Odd (z ^ 2) := by
      have h2 : z ^ 2 ≡ 1 [MOD 2] := hmod_w.of_dvd (dvd_mul_right 2 (w ^ 2))
      exact Nat.odd_iff.mpr h2
    exact hz2_odd.of_dvd_nat (dvd_pow_self z (by decide : 2 ≠ 0))
  have hcop_wz : Nat.Coprime w z := by
    apply Nat.coprime_of_dvd
    intro p hp hpw hpz
    have hp_dvd_z2 : p ∣ z ^ 2 := hpz.trans (dvd_pow_self z (by decide : 2 ≠ 0))
    have hp_dvd_mod : p ∣ 2 * w ^ 2 :=
      hpw.trans (dvd_mul_of_dvd_right (dvd_pow_self w (by decide : 2 ≠ 0)) 2)
    have hp_dvd_diff : p ∣ z ^ 2 - 1 := hp_dvd_mod.trans ((Nat.modEq_iff_dvd' hz_ge1).mp hmod_w.symm)
    have hp_dvd_one : p ∣ 1 := (Nat.dvd_sub_iff_right hz_ge1 hp_dvd_z2).mp hp_dvd_diff
    exact hp.not_dvd_one hp_dvd_one
  have hd_ndvd_z : ¬ d ∣ z := by
    intro hdz
    have hdz2 : d ∣ z ^ 2 := hdz.trans (dvd_pow_self z (by decide : 2 ≠ 0))
    have h0 : z ^ 2 % d = 0 := Nat.mod_eq_zero_of_dvd hdz2
    have h1 : z ^ 2 % d = 1 % d := hmod_d
    rw [h0, Nat.mod_eq_of_lt hd_prime.one_lt] at h1
    exact zero_ne_one h1
  exact ⟨w, z, v, hw_odd, hz_odd, hv_odd, hq1, hQ_final, hqd1_final, hgeom,
    hcop_wz, hd_ndvd_z, hmod_w⟩

/-- Closed-graph quadratic reciprocity and odd-valuation source/target parity invariants
on the remaining prime-times-square Euler-index branch `I = l * t ^ 2` (`a > 1`). -/
theorem exceptional_euler_reciprocity_and_parity_profile {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    q % 16 = 1 ∧
    a % 8 = 1 ∧
    Even (threeOddTargets N q).card ∧
    (∏ r ∈ oddSigmaTargets N q, J((r : ℤ) | q)) = 1 ∧
    J((l : ℤ) | q) = 1 ∧
    J((q : ℤ) | l) = 1 ∧
    J((l : ℤ) | d) = 1 ∧
    (∀ r ∈ m.primeFactors, Even (oddSigmaSources N r).card) := by
  let d := (a + 1) / 2
  obtain ⟨hd_prime, hd8, hq16, w, hw⟩ :=
    prime_mul_square_index_forces_exceptional_prime_length hN ho hq hq4 ha4 ha hqm hform (Or.inr hl) hi
  change d.Prime at hd_prime
  change d % 8 = 1 at hd8
  change (q + 1) / 2 = d * w ^ 2 at hw
  have ha8 : a % 8 = 1 := by
    have ha_eq : a + 1 = 2 * d := by dsimp [d]; omega
    omega
  have ha_pos : 0 < a := by omega
  have hm_ne : m ≠ 0 :=
    (ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self m (by decide : 2 ≠ 0)) _)).pos.ne'
  have hqN : q ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, hform ▸ dvd_mul_of_dvd_left (dvd_pow_self q ha_pos.ne') _, hN.2.ne'⟩
  have hval_q : N.factorization q = a := by
    rw [hform, Nat.factorization_mul (pow_ne_zero a hq.ne_zero) (pow_ne_zero 2 hm_ne),
      Finsupp.add_apply, hq.factorization_pow, Finsupp.single_eq_same, Nat.factorization_pow,
      Finsupp.smul_apply, Nat.factorization_eq_zero_of_not_dvd hqm, smul_eq_mul, mul_zero, add_zero]
  have heven_three : Even (threeOddTargets N q).card := by
    apply (Nat.even_or_odd _).resolve_right
    rw [odd_threeOddTargets_euler_iff hN hqN hq4 (by simpa [hval_q] using ha4), hval_q]
    omega
  have hjacobi_prod : (∏ r ∈ oddSigmaTargets N q, J((r : ℤ) | q)) = 1 := by
    rw [jacobi_prod_oddSigmaTargets_euler hN ho hqN hq4 (by simpa [hval_q] using ha4),
      ZMod.χ₈_nat_eq_if_mod_eight, ite_eq_right (by omega), ite_eq_left (by omega)]
  obtain ⟨v, hmod_plus, _, hsq_all⟩ :=
    prime_mul_square_euler_neighbor_congruences hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨_, _, v', _, _, hgeom⟩ :=
    prime_mul_square_euler_block_equations hN ho hq hq4 ha4 ha hqm hform hl hi
  have hd_pos : 0 < d := hd_prime.pos
  have hgeom_mod : geometricBlock q d % q = 1 := by
    have hsig : geometricBlock q d = sigma 1 (q ^ (d - 1)) := by
      rw [sigma_one_apply_prime_pow hq, Nat.sub_add_cancel hd_pos]
      rfl
    rw [hsig]
    exact sigma_prime_pow_mod_self hq (d - 1)
  have hlv2_mod : (l * v' ^ 2) % q = 1 := by
    rw [← hgeom]
    exact hgeom_mod
  have hq_ndvd_v : ¬ q ∣ v' := by
    intro hqv
    have hq_dvd_prod : q ∣ l * v' ^ 2 :=
      dvd_mul_of_dvd_right (hqv.trans (dvd_pow_self v' (by decide : 2 ≠ 0))) l
    have h0 : (l * v' ^ 2) % q = 0 := Nat.mod_eq_zero_of_dvd hq_dvd_prod
    omega
  have hcop_vq : ((v' : ℤ)).gcd q = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact (hq.coprime_iff_not_dvd.mpr hq_ndvd_v).symm
  have hJ_lv2 : J(((l * v' ^ 2 : ℕ) : ℤ) | q) = 1 := by
    have hmod : (((l * v' ^ 2 : ℕ) : ℤ)) % (q : ℤ) = (1 : ℤ) % (q : ℤ) := by
      exact_mod_cast (show (l * v' ^ 2) % q = 1 % q by
        rw [hlv2_mod, Nat.mod_eq_of_lt hq.one_lt])
    rw [jacobiSym.mod_left' hmod, jacobiSym.one_left]
  have hJ_lq : J((l : ℤ) | q) = 1 := by
    have hmul : J(((l * v' ^ 2 : ℕ) : ℤ) | q) = J((l : ℤ) | q) * J((v' : ℤ) | q) ^ 2 := by
      rw [Nat.cast_mul, Nat.cast_pow, jacobiSym.mul_left, jacobiSym.pow_left]
    rw [jacobiSym.sq_one hcop_vq, mul_one] at hmul
    exact hmul.symm.trans hJ_lv2
  obtain ⟨_, _, _, hl_floor, _, _⟩ :=
    exceptional_index_parameter_floors hN ho hq hq4 ha4 ha hqm hform hl hi
  have hl_odd : Odd l := by
    have hl2 : l ≠ 2 := by omega
    exact hl.odd_of_ne_two hl2
  have hJ_ql : J((q : ℤ) | l) = 1 := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four hq4 hl_odd]
    exact hJ_lq
  have hd_dvd_q1 : d ∣ q + 1 := by
    have hq_half : q + 1 = 2 * ((q + 1) / 2) := by omega
    rw [hq_half, hw]
    exact dvd_mul_of_dvd_right (dvd_mul_right d (w ^ 2)) 2
  have hsq_ld : IsSquare (l : ZMod d) := hsq_all d hd_dvd_q1
  have hld_ne : l ≠ d := by omega
  have hd_ndvd_l : ¬ d ∣ l := fun h => hld_ne ((Nat.prime_dvd_prime_iff_eq hd_prime hl).mp h).symm
  have hl_zmod_ne : ((l : ℤ) : ZMod d) ≠ 0 := by
    intro hz
    have hdz : d ∣ l := by
      rw [← Int.natCast_dvd_natCast]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (l : ℤ) d).mp (by simpa using hz)
    exact hd_ndvd_l hdz
  have hJ_ld : J((l : ℤ) | d) = 1 := by
    let : Fact d.Prime := ⟨hd_prime⟩
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    exact (legendreSym.eq_one_iff d hl_zmod_ne).mpr (by simpa using hsq_ld)
  refine ⟨hq16, ha8, heven_three, hjacobi_prod, hJ_lq, hJ_ql, hJ_ld, ?_⟩
  intro r hr_mem
  have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr_mem
  have hr_dvd_m : r ∣ m := Nat.dvd_of_mem_primeFactors hr_mem
  have hr_dvd_N : r ∣ N :=
    hr_dvd_m.trans ((dvd_pow_self m (by decide : 2 ≠ 0)).trans (hform ▸ dvd_mul_left _ _))
  have hr_odd : Odd r := ho.of_dvd_nat hr_dvd_N
  have hr_ne_q : r ≠ q := fun h => hqm (h ▸ hr_dvd_m)
  have hr_not_q : ¬ r ∣ q := fun h => hr_ne_q ((Nat.prime_dvd_prime_iff_eq hr_prime hq).mp h)
  have hN_even : Even (N.factorization r) := by
    rw [hform, Nat.factorization_mul (pow_ne_zero a hq.ne_zero) (pow_ne_zero 2 hm_ne),
      Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_eq_zero_of_not_dvd hr_not_q, mul_zero, zero_add,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    exact ⟨m.factorization r, by omega⟩
  exact (even_oddSigmaSources_iff hN hr_prime hr_odd).mpr hN_even

end OddPerfect
