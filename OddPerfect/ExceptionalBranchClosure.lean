module

public import OddPerfect.ExceptionalBlockSquare
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exceptional Branch Closure (`OddPerfect.ExceptionalBranchClosure`)

Stepping Stone S8 on the prime-times-square Euler-index branch
`I = sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`, `d := (a + 1) / 2`):
1. `exceptional_d17_fifteen_dvd_w` and `exceptional_d17_w_ge_65760`: unconditional
   `15 ∣ w` and `65760 ≤ w` at `d = 17` (`a = 33`), eliminating `m < 2192` via
   small-modulus quadratic residue obstructions.
2. `exceptional_index_size_gt_ten_pow_740`: removes the `17 < (a + 1) / 2` hypothesis
   from `exceptional_index_size_gt_ten_pow_740_of_gt_17`, yielding `10 ^ 740 < N`
   unconditionally across all `a > 1` on `I = l * t ^ 2`.
3. `exceptional_euler_full_reciprocity_and_source_parity`: closes the Jacobi
   reciprocity loop `J((d : ℤ) | l) = 1`, exact odd-valuation source-count parity
   across `m`, `∏ u ∈ oddSigmaTargets N r, J((u : ℤ) | r) = 1` for all `r ∣ m`,
   and full target/source profile on the prime factors of `y = d * w * z`.
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset
open scoped NumberTheorySymbols

/-! ## 1. Modular Witness Elimination for `d = 17` (`a = 33`) -/

private def modPow17 (a r : ℕ) : ℕ :=
  let a2 := (a * a) % r
  let a4 := (a2 * a2) % r
  let a8 := (a4 * a4) % r
  let a16 := (a8 * a8) % r
  (a16 * a) % r

private lemma modPow17_eq (a r : ℕ) : modPow17 a r = a ^ 17 % r := by
  dsimp [modPow17]
  simp only [Nat.mod_mul_mod, Nat.mul_mod_mod]
  congr 1
  ring

private def noSqSol (lhs coeff r : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => ((coeff * k ^ 2) % r != lhs) && noSqSol lhs coeff r k

private lemma noSqSol_sound {lhs coeff r : ℕ} (k : ℕ)
    (h : noSqSol lhs coeff r k = true) :
    ∀ z < k, (coeff * z ^ 2) % r ≠ lhs := by
  induction k with
  | zero =>
    intro z hz
    omega
  | succ k ih =>
    simp only [noSqSol, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    intro z hz
    rcases Nat.lt_succ_iff_lt_or_eq.mp hz with hlt | rfl
    · exact ih h.2 z hlt
    · exact h.1

private def checkD17Mod (m r : ℕ) : Bool :=
  let w := 30 * m + 15
  let q := 34 * w ^ 2 - 1
  let qr := q % r
  let lhs := (modPow17 qr r + 1) % r
  let coeff := ((qr + 1) * 17) % r
  noSqSol lhs coeff r r

private def d17Primes : List ℕ := [7, 11, 13, 19, 23, 29, 31, 37, 41, 43, 67]

private def checkD17Row (m : ℕ) : Bool :=
  d17Primes.any (fun r => checkD17Mod m r)

private def allRangeBool (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => f n && allRangeBool f n

private lemma allRangeBool_sound {f : ℕ → Bool} (n : ℕ)
    (h : allRangeBool f n = true) : ∀ m < n, f m = true := by
  induction n with
  | zero =>
    intro m hm
    omega
  | succ n ih =>
    simp only [allRangeBool, Bool.and_eq_true] at h
    intro m hm
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hlt | rfl
    · exact ih h.2 m hlt
    · exact h.1

private lemma d17_all_lt_2192 : allRangeBool checkD17Row 2192 = true := by
  decide +kernel

private lemma d17_primes_pos : ∀ r ∈ d17Primes, 0 < r := by
  decide

private lemma d17_small_m_contradiction {m q z : ℕ} (hm : m < 2192)
    (hq1 : q + 1 = 34 * (30 * m + 15) ^ 2)
    (hq17 : q ^ 17 + 1 = (q + 1) * 17 * z ^ 2) : False := by
  have hrow := allRangeBool_sound 2192 d17_all_lt_2192 m hm
  simp only [checkD17Row, List.any_eq_true] at hrow
  obtain ⟨r, hr_mem, hr_ok⟩ := hrow
  have hr_pos : 0 < r := d17_primes_pos r hr_mem
  have hq_eq : q = 34 * (30 * m + 15) ^ 2 - 1 := by omega
  dsimp only [checkD17Mod] at hr_ok
  rw [← hq_eq] at hr_ok
  have hno := noSqSol_sound r hr_ok (z % r) (Nat.mod_lt z hr_pos)
  apply hno
  have hlhs : (modPow17 (q % r) r + 1) % r = (q ^ 17 + 1) % r := by
    simp only [modPow17_eq, Nat.add_mod, Nat.mod_mod, ← Nat.pow_mod]
  have hrhs : (((q % r + 1) * 17) % r * (z % r) ^ 2) % r = ((q + 1) * 17 * z ^ 2) % r := by
    simp only [Nat.mul_mod, Nat.add_mod, Nat.pow_mod, Nat.mod_mod]
  rw [hlhs, hrhs, hq17]

/-- At `d = 17` (`a = 33`), the cofactor `w` in `q + 1 = 34 * w ^ 2` satisfies `15 ∣ w`. -/
theorem exceptional_d17_fifteen_dvd_w {q w z : ℕ} (hq : q.Prime) (hq193 : 193 ≤ q)
    (hq1 : q + 1 = 34 * w ^ 2) (hq17 : q ^ 17 + 1 = (q + 1) * 17 * z ^ 2) :
    15 ∣ w := by
  have h3 : 3 ∣ w := by
    by_contra hw3
    have hw3_mod : w % 3 = 1 ∨ w % 3 = 2 := by omega
    have hq_mod3 : (q + 1) % 3 = 1 := by
      have h1 : (34 * w ^ 2) % 3 = (34 % 3 * ((w % 3) ^ 2 % 3)) % 3 := by
        rw [Nat.mul_mod, Nat.pow_mod]
      rw [← hq1] at h1
      rcases hw3_mod with h | h <;> rw [h] at h1 <;> norm_num at h1 <;> exact h1
    have h3_dvd_q : 3 ∣ q := by omega
    rcases hq.eq_one_or_self_of_dvd 3 h3_dvd_q with h | h <;> omega
  have h5 : 5 ∣ w := by
    by_contra hw5
    have hw5_mod : w % 5 = 1 ∨ w % 5 = 2 ∨ w % 5 = 3 ∨ w % 5 = 4 := by omega
    have hw2_mod : w ^ 2 % 5 = 1 ∨ w ^ 2 % 5 = 4 := by
      rw [Nat.pow_mod]
      rcases hw5_mod with h | h | h | h <;> rw [h] <;> decide
    rcases hw2_mod with h | h
    · have hq_mod5 : q % 5 = 3 := by
        have h1 : (q + 1) % 5 = (34 * w ^ 2) % 5 := congrArg (· % 5) hq1
        rw [Nat.mul_mod, h] at h1
        norm_num at h1
        omega
      have hlhs : (q ^ 17 + 1) % 5 = 4 := by
        rw [Nat.add_mod, Nat.pow_mod, hq_mod5]
      have hrhs : ((q + 1) * 17 * z ^ 2) % 5 = (3 * (z % 5) ^ 2) % 5 := by
        have hq1_mod : (q + 1) % 5 = 4 := by omega
        rw [Nat.mul_mod, Nat.mul_mod (q + 1) 17, hq1_mod, Nat.pow_mod z 2 5]
        norm_num
      have hmod_eq : (4 : ℕ) = (3 * (z % 5) ^ 2) % 5 := by
        rw [← hlhs, ← hrhs, hq17]
      have hz5 : z % 5 < 5 := Nat.mod_lt z (by decide)
      interval_cases hz : z % 5 <;> norm_num at hmod_eq
    · have hq_mod5 : q % 5 = 0 := by
        have h1 : (q + 1) % 5 = (34 * w ^ 2) % 5 := congrArg (· % 5) hq1
        rw [Nat.mul_mod, h] at h1
        norm_num at h1
        omega
      have h5_dvd_q : 5 ∣ q := Nat.dvd_of_mod_eq_zero hq_mod5
      rcases hq.eq_one_or_self_of_dvd 5 h5_dvd_q with h | h <;> omega
  exact (show Nat.Coprime 3 5 by decide).mul_dvd_of_dvd_of_dvd h3 h5

/-- At `d = 17` (`a = 33`), `w ≥ 65760` unconditionally. -/
theorem exceptional_d17_w_ge_65760 {q w z : ℕ} (hq : q.Prime) (hq193 : 193 ≤ q)
    (hw_odd : Odd w) (hq1 : q + 1 = 34 * w ^ 2) (hq17 : q ^ 17 + 1 = (q + 1) * 17 * z ^ 2) :
    65760 ≤ w := by
  have h15 : 15 ∣ w := exceptional_d17_fifteen_dvd_w hq hq193 hq1 hq17
  obtain ⟨k, hk⟩ := h15
  have hk_odd : Odd k := by
    rw [hk] at hw_odd
    exact hw_odd.of_dvd_nat (dvd_mul_left k 15)
  obtain ⟨m, rfl⟩ := hk_odd
  have hw_eq : w = 30 * m + 15 := by rw [hk]; ring
  by_contra! hw_lt
  have hm_lt : m < 2192 := by omega
  rw [hw_eq] at hq1
  exact d17_small_m_contradiction hm_lt hq1 hq17

/-- Unconditional size lower bound `N > 10 ^ 740` across all `a > 1` on the
prime-times-square Euler-index branch `I = sigma 1 (m ^ 2) / q ^ a = l * t ^ 2`. -/
theorem exceptional_index_size_gt_ten_pow_740 {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    10 ^ 740 < N := by
  obtain ⟨hd17_le, _, hq193, _, _, _⟩ :=
    exceptional_index_parameter_floors hN ho hq hq4 ha4 ha hqm hform hl hi
  rcases lt_or_eq_of_le hd17_le with hd17_lt | hd17_eq
  · exact exceptional_index_size_gt_ten_pow_740_of_gt_17 hN ho hq hq4 ha4 ha hqm hform hl hi hd17_lt
  · have hd_eq : (a + 1) / 2 = 17 := hd17_eq.symm
    have ha_eq : a = 33 := by omega
    obtain ⟨w, z, _, hw_odd, _, _, hq1, hQ, _, _, _, _, _⟩ :=
      exceptional_euler_second_block_exact_square hN ho hq hq4 ha4 ha hqm hform hl hi
    change q + 1 = 2 * ((a + 1) / 2) * w ^ 2 at hq1
    change (q ^ ((a + 1) / 2) + 1) / (q + 1) = ((a + 1) / 2) * z ^ 2 at hQ
    rw [hd_eq] at hq1 hQ
    have hq1_34 : q + 1 = 34 * w ^ 2 := by rw [hq1]
    have hdvd : q + 1 ∣ q ^ 17 + 1 := by
      simpa only [one_pow] using (by decide : Odd 17).nat_add_dvd_pow_add_pow q 1
    have hq17 : q ^ 17 + 1 = (q + 1) * 17 * z ^ 2 := by
      calc
        q ^ 17 + 1 = (q + 1) * ((q ^ 17 + 1) / (q + 1)) := (Nat.mul_div_cancel' hdvd).symm
        _ = (q + 1) * (17 * z ^ 2) := by rw [hQ]
        _ = (q + 1) * 17 * z ^ 2 := by ring
    have hw_ge : 65760 ≤ w := exceptional_d17_w_ge_65760 hq hq193 hw_odd hq1_34 hq17
    have hq_ge : 147 * 10 ^ 9 ≤ q := by
      have hw2 : 65760 ^ 2 ≤ w ^ 2 := Nat.pow_le_pow_left hw_ge 2
      have : 34 * 65760 ^ 2 ≤ q + 1 := by omega
      omega
    have h147 : 2 * (10 : ℕ) ^ 146 < 2379 * 147 ^ 66 := by decide
    have h740 : 2 * (10 : ℕ) ^ 740 < 2379 * q ^ (2 * a) := by
      have hpow : (147 * 10 ^ 9) ^ 66 ≤ q ^ (2 * a) := by
        rw [show 2 * a = 66 by omega]
        exact Nat.pow_le_pow_left hq_ge 66
      have hmul : 2 * (10 : ℕ) ^ 146 * (10 ^ 9) ^ 66 < 2379 * 147 ^ 66 * (10 ^ 9) ^ 66 :=
        Nat.mul_lt_mul_of_pos_right h147 (pow_pos (pow_pos (by decide) 9) 66)
      have hlhs : 2 * (10 : ℕ) ^ 740 = 2 * 10 ^ 146 * (10 ^ 9) ^ 66 := by
        rw [← pow_mul, mul_assoc, ← pow_add]
      have hrhs : 2379 * 147 ^ 66 * (10 ^ 9) ^ 66 = 2379 * (147 * 10 ^ 9) ^ 66 := by
        rw [mul_pow]
        ring
      rw [hlhs]
      rw [hrhs] at hmul
      exact lt_of_lt_of_le hmul (Nat.mul_le_mul_left 2379 hpow)
    have h2379 := (euler_component_index_ge_2379 hN ho hq hq4 ha4 hqm hform).1
    have hqa_pos : 0 < q ^ a := pow_pos hq.pos a
    have hN_lower : 2379 * q ^ (2 * a) < 2 * N := by
      have hmul := Nat.mul_lt_mul_of_pos_left h2379 hqa_pos
      calc
        2379 * q ^ (2 * a) = q ^ a * (2379 * q ^ a) := by rw [two_mul, pow_add]; ring
        _ < q ^ a * (2 * m ^ 2) := hmul
        _ = 2 * N := by rw [hform]; ring
    omega

/-! ## 2. Closed-Graph Jacobi Reciprocity & Odd-Valuation Source Parity Across `m` -/

private lemma sum_mod_two_filter_odd {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → ℕ) :
    (∑ i ∈ S, f i) ≡ (S.filter (fun i => Odd (f i))).card [MOD 2] := by
  induction S using Finset.induction_on with
  | empty => exact Nat.ModEq.refl _
  | insert a S ha ih =>
    rw [sum_insert ha, filter_insert]
    by_cases hw : Odd (f a)
    · rw [ite_eq_left hw, card_insert_of_notMem (fun h => ha (mem_filter.mp h).1), add_comm _ 1]
      exact (show f a ≡ 1 [MOD 2] from Nat.odd_iff.mp hw).add ih
    · rw [ite_eq_right hw]
      have hf : f a ≡ 0 [MOD 2] := Nat.even_iff.mp ((Nat.even_or_odd _).resolve_right hw)
      simpa using hf.add ih

/-- Full closed-graph Jacobi reciprocity and odd-valuation source/target parity profile
across `m = l * v * (d * w * z) * t` on `I = l * t ^ 2` (`a > 1`). -/
theorem exceptional_euler_full_reciprocity_and_source_parity {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    J((d : ℤ) | l) = 1 ∧
    (∀ u ∈ N.primeFactors,
      Odd ((m.primeFactors.filter (fun r => u ∈ oddSigmaTargets N r)).card) ↔ u = q ∨ u = l) ∧
    (∀ r ∈ m.primeFactors, (∏ u ∈ oddSigmaTargets N r, J((u : ℤ) | r)) = 1) ∧
    (∃ w z v : ℕ,
      Odd w ∧ Odd z ∧ Odd v ∧
      q + 1 = 2 * d * w ^ 2 ∧
      (q ^ d + 1) / (q + 1) = d * z ^ 2 ∧
      q ^ d + 1 = 2 * (d * w * z) ^ 2 ∧
      geometricBlock q d = l * v ^ 2 ∧
      m = l * v * (d * w * z) * t ∧
      ∀ p ∈ (d * w * z).primeFactors,
        p ∣ m ∧ p ≠ q ∧ Even (oddSigmaSources N p).card ∧
        (¬ (p = 3 ∧ m.factorization 3 = 2) → (oddSigmaTargets N p).Nonempty)) := by
  let d := (a + 1) / 2
  obtain ⟨_, _, _, hl_floor, _, _⟩ :=
    exceptional_index_parameter_floors hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨hd_prime, hd8, _, _, _⟩ :=
    prime_mul_square_index_forces_exceptional_prime_length hN ho hq hq4 ha4 ha hqm hform (Or.inr hl) hi
  change d.Prime at hd_prime
  change d % 8 = 1 at hd8
  obtain ⟨_, _, _, _, _, _, hJ_ld, heven_sources⟩ :=
    exceptional_euler_reciprocity_and_parity_profile hN ho hq hq4 ha4 ha hqm hform hl hi
  change J((l : ℤ) | d) = 1 at hJ_ld
  have hl_odd : Odd l := hl.odd_of_ne_two (by omega)
  have hd4 : d % 4 = 1 := by omega
  have hJ_dl : J((d : ℤ) | l) = 1 := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four hd4 hl_odd]
    exact hJ_ld
  obtain ⟨hodd_sig_m2, hql, hnonempty_targets⟩ :=
    exceptional_index_cofactor_odd_targets hN ho hq hq4 ha4 ha hqm hform hl hi
  have hm_ne : m ≠ 0 :=
    (ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self m (by decide : 2 ≠ 0)) _)).pos.ne'
  have hm2_ne : m ^ 2 ≠ 0 := pow_ne_zero 2 hm_ne
  have hqa_ne : q ^ a ≠ 0 := pow_ne_zero a hq.ne_zero
  have hval_r : ∀ r ∈ m.primeFactors, N.factorization r = 2 * m.factorization r := by
    intro r hr_mem
    have hr : r.Prime := Nat.prime_of_mem_primeFactors hr_mem
    have hr_dvd_m : r ∣ m := Nat.dvd_of_mem_primeFactors hr_mem
    have hr_ne_q : r ≠ q := fun h => hqm (h ▸ hr_dvd_m)
    have hr_not_q : ¬ r ∣ q := fun h => hr_ne_q ((Nat.prime_dvd_prime_iff_eq hr hq).mp h)
    rw [hform, Nat.factorization_mul hqa_ne hm2_ne, Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_eq_zero_of_not_dvd hr_not_q, mul_zero, zero_add,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hsig_m2_prod : sigma 1 (m ^ 2) = ∏ r ∈ m.primeFactors, sigma 1 (r ^ N.factorization r) := by
    have hmult := isMultiplicative_sigma.multiplicative_factorization (sigma 1) hm2_ne
    rw [Finsupp.prod, Nat.support_factorization, Nat.primeFactors_pow m (by decide : 2 ≠ 0)] at hmult
    rw [hmult]
    refine Finset.prod_congr rfl fun r hr_mem => ?_
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, ← hval_r r hr_mem]
  have hodd_source_iff : ∀ u ∈ N.primeFactors,
      Odd ((m.primeFactors.filter (fun r => u ∈ oddSigmaTargets N r)).card) ↔ u = q ∨ u = l := by
    intro u huN
    have hfilter_eq :
        m.primeFactors.filter (fun r => u ∈ oddSigmaTargets N r) =
          m.primeFactors.filter (fun r => Odd ((sigma 1 (r ^ N.factorization r)).factorization u)) := by
      ext r
      simp only [mem_filter, oddSigmaTargets, and_congr_right_iff]
      intro _
      exact ⟨fun h => h.2, fun h => ⟨huN, h⟩⟩
    rw [hfilter_eq]
    have hfac_sum :
        (sigma 1 (m ^ 2)).factorization u =
          ∑ r ∈ m.primeFactors, (sigma 1 (r ^ N.factorization r)).factorization u := by
      rw [hsig_m2_prod]
      exact Nat.factorization_prod_apply fun r hr_mem =>
        (sigma_pos 1 _ (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hr_mem).ne_zero)).ne'
    have hmod2 := sum_mod_two_filter_odd m.primeFactors
      (fun r => (sigma 1 (r ^ N.factorization r)).factorization u)
    rw [← hfac_sum] at hmod2
    have hodd_card_iff :
        Odd ((m.primeFactors.filter (fun r => Odd ((sigma 1 (r ^ N.factorization r)).factorization u))).card) ↔
          Odd ((sigma 1 (m ^ 2)).factorization u) := by
      rw [Nat.odd_iff, Nat.odd_iff]
      exact (congrArg (· = 1) hmod2).symm.to_iff
    rw [hodd_card_iff, ← mem_oddValuationPrimes, hodd_sig_m2]
    simp only [mem_insert, mem_singleton]
  have hjacobi_m : ∀ r ∈ m.primeFactors, (∏ u ∈ oddSigmaTargets N r, J((u : ℤ) | r)) = 1 := by
    intro r hr_mem
    have hr : r.Prime := Nat.prime_of_mem_primeFactors hr_mem
    have hr_dvd_m : r ∣ m := Nat.dvd_of_mem_primeFactors hr_mem
    have hr_dvd_N : r ∣ N :=
      hr_dvd_m.trans ((dvd_pow_self m (by decide : 2 ≠ 0)).trans (hform ▸ dvd_mul_left _ _))
    have hrN : r ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hr, hr_dvd_N, hN.2.ne'⟩
    have hr_even : Even (N.factorization r) := ⟨m.factorization r, by rw [hval_r r hr_mem]; ring⟩
    exact jacobi_prod_oddSigmaTargets_of_even hN ho hrN hr_even
  obtain ⟨w, z, v, hw_odd, hz_odd, hv_odd, hq1, hQ, hqd1, hgeom, _, _, _⟩ :=
    exceptional_euler_second_block_exact_square hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨w₁, y₁, v₁, hq1₁, hqd1₁, hgeom₁, hm_eq₁, _, _, _, _, _⟩ :=
    exceptional_index_cofactor_factorization hN ho hq hq4 ha4 ha hqm hform hl hi
  change q + 1 = 2 * d * w₁ ^ 2 at hq1₁
  change q ^ d + 1 = 2 * y₁ ^ 2 at hqd1₁
  change geometricBlock q d = l * v₁ ^ 2 at hgeom₁
  have hy₁_eq : y₁ = d * w * z := by
    apply Nat.pow_left_injective (by decide : 2 ≠ 0)
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
    rw [← hqd1₁, hqd1]
  have hv₁_eq : v₁ = v := by
    apply Nat.pow_left_injective (by decide : 2 ≠ 0)
    apply Nat.eq_of_mul_eq_mul_left hl.pos
    rw [← hgeom₁, hgeom]
  have hm_eq : m = l * v * (d * w * z) * t := by
    rw [hm_eq₁, hy₁_eq, hv₁_eq]
  refine ⟨hJ_dl, hodd_source_iff, hjacobi_m, w, z, v, hw_odd, hz_odd, hv_odd,
    hq1, hQ, hqd1, hgeom, hm_eq, ?_⟩
  intro p hp_mem
  have hp_dvd_y : p ∣ d * w * z := Nat.dvd_of_mem_primeFactors hp_mem
  have hp_dvd_m : p ∣ m := hp_dvd_y.trans ⟨l * v * t, by rw [hm_eq]; ring⟩
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hp_m : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd_m, hm_ne⟩
  have hp_ne_q : p ≠ q := fun h => hqm (h ▸ hp_dvd_m)
  exact ⟨hp_dvd_m, hp_ne_q, heven_sources p hp_m, hnonempty_targets p hp_m⟩

end OddPerfect
