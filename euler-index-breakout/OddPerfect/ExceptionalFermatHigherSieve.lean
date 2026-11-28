module

public import OddPerfect.ExceptionalFermatCongruences
import Mathlib.Tactic.Primality.Lucas
import Mathlib.Tactic.Ring

/-!
# Exceptional Fermat Higher-Order & Mod-8-Refined Sieve (`OddPerfect.ExceptionalFermatHigherSieve`)

Refines the cyclotomic-subgroup modular obstruction engine for the generalized Fermat
equation `q ^ d + 1 = 2 * y ^ 2` arising on the exceptional Euler-index branch
`I = sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`, `d := (a + 1) / 2`),
exploiting the unconditional `d % 8 = 1` invariant:

1. `pow_add_one_ne_twice_sq_of_order_mod_obstruction` and
   `pow_add_one_ne_twice_sq_of_order_mod_eight_obstruction`: generalize
   `pow_add_one_ne_twice_sq_of_order_obstruction` to restrict the exponent search to
   `k ∈ Finset.range m` with `Nat.Coprime k m` and `k % g = 1 % g` whenever `g ∣ m`
   and `d ≡ 1 [MOD g]` (in particular `g ∣ 8` and `d % 8 = 1`).
2. `pow_add_one_ne_twice_sq_of_mod_five_eq_three` and
   `euler_index_ne_prime_mul_square_of_mod_five_eq_three`: unconditional proof from
   `r = 5, m = 4, d % 4 = 1` that `q % 5 = 3` is impossible on `q ^ d + 1 = 2 * y ^ 2`,
   eliminating 20% of all primes on the exceptional Euler-index branch.
3. `exceptional_euler_mod_five_trichotomy` and
   `exceptional_euler_of_not_three_or_five_dvd`: combines `q % 5 ≠ 3` with
   `q + 1 = 2 * d * w ^ 2` modulo `5`:
   - `q % 5 = 4 → 5 ∣ w ∧ 5 ∣ m ∧ 5 ∣ N`;
   - `(q % 5 = 1 ∨ q % 5 = 2) → (d % 5 = 1 ∨ d % 5 = 4)`;
   - `¬ 5 ∣ N → (q % 5 = 1 ∨ q % 5 = 2) ∧ (d % 5 = 1 ∨ d % 5 = 4) ∧ d % 40 ∈ ({1, 9} : Finset ℕ)`;
   - `¬ 3 ∣ N → ¬ 5 ∣ N → q % 48 = 1 ∧ (q % 5 = 1 ∨ q % 5 = 2) ∧ d % 120 ∈ ({1, 49} : Finset ℕ) ∧ 241 ≤ d ∧ 481 ≤ a`.
4. `HigherExcludedFermatResidue`, `pow_add_one_ne_twice_sq_of_higher_excluded_residue`,
   `euler_index_ne_prime_mul_square_of_higher_excluded_residue`, and
   `componentIndex_ne_odd_prime_power_of_higher_excluded_residue`: 100 new excluded residue
   classes (disjoint from `ExcludedFermatResidue`) across 30 prime moduli unlocked by
   `d % 8 = 1` and orders `m ∈ {3, 4, 5, 6, 7, 8, 9, 10, 12, 16, 24, 40}`, certified via
   `decide +kernel`.
-/

public section

namespace OddPerfect

open ArithmeticFunction

/-! ## 1. Mod-`g` and Mod-`8` Refined Order Obstruction -/

/-- General cyclotomic-subgroup modular obstruction with congruence restriction:
if `g ∣ m`, `d ≡ 1 [MOD g]`, `q ^ m ≡ 1 [MOD r]`, `Nat.Coprime d m`, and no
exponent `k < m` coprime to `m` with `k % g = 1 % g` satisfies
`(q % r) ^ k + 1 ≡ 2 * z ^ 2 [MOD r]`, then `q ^ d + 1 ≠ 2 * y ^ 2`. -/
theorem pow_add_one_ne_twice_sq_of_order_mod_obstruction {q d y r m g : ℕ}
    (hr : 0 < r) (hm : 0 < m) (hgm : g ∣ m)
    (hcycle : q ^ m ≡ 1 [MOD r]) (hdm : Nat.Coprime d m) (hdg : d ≡ 1 [MOD g])
    (hobs : ∀ k ∈ Finset.range m, Nat.Coprime k m → k % g = 1 % g →
      ∀ z ∈ Finset.range r, ((q % r) ^ k + 1) % r ≠ (2 * z ^ 2) % r) :
    q ^ d + 1 ≠ 2 * y ^ 2 := by
  have hreduce : q ^ d ≡ q ^ (d % m) [MOD r] := by
    calc
      q ^ d = q ^ (m * (d / m) + d % m) := congrArg (q ^ ·) (Nat.div_add_mod d m).symm
      _ ≡ 1 ^ (d / m) * q ^ (d % m) [MOD r] := by
        rw [pow_add, pow_mul]
        exact (hcycle.pow _).mul_right _
      _ = q ^ (d % m) := by simp
  have hcop : Nat.Coprime (d % m) m := by
    rw [Nat.Coprime, (Nat.mod_modEq d m).gcd_eq]
    exact hdm
  have hk_mod : (d % m) % g = 1 % g := ((Nat.mod_modEq d m).of_dvd hgm).trans hdg
  intro heq
  apply hobs (d % m) (Finset.mem_range.mpr (Nat.mod_lt d hm)) hcop hk_mod
    (y % r) (Finset.mem_range.mpr (Nat.mod_lt y hr))
  change (q % r) ^ (d % m) + 1 ≡ 2 * (y % r) ^ 2 [MOD r]
  calc
    (q % r) ^ (d % m) + 1 ≡ q ^ (d % m) + 1 [MOD r] :=
      ((Nat.mod_modEq q r).pow _).add_right 1
    _ ≡ q ^ d + 1 [MOD r] := hreduce.symm.add_right 1
    _ = 2 * y ^ 2 := heq
    _ ≡ 2 * (y % r) ^ 2 [MOD r] := ((Nat.mod_modEq y r).symm.pow 2).mul_left 2

/-- Specialization of `pow_add_one_ne_twice_sq_of_order_mod_obstruction` to
`d % 8 = 1` and any `g` dividing both `8` and `m`. -/
theorem pow_add_one_ne_twice_sq_of_order_mod_eight_obstruction {q d y r m g : ℕ}
    (hr : 0 < r) (hm : 0 < m) (hg8 : g ∣ 8) (hgm : g ∣ m)
    (hcycle : q ^ m ≡ 1 [MOD r]) (hdm : Nat.Coprime d m) (hd8 : d % 8 = 1)
    (hobs : ∀ k ∈ Finset.range m, Nat.Coprime k m → k % g = 1 % g →
      ∀ z ∈ Finset.range r, ((q % r) ^ k + 1) % r ≠ (2 * z ^ 2) % r) :
    q ^ d + 1 ≠ 2 * y ^ 2 :=
  pow_add_one_ne_twice_sq_of_order_mod_obstruction hr hm hgm hcycle hdm
    ((show d ≡ 1 [MOD 8] from hd8).of_dvd hg8) hobs

/-! ## 2. Unconditional Elimination of `q % 5 = 3` -/

private lemma mod_five_eq_three_obs :
    ∀ k ∈ Finset.range 4, Nat.Coprime k 4 → k % 4 = 1 % 4 →
      ∀ z ∈ Finset.range 5, (3 ^ k + 1) % 5 ≠ (2 * z ^ 2) % 5 := by
  decide +kernel

/-- Unconditional elimination of `q % 5 = 3` on `q ^ d + 1 = 2 * y ^ 2` whenever
`d % 4 = 1` (in particular whenever `d % 8 = 1`). -/
theorem pow_add_one_ne_twice_sq_of_mod_five_eq_three {q d y : ℕ}
    (hq5 : q % 5 = 3) (hd4 : d % 4 = 1) :
    q ^ d + 1 ≠ 2 * y ^ 2 := by
  have hcycle : q ^ 4 ≡ 1 [MOD 5] := by
    change q ^ 4 % 5 = 1 % 5
    rw [Nat.pow_mod, hq5]
  have hdm : Nat.Coprime d 4 := by
    rw [Nat.Coprime, ← (Nat.mod_modEq d 4).gcd_eq, hd4]
    decide
  have hdg : d ≡ 1 [MOD 4] := hd4
  refine pow_add_one_ne_twice_sq_of_order_mod_obstruction
    (by decide : 0 < 5) (by decide : 0 < 4) dvd_rfl hcycle hdm hdg ?_
  intro k hk hkm hk4 z hz
  rw [hq5]
  exact mod_five_eq_three_obs k hk hkm hk4 z hz

/-- Every exceptional Euler-index candidate (`a > 1`, `I = l * t ^ 2` with
`l = 1 ∨ l.Prime`) satisfies `q % 5 ≠ 3` unconditionally. -/
theorem euler_index_ne_prime_mul_square_of_mod_five_eq_three {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l = 1 ∨ l.Prime) (hq5 : q % 5 = 3) :
    sigma 1 (m ^ 2) / q ^ a ≠ l * t ^ 2 := by
  intro hi
  rcases hl with rfl | hl
  · apply euler_index_not_square_of_exponent_gt_one hN ho hq hq4 ha4 ha hqm hform
    exact ⟨t, by simpa [pow_two] using hi⟩
  · obtain ⟨_, _, hd8, _, _, _, y, _, _, hpow⟩ :=
      exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
    exact pow_add_one_ne_twice_sq_of_mod_five_eq_three hq5 (by omega) hpow

/-! ## 3. Mod-5 Trichotomy and `(¬ 3 ∣ N ∧ ¬ 5 ∣ N)` Floor `241 ≤ d` -/

/-- Cofactor-explicit mod-5 trichotomy on `I = l * t ^ 2` (`a > 1`, `l.Prime`):
exposes the witness `w` with `q + 1 = 2 * d * w ^ 2` and `w ∣ m` so that
`q % 5 = 4` forces `5 ∣ w ∧ 5 ∣ m ∧ 5 ∣ N`. -/
theorem exceptional_euler_mod_five_cofactor_dvd {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    ∃ w : ℕ, q + 1 = 2 * d * w ^ 2 ∧ w ∣ m ∧
      (q % 5 = 4 → 5 ∣ w ∧ 5 ∣ m ∧ 5 ∣ N) := by
  intro d
  obtain ⟨hd, hd17, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨w, y, v, hq1, _, _, hm_eq, _, hdwy, _, _, _⟩ :=
    exceptional_index_cofactor_factorization hN ho hq hq4 ha4 ha hqm hform hl hi
  change d.Prime at hd
  change 17 ≤ d at hd17
  change q + 1 = 2 * d * w ^ 2 at hq1
  change d * w ∣ y at hdwy
  have hwm : w ∣ m :=
    (dvd_mul_left w d).trans (hdwy.trans ⟨l * v * t, by rw [hm_eq]; ring⟩)
  have hmN : m ∣ N :=
    (dvd_pow_self m (by decide : 2 ≠ 0)).trans (hform ▸ dvd_mul_left _ _)
  refine ⟨w, hq1, hwm, ?_⟩
  intro hq5
  have h5_dvd_q1 : 5 ∣ q + 1 := Nat.dvd_of_mod_eq_zero (by omega)
  rw [hq1, mul_assoc] at h5_dvd_q1
  have hp5 : Nat.Prime 5 := by decide
  have hd_not5 : ¬ 5 ∣ d := fun h => by
    rcases hd.eq_one_or_self_of_dvd 5 h with h1 | h5 <;> omega
  have hw5 : 5 ∣ w := by
    rcases hp5.dvd_mul.mp h5_dvd_q1 with h2 | hdw
    · omega
    · rcases hp5.dvd_mul.mp hdw with hd5 | hw2
      · exact absurd hd5 hd_not5
      · exact hp5.dvd_of_dvd_pow hw2
  exact ⟨hw5, hw5.trans hwm, (hw5.trans hwm).trans hmN⟩

/-- Mod-5 trichotomy on `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`):
1. `q % 5 ≠ 3` unconditionally;
2. `q % 5 = 4 → 5 ∣ m ∧ 5 ∣ N`;
3. `(q % 5 = 1 ∨ q % 5 = 2) → (d % 5 = 1 ∨ d % 5 = 4)`;
4. `¬ 5 ∣ N → (q % 5 = 1 ∨ q % 5 = 2) ∧ (d % 5 = 1 ∨ d % 5 = 4) ∧ d % 40 ∈ ({1, 9} : Finset ℕ)`. -/
theorem exceptional_euler_mod_five_trichotomy {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    q % 5 ≠ 3 ∧
    (q % 5 = 4 → 5 ∣ m ∧ 5 ∣ N) ∧
    ((q % 5 = 1 ∨ q % 5 = 2) → (d % 5 = 1 ∨ d % 5 = 4)) ∧
    (¬ 5 ∣ N → (q % 5 = 1 ∨ q % 5 = 2) ∧ (d % 5 = 1 ∨ d % 5 = 4) ∧
      d % 40 ∈ ({1, 9} : Finset ℕ)) := by
  intro d
  obtain ⟨hd, hd17, hd8, hq16, _, _, y, _, _, hpow⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨w, hq1, _, h4_imp⟩ :=
    exceptional_euler_mod_five_cofactor_dvd hN ho hq hq4 ha4 ha hqm hform hl hi
  change d.Prime at hd
  change 17 ≤ d at hd17
  change d % 8 = 1 at hd8
  change q % 16 = 1 at hq16
  change q + 1 = 2 * d * w ^ 2 at hq1
  have hq5_ne3 : q % 5 ≠ 3 := fun h3 =>
    pow_add_one_ne_twice_sq_of_mod_five_eq_three h3 (by omega) hpow
  have hq5_ne0 : q % 5 ≠ 0 := by
    intro h0
    have h5q : 5 ∣ q := Nat.dvd_of_mod_eq_zero h0
    rcases hq.eq_one_or_self_of_dvd 5 h5q with h1 | h5 <;> omega
  have h4_branch : q % 5 = 4 → 5 ∣ m ∧ 5 ∣ N := fun h =>
    let ⟨_, hm5, hN5⟩ := h4_imp h
    ⟨hm5, hN5⟩
  have h12_branch : (q % 5 = 1 ∨ q % 5 = 2) → (d % 5 = 1 ∨ d % 5 = 4) := by
    intro hq12
    have hw_not5 : ¬ 5 ∣ w := by
      intro hw5
      have h5_dvd_q1 : 5 ∣ q + 1 := by
        rw [hq1]
        exact (dvd_pow hw5 (by decide : 2 ≠ 0)).trans (dvd_mul_left _ _)
      omega
    have hw2_mod5 : w ^ 2 % 5 = 1 ∨ w ^ 2 % 5 = 4 := by
      have hw0 : w % 5 ≠ 0 := fun h => hw_not5 (Nat.dvd_of_mod_eq_zero h)
      have hw_cases : w % 5 = 1 ∨ w % 5 = 2 ∨ w % 5 = 3 ∨ w % 5 = 4 := by omega
      rw [pow_two, Nat.mul_mod]
      rcases hw_cases with h | h | h | h <;> rw [h] <;> decide
    have hmod : (2 * d * w ^ 2) % 5 = (q + 1) % 5 := by rw [hq1]
    rw [mul_assoc, Nat.mul_mod, Nat.mul_mod d (w ^ 2) 5, Nat.add_mod q 1 5] at hmod
    rcases hq12 with hq1' | hq2' <;> rcases hw2_mod5 with hw1 | hw4
    · rw [hq1', hw1] at hmod; omega
    · rw [hq1', hw4] at hmod; omega
    · rw [hq2', hw1] at hmod; omega
    · rw [hq2', hw4] at hmod; omega
  refine ⟨hq5_ne3, h4_branch, h12_branch, ?_⟩
  intro hN5
  have hq5_ne4 : q % 5 ≠ 4 := fun h4 => hN5 (h4_branch h4).2
  have hq12 : q % 5 = 1 ∨ q % 5 = 2 := by omega
  have hd14 : d % 5 = 1 ∨ d % 5 = 4 := h12_branch hq12
  have hd40 : d % 40 = 1 ∨ d % 40 = 9 := by omega
  have hd40_mem : d % 40 ∈ ({1, 9} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hd40
  exact ⟨hq12, hd14, hd40_mem⟩

/-- When neither `3` nor `5` divides `N` on `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2`
(`a > 1`, `l.Prime`), we unconditionally obtain `q % 48 = 1`, `q % 5 = 1 ∨ q % 5 = 2`,
`d % 120 ∈ ({1, 49} : Finset ℕ)`, `241 ≤ d`, and `481 ≤ a`. -/
theorem exceptional_euler_of_not_three_or_five_dvd {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2)
    (hN3 : ¬ 3 ∣ N) (hN5 : ¬ 5 ∣ N) :
    let d := (a + 1) / 2
    q % 48 = 1 ∧ (q % 5 = 1 ∨ q % 5 = 2) ∧
      d % 120 ∈ ({1, 49} : Finset ℕ) ∧ 241 ≤ d ∧ 481 ≤ a := by
  intro d
  obtain ⟨hd, _, _, _, _, _, _, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨hq48, hd24, hd73, _⟩ :=
    exceptional_euler_of_not_three_dvd hN ho hq hq4 ha4 ha hqm hform hl hi hN3
  obtain ⟨_, _, _, hnot5⟩ :=
    exceptional_euler_mod_five_trichotomy hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨hq12, hd14, _⟩ := hnot5 hN5
  change d.Prime at hd
  change d % 24 = 1 at hd24
  change 73 ≤ d at hd73
  have hd120 : d % 120 = 1 ∨ d % 120 = 49 := by
    have hcop24_5 : Nat.Coprime 24 5 := by decide
    have hd24_dvd1 : 24 ∣ d - 1 := Nat.dvd_of_mod_eq_zero (by omega)
    rcases hd14 with hd5_1 | hd5_4
    · have hd5_dvd1 : 5 ∣ d - 1 := Nat.dvd_of_mod_eq_zero (by omega)
      obtain ⟨k, hk⟩ := hcop24_5.mul_dvd_of_dvd_of_dvd hd24_dvd1 hd5_dvd1
      exact Or.inl (by omega)
    · have hd24_dvd49 : 24 ∣ d - 49 := Nat.dvd_of_mod_eq_zero (by omega)
      have hd5_dvd49 : 5 ∣ d - 49 := Nat.dvd_of_mod_eq_zero (by omega)
      obtain ⟨k, hk⟩ := hcop24_5.mul_dvd_of_dvd_of_dvd hd24_dvd49 hd5_dvd49
      exact Or.inr (by omega)
  have hd120_mem : d % 120 ∈ ({1, 49} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hd120
  have hd241 : 241 ≤ d := by
    by_contra! hd_lt
    have hq_div : d / 120 = 0 ∨ d / 120 = 1 := by
      rcases Nat.lt_or_ge d 120 with h0 | h1
      · exact Or.inl (Nat.div_eq_of_lt h0)
      · exact Or.inr (by rw [Nat.div_eq_sub_div (by decide) h1, Nat.div_eq_of_lt (by omega)])
    have hmod_eq : d = 120 * (d / 120) + d % 120 := (Nat.div_add_mod d 120).symm
    rcases hq_div with hq0 | hq1
    · rw [hq0, mul_zero, zero_add] at hmod_eq
      rcases hd120 with hm1 | hm49
      · rw [hm1] at hmod_eq; exact absurd (hmod_eq ▸ hd73) (by decide)
      · rw [hm49] at hmod_eq; exact absurd (hmod_eq ▸ hd73) (by decide)
    · rw [hq1, mul_one] at hmod_eq
      rcases hd120 with hm1 | hm49
      · rw [hm1] at hmod_eq
        have hnp : ¬ Nat.Prime 121 := fun h => by
          rcases h.eq_one_or_self_of_dvd 11 (by decide) with h1 | h11 <;> omega
        exact hnp (by simpa [hmod_eq] using hd)
      · rw [hm49] at hmod_eq
        have hnp : ¬ Nat.Prime 169 := fun h => by
          rcases h.eq_one_or_self_of_dvd 13 (by decide) with h1 | h13 <;> omega
        exact hnp (by simpa [hmod_eq] using hd)
  have ha481 : 481 ≤ a :=
    Nat.le_of_add_le_add_right (b := 1)
      (by simpa using (Nat.mul_le_mul_left 2 hd241).trans (Nat.mul_div_le (a + 1) 2))
  exact ⟨hq48, hq12, hd120_mem, hd241, ha481⟩

/-! ## 4. Higher-Order & Mod-8-Refined Excluded Residue Sieve -/

/-- 100 new excluded residue classes (disjoint from `ExcludedFermatResidue`) across
30 prime moduli (`5, 13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101, 109, 127, 137,
149, 151, 157, 173, 181, 193, 197, 199, 223, 229, 233, 241, 313, 379, 401`) having
multiplicative orders `m ∈ {3, 4, 5, 6, 7, 8, 9, 10, 12, 16, 24, 40}` coprime to
every prime `d ≥ 17`, certified under `d % 8 = 1` via `decide +kernel`. -/
@[expose] def HigherExcludedFermatResidue (q : ℕ) : Prop :=
  q % 5 = 3 ∨
  q % 13 = 8 ∨
  q % 17 = 2 ∨ q % 17 = 6 ∨ q % 17 = 9 ∨ q % 17 = 11 ∨
  q % 29 = 12 ∨
  q % 37 = 6 ∨
  q % 41 = 11 ∨ q % 41 = 12 ∨ q % 41 = 14 ∨ q % 41 = 27 ∨ q % 41 = 28 ∨ q % 41 = 34 ∨
  q % 53 = 23 ∨
  q % 61 = 11 ∨
  q % 73 = 10 ∨ q % 73 = 21 ∨ q % 73 = 30 ∨ q % 73 = 43 ∨ q % 73 = 51 ∨ q % 73 = 52 ∨
  q % 89 = 12 ∨ q % 89 = 37 ∨
  q % 97 = 18 ∨ q % 97 = 27 ∨ q % 97 = 33 ∨ q % 97 = 50 ∨ q % 97 = 70 ∨ q % 97 = 79 ∨
  q % 101 = 91 ∨
  q % 109 = 33 ∨
  q % 127 = 19 ∨ q % 127 = 107 ∨
  q % 137 = 41 ∨ q % 137 = 96 ∨
  q % 149 = 44 ∨
  q % 151 = 32 ∨ q % 151 = 118 ∨
  q % 157 = 12 ∨ q % 157 = 13 ∨ q % 157 = 129 ∨ q % 157 = 144 ∨ q % 157 = 145 ∨
  q % 173 = 80 ∨
  q % 181 = 19 ∨ q % 181 = 42 ∨ q % 181 = 48 ∨ q % 181 = 59 ∨
    q % 181 = 125 ∨ q % 181 = 132 ∨ q % 181 = 135 ∨
  q % 193 = 9 ∨ q % 193 = 43 ∨ q % 193 = 81 ∨ q % 193 = 112 ∨
  q % 197 = 14 ∨
  q % 199 = 43 ∨ q % 199 = 58 ∨ q % 199 = 92 ∨ q % 199 = 106 ∨
    q % 199 = 162 ∨ q % 199 = 175 ∨ q % 199 = 178 ∨ q % 199 = 180 ∨
  q % 223 = 39 ∨ q % 223 = 183 ∨
  q % 229 = 94 ∨ q % 229 = 107 ∨ q % 229 = 134 ∨
  q % 233 = 89 ∨ q % 233 = 136 ∨ q % 233 = 144 ∨ q % 233 = 221 ∨
  q % 241 = 16 ∨ q % 241 = 30 ∨ q % 241 = 64 ∨ q % 241 = 87 ∨ q % 241 = 91 ∨
    q % 241 = 98 ∨ q % 241 = 111 ∨ q % 241 = 130 ∨ q % 241 = 177 ∨
    q % 241 = 205 ∨ q % 241 = 226 ∨ q % 241 = 233 ∨
  q % 313 = 29 ∨ q % 313 = 54 ∨ q % 313 = 259 ∨ q % 313 = 284 ∨
  q % 379 = 86 ∨ q % 379 = 94 ∨ q % 379 = 119 ∨ q % 379 = 125 ∨
    q % 379 = 138 ∨ q % 379 = 195 ∨
  q % 401 = 29 ∨ q % 401 = 83 ∨ q % 401 = 329 ∨ q % 401 = 362

private def noTwiceSqMatch (lhs r : ℕ) : Bool :=
  (List.range r).all fun z => lhs != (2 * z ^ 2) % r

open Mathlib.Tactic.Primality in
private def orderModEightObstructionCheck (r m g : ℕ) (xs : List ℕ) : Bool :=
  decide (0 < r ∧ 0 < m ∧ g ∣ 8 ∧ g ∣ m) &&
  xs.all fun x =>
    powMod x m r == 1 % r &&
    (List.range m).all fun k =>
      (Nat.gcd k m != 1) || (k % g != 1 % g) ||
      noTwiceSqMatch ((powMod x k r + 1) % r) r

private theorem pow_add_one_ne_twice_sq_of_mod8_check {q d y r m g : ℕ} {xs : List ℕ}
    (hc : orderModEightObstructionCheck r m g xs = true) (hx : q % r ∈ xs)
    (hdm : Nat.Coprime d m) (hd8 : d % 8 = 1) :
    q ^ d + 1 ≠ 2 * y ^ 2 := by
  simp only [orderModEightObstructionCheck, noTwiceSqMatch, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, beq_iff_eq, Bool.or_eq_true, bne_iff_ne,
    List.mem_range] at hc
  obtain ⟨⟨hr, hm, hg8, hgm⟩, hall⟩ := hc
  obtain ⟨hpow_m, hk_all⟩ := hall (q % r) hx
  have hcycle : q ^ m ≡ 1 [MOD r] := by
    change q ^ m % r = 1 % r
    rw [Nat.pow_mod, ← Mathlib.Tactic.Primality.powMod_def, hpow_m]
  have hobs : ∀ k ∈ Finset.range m, Nat.Coprime k m → k % g = 1 % g →
      ∀ z ∈ Finset.range r, ((q % r) ^ k + 1) % r ≠ (2 * z ^ 2) % r := by
    intro k hk hkm hkg z hz
    have hk_lt : k < m := Finset.mem_range.mp hk
    have hz_lt : z < r := Finset.mem_range.mp hz
    rcases hk_all k hk_lt with (hne | hmod_ne) | hz_all
    · exact absurd hkm hne
    · exact absurd hkg hmod_ne
    · have hneq := hz_all z hz_lt
      rw [Mathlib.Tactic.Primality.powMod_def] at hneq
      have hmod : ((q % r) ^ k % r + 1) % r = ((q % r) ^ k + 1) % r :=
        (Nat.mod_modEq ((q % r) ^ k) r).add_right 1
      exact fun heq => hneq (hmod.trans heq)
  exact pow_add_one_ne_twice_sq_of_order_mod_eight_obstruction hr hm hg8 hgm hcycle hdm hd8 hobs

private lemma coprime_of_prime_ge_17 {d m : ℕ} (hd : d.Prime) (hd17 : 17 ≤ d)
    (hm0 : 0 < m) (hm16 : m ≤ 16) : Nat.Coprime d m :=
  hd.coprime_iff_not_dvd.mpr fun h => absurd (Nat.le_of_dvd hm0 h) (by omega)

private lemma hcheck_5_4 : orderModEightObstructionCheck 5 4 4 [3] = true := by decide +kernel
private lemma hcheck_13_4 : orderModEightObstructionCheck 13 4 4 [8] = true := by decide +kernel
private lemma hcheck_17_8 : orderModEightObstructionCheck 17 8 8 [2, 9] = true := by decide +kernel
private lemma hcheck_17_16 : orderModEightObstructionCheck 17 16 8 [6, 11] = true := by decide +kernel
private lemma hcheck_29_4 : orderModEightObstructionCheck 29 4 4 [12] = true := by decide +kernel
private lemma hcheck_37_4 : orderModEightObstructionCheck 37 4 4 [6] = true := by decide +kernel
private lemma hcheck_41_8 : orderModEightObstructionCheck 41 8 8 [14, 27] = true := by decide +kernel
private lemma hcheck_41_40 : orderModEightObstructionCheck 41 40 8 [11, 12, 28, 34] = true := by decide +kernel
private lemma hcheck_53_4 : orderModEightObstructionCheck 53 4 4 [23] = true := by decide +kernel
private lemma hcheck_61_4 : orderModEightObstructionCheck 61 4 4 [11] = true := by decide +kernel
private lemma hcheck_73_8 : orderModEightObstructionCheck 73 8 8 [10, 51] = true := by decide +kernel
private lemma hcheck_73_24 : orderModEightObstructionCheck 73 24 8 [21, 30, 43, 52] = true := by decide +kernel
private lemma hcheck_89_8 : orderModEightObstructionCheck 89 8 8 [12, 37] = true := by decide +kernel
private lemma hcheck_97_8 : orderModEightObstructionCheck 97 8 8 [33, 50] = true := by decide +kernel
private lemma hcheck_97_16 : orderModEightObstructionCheck 97 16 8 [18, 27, 70, 79] = true := by decide +kernel
private lemma hcheck_101_4 : orderModEightObstructionCheck 101 4 4 [91] = true := by decide +kernel
private lemma hcheck_109_4 : orderModEightObstructionCheck 109 4 4 [33] = true := by decide +kernel
private lemma hcheck_127_3 : orderModEightObstructionCheck 127 3 1 [19, 107] = true := by decide +kernel
private lemma hcheck_137_8 : orderModEightObstructionCheck 137 8 8 [41, 96] = true := by decide +kernel
private lemma hcheck_149_4 : orderModEightObstructionCheck 149 4 4 [44] = true := by decide +kernel
private lemma hcheck_151_3 : orderModEightObstructionCheck 151 3 1 [32, 118] = true := by decide +kernel
private lemma hcheck_157_3 : orderModEightObstructionCheck 157 3 1 [12, 144] = true := by decide +kernel
private lemma hcheck_157_4 : orderModEightObstructionCheck 157 4 4 [129] = true := by decide +kernel
private lemma hcheck_157_6 : orderModEightObstructionCheck 157 6 2 [13, 145] = true := by decide +kernel
private lemma hcheck_173_4 : orderModEightObstructionCheck 173 4 4 [80] = true := by decide +kernel
private lemma hcheck_181_3 : orderModEightObstructionCheck 181 3 1 [48, 132] = true := by decide +kernel
private lemma hcheck_181_4 : orderModEightObstructionCheck 181 4 4 [19] = true := by decide +kernel
private lemma hcheck_181_5 : orderModEightObstructionCheck 181 5 1 [42, 59, 125, 135] = true := by decide +kernel
private lemma hcheck_193_4 : orderModEightObstructionCheck 193 4 4 [81, 112] = true := by decide +kernel
private lemma hcheck_193_8 : orderModEightObstructionCheck 193 8 8 [9, 43] = true := by decide +kernel
private lemma hcheck_197_4 : orderModEightObstructionCheck 197 4 4 [14] = true := by decide +kernel
private lemma hcheck_199_3 : orderModEightObstructionCheck 199 3 1 [92, 106] = true := by decide +kernel
private lemma hcheck_199_9 : orderModEightObstructionCheck 199 9 1 [43, 58, 162, 175, 178, 180] = true := by decide +kernel
private lemma hcheck_223_3 : orderModEightObstructionCheck 223 3 1 [39, 183] = true := by decide +kernel
private lemma hcheck_229_3 : orderModEightObstructionCheck 229 3 1 [94, 134] = true := by decide +kernel
private lemma hcheck_229_4 : orderModEightObstructionCheck 229 4 4 [107] = true := by decide +kernel
private lemma hcheck_233_4 : orderModEightObstructionCheck 233 4 4 [89, 144] = true := by decide +kernel
private lemma hcheck_233_8 : orderModEightObstructionCheck 233 8 8 [136, 221] = true := by decide +kernel
private lemma hcheck_241_4 : orderModEightObstructionCheck 241 4 4 [64, 177] = true := by decide +kernel
private lemma hcheck_241_5 : orderModEightObstructionCheck 241 5 1 [87, 91, 98, 205] = true := by decide +kernel
private lemma hcheck_241_6 : orderModEightObstructionCheck 241 6 2 [16, 226] = true := by decide +kernel
private lemma hcheck_241_8 : orderModEightObstructionCheck 241 8 8 [30, 233] = true := by decide +kernel
private lemma hcheck_241_16 : orderModEightObstructionCheck 241 16 8 [111, 130] = true := by decide +kernel
private lemma hcheck_313_12 : orderModEightObstructionCheck 313 12 4 [29, 54, 259, 284] = true := by decide +kernel
private lemma hcheck_379_7 : orderModEightObstructionCheck 379 7 1 [86, 94, 119, 125, 138, 195] = true := by decide +kernel
private lemma hcheck_401_10 : orderModEightObstructionCheck 401 10 2 [29, 83, 329, 362] = true := by decide +kernel

/-- Every residue class in `HigherExcludedFermatResidue` eliminates
`q ^ d + 1 = 2 * y ^ 2` for every prime exponent `d ≥ 17` with `d % 8 = 1`. -/
theorem pow_add_one_ne_twice_sq_of_higher_excluded_residue {q d y : ℕ}
    (hd : d.Prime) (hd17 : 17 ≤ d) (hd8 : d % 8 = 1)
    (hres : HigherExcludedFermatResidue q) :
    q ^ d + 1 ≠ 2 * y ^ 2 := by
  have h3 : Nat.Coprime d 3 := coprime_of_prime_ge_17 hd hd17 (by decide) (by decide)
  have h4 : Nat.Coprime d 4 := coprime_of_prime_ge_17 hd hd17 (by decide) (by decide)
  have h5 : Nat.Coprime d 5 := coprime_of_prime_ge_17 hd hd17 (by decide) (by decide)
  have h6 : Nat.Coprime d 6 := coprime_of_prime_ge_17 hd hd17 (by decide) (by decide)
  have h7 : Nat.Coprime d 7 := coprime_of_prime_ge_17 hd hd17 (by decide) (by decide)
  have h8 : Nat.Coprime d 8 := coprime_of_prime_ge_17 hd hd17 (by decide) (by decide)
  have h9 : Nat.Coprime d 9 := coprime_of_prime_ge_17 hd hd17 (by decide) (by decide)
  have h10 : Nat.Coprime d 10 := coprime_of_prime_ge_17 hd hd17 (by decide) (by decide)
  have h12 : Nat.Coprime d 12 := coprime_of_prime_ge_17 hd hd17 (by decide) (by decide)
  have h16 : Nat.Coprime d 16 := coprime_of_prime_ge_17 hd hd17 (by decide) (by decide)
  have h24 : Nat.Coprime d 24 := by simpa [show (24 : ℕ) = 3 * 8 by decide] using h3.mul_right h8
  have h40 : Nat.Coprime d 40 := by simpa [show (40 : ℕ) = 5 * 8 by decide] using h5.mul_right h8
  rcases hres with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_5_4 (by simp [h]) h4 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_13_4 (by simp [h]) h4 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_17_8 (by simp [h]) h8 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_17_16 (by simp [h]) h16 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_17_8 (by simp [h]) h8 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_17_16 (by simp [h]) h16 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_29_4 (by simp [h]) h4 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_37_4 (by simp [h]) h4 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_41_40 (by simp [h]) h40 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_41_40 (by simp [h]) h40 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_41_8 (by simp [h]) h8 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_41_8 (by simp [h]) h8 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_41_40 (by simp [h]) h40 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_41_40 (by simp [h]) h40 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_53_4 (by simp [h]) h4 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_61_4 (by simp [h]) h4 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_73_8 (by simp [h]) h8 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_73_24 (by simp [h]) h24 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_73_24 (by simp [h]) h24 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_73_24 (by simp [h]) h24 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_73_8 (by simp [h]) h8 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_73_24 (by simp [h]) h24 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_89_8 (by simp [h]) h8 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_89_8 (by simp [h]) h8 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_97_16 (by simp [h]) h16 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_97_16 (by simp [h]) h16 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_97_8 (by simp [h]) h8 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_97_8 (by simp [h]) h8 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_97_16 (by simp [h]) h16 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_97_16 (by simp [h]) h16 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_101_4 (by simp [h]) h4 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_109_4 (by simp [h]) h4 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_127_3 (by simp [h]) h3 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_127_3 (by simp [h]) h3 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_137_8 (by simp [h]) h8 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_137_8 (by simp [h]) h8 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_149_4 (by simp [h]) h4 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_151_3 (by simp [h]) h3 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_151_3 (by simp [h]) h3 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_157_3 (by simp [h]) h3 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_157_6 (by simp [h]) h6 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_157_4 (by simp [h]) h4 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_157_3 (by simp [h]) h3 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_157_6 (by simp [h]) h6 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_173_4 (by simp [h]) h4 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_181_4 (by simp [h]) h4 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_181_5 (by simp [h]) h5 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_181_3 (by simp [h]) h3 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_181_5 (by simp [h]) h5 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_181_5 (by simp [h]) h5 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_181_3 (by simp [h]) h3 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_181_5 (by simp [h]) h5 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_193_8 (by simp [h]) h8 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_193_8 (by simp [h]) h8 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_193_4 (by simp [h]) h4 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_193_4 (by simp [h]) h4 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_197_4 (by simp [h]) h4 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_199_9 (by simp [h]) h9 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_199_9 (by simp [h]) h9 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_199_3 (by simp [h]) h3 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_199_3 (by simp [h]) h3 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_199_9 (by simp [h]) h9 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_199_9 (by simp [h]) h9 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_199_9 (by simp [h]) h9 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_199_9 (by simp [h]) h9 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_223_3 (by simp [h]) h3 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_223_3 (by simp [h]) h3 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_229_3 (by simp [h]) h3 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_229_4 (by simp [h]) h4 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_229_3 (by simp [h]) h3 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_233_4 (by simp [h]) h4 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_233_8 (by simp [h]) h8 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_233_4 (by simp [h]) h4 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_233_8 (by simp [h]) h8 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_241_6 (by simp [h]) h6 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_241_8 (by simp [h]) h8 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_241_4 (by simp [h]) h4 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_241_5 (by simp [h]) h5 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_241_5 (by simp [h]) h5 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_241_5 (by simp [h]) h5 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_241_16 (by simp [h]) h16 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_241_16 (by simp [h]) h16 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_241_4 (by simp [h]) h4 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_241_5 (by simp [h]) h5 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_241_6 (by simp [h]) h6 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_241_8 (by simp [h]) h8 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_313_12 (by simp [h]) h12 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_313_12 (by simp [h]) h12 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_313_12 (by simp [h]) h12 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_313_12 (by simp [h]) h12 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_379_7 (by simp [h]) h7 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_379_7 (by simp [h]) h7 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_379_7 (by simp [h]) h7 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_379_7 (by simp [h]) h7 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_379_7 (by simp [h]) h7 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_379_7 (by simp [h]) h7 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_401_10 (by simp [h]) h10 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_401_10 (by simp [h]) h10 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_401_10 (by simp [h]) h10 hd8
  · exact pow_add_one_ne_twice_sq_of_mod8_check hcheck_401_10 (by simp [h]) h10 hd8

/-- Unconditional exclusion of `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`,
`l = 1 ∨ l.Prime`) whenever the Euler prime lies in `HigherExcludedFermatResidue`. -/
theorem euler_index_ne_prime_mul_square_of_higher_excluded_residue {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l = 1 ∨ l.Prime) (hres : HigherExcludedFermatResidue q) :
    sigma 1 (m ^ 2) / q ^ a ≠ l * t ^ 2 := by
  intro hi
  rcases hl with rfl | hl
  · apply euler_index_not_square_of_exponent_gt_one hN ho hq hq4 ha4 ha hqm hform
    exact ⟨t, by simpa [pow_two] using hi⟩
  · obtain ⟨hd, hd17, hd8, _, _, _, y, _, _, hpow⟩ :=
      exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
    exact pow_add_one_ne_twice_sq_of_higher_excluded_residue hd hd17 hd8 hres hpow

/-- Unconditional exclusion of odd prime-power component indices
`componentIndex N q = p ^ j` whenever `q` lies in `HigherExcludedFermatResidue`. -/
theorem componentIndex_ne_odd_prime_power_of_higher_excluded_residue
    {N q p j : ℕ} (ho : Odd N) (hN : N.Perfect) (hqN : q ∈ N.primeFactors)
    (hres : HigherExcludedFermatResidue q) (hp : p.Prime) (hj : Odd j) :
    componentIndex N q ≠ p ^ j := by
  intro hi
  let a := N.factorization q
  let b := ordCompl[q] N
  have hq := Nat.prime_of_mem_primeFactors hqN
  have ha : 0 < a := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hqN)
  have hform : N = q ^ a * b := (Nat.ordProj_mul_ordCompl_eq_self N q).symm
  have hqb : ¬ q ∣ b := Nat.not_dvd_ordCompl hq hN.2.ne'
  obtain ⟨i, _, hleft, hright, _⟩ := exists_component_index hN hq hform hqb
  have hci : componentIndex N q = i := by
    rw [componentIndex, show sigma 1 (ordCompl[q] N) = q ^ a * i from hleft]
    exact Nat.mul_div_cancel_left i (pow_pos hq.pos _)
  have hip : i = p ^ j := hci.symm.trans hi
  have hp2 : p ≠ 2 := by
    rintro rfl
    by_cases hj1 : j = 1
    · have hi2 : i = 2 := by simpa [hj1] using hip
      exact component_index_not_prime hN ho hq ha hform hqb hleft hright (hi2 ▸ Nat.prime_two)
    have h4 : 4 ∣ i := hip ▸ pow_dvd_pow 2 (by have := hj.pos; omega : 2 ≤ j)
    have h4b : 4 ∣ 2 * b := hright ▸ h4.trans (dvd_mul_left _ _)
    have hbodd := ho.of_dvd_nat (hform ▸ dvd_mul_left b _)
    exact hbodd.not_two_dvd_nat (Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) h4b)
  obtain ⟨m, hq4, ha4, hqm, hbm⟩ :=
    euler_form_of_odd_component_index hN ho hq ha hform hqb hleft hright
      (hip ▸ (hp.odd_of_ne_two hp2).pow)
  rw [hbm] at hform hleft
  have heq : sigma 1 (m ^ 2) / q ^ a = p ^ j := by
    rw [hleft, Nat.mul_div_cancel_left i (pow_pos hq.pos _), hip]
  have ha' := (odd_prime_power_euler_index_constraints hN ho hq hq4 ha4 hqm hform hp hj heq).1
  obtain ⟨k, hk⟩ := hj
  apply euler_index_ne_prime_mul_square_of_higher_excluded_residue hN ho hq hq4 ha4 ha' hqm hform
    (t := p ^ k) (Or.inr hp) hres
  rw [heq, hk]
  ring

end OddPerfect
