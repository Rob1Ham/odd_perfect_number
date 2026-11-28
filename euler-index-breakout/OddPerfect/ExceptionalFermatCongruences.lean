module

public import OddPerfect.ExceptionalFermatReduction
import Mathlib.Tactic.Primality.Lucas
import Mathlib.Tactic.Ring

/-!
# Exceptional Fermat Congruences (`OddPerfect.ExceptionalFermatCongruences`)

Cyclotomic-subgroup modular obstruction engine for the generalized Fermat
equation `q ^ d + 1 = 2 * y ^ 2` arising on the exceptional Euler-index branch
`I = sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`):
1. `pow_add_one_ne_twice_sq_of_order_obstruction`: general finite-order modular
   obstruction eliminating `q ^ d + 1 = 2 * y ^ 2` whenever `q ^ m ≡ 1 [MOD r]`,
   `Nat.Coprime d m`, and no coprime exponent `k < m` yields a square target
   `2 * z ^ 2` modulo `r`.
2. `ExcludedFermatResidue` and `pow_add_one_ne_twice_sq_of_excluded_residue`:
   48 excluded residue classes across 15 prime moduli (`7, 13, 17, 31, 37, 41,
   61, 73, 79, 89, 97, 101, 103, 109, 113`) having multiplicative orders
   `m ∈ {3, 4, 5, 6, 8, 12}` coprime to every prime `d ≥ 17`, verified via
   kernel-checked `decide +kernel` certificates.
3. `euler_index_ne_prime_mul_square_of_excluded_residue` and
   `componentIndex_ne_odd_prime_power_of_excluded_residue`: unconditional
   exclusion of both `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l = 1 ∨
   l.Prime`) and `componentIndex N q = p ^ j` (`p.Prime`, `Odd j`) under
   `ExcludedFermatResidue q`.
4. `exceptional_euler_mod_three_and_seventy_three_dichotomy` (and
   `exceptional_euler_three_dvd_dichotomy`, `exceptional_euler_of_not_three_dvd`):
   either `q % 3 = 2 ∧ 3 ∣ m ∧ 3 ∣ N` (and in general when `¬ 3 ∣ N`,
   unconditionally), `q % 48 = 1`, `d % 24 = 1`, `73 ≤ d`, and `145 ≤ a`.
-/

public section

namespace OddPerfect

open ArithmeticFunction

/-- General cyclotomic-subgroup modular obstruction: if `q ^ m ≡ 1 [MOD r]`,
`Nat.Coprime d m`, and no exponent `k < m` coprime to `m` satisfies
`(q % r) ^ k + 1 ≡ 2 * z ^ 2 [MOD r]`, then `q ^ d + 1 ≠ 2 * y ^ 2`. -/
theorem pow_add_one_ne_twice_sq_of_order_obstruction {q d y r m : ℕ}
    (hr : 0 < r) (hm : 0 < m)
    (hcycle : q ^ m ≡ 1 [MOD r]) (hdm : Nat.Coprime d m)
    (hobs : ∀ k ∈ Finset.range m, Nat.Coprime k m →
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
  intro heq
  apply hobs (d % m) (Finset.mem_range.mpr (Nat.mod_lt d hm)) hcop
    (y % r) (Finset.mem_range.mpr (Nat.mod_lt y hr))
  change (q % r) ^ (d % m) + 1 ≡ 2 * (y % r) ^ 2 [MOD r]
  calc
    (q % r) ^ (d % m) + 1 ≡ q ^ (d % m) + 1 [MOD r] :=
      ((Nat.mod_modEq q r).pow _).add_right 1
    _ ≡ q ^ d + 1 [MOD r] := hreduce.symm.add_right 1
    _ = 2 * y ^ 2 := heq
    _ ≡ 2 * (y % r) ^ 2 [MOD r] := ((Nat.mod_modEq y r).symm.pow 2).mul_left 2

/-- The 48 residue classes across 15 prime moduli (`7, 13, 17, 31, 37, 41, 61,
73, 79, 89, 97, 101, 103, 109, 113`) where `q` has multiplicative order
`m ∈ {3, 4, 5, 6, 8, 12}` and avoids `q ^ d + 1 = 2 * y ^ 2` for every prime
`d ≥ 17`. -/
@[expose] def ExcludedFermatResidue (q : ℕ) : Prop :=
  q % 7 = 2 ∨ q % 7 = 4 ∨
  q % 13 = 3 ∨ q % 13 = 9 ∨
  q % 17 = 4 ∨ q % 17 = 13 ∨
  q % 31 = 5 ∨ q % 31 = 25 ∨
  q % 37 = 10 ∨ q % 37 = 11 ∨ q % 37 = 26 ∨ q % 37 = 27 ∨
  q % 41 = 10 ∨ q % 41 = 16 ∨ q % 41 = 18 ∨ q % 41 = 37 ∨
  q % 61 = 13 ∨ q % 61 = 14 ∨ q % 61 = 47 ∨ q % 61 = 48 ∨
  q % 73 = 9 ∨ q % 73 = 27 ∨ q % 73 = 46 ∨ q % 73 = 65 ∨
  q % 79 = 23 ∨ q % 79 = 55 ∨
  q % 89 = 34 ∨ q % 89 = 55 ∨
  q % 97 = 6 ∨ q % 97 = 16 ∨ q % 97 = 22 ∨ q % 97 = 36 ∨
  q % 97 = 62 ∨ q % 97 = 75 ∨ q % 97 = 81 ∨ q % 97 = 91 ∨
  q % 101 = 36 ∨ q % 101 = 84 ∨ q % 101 = 87 ∨ q % 101 = 95 ∨
  q % 103 = 46 ∨ q % 103 = 56 ∨
  q % 109 = 45 ∨ q % 109 = 63 ∨
  q % 113 = 18 ∨ q % 113 = 44 ∨ q % 113 = 69 ∨ q % 113 = 95

private def noTwiceSqMatch (lhs r : ℕ) : Bool :=
  (List.range r).all fun z => lhs != (2 * z ^ 2) % r

open Mathlib.Tactic.Primality in
private def orderObstructionCheck (r m : ℕ) (xs : List ℕ) : Bool :=
  decide (0 < r ∧ 0 < m) &&
  xs.all fun x =>
    powMod x m r == 1 % r &&
    (List.range m).all fun k =>
      (Nat.gcd k m != 1) ||
      noTwiceSqMatch ((powMod x k r + 1) % r) r

private theorem pow_add_one_ne_twice_sq_of_check {q d y r m : ℕ} {xs : List ℕ}
    (hc : orderObstructionCheck r m xs = true) (hx : q % r ∈ xs)
    (hdm : Nat.Coprime d m) :
    q ^ d + 1 ≠ 2 * y ^ 2 := by
  simp only [orderObstructionCheck, noTwiceSqMatch, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, beq_iff_eq, Bool.or_eq_true, bne_iff_ne, List.mem_range] at hc
  obtain ⟨⟨hr, hm⟩, hall⟩ := hc
  obtain ⟨hpow_m, hk_all⟩ := hall (q % r) hx
  have hcycle : q ^ m ≡ 1 [MOD r] := by
    change q ^ m % r = 1 % r
    rw [Nat.pow_mod, ← Mathlib.Tactic.Primality.powMod_def, hpow_m]
  have hobs : ∀ k ∈ Finset.range m, Nat.Coprime k m →
      ∀ z ∈ Finset.range r, ((q % r) ^ k + 1) % r ≠ (2 * z ^ 2) % r := by
    intro k hk hkm z hz
    have hk_lt : k < m := Finset.mem_range.mp hk
    have hz_lt : z < r := Finset.mem_range.mp hz
    rcases hk_all k hk_lt with hne | hz_all
    · exact absurd hkm hne
    · have hneq := hz_all z hz_lt
      rw [Mathlib.Tactic.Primality.powMod_def] at hneq
      have hmod : ((q % r) ^ k % r + 1) % r = ((q % r) ^ k + 1) % r :=
        (Nat.mod_modEq ((q % r) ^ k) r).add_right 1
      exact fun heq => hneq (hmod.trans heq)
  exact pow_add_one_ne_twice_sq_of_order_obstruction hr hm hcycle hdm hobs

private lemma coprime_of_prime_ge_17 {d m : ℕ} (hd : d.Prime) (hd17 : 17 ≤ d)
    (hm0 : 0 < m) (hm16 : m ≤ 16) : Nat.Coprime d m :=
  hd.coprime_iff_not_dvd.mpr fun h => absurd (Nat.le_of_dvd hm0 h) (by omega)

private lemma check_7 : orderObstructionCheck 7 3 [2, 4] = true := by decide +kernel
private lemma check_13 : orderObstructionCheck 13 3 [3, 9] = true := by decide +kernel
private lemma check_17 : orderObstructionCheck 17 4 [4, 13] = true := by decide +kernel
private lemma check_31 : orderObstructionCheck 31 3 [5, 25] = true := by decide +kernel
private lemma check_37 : orderObstructionCheck 37 6 [10, 11, 26, 27] = true := by decide +kernel
private lemma check_41 : orderObstructionCheck 41 5 [10, 16, 18, 37] = true := by decide +kernel
private lemma check_61 : orderObstructionCheck 61 6 [13, 14, 47, 48] = true := by decide +kernel
private lemma check_73 : orderObstructionCheck 73 12 [9, 27, 46, 65] = true := by decide +kernel
private lemma check_79 : orderObstructionCheck 79 3 [23, 55] = true := by decide +kernel
private lemma check_89 : orderObstructionCheck 89 4 [34, 55] = true := by decide +kernel
private lemma check_97 :
    orderObstructionCheck 97 12 [6, 16, 22, 36, 62, 75, 81, 91] = true := by decide +kernel
private lemma check_101 : orderObstructionCheck 101 5 [36, 84, 87, 95] = true := by decide +kernel
private lemma check_103 : orderObstructionCheck 103 3 [46, 56] = true := by decide +kernel
private lemma check_109 : orderObstructionCheck 109 3 [45, 63] = true := by decide +kernel
private lemma check_113 : orderObstructionCheck 113 8 [18, 44, 69, 95] = true := by decide +kernel

/-- Every excluded residue class eliminates `q ^ d + 1 = 2 * y ^ 2` for every
prime exponent `d ≥ 17`. -/
theorem pow_add_one_ne_twice_sq_of_excluded_residue {q d y : ℕ}
    (hd : d.Prime) (hd17 : 17 ≤ d) (hres : ExcludedFermatResidue q) :
    q ^ d + 1 ≠ 2 * y ^ 2 := by
  have h3 : Nat.Coprime d 3 := coprime_of_prime_ge_17 hd hd17 (by decide) (by decide)
  have h4 : Nat.Coprime d 4 := coprime_of_prime_ge_17 hd hd17 (by decide) (by decide)
  have h5 : Nat.Coprime d 5 := coprime_of_prime_ge_17 hd hd17 (by decide) (by decide)
  have h6 : Nat.Coprime d 6 := coprime_of_prime_ge_17 hd hd17 (by decide) (by decide)
  have h8 : Nat.Coprime d 8 := coprime_of_prime_ge_17 hd hd17 (by decide) (by decide)
  have h12 : Nat.Coprime d 12 := coprime_of_prime_ge_17 hd hd17 (by decide) (by decide)
  rcases hres with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact pow_add_one_ne_twice_sq_of_check check_7 (by simp [h]) h3
  · exact pow_add_one_ne_twice_sq_of_check check_7 (by simp [h]) h3
  · exact pow_add_one_ne_twice_sq_of_check check_13 (by simp [h]) h3
  · exact pow_add_one_ne_twice_sq_of_check check_13 (by simp [h]) h3
  · exact pow_add_one_ne_twice_sq_of_check check_17 (by simp [h]) h4
  · exact pow_add_one_ne_twice_sq_of_check check_17 (by simp [h]) h4
  · exact pow_add_one_ne_twice_sq_of_check check_31 (by simp [h]) h3
  · exact pow_add_one_ne_twice_sq_of_check check_31 (by simp [h]) h3
  · exact pow_add_one_ne_twice_sq_of_check check_37 (by simp [h]) h6
  · exact pow_add_one_ne_twice_sq_of_check check_37 (by simp [h]) h6
  · exact pow_add_one_ne_twice_sq_of_check check_37 (by simp [h]) h6
  · exact pow_add_one_ne_twice_sq_of_check check_37 (by simp [h]) h6
  · exact pow_add_one_ne_twice_sq_of_check check_41 (by simp [h]) h5
  · exact pow_add_one_ne_twice_sq_of_check check_41 (by simp [h]) h5
  · exact pow_add_one_ne_twice_sq_of_check check_41 (by simp [h]) h5
  · exact pow_add_one_ne_twice_sq_of_check check_41 (by simp [h]) h5
  · exact pow_add_one_ne_twice_sq_of_check check_61 (by simp [h]) h6
  · exact pow_add_one_ne_twice_sq_of_check check_61 (by simp [h]) h6
  · exact pow_add_one_ne_twice_sq_of_check check_61 (by simp [h]) h6
  · exact pow_add_one_ne_twice_sq_of_check check_61 (by simp [h]) h6
  · exact pow_add_one_ne_twice_sq_of_check check_73 (by simp [h]) h12
  · exact pow_add_one_ne_twice_sq_of_check check_73 (by simp [h]) h12
  · exact pow_add_one_ne_twice_sq_of_check check_73 (by simp [h]) h12
  · exact pow_add_one_ne_twice_sq_of_check check_73 (by simp [h]) h12
  · exact pow_add_one_ne_twice_sq_of_check check_79 (by simp [h]) h3
  · exact pow_add_one_ne_twice_sq_of_check check_79 (by simp [h]) h3
  · exact pow_add_one_ne_twice_sq_of_check check_89 (by simp [h]) h4
  · exact pow_add_one_ne_twice_sq_of_check check_89 (by simp [h]) h4
  · exact pow_add_one_ne_twice_sq_of_check check_97 (by simp [h]) h12
  · exact pow_add_one_ne_twice_sq_of_check check_97 (by simp [h]) h12
  · exact pow_add_one_ne_twice_sq_of_check check_97 (by simp [h]) h12
  · exact pow_add_one_ne_twice_sq_of_check check_97 (by simp [h]) h12
  · exact pow_add_one_ne_twice_sq_of_check check_97 (by simp [h]) h12
  · exact pow_add_one_ne_twice_sq_of_check check_97 (by simp [h]) h12
  · exact pow_add_one_ne_twice_sq_of_check check_97 (by simp [h]) h12
  · exact pow_add_one_ne_twice_sq_of_check check_97 (by simp [h]) h12
  · exact pow_add_one_ne_twice_sq_of_check check_101 (by simp [h]) h5
  · exact pow_add_one_ne_twice_sq_of_check check_101 (by simp [h]) h5
  · exact pow_add_one_ne_twice_sq_of_check check_101 (by simp [h]) h5
  · exact pow_add_one_ne_twice_sq_of_check check_101 (by simp [h]) h5
  · exact pow_add_one_ne_twice_sq_of_check check_103 (by simp [h]) h3
  · exact pow_add_one_ne_twice_sq_of_check check_103 (by simp [h]) h3
  · exact pow_add_one_ne_twice_sq_of_check check_109 (by simp [h]) h3
  · exact pow_add_one_ne_twice_sq_of_check check_109 (by simp [h]) h3
  · exact pow_add_one_ne_twice_sq_of_check check_113 (by simp [h]) h8
  · exact pow_add_one_ne_twice_sq_of_check check_113 (by simp [h]) h8
  · exact pow_add_one_ne_twice_sq_of_check check_113 (by simp [h]) h8
  · exact pow_add_one_ne_twice_sq_of_check check_113 (by simp [h]) h8

/-- Unconditional exclusion of `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`,
`l = 1 ∨ l.Prime`) whenever the Euler prime lies in `ExcludedFermatResidue`. -/
theorem euler_index_ne_prime_mul_square_of_excluded_residue {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l = 1 ∨ l.Prime) (hres : ExcludedFermatResidue q) :
    sigma 1 (m ^ 2) / q ^ a ≠ l * t ^ 2 := by
  intro hi
  rcases hl with rfl | hl
  · apply euler_index_not_square_of_exponent_gt_one hN ho hq hq4 ha4 ha hqm hform
    exact ⟨t, by simpa [pow_two] using hi⟩
  · obtain ⟨hd, hd17, _, _, _, _, y, _, _, hpow⟩ :=
      exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
    exact pow_add_one_ne_twice_sq_of_excluded_residue hd hd17 hres hpow

/-- Unconditional exclusion of odd prime-power component indices
`componentIndex N q = p ^ j` whenever `q` lies in `ExcludedFermatResidue`. -/
theorem componentIndex_ne_odd_prime_power_of_excluded_residue
    {N q p j : ℕ} (ho : Odd N) (hN : N.Perfect) (hqN : q ∈ N.primeFactors)
    (hres : ExcludedFermatResidue q) (hp : p.Prime) (hj : Odd j) :
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
  apply euler_index_ne_prime_mul_square_of_excluded_residue hN ho hq hq4 ha4 ha' hqm hform
    (t := p ^ k) (Or.inr hp) hres
  rw [heq, hk]
  ring

/-- Mod-3 and `73`-floor dichotomy on `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2`
with `a > 1` and `l.Prime`: either `3 ∣ w` (forcing `q % 3 = 2`, `3 ∣ m`, and
`3 ∣ N`), or `¬ 3 ∣ w` (forcing `q % 48 = 1`, `d % 24 = 1`, `73 ≤ d`, and
`145 ≤ a`). -/
theorem exceptional_euler_mod_three_and_seventy_three_dichotomy {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    (q % 3 = 2 ∧ 3 ∣ m ∧ 3 ∣ N) ∨
      (q % 48 = 1 ∧ d % 24 = 1 ∧ 73 ≤ d ∧ 145 ≤ a) := by
  intro d
  obtain ⟨hd, hd17, hd8, hq16, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨w, y, v, hq1, _, _, hm_eq, _, hdwy, _, _, _⟩ :=
    exceptional_index_cofactor_factorization hN ho hq hq4 ha4 ha hqm hform hl hi
  change d.Prime at hd
  change 17 ≤ d at hd17
  change d % 8 = 1 at hd8
  change q + 1 = 2 * d * w ^ 2 at hq1
  change d * w ∣ y at hdwy
  have hwm : w ∣ m :=
    (dvd_mul_left w d).trans (hdwy.trans ⟨l * v * t, by rw [hm_eq]; ring⟩)
  have hmN : m ∣ N :=
    (dvd_pow_self m (by decide : 2 ≠ 0)).trans (hform ▸ dvd_mul_left _ _)
  by_cases hw3 : 3 ∣ w
  · have hq3_dvd : 3 ∣ q + 1 := by
      rw [hq1]
      exact (dvd_pow hw3 (by decide : 2 ≠ 0)).trans (dvd_mul_left _ _)
    have hq3 : q % 3 = 2 := by omega
    exact Or.inl ⟨hq3, hw3.trans hwm, (hw3.trans hwm).trans hmN⟩
  · have hq_ne3 : q ≠ 3 := by
      intro h
      subst h
      omega
    have hq_not_dvd3 : ¬ 3 ∣ q := fun h => by
      rcases hq.eq_one_or_self_of_dvd 3 h with h1 | h3 <;> omega
    have hd_not_dvd3 : ¬ 3 ∣ d := fun h => by
      rcases hd.eq_one_or_self_of_dvd 3 h with h1 | h3 <;> omega
    have hq1_not_dvd3 : ¬ 3 ∣ q + 1 := by
      rw [hq1, mul_assoc]
      intro h
      have hp3 : Nat.Prime 3 := by decide
      rcases hp3.dvd_mul.mp h with h2 | hdw
      · omega
      · rcases hp3.dvd_mul.mp hdw with hd3 | hw2
        · exact hd_not_dvd3 hd3
        · exact hw3 (hp3.dvd_of_dvd_pow hw2)
    have hq3 : q % 3 = 1 := by
      have hq0 : q % 3 ≠ 0 := fun h => hq_not_dvd3 (Nat.dvd_of_mod_eq_zero h)
      have hq1_0 : (q + 1) % 3 ≠ 0 := fun h => hq1_not_dvd3 (Nat.dvd_of_mod_eq_zero h)
      omega
    have hw_mod3 : w % 3 = 1 ∨ w % 3 = 2 := by
      have hw0 : w % 3 ≠ 0 := fun h => hw3 (Nat.dvd_of_mod_eq_zero h)
      omega
    have hw2_mod3 : w ^ 2 % 3 = 1 := by
      rw [pow_two, Nat.mul_mod]
      rcases hw_mod3 with h | h <;> rw [h]
    have hd_mod3 : d % 3 = 1 := by
      have hd_cases : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
      have hmod : (2 * d * w ^ 2) % 3 = 2 := by rw [← hq1]; omega
      rw [mul_assoc, Nat.mul_mod, Nat.mul_mod d (w ^ 2) 3, hw2_mod3] at hmod
      rcases hd_cases with h | h | h
      · rw [h] at hmod
        exact absurd hmod (by decide)
      · exact h
      · rw [h] at hmod
        exact absurd hmod (by decide)
    have hq16_dvd : 16 ∣ q - 1 := Nat.dvd_of_mod_eq_zero (by have := hq.one_lt; omega)
    have hq3_dvd : 3 ∣ q - 1 := Nat.dvd_of_mod_eq_zero (by have := hq.one_lt; omega)
    obtain ⟨kq, hkq⟩ := (by decide : Nat.Coprime 16 3).mul_dvd_of_dvd_of_dvd hq16_dvd hq3_dvd
    have hq48 : q % 48 = 1 := by
      have := hq.one_lt
      omega
    have hd8_dvd : 8 ∣ d - 1 := Nat.dvd_of_mod_eq_zero (by omega)
    have hd3_dvd : 3 ∣ d - 1 := Nat.dvd_of_mod_eq_zero (by omega)
    obtain ⟨kd, hkd⟩ := (by decide : Nat.Coprime 8 3).mul_dvd_of_dvd_of_dvd hd8_dvd hd3_dvd
    have hd24 : d % 24 = 1 := by omega
    have hd73 : 73 ≤ d := by
      by_contra! hd_lt
      have hcases : d = 25 ∨ d = 49 := by omega
      rcases hcases with h25 | h49
      · rw [h25] at hd
        exact (by decide : ¬ Nat.Prime 25) hd
      · rw [h49] at hd
        exact (by decide : ¬ Nat.Prime 49) hd
    have ha145 : 145 ≤ a := by
      dsimp [d] at hd73
      omega
    exact Or.inr ⟨hq48, hd24, hd73, ha145⟩

/-- Divisibility-by-`3` dichotomy on `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` with
`a > 1` and `l.Prime`: either `3 ∣ N ∧ 3 ∣ m`, or `¬ 3 ∣ N` together with
`q % 48 = 1`, `d % 24 = 1`, `73 ≤ d`, and `145 ≤ a`. -/
theorem exceptional_euler_three_dvd_dichotomy {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    (3 ∣ N ∧ 3 ∣ m) ∨
      (¬ 3 ∣ N ∧ q % 48 = 1 ∧ d % 24 = 1 ∧ 73 ≤ d ∧ 145 ≤ a) := by
  intro d
  by_cases hN3 : 3 ∣ N
  · have hq_ne3 : q ≠ 3 := by
      intro h
      subst h
      omega
    have hq_not3 : ¬ 3 ∣ q := fun h => by
      rcases hq.eq_one_or_self_of_dvd 3 h with h1 | h3 <;> omega
    have hp3 : Nat.Prime 3 := by decide
    have hm2 : 3 ∣ m ^ 2 := by
      rw [hform] at hN3
      exact (hp3.dvd_mul.mp hN3).resolve_left fun h => hq_not3 (hp3.dvd_of_dvd_pow h)
    exact Or.inl ⟨hN3, hp3.dvd_of_dvd_pow hm2⟩
  · rcases exceptional_euler_mod_three_and_seventy_three_dichotomy
        hN ho hq hq4 ha4 ha hqm hform hl hi with ⟨_, _, h3N⟩ | hmain
    · exact absurd h3N hN3
    · exact Or.inr ⟨hN3, hmain⟩

/-- When `¬ 3 ∣ N` on `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`),
we unconditionally obtain `q % 48 = 1`, `d % 24 = 1`, `73 ≤ d`, and `145 ≤ a`. -/
theorem exceptional_euler_of_not_three_dvd {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2)
    (hN3 : ¬ 3 ∣ N) :
    let d := (a + 1) / 2
    q % 48 = 1 ∧ d % 24 = 1 ∧ 73 ≤ d ∧ 145 ≤ a := by
  rcases exceptional_euler_three_dvd_dichotomy hN ho hq hq4 ha4 ha hqm hform hl hi with
    ⟨h3N, _⟩ | ⟨_, hmain⟩
  · exact absurd h3N hN3
  · exact hmain

end OddPerfect
