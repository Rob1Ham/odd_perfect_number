module

public import OddPerfect.ZelinskyFullSlope
public import OddPerfect.PrimeFive
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Zelinsky Collision Discharge & Unconditional 409/149 Multi-Block Slope

1. **Cross-degree `Φ₃` / `Φ₅` resultant-1 Bézout identity & root disjointness**:
   `(x^3 + 1)(x^2 + x + 1) = x(x^4 + x^3 + x^2 + x + 1) + 1`, yielding coprimality of
   `normalizedSquareSum x` and `normalizedQuarticSum x`, disjointness of their root sets
   modulo any prime `w`, and the combined root-slot cap `≤ 5` (`1 + 4`) for `w ≡ 1 [MOD 3]`,
   `w ≠ 5`.
2. **Zelinsky (2021) quadratic common-divisor collision bounds**:
   - `5 * p ≤ a + b + 1` for distinct odd `a, b ≡ 2 [MOD 3]` sharing a prime divisor `p ≡ 1 [MOD 3]`,
     and uniqueness in the `[0, ⌊5w/2⌋)` window (`card_twoModThree_five_halves_window_le_one`).
   - `3 * p ≤ a + b + 1` for distinct odd `a, b ≡ 1 [MOD 3]` sharing a prime divisor `p ≡ 1 [MOD 3]`.
   - Exact equality `p = a + b + 1` in the cross-mod-3 semiprime collision
     `a^2 + a + 1 = 3 * p * e`, `b^2 + b + 1 = p * f` (`e, f < p`).
3. **Cross-chain `Φ₃(Φ₅(v))` cofactor collision discharge**:
   Exclusion of `v^2 - v + 1 = u^2 + u + 1` for odd `v ≥ 3`, odd `u`; absence of odd roots
   `< v^2 - v + 1` when `v^2 - v + 1` is prime; and exclusion of prime `normalizedSquareSum w`
   when `w = normalizedQuarticSum v` is prime and `w ∈ squareSourcesTwo N`.
4. **Combined valuation budget, exponent-2 capped quartic incidence, and `5`-unconditional
   `409/149` multi-block slope**:
   Eliminates the `¬ 5 ∣ N` hypothesis from `multi_block_coupled_three_five_free` via
   `(37, 7, 98)` weights and exponent-2 capping at `S₅₁ := (squareSources N).filter (· % 5 = 1)`.
5. **Zelinsky (2021) `302/113` and `66/25` density/slack reductions**:
   Derives `302 * ω(N) ≤ 113 * Ω(N) + 286` from an `S₅₁` density cap or from
   `|twoModThreeLargeSources N q| ≥ (2 * ω(N) - 67) / 452` (when `¬ 3 ∣ N`), and derives
   `66 * ω(N) ≤ 25 * Ω(N) + 125` from `|twoModThreeLargeSources N q| ≥ (3 * ω(N) - 25) / 275`.
-/

public section

namespace OddPerfect

open ArithmeticFunction

/-! ## 1. Cross-Degree `Φ₃` / `Φ₅` Resultant-1 Bézout Identity & Root Disjointness -/

/-- Explicit resultant-1 Bézout identity linking `Φ₃(x)` and `Φ₅(x)`:
`(x ^ 3 + 1) * (x ^ 2 + x + 1) = x * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) + 1`. -/
theorem bezout_phi3_phi5 (x : ℕ) :
    (x ^ 3 + 1) * (x ^ 2 + x + 1) = x * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) + 1 := by
  ring

/-- For every `x : ℕ`, `x ^ 2 + x + 1` and `x ^ 4 + x ^ 3 + x ^ 2 + x + 1` are coprime. -/
theorem coprime_sq_add_self_add_one_phi5 (x : ℕ) :
    Nat.Coprime (x ^ 2 + x + 1) (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) := by
  apply Nat.coprime_of_dvd
  intro p hp hd3 hd5
  have hmul3 : p ∣ (x ^ 3 + 1) * (x ^ 2 + x + 1) := hd3.mul_left _
  have hmul5 : p ∣ x * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) := hd5.mul_left _
  rw [bezout_phi3_phi5 x] at hmul3
  exact hp.not_dvd_one ((Nat.dvd_add_right hmul5).mp hmul3)

private lemma normalizedSquareSum_dvd_sq_add_self_add_one_cd (x : ℕ) :
    normalizedSquareSum x ∣ x ^ 2 + x + 1 := by
  by_cases hx : x % 3 = 1
  · obtain ⟨k, rfl⟩ : ∃ k, x = 3 * k + 1 := ⟨x / 3, by omega⟩
    have hnorm : normalizedSquareSum (3 * k + 1) = 3 * k ^ 2 + 3 * k + 1 := by
      rw [normalizedSquareSum, ite_eq_left (show (3 * k + 1) % 3 = 1 by omega)]
      rw [show (3 * k + 1) ^ 2 + (3 * k + 1) + 1 = 3 * (3 * k ^ 2 + 3 * k + 1) by ring]
      simp
    rw [hnorm]
    exact ⟨3, by ring⟩
  · simp [normalizedSquareSum, hx]

private lemma normalizedQuarticSum_dvd_phi5_cd (x : ℕ) :
    normalizedQuarticSum x ∣ x ^ 4 + x ^ 3 + x ^ 2 + x + 1 := by
  by_cases hx : x % 5 = 1
  · obtain ⟨k, rfl⟩ : ∃ k, x = 5 * k + 1 := ⟨x / 5, by omega⟩
    have hnorm : normalizedQuarticSum (5 * k + 1) =
        125 * k ^ 4 + 125 * k ^ 3 + 50 * k ^ 2 + 10 * k + 1 := by
      rw [normalizedQuarticSum, ite_eq_left (show (5 * k + 1) % 5 = 1 by omega)]
      rw [show (5 * k + 1) ^ 4 + (5 * k + 1) ^ 3 + (5 * k + 1) ^ 2 + (5 * k + 1) + 1 =
          5 * (125 * k ^ 4 + 125 * k ^ 3 + 50 * k ^ 2 + 10 * k + 1) by ring]
      simp
    rw [hnorm]
    exact ⟨5, by ring⟩
  · simp [normalizedQuarticSum, hx]

/-- `normalizedSquareSum x` and `normalizedQuarticSum x` are coprime for every `x : ℕ`. -/
theorem coprime_normalizedSquareSum_normalizedQuarticSum (x : ℕ) :
    Nat.Coprime (normalizedSquareSum x) (normalizedQuarticSum x) :=
  ((coprime_sq_add_self_add_one_phi5 x).coprime_dvd_left
    (normalizedSquareSum_dvd_sq_add_self_add_one_cd x)).coprime_dvd_right
    (normalizedQuarticSum_dvd_phi5_cd x)

/-- Modulo any prime `w`, the root sets of `normalizedSquareSum` and `normalizedQuarticSum`
in `Finset.range w` are disjoint. -/
theorem disjoint_roots_phi3_phi5_range {w : ℕ} (hw : w.Prime) :
    Disjoint ((Finset.range w).filter (fun x => w ∣ normalizedSquareSum x))
      ((Finset.range w).filter (fun x => w ∣ normalizedQuarticSum x)) := by
  rw [Finset.disjoint_left]
  intro x hx3 hx5
  have hd3 := (Finset.mem_filter.mp hx3).2
  have hd5 := (Finset.mem_filter.mp hx5).2
  have hcop := coprime_normalizedSquareSum_normalizedQuarticSum x
  exact hw.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hd3 hd5)

/-- For any prime `w ≠ 5` with `w ≡ 1 [MOD 3]`, the combined set of `2 [MOD 3]` quadratic roots
and quintic roots in `Finset.range w` has cardinality at most `5`. -/
theorem card_range_dvd_square_or_quartic_le {w : ℕ} (hw : w.Prime) (hw5 : w ≠ 5)
    (hw1 : w % 3 = 1) :
    (((Finset.range w).filter (fun x => x % 3 = 2 ∧ w ∣ x ^ 2 + x + 1)) ∪
        ((Finset.range w).filter (fun x => w ∣ geometricBlock x 5))).card ≤ 5 := by
  calc
    (((Finset.range w).filter (fun x => x % 3 = 2 ∧ w ∣ x ^ 2 + x + 1)) ∪
        ((Finset.range w).filter (fun x => w ∣ geometricBlock x 5))).card
      ≤ ((Finset.range w).filter (fun x => x % 3 = 2 ∧ w ∣ x ^ 2 + x + 1)).card +
          ((Finset.range w).filter (fun x => w ∣ geometricBlock x 5)).card := Finset.card_union_le _ _
    _ ≤ 1 + (5 - 1) := Nat.add_le_add
        (card_twoModThree_dvd_sq_add_self_add_one_le_one hw hw1)
        (card_range_dvd_geometricBlock_le_pred (by decide : Nat.Prime 5) hw hw5)
    _ = 5 := by decide

/-! ## 2. Zelinsky's (2021) Quadratic Common-Divisor Collision Lemmas -/

private lemma zelinsky_twoModThree_common_divisor_le_of_lt {a b p : ℕ}
    (ha_odd : Odd a) (hb_odd : Odd b) (hba : b < a)
    (ha3 : a % 3 = 2) (hb3 : b % 3 = 2)
    (hp : p.Prime) (hp3 : p % 3 = 1)
    (hda : p ∣ a ^ 2 + a + 1) (hdb : p ∣ b ^ 2 + b + 1) :
    5 * p ≤ a + b + 1 := by
  have hp_ne2 : p ≠ 2 := by omega
  have hp_mod2 : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp_ne2)
  have ha_mod2 : a % 2 = 1 := Nat.odd_iff.mp ha_odd
  have hb_mod2 : b % 2 = 1 := Nat.odd_iff.mp hb_odd
  have : Fact p.Prime := ⟨hp⟩
  have ha_z : (a : ZMod p) ^ 2 + (a : ZMod p) + 1 = 0 := by
    have h0 := (ZMod.natCast_eq_zero_iff (a ^ 2 + a + 1) p).mpr hda
    push_cast at h0
    exact h0
  have hb_z : (b : ZMod p) ^ 2 + (b : ZMod p) + 1 = 0 := by
    have h0 := (ZMod.natCast_eq_zero_iff (b ^ 2 + b + 1) p).mpr hdb
    push_cast at h0
    exact h0
  have hprod : ((a : ZMod p) - (b : ZMod p)) * ((a : ZMod p) + (b : ZMod p) + 1) = 0 := by
    calc
      ((a : ZMod p) - (b : ZMod p)) * ((a : ZMod p) + (b : ZMod p) + 1)
          = ((a : ZMod p) ^ 2 + (a : ZMod p) + 1) - ((b : ZMod p) ^ 2 + (b : ZMod p) + 1) := by
              ring
      _ = 0 - 0 := by rw [ha_z, hb_z]
      _ = 0 := sub_zero 0
  by_cases hdiv : p ∣ a - b
  · obtain ⟨k, hk⟩ := hdiv
    have hpk_pos : 0 < p * k := by omega
    have hk_pos : 0 < k := Nat.pos_of_mul_pos_left hpk_pos
    have hk2 : k % 2 = 0 := by
      have h1 : (p * k) % 2 = (a - b) % 2 := congrArg (· % 2) hk.symm
      rw [Nat.mul_mod, hp_mod2, Nat.one_mul, Nat.mod_mod] at h1
      omega
    have hk3 : k % 3 = 0 := by
      have h1 : (p * k) % 3 = (a - b) % 3 := congrArg (· % 3) hk.symm
      rw [Nat.mul_mod, hp3, Nat.one_mul, Nat.mod_mod] at h1
      omega
    have hk6 : 6 ≤ k := by omega
    have h6p : 6 * p ≤ a - b := by nlinarith
    omega
  · have hne_z : (a : ZMod p) - (b : ZMod p) ≠ 0 := by
      intro hsub
      apply hdiv
      apply (ZMod.natCast_eq_zero_iff (a - b) p).mp
      rw [Nat.cast_sub hba.le]
      exact hsub
    have hsum_z : (a : ZMod p) + (b : ZMod p) + 1 = 0 :=
      (mul_eq_zero.mp hprod).resolve_left hne_z
    have hdvd : p ∣ a + b + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      exact hsum_z
    obtain ⟨m, hm⟩ := hdvd
    have hm2 : m % 2 = 1 := by
      have h1 : (p * m) % 2 = (a + b + 1) % 2 := congrArg (· % 2) hm.symm
      rw [Nat.mul_mod, hp_mod2, Nat.one_mul, Nat.mod_mod] at h1
      omega
    have hm3 : m % 3 = 2 := by
      have h1 : (p * m) % 3 = (a + b + 1) % 3 := congrArg (· % 3) hm.symm
      rw [Nat.mul_mod, hp3, Nat.one_mul, Nat.mod_mod] at h1
      omega
    have hm5 : 5 ≤ m := by omega
    nlinarith

/-- **Zelinsky's (2021) `2 [MOD 3]` common-divisor collision bound**:
Distinct odd integers `a, b ≡ 2 [MOD 3]` whose quadratic sums `x^2 + x + 1` share a prime factor
`p ≡ 1 [MOD 3]` satisfy `5 * p ≤ a + b + 1`. -/
theorem zelinsky_twoModThree_common_divisor_le {a b p : ℕ}
    (ha_odd : Odd a) (hb_odd : Odd b) (hab : a ≠ b)
    (ha3 : a % 3 = 2) (hb3 : b % 3 = 2)
    (hp : p.Prime) (hp3 : p % 3 = 1)
    (hda : p ∣ a ^ 2 + a + 1) (hdb : p ∣ b ^ 2 + b + 1) :
    5 * p ≤ a + b + 1 := by
  rcases lt_or_gt_of_ne hab with hab_lt | hba_lt
  · have h := zelinsky_twoModThree_common_divisor_le_of_lt hb_odd ha_odd hab_lt hb3 ha3
      hp hp3 hdb hda
    omega
  · exact zelinsky_twoModThree_common_divisor_le_of_lt ha_odd hb_odd hba_lt ha3 hb3
      hp hp3 hda hdb

/-- For any prime `w ≡ 1 [MOD 3]`, there is at most one odd `x < ⌊5 * w / 2⌋` with `x ≡ 2 [MOD 3]`
and `w ∣ x^2 + x + 1`. -/
theorem card_twoModThree_five_halves_window_le_one {w : ℕ} (hw : w.Prime) (hw1 : w % 3 = 1) :
    ((Finset.range ((5 * w) / 2)).filter
      (fun x => Odd x ∧ x % 3 = 2 ∧ w ∣ x ^ 2 + x + 1)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hab
  have ha_m := Finset.mem_filter.mp ha
  have hb_m := Finset.mem_filter.mp hb
  have ha_lt : a < (5 * w) / 2 := Finset.mem_range.mp ha_m.1
  have hb_lt : b < (5 * w) / 2 := Finset.mem_range.mp hb_m.1
  have hle := zelinsky_twoModThree_common_divisor_le ha_m.2.1 hb_m.2.1 hab
    ha_m.2.2.1 hb_m.2.2.1 hw hw1 ha_m.2.2.2 hb_m.2.2.2
  omega

private lemma zelinsky_oneModThree_common_divisor_le_of_lt {a b p : ℕ}
    (ha_odd : Odd a) (hb_odd : Odd b) (hba : b < a)
    (ha3 : a % 3 = 1) (hb3 : b % 3 = 1)
    (hp : p.Prime) (hp3 : p % 3 = 1)
    (hda : p ∣ a ^ 2 + a + 1) (hdb : p ∣ b ^ 2 + b + 1) :
    3 * p ≤ a + b + 1 := by
  have hp_ne2 : p ≠ 2 := by omega
  have hp_mod2 : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp_ne2)
  have ha_mod2 : a % 2 = 1 := Nat.odd_iff.mp ha_odd
  have hb_mod2 : b % 2 = 1 := Nat.odd_iff.mp hb_odd
  have : Fact p.Prime := ⟨hp⟩
  have ha_z : (a : ZMod p) ^ 2 + (a : ZMod p) + 1 = 0 := by
    have h0 := (ZMod.natCast_eq_zero_iff (a ^ 2 + a + 1) p).mpr hda
    push_cast at h0
    exact h0
  have hb_z : (b : ZMod p) ^ 2 + (b : ZMod p) + 1 = 0 := by
    have h0 := (ZMod.natCast_eq_zero_iff (b ^ 2 + b + 1) p).mpr hdb
    push_cast at h0
    exact h0
  have hprod : ((a : ZMod p) - (b : ZMod p)) * ((a : ZMod p) + (b : ZMod p) + 1) = 0 := by
    calc
      ((a : ZMod p) - (b : ZMod p)) * ((a : ZMod p) + (b : ZMod p) + 1)
          = ((a : ZMod p) ^ 2 + (a : ZMod p) + 1) - ((b : ZMod p) ^ 2 + (b : ZMod p) + 1) := by
              ring
      _ = 0 - 0 := by rw [ha_z, hb_z]
      _ = 0 := sub_zero 0
  by_cases hdiv : p ∣ a - b
  · obtain ⟨k, hk⟩ := hdiv
    have hpk_pos : 0 < p * k := by omega
    have hk_pos : 0 < k := Nat.pos_of_mul_pos_left hpk_pos
    have hk2 : k % 2 = 0 := by
      have h1 : (p * k) % 2 = (a - b) % 2 := congrArg (· % 2) hk.symm
      rw [Nat.mul_mod, hp_mod2, Nat.one_mul, Nat.mod_mod] at h1
      omega
    have hk3 : k % 3 = 0 := by
      have h1 : (p * k) % 3 = (a - b) % 3 := congrArg (· % 3) hk.symm
      rw [Nat.mul_mod, hp3, Nat.one_mul, Nat.mod_mod] at h1
      omega
    have hk6 : 6 ≤ k := by omega
    have h6p : 6 * p ≤ a - b := by nlinarith
    omega
  · have hne_z : (a : ZMod p) - (b : ZMod p) ≠ 0 := by
      intro hsub
      apply hdiv
      apply (ZMod.natCast_eq_zero_iff (a - b) p).mp
      rw [Nat.cast_sub hba.le]
      exact hsub
    have hsum_z : (a : ZMod p) + (b : ZMod p) + 1 = 0 :=
      (mul_eq_zero.mp hprod).resolve_left hne_z
    have hdvd : p ∣ a + b + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      exact hsum_z
    obtain ⟨m, hm⟩ := hdvd
    have hpm_pos : 0 < p * m := by omega
    have hm_pos : 0 < m := Nat.pos_of_mul_pos_left hpm_pos
    have hm3 : m % 3 = 0 := by
      have h1 : (p * m) % 3 = (a + b + 1) % 3 := congrArg (· % 3) hm.symm
      rw [Nat.mul_mod, hp3, Nat.one_mul, Nat.mod_mod] at h1
      omega
    have hm3_ge : 3 ≤ m := by omega
    nlinarith

/-- **Zelinsky's (2021) `1 [MOD 3]` common-divisor collision bound**:
Distinct odd integers `a, b ≡ 1 [MOD 3]` whose quadratic sums `x^2 + x + 1` share a prime factor
`p ≡ 1 [MOD 3]` satisfy `3 * p ≤ a + b + 1`. -/
theorem zelinsky_oneModThree_common_divisor_le {a b p : ℕ}
    (ha_odd : Odd a) (hb_odd : Odd b) (hab : a ≠ b)
    (ha3 : a % 3 = 1) (hb3 : b % 3 = 1)
    (hp : p.Prime) (hp3 : p % 3 = 1)
    (hda : p ∣ a ^ 2 + a + 1) (hdb : p ∣ b ^ 2 + b + 1) :
    3 * p ≤ a + b + 1 := by
  rcases lt_or_gt_of_ne hab with hab_lt | hba_lt
  · have h := zelinsky_oneModThree_common_divisor_le_of_lt hb_odd ha_odd hab_lt hb3 ha3
      hp hp3 hdb hda
    omega
  · exact zelinsky_oneModThree_common_divisor_le_of_lt ha_odd hb_odd hba_lt ha3 hb3
      hp hp3 hda hdb

/-- **Cross-mod-3 semiprime collision identity**:
If odd `a ≡ 1 [MOD 3]` and odd `b ≡ 2 [MOD 3]` satisfy `a^2 + a + 1 = 3 * p * e` and
`b^2 + b + 1 = p * f` with `0 < e, f < p` for a prime `p ≡ 1 [MOD 3]`, then `p = a + b + 1`. -/
theorem zelinsky_cross_mod_three_semiprime_eq {a b p e f : ℕ}
    (ha_odd : Odd a) (hb_odd : Odd b) (ha3 : a % 3 = 1) (hb3 : b % 3 = 2)
    (hp : p.Prime) (hp3 : p % 3 = 1) (he : 0 < e) (_hf : 0 < f)
    (hep : e < p) (hfp : f < p)
    (ha_eq : a ^ 2 + a + 1 = 3 * p * e) (hb_eq : b ^ 2 + b + 1 = p * f) :
    p = a + b + 1 := by
  have hp_ne2 : p ≠ 2 := by omega
  have hp_mod2 : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp_ne2)
  have ha_mod2 : a % 2 = 1 := Nat.odd_iff.mp ha_odd
  have hb_mod2 : b % 2 = 1 := Nat.odd_iff.mp hb_odd
  have hb_lt : b < p := by
    have hpf : p * f < p * p := Nat.mul_lt_mul_of_pos_left hfp hp.pos
    have hb2 : b ^ 2 < p ^ 2 := by nlinarith
    by_contra! hle
    have := Nat.pow_le_pow_left hle 2
    omega
  have ha_lt : a < 2 * p := by
    have hpe : 3 * p * e < 3 * p * p := by nlinarith
    have ha2 : a ^ 2 < (2 * p) ^ 2 := by nlinarith [hp.pos]
    by_contra! hle
    have := Nat.pow_le_pow_left hle 2
    nlinarith
  have hda : p ∣ a ^ 2 + a + 1 := ⟨3 * e, by rw [ha_eq]; ring⟩
  have hdb : p ∣ b ^ 2 + b + 1 := ⟨f, hb_eq⟩
  have : Fact p.Prime := ⟨hp⟩
  have ha_z : (a : ZMod p) ^ 2 + (a : ZMod p) + 1 = 0 := by
    have h0 := (ZMod.natCast_eq_zero_iff (a ^ 2 + a + 1) p).mpr hda
    push_cast at h0
    exact h0
  have hb_z : (b : ZMod p) ^ 2 + (b : ZMod p) + 1 = 0 := by
    have h0 := (ZMod.natCast_eq_zero_iff (b ^ 2 + b + 1) p).mpr hdb
    push_cast at h0
    exact h0
  have hprod : ((a : ZMod p) - (b : ZMod p)) * ((a : ZMod p) + (b : ZMod p) + 1) = 0 := by
    calc
      ((a : ZMod p) - (b : ZMod p)) * ((a : ZMod p) + (b : ZMod p) + 1)
          = ((a : ZMod p) ^ 2 + (a : ZMod p) + 1) - ((b : ZMod p) ^ 2 + (b : ZMod p) + 1) := by
              ring
      _ = 0 - 0 := by rw [ha_z, hb_z]
      _ = 0 := sub_zero 0
  have hne_z : (a : ZMod p) - (b : ZMod p) ≠ 0 := by
    intro hsub
    have heq_z : (a : ZMod p) = (b : ZMod p) := sub_eq_zero.mp hsub
    have hab : a ≠ b := by omega
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · have hd : p ∣ b - a := by
        apply (ZMod.natCast_eq_zero_iff (b - a) p).mp
        rw [Nat.cast_sub hlt.le, sub_eq_zero]
        exact heq_z.symm
      have hle := Nat.le_of_dvd (by omega) hd
      omega
    · have hd : p ∣ a - b := by
        apply (ZMod.natCast_eq_zero_iff (a - b) p).mp
        rw [Nat.cast_sub hlt.le, sub_eq_zero]
        exact heq_z
      obtain ⟨k, hk⟩ := hd
      have hk_pos : 0 < k := Nat.pos_of_mul_pos_left (by omega : 0 < p * k)
      have hk_lt2 : k < 2 := by
        by_contra! hk2
        have : 2 * p ≤ p * k := by nlinarith
        omega
      have hk1 : k = 1 := by omega
      rw [hk1, mul_one] at hk
      omega
  have hsum_z : (a : ZMod p) + (b : ZMod p) + 1 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left hne_z
  have hdvd : p ∣ a + b + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    exact hsum_z
  obtain ⟨m, hm⟩ := hdvd
  have hm_lt3 : m < 3 := by
    by_contra! hm3
    have : 3 * p ≤ p * m := by nlinarith
    omega
  have hm2 : m % 2 = 1 := by
    have h1 : (p * m) % 2 = (a + b + 1) % 2 := congrArg (· % 2) hm.symm
    rw [Nat.mul_mod, hp_mod2, Nat.one_mul, Nat.mod_mod] at h1
    omega
  have hm1 : m = 1 := by omega
  rw [hm1, mul_one] at hm
  exact hm.symm

/-! ## 3. Cross-Chain `Φ₃(Φ₅(v))` Cofactor Collision Discharge -/

/-- For odd `v ≥ 3` and odd `u`, `v ^ 2 - v + 1 ≠ u ^ 2 + u + 1`. -/
theorem phi5_sub_quad_ne_sq_add_self_add_one {v u : ℕ} (hv : Odd v) (hu : Odd u) (hv3 : 3 ≤ v) :
    v ^ 2 - v + 1 ≠ u ^ 2 + u + 1 := by
  intro heq
  have h1 : v ^ 2 - v + 1 = (v - 1) ^ 2 + (v - 1) + 1 := by
    zify [show 1 ≤ v by omega, show v ≤ v ^ 2 by nlinarith]
    ring
  rw [h1] at heq
  have hmono : StrictMono (fun x : ℕ => x ^ 2 + x + 1) := by
    intro a b hab
    have hsq : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hab.le 2
    dsimp
    omega
  have hvu : v - 1 = u := hmono.injective heq
  have hv2 := Nat.odd_iff.mp hv
  have hu2 := Nat.odd_iff.mp hu
  omega

/-- When `v ≥ 3` is odd and `w = v^2 - v + 1` is prime, the only roots of `x^2 + x + 1 ≡ 0 [MOD w]`
in `Finset.range w` are the even integers `v - 1` and `(v - 1)^2`, so no odd `x < w` satisfies
`w ∣ x^2 + x + 1`. -/
theorem phi5_sub_quad_prime_no_odd_roots_lt {v : ℕ} (hv : Odd v) (hv3 : 3 ≤ v)
    (hw : (v ^ 2 - v + 1).Prime) :
    ((Finset.range (v ^ 2 - v + 1)).filter
      (fun x => Odd x ∧ (v ^ 2 - v + 1) ∣ x ^ 2 + x + 1)) = ∅ := by
  let w := v ^ 2 - v + 1
  let r₁ := v - 1
  let r₂ := (v - 1) ^ 2
  have hv1 : 1 ≤ v := by omega
  have hv_sq : v ≤ v ^ 2 := by nlinarith
  have hr1_ge2 : 2 ≤ r₁ := by omega
  have hr1_lt_r2 : r₁ < r₂ := by
    dsimp [r₁, r₂]
    nlinarith
  have hr2_add_v : r₂ + v = w := by
    dsimp [r₂, w]
    zify [hv1, hv_sq]
    ring
  have hr2_lt_w : r₂ < w := by omega
  have hr1_lt_w : r₁ < w := hr1_lt_r2.trans hr2_lt_w
  have hdvd1 : w ∣ r₁ ^ 2 + r₁ + 1 := by
    have heq1 : r₁ ^ 2 + r₁ + 1 = w := by
      dsimp [r₁, w]
      zify [hv1, hv_sq]
      ring
    rw [heq1]
  have hdvd2 : w ∣ r₂ ^ 2 + r₂ + 1 := by
    refine ⟨r₁ ^ 2 - r₁ + 1, ?_⟩
    have hr1_sq : v - 1 ≤ (v - 1) ^ 2 := by nlinarith
    dsimp [r₁, r₂, w]
    zify [hv1, hv_sq, hr1_sq]
    ring
  have hsub : ({r₁, r₂} : Finset ℕ) ⊆ (Finset.range w).filter (fun x => w ∣ x ^ 2 + x + 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr1_lt_w, hdvd1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr2_lt_w, hdvd2⟩
  have hcard2 : ({r₁, r₂} : Finset ℕ).card = 2 := Finset.card_pair hr1_lt_r2.ne
  have heq : ({r₁, r₂} : Finset ℕ) = (Finset.range w).filter (fun x => w ∣ x ^ 2 + x + 1) :=
    Finset.eq_of_subset_of_card_le hsub ((card_range_dvd_sq_add_self_add_one_le_two hw).trans hcard2.ge)
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨hx_range, hx_odd, hx_dvd⟩ := Finset.mem_filter.mp hx
  have hx_mem : x ∈ (Finset.range w).filter (fun y => w ∣ y ^ 2 + y + 1) :=
    Finset.mem_filter.mpr ⟨hx_range, hx_dvd⟩
  rw [← heq] at hx_mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx_mem
  have hv2 := Nat.odd_iff.mp hv
  have hx2 := Nat.odd_iff.mp hx_odd
  rcases hx_mem with rfl | rfl
  · omega
  · have hr2_even : ((v - 1) ^ 2) % 2 = 0 := by
      have hv_sub_mod : (v - 1) % 2 = 0 := by omega
      simp [pow_two, Nat.mul_mod, hv_sub_mod]
    omega

/-- If `w = normalizedQuarticSum v` is prime for a prime `v ≥ 3` with `v % 5 ≠ 1` and
`w ∈ squareSourcesTwo N`, then `normalizedSquareSum w` is composite and congruent to `3 [MOD 4]`. -/
theorem quartic_prime_target_disjoint_squareSourcesTwo_prime {N v : ℕ}
    (hv_prime : v.Prime) (hv3 : 3 ≤ v) (hv_mod5 : v % 5 ≠ 1)
    (hw : (normalizedQuarticSum v).Prime)
    (hw_mem : normalizedQuarticSum v ∈ squareSourcesTwo N) :
    ¬ (normalizedSquareSum (normalizedQuarticSum v)).Prime ∧
      normalizedSquareSum (normalizedQuarticSum v) % 4 = 3 := by
  let w := normalizedQuarticSum v
  change ¬ (normalizedSquareSum w).Prime ∧ normalizedSquareSum w % 4 = 3
  have hw_sq : w ∈ squareSources N := (Finset.mem_filter.mp hw_mem).1
  have hw_mod3_ne1 : w % 3 ≠ 1 := (Finset.mem_filter.mp hw_mem).2
  have hw_ne3 : w ≠ 3 := (Finset.mem_filter.mp hw_sq).2.1
  have hw_eq : w = v ^ 4 + v ^ 3 + v ^ 2 + v + 1 := by
    simp [w, normalizedQuarticSum, hv_mod5]
  have hsq_eq : normalizedSquareSum w = w ^ 2 + w + 1 := by
    simp [normalizedSquareSum, hw_mod3_ne1]
  have hnot_prime : ¬ (normalizedSquareSum w).Prime := by
    rw [hsq_eq, hw_eq]
    exact not_prime_sq_add_self_add_one_of_phi5 (by omega)
  have hw20 : w % 20 = 1 := quartic_prime_target_one_mod_twenty hv_prime hv3 hw
  have hw4 : w % 4 = 1 := by omega
  have hw3_ne0 : w % 3 ≠ 0 := by
    intro h0
    exact hw_ne3 ((Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) hw).mp
      (Nat.dvd_of_mod_eq_zero h0)).symm
  have hw3 : w % 3 = 2 := by omega
  have hmod4 : normalizedSquareSum w % 4 = 3 :=
    normalizedSquareSum_mod_four_three (Or.inl ⟨hw3, hw4⟩)
  exact ⟨hnot_prime, hmod4⟩

/-! ## 4. Combined Valuation Budget, Exponent-2 Capped Quartic Incidence, & `409/149` Slope -/

/-- **Combined Quadratic + Quartic Valuation Budget**:
The total number of prime factors (with multiplicity) emitted by `normalizedSquareSum` over
`squareSources N` and `normalizedQuarticSum` over `quarticSourcesZero N q ∪ quarticSourcesOne N q`
is bounded above by the sum of `N.factorization w` over the union `T₃ ∪ T₅` of their target sets. -/
theorem combined_square_quartic_valuation_budget {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (_hq4 : q % 4 = 1) (_he : N.factorization q % 4 = 1)
    (hev : ∀ r, r ≠ q → Even (N.factorization r)) :
    (∑ u ∈ squareSources N, cardFactors (normalizedSquareSum u)) +
        (∑ v ∈ quarticSourcesZero N q ∪ quarticSourcesOne N q,
          cardFactors (normalizedQuarticSum v)) ≤
      ∑ w ∈ insert q (squareSourcesOne N ∪ oneModThreeLargeSources N q) ∪
          oneModFiveTargets N q,
        N.factorization w := by
  let S := squareSources N
  let Q := quarticSourcesZero N q ∪ quarticSourcesOne N q
  let T₃ := insert q (squareSourcesOne N ∪ oneModThreeLargeSources N q)
  let T₅ := oneModFiveTargets N q
  let T := T₃ ∪ T₅
  let f : ℕ → ℕ := fun r =>
    if N.factorization r = 2 then normalizedSquareSum r else normalizedQuarticSum r
  have hS_sub : S ⊆ N.primeFactors := Finset.filter_subset _ _
  have hQ_sub : Q ⊆ N.primeFactors := by
    intro r hr
    rcases Finset.mem_union.mp hr with h0 | h1
    · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp h0).1
    · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp h1).1
  have hSQ_sub : S ∪ Q ⊆ N.primeFactors := Finset.union_subset hS_sub hQ_sub
  have hS_src {u : ℕ} (hu : u ∈ S) : u.Prime ∧ 3 < u ∧ N.factorization u = 2 := by
    obtain ⟨hmem, h3, hex⟩ := Finset.mem_filter.mp hu
    have hprime := Nat.prime_of_mem_primeFactors hmem
    have hodd := Nat.odd_iff.mp (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hmem))
    have := hprime.two_le
    exact ⟨hprime, by omega, hex⟩
  have hQ_src {v : ℕ} (hv : v ∈ Q) : v.Prime ∧ 3 ≤ v ∧ N.factorization v = 4 := by
    have hvN := hQ_sub hv
    have hvp := Nat.prime_of_mem_primeFactors hvN
    have hvo := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hvN)
    have hv_ge2 := hvp.two_le
    have hv_ne2 : v ≠ 2 := fun h => by subst h; exact (by decide : ¬ Odd 2) hvo
    have hv4 : N.factorization v = 4 := by
      rcases Finset.mem_union.mp hv with h0 | h1
      · exact (Finset.mem_filter.mp h0).2.1
      · exact (Finset.mem_filter.mp h1).2.1
    exact ⟨hvp, by omega, hv4⟩
  have hdis_SQ : Disjoint S Q := by
    apply Finset.disjoint_left.mpr
    intro r hrS hrQ
    have h2 := (hS_src hrS).2.2
    have h4 := (hQ_src hrQ).2.2
    omega
  have hdiv : ∀ r ∈ S ∪ Q, f r ∣ sigma 1 (r ^ N.factorization r) := by
    intro r hr
    rcases Finset.mem_union.mp hr with hrS | hrQ
    · obtain ⟨hrp, hr3, hr2⟩ := hS_src hrS
      simp only [f, ite_eq_left hr2, hr2]
      exact normalizedSquareSum_dvd_sigma hrp hr3
    · obtain ⟨hrp, hr3, hr4⟩ := hQ_src hrQ
      have hne2 : N.factorization r ≠ 2 := by omega
      simp only [f, ite_eq_right hne2, hr4]
      exact (quartic_sigma_properties hrp hr3).2.1
  have hcover : ∀ r ∈ S ∪ Q, (f r).primeFactors ⊆ T := by
    intro r hr w hw
    rcases Finset.mem_union.mp hr with hrS | hrQ
    · obtain ⟨hrp, hr3, hr2⟩ := hS_src hrS
      simp only [f, ite_eq_left hr2] at hw
      obtain ⟨hwp, hwdvd, _⟩ := Nat.mem_primeFactors.mp hw
      have hd := hwdvd.trans (normalizedSquareSum_dvd_sigma hrp hr3)
      rw [sigma_one_apply_prime_pow hrp] at hd
      have hmod := (prime_dvd_sq_add_self_add_one hwp (by
        simpa [Finset.sum_range_succ, add_comm, add_assoc, add_left_comm] using hd)).resolve_left
        (fun h => three_not_dvd_normalizedSquareSum hrp hr3 (h ▸ hwdvd))
      have hodd := hwp.odd_of_ne_two (by omega)
      have hwN : w ∣ N := by
        apply dvd_perfect_of_exact_prime_pow hN hrp (Nat.ordProj_dvd _ _) _ hwp hodd
        · rw [← sigma_one_apply, hr2]
          exact hwdvd.trans (normalizedSquareSum_dvd_sigma hrp hr3)
        · rw [hrp.pow_dvd_iff_le_factorization hN.2.ne']
          omega
      have hwmem := Nat.mem_primeFactors.mpr ⟨hwp, hwN, hN.2.ne'⟩
      apply Finset.mem_union_left
      by_cases hwq : w = q
      · exact Finset.mem_insert.mpr (Or.inl hwq)
      · apply Finset.mem_insert_of_mem
        have hw3 : w ≠ 3 := by omega
        by_cases hex : N.factorization w = 2
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨hwmem, hw3, hex⟩, hmod⟩)
        · have hpos := (hwp.dvd_iff_one_le_factorization hN.2.ne').mp hwN
          obtain ⟨k, hk⟩ := hev w hwq
          exact Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨hwmem, hw3, hwq, by omega⟩, hmod⟩)
    · obtain ⟨hrp, hr3, hr4⟩ := hQ_src hrQ
      have hne2 : N.factorization r ≠ 2 := by omega
      simp only [f, ite_eq_right hne2] at hw
      obtain ⟨hwp, hwdvd, _⟩ := Nat.mem_primeFactors.mp hw
      have hprops := quartic_sigma_properties hrp hr3
      have hw_mod : w % 5 = 1 := hprops.2.2.2 w hwp hwdvd
      have hw_odd := hwp.odd_of_ne_two (by omega)
      have hw_sig : w ∣ ∑ d ∈ (r ^ 4).divisors, d := by
        rw [← sigma_one_apply]
        exact hwdvd.trans hprops.2.1
      have hr4_dvd : r ^ 4 ∣ N := by simpa [hr4] using Nat.ordProj_dvd N r
      have hwN : w ∣ N := by
        apply dvd_perfect_of_exact_prime_pow hN hrp hr4_dvd _ hwp hw_odd hw_sig
        rw [hrp.pow_dvd_iff_le_factorization hN.2.ne']
        omega
      have hwmem := Nat.mem_primeFactors.mpr ⟨hwp, hwN, hN.2.ne'⟩
      apply Finset.mem_union_right
      by_cases hwq : w = q
      · exact Finset.mem_insert.mpr (Or.inl hwq)
      · exact Finset.mem_insert_of_mem
          (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hwq, hwmem⟩, hw_mod⟩)
  have hT_sub : T ⊆ N.primeFactors := by
    intro w hw
    rcases Finset.mem_union.mp hw with h3 | h5
    · rcases Finset.mem_insert.mp h3 with rfl | h
      · exact hq
      · rcases Finset.mem_union.mp h with h | h
        · exact hS_sub (Finset.mem_filter.mp h).1
        · exact (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1
    · rcases Finset.mem_insert.mp h5 with rfl | h
      · exact hq
      · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp h).1
  have hupper := sum_cardFactors_le_target_exponents hN (S ∪ Q) T f hSQ_sub hdiv hcover
    (fun w hw => ⟨Nat.prime_of_mem_primeFactors (hT_sub hw),
      ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors (hT_sub hw))⟩)
  rw [Finset.sum_union hdis_SQ] at hupper
  have hsum_S : ∑ u ∈ S, cardFactors (f u) = ∑ u ∈ S, cardFactors (normalizedSquareSum u) := by
    refine Finset.sum_congr rfl fun u hu => ?_
    simp [f, (hS_src hu).2.2]
  have hsum_Q : ∑ v ∈ Q, cardFactors (f v) = ∑ v ∈ Q, cardFactors (normalizedQuarticSum v) := by
    refine Finset.sum_congr rfl fun v hv => ?_
    have hne2 : N.factorization v ≠ 2 := by have := (hQ_src hv).2.2; omega
    simp [f, hne2]
  rw [hsum_S, hsum_Q] at hupper
  exact hupper

private lemma quartic_one_lt_cd {u : ℕ} (hu3 : 3 ≤ u) :
    1 < normalizedQuarticSum u := by
  by_cases h5 : u % 5 = 1
  · obtain ⟨k, rfl⟩ : ∃ k, u = 5 * k + 1 := ⟨u / 5, by omega⟩
    have hnorm : normalizedQuarticSum (5 * k + 1) =
        125 * k ^ 4 + 125 * k ^ 3 + 50 * k ^ 2 + 10 * k + 1 := by
      rw [normalizedQuarticSum, ite_eq_left (show (5 * k + 1) % 5 = 1 by omega)]
      rw [show (5 * k + 1) ^ 4 + (5 * k + 1) ^ 3 + (5 * k + 1) ^ 2 + (5 * k + 1) + 1 =
          5 * (125 * k ^ 4 + 125 * k ^ 3 + 50 * k ^ 2 + 10 * k + 1) by ring]
      simp
    rw [hnorm]
    have hk : 1 ≤ k := by omega
    nlinarith
  · simp only [normalizedQuarticSum, ite_eq_right h5]
    have h2 : 9 ≤ u ^ 2 := by nlinarith
    omega

private lemma quartic_gt_self_of_mod_one_cd {u : ℕ} (hu3 : 3 ≤ u) (hu_mod : u % 5 = 1) :
    u < normalizedQuarticSum u := by
  obtain ⟨k, rfl⟩ : ∃ k, u = 5 * k + 1 := ⟨u / 5, by omega⟩
  have hnorm : normalizedQuarticSum (5 * k + 1) =
      125 * k ^ 4 + 125 * k ^ 3 + 50 * k ^ 2 + 10 * k + 1 := by
    rw [normalizedQuarticSum, ite_eq_left (show (5 * k + 1) % 5 = 1 by omega)]
    rw [show (5 * k + 1) ^ 4 + (5 * k + 1) ^ 3 + (5 * k + 1) ^ 2 + (5 * k + 1) + 1 =
        5 * (125 * k ^ 4 + 125 * k ^ 3 + 50 * k ^ 2 + 10 * k + 1) by ring]
    simp
  rw [hnorm]
  have hk : 1 ≤ k := by omega
  nlinarith

private lemma le_pow_cardFactors_of_primeFactors_le_cd {M u : ℕ} (hM : M ≠ 0)
    (h : ∀ w ∈ M.primeFactors, w ≤ u) : M ≤ u ^ cardFactors M := by
  calc
    M = ∏ w ∈ M.primeFactors, w ^ M.factorization w := Nat.prod_primeFactors_pow_factorization hM
    _ ≤ ∏ w ∈ M.primeFactors, u ^ M.factorization w :=
        Finset.prod_le_prod fun w hw => Nat.pow_le_pow_left (h w hw) _
    _ = u ^ ∑ w ∈ M.primeFactors, M.factorization w := Finset.prod_pow_eq_pow_sum _ _ _
    _ = u ^ cardFactors M := by
        rw [cardFactors_eq_sum_factorization]
        rfl

private lemma quartic_zero_exists_gt_of_cardFactors_le_three_cd {u : ℕ} (hu3 : 3 ≤ u)
    (hu_mod : u % 5 ≠ 1) (hcard : cardFactors (normalizedQuarticSum u) ≤ 3) :
    ∃ w ∈ (normalizedQuarticSum u).primeFactors, u < w := by
  have hnorm : normalizedQuarticSum u = u ^ 4 + u ^ 3 + u ^ 2 + u + 1 := by
    simp [normalizedQuarticSum, hu_mod]
  by_contra! hle
  have hM_ne : normalizedQuarticSum u ≠ 0 := by rw [hnorm]; positivity
  have hbound := le_pow_cardFactors_of_primeFactors_le_cd hM_ne hle
  have hpow : u ^ cardFactors (normalizedQuarticSum u) ≤ u ^ 3 :=
    Nat.pow_le_pow_right (by omega) hcard
  have h34 : u ^ 3 ≤ u ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hle_pow : u ^ 4 + u ^ 3 + u ^ 2 + u + 1 ≤ u ^ 4 := by
    calc
      u ^ 4 + u ^ 3 + u ^ 2 + u + 1 = normalizedQuarticSum u := hnorm.symm
      _ ≤ u ^ cardFactors (normalizedQuarticSum u) := hbound
      _ ≤ u ^ 3 := hpow
      _ ≤ u ^ 4 := h34
  have hpos : 0 < u ^ 3 + u ^ 2 + u + 1 := by positivity
  omega

private lemma normalizedQuarticSum_strictMono_of_mod_ne_one_cd {u v : ℕ}
    (hu_mod : u % 5 ≠ 1) (hv_mod : v % 5 ≠ 1)
    (heq : normalizedQuarticSum u = normalizedQuarticSum v) : u = v := by
  simp only [normalizedQuarticSum, ite_eq_right hu_mod, ite_eq_right hv_mod] at heq
  have hmono : StrictMono (fun x : ℕ => x ^ 4 + x ^ 3 + x ^ 2 + x + 1) := by
    intro a b hab
    have h2 : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hab.le 2
    have h3 : a ^ 3 ≤ b ^ 3 := Nat.pow_le_pow_left hab.le 3
    have h4 : a ^ 4 ≤ b ^ 4 := Nat.pow_le_pow_left hab.le 4
    dsimp
    omega
  exact hmono.injective heq

private lemma geometricBlock_five_eq_cd (x : ℕ) :
    geometricBlock x 5 = x ^ 4 + x ^ 3 + x ^ 2 + x + 1 := by
  simp [geometricBlock, Finset.sum_range_succ]
  ring

/-- **Exponent-2 Capped Quartic Root-Slot Incidence (`¬ 3 ∣ N`)**:
Caps upward `l = 5` root fibers at square targets `w ∈ S₅₁` by `N.factorization w = 2`
and uses `quartic_prime_target_disjoint_squareSourcesTwo_prime` to keep `T_B₁` disjoint
from `A₁₂_₅₁`. -/
theorem quarticSources_e2_capped_incidence {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (h3 : ¬ 3 ∣ N) :
    let S₅₁ := (squareSources N).filter (· % 5 = 1)
    let A₁₂_₅₁ := S₅₁.filter (fun w => (normalizedSquareSum w).Prime)
    let S₅₁_comp := S₅₁.filter (fun w => ¬ (normalizedSquareSum w).Prime)
    let T₅_high := (oneModFiveTargets N q) \ S₅₁
    5 * (quarticSourcesZero N q).card + 3 * (quarticSourcesOne N q).card ≤
      2 * (∑ r ∈ oneModFiveTargets N q, N.factorization r) +
        2 * A₁₂_₅₁.card + 4 * S₅₁_comp.card + 4 * T₅_high.card := by
  intro S₅₁ A₁₂_₅₁ S₅₁_comp T₅_high
  let Q₀ := quarticSourcesZero N q
  let Q₁ := quarticSourcesOne N q
  let Q := Q₀ ∪ Q₁
  let T₅ := oneModFiveTargets N q
  have hdis_Q : Disjoint Q₀ Q₁ := by
    apply Finset.disjoint_left.mpr
    intro r h0 h1
    exact (Finset.mem_filter.mp h0).2.2 (Finset.mem_filter.mp h1).2.2
  have hQ_sub : Q ⊆ N.primeFactors := by
    intro r hr
    rcases Finset.mem_union.mp hr with h0 | h1
    · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp h0).1
    · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp h1).1
  have hsource {u : ℕ} (hu : u ∈ Q) : u.Prime ∧ 3 ≤ u ∧ N.factorization u = 4 := by
    have huN : u ∈ N.primeFactors := hQ_sub hu
    have hup := Nat.prime_of_mem_primeFactors huN
    have huo := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors huN)
    have hu_ge2 := hup.two_le
    have hu_ne2 : u ≠ 2 := fun h => by subst h; exact (by decide : ¬ Odd 2) huo
    have hu_fac : N.factorization u = 4 := by
      rcases Finset.mem_union.mp hu with h0 | h1
      · exact (Finset.mem_filter.mp h0).2.1
      · exact (Finset.mem_filter.mp h1).2.1
    exact ⟨hup, by omega, hu_fac⟩
  have hlocalDiv (u : ℕ) (hu : u ∈ Q) :
      normalizedQuarticSum u ∣ sigma 1 (u ^ N.factorization u) := by
    obtain ⟨hup, hu3, h4⟩ := hsource hu
    rw [h4]
    exact (quartic_sigma_properties hup hu3).2.1
  have hcover (u : ℕ) (hu : u ∈ Q) : (normalizedQuarticSum u).primeFactors ⊆ T₅ := by
    intro w hw
    obtain ⟨hup, hu3, h4⟩ := hsource hu
    obtain ⟨hwp, hwdvd, _⟩ := Nat.mem_primeFactors.mp hw
    have hprops := quartic_sigma_properties hup hu3
    have hw_mod : w % 5 = 1 := hprops.2.2.2 w hwp hwdvd
    have hw_odd : Odd w := hwp.odd_of_ne_two (by omega)
    have hw_sig : w ∣ ∑ d ∈ (u ^ 4).divisors, d := by
      rw [← sigma_one_apply]
      exact hwdvd.trans hprops.2.1
    have hu4_dvd : u ^ 4 ∣ N := by simpa [h4] using Nat.ordProj_dvd N u
    have hw_dvd_N : w ∣ N := by
      apply dvd_perfect_of_exact_prime_pow hN hup hu4_dvd _ hwp hw_odd hw_sig
      rw [hup.pow_dvd_iff_le_factorization hN.2.ne']
      omega
    have hw_mem := Nat.mem_primeFactors.mpr ⟨hwp, hw_dvd_N, hN.2.ne'⟩
    by_cases hwq : w = q
    · exact Finset.mem_insert.mpr (Or.inl hwq)
    · exact Finset.mem_insert_of_mem
        (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hwq, hw_mem⟩, hw_mod⟩)
  have hT_sub : T₅ ⊆ N.primeFactors := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | h
    · exact hq
    · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp h).1
  have hupper := sum_cardFactors_le_target_exponents hN Q T₅ normalizedQuarticSum
    hQ_sub hlocalDiv hcover (fun r hr =>
      ⟨Nat.prime_of_mem_primeFactors (hT_sub hr),
        ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors (hT_sub hr))⟩)
  let B₁ := Q₀.filter fun u => (normalizedQuarticSum u).Prime
  let B₂ := Q₀.filter fun u => cardFactors (normalizedQuarticSum u) = 2
  let B₃ := Q₀.filter fun u => cardFactors (normalizedQuarticSum u) = 3
  let B₄ := Q₀.filter fun u => 4 ≤ cardFactors (normalizedQuarticSum u)
  let C₁ := Q₁.filter fun u => (normalizedQuarticSum u).Prime
  let C₂ := Q₁.filter fun u => 2 ≤ cardFactors (normalizedQuarticSum u)
  have hQ₀_part : Q₀ = B₁ ∪ B₂ ∪ B₃ ∪ B₄ := by
    ext u
    simp only [B₁, B₂, B₃, B₄, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hu
      have hu3 := (hsource (Finset.mem_union_left _ hu)).2.1
      have hpos := cardFactors_pos_iff_one_lt.mpr (quartic_one_lt_cd hu3)
      by_cases h1 : cardFactors (normalizedQuarticSum u) = 1
      · exact Or.inl (Or.inl (Or.inl ⟨hu, cardFactors_eq_one_iff_prime.mp h1⟩))
      · by_cases h2 : cardFactors (normalizedQuarticSum u) = 2
        · exact Or.inl (Or.inl (Or.inr ⟨hu, h2⟩))
        · by_cases h3c : cardFactors (normalizedQuarticSum u) = 3
          · exact Or.inl (Or.inr ⟨hu, h3c⟩)
          · exact Or.inr ⟨hu, by omega⟩
    · rintro (((⟨hu, _⟩ | ⟨hu, _⟩) | ⟨hu, _⟩) | ⟨hu, _⟩) <;> exact hu
  have hdis_B₁_B₂ : Disjoint B₁ B₂ := by
    apply Finset.disjoint_left.mpr
    intro u h1 h2
    have hp1 := cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp h1).2
    have hp2 := (Finset.mem_filter.mp h2).2
    omega
  have hdis_B₁₂_B₃ : Disjoint (B₁ ∪ B₂) B₃ := by
    apply Finset.disjoint_left.mpr
    intro u h12 h3c
    have hp3 := (Finset.mem_filter.mp h3c).2
    rcases Finset.mem_union.mp h12 with h1 | h2
    · have hp1 := cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp h1).2
      omega
    · have hp2 := (Finset.mem_filter.mp h2).2
      omega
  have hdis_B₁₂₃_B₄ : Disjoint (B₁ ∪ B₂ ∪ B₃) B₄ := by
    apply Finset.disjoint_left.mpr
    intro u h123 h4
    have hge4 := (Finset.mem_filter.mp h4).2
    rcases Finset.mem_union.mp h123 with h12 | h3c
    · rcases Finset.mem_union.mp h12 with h1 | h2
      · have hp1 := cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp h1).2
        omega
      · have hp2 := (Finset.mem_filter.mp h2).2
        omega
    · have hp3 := (Finset.mem_filter.mp h3c).2
      omega
  have hQ₀_card : Q₀.card = B₁.card + B₂.card + B₃.card + B₄.card := by
    rw [hQ₀_part, Finset.card_union_of_disjoint hdis_B₁₂₃_B₄,
      Finset.card_union_of_disjoint hdis_B₁₂_B₃, Finset.card_union_of_disjoint hdis_B₁_B₂]
  have hQ₁_part : Q₁ = C₁ ∪ C₂ := by
    ext u
    simp only [C₁, C₂, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hu
      have hu3 := (hsource (Finset.mem_union_right _ hu)).2.1
      have hpos := cardFactors_pos_iff_one_lt.mpr (quartic_one_lt_cd hu3)
      by_cases h1 : cardFactors (normalizedQuarticSum u) = 1
      · exact Or.inl ⟨hu, cardFactors_eq_one_iff_prime.mp h1⟩
      · exact Or.inr ⟨hu, by omega⟩
    · rintro (⟨hu, _⟩ | ⟨hu, _⟩) <;> exact hu
  have hdis_C₁_C₂ : Disjoint C₁ C₂ := by
    apply Finset.disjoint_left.mpr
    intro u h1 h2
    have hp1 := cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp h1).2
    have hge2 := (Finset.mem_filter.mp h2).2
    omega
  have hQ₁_card : Q₁.card = C₁.card + C₂.card := by
    rw [hQ₁_part, Finset.card_union_of_disjoint hdis_C₁_C₂]
  have hsum_Q₀ :
      B₁.card + 2 * B₂.card + 3 * B₃.card + 4 * B₄.card ≤
        ∑ u ∈ Q₀, cardFactors (normalizedQuarticSum u) := by
    rw [hQ₀_part, Finset.sum_union hdis_B₁₂₃_B₄, Finset.sum_union hdis_B₁₂_B₃,
      Finset.sum_union hdis_B₁_B₂]
    have h1 : B₁.card ≤ ∑ u ∈ B₁, cardFactors (normalizedQuarticSum u) := by
      calc
        B₁.card = ∑ _u ∈ B₁, 1 := by simp
        _ ≤ ∑ u ∈ B₁, cardFactors (normalizedQuarticSum u) := by
            refine Finset.sum_le_sum fun u hu => ?_
            rw [cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp hu).2]
    have h2 : 2 * B₂.card ≤ ∑ u ∈ B₂, cardFactors (normalizedQuarticSum u) := by
      calc
        2 * B₂.card = ∑ _u ∈ B₂, 2 := by simp [Nat.mul_comm]
        _ ≤ ∑ u ∈ B₂, cardFactors (normalizedQuarticSum u) := by
            refine Finset.sum_le_sum fun u hu => ?_
            rw [(Finset.mem_filter.mp hu).2]
    have h3s : 3 * B₃.card ≤ ∑ u ∈ B₃, cardFactors (normalizedQuarticSum u) := by
      calc
        3 * B₃.card = ∑ _u ∈ B₃, 3 := by simp [Nat.mul_comm]
        _ ≤ ∑ u ∈ B₃, cardFactors (normalizedQuarticSum u) := by
            refine Finset.sum_le_sum fun u hu => ?_
            rw [(Finset.mem_filter.mp hu).2]
    have h4 : 4 * B₄.card ≤ ∑ u ∈ B₄, cardFactors (normalizedQuarticSum u) := by
      calc
        4 * B₄.card = ∑ _u ∈ B₄, 4 := by simp [Nat.mul_comm]
        _ ≤ ∑ u ∈ B₄, cardFactors (normalizedQuarticSum u) :=
            Finset.sum_le_sum fun u hu => (Finset.mem_filter.mp hu).2
    omega
  have hsum_Q₁ :
      C₁.card + 2 * C₂.card ≤ ∑ u ∈ Q₁, cardFactors (normalizedQuarticSum u) := by
    rw [hQ₁_part, Finset.sum_union hdis_C₁_C₂]
    have h1 : C₁.card ≤ ∑ u ∈ C₁, cardFactors (normalizedQuarticSum u) := by
      calc
        C₁.card = ∑ _u ∈ C₁, 1 := by simp
        _ ≤ ∑ u ∈ C₁, cardFactors (normalizedQuarticSum u) := by
            refine Finset.sum_le_sum fun u hu => ?_
            rw [cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp hu).2]
    have h2 : 2 * C₂.card ≤ ∑ u ∈ C₂, cardFactors (normalizedQuarticSum u) := by
      calc
        2 * C₂.card = ∑ _u ∈ C₂, 2 := by simp [Nat.mul_comm]
        _ ≤ ∑ u ∈ C₂, cardFactors (normalizedQuarticSum u) :=
            Finset.sum_le_sum fun u hu => (Finset.mem_filter.mp hu).2
    omega
  have hsum_Q :
      ∑ u ∈ Q, cardFactors (normalizedQuarticSum u) =
        ∑ u ∈ Q₀, cardFactors (normalizedQuarticSum u) +
          ∑ u ∈ Q₁, cardFactors (normalizedQuarticSum u) :=
    Finset.sum_union hdis_Q
  let Up₅ := (Q ×ˢ T₅).filter fun uw => uw.1 < uw.2 ∧ uw.2 ∣ normalizedQuarticSum uw.1
  let U_up := B₁ ∪ B₂ ∪ B₃ ∪ C₁
  have hdis_B₁₂₃_C₁ : Disjoint (B₁ ∪ B₂ ∪ B₃) C₁ := by
    apply Finset.disjoint_left.mpr
    intro u h123 hc1
    have huQ₁ := (Finset.mem_filter.mp hc1).1
    rcases Finset.mem_union.mp h123 with h12 | h3c
    · rcases Finset.mem_union.mp h12 with h1 | h2
      · exact Finset.disjoint_left.mp hdis_Q (Finset.mem_filter.mp h1).1 huQ₁
      · exact Finset.disjoint_left.mp hdis_Q (Finset.mem_filter.mp h2).1 huQ₁
    · exact Finset.disjoint_left.mp hdis_Q (Finset.mem_filter.mp h3c).1 huQ₁
  have hU_up_card : U_up.card = B₁.card + B₂.card + B₃.card + C₁.card := by
    dsimp only [U_up]
    rw [Finset.card_union_of_disjoint hdis_B₁₂₃_C₁, Finset.card_union_of_disjoint hdis_B₁₂_B₃,
      Finset.card_union_of_disjoint hdis_B₁_B₂]
  have hU_up_sub : U_up ⊆ Up₅.image Prod.fst := by
    intro u hu
    rw [Finset.mem_image]
    rcases Finset.mem_union.mp hu with hB123 | hC₁
    · rcases Finset.mem_union.mp hB123 with hB12 | huB₃
      · rcases Finset.mem_union.mp hB12 with huB₁ | huB₂
        · obtain ⟨huQ₀, hwp⟩ := Finset.mem_filter.mp huB₁
          have huQ : u ∈ Q := Finset.mem_union_left _ huQ₀
          have hu_mod : u % 5 ≠ 1 := (Finset.mem_filter.mp huQ₀).2.2
          have hu3 := (hsource huQ).2.1
          let w := normalizedQuarticSum u
          have hwT : w ∈ T₅ := hcover u huQ (Nat.mem_primeFactors.mpr ⟨hwp, dvd_rfl, hwp.ne_zero⟩)
          have hlt : u < w := by
            have hnorm : w = u ^ 4 + u ^ 3 + u ^ 2 + u + 1 := by simp [w, normalizedQuarticSum, hu_mod]
            have hsq : 3 * u ≤ u ^ 2 := by nlinarith
            rw [hnorm]
            omega
          exact ⟨(u, w), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huQ, hwT⟩, hlt, dvd_rfl⟩, rfl⟩
        · obtain ⟨huQ₀, h2⟩ := Finset.mem_filter.mp huB₂
          have huQ : u ∈ Q := Finset.mem_union_left _ huQ₀
          have hu3 := (hsource huQ).2.1
          have hu_mod : u % 5 ≠ 1 := (Finset.mem_filter.mp huQ₀).2.2
          obtain ⟨w, hw_pf, huw⟩ :=
            quartic_zero_exists_gt_of_cardFactors_le_three_cd hu3 hu_mod (by omega)
          exact ⟨(u, w), Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨huQ, hcover u huQ hw_pf⟩, huw, Nat.dvd_of_mem_primeFactors hw_pf⟩, rfl⟩
      · obtain ⟨huQ₀, h3c⟩ := Finset.mem_filter.mp huB₃
        have huQ : u ∈ Q := Finset.mem_union_left _ huQ₀
        have hu3 := (hsource huQ).2.1
        have hu_mod : u % 5 ≠ 1 := (Finset.mem_filter.mp huQ₀).2.2
        obtain ⟨w, hw_pf, huw⟩ :=
          quartic_zero_exists_gt_of_cardFactors_le_three_cd hu3 hu_mod (by omega)
        exact ⟨(u, w), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨huQ, hcover u huQ hw_pf⟩, huw, Nat.dvd_of_mem_primeFactors hw_pf⟩, rfl⟩
    · obtain ⟨huQ₁, hwp⟩ := Finset.mem_filter.mp hC₁
      have huQ : u ∈ Q := Finset.mem_union_right _ huQ₁
      have hu3 := (hsource huQ).2.1
      have hu_mod : u % 5 = 1 := (Finset.mem_filter.mp huQ₁).2.2
      let w := normalizedQuarticSum u
      have hwT : w ∈ T₅ := hcover u huQ (Nat.mem_primeFactors.mpr ⟨hwp, dvd_rfl, hwp.ne_zero⟩)
      have hlt : u < w := quartic_gt_self_of_mod_one_cd hu3 hu_mod
      exact ⟨(u, w), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huQ, hwT⟩, hlt, dvd_rfl⟩, rfl⟩
  have hUp_lower : B₁.card + B₂.card + B₃.card + C₁.card ≤ Up₅.card := by
    rw [← hU_up_card]
    exact (Finset.card_le_card hU_up_sub).trans Finset.card_image_le
  let T_B₁ := B₁.image normalizedQuarticSum
  have hT_B₁_sub : T_B₁ ⊆ T₅ := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨huQ₀, hwp⟩ := Finset.mem_filter.mp hu
    exact hcover u (Finset.mem_union_left _ huQ₀)
      (Nat.mem_primeFactors.mpr ⟨hwp, dvd_rfl, hwp.ne_zero⟩)
  have hT_B₁_card : T_B₁.card = B₁.card := by
    apply Finset.card_image_of_injOn
    intro u hu v hv heq
    have hu_mod : u % 5 ≠ 1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2.2
    have hv_mod : v % 5 ≠ 1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2.2
    exact normalizedQuarticSum_strictMono_of_mod_ne_one_cd hu_mod hv_mod heq
  have hUp_fiber : Up₅.card = ∑ w ∈ T₅, (Up₅.filter fun uw => uw.2 = w).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro uw huw
    exact (Finset.mem_product.mp (Finset.mem_filter.mp huw).1).2
  have hfiber_le (w : ℕ) :
      (Up₅.filter fun uw => uw.2 = w).card ≤
        (Q.filter fun v => v < w ∧ w ∣ normalizedQuarticSum v).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro uw huw
      obtain ⟨huw_Up, rfl⟩ := Finset.mem_filter.mp huw
      obtain ⟨huw_prod, hlt, hdvd⟩ := Finset.mem_filter.mp huw_Up
      exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp huw_prod).1, hlt, hdvd⟩
    · intro x hx y hy hxy
      obtain ⟨_, hx2⟩ := Finset.mem_filter.mp hx
      obtain ⟨_, hy2⟩ := Finset.mem_filter.mp hy
      exact Prod.ext hxy (hx2.trans hy2.symm)
  have hfiber_T_B₁ : ∀ w ∈ T_B₁, (Up₅.filter fun uw => uw.2 = w).card ≤ 1 := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨huQ₀, hwp⟩ := Finset.mem_filter.mp hu
    have huQ : u ∈ Q := Finset.mem_union_left _ huQ₀
    have hup := (hsource huQ).1
    have hu_mod : u % 5 ≠ 1 := (Finset.mem_filter.mp huQ₀).2.2
    have hw_eq : normalizedQuarticSum u = geometricBlock u 5 := by
      rw [geometricBlock_five_eq_cd]
      simp [normalizedQuarticSum, hu_mod]
    have hsub :
        (Q.filter fun v => v < normalizedQuarticSum u ∧ normalizedQuarticSum u ∣ normalizedQuarticSum v) ⊆
          {u} := by
      intro v hv
      obtain ⟨hvQ, hvw, hdvd⟩ := Finset.mem_filter.mp hv
      have hvp := (hsource hvQ).1
      rw [Finset.mem_singleton]
      rw [hw_eq] at hvw hdvd hwp
      exact geometricBlock_prime_root_unique hup (by decide : Nat.Prime 5) (by decide : 3 ≤ 5)
        hwp hvp hvw (hdvd.trans ((normalizedQuarticSum_dvd_phi5_cd v).trans
          (by rw [geometricBlock_five_eq_cd])))
    exact (hfiber_le _).trans ((Finset.card_le_card hsub).trans (by simp))
  have hfiber_other : ∀ w ∈ T₅ \ T_B₁, (Up₅.filter fun uw => uw.2 = w).card ≤ 4 := by
    intro w hw
    have hwT : w ∈ T₅ := (Finset.mem_sdiff.mp hw).1
    have hwp : w.Prime := Nat.prime_of_mem_primeFactors (hT_sub hwT)
    by_cases hw5 : w = 5
    · subst hw5
      have hempty : Q.filter (fun v => v < 5 ∧ 5 ∣ normalizedQuarticSum v) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro v hv
        obtain ⟨hvQ, _, hdvd⟩ := Finset.mem_filter.mp hv
        obtain ⟨hvp, hv3, _⟩ := hsource hvQ
        exact (quartic_sigma_properties hvp hv3).2.2.1 hdvd
      exact (hfiber_le 5).trans (by rw [hempty]; simp)
    · have hsub :
          (Q.filter fun v => v < w ∧ w ∣ normalizedQuarticSum v) ⊆
            (Finset.range w).filter (fun x => w ∣ geometricBlock x 5) := by
        intro v hv
        obtain ⟨_, hvw, hdvd⟩ := Finset.mem_filter.mp hv
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hvw,
            hdvd.trans ((normalizedQuarticSum_dvd_phi5_cd v).trans (by rw [geometricBlock_five_eq_cd]))⟩
      exact (hfiber_le w).trans
        ((Finset.card_le_card hsub).trans
          (card_range_dvd_geometricBlock_le_pred (by decide : Nat.Prime 5) hwp hw5))
  have hS₅₁_sub : S₅₁ ⊆ T₅ := by
    intro w hw
    obtain ⟨hwS, hw5⟩ := Finset.mem_filter.mp hw
    have hwN : w ∈ N.primeFactors := (Finset.mem_filter.mp hwS).1
    by_cases hwq : w = q
    · exact Finset.mem_insert.mpr (Or.inl hwq)
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hwq, hwN⟩, hw5⟩)
  have hA₁₂_sub : A₁₂_₅₁ ⊆ T₅ := (Finset.filter_subset _ _).trans hS₅₁_sub
  have hfiber_S₅₁ : ∀ w ∈ S₅₁, (Up₅.filter fun uw => uw.2 = w).card ≤ 2 := by
    intro w hw
    obtain ⟨hwS, _⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwN, _, hw2⟩ := Finset.mem_filter.mp hwS
    have hwp := Nat.prime_of_mem_primeFactors hwN
    have hwo := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hwN)
    have hcard_le : (Q.filter fun v => v < w ∧ w ∣ normalizedQuarticSum v).card ≤ N.factorization w := by
      apply card_le_factorization_of_sigma_sources hN hwo hwp
      · exact (Finset.filter_subset _ _).trans hQ_sub
      · intro v hv
        obtain ⟨hvQ, _, hdvd⟩ := Finset.mem_filter.mp hv
        exact hdvd.trans (hlocalDiv v hvQ)
    rw [hw2] at hcard_le
    exact (hfiber_le w).trans hcard_le
  have hS1_zero : (squareSourcesOne N).card = 0 := by
    have hb := squareSourcesOne_card_le_three_exponent hN
    have hz : N.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd h3
    omega
  have hS_eq_S2 : squareSources N = squareSourcesTwo N := by
    rw [squareSources_eq_union_one_two N, Finset.card_eq_zero.mp hS1_zero, Finset.empty_union]
  have hdis_TB₁_A₁₂ : Disjoint T_B₁ A₁₂_₅₁ := by
    apply Finset.disjoint_left.mpr
    intro w hwTB₁ hwA
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hwTB₁
    obtain ⟨hvQ₀, hvp_q⟩ := Finset.mem_filter.mp hv
    have hv_src := hsource (Finset.mem_union_left _ hvQ₀)
    have hv_mod5 : v % 5 ≠ 1 := (Finset.mem_filter.mp hvQ₀).2.2
    obtain ⟨hwS51, hw_sq_prime⟩ := Finset.mem_filter.mp hwA
    have hwS : normalizedQuarticSum v ∈ squareSources N := (Finset.mem_filter.mp hwS51).1
    have hwS2 : normalizedQuarticSum v ∈ squareSourcesTwo N := hS_eq_S2 ▸ hwS
    exact (quartic_prime_target_disjoint_squareSourcesTwo_prime
      hv_src.1 hv_src.2.1 hv_mod5 hvp_q hwS2).1 hw_sq_prime
  have hT_B₁_sub_sdiff : T_B₁ ⊆ T₅ \ A₁₂_₅₁ := by
    intro w hw
    exact Finset.mem_sdiff.mpr ⟨hT_B₁_sub hw, Finset.disjoint_left.mp hdis_TB₁_A₁₂ hw⟩
  have hUp_upper :
      Up₅.card + 3 * B₁.card ≤ 2 * A₁₂_₅₁.card + 4 * S₅₁_comp.card + 4 * T₅_high.card := by
    let f : ℕ → ℕ := fun w => (Up₅.filter fun uw => uw.2 = w).card
    have hs1 := Finset.sum_sdiff hA₁₂_sub (f := f)
    have hs2 := Finset.sum_sdiff hT_B₁_sub_sdiff (f := f)
    have hsum_A : ∑ w ∈ A₁₂_₅₁, f w ≤ 2 * A₁₂_₅₁.card := by
      calc
        ∑ w ∈ A₁₂_₅₁, f w ≤ ∑ _w ∈ A₁₂_₅₁, 2 :=
            Finset.sum_le_sum fun w hw => hfiber_S₅₁ w (Finset.filter_subset _ _ hw)
        _ = 2 * A₁₂_₅₁.card := by simp [Nat.mul_comm]
    have hsum_TB₁ : ∑ w ∈ T_B₁, f w ≤ T_B₁.card := by
      calc
        ∑ w ∈ T_B₁, f w ≤ ∑ _w ∈ T_B₁, 1 := Finset.sum_le_sum hfiber_T_B₁
        _ = T_B₁.card := by simp
    have hsum_rem :
        ∑ w ∈ (T₅ \ A₁₂_₅₁) \ T_B₁, f w ≤ 4 * ((T₅ \ A₁₂_₅₁) \ T_B₁).card := by
      calc
        ∑ w ∈ (T₅ \ A₁₂_₅₁) \ T_B₁, f w ≤ ∑ _w ∈ (T₅ \ A₁₂_₅₁) \ T_B₁, 4 := by
            refine Finset.sum_le_sum fun w hw => ?_
            have hw1 := (Finset.mem_sdiff.mp hw).1
            have hw2 := (Finset.mem_sdiff.mp hw).2
            exact hfiber_other w (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hw1).1, hw2⟩)
        _ = 4 * ((T₅ \ A₁₂_₅₁) \ T_B₁).card := by simp [Nat.mul_comm]
    have hc1 : A₁₂_₅₁.card + (T₅ \ A₁₂_₅₁).card = T₅.card := by
      rw [← Finset.card_union_of_disjoint disjoint_sdiff_self_right,
        Finset.union_sdiff_of_subset hA₁₂_sub]
    have hc2 : T_B₁.card + ((T₅ \ A₁₂_₅₁) \ T_B₁).card = (T₅ \ A₁₂_₅₁).card := by
      rw [← Finset.card_union_of_disjoint disjoint_sdiff_self_right,
        Finset.union_sdiff_of_subset hT_B₁_sub_sdiff]
    have hc3 : S₅₁.card + T₅_high.card = T₅.card := by
      dsimp only [T₅_high]
      rw [← Finset.card_union_of_disjoint disjoint_sdiff_self_right,
        Finset.union_sdiff_of_subset hS₅₁_sub]
    have hS₅₁_part : S₅₁ = A₁₂_₅₁ ∪ S₅₁_comp := by
      ext w
      simp only [A₁₂_₅₁, S₅₁_comp, Finset.mem_union, Finset.mem_filter]
      by_cases hp : (normalizedSquareSum w).Prime <;> tauto
    have hdis_S₅₁ : Disjoint A₁₂_₅₁ S₅₁_comp :=
      Finset.disjoint_left.mpr fun w h1 h2 =>
        (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hc4 : S₅₁.card = A₁₂_₅₁.card + S₅₁_comp.card := by
      rw [hS₅₁_part, Finset.card_union_of_disjoint hdis_S₅₁]
    change Up₅.card = ∑ w ∈ T₅, f w at hUp_fiber
    omega
  change 5 * Q₀.card + 3 * Q₁.card ≤
      2 * (∑ r ∈ T₅, N.factorization r) + 2 * A₁₂_₅₁.card + 4 * S₅₁_comp.card + 4 * T₅_high.card
  omega

/-- **`5`-Unconditional `409/149` Coupled Multi-Block Slope (`¬ 3 ∣ N`)**:
Combines `squareSources_vieta_root_slot_incidence_three_free` (weight `37`),
`quarticSources_e2_capped_incidence` (weight `7`), and `quarticSourcesOne_card_le_five_exponent`
(weight `98`) without assuming `¬ 5 ∣ N`. -/
theorem multi_block_coupled_three_free_uncond_five {N : ℕ} (ho : Odd N) (hN : N.Perfect)
    (h3 : ¬ 3 ∣ N) :
    409 * N.primeFactors.card ≤
      149 * N.primeFactorsList.length + 1099 +
        42 * ((squareSources N).filter (fun w => w % 5 = 1 ∧ (normalizedSquareSum w).Prime)).card +
        56 * ((squareSources N).filter (fun w => w % 5 = 1 ∧ ¬ (normalizedSquareSum w).Prime)).card := by
  obtain ⟨q, hq, hq4, he, hev⟩ := euler_exponents ho hN
  let S := squareSources N
  let Q₀ := quarticSourcesZero N q
  let Q₁ := quarticSourcesOne N q
  let L := largeSources N q
  let R := L.filter fun r => 6 ≤ N.factorization r
  let R₅ := R.filter fun r => r % 5 = 1
  let R₀ := R.filter fun r => r % 5 ≠ 1
  let S₅₁ := S.filter fun r => r % 5 = 1
  let A₁₂_₅₁ := S₅₁.filter fun w => (normalizedSquareSum w).Prime
  let S₅₁_comp := S₅₁.filter fun w => ¬ (normalizedSquareSum w).Prime
  let T₅ := oneModFiveTargets N q
  let T₅_high := T₅ \ S₅₁
  have hpos {r : ℕ} (hr : r ∈ N.primeFactors) : 0 < N.factorization r :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
  have hS1_zero : (squareSourcesOne N).card = 0 := by
    have hb := squareSourcesOne_card_le_three_exponent hN
    have hz : N.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd h3
    omega
  have hS_eq_S2 : S = squareSourcesTwo N := by
    dsimp only [S]
    rw [squareSources_eq_union_one_two N, Finset.card_eq_zero.mp hS1_zero, Finset.empty_union]
  have h3not : 3 ∉ N.primeFactors := fun h => h3 (Nat.dvd_of_mem_primeFactors h)
  have hL_part : L = Q₀ ∪ Q₁ ∪ R := by
    ext r
    simp only [L, largeSources, Q₀, quarticSourcesZero, Q₁, quarticSourcesOne, R,
      Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
    constructor
    · intro ⟨hr, hr3, hrq, hge4⟩
      obtain ⟨k, hk⟩ := hev r hrq
      by_cases h4 : N.factorization r = 4
      · by_cases hm5 : r % 5 = 1
        · exact Or.inl (Or.inr ⟨⟨hrq, hr⟩, h4, hm5⟩)
        · exact Or.inl (Or.inl ⟨⟨hrq, hr⟩, h4, hm5⟩)
      · exact Or.inr ⟨⟨hr, hr3, hrq, hge4⟩, by omega⟩
    · rintro ((⟨⟨hrq, hr⟩, h4, _⟩ | ⟨⟨hrq, hr⟩, h4, _⟩) | ⟨⟨hr, hr3, hrq, hge4⟩, _⟩)
      · exact ⟨hr, fun h => by subst r; exact h3not hr, hrq, by omega⟩
      · exact ⟨hr, fun h => by subst r; exact h3not hr, hrq, by omega⟩
      · exact ⟨hr, hr3, hrq, hge4⟩
  have hdis_Q₀_Q₁ : Disjoint Q₀ Q₁ := by
    apply Finset.disjoint_left.mpr
    intro r h0 h1
    exact (Finset.mem_filter.mp h0).2.2 (Finset.mem_filter.mp h1).2.2
  have hdis_Q₀₁_R : Disjoint (Q₀ ∪ Q₁) R := by
    apply Finset.disjoint_left.mpr
    intro r h01 hr
    have h6 := (Finset.mem_filter.mp hr).2
    rcases Finset.mem_union.mp h01 with h0 | h1
    · have h4 := (Finset.mem_filter.mp h0).2.1
      omega
    · have h4 := (Finset.mem_filter.mp h1).2.1
      omega
  have hR_part : R = R₅ ∪ R₀ := by
    ext r
    simp only [R₅, R₀, Finset.mem_union, Finset.mem_filter]
    by_cases h : r % 5 = 1 <;> tauto
  have hdis_R : Disjoint R₅ R₀ := by
    apply Finset.disjoint_left.mpr
    intro r h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hSL_parts : N.primeFactors.erase q = S ∪ L := by
    ext r
    simp only [Finset.mem_erase, S, squareSources, L, largeSources, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hrq, hr⟩
      have hr3 : r ≠ 3 := fun h => by subst r; exact h3not hr
      have := hpos hr
      obtain ⟨k, hk⟩ := hev r hrq
      by_cases h2 : N.factorization r = 2
      · exact Or.inl ⟨hr, hr3, h2⟩
      · exact Or.inr ⟨hr, hr3, hrq, by omega⟩
    · rintro (⟨hr, _, h2⟩ | ⟨hr, _, hrq, _⟩)
      · exact ⟨fun h => by subst r; omega, hr⟩
      · exact ⟨hrq, hr⟩
  have hdis_SL : Disjoint S L := by
    apply Finset.disjoint_left.mpr
    intro r hs hl
    have h2 := (Finset.mem_filter.mp hs).2.2
    have h4 := (Finset.mem_filter.mp hl).2.2.2
    omega
  have hT5_sub : T₅ ⊆ insert q (S₅₁ ∪ (Q₁ ∪ R₅)) := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | h
    · exact Finset.mem_insert.mpr (Or.inl rfl)
    apply Finset.mem_insert_of_mem
    obtain ⟨hr_er, hm5⟩ := Finset.mem_filter.mp h
    rw [hSL_parts, Finset.mem_union] at hr_er
    rcases hr_er with hrS | hrL
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hrS, hm5⟩)
    · rw [hL_part, Finset.mem_union] at hrL
      rcases hrL with hrQ01 | hrR
      · rcases Finset.mem_union.mp hrQ01 with hrQ0 | hrQ1
        · exfalso
          exact (Finset.mem_filter.mp hrQ0).2.2 hm5
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ hrQ1)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hrR, hm5⟩))
  have hT5_high_sub : T₅_high ⊆ insert q (Q₁ ∪ R₅) := by
    intro r hr
    obtain ⟨hrT5, hrnS51⟩ := Finset.mem_sdiff.mp hr
    have hr_in := hT5_sub hrT5
    rcases Finset.mem_insert.mp hr_in with rfl | h
    · exact Finset.mem_insert.mpr (Or.inl rfl)
    · rcases Finset.mem_union.mp h with hrS51 | hrQ1R5
      · exact (hrnS51 hrS51).elim
      · exact Finset.mem_insert_of_mem hrQ1R5
  have hT5_high_card_le : T₅_high.card ≤ 1 + Q₁.card + R₅.card := by
    have hle := Finset.card_le_card hT5_high_sub
    have h1 := Finset.card_insert_le q (Q₁ ∪ R₅)
    have h2 := Finset.card_union_le Q₁ R₅
    omega
  have hdis_S51_Q1R5 : Disjoint S₅₁ (Q₁ ∪ R₅) := by
    apply Finset.disjoint_left.mpr
    intro r hrS hrQR
    have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hrS).1).2.2
    rcases Finset.mem_union.mp hrQR with hrQ1 | hrR5
    · have h4 := (Finset.mem_filter.mp hrQ1).2.1
      omega
    · have h6 := (Finset.mem_filter.mp (Finset.mem_filter.mp hrR5).1).2
      omega
  have hdis_Q1_R5 : Disjoint Q₁ R₅ := by
    apply Finset.disjoint_left.mpr
    intro r hrQ1 hrR5
    have h4 := (Finset.mem_filter.mp hrQ1).2.1
    have h6 := (Finset.mem_filter.mp (Finset.mem_filter.mp hrR5).1).2
    omega
  have hq_not_mem : q ∉ S₅₁ ∪ (Q₁ ∪ R₅) := by
    intro h
    rcases Finset.mem_union.mp h with hS | hQR
    · have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.2
      omega
    · rcases Finset.mem_union.mp hQR with hQ1 | hR5
      · exact (Finset.mem_erase.mp (Finset.mem_filter.mp hQ1).1).1 rfl
      · exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hR5).1).1).2.2.1 rfl
  have hT5_sum_le : ∑ r ∈ T₅, N.factorization r ≤
      N.factorization q + ∑ r ∈ S₅₁, N.factorization r +
        ∑ r ∈ Q₁, N.factorization r + ∑ r ∈ R₅, N.factorization r := by
    calc
      ∑ r ∈ T₅, N.factorization r
          ≤ ∑ r ∈ insert q (S₅₁ ∪ (Q₁ ∪ R₅)), N.factorization r :=
              Finset.sum_le_sum_of_subset hT5_sub
      _ = N.factorization q + (∑ r ∈ S₅₁, N.factorization r +
            (∑ r ∈ Q₁, N.factorization r + ∑ r ∈ R₅, N.factorization r)) := by
              rw [Finset.sum_insert hq_not_mem, Finset.sum_union hdis_S51_Q1R5,
                Finset.sum_union hdis_Q1_R5]
      _ = N.factorization q + ∑ r ∈ S₅₁, N.factorization r +
            ∑ r ∈ Q₁, N.factorization r + ∑ r ∈ R₅, N.factorization r := by
              ring
  have hS51_part : S₅₁ = A₁₂_₅₁ ∪ S₅₁_comp := by
    ext w
    simp only [A₁₂_₅₁, S₅₁_comp, Finset.mem_union, Finset.mem_filter]
    by_cases hp : (normalizedSquareSum w).Prime <;> tauto
  have hdis_A12_comp : Disjoint A₁₂_₅₁ S₅₁_comp :=
    Finset.disjoint_left.mpr fun w h1 h2 =>
      (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hS51_card : S₅₁.card = A₁₂_₅₁.card + S₅₁_comp.card := by
    rw [hS51_part, Finset.card_union_of_disjoint hdis_A12_comp]
  have hS51_sum : ∑ r ∈ S₅₁, N.factorization r = 2 * A₁₂_₅₁.card + 2 * S₅₁_comp.card := by
    calc
      ∑ r ∈ S₅₁, N.factorization r = ∑ _r ∈ S₅₁, (2 : ℕ) :=
        Finset.sum_congr rfl fun r hr => (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.2
      _ = 2 * S₅₁.card := by simp [Nat.mul_comm]
      _ = 2 * A₁₂_₅₁.card + 2 * S₅₁_comp.card := by rw [hS51_card]; ring
  have hQ5 := quarticSources_e2_capped_incidence ho hN hq h3
  change 5 * Q₀.card + 3 * Q₁.card ≤
    2 * (∑ r ∈ T₅, N.factorization r) + 2 * A₁₂_₅₁.card + 4 * S₅₁_comp.card + 4 * T₅_high.card
    at hQ5
  have h3inc := squareSources_vieta_root_slot_incidence_three_free ho hN hq hq4 he hev h3
  have hL1_sub : oneModThreeLargeSources N q ⊆ L := Finset.filter_subset _ _
  have hL1_card_le : (oneModThreeLargeSources N q).card ≤ L.card := Finset.card_le_card hL1_sub
  have hL1_sum_le : ∑ r ∈ oneModThreeLargeSources N q, N.factorization r ≤
      ∑ r ∈ L, N.factorization r := Finset.sum_le_sum_of_subset hL1_sub
  have hQ0_sum : ∑ r ∈ Q₀, N.factorization r = 4 * Q₀.card := by
    calc
      ∑ r ∈ Q₀, N.factorization r = ∑ _r ∈ Q₀, (4 : ℕ) :=
        Finset.sum_congr rfl fun r hr => (Finset.mem_filter.mp hr).2.1
      _ = 4 * Q₀.card := by simp [Nat.mul_comm]
  have hQ1_sum : ∑ r ∈ Q₁, N.factorization r = 4 * Q₁.card := by
    calc
      ∑ r ∈ Q₁, N.factorization r = ∑ _r ∈ Q₁, (4 : ℕ) :=
        Finset.sum_congr rfl fun r hr => (Finset.mem_filter.mp hr).2.1
      _ = 4 * Q₁.card := by simp [Nat.mul_comm]
  let ex₅ := ∑ r ∈ R₅, (N.factorization r - 6)
  let ex₀ := ∑ r ∈ R₀, (N.factorization r - 6)
  have hR5_sum : ∑ r ∈ R₅, N.factorization r = 6 * R₅.card + ex₅ := by
    have hadd : ∑ r ∈ R₅, N.factorization r = ∑ r ∈ R₅, (6 + (N.factorization r - 6)) := by
      refine Finset.sum_congr rfl fun r hr => ?_
      have hge6 : 6 ≤ N.factorization r := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2
      omega
    rw [hadd, Finset.sum_add_distrib]
    simp [Nat.mul_comm, ex₅]
  have hR0_sum : ∑ r ∈ R₀, N.factorization r = 6 * R₀.card + ex₀ := by
    have hadd : ∑ r ∈ R₀, N.factorization r = ∑ r ∈ R₀, (6 + (N.factorization r - 6)) := by
      refine Finset.sum_congr rfl fun r hr => ?_
      have hge6 : 6 ≤ N.factorization r := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2
      omega
    rw [hadd, Finset.sum_add_distrib]
    simp [Nat.mul_comm, ex₀]
  have hL_card : L.card = Q₀.card + Q₁.card + R₅.card + R₀.card := by
    rw [hL_part, Finset.card_union_of_disjoint hdis_Q₀₁_R,
      Finset.card_union_of_disjoint hdis_Q₀_Q₁, hR_part, Finset.card_union_of_disjoint hdis_R]
    ring
  have hL_sum : ∑ r ∈ L, N.factorization r =
      4 * Q₀.card + 4 * Q₁.card + 6 * R₅.card + 6 * R₀.card + ex₅ + ex₀ := by
    rw [hL_part, Finset.sum_union hdis_Q₀₁_R, Finset.sum_union hdis_Q₀_Q₁,
      hQ0_sum, hQ1_sum, hR_part, Finset.sum_union hdis_R, hR5_sum, hR0_sum]
    ring
  have hS_sum : ∑ r ∈ S, N.factorization r = 2 * S.card := by
    calc
      ∑ r ∈ S, N.factorization r = ∑ _r ∈ S, (2 : ℕ) :=
        Finset.sum_congr rfl fun r hr => (Finset.mem_filter.mp hr).2.2
      _ = 2 * S.card := by simp [Nat.mul_comm]
  have hcard_tot : N.primeFactors.card = 1 + S.card + L.card := by
    have := Finset.card_erase_add_one hq
    rw [hSL_parts, Finset.card_union_of_disjoint hdis_SL] at this
    omega
  have htot : N.primeFactorsList.length =
      N.factorization q + 2 * S.card + ∑ r ∈ L, N.factorization r := by
    have htot1 : N.primeFactorsList.length =
        N.factorization q + ∑ r ∈ N.primeFactors.erase q, N.factorization r := by
      rw [← cardFactors_apply, cardFactors_eq_sum_factorization]
      exact (Finset.add_sum_erase N.primeFactors _ hq).symm
    rw [hSL_parts, Finset.sum_union hdis_SL, hS_sum] at htot1
    omega
  have hQ1_le_five : Q₁.card ≤ N.factorization 5 :=
    quarticSourcesOne_card_le_five_exponent (N := N) (q := q) hN
  have hfive_bound : N.factorization 5 ≤ N.factorization q + 6 + ex₀ := by
    by_cases h5N : 5 ∈ N.primeFactors
    · by_cases h5q : 5 = q
      · rw [h5q]
        omega
      · have h5er : 5 ∈ N.primeFactors.erase q := Finset.mem_erase.mpr ⟨h5q, h5N⟩
        rw [hSL_parts, Finset.mem_union] at h5er
        rcases h5er with h5S | h5L
        · have h2 := (Finset.mem_filter.mp h5S).2.2
          omega
        · rw [hL_part, Finset.mem_union] at h5L
          rcases h5L with h5Q | h5R
          · rcases Finset.mem_union.mp h5Q with h5Q0 | h5Q1
            · have h4 := (Finset.mem_filter.mp h5Q0).2.1
              omega
            · have hm5 : 5 % 5 = 1 := (Finset.mem_filter.mp h5Q1).2.2
              omega
          · rw [hR_part, Finset.mem_union] at h5R
            rcases h5R with h5R5 | h5R0
            · have hm5 : 5 % 5 = 1 := (Finset.mem_filter.mp h5R5).2
              omega
            · have hge6 : 6 ≤ N.factorization 5 :=
                (Finset.mem_filter.mp (Finset.mem_filter.mp h5R0).1).2
              have hle_ex : N.factorization 5 - 6 ≤ ex₀ :=
                Finset.single_le_sum (f := fun r => N.factorization r - 6)
                  (fun _ _ => Nat.zero_le _) h5R0
              omega
    · have hz : N.factorization 5 = 0 := Finsupp.notMem_support_iff.mp h5N
      omega
  have hQ1_bound : Q₁.card ≤ N.factorization q + 6 + ex₀ := hQ1_le_five.trans hfive_bound
  have hS_bound : 3 * S.card ≤
      2 + N.factorization q + 6 * Q₀.card + 6 * Q₁.card +
        8 * R₅.card + 8 * R₀.card + ex₅ + ex₀ := by
    rw [← hS_eq_S2] at h3inc
    linarith [h3inc, hL1_card_le, hL1_sum_le, hL_card, hL_sum]
  have hQ5_bound : 5 * Q₀.card + 3 * Q₁.card ≤
      4 + 2 * N.factorization q + 6 * A₁₂_₅₁.card + 8 * S₅₁_comp.card +
        12 * Q₁.card + 16 * R₅.card + 2 * ex₅ := by
    linarith [hQ5, hT5_sum_le, hS51_sum, hQ1_sum, hR5_sum, hT5_high_card_le]
  have hA12_eq :
      A₁₂_₅₁ = (squareSources N).filter (fun w => w % 5 = 1 ∧ (normalizedSquareSum w).Prime) := by
    ext w
    simp only [A₁₂_₅₁, S₅₁, S, Finset.mem_filter, and_assoc]
  have hcomp_eq :
      S₅₁_comp = (squareSources N).filter (fun w => w % 5 = 1 ∧ ¬ (normalizedSquareSum w).Prime) := by
    ext w
    simp only [S₅₁_comp, S₅₁, S, Finset.mem_filter, and_assoc]
  rw [← hA12_eq, ← hcomp_eq]
  change 409 * N.primeFactors.card ≤
    149 * N.primeFactorsList.length + 1099 + 42 * A₁₂_₅₁.card + 56 * S₅₁_comp.card
  linarith [hS_bound, hQ5_bound, hQ1_bound, hcard_tot, hL_card, htot, hL_sum]

/-- Simplified `5`-unconditional `409/149` slope aggregating all `w ∈ (squareSources N).filter (· % 5 = 1)`
with weight `56`. -/
theorem multi_block_coupled_three_free_uncond_five_simple {N : ℕ} (ho : Odd N) (hN : N.Perfect)
    (h3 : ¬ 3 ∣ N) :
    409 * N.primeFactors.card ≤
      149 * N.primeFactorsList.length + 1099 +
        56 * ((squareSources N).filter (· % 5 = 1)).card := by
  have h := multi_block_coupled_three_free_uncond_five ho hN h3
  let S₅₁ := (squareSources N).filter (· % 5 = 1)
  let A₁₂ := S₅₁.filter (fun w => (normalizedSquareSum w).Prime)
  let S_comp := S₅₁.filter (fun w => ¬ (normalizedSquareSum w).Prime)
  have hpart : S₅₁ = A₁₂ ∪ S_comp := by
    ext w
    simp only [S₅₁, A₁₂, S_comp, Finset.mem_union, Finset.mem_filter]
    by_cases hp : (normalizedSquareSum w).Prime <;> tauto
  have hdis : Disjoint A₁₂ S_comp :=
    Finset.disjoint_left.mpr fun w h1 h2 =>
      (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hcard : S₅₁.card = A₁₂.card + S_comp.card := by
    rw [hpart, Finset.card_union_of_disjoint hdis]
  have hA_eq :
      A₁₂ = (squareSources N).filter (fun w => w % 5 = 1 ∧ (normalizedSquareSum w).Prime) := by
    ext w
    simp only [A₁₂, S₅₁, Finset.mem_filter, and_assoc]
  have hC_eq :
      S_comp = (squareSources N).filter (fun w => w % 5 = 1 ∧ ¬ (normalizedSquareSum w).Prime) := by
    ext w
    simp only [S_comp, S₅₁, Finset.mem_filter, and_assoc]
  rw [← hA_eq, ← hC_eq] at h
  change 409 * N.primeFactors.card ≤ 149 * N.primeFactorsList.length + 1099 + 56 * S₅₁.card
  omega

/-- When `¬ 3 ∣ N` and `(squareSources N).filter (· % 5 = 1) = ∅`,
`409 * ω(N) ≤ 149 * Ω(N) + 1099` holds unconditionally even when `5 ∣ N`. -/
theorem multi_block_slope_three_free_uncond_five_of_S51_empty {N : ℕ} (ho : Odd N) (hN : N.Perfect)
    (h3 : ¬ 3 ∣ N) (hempty : (squareSources N).filter (· % 5 = 1) = ∅) :
    409 * N.primeFactors.card ≤ 149 * N.primeFactorsList.length + 1099 := by
  have h := multi_block_coupled_three_free_uncond_five_simple ho hN h3
  rw [hempty, Finset.card_empty, mul_zero, add_zero] at h
  exact h

/-! ## 5. Zelinsky (2021) `302/113` and `66/25` Reductions & Density/Slack Closures -/

/-- Under `¬ 3 ∣ N`, the `5`-unconditional `409/149` slope yields Zelinsky's (2021)
`302 * ω(N) ≤ 113 * Ω(N) + 286` whenever `6328 * |S₅₁| + 81573 ≤ 1219 * ω(N)`. -/
theorem zelinsky_302_113_of_S51_bound {N : ℕ} (ho : Odd N) (hN : N.Perfect) (h3 : ¬ 3 ∣ N)
    (hS51 : 6328 * ((squareSources N).filter (· % 5 = 1)).card + 81573 ≤
      1219 * N.primeFactors.card) :
    302 * N.primeFactors.card ≤ 113 * N.primeFactorsList.length + 286 := by
  have h := multi_block_coupled_three_free_uncond_five_simple ho hN h3
  omega

/-- Under `¬ 3 ∣ N`, `sharpened_cyclotomic_slope_three_free` yields Zelinsky's (2021)
`302 * ω(N) ≤ 113 * Ω(N) + 286` whenever `2 * ω(N) ≤ 452 * |twoModThreeLargeSources N q| + 67`. -/
theorem zelinsky_302_113_of_twoModThreeLarge_density {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r, r ≠ q → Even (N.factorization r)) (h3 : ¬ 3 ∣ N)
    (hdens : 2 * N.primeFactors.card ≤ 452 * (twoModThreeLargeSources N q).card + 67) :
    302 * N.primeFactors.card ≤ 113 * N.primeFactorsList.length + 286 := by
  have h := (sharpened_cyclotomic_slope_three_free ho hN hq hq4 he hev h3).2
  omega

/-- Unconditionally (whether `3 ∣ N` or not), `sharpened_cyclotomic_prime_factor_count` yields
Zelinsky's (2021) `66 * ω(N) ≤ 25 * Ω(N) + 125` whenever
`3 * ω(N) ≤ 275 * |twoModThreeLargeSources N q| + 25`. -/
theorem zelinsky_66_25_of_twoModThreeLarge_density {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r, r ≠ q → Even (N.factorization r))
    (hdens : 3 * N.primeFactors.card ≤ 275 * (twoModThreeLargeSources N q).card + 25) :
    66 * N.primeFactors.card ≤ 25 * N.primeFactorsList.length + 125 := by
  have h := sharpened_cyclotomic_prime_factor_count ho hN hq hq4 he hev
  omega

/-- Combined Zelinsky (2021) `302/113` (`¬ 3 ∣ N`) and `66/25` (`3 ∣ N`) slope and least-prime
logarithmic/exponential pinch discharge under the residual Triple-Threat / large-source slack
hypotheses. -/
theorem zelinsky_302_113_and_66_25_of_triple_threat_discharge {N p q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) (hmin : ∀ s ∈ N.primeFactors, p ≤ s)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r, r ≠ q → Even (N.factorization r))
    (hno3_slack : ¬ 3 ∣ N →
      6 * N.primeFactors.card ≤
        1356 * (twoModThreeLargeSources N q).card +
          226 * (squareSourcesSemiprimeTwo N).card + 201)
    (h3_slack : 3 ∣ N →
      3 * N.primeFactors.card ≤ 275 * (twoModThreeLargeSources N q).card + 25) :
    (¬ 3 ∣ N →
      302 * N.primeFactors.card ≤ 113 * N.primeFactorsList.length + 286 ∧
        (302 * ((p : ℝ) - 1) * Real.log 2 - 286) / 113 < (N.primeFactorsList.length : ℝ) ∧
        p ^ N.primeFactorsList.length ≤ N) ∧
    (3 ∣ N →
      66 * N.primeFactors.card ≤ 25 * N.primeFactorsList.length + 125 ∧
        (66 * ((p : ℝ) - 1) * Real.log 2 - 125) / 25 < (N.primeFactorsList.length : ℝ) ∧
        p ^ N.primeFactorsList.length ≤ N) := by
  refine ⟨?_, ?_⟩
  · intro hno3
    have hcyc := (sharpened_cyclotomic_slope_three_free ho hN hq hq4 he hev hno3).1
    have hsl := hno3_slack hno3
    have h302 : 302 * N.primeFactors.card ≤ 113 * N.primeFactorsList.length + 286 := by omega
    have hpinch := zelinsky_slope_302_113_envelope ho hN hp hmin h302
    exact ⟨h302, hpinch.1, hpinch.2⟩
  · intro h3
    have h66 := zelinsky_66_25_of_twoModThreeLarge_density ho hN hq hq4 he hev (h3_slack h3)
    have hpinch := zelinsky_slope_66_25_envelope ho hN hp hmin h66
    exact ⟨h66, hpinch.1, hpinch.2⟩

end OddPerfect
