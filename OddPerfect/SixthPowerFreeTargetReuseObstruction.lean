module

public import OddPerfect.QuarticChainBaselineAndReuse
public import OddPerfect.GlobalTier2WaveKObstruction
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Sixth-Power-Free Prime-Target Reuse Obstruction (`OddPerfect.SixthPowerFreeTargetReuseObstruction`)

Formalizes:
1. Supporting root-counting and non-square lemmas:
   - `not_isSquare_quartic_sigma` (`u ≥ 2`, `u ≠ 3`; note `u = 3` gives `121 = 11 ^ 2`)
   - `quarticChainIntermediate_unique_prime_source_lt`
   - `sq_add_self_add_one_no_odd_roots_lt_of_quarticFirstFactor_prime`
   - `card_range_two_mod_three_dvd_sq_add_self_add_one_le_one`
2. Zero-loss `Q → S₅₁_col` bound `sixth_power_free_quartic_to_S51_col_bound`
   (`Q₁₃.card + 2 * Q₂₃.card ≤ 2 * S₅₁_col.card`).
3. Full fine block conservation (`E1..E4`), non-cube block invariants (`U_*`),
   upward target-reuse bounds (`U_up_Phi3_TA1`, `U_up_A_TSp2`), and Farkas-dual
   global consequences:
   - `sixth_power_free_prime_target_reuse_obstruction`
   - `sixth_power_free_prime_target_reuse_master_profile`
   - `no_sixth_power_free_odd_perfect_of_assessment_regime`
4. Explicit separation & surviving count-family theorems:
   - `SatisfiesWaveKAndSlackBounds` and `SatisfiesTargetReuseBounds`
   - `assessment_count_family_passes_waveK_fails_target_reuse`
   - `high_Q23_count_family_passes_waveK_fails_target_reuse`
   - `low_collision_count_family_passes_waveK_fails_target_reuse`
   - `surviving_square_ramified_count_family_satisfies_all`
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

private theorem sigma_one_prime_local {p : ℕ} (hp : p.Prime) : sigma 1 p = p + 1 := by
  rw [← pow_one p, sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

private theorem sigma_one_sq_local {p : ℕ} (hp : p.Prime) : sigma 1 (p ^ 2) = p ^ 2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

private theorem sigma_one_four_local {p : ℕ} (hp : p.Prime) :
    sigma 1 (p ^ 4) = p ^ 4 + p ^ 3 + p ^ 2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

private theorem odd_factor_of_nonsquare_local {a : ℕ} (ha : ¬ IsSquare a) :
    ∃ p, p.Prime ∧ Odd (a.factorization p) := by
  by_contra! h
  exact ha (Nat.isSquare_iff_even_factorization.mpr h)

/-! ## 1. Supporting Root & Nonsquare Lemmas -/

/-- `u ^ 4 + u ^ 3 + u ^ 2 + u + 1` is never a square for `2 ≤ u` with `u ≠ 3`
(note `3 ^ 4 + 3 ^ 3 + 3 ^ 2 + 3 + 1 = 121 = 11 ^ 2`). -/
theorem not_isSquare_quartic_sigma {u : ℕ} (hu : 2 ≤ u) (hu3 : u ≠ 3) :
    ¬ IsSquare (u ^ 4 + u ^ 3 + u ^ 2 + u + 1) := by
  rcases (by omega : u = 2 ∨ 4 ≤ u) with rfl | hu4
  · rintro ⟨y, hy⟩
    exact Nat.not_exists_sq' (m := 5) (n := 31) (by decide) (by decide)
      ⟨y, by simpa [pow_two] using hy.symm⟩
  · obtain ⟨k, rfl⟩ : ∃ k, u = 4 + k := Nat.exists_eq_add_of_le hu4
    have hlo : (2 * (4 + k) ^ 2 + (4 + k)) ^ 2 <
        4 * ((4 + k) ^ 4 + (4 + k) ^ 3 + (4 + k) ^ 2 + (4 + k) + 1) := by
      ring_nf
      omega
    have hhi : 4 * ((4 + k) ^ 4 + (4 + k) ^ 3 + (4 + k) ^ 2 + (4 + k) + 1) <
        (2 * (4 + k) ^ 2 + (4 + k) + 1) ^ 2 := by
      ring_nf
      omega
    rintro ⟨y, hy⟩
    exact Nat.not_exists_sq' hlo hhi ⟨2 * y, by rw [hy]; ring⟩

/-- If `w` and `s := quarticPoly w` are both prime, then `w` is the unique prime `u < s`
with `s ∣ quarticPoly u`. -/
theorem quarticChainIntermediate_unique_prime_source_lt {w : ℕ}
    (hw : w.Prime) (hs : (quarticPoly w).Prime) :
    ((Finset.range (quarticPoly w)).filter
      (fun u => u.Prime ∧ quarticPoly w ∣ quarticPoly u)) ⊆ {w} := by
  let s := quarticPoly w
  change ((Finset.range s).filter (fun u => u.Prime ∧ s ∣ quarticPoly u)) ⊆ {w}
  have hw2 : 2 ≤ w := hw.two_le
  have hw_lt2 : w < w ^ 2 := by nlinarith
  have hw2_lt3 : w ^ 2 < w ^ 3 := by nlinarith
  have hw3_lt4 : w ^ 3 < w ^ 4 := by nlinarith
  have hw4_lt_s : w ^ 4 < s := by dsimp [s, quarticPoly]; omega
  let : Fact s.Prime := ⟨hs⟩
  let P : Polynomial (ZMod s) :=
    Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + Polynomial.C 1
  have hP_deg : P.natDegree ≤ 4 := by
    dsimp [P]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by simp))
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by simp))
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by simp))
    refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) (by simp))
  have hP_ne0 : P ≠ 0 := by
    intro h0
    have hc := congrArg (fun Q : Polynomial (ZMod s) => Q.coeff 4) h0
    simp only [P, Polynomial.coeff_zero, Polynomial.coeff_add, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C] at hc
    norm_num at hc
  have hroots_le : P.roots.toFinset.card ≤ 4 :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' P).trans hP_deg)
  let S := (Finset.range s).filter (fun u => s ∣ quarticPoly u)
  have hS_le4 : S.card ≤ 4 := by
    have hle : S.card ≤ P.roots.toFinset.card := by
      refine Finset.card_le_card_of_injOn (fun u : ℕ => (u : ZMod s)) ?_ ?_
      · intro u hu
        obtain ⟨_, hu_dvd⟩ := Finset.mem_filter.mp hu
        have hz : ((quarticPoly u : ℕ) : ZMod s) = 0 :=
          (ZMod.natCast_eq_zero_iff (quarticPoly u) s).mpr hu_dvd
        dsimp [quarticPoly] at hz
        push_cast at hz
        have hroot : P.IsRoot (u : ZMod s) := by
          rw [Polynomial.IsRoot]
          simp only [P, Polynomial.eval_add, Polynomial.eval_pow,
            Polynomial.eval_X, Polynomial.eval_C]
          exact hz
        exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP_ne0).mpr hroot)
      · intro u₁ hu₁ u₂ hu₂ heq
        have h1 : u₁ < s := Finset.mem_range.mp (Finset.mem_filter.mp hu₁).1
        have h2 : u₂ < s := Finset.mem_range.mp (Finset.mem_filter.mp hu₂).1
        have hval := congrArg ZMod.val heq
        rwa [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at hval
    exact hle.trans hroots_le
  have hw5 : (w : ZMod s) ^ 5 = 1 := by
    have hs_z : (s : ZMod s) = 0 := ZMod.natCast_self s
    have hsum_z : (w : ZMod s) ^ 4 + (w : ZMod s) ^ 3 + (w : ZMod s) ^ 2 + (w : ZMod s) + 1 = 0 := by
      have hc : ((quarticPoly w : ℕ) : ZMod s) = 0 := hs_z
      dsimp [quarticPoly] at hc
      push_cast at hc
      exact hc
    have hmul0 : ((w : ZMod s) - 1) *
        ((w : ZMod s) ^ 4 + (w : ZMod s) ^ 3 + (w : ZMod s) ^ 2 + (w : ZMod s) + 1) = 0 := by
      rw [hsum_z, mul_zero]
    have hpow0 : (w : ZMod s) ^ 5 - 1 = 0 := by
      calc
        (w : ZMod s) ^ 5 - 1
            = ((w : ZMod s) - 1) *
                ((w : ZMod s) ^ 4 + (w : ZMod s) ^ 3 + (w : ZMod s) ^ 2 + (w : ZMod s) + 1) := by
              ring
        _ = 0 := hmul0
    exact sub_eq_zero.mp hpow0
  have hdvd_pow : ∀ j : ℕ, 1 < w ^ j → w ^ j < s → s ∣ quarticPoly (w ^ j) := by
    intro j h1 hlt
    have hne1 : ((w ^ j : ℕ) : ZMod s) - 1 ≠ 0 := by
      intro heq
      have h1' : ((w ^ j : ℕ) : ZMod s) = ((1 : ℕ) : ZMod s) := by
        simpa using sub_eq_zero.mp heq
      have hval := congrArg ZMod.val h1'
      rw [ZMod.val_natCast_of_lt hlt, ZMod.val_natCast_of_lt hs.one_lt] at hval
      omega
    have hprod0 : (((w ^ j : ℕ) : ZMod s) - 1) * ((quarticPoly (w ^ j) : ℕ) : ZMod s) = 0 := by
      dsimp [quarticPoly]
      push_cast
      calc
        ((w : ZMod s) ^ j - 1) *
            (((w : ZMod s) ^ j) ^ 4 + ((w : ZMod s) ^ j) ^ 3 +
              ((w : ZMod s) ^ j) ^ 2 + (w : ZMod s) ^ j + 1)
            = ((w : ZMod s) ^ j) ^ 5 - 1 := by ring
        _ = ((w : ZMod s) ^ 5) ^ j - 1 := by ring
        _ = 1 ^ j - 1 := by rw [hw5]
        _ = 0 := by simp
    have hzero : ((quarticPoly (w ^ j) : ℕ) : ZMod s) = 0 :=
      (mul_eq_zero.mp hprod0).resolve_left hne1
    exact (ZMod.natCast_eq_zero_iff (quarticPoly (w ^ j)) s).mp hzero
  let R : Finset ℕ := {w, w ^ 2, w ^ 3, w ^ 4}
  have hR_sub : R ⊆ S := by
    intro u hu
    simp only [R, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), dvd_rfl⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hdvd_pow 2 (by omega) (by omega)⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hdvd_pow 3 (by omega) (by omega)⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hw4_lt_s, hdvd_pow 4 (by omega) hw4_lt_s⟩
  have hR_card : R.card = 4 := by
    have h34 : w ^ 3 ∉ ({w ^ 4} : Finset ℕ) := by simp; omega
    have h234 : w ^ 2 ∉ ({w ^ 3, w ^ 4} : Finset ℕ) := by simp; omega
    have h1234 : w ∉ ({w ^ 2, w ^ 3, w ^ 4} : Finset ℕ) := by simp; omega
    rw [Finset.card_insert_of_notMem h1234, Finset.card_insert_of_notMem h234,
      Finset.card_insert_of_notMem h34, Finset.card_singleton]
  have hR_eq : R = S := Finset.eq_of_subset_of_card_le hR_sub (by omega)
  have hnot_prime_pow : ∀ j : ℕ, 2 ≤ j → ¬ (w ^ j).Prime := by
    intro j hj hp
    have hdvd : w ∣ w ^ j := dvd_pow_self w (by omega)
    rcases hp.eq_one_or_self_of_dvd w hdvd with h1 | heq
    · omega
    · have hle : w ^ 2 ≤ w ^ j := Nat.pow_le_pow_right hw.pos hj
      omega
  intro u hu
  obtain ⟨hu_range, hu_prime, hu_dvd⟩ := Finset.mem_filter.mp hu
  have hu_S : u ∈ S := Finset.mem_filter.mpr ⟨hu_range, hu_dvd⟩
  rw [← hR_eq] at hu_S
  simp only [R, Finset.mem_insert, Finset.mem_singleton] at hu_S
  rcases hu_S with rfl | rfl | rfl | rfl
  · exact Finset.mem_singleton_self _
  · exact absurd hu_prime (hnot_prime_pow 2 (by decide))
  · exact absurd hu_prime (hnot_prime_pow 3 (by decide))
  · exact absurd hu_prime (hnot_prime_pow 4 (by decide))

/-- When `w` is odd (`3 ≤ w`) and `t := quarticFirstFactor w` is prime, the only two roots of
`s ^ 2 + s + 1 ≡ 0 (mod t)` in `Finset.range t` are `w - 1` and `(w - 1) ^ 2`, both even. -/
theorem sq_add_self_add_one_no_odd_roots_lt_of_quarticFirstFactor_prime {w : ℕ}
    (hw_odd : Odd w) (hw3 : 3 ≤ w) (ht : (quarticFirstFactor w).Prime) :
    ((Finset.range (quarticFirstFactor w)).filter
      (fun s => Odd s ∧ quarticFirstFactor w ∣ s ^ 2 + s + 1)) = ∅ := by
  let t := quarticFirstFactor w
  change ((Finset.range t).filter (fun s => Odd s ∧ t ∣ s ^ 2 + s + 1)) = ∅
  let : Fact t.Prime := ⟨ht⟩
  let P : Polynomial (ZMod t) := Polynomial.X ^ 2 + Polynomial.X + Polynomial.C 1
  have hP_deg : P.natDegree ≤ 2 := by
    dsimp [P]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by simp))
    exact (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) (by simp))
  have hP_ne0 : P ≠ 0 := by
    intro h0
    have hc := congrArg (fun Q : Polynomial (ZMod t) => Q.coeff 2) h0
    simp only [P, Polynomial.coeff_zero, Polynomial.coeff_add, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C] at hc
    norm_num at hc
  have hroots_le : P.roots.toFinset.card ≤ 2 :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' P).trans hP_deg)
  let S := (Finset.range t).filter (fun s => t ∣ s ^ 2 + s + 1)
  have hS_le2 : S.card ≤ 2 := by
    have hle : S.card ≤ P.roots.toFinset.card := by
      refine Finset.card_le_card_of_injOn (fun s : ℕ => (s : ZMod t)) ?_ ?_
      · intro s hs
        obtain ⟨_, hs_dvd⟩ := Finset.mem_filter.mp hs
        have hz : ((s ^ 2 + s + 1 : ℕ) : ZMod t) = 0 :=
          (ZMod.natCast_eq_zero_iff (s ^ 2 + s + 1) t).mpr hs_dvd
        push_cast at hz
        have hroot : P.IsRoot (s : ZMod t) := by
          rw [Polynomial.IsRoot]
          simp only [P, Polynomial.eval_add, Polynomial.eval_pow,
            Polynomial.eval_X, Polynomial.eval_C]
          exact hz
        exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP_ne0).mpr hroot)
      · intro s₁ hs₁ s₂ hs₂ heq
        have h1 : s₁ < t := Finset.mem_range.mp (Finset.mem_filter.mp hs₁).1
        have h2 : s₂ < t := Finset.mem_range.mp (Finset.mem_filter.mp hs₂).1
        have hval := congrArg ZMod.val heq
        rwa [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at hval
    exact hle.trans hroots_le
  let r₁ := w - 1
  let r₂ := (w - 1) ^ 2
  have hr₁_lt : r₁ < r₂ := by
    dsimp [r₁, r₂]
    have h1 : 2 ≤ w - 1 := by omega
    nlinarith
  have hr₂_lt : r₂ < t := by
    dsimp [r₂, t, quarticFirstFactor]
    have hle : w ≤ w ^ 2 := Nat.le_self_pow (by decide : 2 ≠ 0) w
    zify [(by omega : 1 ≤ w), hle]
    nlinarith
  have hr₁_dvd : t ∣ r₁ ^ 2 + r₁ + 1 := by
    have heq : r₁ ^ 2 + r₁ + 1 = t := by
      dsimp [r₁, t, quarticFirstFactor]
      have hle : w ≤ w ^ 2 := Nat.le_self_pow (by decide : 2 ≠ 0) w
      zify [(by omega : 1 ≤ w), hle]
      ring
    rw [heq]
  have hr₂_dvd : t ∣ r₂ ^ 2 + r₂ + 1 := by
    have heq : r₂ ^ 2 + r₂ + 1 = (w ^ 2 - 3 * w + 3) * t := by
      dsimp [r₂, t, quarticFirstFactor]
      have hle1 : 1 ≤ w := by omega
      have hle2 : w ≤ w ^ 2 := Nat.le_self_pow (by decide : 2 ≠ 0) w
      have hle3 : 3 * w ≤ w ^ 2 := by nlinarith
      zify [hle1, hle2, hle3]
      ring
    rw [heq]
    exact dvd_mul_left t _
  have hsub : ({r₁, r₂} : Finset ℕ) ⊆ S := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hr₁_dvd⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr₂_lt, hr₂_dvd⟩
  have hcard_pair : ({r₁, r₂} : Finset ℕ).card = 2 := Finset.card_pair hr₁_lt.ne
  have hS_eq : ({r₁, r₂} : Finset ℕ) = S := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hr₁_even : ¬ Odd r₁ := by
    obtain ⟨k, hk⟩ := hw_odd
    rw [Nat.not_odd_iff_even]
    exact ⟨k, by dsimp [r₁]; omega⟩
  have hr₂_even : ¬ Odd r₂ := by
    rw [Nat.not_odd_iff_even]
    have hr₁_ev : Even r₁ := Nat.not_odd_iff_even.mp hr₁_even
    exact hr₁_ev.pow_of_ne_zero (by decide)
  rw [Finset.eq_empty_iff_forall_notMem]
  intro s hs
  obtain ⟨hs_range, hs_odd, hs_dvd⟩ := Finset.mem_filter.mp hs
  have hs_S : s ∈ S := Finset.mem_filter.mpr ⟨hs_range, hs_dvd⟩
  rw [← hS_eq] at hs_S
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs_S
  rcases hs_S with rfl | rfl
  · exact hr₁_even hs_odd
  · exact hr₂_even hs_odd

/-- If `t` is prime and `t % 3 = 1`, there is at most one `s < t` with `s % 3 = 2` and
`t ∣ s ^ 2 + s + 1`. -/
theorem card_range_two_mod_three_dvd_sq_add_self_add_one_le_one {t : ℕ}
    (ht : t.Prime) (ht3 : t % 3 = 1) :
    ((Finset.range t).filter (fun s => s % 3 = 2 ∧ t ∣ s ^ 2 + s + 1)).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro s₁ hs₁ s₂ hs₂
  obtain ⟨hr₁, hm₁, hd₁⟩ := Finset.mem_filter.mp hs₁
  obtain ⟨hr₂, hm₂, hd₂⟩ := Finset.mem_filter.mp hs₂
  have h1_lt : s₁ < t := Finset.mem_range.mp hr₁
  have h2_lt : s₂ < t := Finset.mem_range.mp hr₂
  let : Fact t.Prime := ⟨ht⟩
  have hz1 : ((s₁ ^ 2 + s₁ + 1 : ℕ) : ZMod t) = 0 :=
    (ZMod.natCast_eq_zero_iff (s₁ ^ 2 + s₁ + 1) t).mpr hd₁
  have hz2 : ((s₂ ^ 2 + s₂ + 1 : ℕ) : ZMod t) = 0 :=
    (ZMod.natCast_eq_zero_iff (s₂ ^ 2 + s₂ + 1) t).mpr hd₂
  push_cast at hz1 hz2
  have hprod : ((s₁ : ZMod t) - (s₂ : ZMod t)) * ((s₁ : ZMod t) + (s₂ : ZMod t) + 1) = 0 := by
    calc
      ((s₁ : ZMod t) - (s₂ : ZMod t)) * ((s₁ : ZMod t) + (s₂ : ZMod t) + 1)
          = ((s₁ : ZMod t) ^ 2 + (s₁ : ZMod t) + 1) -
              ((s₂ : ZMod t) ^ 2 + (s₂ : ZMod t) + 1) := by ring
      _ = 0 - 0 := by rw [hz1, hz2]
      _ = 0 := sub_zero 0
  rcases mul_eq_zero.mp hprod with hsub | hsum
  · have heq : (s₁ : ZMod t) = (s₂ : ZMod t) := sub_eq_zero.mp hsub
    have hval := congrArg ZMod.val heq
    rwa [ZMod.val_natCast_of_lt h1_lt, ZMod.val_natCast_of_lt h2_lt] at hval
  · exfalso
    have heq : ((s₁ + s₂ + 1 : ℕ) : ZMod t) = 0 := by
      push_cast
      exact hsum
    have hdvd : t ∣ s₁ + s₂ + 1 := (ZMod.natCast_eq_zero_iff (s₁ + s₂ + 1) t).mp heq
    obtain ⟨k, hk⟩ := hdvd
    have hk_pos : 1 ≤ k := by
      by_contra! hk0
      have : k = 0 := by omega
      rw [this, mul_zero] at hk
      omega
    have hk_lt2 : k < 2 := by
      by_contra! hk2
      have hge : 2 * t ≤ t * k := by
        calc 2 * t = t * 2 := by ring
          _ ≤ t * k := Nat.mul_le_mul_left t hk2
      omega
    have hk1 : k = 1 := by omega
    rw [hk1, mul_one] at hk
    omega

/-! ## 2. Shared Invariants, `expCount` Helpers, and `Q → S₅₁_col` Bound -/

private theorem expCount_mul_of_coprime {A B j : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hcop : A.Coprime B) (_hj : 1 ≤ j) :
    expCount (A * B) j = expCount A j + expCount B j := by
  unfold expCount
  have hpf : (A * B).primeFactors = A.primeFactors ∪ B.primeFactors :=
    Nat.primeFactors_mul hA hB
  have hdisj_pf : Disjoint A.primeFactors B.primeFactors := hcop.disjoint_primeFactors
  have hfac : ∀ r, (A * B).factorization r = A.factorization r + B.factorization r := fun r => by
    rw [Nat.factorization_mul hA hB, Finsupp.add_apply]
  have hA_filt : (A * B).primeFactors.filter (fun r => (A * B).factorization r = j) =
      A.primeFactors.filter (fun r => A.factorization r = j) ∪
        B.primeFactors.filter (fun r => B.factorization r = j) := by
    ext r
    simp only [hpf, Finset.mem_filter, Finset.mem_union, hfac]
    constructor
    · rintro ⟨hrA | hrB, hrj⟩
      · left
        have hrnotB : r ∉ B.primeFactors := Finset.disjoint_left.mp hdisj_pf hrA
        have hB0 : B.factorization r = 0 := Finsupp.notMem_support_iff.mp hrnotB
        exact ⟨hrA, by omega⟩
      · right
        have hrnotA : r ∉ A.primeFactors := Finset.disjoint_right.mp hdisj_pf hrB
        have hA0 : A.factorization r = 0 := Finsupp.notMem_support_iff.mp hrnotA
        exact ⟨hrB, by omega⟩
    · rintro (⟨hrA, hrj⟩ | ⟨hrB, hrj⟩)
      · have hrnotB : r ∉ B.primeFactors := Finset.disjoint_left.mp hdisj_pf hrA
        have hB0 : B.factorization r = 0 := Finsupp.notMem_support_iff.mp hrnotB
        exact ⟨Or.inl hrA, by omega⟩
      · have hrnotA : r ∉ A.primeFactors := Finset.disjoint_right.mp hdisj_pf hrB
        have hA0 : A.factorization r = 0 := Finsupp.notMem_support_iff.mp hrnotA
        exact ⟨Or.inr hrB, by omega⟩
  have hdisj_filt : Disjoint
      (A.primeFactors.filter (fun r => A.factorization r = j))
      (B.primeFactors.filter (fun r => B.factorization r = j)) :=
    hdisj_pf.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  rw [hA_filt, Finset.card_union_of_disjoint hdisj_filt]

private theorem expCount_eq_sum_indicator_of_subset {M j : ℕ} {T : Finset ℕ}
    (_hM0 : M ≠ 0) (hj : 1 ≤ j) (hsub : M.primeFactors ⊆ T) :
    expCount M j = ∑ r ∈ T, (if M.factorization r = j then 1 else 0) := by
  unfold expCount
  have hfilt : M.primeFactors.filter (fun r => M.factorization r = j) =
      T.filter (fun r => M.factorization r = j) := by
    ext r
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hrM, hrj⟩
      exact ⟨hsub hrM, hrj⟩
    · rintro ⟨_, hrj⟩
      have hr_pos : 0 < M.factorization r := by omega
      have hrM : r ∈ M.primeFactors := Finsupp.mem_support_iff.mpr hr_pos.ne'
      exact ⟨hrM, hrj⟩
  rw [hfilt, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]

private theorem expCount_of_prime {p j : ℕ} (hp : p.Prime) :
    expCount p j = if j = 1 then 1 else 0 := by
  unfold expCount
  rw [hp.primeFactors]
  split_ifs with hj
  · subst hj
    rw [Finset.filter_true_of_mem (fun r hr => by
      simp [Finset.mem_singleton.mp hr, hp.factorization_self]), Finset.card_singleton]
  · have h0 : Finset.filter (fun r => p.factorization r = j) {p} = ∅ := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      rintro rfl h
      rw [hp.factorization_self] at h
      exact hj h.symm
    rw [h0, Finset.card_empty]

private theorem expCount_of_cardFactors_two_nonsquare {M : ℕ}
    (hM : 1 < M) (hcard : cardFactors M = 2) (hnsq : ¬ IsSquare M) :
    expCount M 1 = 2 ∧ expCount M 2 = 0 ∧ expCount M 3 = 0 ∧ expCount M 4 = 0 := by
  have hM0 : M ≠ 0 := by omega
  have hle2 : ∀ r ∈ M.primeFactors, M.factorization r ≤ 2 := by
    intro r hr
    have hsum : cardFactors M = ∑ p ∈ M.primeFactors, M.factorization p := by
      rw [cardFactors_eq_sum_factorization, Finsupp.sum]
      rfl
    have hle := Finset.single_le_sum (f := fun p => M.factorization p) (fun _ _ => Nat.zero_le _) hr
    omega
  have hle4 : ∀ r ∈ M.primeFactors, M.factorization r ≤ 4 := fun r hr => (hle2 r hr).trans (by decide)
  have hncube : ∀ y : ℕ, M ≠ y ^ 3 := by
    intro y heq
    by_cases hy : y ≤ 1
    · have : y ^ 3 ≤ 1 := Nat.pow_le_pow_left hy 3
      omega
    · have hy2 : 2 ≤ y := by omega
      have hc : cardFactors (y ^ 3) = 3 * cardFactors y := by
        rw [show y ^ 3 = y * (y * y) by ring,
          cardFactors_mul (by omega) (mul_ne_zero (by omega) (by omega)),
          cardFactors_mul (by omega) (by omega)]
        ring
      have hpos : 0 < cardFactors y := cardFactors_pos_iff_one_lt.mpr (by omega)
      rw [heq, hc] at hcard
      omega
  obtain ⟨_, hOm, hodd, _, _, _⟩ := fourth_power_bounded_non_sq_non_cube_expCount hM hle4 hnsq hncube
  omega

private theorem sixth_power_free_source_invariants {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    ¬ 3 ∣ N ∧
    ¬ 5 ∣ N ∧
    N.factorization q = 1 ∧
    squareSourcesOne N = ∅ ∧
    (∀ s ∈ squareSources N, s.Prime ∧ s % 3 = 2 ∧ 53 ≤ s ∧ s ≠ q ∧
      N.factorization s = 2) ∧
    (∀ u ∈ largeSources N q, u.Prime ∧ u % 5 ≠ 1 ∧ 53 ≤ u ∧ u ≠ q ∧
      N.factorization u = 4) ∧
    N.primeFactors = insert q (squareSources N ∪ largeSources N q) ∧
    q ∉ squareSources N ∪ largeSources N q ∧
    Disjoint (squareSources N) (largeSources N q) ∧
    (∀ r ∈ N.primeFactors, N.factorization r ≤ 4) := by
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have h5 : ¬ 5 ∣ N := sixth_power_free_five_not_dvd ho hN hfree
  have hq1 : N.factorization q = 1 := sixth_power_free_euler_exponent_one ho hN hq he hfree
  have hfour : ∀ r ∈ largeSources N q, N.factorization r = 4 :=
    (three_free_sixthPowerFree_forces_147_largeSources ho hN hq hq4 he hev h3 hfree).1
  have hS1_empty : squareSourcesOne N = ∅ := by
    have hb := squareSourcesOne_card_le_three_exponent hN
    have hz : N.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd h3
    exact Finset.card_eq_zero.mp (by omega)
  have hsq_prop : ∀ s ∈ squareSources N,
      s.Prime ∧ s % 3 = 2 ∧ 53 ≤ s ∧ s ≠ q ∧ N.factorization s = 2 := by
    intro s hs
    obtain ⟨hs_mem, _, hs_exp⟩ := Finset.mem_filter.mp hs
    have hs_prime := Nat.prime_of_mem_primeFactors hs_mem
    have hs_dvd := Nat.dvd_of_mem_primeFactors hs_mem
    have hs53 := sixth_power_free_min_prime_ge_53 ho hN hfree hs_mem
    have hs_neq : s ≠ q := fun h => by subst s; omega
    have hs_not1 : s % 3 ≠ 1 := by
      intro h1
      have hmem1 : s ∈ squareSourcesOne N := Finset.mem_filter.mpr ⟨hs, h1⟩
      simp [hS1_empty] at hmem1
    have hs_not0 : s % 3 ≠ 0 := fun h0 => h3 ((Nat.dvd_of_mod_eq_zero h0).trans hs_dvd)
    exact ⟨hs_prime, by omega, hs53, hs_neq, hs_exp⟩
  have hlg_prop : ∀ u ∈ largeSources N q,
      u.Prime ∧ u % 5 ≠ 1 ∧ 53 ≤ u ∧ u ≠ q ∧ N.factorization u = 4 := by
    intro u hu
    obtain ⟨hu_mem, _, hu_neq, _⟩ := Finset.mem_filter.mp hu
    have hu_exp := hfour u hu
    have hu_prime := Nat.prime_of_mem_primeFactors hu_mem
    have hu53 := sixth_power_free_min_prime_ge_53 ho hN hfree hu_mem
    have hu_not5 : u % 5 ≠ 1 := by
      intro hmod5
      have hmem5 : u ∈ quarticSourcesOne N q :=
        Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hu_neq, hu_mem⟩, hu_exp, hmod5⟩
      have hpos := Finset.card_pos.mpr ⟨u, hmem5⟩
      have hle := quarticSourcesOne_card_le_five_exponent (q := q) hN
      have hz : N.factorization 5 = 0 := Nat.factorization_eq_zero_of_not_dvd h5
      omega
    exact ⟨hu_prime, hu_not5, hu53, hu_neq, hu_exp⟩
  have hparts : N.primeFactors = insert q (squareSources N ∪ largeSources N q) := by
    ext r
    simp only [Finset.mem_insert, Finset.mem_union, squareSources, largeSources, Finset.mem_filter]
    constructor
    · intro hr
      by_cases hrq : r = q
      · exact Or.inl hrq
      · right
        have hr_prime := Nat.prime_of_mem_primeFactors hr
        have hr3 : r ≠ 3 := fun h => h3 (h ▸ Nat.dvd_of_mem_primeFactors hr)
        have hr_pos : 0 < N.factorization r := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
        have hr_lt6 : ¬ 6 ≤ N.factorization r := fun hge =>
          hfree r hr_prime ((hr_prime.pow_dvd_iff_le_factorization hN.2.ne').2 hge)
        obtain ⟨_, hk⟩ := hev r hrq
        by_cases htwo : N.factorization r = 2
        · exact Or.inl ⟨hr, hr3, htwo⟩
        · exact Or.inr ⟨hr, hr3, hrq, by omega⟩
    · rintro (rfl | ⟨hr, _, _⟩ | ⟨hr, _, _, _⟩) <;> assumption
  have hq_notin : q ∉ squareSources N ∪ largeSources N q := by
    intro hmem
    rcases Finset.mem_union.mp hmem with hsq | hlg
    · have := (Finset.mem_filter.mp hsq).2.2
      omega
    · exact (Finset.mem_filter.mp hlg).2.2.1 rfl
  have hdisj : Disjoint (squareSources N) (largeSources N q) := by
    apply Finset.disjoint_left.mpr
    intro r hs hl
    have htwo := (Finset.mem_filter.mp hs).2.2
    have hlarge := (Finset.mem_filter.mp hl).2.2.2
    omega
  have hle4 : ∀ r ∈ N.primeFactors, N.factorization r ≤ 4 := by
    intro r hr
    by_cases hrq : r = q
    · subst hrq; omega
    · have hr_prime := Nat.prime_of_mem_primeFactors hr
      have hr_lt6 : ¬ 6 ≤ N.factorization r := fun hge =>
        hfree r hr_prime ((hr_prime.pow_dvd_iff_le_factorization hN.2.ne').2 hge)
      obtain ⟨_, hk⟩ := hev r hrq
      omega
  exact ⟨h3, h5, hq1, hS1_empty, hsq_prop, hlg_prop, hparts, hq_notin, hdisj, hle4⟩

/-- **Zero-Loss `Q → S₅₁_col` Bound**:
On any sixth-power-free odd perfect number `N`,
`oneModThreeLargeSources N q` (`Q₁₃`) and `twoModThreeLargeSources N q` (`Q₂₃`) satisfy
`Q₁₃.card + 2 * Q₂₃.card ≤ 2 * S₅₁_col.card`. -/
theorem sixth_power_free_quartic_to_S51_col_bound {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S₅₁ := (squareSources N).filter (· % 5 = 1)
    let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
    let Q₁₃ := oneModThreeLargeSources N q
    let Q₂₃ := twoModThreeLargeSources N q
    Q₁₃.card + 2 * Q₂₃.card ≤ 2 * S₅₁_col.card := by
  intro S₅₁ S₅₁_col Q₁₃ Q₂₃
  obtain ⟨_, _, _, _, hsq_prop, hlg_prop, _, _, _, _⟩ :=
    sixth_power_free_source_invariants ho hN hq hq4 he hev hfree
  have hhit := (sixth_power_free_largeSources_hit_S51_col ho hN hq hq4 he hev hfree).1
  have hdich := sixth_power_free_quartic_cardFactors_mod_three_dichotomy ho hN hq hq4 he hev hfree
  have hmut2 := (euler_linear_and_exponent_two_mutual_exclusion ho hN hq hq4 he hev).2
  let inc := ((largeSources N q) ×ˢ S₅₁_col).filter
    (fun us => us.2 ∈ (sigma 1 (us.1 ^ 4)).primeFactors)
  have hinc_ub : inc.card ≤ 2 * S₅₁_col.card := by
    have hfib : inc.card = ∑ s ∈ S₅₁_col, (inc.filter (fun us => us.2 = s)).card :=
      Finset.card_eq_sum_card_fiberwise fun us hus =>
        (Finset.mem_product.mp (Finset.mem_filter.mp hus).1).2
    rw [hfib]
    calc
      ∑ s ∈ S₅₁_col, (inc.filter (fun us => us.2 = s)).card
          ≤ ∑ _s ∈ S₅₁_col, 2 := by
            refine Finset.sum_le_sum fun s hs => ?_
            let src_s := N.primeFactors.filter (fun p => s ∈ (oddComponentSigma N q p).primeFactors)
            have hsrc_card : src_s.card = 2 := (Finset.mem_filter.mp hs).2
            have hle : (inc.filter (fun us => us.2 = s)).card ≤ src_s.card := by
              refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
              · intro us hus
                obtain ⟨hus_inc, rfl⟩ := Finset.mem_filter.mp hus
                obtain ⟨hus_prod, hs_mem⟩ := Finset.mem_filter.mp hus_inc
                have hu_lg := (Finset.mem_product.mp hus_prod).1
                have hu_mem := (Finset.mem_filter.mp hu_lg).1
                obtain ⟨_, _, _, hu_neq, hu_exp⟩ := hlg_prop us.1 hu_lg
                have hcomp : oddComponentSigma N q us.1 = sigma 1 (us.1 ^ 4) := by
                  unfold oddComponentSigma
                  simp only [hu_neq, ite_false, hu_exp]
                exact Finset.mem_filter.mpr ⟨hu_mem, hcomp.symm ▸ hs_mem⟩
              · intro ⟨u₁, s₁⟩ h1 ⟨u₂, s₂⟩ h2 heq
                have hs1 : s₁ = s := (Finset.mem_filter.mp h1).2
                have hs2 : s₂ = s := (Finset.mem_filter.mp h2).2
                dsimp only at heq
                ext <;> simp [heq, hs1, hs2]
            omega
      _ = 2 * S₅₁_col.card := by simp [Finset.sum_const, Nat.mul_comm]
  have hQ_parts : largeSources N q = Q₁₃ ∪ Q₂₃ := by
    ext u
    simp only [Q₁₃, Q₂₃, oneModThreeLargeSources, twoModThreeLargeSources,
      Finset.mem_union, Finset.mem_filter]
    by_cases h : u % 3 = 1 <;> tauto
  have hQ_disj : Disjoint Q₁₃ Q₂₃ := by
    apply Finset.disjoint_left.mpr
    intro u h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hfib_u : inc.card = ∑ u ∈ largeSources N q, (inc.filter (fun us => us.1 = u)).card :=
    Finset.card_eq_sum_card_fiberwise fun us hus =>
      (Finset.mem_product.mp (Finset.mem_filter.mp hus).1).1
  have hQ13_lb : Q₁₃.card ≤ ∑ w ∈ Q₁₃, (inc.filter (fun us => us.1 = w)).card := by
    calc
      Q₁₃.card = ∑ _w ∈ Q₁₃, 1 := by simp [Finset.sum_const]
      _ ≤ ∑ w ∈ Q₁₃, (inc.filter (fun us => us.1 = w)).card := by
            refine Finset.sum_le_sum fun w hw => ?_
            have hw_lg : w ∈ largeSources N q := (Finset.mem_filter.mp hw).1
            have hw_prime := (hlg_prop w hw_lg).1
            have hsig_ne0 : sigma 1 (w ^ 4) ≠ 0 := by
              rw [sigma_one_four_local hw_prime]
              positivity
            by_cases hqw : q ∣ sigma 1 (w ^ 4)
            · obtain ⟨_, s, hs_col, hs_odd⟩ :=
                quartic_oneModThree_euler_dvd_has_S51_col_factor ho hN hq hq4 he hev hfree hw hqw
              have hs_pf : s ∈ (sigma 1 (w ^ 4)).primeFactors :=
                Finsupp.mem_support_iff.mpr hs_odd.pos.ne'
              exact Finset.card_pos.mpr ⟨(w, s), Finset.mem_filter.mpr
                ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hw_lg, hs_col⟩, hs_pf⟩, rfl⟩⟩
            · obtain ⟨s, hs_col, hs_dvd⟩ := hhit w hw_lg hqw
              have hs_S51 := (Finset.mem_filter.mp hs_col).1
              have hs_sq := (Finset.mem_filter.mp hs_S51).1
              have hs_prime := (hsq_prop s hs_sq).1
              have hs_pf : s ∈ (sigma 1 (w ^ 4)).primeFactors :=
                Nat.mem_primeFactors.mpr ⟨hs_prime, hs_dvd, hsig_ne0⟩
              exact Finset.card_pos.mpr ⟨(w, s), Finset.mem_filter.mpr
                ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hw_lg, hs_col⟩, hs_pf⟩, rfl⟩⟩
  have hQ23_lb : 2 * Q₂₃.card ≤ ∑ u ∈ Q₂₃, (inc.filter (fun us => us.1 = u)).card := by
    calc
      2 * Q₂₃.card = ∑ _u ∈ Q₂₃, 2 := by simp [Finset.sum_const, Nat.mul_comm]
      _ ≤ ∑ u ∈ Q₂₃, (inc.filter (fun us => us.1 = u)).card := by
            refine Finset.sum_le_sum fun u hu => ?_
            have hu_lg : u ∈ largeSources N q := (Finset.mem_filter.mp hu).1
            have hu_mem := (Finset.mem_filter.mp hu_lg).1
            obtain ⟨hu_prime, _, hu53, hu_neq, hu_exp⟩ := hlg_prop u hu_lg
            have hu_odd : Odd u := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hu_mem)
            have hsig_eq : sigma 1 (u ^ 4) = u ^ 4 + u ^ 3 + u ^ 2 + u + 1 :=
              sigma_one_four_local hu_prime
            have hsig_ne0 : sigma 1 (u ^ 4) ≠ 0 := by rw [hsig_eq]; positivity
            have hnot_sq : ¬ IsSquare (sigma 1 (u ^ 4)) := by
              rw [hsig_eq]
              exact not_isSquare_quartic_sigma (by omega) (by omega)
            obtain ⟨_, hpf_S51, heven_cf, _, _⟩ := hdich.2 u hu
            let M := sigma 1 (u ^ 4)
            have hM_le2 : ∀ s ∈ M.primeFactors, M.factorization s ≤ 2 := by
              intro s hs
              have hs_S51 : s ∈ S₅₁ := (hpf_S51 s hs).1
              have hs_sq := (Finset.mem_filter.mp hs_S51).1
              have hs_prime := (hsq_prop s hs_sq).1
              have hs_odd := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hs_sq).1)
              have hs_exp2 := (hsq_prop s hs_sq).2.2.2.2
              have hsum := factorization_eq_sum_sigma_factorizations hN hs_odd hs_prime
              have hle := Finset.single_le_sum
                (f := fun p => (sigma 1 (p ^ N.factorization p)).factorization s)
                (fun _ _ => Nat.zero_le _) hu_mem
              rw [hu_exp] at hle
              change (sigma 1 (u ^ 4)).factorization s ≤ 2
              omega
            let E1 := M.primeFactors.filter (fun s => M.factorization s = 1)
            let E2 := M.primeFactors.filter (fun s => M.factorization s = 2)
            have hE_parts : M.primeFactors = E1 ∪ E2 := by
              ext s
              simp only [E1, E2, Finset.mem_union, Finset.mem_filter]
              constructor
              · intro hs
                have hpos : 0 < M.factorization s := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hs)
                have hle := hM_le2 s hs
                rcases (show M.factorization s = 1 ∨ M.factorization s = 2 by omega) with h1 | h2
                · exact Or.inl ⟨hs, h1⟩
                · exact Or.inr ⟨hs, h2⟩
              · rintro (⟨hs, _⟩ | ⟨hs, _⟩) <;> exact hs
            have hE_disj : Disjoint E1 E2 := by
              apply Finset.disjoint_left.mpr
              intro s h1 h2
              have hv1 := (Finset.mem_filter.mp h1).2
              have hv2 := (Finset.mem_filter.mp h2).2
              omega
            have hcf_eq : cardFactors M = E1.card + 2 * E2.card := by
              have hsum_fac : cardFactors M = ∑ s ∈ M.primeFactors, M.factorization s := by
                rw [cardFactors_eq_sum_factorization, Finsupp.sum]; rfl
              rw [hsum_fac, hE_parts, Finset.sum_union hE_disj]
              have h1 : ∑ s ∈ E1, M.factorization s = E1.card := by
                calc
                  ∑ s ∈ E1, M.factorization s = ∑ _s ∈ E1, 1 :=
                    Finset.sum_congr rfl fun s hs => (Finset.mem_filter.mp hs).2
                  _ = E1.card := by simp [Finset.sum_const]
              have h2 : ∑ s ∈ E2, M.factorization s = 2 * E2.card := by
                calc
                  ∑ s ∈ E2, M.factorization s = ∑ _s ∈ E2, 2 :=
                    Finset.sum_congr rfl fun s hs => (Finset.mem_filter.mp hs).2
                  _ = 2 * E2.card := by simp [Finset.sum_const, Nat.mul_comm]
              rw [h1, h2]
            have hE1_even : Even E1.card := by
              have hcf_mod : cardFactors M % 2 = 0 := Nat.even_iff.mp heven_cf
              refine Nat.even_iff.mpr ?_
              omega
            have hE1_pos : 1 ≤ E1.card := by
              obtain ⟨s, _, hs_odd⟩ := odd_factor_of_nonsquare_local hnot_sq
              have hs_pf : s ∈ M.primeFactors := Finsupp.mem_support_iff.mpr hs_odd.pos.ne'
              have hle := hM_le2 s hs_pf
              have hs1 : M.factorization s = 1 := by
                rcases hs_odd with ⟨k, hk⟩
                change M.factorization s = 2 * k + 1 at hk
                omega
              exact Finset.card_pos.mpr ⟨s, Finset.mem_filter.mpr ⟨hs_pf, hs1⟩⟩
            have hE1_ge2 : 2 ≤ E1.card := by
              obtain ⟨_, hk⟩ := hE1_even
              omega
            have hE1_sub : E1.image (fun s => (u, s)) ⊆ inc.filter (fun us => us.1 = u) := by
              intro us hus
              obtain ⟨s, hs_E1, rfl⟩ := Finset.mem_image.mp hus
              obtain ⟨hs_pf, hs_fac1⟩ := Finset.mem_filter.mp hs_E1
              have hs_S51 : s ∈ S₅₁ := (hpf_S51 s hs_pf).1
              have hs_sq := (Finset.mem_filter.mp hs_S51).1
              have hs_mem := (Finset.mem_filter.mp hs_sq).1
              have hs_prime := (hsq_prop s hs_sq).1
              have hs_exp2 := (hsq_prop s hs_sq).2.2.2.2
              have hs_col : s ∈ S₅₁_col := by
                refine Finset.mem_filter.mpr ⟨hs_S51, ?_⟩
                rcases hmut2 s hs_mem hs_exp2 with ⟨hi2, _, _⟩ | ⟨_, _, p, hp_mem, hs2_dvd_p, hnot_other⟩
                · exact hi2
                · exfalso
                  have hcomp_u : oddComponentSigma N q u = M := by
                    unfold oddComponentSigma
                    simp [hu_neq, hu_exp, M]
                  have hs_dvd_M : s ∣ M := Nat.dvd_of_mem_primeFactors hs_pf
                  have hup : u = p := by
                    by_contra hne
                    exact hnot_other u hu_mem hne (hcomp_u.symm ▸ hs_dvd_M)
                  rw [← hup, hcomp_u] at hs2_dvd_p
                  have h2le : 2 ≤ M.factorization s :=
                    (hs_prime.pow_dvd_iff_le_factorization hsig_ne0).mp hs2_dvd_p
                  omega
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu_lg, hs_col⟩, hs_pf⟩, rfl⟩
            have hinj : (E1.image (fun s => (u, s))).card = E1.card :=
              Finset.card_image_of_injOn fun _ _ _ _ heq => (Prod.ext_iff.mp heq).2
            calc
              2 ≤ E1.card := hE1_ge2
              _ = (E1.image (fun s => (u, s))).card := hinj.symm
              _ ≤ (inc.filter (fun us => us.1 = u)).card := Finset.card_le_card hE1_sub
  rw [hfib_u, hQ_parts, Finset.sum_union hQ_disj] at hinc_ub
  omega

/-! ## 3. Fine Conservation System & Farkas Linear Reductions -/

private theorem sq_sigma_primeFactors_subset {N q s : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hs : s ∈ squareSources N) :
    (sigma 1 (s ^ 2)).primeFactors ⊆ insert q (oneModThreeLargeSources N q) := by
  obtain ⟨h3, _, _, _, hsq_prop, _, hparts, _, _, _⟩ :=
    sixth_power_free_source_invariants ho hN hq hq4 he hev hfree
  obtain ⟨hs_prime, _, _, _, hs_exp⟩ := hsq_prop s hs
  have hs_odd : Odd s := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hs).1)
  have hsig_sq : sigma 1 (s ^ 2) = s ^ 2 + s + 1 := sigma_one_sq_local hs_prime
  have hsig_odd : Odd (sigma 1 (s ^ 2)) := by
    rw [hsig_sq]
    exact (hs_odd.pow.add_odd hs_odd).add_one
  intro w hw
  have hw_prime := Nat.prime_of_mem_primeFactors hw
  have hw_dvd := Nat.dvd_of_mem_primeFactors hw
  by_cases hwq : w = q
  · subst hwq; exact Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    have hw_odd : Odd w := hsig_odd.of_dvd_nat hw_dvd
    have hw_N : w ∣ N := by
      apply dvd_perfect_of_exact_prime_pow hN hs_prime (hs_exp ▸ Nat.ordProj_dvd N s)
        ((hs_prime.pow_dvd_iff_le_factorization hN.2.ne').not.mpr (by omega))
        hw_prime hw_odd
      rw [← sigma_one_apply]
      exact hw_dvd
    have hw_mem : w ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hw_prime, hw_N, hN.2.ne'⟩
    have hw_mod3 : w % 3 = 1 := by
      rcases prime_dvd_sq_add_self_add_one hw_prime (hsig_sq ▸ hw_dvd) with rfl | h1
      · exact (h3 hw_N).elim
      · exact h1
    have hw_union : w ∈ squareSources N ∪ largeSources N q := by
      rcases Finset.mem_insert.mp (hparts ▸ hw_mem) with hq_eq | hmem
      · exact (hwq hq_eq).elim
      · exact hmem
    have hw_lg : w ∈ largeSources N q := by
      rcases Finset.mem_union.mp hw_union with hw_sq | hw_lg
      · have := (hsq_prop w hw_sq).2.1
        omega
      · exact hw_lg
    exact Finset.mem_filter.mpr ⟨hw_lg, hw_mod3⟩

private theorem nat_four_part_cases {a b c d k : ℕ}
    (hk : k = a + b + c + d) (hs : a + 2 * b + 3 * c + 4 * d = 4) :
    (k = 1 → a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 1) ∧
    (k = 2 ∧ 1 ≤ a + c → a = 1 ∧ b = 0 ∧ c = 1 ∧ d = 0) ∧
    (k = 2 ∧ ¬ 1 ≤ a + c → a = 0 ∧ b = 2 ∧ c = 0 ∧ d = 0) ∧
    (k = 3 → a = 2 ∧ b = 1 ∧ c = 0 ∧ d = 0) ∧
    (k = 4 → a = 4 ∧ b = 0 ∧ c = 0 ∧ d = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro _; exact ⟨by omega, by omega, by omega, by omega⟩
  · rintro ⟨_, _⟩; exact ⟨by omega, by omega, by omega, by omega⟩
  · rintro ⟨_, _⟩; exact ⟨by omega, by omega, by omega, by omega⟩
  · intro _; exact ⟨by omega, by omega, by omega, by omega⟩
  · intro _; exact ⟨by omega, by omega, by omega, by omega⟩

private theorem per_target_inExpCount {N q r : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hr : r ∈ oneModThreeLargeSources N q) :
    let inExp := fun j =>
      (N.primeFactors.filter (fun p => (oddComponentSigma N q p).factorization r = j)).card
    let hasOdd := ∃ p ∈ N.primeFactors, Odd ((oddComponentSigma N q p).factorization r)
    (indegAt N q r = 1 →
      inExp 1 = 0 ∧ inExp 2 = 0 ∧ inExp 3 = 0 ∧ inExp 4 = 1) ∧
    (indegAt N q r = 2 ∧ hasOdd →
      inExp 1 = 1 ∧ inExp 2 = 0 ∧ inExp 3 = 1 ∧ inExp 4 = 0) ∧
    (indegAt N q r = 2 ∧ ¬ hasOdd →
      inExp 1 = 0 ∧ inExp 2 = 2 ∧ inExp 3 = 0 ∧ inExp 4 = 0) ∧
    (indegAt N q r = 3 →
      inExp 1 = 2 ∧ inExp 2 = 1 ∧ inExp 3 = 0 ∧ inExp 4 = 0) ∧
    (indegAt N q r = 4 →
      inExp 1 = 4 ∧ inExp 2 = 0 ∧ inExp 3 = 0 ∧ inExp 4 = 0) := by
  intro inExp hasOdd
  obtain ⟨_, _, _, _, _, hlg_prop, _, _, _, _⟩ :=
    sixth_power_free_source_invariants ho hN hq hq4 he hev hfree
  obtain ⟨hprops, hprod, _, _⟩ := prod_oddComponentSigma_eq_self ho hN hq hq4 he hev
  have hc0 : ∀ p ∈ N.primeFactors, oddComponentSigma N q p ≠ 0 := fun p hp => by
    have := (hprops p hp).2.2
    omega
  have hr_lg : r ∈ largeSources N q := (Finset.mem_filter.mp hr).1
  have hr_exp4 : N.factorization r = 4 := (hlg_prop r hr_lg).2.2.2.2
  have hprod_fac : ∑ p ∈ N.primeFactors, (oddComponentSigma N q p).factorization r = 4 := by
    have hfac_n : N.factorization r =
        ∑ p ∈ N.primeFactors, (oddComponentSigma N q p).factorization r := by
      conv_lhs => rw [← hprod]
      exact Nat.factorization_prod_apply hc0
    omega
  have hle4 : ∀ p ∈ N.primeFactors, (oddComponentSigma N q p).factorization r ≤ 4 := by
    intro p hp
    have hle := Finset.single_le_sum
      (f := fun x => (oddComponentSigma N q x).factorization r) (fun _ _ => Nat.zero_le _) hp
    omega
  let S (j : ℕ) := N.primeFactors.filter (fun p => (oddComponentSigma N q p).factorization r = j)
  have hdisj : ∀ a b, a ≠ b → Disjoint (S a) (S b) := by
    intro a b hab
    apply Finset.disjoint_left.mpr
    intro p ha hb
    have h1 := (Finset.mem_filter.mp ha).2
    have h2 := (Finset.mem_filter.mp hb).2
    omega
  have hpos_parts :
      N.primeFactors.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors) =
        S 1 ∪ S 2 ∪ S 3 ∪ S 4 := by
    ext p
    simp only [S, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hp, hrp⟩
      have hpos : 1 ≤ (oddComponentSigma N q p).factorization r :=
        Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hrp)
      have hle := hle4 p hp
      rcases (show (oddComponentSigma N q p).factorization r = 1 ∨
          (oddComponentSigma N q p).factorization r = 2 ∨
          (oddComponentSigma N q p).factorization r = 3 ∨
          (oddComponentSigma N q p).factorization r = 4 by omega) with h | h | h | h
      · exact Or.inl (Or.inl (Or.inl ⟨hp, h⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨hp, h⟩))
      · exact Or.inl (Or.inr ⟨hp, h⟩)
      · exact Or.inr ⟨hp, h⟩
    · rintro (((⟨hp, h1⟩ | ⟨hp, h2⟩) | ⟨hp, h3⟩) | ⟨hp, h4⟩)
      · exact ⟨hp, Finsupp.mem_support_iff.mpr (by rw [h1]; decide)⟩
      · exact ⟨hp, Finsupp.mem_support_iff.mpr (by rw [h2]; decide)⟩
      · exact ⟨hp, Finsupp.mem_support_iff.mpr (by rw [h3]; decide)⟩
      · exact ⟨hp, Finsupp.mem_support_iff.mpr (by rw [h4]; decide)⟩
  have hdisj12 : Disjoint (S 1) (S 2) := hdisj 1 2 (by decide)
  have hdisj123 : Disjoint (S 1 ∪ S 2) (S 3) :=
    Finset.disjoint_union_left.mpr ⟨hdisj 1 3 (by decide), hdisj 2 3 (by decide)⟩
  have hdisj1234 : Disjoint (S 1 ∪ S 2 ∪ S 3) (S 4) :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨hdisj 1 4 (by decide), hdisj 2 4 (by decide)⟩,
       hdisj 3 4 (by decide)⟩
  have hindeg_eq : indegAt N q r = inExp 1 + inExp 2 + inExp 3 + inExp 4 := by
    unfold indegAt
    rw [hpos_parts, Finset.card_union_of_disjoint hdisj1234,
      Finset.card_union_of_disjoint hdisj123, Finset.card_union_of_disjoint hdisj12]
  have hsum_j : ∀ j : ℕ, ∑ p ∈ S j, (oddComponentSigma N q p).factorization r = j * inExp j := by
    intro j
    calc
      ∑ p ∈ S j, (oddComponentSigma N q p).factorization r = ∑ _p ∈ S j, j :=
        Finset.sum_congr rfl fun p hp => (Finset.mem_filter.mp hp).2
      _ = j * inExp j := by
        dsimp [S, inExp]
        simp [Finset.sum_const, Nat.mul_comm]
  have hsum4 : inExp 1 + 2 * inExp 2 + 3 * inExp 3 + 4 * inExp 4 = 4 := by
    have hsplit :
        (∑ p ∈ N.primeFactors, (oddComponentSigma N q p).factorization r) =
          ∑ p ∈ N.primeFactors.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors),
            (oddComponentSigma N q p).factorization r := by
      rw [← Finset.sum_filter_add_sum_filter_not N.primeFactors
        (fun p => r ∈ (oddComponentSigma N q p).primeFactors)]
      have hz :
          (∑ p ∈ N.primeFactors.filter (fun p => r ∉ (oddComponentSigma N q p).primeFactors),
            (oddComponentSigma N q p).factorization r) = 0 :=
        Finset.sum_eq_zero fun p hp =>
          Finsupp.notMem_support_iff.mp (Finset.mem_filter.mp hp).2
      rw [hz, add_zero]
    rw [hsplit, hpos_parts, Finset.sum_union hdisj1234, Finset.sum_union hdisj123,
      Finset.sum_union hdisj12, hsum_j 1, hsum_j 2, hsum_j 3, hsum_j 4] at hprod_fac
    linarith only [hprod_fac]
  have hodd_iff : hasOdd ↔ 1 ≤ inExp 1 + inExp 3 := by
    constructor
    · rintro ⟨p, hp, hp_odd⟩
      have hpos : 0 < (oddComponentSigma N q p).factorization r := hp_odd.pos
      have hle := hle4 p hp
      obtain ⟨_, hk⟩ := hp_odd
      rcases (show (oddComponentSigma N q p).factorization r = 1 ∨
          (oddComponentSigma N q p).factorization r = 3 by omega) with h1 | h3
      · have : 1 ≤ inExp 1 := Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, h1⟩⟩
        omega
      · have : 1 ≤ inExp 3 := Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, h3⟩⟩
        omega
    · intro h13
      by_cases h1 : 1 ≤ inExp 1
      · obtain ⟨p, hp⟩ := Finset.card_pos.mp h1
        obtain ⟨hp_mem, hp1⟩ := Finset.mem_filter.mp hp
        exact ⟨p, hp_mem, by rw [hp1]; decide⟩
      · have h3 : 1 ≤ inExp 3 := by omega
        obtain ⟨p, hp⟩ := Finset.card_pos.mp h3
        obtain ⟨hp_mem, hp3⟩ := Finset.mem_filter.mp hp
        exact ⟨p, hp_mem, by rw [hp3]; decide⟩
  have hc := nat_four_part_cases hindeg_eq hsum4
  refine ⟨hc.1, ?_, ?_, hc.2.2.2.1, hc.2.2.2.2⟩
  · rintro ⟨h2, ho_r⟩
    exact hc.2.1 ⟨h2, hodd_iff.mp ho_r⟩
  · rintro ⟨h2, hno_r⟩
    exact hc.2.2.1 ⟨h2, fun h => hno_r (hodd_iff.mpr h)⟩

private theorem farkas_int_reductions
    (S50 S51_col S51_rep Q23 Q13 EQ13
     k q_Q Q13_3 Q13_5p Q23_2 Q23_4p
     S_p S_2 S_3p
     k_A1 k_A2 k_A3p
     k_B1 k_B26 k_B7p
     T_4 T_31 T_22 T_211 T_1111
     q_S
     HQ_e1 HQ_e2 HQ_e3 HQ_e4
     S3p_e1 S3p_e2 S3p_e3 S3p_e4
     A3p_e1 A3p_e2 A3p_e3 A3p_e4
     B26_e1 B26_e2 B26_e3 B26_e4
     B7p_e1 B7p_e2 B7p_e3 B7p_e4 : ℤ)
    (hS50 : 0 ≤ S50) (_hS51_col : 0 ≤ S51_col) (hS51_rep : 0 ≤ S51_rep)
    (hQ23 : 0 ≤ Q23) (_hQ13 : 0 ≤ Q13) (_hEQ13 : 0 ≤ EQ13)
    (hk : 0 ≤ k) (hq_Q : 0 ≤ q_Q) (hQ13_3 : 0 ≤ Q13_3) (hQ13_5p : 0 ≤ Q13_5p)
    (hQ23_2 : 0 ≤ Q23_2) (hQ23_4p : 0 ≤ Q23_4p)
    (_hS_p : 0 ≤ S_p) (hS_2 : 0 ≤ S_2) (_hS_3p : 0 ≤ S_3p)
    (_hk_A1 : 0 ≤ k_A1) (hk_A2 : 0 ≤ k_A2) (hk_A3p : 0 ≤ k_A3p)
    (_hk_B1 : 0 ≤ k_B1) (_hk_B26 : 0 ≤ k_B26) (hk_B7p : 0 ≤ k_B7p)
    (hT_4 : 0 ≤ T_4) (_hT_31 : 0 ≤ T_31) (hT_22 : 0 ≤ T_22)
    (_hT_211 : 0 ≤ T_211) (hT_1111 : 0 ≤ T_1111)
    (hq_S : 0 ≤ q_S)
    (hHQ_e1 : 0 ≤ HQ_e1) (hHQ_e2 : 0 ≤ HQ_e2) (hHQ_e3 : 0 ≤ HQ_e3) (hHQ_e4 : 0 ≤ HQ_e4)
    (_hS3p_e1 : 0 ≤ S3p_e1) (_hS3p_e2 : 0 ≤ S3p_e2) (_hS3p_e3 : 0 ≤ S3p_e3) (_hS3p_e4 : 0 ≤ S3p_e4)
    (_hA3p_e1 : 0 ≤ A3p_e1) (_hA3p_e2 : 0 ≤ A3p_e2) (_hA3p_e3 : 0 ≤ A3p_e3) (_hA3p_e4 : 0 ≤ A3p_e4)
    (_hB26_e1 : 0 ≤ B26_e1) (_hB26_e2 : 0 ≤ B26_e2) (_hB26_e3 : 0 ≤ B26_e3) (_hB26_e4 : 0 ≤ B26_e4)
    (hB7p_e1 : 0 ≤ B7p_e1) (hB7p_e2 : 0 ≤ B7p_e2) (_hB7p_e3 : 0 ≤ B7p_e3) (_hB7p_e4 : 0 ≤ B7p_e4)
    (E1_q : q_Q + q_S = 1)
    (E2_Q13 : Q13 = k + q_Q + Q13_3 + Q13_5p)
    (E2_Q23 : Q23 = Q23_2 + Q23_4p)
    (E3_Snc : S_p + S_2 + S_3p + k = S50 + S51_col + S51_rep)
    (E3_chA : k_A1 + k_A2 + k_A3p = k)
    (E3_chB : k_B1 + k_B26 + k_B7p = k)
    (E3_tgt : T_4 + T_31 + T_22 + T_211 + T_1111 = Q13)
    (EQ13_eq : EQ13 = T_31 + T_22 + 2 * T_211 + 3 * T_1111)
    (E4_e1 : HQ_e1 + S_p + 2 * S_2 + S3p_e1 + k_A1 + 2 * k_A2 + A3p_e1 + k_B1 + B26_e1 + B7p_e1 =
      q_S + T_31 + 2 * T_211 + 4 * T_1111)
    (E4_e2 : HQ_e2 + S3p_e2 + A3p_e2 + B26_e2 + B7p_e2 = 2 * T_22 + T_211)
    (E4_e3 : HQ_e3 + S3p_e3 + A3p_e3 + B26_e3 + B7p_e3 = T_31)
    (E4_e4 : HQ_e4 + S3p_e4 + A3p_e4 + B26_e4 + B7p_e4 = T_4)
    (U_Q_Om : k + q_Q + 3 * Q13_3 + 5 * Q13_5p + 2 * Q23_2 + 4 * Q23_4p ≤
      2 * S51_col + 2 * S51_rep)
    (U_Q_e1 : Q13 + 2 * Q23 ≤ 2 * S51_col)
    (U_up_Phi5 : 2 * k + Q13_3 + Q23_2 ≤ 2 * S51_col + S51_rep)
    (U_S3p_Om : 3 * S_3p ≤ S3p_e1 + 2 * S3p_e2 + 3 * S3p_e3 + 4 * S3p_e4)
    (U_S3p_om : 2 * S_3p ≤ S3p_e1 + S3p_e2 + S3p_e3 + S3p_e4)
    (U_S3p_ncb : S_3p ≤ S3p_e1 + S3p_e2 + S3p_e4)
    (U_A3p_Om : 3 * k_A3p ≤ A3p_e1 + 2 * A3p_e2 + 3 * A3p_e3 + 4 * A3p_e4)
    (U_A3p_om : 2 * k_A3p ≤ A3p_e1 + A3p_e2 + A3p_e3 + A3p_e4)
    (U_A3p_ncb : k_A3p ≤ A3p_e1 + A3p_e2 + A3p_e4)
    (U_B26_lo : 2 * k_B26 ≤ B26_e1 + 2 * B26_e2 + 3 * B26_e3 + 4 * B26_e4)
    (U_B26_om : 2 * k_B26 ≤ B26_e1 + B26_e2 + B26_e3 + B26_e4)
    (U_B26_ncb : k_B26 ≤ B26_e1 + B26_e2 + B26_e4)
    (U_B7p_Om : 7 * k_B7p ≤ B7p_e1 + 2 * B7p_e2 + 3 * B7p_e3 + 4 * B7p_e4)
    (U_B7p_ncb : k_B7p ≤ B7p_e1 + B7p_e2 + B7p_e4)
    (U_up_Phi3_TA1 : S_p + S_2 + k_B1 + k_A1 ≤ q_S + T_31 + T_211 + T_1111)
    (U_up_A_TSp2 : k_A1 + k_A2 + 2 * S_p ≤ 2 * (q_S + T_31 + T_211 + T_1111)) :
    let om1 := S50 + S51_col + S51_rep + Q23 + Q13
    let S51 := S51_col + S51_rep
    let E := S51_col + EQ13
    Q23 ≤ Q13 + 1 ∧
    2 * (1 + om1) ≤ 7 * Q13 + 6 ∧
    5 * (1 + om1) ≤ 16 * S51 + 16 ∧
    (1 + om1) ≤ 6 * S51_col + 2 ∧
    13 * (1 + om1) ≤ 20 * E + 38 ∧
    9 * Q13 ≤ 8 * EQ13 + 8 * S51_rep + 8 * Q23 + 8 * S50 + 10 ∧
    (1 + om1) + 20 * Q13 ≤ 20 * EQ13 + 20 * S51_rep + 20 * Q23 + 20 * S50 + 26 := by
  intro om1 S51 E
  have hE4_rhs : (q_S + T_31 + 2 * T_211 + 4 * T_1111) + 2 * (2 * T_22 + T_211) +
      3 * T_31 + 4 * T_4 = q_S + 4 * Q13 := by
    linarith only [E3_tgt]
  have hHQ_wt : 0 ≤ HQ_e1 + 2 * HQ_e2 + 3 * HQ_e3 + 4 * HQ_e4 := by
    linarith only [hHQ_e1, hHQ_e2, hHQ_e3, hHQ_e4]
  have hE_wt : S_p + 2 * S_2 + 3 * S_3p + k_A1 + 2 * k_A2 + 3 * k_A3p + k_B1 + 2 * k_B26 +
      7 * k_B7p ≤ q_S + 4 * Q13 := by
    linarith only [E4_e1, E4_e2, E4_e3, E4_e4, hE4_rhs, hHQ_wt,
      U_S3p_Om, U_A3p_Om, U_B26_lo, U_B7p_Om]
  have hI_wt : 2 * S_p + 4 * S_2 + 6 * S_3p + 2 * k_A1 + 4 * k_A2 + 5 * k_A3p + 2 * k_B1 +
      4 * k_B26 + 4 * k_B7p ≤ 2 * q_S + 8 * Q13 := by
    linarith only [hE_wt, hk_A3p, hk_B7p]
  have hTA1 : S_p + S_2 + k_B1 + k_A1 ≤ q_S + Q13 := by
    linarith only [U_up_Phi3_TA1, E3_tgt, hT_4, hT_22]
  have hTA2 : k_A1 + k_A2 + 2 * S_p ≤ 2 * (q_S + Q13) := by
    linarith only [U_up_A_TSp2, E3_tgt, hT_4, hT_22]
  have hMI_triple : 6 * (S50 + S51) + 3 * k ≤ 6 * q_S + 12 * Q13 := by
    linarith only [hI_wt, hTA1, hTA2, E3_Snc, E3_chA, E3_chB]
  have hMI_lt : 3 * (2 * (S50 + S51) + k) < 3 * (2 * q_S + 4 * Q13 + 1) := by
    linarith only [hMI_triple]
  have hMI : 2 * (S50 + S51) + k ≤ 2 * q_S + 4 * Q13 :=
    Int.lt_add_one_iff.mp (lt_of_mul_lt_mul_left hMI_lt (by norm_num))
  have hU_Q_Om_2 : k + q_Q + 2 * Q13_3 + 2 * Q13_5p + 2 * Q23 ≤ 2 * S51 := by
    linarith only [U_Q_Om, E2_Q23, hQ13_3, hQ13_5p, hQ23_4p]
  have h1_lt : 2 * Q23 < 2 * (Q13 + 1 + 1) := by
    linarith only [hMI, hU_Q_Om_2, E1_q, E2_Q13, hS50, hq_Q]
  have h1 : Q23 ≤ Q13 + 1 :=
    Int.lt_add_one_iff.mp (lt_of_mul_lt_mul_left h1_lt (by norm_num))
  have hU_Q_Om_3 : k + q_Q + 3 * Q13_3 + 3 * Q13_5p + 2 * Q23 ≤ 2 * S51 := by
    linarith only [U_Q_Om, E2_Q23, hQ13_5p, hQ23_4p]
  have h2 : 2 * (1 + om1) ≤ 7 * Q13 + 6 := by
    linarith only [hU_Q_Om_3, hMI, E1_q, E2_Q13, hS50, hq_Q]
  have hU_Q_Om_h3 : 7 * k + 7 * q_Q + 21 * Q13_3 + 30 * Q13_5p + 10 * Q23 ≤ 14 * S51 := by
    linarith only [U_Q_Om, E2_Q23, hQ13_5p, hQ23_2, hQ23_4p]
  have hU_Phi5_h3 : 18 * k + 9 * Q13_3 ≤ 18 * S51 := by
    linarith only [U_up_Phi5, hQ23_2, hS51_rep]
  have h3_lt : 2 * (5 * (1 + om1)) < 2 * ((16 * S51 + 16) + 1) := by
    linarith only [hU_Q_Om_h3, hU_Phi5_h3, hMI, E1_q, E2_Q13, hq_Q, hq_S]
  have h3 : 5 * (1 + om1) ≤ 16 * S51 + 16 :=
    Int.lt_add_one_iff.mp (lt_of_mul_lt_mul_left h3_lt (by norm_num))
  have h4_lt : 2 * (1 + om1) < 2 * (6 * S51_col + 2 + 1) := by
    linarith only [hMI, U_Q_e1, E1_q, hk, hQ23, hq_Q]
  have h4 : 1 + om1 ≤ 6 * S51_col + 2 :=
    Int.lt_add_one_iff.mp (lt_of_mul_lt_mul_left h4_lt (by norm_num))
  have hL_S3p : 5 * S_3p ≤ 3 * S3p_e1 + 3 * S3p_e2 + 2 * S3p_e3 + 3 * S3p_e4 := by
    linarith only [U_S3p_om, U_S3p_ncb]
  have hL_A3p : 5 * k_A3p ≤ 3 * A3p_e1 + 3 * A3p_e2 + 2 * A3p_e3 + 3 * A3p_e4 := by
    linarith only [U_A3p_om, U_A3p_ncb]
  have hL_B26 : 5 * k_B26 ≤ 3 * B26_e1 + 3 * B26_e2 + 2 * B26_e3 + 3 * B26_e4 := by
    linarith only [U_B26_om, U_B26_ncb]
  have hL_B7p_lt : 3 * (5 * k_B7p) < 3 * (3 * B7p_e1 + 3 * B7p_e2 + 2 * B7p_e3 + 3 * B7p_e4 + 1) := by
    linarith only [U_B7p_Om, U_B7p_ncb, hB7p_e1, hB7p_e2]
  have hL_B7p' : 5 * k_B7p ≤ 3 * B7p_e1 + 3 * B7p_e2 + 2 * B7p_e3 + 3 * B7p_e4 :=
    Int.lt_add_one_iff.mp (lt_of_mul_lt_mul_left hL_B7p_lt (by norm_num))
  have hL_HQ : 0 ≤ 3 * HQ_e1 + 3 * HQ_e2 + 2 * HQ_e3 + 3 * HQ_e4 := by
    linarith only [hHQ_e1, hHQ_e2, hHQ_e3, hHQ_e4]
  have hL_rhs : 3 * (q_S + T_31 + 2 * T_211 + 4 * T_1111) + 3 * (2 * T_22 + T_211) + 2 * T_31 +
      3 * T_4 + 2 * (q_S + T_31 + T_211 + T_1111) ≤ 5 * q_S + 3 * Q13 + 4 * EQ13 := by
    linarith only [E3_tgt, EQ13_eq, hT_22, hT_1111]
  have hML_pre : 5 * S_p + 8 * S_2 + 5 * S_3p + 5 * k_A1 + 6 * k_A2 + 5 * k_A3p + 5 * k_B1 +
      5 * k_B26 + 5 * k_B7p ≤ 5 * q_S + 3 * Q13 + 4 * EQ13 := by
    linarith only [E4_e1, E4_e2, E4_e3, E4_e4, U_up_Phi3_TA1,
      hL_S3p, hL_A3p, hL_B26, hL_B7p', hL_HQ, hL_rhs]
  have hML : 5 * (S50 + S51) + 5 * k ≤ 5 * q_S + 3 * Q13 + 4 * EQ13 := by
    linarith only [hML_pre, E3_Snc, E3_chA, E3_chB, hS_2, hk_A2]
  have hU_Q_Om_h5 : 72 * k + 72 * q_Q + 216 * Q13_3 + 216 * Q13_5p + 144 * Q23 ≤ 144 * S51 := by
    linarith only [U_Q_Om, E2_Q23, hQ13_5p, hQ23_4p]
  have h5_lt : 12 * (13 * (1 + om1)) < 12 * (20 * E + 38 + 1) := by
    linarith only [hML, hU_Q_Om_h5, U_Q_e1, E1_q, E2_Q13, hS50, hk, hq_Q, hQ23]
  have h5 : 13 * (1 + om1) ≤ 20 * E + 38 :=
    Int.lt_add_one_iff.mp (lt_of_mul_lt_mul_left h5_lt (by norm_num))
  have hU_Q_Om_h6 : 15 * k + 15 * q_Q + 45 * Q13_3 + 45 * Q13_5p + 30 * Q23 ≤ 30 * S51 := by
    linarith only [U_Q_Om, E2_Q23, hQ13_5p, hQ23_4p]
  have h6_lt : 3 * (9 * Q13) < 3 * (8 * EQ13 + 8 * S51_rep + 8 * Q23 + 8 * S50 + 10 + 1) := by
    linarith only [hML, hU_Q_Om_h6, E1_q, E2_Q13, hS50, hS51_rep, hQ23, hq_Q]
  have h6 : 9 * Q13 ≤ 8 * EQ13 + 8 * S51_rep + 8 * Q23 + 8 * S50 + 10 :=
    Int.lt_add_one_iff.mp (lt_of_mul_lt_mul_left h6_lt (by norm_num))
  have hU_Q_Om_h7 : 36 * k + 36 * q_Q + 108 * Q13_3 + 108 * Q13_5p + 72 * Q23 ≤ 72 * S51 := by
    linarith only [U_Q_Om, E2_Q23, hQ13_5p, hQ23_4p]
  have h7_lt : 3 * ((1 + om1) + 20 * Q13) <
      3 * (20 * EQ13 + 20 * S51_rep + 20 * Q23 + 20 * S50 + 26 + 1) := by
    linarith only [hML, hU_Q_Om_h7, E1_q, E2_Q13, hS50, hS51_rep, hQ23, hk, hq_Q]
  have h7 : (1 + om1) + 20 * Q13 ≤ 20 * EQ13 + 20 * S51_rep + 20 * Q23 + 20 * S50 + 26 :=
    Int.lt_add_one_iff.mp (lt_of_mul_lt_mul_left h7_lt (by norm_num))
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-! ## 4. Fine Partition Helpers & Main Target-Reuse Obstruction Theorems -/

private def fineS50 (N : ℕ) : Finset ℕ := (squareSources N).filter (· % 5 ≠ 1)
private def fineS51 (N : ℕ) : Finset ℕ := (squareSources N).filter (· % 5 = 1)
private def fineS51Col (N q : ℕ) : Finset ℕ := (fineS51 N).filter (fun r => indegAt N q r = 2)
private def fineS51Rep (N q : ℕ) : Finset ℕ := (fineS51 N).filter (fun r => indegAt N q r = 1)
private def fineQ13q (N q : ℕ) : Finset ℕ :=
  (oneModThreeLargeSources N q).filter (fun w => q ∣ sigma 1 (w ^ 4))
private def fineSqQ (N q : ℕ) : Finset ℕ :=
  (squareSources N).filter (fun s => q ∣ sigma 1 (s ^ 2))
private def fineQ13_3 (N q : ℕ) : Finset ℕ :=
  (oneModThreeLargeSources N q).filter
    (fun w => ¬ q ∣ sigma 1 (w ^ 4) ∧ cardFactors (sigma 1 (w ^ 4)) = 3)
private def fineQ13_5p (N q : ℕ) : Finset ℕ :=
  (oneModThreeLargeSources N q).filter
    (fun w => ¬ q ∣ sigma 1 (w ^ 4) ∧ 5 ≤ cardFactors (sigma 1 (w ^ 4)))
private def fineQ23_2 (N q : ℕ) : Finset ℕ :=
  (twoModThreeLargeSources N q).filter (fun u => cardFactors (sigma 1 (u ^ 4)) = 2)
private def fineQ23_4p (N q : ℕ) : Finset ℕ :=
  (twoModThreeLargeSources N q).filter (fun u => 4 ≤ cardFactors (sigma 1 (u ^ 4)))
private def fineSnc (N q : ℕ) : Finset ℕ := squareSources N \ quarticChainIntermediates N q
private def fineSp (N q : ℕ) : Finset ℕ :=
  (fineSnc N q).filter (fun s => cardFactors (sigma 1 (s ^ 2)) = 1)
private def fineS2 (N q : ℕ) : Finset ℕ :=
  (fineSnc N q).filter (fun s => cardFactors (sigma 1 (s ^ 2)) = 2)
private def fineS3p (N q : ℕ) : Finset ℕ :=
  (fineSnc N q).filter (fun s => 3 ≤ cardFactors (sigma 1 (s ^ 2)))
private def fineKA1 (N q : ℕ) : Finset ℕ :=
  (quarticChainSources N q).filter (fun w => cardFactors (quarticFirstFactor w) = 1)
private def fineKA2 (N q : ℕ) : Finset ℕ :=
  (quarticChainSources N q).filter (fun w => cardFactors (quarticFirstFactor w) = 2)
private def fineKA3p (N q : ℕ) : Finset ℕ :=
  (quarticChainSources N q).filter (fun w => 3 ≤ cardFactors (quarticFirstFactor w))
private def fineKB1 (N q : ℕ) : Finset ℕ :=
  (quarticChainSources N q).filter (fun w => cardFactors (quarticSecondFactor w) = 1)
private def fineKB26 (N q : ℕ) : Finset ℕ :=
  (quarticChainSources N q).filter
    (fun w => 2 ≤ cardFactors (quarticSecondFactor w) ∧ cardFactors (quarticSecondFactor w) ≤ 6)
private def fineKB7p (N q : ℕ) : Finset ℕ :=
  (quarticChainSources N q).filter (fun w => 7 ≤ cardFactors (quarticSecondFactor w))
private def fineT4 (N q : ℕ) : Finset ℕ :=
  (oneModThreeLargeSources N q).filter (fun r => indegAt N q r = 1)
private def fineT31 (N q : ℕ) : Finset ℕ :=
  (oneModThreeLargeSources N q).filter
    (fun r => indegAt N q r = 2 ∧ ∃ p ∈ N.primeFactors, Odd ((oddComponentSigma N q p).factorization r))
private def fineT22 (N q : ℕ) : Finset ℕ :=
  (oneModThreeLargeSources N q).filter
    (fun r => indegAt N q r = 2 ∧ ¬ ∃ p ∈ N.primeFactors, Odd ((oddComponentSigma N q p).factorization r))
private def fineT211 (N q : ℕ) : Finset ℕ :=
  (oneModThreeLargeSources N q).filter (fun r => indegAt N q r = 3)
private def fineT1111 (N q : ℕ) : Finset ℕ :=
  (oneModThreeLargeSources N q).filter (fun r => indegAt N q r = 4)
private def fineHQe (N q j : ℕ) : ℕ :=
  ((oneModThreeLargeSources N q).filter (fun r => ((q + 1) / 2).factorization r = j)).card
private def fineS3pe (N q j : ℕ) : ℕ := ∑ s ∈ fineS3p N q, expCount (sigma 1 (s ^ 2)) j
private def fineA3pe (N q j : ℕ) : ℕ := ∑ w ∈ fineKA3p N q, expCount (quarticFirstFactor w) j
private def fineB26e (N q j : ℕ) : ℕ := ∑ w ∈ fineKB26 N q, expCount (quarticSecondFactor w) j
private def fineB7pe (N q j : ℕ) : ℕ := ∑ w ∈ fineKB7p N q, expCount (quarticSecondFactor w) j
private def fineTe1 (N q : ℕ) : Finset ℕ :=
  (insert q (oneModThreeLargeSources N q)).filter
    (fun t => ∃ s ∈ squareSources N, (sigma 1 (s ^ 2)).factorization t = 1)

private theorem fine_Q_partition_and_bounds {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    (fineQ13q N q).card + (fineSqQ N q).card = 1 ∧
    (oneModThreeLargeSources N q).card =
      (quarticChainSources N q).card + (fineQ13q N q).card +
        (fineQ13_3 N q).card + (fineQ13_5p N q).card ∧
    (twoModThreeLargeSources N q).card = (fineQ23_2 N q).card + (fineQ23_4p N q).card ∧
    (quarticChainSources N q).card + (fineQ13q N q).card + 3 * (fineQ13_3 N q).card +
      5 * (fineQ13_5p N q).card + 2 * (fineQ23_2 N q).card + 4 * (fineQ23_4p N q).card ≤
      2 * (fineS51Col N q).card + 2 * (fineS51Rep N q).card ∧
    2 * (quarticChainSources N q).card + (fineQ13_3 N q).card + (fineQ23_2 N q).card ≤
      2 * (fineS51Col N q).card + (fineS51Rep N q).card := by
  obtain ⟨_, _, hq1, _, hsq_prop, hlg_prop, hparts, hq_notin, hdisj, _⟩ :=
    sixth_power_free_source_invariants ho hN hq hq4 he hev hfree
  have hq_prime := Nat.prime_of_mem_primeFactors hq
  have hq_odd : Odd q := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)
  have hdich := sixth_power_free_quartic_cardFactors_mod_three_dichotomy ho hN hq hq4 he hev hfree
  obtain ⟨hS51_u, hS51_disj, hS51_card, _, _, _⟩ :=
    sixth_power_free_S51_collision_repeat_split ho hN hq hq4 he hev hfree
  change fineS51 N = fineS51Col N q ∪ fineS51Rep N q at hS51_u
  change Disjoint (fineS51Col N q) (fineS51Rep N q) at hS51_disj
  change (fineS51 N).card = (fineS51Col N q).card + (fineS51Rep N q).card at hS51_card
  have hQ_parts : largeSources N q = oneModThreeLargeSources N q ∪ twoModThreeLargeSources N q := by
    ext u; simp only [oneModThreeLargeSources, twoModThreeLargeSources, Finset.mem_union, Finset.mem_filter]
    by_cases h : u % 3 = 1 <;> tauto
  have hQ_disj : Disjoint (oneModThreeLargeSources N q) (twoModThreeLargeSources N q) := by
    apply Finset.disjoint_left.mpr; intro u h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hq_sum_eq1 :
      ∑ p ∈ N.primeFactors, (sigma 1 (p ^ N.factorization p)).factorization q = 1 :=
    (factorization_eq_sum_sigma_factorizations hN hq_odd hq_prime).symm.trans hq1
  have hq_at_q : (sigma 1 (q ^ N.factorization q)).factorization q = 0 := by
    rw [hq1, pow_one, sigma_one_prime_local hq_prime]
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hd
    exact hq_prime.not_dvd_one ((Nat.dvd_add_right dvd_rfl).mp hd)
  have hq_on_Q23 : ∑ u ∈ twoModThreeLargeSources N q, (sigma 1 (u ^ 4)).factorization q = 0 :=
    Finset.sum_eq_zero fun u hu => Nat.factorization_eq_zero_of_not_dvd (hdich.2 u hu).1
  have hfac_q_le1 : ∀ p ∈ N.primeFactors, (sigma 1 (p ^ N.factorization p)).factorization q ≤ 1 := by
    intro p hp
    have hle := Finset.single_le_sum
      (f := fun x => (sigma 1 (x ^ N.factorization x)).factorization q)
      (fun _ _ => Nat.zero_le _) hp
    omega
  have hS_q_sum : ∑ s ∈ squareSources N, (sigma 1 (s ^ 2)).factorization q = (fineSqQ N q).card := by
    rw [← Finset.sum_filter_add_sum_filter_not (squareSources N) (fun s => q ∣ sigma 1 (s ^ 2))]
    have h0 : ∑ s ∈ (squareSources N).filter (fun s => ¬ q ∣ sigma 1 (s ^ 2)),
        (sigma 1 (s ^ 2)).factorization q = 0 :=
      Finset.sum_eq_zero fun s hs => Nat.factorization_eq_zero_of_not_dvd (Finset.mem_filter.mp hs).2
    have h1 : ∑ s ∈ fineSqQ N q, (sigma 1 (s ^ 2)).factorization q = (fineSqQ N q).card := by
      calc ∑ s ∈ fineSqQ N q, (sigma 1 (s ^ 2)).factorization q = ∑ _s ∈ fineSqQ N q, 1 := by
            refine Finset.sum_congr rfl fun s hs => ?_
            obtain ⟨hs_sq, hs_dvd⟩ := Finset.mem_filter.mp hs
            have hs_mem := (Finset.mem_filter.mp hs_sq).1
            have hs_prime := (hsq_prop s hs_sq).1
            have hs_exp := (hsq_prop s hs_sq).2.2.2.2
            have hs_ne0 : sigma 1 (s ^ 2) ≠ 0 := by rw [sigma_one_sq_local hs_prime]; positivity
            have hge1 : 1 ≤ (sigma 1 (s ^ 2)).factorization q :=
              (hq_prime.dvd_iff_one_le_factorization hs_ne0).mp hs_dvd
            have hle1 := hfac_q_le1 s hs_mem
            rw [hs_exp] at hle1; omega
        _ = (fineSqQ N q).card := by simp [Finset.sum_const]
    change (∑ x ∈ fineSqQ N q, _) + _ = _
    rw [h0, add_zero]; exact h1
  have hQ13_q_sum :
      ∑ w ∈ oneModThreeLargeSources N q, (sigma 1 (w ^ 4)).factorization q = (fineQ13q N q).card := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (oneModThreeLargeSources N q) (fun w => q ∣ sigma 1 (w ^ 4))]
    have h0 : ∑ w ∈ (oneModThreeLargeSources N q).filter (fun w => ¬ q ∣ sigma 1 (w ^ 4)),
        (sigma 1 (w ^ 4)).factorization q = 0 :=
      Finset.sum_eq_zero fun w hw => Nat.factorization_eq_zero_of_not_dvd (Finset.mem_filter.mp hw).2
    have h1 : ∑ w ∈ fineQ13q N q, (sigma 1 (w ^ 4)).factorization q = (fineQ13q N q).card := by
      calc ∑ w ∈ fineQ13q N q, (sigma 1 (w ^ 4)).factorization q = ∑ _w ∈ fineQ13q N q, 1 := by
            refine Finset.sum_congr rfl fun w hw => ?_
            obtain ⟨hw_Q13, hw_dvd⟩ := Finset.mem_filter.mp hw
            have hw_lg := (Finset.mem_filter.mp hw_Q13).1
            have hw_mem := (Finset.mem_filter.mp hw_lg).1
            have hw_prime := (hlg_prop w hw_lg).1
            have hw_exp := (hlg_prop w hw_lg).2.2.2.2
            have hw_ne0 : sigma 1 (w ^ 4) ≠ 0 := by rw [sigma_one_four_local hw_prime]; positivity
            have hge1 : 1 ≤ (sigma 1 (w ^ 4)).factorization q :=
              (hq_prime.dvd_iff_one_le_factorization hw_ne0).mp hw_dvd
            have hle1 := hfac_q_le1 w hw_mem
            rw [hw_exp] at hle1; omega
        _ = (fineQ13q N q).card := by simp [Finset.sum_const]
    change (∑ x ∈ fineQ13q N q, _) + _ = _
    rw [h0, add_zero]; exact h1
  have hE1_q : (fineQ13q N q).card + (fineSqQ N q).card = 1 := by
    rw [hparts, Finset.sum_insert hq_notin, hq_at_q, zero_add, Finset.sum_union hdisj] at hq_sum_eq1
    have hsq_rw : ∑ s ∈ squareSources N, (sigma 1 (s ^ N.factorization s)).factorization q =
        ∑ s ∈ squareSources N, (sigma 1 (s ^ 2)).factorization q :=
      Finset.sum_congr rfl fun s hs => by rw [(hsq_prop s hs).2.2.2.2]
    have hlg_rw : ∑ u ∈ largeSources N q, (sigma 1 (u ^ N.factorization u)).factorization q =
        ∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization q :=
      Finset.sum_congr rfl fun u hu => by rw [(hlg_prop u hu).2.2.2.2]
    rw [hsq_rw, hlg_rw, hQ_parts, Finset.sum_union hQ_disj, hS_q_sum, hQ13_q_sum, hq_on_Q23,
      add_zero] at hq_sum_eq1
    omega
  obtain ⟨hK_src_eq, hK_src_nq, hK_int_col, hK_card⟩ :=
    quarticChainSources_eq_oneModThree_prime_and_card ho hN hq hq4 he hev hfree
  change quarticChainIntermediates N q ⊆ fineS51Col N q at hK_int_col
  have hK_mem : ∀ w ∈ quarticChainSources N q,
      w ∈ oneModThreeLargeSources N q ∧ (sigma 1 (w ^ 4)).Prime := fun w hw => by
    rw [hK_src_eq] at hw; exact Finset.mem_filter.mp hw
  have hQ13_parts : oneModThreeLargeSources N q =
      quarticChainSources N q ∪ fineQ13q N q ∪ fineQ13_3 N q ∪ fineQ13_5p N q := by
    ext w
    simp only [fineQ13q, fineQ13_3, fineQ13_5p, hK_src_eq, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hw
      by_cases hqw : q ∣ sigma 1 (w ^ 4)
      · exact Or.inl (Or.inl (Or.inr ⟨hw, hqw⟩))
      · obtain ⟨_, hodd, hbr⟩ := hdich.1 w hw hqw
        rcases hbr with hp | hge3
        · exact Or.inl (Or.inl (Or.inl ⟨hw, hp⟩))
        · by_cases h3c : cardFactors (sigma 1 (w ^ 4)) = 3
          · exact Or.inl (Or.inr ⟨hw, hqw, h3c⟩)
          · have hodd_v := Nat.odd_iff.mp hodd
            exact Or.inr ⟨hw, hqw, by omega⟩
    · rintro (((⟨hw, _⟩ | ⟨hw, _⟩) | ⟨hw, _⟩) | ⟨hw, _⟩) <;> exact hw
  have hdisj_K_q : Disjoint (quarticChainSources N q) (fineQ13q N q) :=
    Finset.disjoint_left.mpr fun w hw1 hw2 => hK_src_nq w hw1 (Finset.mem_filter.mp hw2).2
  have hdisj_Kq_3 : Disjoint (quarticChainSources N q ∪ fineQ13q N q) (fineQ13_3 N q) := by
    apply Finset.disjoint_left.mpr; intro w hw1 hw2
    obtain ⟨_, hnq, h3c⟩ := Finset.mem_filter.mp hw2
    rcases Finset.mem_union.mp hw1 with hwK | hwq
    · have hp := (hK_mem w hwK).2; rw [cardFactors_apply_prime hp] at h3c; omega
    · exact hnq (Finset.mem_filter.mp hwq).2
  have hdisj_Kq3_5p :
      Disjoint (quarticChainSources N q ∪ fineQ13q N q ∪ fineQ13_3 N q) (fineQ13_5p N q) := by
    apply Finset.disjoint_left.mpr; intro w hw1 hw2
    obtain ⟨_, hnq, h5c⟩ := Finset.mem_filter.mp hw2
    rcases Finset.mem_union.mp hw1 with hwKq | hw3
    · rcases Finset.mem_union.mp hwKq with hwK | hwq
      · have hp := (hK_mem w hwK).2; rw [cardFactors_apply_prime hp] at h5c; omega
      · exact hnq (Finset.mem_filter.mp hwq).2
    · have h3c := (Finset.mem_filter.mp hw3).2.2; omega
  have hE2_Q13 : (oneModThreeLargeSources N q).card =
      (quarticChainSources N q).card + (fineQ13q N q).card +
        (fineQ13_3 N q).card + (fineQ13_5p N q).card := by
    conv_lhs => rw [hQ13_parts]
    rw [Finset.card_union_of_disjoint hdisj_Kq3_5p,
      Finset.card_union_of_disjoint hdisj_Kq_3,
      Finset.card_union_of_disjoint hdisj_K_q]
  have hQ23_parts : twoModThreeLargeSources N q = fineQ23_2 N q ∪ fineQ23_4p N q := by
    ext u
    simp only [fineQ23_2, fineQ23_4p, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hu
      obtain ⟨_, _, hev_cf, _, hge2⟩ := hdich.2 u hu
      have hev_v := Nat.even_iff.mp hev_cf
      by_cases h2c : cardFactors (sigma 1 (u ^ 4)) = 2
      · exact Or.inl ⟨hu, h2c⟩
      · exact Or.inr ⟨hu, by omega⟩
    · rintro (⟨hu, _⟩ | ⟨hu, _⟩) <;> exact hu
  have hQ23_disj : Disjoint (fineQ23_2 N q) (fineQ23_4p N q) := by
    apply Finset.disjoint_left.mpr; intro u h1 h2
    have h2c := (Finset.mem_filter.mp h1).2
    have h4c := (Finset.mem_filter.mp h2).2
    omega
  have hE2_Q23 : (twoModThreeLargeSources N q).card =
      (fineQ23_2 N q).card + (fineQ23_4p N q).card := by
    conv_lhs => rw [hQ23_parts]
    exact Finset.card_union_of_disjoint hQ23_disj
  have hU_Q_Om :
      (quarticChainSources N q).card + (fineQ13q N q).card + 3 * (fineQ13_3 N q).card +
        5 * (fineQ13_5p N q).card + 2 * (fineQ23_2 N q).card + 4 * (fineQ23_4p N q).card ≤
        2 * (fineS51Col N q).card + 2 * (fineS51Rep N q).card := by
    have hid1 := (sixth_power_free_bipartite_multiplicity_identities ho hN hq hq4 he hev hfree).1
    change (∑ u ∈ largeSources N q, cardFactors (sigma 1 (u ^ 4))) +
        (∑ p ∈ fineS51 N, ((q + 1) / 2).factorization p) =
        2 * (fineS51 N).card + ∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization q at hid1
    have hq_tot : ∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization q = (fineQ13q N q).card := by
      rw [hQ_parts, Finset.sum_union hQ_disj, hQ13_q_sum, hq_on_Q23, add_zero]
    have hsum_split :
        ∑ u ∈ largeSources N q, cardFactors (sigma 1 (u ^ 4)) =
          (∑ w ∈ quarticChainSources N q, cardFactors (sigma 1 (w ^ 4))) +
            (∑ w ∈ fineQ13q N q, cardFactors (sigma 1 (w ^ 4))) +
            (∑ w ∈ fineQ13_3 N q, cardFactors (sigma 1 (w ^ 4))) +
            (∑ w ∈ fineQ13_5p N q, cardFactors (sigma 1 (w ^ 4))) +
            (∑ u ∈ fineQ23_2 N q, cardFactors (sigma 1 (u ^ 4))) +
            (∑ u ∈ fineQ23_4p N q, cardFactors (sigma 1 (u ^ 4))) := by
      rw [hQ_parts, Finset.sum_union hQ_disj, hQ13_parts,
        Finset.sum_union hdisj_Kq3_5p, Finset.sum_union hdisj_Kq_3, Finset.sum_union hdisj_K_q,
        hQ23_parts, Finset.sum_union hQ23_disj]
      ring
    have hK_sum : ∑ w ∈ quarticChainSources N q, cardFactors (sigma 1 (w ^ 4)) =
        (quarticChainSources N q).card := by
      calc ∑ w ∈ quarticChainSources N q, cardFactors (sigma 1 (w ^ 4))
            = ∑ _w ∈ quarticChainSources N q, 1 :=
              Finset.sum_congr rfl fun w hw => cardFactors_apply_prime (hK_mem w hw).2
        _ = (quarticChainSources N q).card := by simp [Finset.sum_const]
    have hq_lb : 2 * (fineQ13q N q).card ≤ ∑ w ∈ fineQ13q N q, cardFactors (sigma 1 (w ^ 4)) := by
      calc 2 * (fineQ13q N q).card = ∑ _w ∈ fineQ13q N q, 2 := by simp [Finset.sum_const, Nat.mul_comm]
        _ ≤ ∑ w ∈ fineQ13q N q, cardFactors (sigma 1 (w ^ 4)) := Finset.sum_le_sum fun w hw => by
              obtain ⟨hw_Q13, hqw⟩ := Finset.mem_filter.mp hw
              exact (quartic_oneModThree_euler_dvd_has_S51_col_factor
                ho hN hq hq4 he hev hfree hw_Q13 hqw).1
    have h3_lb : ∑ w ∈ fineQ13_3 N q, cardFactors (sigma 1 (w ^ 4)) = 3 * (fineQ13_3 N q).card := by
      calc ∑ w ∈ fineQ13_3 N q, cardFactors (sigma 1 (w ^ 4)) = ∑ _w ∈ fineQ13_3 N q, 3 :=
            Finset.sum_congr rfl fun w hw => (Finset.mem_filter.mp hw).2.2
        _ = 3 * (fineQ13_3 N q).card := by simp [Finset.sum_const, Nat.mul_comm]
    have h5_lb : 5 * (fineQ13_5p N q).card ≤ ∑ w ∈ fineQ13_5p N q, cardFactors (sigma 1 (w ^ 4)) := by
      calc 5 * (fineQ13_5p N q).card = ∑ _w ∈ fineQ13_5p N q, 5 := by simp [Finset.sum_const, Nat.mul_comm]
        _ ≤ ∑ w ∈ fineQ13_5p N q, cardFactors (sigma 1 (w ^ 4)) :=
          Finset.sum_le_sum fun w hw => (Finset.mem_filter.mp hw).2.2
    have h2_lb : ∑ u ∈ fineQ23_2 N q, cardFactors (sigma 1 (u ^ 4)) = 2 * (fineQ23_2 N q).card := by
      calc ∑ u ∈ fineQ23_2 N q, cardFactors (sigma 1 (u ^ 4)) = ∑ _u ∈ fineQ23_2 N q, 2 :=
            Finset.sum_congr rfl fun u hu => (Finset.mem_filter.mp hu).2
        _ = 2 * (fineQ23_2 N q).card := by simp [Finset.sum_const, Nat.mul_comm]
    have h4_lb : 4 * (fineQ23_4p N q).card ≤ ∑ u ∈ fineQ23_4p N q, cardFactors (sigma 1 (u ^ 4)) := by
      calc 4 * (fineQ23_4p N q).card = ∑ _u ∈ fineQ23_4p N q, 4 := by simp [Finset.sum_const, Nat.mul_comm]
        _ ≤ ∑ u ∈ fineQ23_4p N q, cardFactors (sigma 1 (u ^ 4)) :=
          Finset.sum_le_sum fun u hu => (Finset.mem_filter.mp hu).2
    omega
  have hU_up_Phi5 :
      2 * (quarticChainSources N q).card + (fineQ13_3 N q).card + (fineQ23_2 N q).card ≤
        2 * (fineS51Col N q).card + (fineS51Rep N q).card := by
    let up5 := ((largeSources N q) ×ˢ fineS51 N).filter
      (fun us => us.1 < us.2 ∧ us.2 ∈ (sigma 1 (us.1 ^ 4)).primeFactors)
    have hsub_K : quarticChainSources N q ⊆ largeSources N q := fun w hw =>
      (Finset.mem_filter.mp (hK_mem w hw).1).1
    have hsub_3 : fineQ13_3 N q ⊆ largeSources N q := fun w hw =>
      (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
    have hsub_2 : fineQ23_2 N q ⊆ largeSources N q := fun u hu =>
      (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).1
    have hdisj_K3 : Disjoint (quarticChainSources N q) (fineQ13_3 N q) :=
      Finset.disjoint_left.mpr fun w h1 h2 => by
        have hp := (hK_mem w h1).2
        have h3c := (Finset.mem_filter.mp h2).2.2
        rw [cardFactors_apply_prime hp] at h3c; omega
    have hdisj_K3_2 : Disjoint (quarticChainSources N q ∪ fineQ13_3 N q) (fineQ23_2 N q) := by
      apply Finset.disjoint_left.mpr; intro u h1 h2
      have hu_Q23 := (Finset.mem_filter.mp h2).1
      have hu_Q13 : u ∈ oneModThreeLargeSources N q := by
        rcases Finset.mem_union.mp h1 with hK | h3c
        · exact (hK_mem u hK).1
        · exact (Finset.mem_filter.mp h3c).1
      exact Finset.disjoint_left.mp hQ_disj hu_Q13 hu_Q23
    have hup5_lb : (quarticChainSources N q).card + (fineQ13_3 N q).card + (fineQ23_2 N q).card ≤
        up5.card := by
      have hfib : up5.card = ∑ u ∈ largeSources N q, (up5.filter (fun us => us.1 = u)).card :=
        Finset.card_eq_sum_card_fiberwise fun us hus =>
          (Finset.mem_product.mp (Finset.mem_filter.mp hus).1).1
      have hunion_sub : quarticChainSources N q ∪ fineQ13_3 N q ∪ fineQ23_2 N q ⊆ largeSources N q :=
        Finset.union_subset (Finset.union_subset hsub_K hsub_3) hsub_2
      have hcard_union : (quarticChainSources N q ∪ fineQ13_3 N q ∪ fineQ23_2 N q).card =
          (quarticChainSources N q).card + (fineQ13_3 N q).card + (fineQ23_2 N q).card := by
        rw [Finset.card_union_of_disjoint hdisj_K3_2, Finset.card_union_of_disjoint hdisj_K3]
      have hex_gt : ∀ u ∈ quarticChainSources N q ∪ fineQ13_3 N q ∪ fineQ23_2 N q,
          1 ≤ (up5.filter (fun us => us.1 = u)).card := by
        intro u hu
        rcases Finset.mem_union.mp hu with huK3 | hu2
        · rcases Finset.mem_union.mp huK3 with huK | hu3
          · have hu_lg := hsub_K huK
            have hu_prime := (hlg_prop u hu_lg).1
            have hu_sig_prime := (hK_mem u huK).2
            let s := sigma 1 (u ^ 4)
            have hs_int : s ∈ quarticChainIntermediates N q := Finset.mem_image.mpr ⟨u, huK, rfl⟩
            have hs_S51 : s ∈ fineS51 N := (Finset.mem_filter.mp (hK_int_col hs_int)).1
            have hus_lt : u < s := by
              dsimp [s]; rw [sigma_one_four_local hu_prime]
              have : u < u ^ 2 := by nlinarith only [hu_prime.two_le]
              omega
            have hs_pf : s ∈ (sigma 1 (u ^ 4)).primeFactors :=
              Nat.mem_primeFactors.mpr ⟨hu_sig_prime, dvd_rfl, hu_sig_prime.ne_zero⟩
            exact Finset.card_pos.mpr ⟨(u, s), Finset.mem_filter.mpr
              ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu_lg, hs_S51⟩, hus_lt, hs_pf⟩, rfl⟩⟩
          · obtain ⟨hu_Q13, hu_nq, hu_cf3⟩ := Finset.mem_filter.mp hu3
            have hu_lg := (Finset.mem_filter.mp hu_Q13).1
            have hu_prime := (hlg_prop u hu_lg).1
            have hsig_eq : sigma 1 (u ^ 4) = u ^ 4 + u ^ 3 + u ^ 2 + u + 1 :=
              sigma_one_four_local hu_prime
            have hsig_ne0 : sigma 1 (u ^ 4) ≠ 0 := by rw [hsig_eq]; positivity
            have hw_prop := (hdich.1 u hu_Q13 hu_nq).1
            have hex : ∃ s ∈ (sigma 1 (u ^ 4)).primeFactors, u < s := by
              by_contra! hall
              have hprod_le : sigma 1 (u ^ 4) ≤ u ^ 3 := by
                calc sigma 1 (u ^ 4)
                    = ∏ p ∈ (sigma 1 (u ^ 4)).primeFactors,
                        p ^ (sigma 1 (u ^ 4)).factorization p :=
                      Nat.prod_primeFactors_pow_factorization hsig_ne0
                  _ ≤ ∏ p ∈ (sigma 1 (u ^ 4)).primeFactors,
                        u ^ (sigma 1 (u ^ 4)).factorization p :=
                      Finset.prod_le_prod fun p hp => Nat.pow_le_pow_left (hall p hp) _
                  _ = u ^ (∑ p ∈ (sigma 1 (u ^ 4)).primeFactors,
                        (sigma 1 (u ^ 4)).factorization p) := Finset.prod_pow_eq_pow_sum _ _ _
                  _ = u ^ cardFactors (sigma 1 (u ^ 4)) := by
                      rw [cardFactors_eq_sum_factorization, Finsupp.sum]; rfl
                  _ = u ^ 3 := by rw [hu_cf3]
              have hlt : u ^ 3 < sigma 1 (u ^ 4) := by rw [hsig_eq]; omega
              omega
            obtain ⟨s, hs_pf, hus_lt⟩ := hex
            exact Finset.card_pos.mpr ⟨(u, s), Finset.mem_filter.mpr
              ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu_lg, (hw_prop s hs_pf).1⟩,
                hus_lt, hs_pf⟩, rfl⟩⟩
        · obtain ⟨hu_Q23, hu_cf2⟩ := Finset.mem_filter.mp hu2
          have hu_lg := (Finset.mem_filter.mp hu_Q23).1
          have hu_prime := (hlg_prop u hu_lg).1
          have hsig_eq : sigma 1 (u ^ 4) = u ^ 4 + u ^ 3 + u ^ 2 + u + 1 :=
            sigma_one_four_local hu_prime
          have hsig_ne0 : sigma 1 (u ^ 4) ≠ 0 := by rw [hsig_eq]; positivity
          have hw_prop := (hdich.2 u hu_Q23).2.1
          have hex : ∃ s ∈ (sigma 1 (u ^ 4)).primeFactors, u < s := by
            by_contra! hall
            have hprod_le : sigma 1 (u ^ 4) ≤ u ^ 2 := by
              calc sigma 1 (u ^ 4)
                  = ∏ p ∈ (sigma 1 (u ^ 4)).primeFactors,
                      p ^ (sigma 1 (u ^ 4)).factorization p :=
                    Nat.prod_primeFactors_pow_factorization hsig_ne0
                _ ≤ ∏ p ∈ (sigma 1 (u ^ 4)).primeFactors,
                      u ^ (sigma 1 (u ^ 4)).factorization p :=
                    Finset.prod_le_prod fun p hp => Nat.pow_le_pow_left (hall p hp) _
                _ = u ^ (∑ p ∈ (sigma 1 (u ^ 4)).primeFactors,
                      (sigma 1 (u ^ 4)).factorization p) := Finset.prod_pow_eq_pow_sum _ _ _
                _ = u ^ cardFactors (sigma 1 (u ^ 4)) := by
                    rw [cardFactors_eq_sum_factorization, Finsupp.sum]; rfl
                _ = u ^ 2 := by rw [hu_cf2]
            have hlt : u ^ 2 < sigma 1 (u ^ 4) := by rw [hsig_eq]; omega
            omega
          obtain ⟨s, hs_pf, hus_lt⟩ := hex
          exact Finset.card_pos.mpr ⟨(u, s), Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu_lg, (hw_prop s hs_pf).1⟩,
              hus_lt, hs_pf⟩, rfl⟩⟩
      calc (quarticChainSources N q).card + (fineQ13_3 N q).card + (fineQ23_2 N q).card
          = (quarticChainSources N q ∪ fineQ13_3 N q ∪ fineQ23_2 N q).card := hcard_union.symm
        _ = ∑ _u ∈ quarticChainSources N q ∪ fineQ13_3 N q ∪ fineQ23_2 N q, 1 := by
            simp [Finset.sum_const]
        _ ≤ ∑ u ∈ quarticChainSources N q ∪ fineQ13_3 N q ∪ fineQ23_2 N q,
              (up5.filter (fun us => us.1 = u)).card := Finset.sum_le_sum hex_gt
        _ ≤ ∑ u ∈ largeSources N q, (up5.filter (fun us => us.1 = u)).card :=
            Finset.sum_le_sum_of_subset hunion_sub
        _ = up5.card := hfib.symm
    have hup5_ub : up5.card ≤ (quarticChainSources N q).card +
        2 * ((fineS51Col N q).card - (quarticChainSources N q).card) + (fineS51Rep N q).card := by
      have hfib : up5.card = ∑ s ∈ fineS51 N, (up5.filter (fun us => us.2 = s)).card :=
        Finset.card_eq_sum_card_fiberwise fun us hus =>
          (Finset.mem_product.mp (Finset.mem_filter.mp hus).1).2
      have hS51_parts : fineS51 N =
          quarticChainIntermediates N q ∪ (fineS51Col N q \ quarticChainIntermediates N q) ∪
            fineS51Rep N q := by
        ext s
        simp only [fineS51Col, fineS51Rep, Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter]
        constructor
        · intro hs
          by_cases hK : s ∈ quarticChainIntermediates N q
          · exact Or.inl (Or.inl hK)
          · have hs_col_or_rep : s ∈ fineS51Col N q ∨ s ∈ fineS51Rep N q := by
              rw [hS51_u] at hs; exact Finset.mem_union.mp hs
            rcases hs_col_or_rep with hcol | hrep
            · exact Or.inl (Or.inr ⟨⟨hs, (Finset.mem_filter.mp hcol).2⟩, hK⟩)
            · exact Or.inr (Finset.mem_filter.mp hrep)
        · rintro ((hK | ⟨⟨hs, _⟩, _⟩) | ⟨hs, _⟩)
          · exact (Finset.mem_filter.mp (hK_int_col hK)).1
          · exact hs
          · exact hs
      have hdisj1 : Disjoint (quarticChainIntermediates N q)
          (fineS51Col N q \ quarticChainIntermediates N q) := Finset.sdiff_disjoint.symm
      have hdisj2 : Disjoint
          (quarticChainIntermediates N q ∪ (fineS51Col N q \ quarticChainIntermediates N q))
          (fineS51Rep N q) :=
        Finset.disjoint_union_left.mpr
          ⟨hS51_disj.mono_left hK_int_col, hS51_disj.mono_left Finset.sdiff_subset⟩
      have hfib_le_indeg : ∀ s ∈ fineS51 N, (up5.filter (fun us => us.2 = s)).card ≤ indegAt N q s := by
        intro s _
        refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
        · intro us hus
          obtain ⟨hus_up, rfl⟩ := Finset.mem_filter.mp hus
          obtain ⟨hus_prod, _, hs_pf⟩ := Finset.mem_filter.mp hus_up
          have hu_lg := (Finset.mem_product.mp hus_prod).1
          have hu_mem := (Finset.mem_filter.mp hu_lg).1
          obtain ⟨_, _, _, hu_neq, hu_exp⟩ := hlg_prop us.1 hu_lg
          have hcomp : oddComponentSigma N q us.1 = sigma 1 (us.1 ^ 4) := by
            unfold oddComponentSigma; simp [hu_neq, hu_exp]
          exact Finset.mem_filter.mpr ⟨hu_mem, hcomp.symm ▸ hs_pf⟩
        · intro ⟨u₁, s₁⟩ h1 ⟨u₂, s₂⟩ h2 heq
          have hs1 : s₁ = s := (Finset.mem_filter.mp h1).2
          have hs2 : s₂ = s := (Finset.mem_filter.mp h2).2
          dsimp only at heq; ext <;> simp [heq, hs1, hs2]
      have hK_le1 : ∀ s ∈ quarticChainIntermediates N q,
          (up5.filter (fun us => us.2 = s)).card ≤ 1 := by
        intro s hs
        obtain ⟨w₀, hw₀_K, rfl⟩ := Finset.mem_image.mp hs
        have hw₀_lg := (Finset.mem_filter.mp (hK_mem w₀ hw₀_K).1).1
        have hw₀_prime := (hlg_prop w₀ hw₀_lg).1
        have hs_prime := (hK_mem w₀ hw₀_K).2
        have hs_eq : sigma 1 (w₀ ^ 4) = quarticPoly w₀ := sigma_one_four_local hw₀_prime
        have hs_qprime : (quarticPoly w₀).Prime := hs_eq ▸ hs_prime
        have huniq := quarticChainIntermediate_unique_prime_source_lt hw₀_prime hs_qprime
        have hsub : up5.filter (fun us => us.2 = sigma 1 (w₀ ^ 4)) ⊆ {(w₀, sigma 1 (w₀ ^ 4))} := by
          intro us hus
          obtain ⟨hus_up, hs_us⟩ := Finset.mem_filter.mp hus
          obtain ⟨hus_prod, hus_lt, hs_pf⟩ := Finset.mem_filter.mp hus_up
          have hu_lg := (Finset.mem_product.mp hus_prod).1
          have hu_prime := (hlg_prop us.1 hu_lg).1
          have hs_dvd : quarticPoly w₀ ∣ quarticPoly us.1 := by
            have hq_eq : quarticPoly us.1 = sigma 1 (us.1 ^ 4) :=
              (sigma_one_four_local hu_prime).symm
            rw [← hs_eq, ← hs_us, hq_eq]
            exact Nat.dvd_of_mem_primeFactors hs_pf
          have hu_lt : us.1 < quarticPoly w₀ := by rw [← hs_eq, ← hs_us]; exact hus_lt
          have hu_eq := Finset.mem_singleton.mp
            (huniq (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hu_lt, hu_prime, hs_dvd⟩))
          exact Finset.mem_singleton.mpr (Prod.ext hu_eq hs_us)
        exact (Finset.card_le_card hsub).trans (by simp)
      have hcol_le2 : ∀ s ∈ fineS51Col N q \ quarticChainIntermediates N q,
          (up5.filter (fun us => us.2 = s)).card ≤ 2 := by
        intro s hs
        have hs_col := (Finset.mem_sdiff.mp hs).1
        have hi2 : indegAt N q s = 2 := (Finset.mem_filter.mp hs_col).2
        exact (hfib_le_indeg s (Finset.mem_filter.mp hs_col).1).trans (by omega)
      have hrep_le1 : ∀ s ∈ fineS51Rep N q, (up5.filter (fun us => us.2 = s)).card ≤ 1 := by
        intro s hs
        have hi1 : indegAt N q s = 1 := (Finset.mem_filter.mp hs).2
        exact (hfib_le_indeg s (Finset.mem_filter.mp hs).1).trans (by omega)
      rw [hfib, hS51_parts, Finset.sum_union hdisj2, Finset.sum_union hdisj1]
      have h1 : ∑ s ∈ quarticChainIntermediates N q, (up5.filter (fun us => us.2 = s)).card ≤
          (quarticChainSources N q).card := by
        calc ∑ s ∈ quarticChainIntermediates N q, (up5.filter (fun us => us.2 = s)).card
              ≤ ∑ _s ∈ quarticChainIntermediates N q, 1 := Finset.sum_le_sum hK_le1
          _ = (quarticChainIntermediates N q).card := by simp [Finset.sum_const]
          _ = (quarticChainSources N q).card := hK_card
      have h2 : ∑ s ∈ fineS51Col N q \ quarticChainIntermediates N q,
            (up5.filter (fun us => us.2 = s)).card ≤
          2 * ((fineS51Col N q).card - (quarticChainSources N q).card) := by
        calc ∑ s ∈ fineS51Col N q \ quarticChainIntermediates N q,
              (up5.filter (fun us => us.2 = s)).card
              ≤ ∑ _s ∈ fineS51Col N q \ quarticChainIntermediates N q, 2 := Finset.sum_le_sum hcol_le2
          _ = 2 * (fineS51Col N q \ quarticChainIntermediates N q).card := by
              simp [Finset.sum_const, Nat.mul_comm]
          _ = 2 * ((fineS51Col N q).card - (quarticChainSources N q).card) := by
              rw [Finset.card_sdiff_of_subset hK_int_col, hK_card]
      have h3s : ∑ s ∈ fineS51Rep N q, (up5.filter (fun us => us.2 = s)).card ≤
          (fineS51Rep N q).card := by
        calc ∑ s ∈ fineS51Rep N q, (up5.filter (fun us => us.2 = s)).card
              ≤ ∑ _s ∈ fineS51Rep N q, 1 := Finset.sum_le_sum hrep_le1
          _ = (fineS51Rep N q).card := by simp [Finset.sum_const]
      omega
    have hK_le_col : (quarticChainSources N q).card ≤ (fineS51Col N q).card := by
      rw [← hK_card]; exact Finset.card_le_card hK_int_col
    omega
  exact ⟨hE1_q, hE2_Q13, hE2_Q23, hU_Q_Om, hU_up_Phi5⟩

private theorem fine_block_and_target_conservation {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    (fineSp N q).card + (fineS2 N q).card + (fineS3p N q).card + (quarticChainSources N q).card =
      (fineS50 N).card + (fineS51Col N q).card + (fineS51Rep N q).card ∧
    (fineKA1 N q).card + (fineKA2 N q).card + (fineKA3p N q).card = (quarticChainSources N q).card ∧
    (fineKB1 N q).card + (fineKB26 N q).card + (fineKB7p N q).card = (quarticChainSources N q).card ∧
    (fineT4 N q).card + (fineT31 N q).card + (fineT22 N q).card +
      (fineT211 N q).card + (fineT1111 N q).card = (oneModThreeLargeSources N q).card ∧
    (∑ r ∈ oneModThreeLargeSources N q, (indegAt N q r - 1)) =
      (fineT31 N q).card + (fineT22 N q).card + 2 * (fineT211 N q).card + 3 * (fineT1111 N q).card ∧
    (fineHQe N q 1 + (fineSp N q).card + 2 * (fineS2 N q).card + fineS3pe N q 1 +
      (fineKA1 N q).card + 2 * (fineKA2 N q).card + fineA3pe N q 1 +
      (fineKB1 N q).card + fineB26e N q 1 + fineB7pe N q 1 =
      (fineSqQ N q).card + (fineT31 N q).card + 2 * (fineT211 N q).card + 4 * (fineT1111 N q).card) ∧
    (fineHQe N q 2 + fineS3pe N q 2 + fineA3pe N q 2 + fineB26e N q 2 + fineB7pe N q 2 =
      2 * (fineT22 N q).card + (fineT211 N q).card) ∧
    (fineHQe N q 3 + fineS3pe N q 3 + fineA3pe N q 3 + fineB26e N q 3 + fineB7pe N q 3 =
      (fineT31 N q).card) ∧
    (fineHQe N q 4 + fineS3pe N q 4 + fineA3pe N q 4 + fineB26e N q 4 + fineB7pe N q 4 =
      (fineT4 N q).card) ∧
    (3 * (fineS3p N q).card ≤
      fineS3pe N q 1 + 2 * fineS3pe N q 2 + 3 * fineS3pe N q 3 + 4 * fineS3pe N q 4 ∧
      2 * (fineS3p N q).card ≤ fineS3pe N q 1 + fineS3pe N q 2 + fineS3pe N q 3 + fineS3pe N q 4 ∧
      (fineS3p N q).card ≤ fineS3pe N q 1 + fineS3pe N q 2 + fineS3pe N q 4) ∧
    (3 * (fineKA3p N q).card ≤
      fineA3pe N q 1 + 2 * fineA3pe N q 2 + 3 * fineA3pe N q 3 + 4 * fineA3pe N q 4 ∧
      2 * (fineKA3p N q).card ≤ fineA3pe N q 1 + fineA3pe N q 2 + fineA3pe N q 3 + fineA3pe N q 4 ∧
      (fineKA3p N q).card ≤ fineA3pe N q 1 + fineA3pe N q 2 + fineA3pe N q 4) ∧
    (2 * (fineKB26 N q).card ≤
      fineB26e N q 1 + 2 * fineB26e N q 2 + 3 * fineB26e N q 3 + 4 * fineB26e N q 4 ∧
      2 * (fineKB26 N q).card ≤ fineB26e N q 1 + fineB26e N q 2 + fineB26e N q 3 + fineB26e N q 4 ∧
      (fineKB26 N q).card ≤ fineB26e N q 1 + fineB26e N q 2 + fineB26e N q 4) ∧
    (7 * (fineKB7p N q).card ≤
      fineB7pe N q 1 + 2 * fineB7pe N q 2 + 3 * fineB7pe N q 3 + 4 * fineB7pe N q 4 ∧
      (fineKB7p N q).card ≤ fineB7pe N q 1 + fineB7pe N q 2 + fineB7pe N q 4) := by
  obtain ⟨_, _, hq1, _, hsq_prop, hlg_prop, hparts, hq_notin, _, hN_le4⟩ :=
    sixth_power_free_source_invariants ho hN hq hq4 he hev hfree
  have hq_prime := Nat.prime_of_mem_primeFactors hq
  have hq_odd : Odd q := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)
  obtain ⟨hcons, _, _⟩ := factorization_eq_indegAt_add_localRepeatAt ho hN hq hq4 he hev
  obtain ⟨_, _, hS51_card, _, _, _⟩ :=
    sixth_power_free_S51_collision_repeat_split ho hN hq hq4 he hev hfree
  change (fineS51 N).card = (fineS51Col N q).card + (fineS51Rep N q).card at hS51_card
  obtain ⟨hK_src_eq, _, hK_int_col, hK_card⟩ :=
    quarticChainSources_eq_oneModThree_prime_and_card ho hN hq hq4 he hev hfree
  change quarticChainIntermediates N q ⊆ fineS51Col N q at hK_int_col
  have hK_mem : ∀ w ∈ quarticChainSources N q,
      w ∈ oneModThreeLargeSources N q ∧ (sigma 1 (w ^ 4)).Prime := fun w hw => by
    rw [hK_src_eq] at hw; exact Finset.mem_filter.mp hw
  have hK_int_sq : quarticChainIntermediates N q ⊆ squareSources N := fun s hs =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp (hK_int_col hs)).1).1
  have hS_parts : squareSources N = fineS50 N ∪ fineS51 N := by
    ext s; simp only [fineS50, fineS51, Finset.mem_union, Finset.mem_filter]
    by_cases h : s % 5 = 1 <;> tauto
  have hS_disj : Disjoint (fineS50 N) (fineS51 N) :=
    Finset.disjoint_left.mpr fun s h1 h2 => (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
  have hS_card : (squareSources N).card =
      (fineS50 N).card + (fineS51Col N q).card + (fineS51Rep N q).card := by
    rw [hS_parts, Finset.card_union_of_disjoint hS_disj, hS51_card]; omega
  have hSnc_parts : fineSnc N q = fineSp N q ∪ fineS2 N q ∪ fineS3p N q := by
    ext s
    simp only [fineSp, fineS2, fineS3p, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hs
      have hs_sq := (Finset.mem_sdiff.mp hs).1
      have hs_prime := (hsq_prop s hs_sq).1
      have hgt1 : 1 < sigma 1 (s ^ 2) := by
        rw [sigma_one_sq_local hs_prime]; nlinarith only [hs_prime.two_le]
      have hpos : 0 < cardFactors (sigma 1 (s ^ 2)) := cardFactors_pos_iff_one_lt.mpr hgt1
      by_cases h1 : cardFactors (sigma 1 (s ^ 2)) = 1
      · exact Or.inl (Or.inl ⟨hs, h1⟩)
      · by_cases h2 : cardFactors (sigma 1 (s ^ 2)) = 2
        · exact Or.inl (Or.inr ⟨hs, h2⟩)
        · exact Or.inr ⟨hs, by omega⟩
    · rintro ((⟨hs, _⟩ | ⟨hs, _⟩) | ⟨hs, _⟩) <;> exact hs
  have hS_p_2_disj : Disjoint (fineSp N q) (fineS2 N q) :=
    Finset.disjoint_left.mpr fun s h1 h2 => by
      have c1 := (Finset.mem_filter.mp h1).2; have c2 := (Finset.mem_filter.mp h2).2; omega
  have hS_p2_3p_disj : Disjoint (fineSp N q ∪ fineS2 N q) (fineS3p N q) :=
    Finset.disjoint_left.mpr fun s h1 h2 => by
      have c3 := (Finset.mem_filter.mp h2).2
      rcases Finset.mem_union.mp h1 with h1' | h2'
      · have c1 := (Finset.mem_filter.mp h1').2; omega
      · have c2 := (Finset.mem_filter.mp h2').2; omega
  have hE3_Snc : (fineSp N q).card + (fineS2 N q).card + (fineS3p N q).card +
      (quarticChainSources N q).card =
      (fineS50 N).card + (fineS51Col N q).card + (fineS51Rep N q).card := by
    have hnc_card : (fineSnc N q).card = (fineSp N q).card + (fineS2 N q).card + (fineS3p N q).card := by
      conv_lhs => rw [hSnc_parts]
      rw [Finset.card_union_of_disjoint hS_p2_3p_disj, Finset.card_union_of_disjoint hS_p_2_disj]
    have hsdiff : (fineSnc N q).card = (squareSources N).card - (quarticChainIntermediates N q).card :=
      Finset.card_sdiff_of_subset hK_int_sq
    have hK_le : (quarticChainIntermediates N q).card ≤ (squareSources N).card :=
      Finset.card_le_card hK_int_sq
    omega
  have hkA_parts : quarticChainSources N q = fineKA1 N q ∪ fineKA2 N q ∪ fineKA3p N q := by
    ext w
    simp only [fineKA1, fineKA2, fineKA3p, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hw
      have hw_lg := (Finset.mem_filter.mp (hK_mem w hw).1).1
      have hw53 := (hlg_prop w hw_lg).2.2.1
      have hgt1 : 1 < quarticFirstFactor w := by
        unfold quarticFirstFactor
        have : w + 1 ≤ w ^ 2 := by nlinarith only [hw53]
        omega
      have hpos : 0 < cardFactors (quarticFirstFactor w) := cardFactors_pos_iff_one_lt.mpr hgt1
      by_cases h1 : cardFactors (quarticFirstFactor w) = 1
      · exact Or.inl (Or.inl ⟨hw, h1⟩)
      · by_cases h2 : cardFactors (quarticFirstFactor w) = 2
        · exact Or.inl (Or.inr ⟨hw, h2⟩)
        · exact Or.inr ⟨hw, by omega⟩
    · rintro ((⟨hw, _⟩ | ⟨hw, _⟩) | ⟨hw, _⟩) <;> exact hw
  have hdisj_A12 : Disjoint (fineKA1 N q) (fineKA2 N q) :=
    Finset.disjoint_left.mpr fun w h1 h2 => by
      have c1 := (Finset.mem_filter.mp h1).2; have c2 := (Finset.mem_filter.mp h2).2; omega
  have hdisj_A12_3p : Disjoint (fineKA1 N q ∪ fineKA2 N q) (fineKA3p N q) :=
    Finset.disjoint_left.mpr fun w h1 h2 => by
      have c3 := (Finset.mem_filter.mp h2).2
      rcases Finset.mem_union.mp h1 with h1' | h2'
      · have c1 := (Finset.mem_filter.mp h1').2; omega
      · have c2 := (Finset.mem_filter.mp h2').2; omega
  have hE3_chA : (fineKA1 N q).card + (fineKA2 N q).card + (fineKA3p N q).card =
      (quarticChainSources N q).card := by
    conv_rhs => rw [hkA_parts]
    rw [Finset.card_union_of_disjoint hdisj_A12_3p, Finset.card_union_of_disjoint hdisj_A12]
  have hkB_parts : quarticChainSources N q = fineKB1 N q ∪ fineKB26 N q ∪ fineKB7p N q := by
    ext w
    simp only [fineKB1, fineKB26, fineKB7p, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hw
      have hw_lg := (Finset.mem_filter.mp (hK_mem w hw).1).1
      have hw53 := (hlg_prop w hw_lg).2.2.1
      have hgt1 : 1 < quarticSecondFactor w := by unfold quarticSecondFactor; omega
      have hpos : 0 < cardFactors (quarticSecondFactor w) := cardFactors_pos_iff_one_lt.mpr hgt1
      by_cases h1 : cardFactors (quarticSecondFactor w) = 1
      · exact Or.inl (Or.inl ⟨hw, h1⟩)
      · by_cases h6 : cardFactors (quarticSecondFactor w) ≤ 6
        · exact Or.inl (Or.inr ⟨hw, by omega, h6⟩)
        · exact Or.inr ⟨hw, by omega⟩
    · rintro ((⟨hw, _⟩ | ⟨hw, _⟩) | ⟨hw, _⟩) <;> exact hw
  have hdisj_B1_26 : Disjoint (fineKB1 N q) (fineKB26 N q) :=
    Finset.disjoint_left.mpr fun w h1 h2 => by
      have c1 := (Finset.mem_filter.mp h1).2; have c2 := (Finset.mem_filter.mp h2).2.1; omega
  have hdisj_B126_7p : Disjoint (fineKB1 N q ∪ fineKB26 N q) (fineKB7p N q) :=
    Finset.disjoint_left.mpr fun w h1 h2 => by
      have c7 := (Finset.mem_filter.mp h2).2
      rcases Finset.mem_union.mp h1 with h1' | h2'
      · have c1 := (Finset.mem_filter.mp h1').2; omega
      · have c6 := (Finset.mem_filter.mp h2').2.2; omega
  have hE3_chB : (fineKB1 N q).card + (fineKB26 N q).card + (fineKB7p N q).card =
      (quarticChainSources N q).card := by
    conv_rhs => rw [hkB_parts]
    rw [Finset.card_union_of_disjoint hdisj_B126_7p, Finset.card_union_of_disjoint hdisj_B1_26]
  have hQ13_indeg_range : ∀ r ∈ oneModThreeLargeSources N q, 1 ≤ indegAt N q r ∧ indegAt N q r ≤ 4 := by
    intro r hr
    have hr_lg := (Finset.mem_filter.mp hr).1
    have hr_mem := (Finset.mem_filter.mp hr_lg).1
    have hr_exp4 := (hlg_prop r hr_lg).2.2.2.2
    obtain ⟨h1, _, hle⟩ := hcons r hr_mem
    exact ⟨h1, by omega⟩
  have hT_parts : oneModThreeLargeSources N q =
      fineT4 N q ∪ fineT31 N q ∪ fineT22 N q ∪ fineT211 N q ∪ fineT1111 N q := by
    ext r
    simp only [fineT4, fineT31, fineT22, fineT211, fineT1111, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hr
      obtain ⟨h1, h4⟩ := hQ13_indeg_range r hr
      rcases (show indegAt N q r = 1 ∨ indegAt N q r = 2 ∨
          indegAt N q r = 3 ∨ indegAt N q r = 4 by omega) with h | h | h | h
      · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨hr, h⟩)))
      · by_cases ho_r : ∃ p ∈ N.primeFactors, Odd ((oddComponentSigma N q p).factorization r)
        · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hr, h, ho_r⟩)))
        · exact Or.inl (Or.inl (Or.inr ⟨hr, h, ho_r⟩))
      · exact Or.inl (Or.inr ⟨hr, h⟩)
      · exact Or.inr ⟨hr, h⟩
    · rintro ((((⟨hr, _⟩ | ⟨hr, _⟩) | ⟨hr, _⟩) | ⟨hr, _⟩) | ⟨hr, _⟩) <;> exact hr
  have hT_disj1 : Disjoint (fineT4 N q) (fineT31 N q) :=
    Finset.disjoint_left.mpr fun r h1 h2 => by
      have c1 := (Finset.mem_filter.mp h1).2; have c2 := (Finset.mem_filter.mp h2).2.1; omega
  have hT_disj2 : Disjoint (fineT4 N q ∪ fineT31 N q) (fineT22 N q) :=
    Finset.disjoint_left.mpr fun r h1 h2 => by
      obtain ⟨_, c2, hno⟩ := Finset.mem_filter.mp h2
      rcases Finset.mem_union.mp h1 with h | h
      · have c1 := (Finset.mem_filter.mp h).2; omega
      · exact hno (Finset.mem_filter.mp h).2.2
  have hT_disj3 : Disjoint (fineT4 N q ∪ fineT31 N q ∪ fineT22 N q) (fineT211 N q) :=
    Finset.disjoint_left.mpr fun r h1 h2 => by
      have c3 := (Finset.mem_filter.mp h2).2
      rcases Finset.mem_union.mp h1 with h431 | h22
      · rcases Finset.mem_union.mp h431 with h4 | h31
        · have := (Finset.mem_filter.mp h4).2; omega
        · have := (Finset.mem_filter.mp h31).2.1; omega
      · have := (Finset.mem_filter.mp h22).2.1; omega
  have hT_disj4 : Disjoint (fineT4 N q ∪ fineT31 N q ∪ fineT22 N q ∪ fineT211 N q) (fineT1111 N q) :=
    Finset.disjoint_left.mpr fun r h1 h2 => by
      have c4 := (Finset.mem_filter.mp h2).2
      rcases Finset.mem_union.mp h1 with h43122 | h211
      · rcases Finset.mem_union.mp h43122 with h431 | h22
        · rcases Finset.mem_union.mp h431 with h4 | h31
          · have := (Finset.mem_filter.mp h4).2; omega
          · have := (Finset.mem_filter.mp h31).2.1; omega
        · have := (Finset.mem_filter.mp h22).2.1; omega
      · have := (Finset.mem_filter.mp h211).2; omega
  have hE3_tgt : (fineT4 N q).card + (fineT31 N q).card + (fineT22 N q).card +
      (fineT211 N q).card + (fineT1111 N q).card = (oneModThreeLargeSources N q).card := by
    conv_rhs => rw [hT_parts]
    rw [Finset.card_union_of_disjoint hT_disj4, Finset.card_union_of_disjoint hT_disj3,
      Finset.card_union_of_disjoint hT_disj2, Finset.card_union_of_disjoint hT_disj1]
  have hEQ13_eq : (∑ r ∈ oneModThreeLargeSources N q, (indegAt N q r - 1)) =
      (fineT31 N q).card + (fineT22 N q).card + 2 * (fineT211 N q).card + 3 * (fineT1111 N q).card := by
    conv_lhs => rw [hT_parts]
    rw [Finset.sum_union hT_disj4, Finset.sum_union hT_disj3,
      Finset.sum_union hT_disj2, Finset.sum_union hT_disj1]
    have s4 : ∑ r ∈ fineT4 N q, (indegAt N q r - 1) = 0 :=
      Finset.sum_eq_zero fun r hr => by have := (Finset.mem_filter.mp hr).2; omega
    have s31 : ∑ r ∈ fineT31 N q, (indegAt N q r - 1) = (fineT31 N q).card := by
      calc ∑ r ∈ fineT31 N q, (indegAt N q r - 1) = ∑ _r ∈ fineT31 N q, 1 :=
            Finset.sum_congr rfl fun r hr => by have := (Finset.mem_filter.mp hr).2.1; omega
        _ = (fineT31 N q).card := by simp [Finset.sum_const]
    have s22 : ∑ r ∈ fineT22 N q, (indegAt N q r - 1) = (fineT22 N q).card := by
      calc ∑ r ∈ fineT22 N q, (indegAt N q r - 1) = ∑ _r ∈ fineT22 N q, 1 :=
            Finset.sum_congr rfl fun r hr => by have := (Finset.mem_filter.mp hr).2.1; omega
        _ = (fineT22 N q).card := by simp [Finset.sum_const]
    have s211 : ∑ r ∈ fineT211 N q, (indegAt N q r - 1) = 2 * (fineT211 N q).card := by
      calc ∑ r ∈ fineT211 N q, (indegAt N q r - 1) = ∑ _r ∈ fineT211 N q, 2 :=
            Finset.sum_congr rfl fun r hr => by have := (Finset.mem_filter.mp hr).2; omega
        _ = 2 * (fineT211 N q).card := by simp [Finset.sum_const, Nat.mul_comm]
    have s1111 : ∑ r ∈ fineT1111 N q, (indegAt N q r - 1) = 3 * (fineT1111 N q).card := by
      calc ∑ r ∈ fineT1111 N q, (indegAt N q r - 1) = ∑ _r ∈ fineT1111 N q, 3 :=
            Finset.sum_congr rfl fun r hr => by have := (Finset.mem_filter.mp hr).2; omega
        _ = 3 * (fineT1111 N q).card := by simp [Finset.sum_const, Nat.mul_comm]
    rw [s4, s31, s22, s211, s1111, zero_add]
  have hsq_le4 : ∀ s ∈ squareSources N, ∀ r ∈ (sigma 1 (s ^ 2)).primeFactors,
      (sigma 1 (s ^ 2)).factorization r ≤ 4 := by
    intro s hs r hr
    have hs_sq_pf : s ∈ N.primeFactors := (Finset.mem_filter.mp hs).1
    have hs_exp := (hsq_prop s hs).2.2.2.2
    have hr_sub := sq_sigma_primeFactors_subset ho hN hq hq4 he hev hfree hs hr
    have hr_N : r ∈ N.primeFactors := by
      rcases Finset.mem_insert.mp hr_sub with rfl | hrQ
      · exact hq
      · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hrQ).1).1
    have hr_prime := Nat.prime_of_mem_primeFactors hr_N
    have hr_odd := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr_N)
    have hsum := factorization_eq_sum_sigma_factorizations hN hr_odd hr_prime
    have hle := Finset.single_le_sum
      (f := fun p => (sigma 1 (p ^ N.factorization p)).factorization r)
      (fun _ _ => Nat.zero_le _) hs_sq_pf
    rw [hs_exp] at hle
    have := hN_le4 r hr_N; omega
  have hS3p_inv :
      3 * (fineS3p N q).card ≤
        fineS3pe N q 1 + 2 * fineS3pe N q 2 + 3 * fineS3pe N q 3 + 4 * fineS3pe N q 4 ∧
      2 * (fineS3p N q).card ≤
        fineS3pe N q 1 + fineS3pe N q 2 + fineS3pe N q 3 + fineS3pe N q 4 ∧
      (fineS3p N q).card ≤ fineS3pe N q 1 + fineS3pe N q 2 + fineS3pe N q 4 := by
    have hpt : ∀ s ∈ fineS3p N q,
        let M := sigma 1 (s ^ 2)
        3 ≤ expCount M 1 + 2 * expCount M 2 + 3 * expCount M 3 + 4 * expCount M 4 ∧
        2 ≤ expCount M 1 + expCount M 2 + expCount M 3 + expCount M 4 ∧
        1 ≤ expCount M 1 + expCount M 2 + expCount M 4 := by
      intro s hs
      have hs_sq := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hs).1).1
      have hs_cf3 : 3 ≤ cardFactors (sigma 1 (s ^ 2)) := (Finset.mem_filter.mp hs).2
      obtain ⟨hs_prime, hs_mod3, _, _, _⟩ := hsq_prop s hs_sq
      have hsig_sq : sigma 1 (s ^ 2) = s ^ 2 + s + 1 := sigma_one_sq_local hs_prime
      have hgt1 : 1 < sigma 1 (s ^ 2) := by rw [hsig_sq]; nlinarith only [hs_prime.two_le]
      have hnsq : ¬ IsSquare (sigma 1 (s ^ 2)) := by
        rw [hsig_sq]; rintro ⟨y, hy⟩
        have h1 : s ^ 2 < s ^ 2 + s + 1 := by omega
        have h2 : s ^ 2 + s + 1 < (s + 1) ^ 2 := by nlinarith only [hs_prime.two_le]
        exact Nat.not_exists_sq' h1 h2 ⟨y, by simpa [pow_two] using hy.symm⟩
      have hncube : ∀ y : ℕ, sigma 1 (s ^ 2) ≠ y ^ 3 := by
        rw [hsig_sq]; exact sq_add_self_add_one_ne_cube_of_two_mod_three hs_prime hs_mod3
      obtain ⟨h1, h2, _, h4, h5, _⟩ :=
        fourth_power_bounded_non_sq_non_cube_expCount hgt1 (hsq_le4 s hs_sq) hnsq hncube
      have h2pf := h5 (by omega)
      exact ⟨by omega, by omega, h4⟩
    refine ⟨?_, ?_, ?_⟩
    · calc 3 * (fineS3p N q).card = ∑ _s ∈ fineS3p N q, 3 := by simp [Finset.sum_const, Nat.mul_comm]
        _ ≤ ∑ s ∈ fineS3p N q, (expCount (sigma 1 (s ^ 2)) 1 + 2 * expCount (sigma 1 (s ^ 2)) 2 +
            3 * expCount (sigma 1 (s ^ 2)) 3 + 4 * expCount (sigma 1 (s ^ 2)) 4) :=
          Finset.sum_le_sum fun s hs => (hpt s hs).1
        _ = fineS3pe N q 1 + 2 * fineS3pe N q 2 + 3 * fineS3pe N q 3 + 4 * fineS3pe N q 4 := by
          simp only [fineS3pe, Finset.sum_add_distrib, Finset.mul_sum]
    · calc 2 * (fineS3p N q).card = ∑ _s ∈ fineS3p N q, 2 := by simp [Finset.sum_const, Nat.mul_comm]
        _ ≤ ∑ s ∈ fineS3p N q, (expCount (sigma 1 (s ^ 2)) 1 + expCount (sigma 1 (s ^ 2)) 2 +
            expCount (sigma 1 (s ^ 2)) 3 + expCount (sigma 1 (s ^ 2)) 4) :=
          Finset.sum_le_sum fun s hs => (hpt s hs).2.1
        _ = fineS3pe N q 1 + fineS3pe N q 2 + fineS3pe N q 3 + fineS3pe N q 4 := by
          simp only [fineS3pe, Finset.sum_add_distrib]
    · calc (fineS3p N q).card = ∑ _s ∈ fineS3p N q, 1 := by simp [Finset.sum_const]
        _ ≤ ∑ s ∈ fineS3p N q, (expCount (sigma 1 (s ^ 2)) 1 + expCount (sigma 1 (s ^ 2)) 2 +
            expCount (sigma 1 (s ^ 2)) 4) :=
          Finset.sum_le_sum fun s hs => (hpt s hs).2.2
        _ = fineS3pe N q 1 + fineS3pe N q 2 + fineS3pe N q 4 := by
          simp only [fineS3pe, Finset.sum_add_distrib]
  have hK_cop : ∀ w ∈ quarticChainSources N q,
      (quarticFirstFactor w).Coprime (quarticSecondFactor w) ∧
      quarticFirstFactor w ≠ 0 ∧ quarticSecondFactor w ≠ 0 ∧
      sigma 1 ((sigma 1 (w ^ 4)) ^ 2) = quarticFirstFactor w * quarticSecondFactor w := by
    intro w hw
    have hw_lg := (Finset.mem_filter.mp (hK_mem w hw).1).1
    have hw_prime := (hlg_prop w hw_lg).1
    have hs_sq := hK_int_sq (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
    have hs_prime := (hsq_prop (sigma 1 (w ^ 4)) hs_sq).1
    have hs_exp := (hsq_prop (sigma 1 (w ^ 4)) hs_sq).2.2.2.2
    have hprod_eq : sigma 1 ((sigma 1 (w ^ 4)) ^ 2) = quarticFirstFactor w * quarticSecondFactor w := by
      rw [sigma_one_sq_local hs_prime, sigma_one_four_local hw_prime]
      exact quartic_phi3_factor_product w
    have h31 : ¬ 31 ∣ quarticFirstFactor w * quarticSecondFactor w := by
      rw [← hprod_eq]; intro hd
      have h31_N : 31 ∣ N := by
        apply dvd_perfect_of_exact_prime_pow hN hs_prime (hs_exp ▸ Nat.ordProj_dvd N (sigma 1 (w ^ 4)))
          ((hs_prime.pow_dvd_iff_le_factorization hN.2.ne').not.mpr (by omega))
          (by decide : Nat.Prime 31) (by decide : Odd 31)
        rw [← sigma_one_apply]; exact hd
      have h31_mem : 31 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, h31_N, hN.2.ne'⟩
      have := sixth_power_free_min_prime_ge_53 ho hN hfree h31_mem; omega
    have hA0 : quarticFirstFactor w ≠ 0 := by unfold quarticFirstFactor; omega
    have hB0 : quarticSecondFactor w ≠ 0 := by unfold quarticSecondFactor; positivity
    exact ⟨quartic_factors_coprime h31, hA0, hB0, hprod_eq⟩
  have hA_le4 : ∀ w ∈ quarticChainSources N q, ∀ r ∈ (quarticFirstFactor w).primeFactors,
      (quarticFirstFactor w).factorization r ≤ 4 := by
    intro w hw r hr
    obtain ⟨_, hA0, hB0, hprod_eq⟩ := hK_cop w hw
    have hs_sq := hK_int_sq (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
    have hr_pf : r ∈ (sigma 1 ((sigma 1 (w ^ 4)) ^ 2)).primeFactors := by
      rw [hprod_eq, Nat.primeFactors_mul hA0 hB0]; exact Finset.mem_union_left _ hr
    have hle4 := hsq_le4 (sigma 1 (w ^ 4)) hs_sq r hr_pf
    rw [hprod_eq, Nat.factorization_mul hA0 hB0, Finsupp.add_apply] at hle4; omega
  have hB_le4 : ∀ w ∈ quarticChainSources N q, ∀ r ∈ (quarticSecondFactor w).primeFactors,
      (quarticSecondFactor w).factorization r ≤ 4 := by
    intro w hw r hr
    obtain ⟨_, hA0, hB0, hprod_eq⟩ := hK_cop w hw
    have hs_sq := hK_int_sq (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
    have hr_pf : r ∈ (sigma 1 ((sigma 1 (w ^ 4)) ^ 2)).primeFactors := by
      rw [hprod_eq, Nat.primeFactors_mul hA0 hB0]; exact Finset.mem_union_right _ hr
    have hle4 := hsq_le4 (sigma 1 (w ^ 4)) hs_sq r hr_pf
    rw [hprod_eq, Nat.factorization_mul hA0 hB0, Finsupp.add_apply] at hle4; omega
  have hA3p_inv :
      3 * (fineKA3p N q).card ≤
        fineA3pe N q 1 + 2 * fineA3pe N q 2 + 3 * fineA3pe N q 3 + 4 * fineA3pe N q 4 ∧
      2 * (fineKA3p N q).card ≤
        fineA3pe N q 1 + fineA3pe N q 2 + fineA3pe N q 3 + fineA3pe N q 4 ∧
      (fineKA3p N q).card ≤ fineA3pe N q 1 + fineA3pe N q 2 + fineA3pe N q 4 := by
    have hpt : ∀ w ∈ fineKA3p N q,
        let M := quarticFirstFactor w
        3 ≤ expCount M 1 + 2 * expCount M 2 + 3 * expCount M 3 + 4 * expCount M 4 ∧
        2 ≤ expCount M 1 + expCount M 2 + expCount M 3 + expCount M 4 ∧
        1 ≤ expCount M 1 + expCount M 2 + expCount M 4 := by
      intro w hw
      have hwK := (Finset.mem_filter.mp hw).1
      have hcf3 : 3 ≤ cardFactors (quarticFirstFactor w) := (Finset.mem_filter.mp hw).2
      have hw_lg := (Finset.mem_filter.mp (hK_mem w hwK).1).1
      obtain ⟨hw_prime, _, hw53, _, _⟩ := hlg_prop w hw_lg
      have hgt1 : 1 < quarticFirstFactor w := by
        unfold quarticFirstFactor
        have : w + 1 ≤ w ^ 2 := by nlinarith only [hw53]
        omega
      obtain ⟨_, h2, _, h4, h5, _⟩ := fourth_power_bounded_non_sq_non_cube_expCount hgt1
        (hA_le4 w hwK) (quarticFirstFactor_not_isSquare (by omega : 19 ≤ w))
        (quarticFirstFactor_ne_cube_of_prime_ne_nineteen hw_prime (by omega))
      have h2pf := h5 (by omega)
      exact ⟨by omega, by omega, h4⟩
    refine ⟨?_, ?_, ?_⟩
    · calc 3 * (fineKA3p N q).card = ∑ _w ∈ fineKA3p N q, 3 := by simp [Finset.sum_const, Nat.mul_comm]
        _ ≤ ∑ w ∈ fineKA3p N q, (expCount (quarticFirstFactor w) 1 +
            2 * expCount (quarticFirstFactor w) 2 + 3 * expCount (quarticFirstFactor w) 3 +
            4 * expCount (quarticFirstFactor w) 4) := Finset.sum_le_sum fun w hw => (hpt w hw).1
        _ = fineA3pe N q 1 + 2 * fineA3pe N q 2 + 3 * fineA3pe N q 3 + 4 * fineA3pe N q 4 := by
          simp only [fineA3pe, Finset.sum_add_distrib, Finset.mul_sum]
    · calc 2 * (fineKA3p N q).card = ∑ _w ∈ fineKA3p N q, 2 := by simp [Finset.sum_const, Nat.mul_comm]
        _ ≤ ∑ w ∈ fineKA3p N q, (expCount (quarticFirstFactor w) 1 +
            expCount (quarticFirstFactor w) 2 + expCount (quarticFirstFactor w) 3 +
            expCount (quarticFirstFactor w) 4) := Finset.sum_le_sum fun w hw => (hpt w hw).2.1
        _ = fineA3pe N q 1 + fineA3pe N q 2 + fineA3pe N q 3 + fineA3pe N q 4 := by
          simp only [fineA3pe, Finset.sum_add_distrib]
    · calc (fineKA3p N q).card = ∑ _w ∈ fineKA3p N q, 1 := by simp [Finset.sum_const]
        _ ≤ ∑ w ∈ fineKA3p N q, (expCount (quarticFirstFactor w) 1 +
            expCount (quarticFirstFactor w) 2 + expCount (quarticFirstFactor w) 4) :=
          Finset.sum_le_sum fun w hw => (hpt w hw).2.2
        _ = fineA3pe N q 1 + fineA3pe N q 2 + fineA3pe N q 4 := by
          simp only [fineA3pe, Finset.sum_add_distrib]
  have hB26_inv :
      2 * (fineKB26 N q).card ≤
        fineB26e N q 1 + 2 * fineB26e N q 2 + 3 * fineB26e N q 3 + 4 * fineB26e N q 4 ∧
      2 * (fineKB26 N q).card ≤
        fineB26e N q 1 + fineB26e N q 2 + fineB26e N q 3 + fineB26e N q 4 ∧
      (fineKB26 N q).card ≤ fineB26e N q 1 + fineB26e N q 2 + fineB26e N q 4 := by
    have hpt : ∀ w ∈ fineKB26 N q,
        let M := quarticSecondFactor w
        2 ≤ expCount M 1 + 2 * expCount M 2 + 3 * expCount M 3 + 4 * expCount M 4 ∧
        2 ≤ expCount M 1 + expCount M 2 + expCount M 3 + expCount M 4 ∧
        1 ≤ expCount M 1 + expCount M 2 + expCount M 4 := by
      intro w hw
      have hwK := (Finset.mem_filter.mp hw).1
      obtain ⟨hcf2, _⟩ := (Finset.mem_filter.mp hw).2
      have hw_lg := (Finset.mem_filter.mp (hK_mem w hwK).1).1
      have hw53 := (hlg_prop w hw_lg).2.2.1
      have hgt1 : 1 < quarticSecondFactor w := by unfold quarticSecondFactor; omega
      obtain ⟨_, h2, _, h4, h5, _⟩ := fourth_power_bounded_non_sq_non_cube_expCount hgt1
        (hB_le4 w hwK) (quarticSecondFactor_not_isSquare (by omega : 19 ≤ w))
        (quarticSecondFactor_not_isCube (by omega : 2 ≤ w))
      have h2pf := h5 hcf2
      exact ⟨by omega, by omega, h4⟩
    refine ⟨?_, ?_, ?_⟩
    · calc 2 * (fineKB26 N q).card = ∑ _w ∈ fineKB26 N q, 2 := by simp [Finset.sum_const, Nat.mul_comm]
        _ ≤ ∑ w ∈ fineKB26 N q, (expCount (quarticSecondFactor w) 1 +
            2 * expCount (quarticSecondFactor w) 2 + 3 * expCount (quarticSecondFactor w) 3 +
            4 * expCount (quarticSecondFactor w) 4) := Finset.sum_le_sum fun w hw => (hpt w hw).1
        _ = fineB26e N q 1 + 2 * fineB26e N q 2 + 3 * fineB26e N q 3 + 4 * fineB26e N q 4 := by
          simp only [fineB26e, Finset.sum_add_distrib, Finset.mul_sum]
    · calc 2 * (fineKB26 N q).card = ∑ _w ∈ fineKB26 N q, 2 := by simp [Finset.sum_const, Nat.mul_comm]
        _ ≤ ∑ w ∈ fineKB26 N q, (expCount (quarticSecondFactor w) 1 +
            expCount (quarticSecondFactor w) 2 + expCount (quarticSecondFactor w) 3 +
            expCount (quarticSecondFactor w) 4) := Finset.sum_le_sum fun w hw => (hpt w hw).2.1
        _ = fineB26e N q 1 + fineB26e N q 2 + fineB26e N q 3 + fineB26e N q 4 := by
          simp only [fineB26e, Finset.sum_add_distrib]
    · calc (fineKB26 N q).card = ∑ _w ∈ fineKB26 N q, 1 := by simp [Finset.sum_const]
        _ ≤ ∑ w ∈ fineKB26 N q, (expCount (quarticSecondFactor w) 1 +
            expCount (quarticSecondFactor w) 2 + expCount (quarticSecondFactor w) 4) :=
          Finset.sum_le_sum fun w hw => (hpt w hw).2.2
        _ = fineB26e N q 1 + fineB26e N q 2 + fineB26e N q 4 := by
          simp only [fineB26e, Finset.sum_add_distrib]
  have hB7p_inv :
      7 * (fineKB7p N q).card ≤
        fineB7pe N q 1 + 2 * fineB7pe N q 2 + 3 * fineB7pe N q 3 + 4 * fineB7pe N q 4 ∧
      (fineKB7p N q).card ≤ fineB7pe N q 1 + fineB7pe N q 2 + fineB7pe N q 4 := by
    have hpt : ∀ w ∈ fineKB7p N q,
        let M := quarticSecondFactor w
        7 ≤ expCount M 1 + 2 * expCount M 2 + 3 * expCount M 3 + 4 * expCount M 4 ∧
        1 ≤ expCount M 1 + expCount M 2 + expCount M 4 := by
      intro w hw
      have hwK := (Finset.mem_filter.mp hw).1
      have hcf7 := (Finset.mem_filter.mp hw).2
      have hw_lg := (Finset.mem_filter.mp (hK_mem w hwK).1).1
      have hw53 := (hlg_prop w hw_lg).2.2.1
      have hgt1 : 1 < quarticSecondFactor w := by unfold quarticSecondFactor; omega
      obtain ⟨_, h2, _, h4, _, _⟩ := fourth_power_bounded_non_sq_non_cube_expCount hgt1
        (hB_le4 w hwK) (quarticSecondFactor_not_isSquare (by omega : 19 ≤ w))
        (quarticSecondFactor_not_isCube (by omega : 2 ≤ w))
      exact ⟨by omega, h4⟩
    refine ⟨?_, ?_⟩
    · calc 7 * (fineKB7p N q).card = ∑ _w ∈ fineKB7p N q, 7 := by simp [Finset.sum_const, Nat.mul_comm]
        _ ≤ ∑ w ∈ fineKB7p N q, (expCount (quarticSecondFactor w) 1 +
            2 * expCount (quarticSecondFactor w) 2 + 3 * expCount (quarticSecondFactor w) 3 +
            4 * expCount (quarticSecondFactor w) 4) := Finset.sum_le_sum fun w hw => (hpt w hw).1
        _ = fineB7pe N q 1 + 2 * fineB7pe N q 2 + 3 * fineB7pe N q 3 + 4 * fineB7pe N q 4 := by
          simp only [fineB7pe, Finset.sum_add_distrib, Finset.mul_sum]
    · calc (fineKB7p N q).card = ∑ _w ∈ fineKB7p N q, 1 := by simp [Finset.sum_const]
        _ ≤ ∑ w ∈ fineKB7p N q, (expCount (quarticSecondFactor w) 1 +
            expCount (quarticSecondFactor w) 2 + expCount (quarticSecondFactor w) 4) :=
          Finset.sum_le_sum fun w hw => (hpt w hw).2
        _ = fineB7pe N q 1 + fineB7pe N q 2 + fineB7pe N q 4 := by
          simp only [fineB7pe, Finset.sum_add_distrib]
  have hsum_sq_expCount : ∀ j, 1 ≤ j →
      (∑ s ∈ squareSources N, expCount (sigma 1 (s ^ 2)) j) =
        (if j = 1 then (fineSp N q).card else 0) +
        (if j = 1 then 2 * (fineS2 N q).card else 0) + fineS3pe N q j +
        (if j = 1 then (fineKA1 N q).card else 0) + (if j = 1 then 2 * (fineKA2 N q).card else 0) +
        fineA3pe N q j +
        (if j = 1 then (fineKB1 N q).card else 0) + fineB26e N q j + fineB7pe N q j := by
    intro j hj
    have hS_split : squareSources N = fineSnc N q ∪ quarticChainIntermediates N q :=
      (Finset.sdiff_union_of_subset hK_int_sq).symm
    have hS_disj2 : Disjoint (fineSnc N q) (quarticChainIntermediates N q) := Finset.sdiff_disjoint
    rw [hS_split, Finset.sum_union hS_disj2, hSnc_parts, Finset.sum_union hS_p2_3p_disj,
      Finset.sum_union hS_p_2_disj]
    have hs_p : ∑ s ∈ fineSp N q, expCount (sigma 1 (s ^ 2)) j =
        if j = 1 then (fineSp N q).card else 0 := by
      split_ifs with hj1
      · subst hj1
        calc ∑ s ∈ fineSp N q, expCount (sigma 1 (s ^ 2)) 1 = ∑ _s ∈ fineSp N q, 1 := by
              refine Finset.sum_congr rfl fun s hs => ?_
              have hp := cardFactors_eq_one_iff_prime.mp (Finset.mem_filter.mp hs).2
              simpa using expCount_of_prime (j := 1) hp
          _ = (fineSp N q).card := by simp [Finset.sum_const]
      · refine Finset.sum_eq_zero fun s hs => ?_
        have hp := cardFactors_eq_one_iff_prime.mp (Finset.mem_filter.mp hs).2
        simp [expCount_of_prime hp, hj1]
    have hs_2 : ∑ s ∈ fineS2 N q, expCount (sigma 1 (s ^ 2)) j =
        if j = 1 then 2 * (fineS2 N q).card else 0 := by
      have hpt : ∀ s ∈ fineS2 N q, expCount (sigma 1 (s ^ 2)) 1 = 2 ∧
          expCount (sigma 1 (s ^ 2)) 2 = 0 ∧ expCount (sigma 1 (s ^ 2)) 3 = 0 ∧
          expCount (sigma 1 (s ^ 2)) 4 = 0 := by
        intro s hs
        have hs_sq := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hs).1).1
        have hs_prime := (hsq_prop s hs_sq).1
        have hgt1 : 1 < sigma 1 (s ^ 2) := by
          rw [sigma_one_sq_local hs_prime]; nlinarith only [hs_prime.two_le]
        have hnsq : ¬ IsSquare (sigma 1 (s ^ 2)) := by
          rw [sigma_one_sq_local hs_prime]; rintro ⟨y, hy⟩
          have hlo : s ^ 2 < s ^ 2 + s + 1 := by omega
          have hhi : s ^ 2 + s + 1 < (s + 1) ^ 2 := by nlinarith only [hs_prime.two_le]
          exact Nat.not_exists_sq' hlo hhi ⟨y, by simpa [pow_two] using hy.symm⟩
        exact expCount_of_cardFactors_two_nonsquare hgt1 (Finset.mem_filter.mp hs).2 hnsq
      by_cases hj1 : j = 1
      · subst hj1; simp only [ite_true]
        calc ∑ s ∈ fineS2 N q, expCount (sigma 1 (s ^ 2)) 1 = ∑ _s ∈ fineS2 N q, 2 :=
              Finset.sum_congr rfl fun s hs => (hpt s hs).1
          _ = 2 * (fineS2 N q).card := by simp [Finset.sum_const, Nat.mul_comm]
      · simp only [hj1, ite_false]
        refine Finset.sum_eq_zero fun s hs => ?_
        rcases (show j = 2 ∨ j = 3 ∨ j = 4 ∨ 5 ≤ j by omega) with rfl | rfl | rfl | hj5
        · exact (hpt s hs).2.1
        · exact (hpt s hs).2.2.1
        · exact (hpt s hs).2.2.2
        · unfold expCount
          have hs_sq := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hs).1).1
          have h0 : (sigma 1 (s ^ 2)).primeFactors.filter
              (fun r => (sigma 1 (s ^ 2)).factorization r = j) = ∅ := by
            ext r; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
            intro hr; have := hsq_le4 s hs_sq r hr; omega
          rw [h0, Finset.card_empty]
    have hK_sum :
        ∑ s ∈ quarticChainIntermediates N q, expCount (sigma 1 (s ^ 2)) j =
          ∑ w ∈ quarticChainSources N q, expCount (quarticFirstFactor w) j +
          ∑ w ∈ quarticChainSources N q, expCount (quarticSecondFactor w) j := by
      have hinj : Set.InjOn (fun w => sigma 1 (w ^ 4)) (quarticChainSources N q : Set ℕ) := by
        intro w₁ hw₁ w₂ hw₂ heq
        have hw₁_p := (hlg_prop w₁ (Finset.mem_filter.mp (hK_mem w₁ hw₁).1).1).1
        have hw₂_p := (hlg_prop w₂ (Finset.mem_filter.mp (hK_mem w₂ hw₂).1).1).1
        dsimp only at heq
        rw [sigma_one_four_local hw₁_p, sigma_one_four_local hw₂_p] at heq
        rcases lt_trichotomy w₁ w₂ with hlt | rfl | hgt
        · have : w₁ ^ 2 < w₂ ^ 2 := Nat.pow_lt_pow_left hlt (by decide)
          have : w₁ ^ 3 < w₂ ^ 3 := Nat.pow_lt_pow_left hlt (by decide)
          have : w₁ ^ 4 < w₂ ^ 4 := Nat.pow_lt_pow_left hlt (by decide)
          omega
        · rfl
        · have : w₂ ^ 2 < w₁ ^ 2 := Nat.pow_lt_pow_left hgt (by decide)
          have : w₂ ^ 3 < w₁ ^ 3 := Nat.pow_lt_pow_left hgt (by decide)
          have : w₂ ^ 4 < w₁ ^ 4 := Nat.pow_lt_pow_left hgt (by decide)
          omega
      change ∑ s ∈ (quarticChainSources N q).image (fun w => sigma 1 (w ^ 4)),
        expCount (sigma 1 (s ^ 2)) j = _
      rw [Finset.sum_image hinj, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun w hw => ?_
      obtain ⟨hcop, hA0, hB0, hprod_eq⟩ := hK_cop w hw
      rw [hprod_eq, expCount_mul_of_coprime hA0 hB0 hcop hj]
    have hA_sum :
        ∑ w ∈ quarticChainSources N q, expCount (quarticFirstFactor w) j =
          (if j = 1 then (fineKA1 N q).card else 0) +
          (if j = 1 then 2 * (fineKA2 N q).card else 0) + fineA3pe N q j := by
      conv_lhs => rw [hkA_parts, Finset.sum_union hdisj_A12_3p, Finset.sum_union hdisj_A12]
      have ha1 : ∑ w ∈ fineKA1 N q, expCount (quarticFirstFactor w) j =
          if j = 1 then (fineKA1 N q).card else 0 := by
        split_ifs with hj1
        · subst hj1
          calc ∑ w ∈ fineKA1 N q, expCount (quarticFirstFactor w) 1 = ∑ _w ∈ fineKA1 N q, 1 := by
                refine Finset.sum_congr rfl fun w hw => ?_
                have hp := cardFactors_eq_one_iff_prime.mp (Finset.mem_filter.mp hw).2
                simpa using expCount_of_prime (j := 1) hp
            _ = (fineKA1 N q).card := by simp [Finset.sum_const]
        · refine Finset.sum_eq_zero fun w hw => ?_
          have hp := cardFactors_eq_one_iff_prime.mp (Finset.mem_filter.mp hw).2
          simp [expCount_of_prime hp, hj1]
      have ha2 : ∑ w ∈ fineKA2 N q, expCount (quarticFirstFactor w) j =
          if j = 1 then 2 * (fineKA2 N q).card else 0 := by
        have hpt : ∀ w ∈ fineKA2 N q, expCount (quarticFirstFactor w) 1 = 2 ∧
            expCount (quarticFirstFactor w) 2 = 0 ∧ expCount (quarticFirstFactor w) 3 = 0 ∧
            expCount (quarticFirstFactor w) 4 = 0 := by
          intro w hw
          have hwK := (Finset.mem_filter.mp hw).1
          have hw_lg := (Finset.mem_filter.mp (hK_mem w hwK).1).1
          have hw53 := (hlg_prop w hw_lg).2.2.1
          have hgt1 : 1 < quarticFirstFactor w := by
            unfold quarticFirstFactor
            have : w + 1 ≤ w ^ 2 := by nlinarith only [hw53]
            omega
          exact expCount_of_cardFactors_two_nonsquare hgt1 (Finset.mem_filter.mp hw).2
            (quarticFirstFactor_not_isSquare (by omega : 19 ≤ w))
        by_cases hj1 : j = 1
        · subst hj1; simp only [ite_true]
          calc ∑ w ∈ fineKA2 N q, expCount (quarticFirstFactor w) 1 = ∑ _w ∈ fineKA2 N q, 2 :=
                Finset.sum_congr rfl fun w hw => (hpt w hw).1
            _ = 2 * (fineKA2 N q).card := by simp [Finset.sum_const, Nat.mul_comm]
        · simp only [hj1, ite_false]
          refine Finset.sum_eq_zero fun w hw => ?_
          have hwK := (Finset.mem_filter.mp hw).1
          rcases (show j = 2 ∨ j = 3 ∨ j = 4 ∨ 5 ≤ j by omega) with rfl | rfl | rfl | hj5
          · exact (hpt w hw).2.1
          · exact (hpt w hw).2.2.1
          · exact (hpt w hw).2.2.2
          · unfold expCount
            have h0 : (quarticFirstFactor w).primeFactors.filter
                (fun r => (quarticFirstFactor w).factorization r = j) = ∅ := by
              ext r; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
              intro hr; have := hA_le4 w hwK r hr; omega
            rw [h0, Finset.card_empty]
      rw [ha1, ha2]; rfl
    have hB_sum :
        ∑ w ∈ quarticChainSources N q, expCount (quarticSecondFactor w) j =
          (if j = 1 then (fineKB1 N q).card else 0) + fineB26e N q j + fineB7pe N q j := by
      conv_lhs => rw [hkB_parts, Finset.sum_union hdisj_B126_7p, Finset.sum_union hdisj_B1_26]
      have hb1 : ∑ w ∈ fineKB1 N q, expCount (quarticSecondFactor w) j =
          if j = 1 then (fineKB1 N q).card else 0 := by
        split_ifs with hj1
        · subst hj1
          calc ∑ w ∈ fineKB1 N q, expCount (quarticSecondFactor w) 1 = ∑ _w ∈ fineKB1 N q, 1 := by
                refine Finset.sum_congr rfl fun w hw => ?_
                have hp := cardFactors_eq_one_iff_prime.mp (Finset.mem_filter.mp hw).2
                simpa using expCount_of_prime (j := 1) hp
            _ = (fineKB1 N q).card := by simp [Finset.sum_const]
        · refine Finset.sum_eq_zero fun w hw => ?_
          have hp := cardFactors_eq_one_iff_prime.mp (Finset.mem_filter.mp hw).2
          simp [expCount_of_prime hp, hj1]
      rw [hb1]; rfl
    rw [hs_p, hs_2, hK_sum, hA_sum, hB_sum]
    change _ + _ + fineS3pe N q j + _ = _
    ring
  have hfac_q_le1 : ∀ p ∈ N.primeFactors, (sigma 1 (p ^ N.factorization p)).factorization q ≤ 1 := by
    intro p hp
    have hsum := factorization_eq_sum_sigma_factorizations hN hq_odd hq_prime
    have hle := Finset.single_le_sum
      (f := fun x => (sigma 1 (x ^ N.factorization x)).factorization q)
      (fun _ _ => Nat.zero_le _) hp
    omega
  have hsum_sq_tgt : ∀ j, 1 ≤ j → j ≤ 4 →
      fineHQe N q j + ∑ s ∈ squareSources N, expCount (sigma 1 (s ^ 2)) j =
        (if j = 1 then (fineSqQ N q).card else 0) +
        ∑ r ∈ oneModThreeLargeSources N q,
          (N.primeFactors.filter (fun p => (oddComponentSigma N q p).factorization r = j)).card := by
    intro j hj _
    have hq_notin_Q13 : q ∉ oneModThreeLargeSources N q := fun h =>
      hq_notin (Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mp h).1))
    have hlhs_sq :
        ∑ s ∈ squareSources N, expCount (sigma 1 (s ^ 2)) j =
          (∑ s ∈ squareSources N, if (sigma 1 (s ^ 2)).factorization q = j then 1 else 0) +
          ∑ r ∈ oneModThreeLargeSources N q, ∑ s ∈ squareSources N,
            if (sigma 1 (s ^ 2)).factorization r = j then 1 else 0 := by
      have hpt : ∀ s ∈ squareSources N,
          expCount (sigma 1 (s ^ 2)) j =
            (if (sigma 1 (s ^ 2)).factorization q = j then 1 else 0) +
            ∑ r ∈ oneModThreeLargeSources N q,
              if (sigma 1 (s ^ 2)).factorization r = j then 1 else 0 := by
        intro s hs
        have hs_prime := (hsq_prop s hs).1
        have hs_ne0 : sigma 1 (s ^ 2) ≠ 0 := by rw [sigma_one_sq_local hs_prime]; positivity
        rw [expCount_eq_sum_indicator_of_subset hs_ne0 hj
          (sq_sigma_primeFactors_subset ho hN hq hq4 he hev hfree hs),
          Finset.sum_insert hq_notin_Q13]
      calc ∑ s ∈ squareSources N, expCount (sigma 1 (s ^ 2)) j
          = ∑ s ∈ squareSources N,
              ((if (sigma 1 (s ^ 2)).factorization q = j then 1 else 0) +
                ∑ r ∈ oneModThreeLargeSources N q,
                  if (sigma 1 (s ^ 2)).factorization r = j then 1 else 0) :=
            Finset.sum_congr rfl hpt
        _ = (∑ s ∈ squareSources N, if (sigma 1 (s ^ 2)).factorization q = j then 1 else 0) +
              ∑ s ∈ squareSources N, ∑ r ∈ oneModThreeLargeSources N q,
                if (sigma 1 (s ^ 2)).factorization r = j then 1 else 0 := Finset.sum_add_distrib
        _ = _ := by rw [Finset.sum_comm]
    have hq_part :
        (∑ s ∈ squareSources N, if (sigma 1 (s ^ 2)).factorization q = j then 1 else 0) =
          if j = 1 then (fineSqQ N q).card else 0 := by
      split_ifs with hj1
      · subst hj1
        have hfilt : (squareSources N).filter (fun s => (sigma 1 (s ^ 2)).factorization q = 1) =
            fineSqQ N q := by
          ext s; simp only [fineSqQ, Finset.mem_filter]; constructor
          · rintro ⟨hs, h1⟩
            have hs_prime := (hsq_prop s hs).1
            have hs_ne0 : sigma 1 (s ^ 2) ≠ 0 := by rw [sigma_one_sq_local hs_prime]; positivity
            exact ⟨hs, (hq_prime.dvd_iff_one_le_factorization hs_ne0).mpr (by omega)⟩
          · rintro ⟨hs, hdvd⟩
            have hs_mem := (Finset.mem_filter.mp hs).1
            have hs_prime := (hsq_prop s hs).1
            have hs_exp := (hsq_prop s hs).2.2.2.2
            have hs_ne0 : sigma 1 (s ^ 2) ≠ 0 := by rw [sigma_one_sq_local hs_prime]; positivity
            have hge1 : 1 ≤ (sigma 1 (s ^ 2)).factorization q :=
              (hq_prime.dvd_iff_one_le_factorization hs_ne0).mp hdvd
            have hle1 := hfac_q_le1 s hs_mem
            rw [hs_exp] at hle1; exact ⟨hs, by omega⟩
        rw [← hfilt, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      · refine Finset.sum_eq_zero fun s hs => ?_
        have hs_mem := (Finset.mem_filter.mp hs).1
        have hs_exp := (hsq_prop s hs).2.2.2.2
        have hle1 := hfac_q_le1 s hs_mem
        rw [hs_exp] at hle1
        simp only [ite_eq_right_iff]; intro heq; omega
    have hr_part : ∀ r ∈ oneModThreeLargeSources N q,
        (if ((q + 1) / 2).factorization r = j then 1 else 0) +
          (∑ s ∈ squareSources N, if (sigma 1 (s ^ 2)).factorization r = j then 1 else 0) =
          (N.primeFactors.filter (fun p => (oddComponentSigma N q p).factorization r = j)).card := by
      intro r hr
      have hr_lg := (Finset.mem_filter.mp hr).1
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one, hparts, Finset.filter_insert]
      have hq_comp : oddComponentSigma N q q = (q + 1) / 2 := by
        unfold oddComponentSigma; simp only [ite_true]
        rw [hq1, pow_one, sigma_one_prime_local hq_prime]
      have hlg_none :
          (largeSources N q).filter (fun p => (oddComponentSigma N q p).factorization r = j) = ∅ := by
        ext p; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hp hpj
        have hp_neq := (hlg_prop p hp).2.2.2.1
        have hp_exp := (hlg_prop p hp).2.2.2.2
        have hcomp : oddComponentSigma N q p = sigma 1 (p ^ 4) := by
          unfold oddComponentSigma; simp [hp_neq, hp_exp]
        have hndvd := sixth_power_free_quartic_mutual_exclusion ho hN hq hq4 he hev hfree r hr_lg p hp
        have hz : (oddComponentSigma N q p).factorization r = 0 := by
          rw [hcomp]; exact Nat.factorization_eq_zero_of_not_dvd hndvd
        omega
      have hsq_eq :
          (squareSources N).filter (fun p => (oddComponentSigma N q p).factorization r = j) =
            (squareSources N).filter (fun s => (sigma 1 (s ^ 2)).factorization r = j) := by
        refine Finset.filter_congr fun s hs => ?_
        have hs_neq := (hsq_prop s hs).2.2.2.1
        have hs_exp := (hsq_prop s hs).2.2.2.2
        have hcomp : oddComponentSigma N q s = sigma 1 (s ^ 2) := by
          unfold oddComponentSigma; simp [hs_neq, hs_exp]
        rw [hcomp]
      have hfilt_u :
          (squareSources N ∪ largeSources N q).filter
              (fun p => (oddComponentSigma N q p).factorization r = j) =
            (squareSources N).filter (fun s => (sigma 1 (s ^ 2)).factorization r = j) := by
        rw [Finset.filter_union, hlg_none, Finset.union_empty, hsq_eq]
      rw [hfilt_u, hq_comp]
      split_ifs with hq_cond
      · rw [Finset.card_insert_of_notMem]
        · ring
        · intro hmem
          exact hq_notin (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mp hmem).1))
      · ring
    have hHQ_eq : fineHQe N q j =
        ∑ r ∈ oneModThreeLargeSources N q, if ((q + 1) / 2).factorization r = j then 1 else 0 := by
      unfold fineHQe
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    rw [hlhs_sq, hq_part, hHQ_eq]
    have hcomb :
        (∑ r ∈ oneModThreeLargeSources N q, if ((q + 1) / 2).factorization r = j then 1 else 0) +
          ((if j = 1 then (fineSqQ N q).card else 0) +
            ∑ r ∈ oneModThreeLargeSources N q, ∑ s ∈ squareSources N,
              if (sigma 1 (s ^ 2)).factorization r = j then 1 else 0) =
          (if j = 1 then (fineSqQ N q).card else 0) +
            ∑ r ∈ oneModThreeLargeSources N q,
              ((if ((q + 1) / 2).factorization r = j then 1 else 0) +
                ∑ s ∈ squareSources N, if (sigma 1 (s ^ 2)).factorization r = j then 1 else 0) := by
      rw [add_left_comm, ← Finset.sum_add_distrib]
    rw [hcomb]
    congr 1
    exact Finset.sum_congr rfl hr_part
  have hsum_inExp : ∀ j : ℕ, 1 ≤ j → j ≤ 4 →
      (∑ r ∈ oneModThreeLargeSources N q,
        (N.primeFactors.filter (fun p => (oddComponentSigma N q p).factorization r = j)).card) =
        (if j = 4 then (fineT4 N q).card else 0) +
        (if j = 1 ∨ j = 3 then (fineT31 N q).card else 0) +
        (if j = 2 then 2 * (fineT22 N q).card else 0) +
        (if j = 1 then 2 * (fineT211 N q).card else if j = 2 then (fineT211 N q).card else 0) +
        (if j = 1 then 4 * (fineT1111 N q).card else 0) := by
    intro j hj1 hj4
    conv_lhs => rw [hT_parts]
    rw [Finset.sum_union hT_disj4, Finset.sum_union hT_disj3,
      Finset.sum_union hT_disj2, Finset.sum_union hT_disj1]
    have s4 : ∑ r ∈ fineT4 N q,
        (N.primeFactors.filter (fun p => (oddComponentSigma N q p).factorization r = j)).card =
        if j = 4 then (fineT4 N q).card else 0 := by
      have hpt : ∀ r ∈ fineT4 N q,
          (N.primeFactors.filter (fun p => (oddComponentSigma N q p).factorization r = j)).card =
            if j = 4 then 1 else 0 := by
        intro r hr
        obtain ⟨hr_Q13, hr1⟩ := Finset.mem_filter.mp hr
        obtain ⟨h1, h2, h3c, h4⟩ := (per_target_inExpCount ho hN hq hq4 he hev hfree hr_Q13).1 hr1
        rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl
        · simpa using h1
        · simpa using h2
        · simpa using h3c
        · simpa using h4
      rw [Finset.sum_congr rfl hpt]; simp [Finset.sum_const]
    have s31 : ∑ r ∈ fineT31 N q,
        (N.primeFactors.filter (fun p => (oddComponentSigma N q p).factorization r = j)).card =
        if j = 1 ∨ j = 3 then (fineT31 N q).card else 0 := by
      have hpt : ∀ r ∈ fineT31 N q,
          (N.primeFactors.filter (fun p => (oddComponentSigma N q p).factorization r = j)).card =
            if j = 1 ∨ j = 3 then 1 else 0 := by
        intro r hr
        obtain ⟨hr_Q13, hr2, hro⟩ := Finset.mem_filter.mp hr
        obtain ⟨h1, h2, h3c, h4⟩ :=
          (per_target_inExpCount ho hN hq hq4 he hev hfree hr_Q13).2.1 ⟨hr2, hro⟩
        rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl
        · simpa using h1
        · simpa using h2
        · simpa using h3c
        · simpa using h4
      rw [Finset.sum_congr rfl hpt]; simp [Finset.sum_const]
    have s22 : ∑ r ∈ fineT22 N q,
        (N.primeFactors.filter (fun p => (oddComponentSigma N q p).factorization r = j)).card =
        if j = 2 then 2 * (fineT22 N q).card else 0 := by
      have hpt : ∀ r ∈ fineT22 N q,
          (N.primeFactors.filter (fun p => (oddComponentSigma N q p).factorization r = j)).card =
            if j = 2 then 2 else 0 := by
        intro r hr
        obtain ⟨hr_Q13, hr2, hrno⟩ := Finset.mem_filter.mp hr
        obtain ⟨h1, h2, h3c, h4⟩ :=
          (per_target_inExpCount ho hN hq hq4 he hev hfree hr_Q13).2.2.1 ⟨hr2, hrno⟩
        rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl
        · simpa using h1
        · simpa using h2
        · simpa using h3c
        · simpa using h4
      rw [Finset.sum_congr rfl hpt]; simp [Finset.sum_const, Nat.mul_comm]
    have s211 : ∑ r ∈ fineT211 N q,
        (N.primeFactors.filter (fun p => (oddComponentSigma N q p).factorization r = j)).card =
        if j = 1 then 2 * (fineT211 N q).card else if j = 2 then (fineT211 N q).card else 0 := by
      have hpt : ∀ r ∈ fineT211 N q,
          (N.primeFactors.filter (fun p => (oddComponentSigma N q p).factorization r = j)).card =
            if j = 1 then 2 else if j = 2 then 1 else 0 := by
        intro r hr
        obtain ⟨hr_Q13, hr3⟩ := Finset.mem_filter.mp hr
        obtain ⟨h1, h2, h3c, h4⟩ := (per_target_inExpCount ho hN hq hq4 he hev hfree hr_Q13).2.2.2.1 hr3
        rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl
        · simpa using h1
        · simpa using h2
        · simpa using h3c
        · simpa using h4
      rw [Finset.sum_congr rfl hpt]
      split_ifs <;> simp [Finset.sum_const, Nat.mul_comm]
    have s1111 : ∑ r ∈ fineT1111 N q,
        (N.primeFactors.filter (fun p => (oddComponentSigma N q p).factorization r = j)).card =
        if j = 1 then 4 * (fineT1111 N q).card else 0 := by
      have hpt : ∀ r ∈ fineT1111 N q,
          (N.primeFactors.filter (fun p => (oddComponentSigma N q p).factorization r = j)).card =
            if j = 1 then 4 else 0 := by
        intro r hr
        obtain ⟨hr_Q13, hr4⟩ := Finset.mem_filter.mp hr
        obtain ⟨h1, h2, h3c, h4⟩ := (per_target_inExpCount ho hN hq hq4 he hev hfree hr_Q13).2.2.2.2 hr4
        rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl
        · simpa using h1
        · simpa using h2
        · simpa using h3c
        · simpa using h4
      rw [Finset.sum_congr rfl hpt]; simp [Finset.sum_const, Nat.mul_comm]
    rw [s4, s31, s22, s211, s1111]
  have hE4_e1 : fineHQe N q 1 + (fineSp N q).card + 2 * (fineS2 N q).card + fineS3pe N q 1 +
      (fineKA1 N q).card + 2 * (fineKA2 N q).card + fineA3pe N q 1 + (fineKB1 N q).card +
      fineB26e N q 1 + fineB7pe N q 1 =
      (fineSqQ N q).card + (fineT31 N q).card + 2 * (fineT211 N q).card + 4 * (fineT1111 N q).card := by
    have h1 := hsum_sq_tgt 1 (by decide) (by decide)
    rw [hsum_sq_expCount 1 (by decide), hsum_inExp 1 (by decide) (by decide)] at h1
    simp only [ite_true, true_or, Nat.reduceEqDiff, ite_false] at h1
    linarith only [h1]
  have hE4_e2 : fineHQe N q 2 + fineS3pe N q 2 + fineA3pe N q 2 + fineB26e N q 2 + fineB7pe N q 2 =
      2 * (fineT22 N q).card + (fineT211 N q).card := by
    have h2 := hsum_sq_tgt 2 (by decide) (by decide)
    rw [hsum_sq_expCount 2 (by decide), hsum_inExp 2 (by decide) (by decide)] at h2
    simp only [Nat.reduceEqDiff, ite_false, ite_true, or_self] at h2
    linarith only [h2]
  have hE4_e3 : fineHQe N q 3 + fineS3pe N q 3 + fineA3pe N q 3 + fineB26e N q 3 + fineB7pe N q 3 =
      (fineT31 N q).card := by
    have h3c := hsum_sq_tgt 3 (by decide) (by decide)
    rw [hsum_sq_expCount 3 (by decide), hsum_inExp 3 (by decide) (by decide)] at h3c
    simp only [Nat.reduceEqDiff, ite_false, or_true, ite_true] at h3c
    linarith only [h3c]
  have hE4_e4 : fineHQe N q 4 + fineS3pe N q 4 + fineA3pe N q 4 + fineB26e N q 4 + fineB7pe N q 4 =
      (fineT4 N q).card := by
    have h4 := hsum_sq_tgt 4 (by decide) (by decide)
    rw [hsum_sq_expCount 4 (by decide), hsum_inExp 4 (by decide) (by decide)] at h4
    simp only [Nat.reduceEqDiff, ite_false, or_self, ite_true] at h4
    linarith only [h4]
  exact ⟨hE3_Snc, hE3_chA, hE3_chB, hE3_tgt, hEQ13_eq, hE4_e1, hE4_e2, hE4_e3, hE4_e4,
    hS3p_inv, hA3p_inv, hB26_inv, hB7p_inv⟩

private theorem fine_upward_reuse_bounds {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    (fineSp N q).card + (fineS2 N q).card + (fineKB1 N q).card + (fineKA1 N q).card ≤
      (fineSqQ N q).card + (fineT31 N q).card + (fineT211 N q).card + (fineT1111 N q).card ∧
    (fineKA1 N q).card + (fineKA2 N q).card + 2 * (fineSp N q).card ≤
      2 * ((fineSqQ N q).card + (fineT31 N q).card + (fineT211 N q).card + (fineT1111 N q).card) := by
  obtain ⟨_, _, _, _, hsq_prop, hlg_prop, _, _, _, _⟩ :=
    sixth_power_free_source_invariants ho hN hq hq4 he hev hfree
  have hq_prime := Nat.prime_of_mem_primeFactors hq
  obtain ⟨hK_src_eq, _, hK_int_col, _⟩ :=
    quarticChainSources_eq_oneModThree_prime_and_card ho hN hq hq4 he hev hfree
  have hK_mem : ∀ w ∈ quarticChainSources N q,
      w ∈ oneModThreeLargeSources N q ∧ (sigma 1 (w ^ 4)).Prime := fun w hw => by
    rw [hK_src_eq] at hw; exact Finset.mem_filter.mp hw
  have hK_int_sq : quarticChainIntermediates N q ⊆ squareSources N := fun s hs =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp (hK_int_col hs)).1).1
  have hK_cop : ∀ w ∈ quarticChainSources N q,
      (quarticFirstFactor w).Coprime (quarticSecondFactor w) ∧
      quarticFirstFactor w ≠ 0 ∧ quarticSecondFactor w ≠ 0 ∧
      sigma 1 ((sigma 1 (w ^ 4)) ^ 2) = quarticFirstFactor w * quarticSecondFactor w := by
    intro w hw
    have hw_lg := (Finset.mem_filter.mp (hK_mem w hw).1).1
    have hw_prime := (hlg_prop w hw_lg).1
    have hs_sq := hK_int_sq (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
    have hs_prime := (hsq_prop (sigma 1 (w ^ 4)) hs_sq).1
    have hs_exp := (hsq_prop (sigma 1 (w ^ 4)) hs_sq).2.2.2.2
    have hprod_eq : sigma 1 ((sigma 1 (w ^ 4)) ^ 2) = quarticFirstFactor w * quarticSecondFactor w := by
      rw [sigma_one_sq_local hs_prime, sigma_one_four_local hw_prime]
      exact quartic_phi3_factor_product w
    have h31 : ¬ 31 ∣ quarticFirstFactor w * quarticSecondFactor w := by
      rw [← hprod_eq]; intro hd
      have h31_N : 31 ∣ N := by
        apply dvd_perfect_of_exact_prime_pow hN hs_prime (hs_exp ▸ Nat.ordProj_dvd N (sigma 1 (w ^ 4)))
          ((hs_prime.pow_dvd_iff_le_factorization hN.2.ne').not.mpr (by omega))
          (by decide : Nat.Prime 31) (by decide : Odd 31)
        rw [← sigma_one_apply]; exact hd
      have h31_mem : 31 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, h31_N, hN.2.ne'⟩
      have := sixth_power_free_min_prime_ge_53 ho hN hfree h31_mem; omega
    have hA0 : quarticFirstFactor w ≠ 0 := by unfold quarticFirstFactor; omega
    have hB0 : quarticSecondFactor w ≠ 0 := by unfold quarticSecondFactor; positivity
    exact ⟨quartic_factors_coprime h31, hA0, hB0, hprod_eq⟩
  have hSp_sub_sq : fineSp N q ⊆ squareSources N := (Finset.filter_subset _ _).trans Finset.sdiff_subset
  have hS2_sub_sq : fineS2 N q ⊆ squareSources N := (Finset.filter_subset _ _).trans Finset.sdiff_subset
  have hTe1_ub : (fineTe1 N q).card ≤
      (fineSqQ N q).card + (fineT31 N q).card + (fineT211 N q).card + (fineT1111 N q).card := by
    have hsplit : (fineTe1 N q).card ≤
        (if q ∈ fineTe1 N q then 1 else 0) + ((fineTe1 N q).erase q).card := by
      by_cases hq_mem : q ∈ fineTe1 N q
      · simp only [hq_mem, ↓reduceIte, ← Finset.card_erase_add_one hq_mem]; omega
      · simp only [hq_mem, ↓reduceIte, Finset.erase_eq_of_notMem hq_mem]; omega
    have hq_le_Sq : (if q ∈ fineTe1 N q then 1 else 0) ≤ (fineSqQ N q).card := by
      split_ifs with hq_mem
      · obtain ⟨_, s, hs_sq, hs_fac1⟩ := Finset.mem_filter.mp hq_mem
        have hs_prime := (hsq_prop s hs_sq).1
        have hs_ne0 : sigma 1 (s ^ 2) ≠ 0 := by rw [sigma_one_sq_local hs_prime]; positivity
        have hq_dvd : q ∣ sigma 1 (s ^ 2) := (hq_prime.dvd_iff_one_le_factorization hs_ne0).mpr (by omega)
        exact Finset.card_pos.mpr ⟨s, Finset.mem_filter.mpr ⟨hs_sq, hq_dvd⟩⟩
      · exact Nat.zero_le _
    have herase_sub : (fineTe1 N q).erase q ⊆ fineT31 N q ∪ fineT211 N q ∪ fineT1111 N q := by
      intro t ht
      obtain ⟨htq, ht_mem⟩ := Finset.mem_erase.mp ht
      obtain ⟨ht_ins, s, hs_sq, hs_fac1⟩ := Finset.mem_filter.mp ht_mem
      have ht_Q13 : t ∈ oneModThreeLargeSources N q := (Finset.mem_insert.mp ht_ins).resolve_left htq
      have hs_mem := (Finset.mem_filter.mp hs_sq).1
      have hs_neq := (hsq_prop s hs_sq).2.2.2.1
      have hs_exp := (hsq_prop s hs_sq).2.2.2.2
      have hcomp_s : oddComponentSigma N q s = sigma 1 (s ^ 2) := by
        unfold oddComponentSigma; simp [hs_neq, hs_exp]
      have hin1 : 1 ≤ (N.primeFactors.filter
          (fun p => (oddComponentSigma N q p).factorization t = 1)).card :=
        Finset.card_pos.mpr ⟨s, Finset.mem_filter.mpr ⟨hs_mem, hcomp_s ▸ hs_fac1⟩⟩
      obtain ⟨h1, _, hle⟩ := (factorization_eq_indegAt_add_localRepeatAt ho hN hq hq4 he hev).1 t
        (Finset.mem_filter.mp (Finset.mem_filter.mp ht_Q13).1).1
      have ht_lg := (Finset.mem_filter.mp ht_Q13).1
      have ht_exp4 := (hlg_prop t ht_lg).2.2.2.2
      rcases (show indegAt N q t = 1 ∨ indegAt N q t = 2 ∨
          indegAt N q t = 3 ∨ indegAt N q t = 4 by omega) with hi1 | hi2 | hi3 | hi4
      · exfalso
        have h1_0 := (per_target_inExpCount ho hN hq hq4 he hev hfree ht_Q13).1 hi1 |>.1
        dsimp only at h1_0; omega
      · have hodd : ∃ p ∈ N.primeFactors, Odd ((oddComponentSigma N q p).factorization t) :=
          ⟨s, hs_mem, by rw [hcomp_s, hs_fac1]; decide⟩
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ht_Q13, hi2, hodd⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht_Q13, hi3⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht_Q13, hi4⟩)
    have hcard_er : ((fineTe1 N q).erase q).card ≤
        (fineT31 N q).card + (fineT211 N q).card + (fineT1111 N q).card :=
      (Finset.card_le_card herase_sub).trans
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    omega
  have hU_up_Phi3_TA1 :
      (fineSp N q).card + (fineS2 N q).card + (fineKB1 N q).card + (fineKA1 N q).card ≤
        (fineSqQ N q).card + (fineT31 N q).card + (fineT211 N q).card + (fineT1111 N q).card := by
    let T_A1 := (fineKA1 N q).image quarticFirstFactor
    have hTA1_inj : Set.InjOn quarticFirstFactor (fineKA1 N q : Set ℕ) := by
      intro w₁ hw₁ w₂ hw₂ heq
      have h1_ge : 1 ≤ w₁ := by
        have := (hlg_prop w₁ (Finset.mem_filter.mp (hK_mem w₁ (Finset.mem_filter.mp hw₁).1).1).1).2.2.1
        omega
      have h2_ge : 1 ≤ w₂ := by
        have := (hlg_prop w₂ (Finset.mem_filter.mp (hK_mem w₂ (Finset.mem_filter.mp hw₂).1).1).1).2.2.1
        omega
      dsimp [quarticFirstFactor] at heq
      have hle1 : w₁ ≤ w₁ ^ 2 := Nat.le_self_pow (by decide : 2 ≠ 0) w₁
      have hle2 : w₂ ≤ w₂ ^ 2 := Nat.le_self_pow (by decide : 2 ≠ 0) w₂
      zify [hle1, hle2] at heq
      have hfac : ((w₁ : ℤ) - (w₂ : ℤ)) * ((w₁ : ℤ) + (w₂ : ℤ) - 1) = 0 := by linarith only [heq]
      rcases mul_eq_zero.mp hfac with hsub | hadd
      · exact Nat.cast_injective (sub_eq_zero.mp hsub)
      · exfalso; omega
    have hTA1_card : T_A1.card = (fineKA1 N q).card := Finset.card_image_of_injOn hTA1_inj
    have hTA1_sub : T_A1 ⊆ fineTe1 N q := by
      intro t ht
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp ht
      have hwK := (Finset.mem_filter.mp hw).1
      have ht_prime : (quarticFirstFactor w).Prime :=
        cardFactors_eq_one_iff_prime.mp (Finset.mem_filter.mp hw).2
      obtain ⟨hcop, hA0, hB0, hprod_eq⟩ := hK_cop w hwK
      let s := sigma 1 (w ^ 4)
      have hs_sq : s ∈ squareSources N := hK_int_sq (Finset.mem_image.mpr ⟨w, hwK, rfl⟩)
      have ht_fac1 : (sigma 1 (s ^ 2)).factorization (quarticFirstFactor w) = 1 := by
        rw [hprod_eq, Nat.factorization_mul hA0 hB0, Finsupp.add_apply, ht_prime.factorization_self]
        have hndvd : ¬ quarticFirstFactor w ∣ quarticSecondFactor w := fun hd =>
          ht_prime.not_dvd_one (hcop ▸ Nat.dvd_gcd dvd_rfl hd)
        rw [Nat.factorization_eq_zero_of_not_dvd hndvd, add_zero]
      have ht_pf : quarticFirstFactor w ∈ (sigma 1 (s ^ 2)).primeFactors :=
        Finsupp.mem_support_iff.mpr (by rw [ht_fac1]; decide)
      have ht_ins := sq_sigma_primeFactors_subset ho hN hq hq4 he hev hfree hs_sq ht_pf
      exact Finset.mem_filter.mpr ⟨ht_ins, s, hs_sq, ht_fac1⟩
    let upPhi3 := (squareSources N ×ˢ (fineTe1 N q \ T_A1)).filter
      (fun st => st.1 < st.2 ∧ st.2 ∣ st.1 ^ 2 + st.1 + 1)
    have hup_ub : upPhi3.card ≤ (fineTe1 N q).card - (fineKA1 N q).card := by
      have hfib : upPhi3.card =
          ∑ t ∈ fineTe1 N q \ T_A1, (upPhi3.filter (fun st => st.2 = t)).card :=
        Finset.card_eq_sum_card_fiberwise fun st hst =>
          (Finset.mem_product.mp (Finset.mem_filter.mp hst).1).2
      rw [hfib]
      calc ∑ t ∈ fineTe1 N q \ T_A1, (upPhi3.filter (fun st => st.2 = t)).card
          ≤ ∑ _t ∈ fineTe1 N q \ T_A1, 1 := by
            refine Finset.sum_le_sum fun t ht => ?_
            have ht_e1 := (Finset.mem_sdiff.mp ht).1
            have ht_ins := (Finset.mem_filter.mp ht_e1).1
            have ht_prime_and_mod3 : t.Prime ∧ t % 3 = 1 := by
              rcases Finset.mem_insert.mp ht_ins with rfl | ht_Q13
              · have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
                obtain ⟨hq12, _⟩ := three_free_euler_prime_mod_twelve ho hN hq hq4 he h3
                exact ⟨hq_prime, by omega⟩
              · have ht_lg := (Finset.mem_filter.mp ht_Q13).1
                exact ⟨(hlg_prop t ht_lg).1, (Finset.mem_filter.mp ht_Q13).2⟩
            have hle : (upPhi3.filter (fun st => st.2 = t)).card ≤
                ((Finset.range t).filter (fun s => s % 3 = 2 ∧ t ∣ s ^ 2 + s + 1)).card := by
              refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
              · intro st hst
                obtain ⟨hst_up, rfl⟩ := Finset.mem_filter.mp hst
                obtain ⟨hst_prod, hlt, hdvd⟩ := Finset.mem_filter.mp hst_up
                have hs_sq := (Finset.mem_product.mp hst_prod).1
                exact Finset.mem_filter.mpr
                  ⟨Finset.mem_range.mpr hlt, (hsq_prop st.1 hs_sq).2.1, hdvd⟩
              · intro ⟨s₁, t₁⟩ h1 ⟨s₂, t₂⟩ h2 heq
                have ht1 : t₁ = t := (Finset.mem_filter.mp h1).2
                have ht2 : t₂ = t := (Finset.mem_filter.mp h2).2
                dsimp only at heq; ext <;> simp [heq, ht1, ht2]
            exact hle.trans (card_range_two_mod_three_dvd_sq_add_self_add_one_le_one
              ht_prime_and_mod3.1 ht_prime_and_mod3.2)
        _ = (fineTe1 N q \ T_A1).card := by simp [Finset.sum_const]
        _ = (fineTe1 N q).card - (fineKA1 N q).card := by
            rw [Finset.card_sdiff_of_subset hTA1_sub, hTA1_card]
    let kB1_int := (fineKB1 N q).image (fun w => sigma 1 (w ^ 4))
    have hkB1_inj : Set.InjOn (fun w => sigma 1 (w ^ 4)) (fineKB1 N q : Set ℕ) := by
      intro w₁ hw₁ w₂ hw₂ heq
      have hw₁_p := (hlg_prop w₁ (Finset.mem_filter.mp (hK_mem w₁ (Finset.mem_filter.mp hw₁).1).1).1).1
      have hw₂_p := (hlg_prop w₂ (Finset.mem_filter.mp (hK_mem w₂ (Finset.mem_filter.mp hw₂).1).1).1).1
      dsimp only at heq
      rw [sigma_one_four_local hw₁_p, sigma_one_four_local hw₂_p] at heq
      rcases lt_trichotomy w₁ w₂ with hlt | rfl | hgt
      · have : w₁ ^ 2 < w₂ ^ 2 := Nat.pow_lt_pow_left hlt (by decide)
        have : w₁ ^ 3 < w₂ ^ 3 := Nat.pow_lt_pow_left hlt (by decide)
        have : w₁ ^ 4 < w₂ ^ 4 := Nat.pow_lt_pow_left hlt (by decide)
        omega
      · rfl
      · have : w₂ ^ 2 < w₁ ^ 2 := Nat.pow_lt_pow_left hgt (by decide)
        have : w₂ ^ 3 < w₁ ^ 3 := Nat.pow_lt_pow_left hgt (by decide)
        have : w₂ ^ 4 < w₁ ^ 4 := Nat.pow_lt_pow_left hgt (by decide)
        omega
    have hkB1_card : kB1_int.card = (fineKB1 N q).card := Finset.card_image_of_injOn hkB1_inj
    have hkB1_sub_K : kB1_int ⊆ quarticChainIntermediates N q :=
      Finset.image_subset_image (Finset.filter_subset _ _)
    have hkB1_sub_sq : kB1_int ⊆ squareSources N := hkB1_sub_K.trans hK_int_sq
    have hS_p_2_disj : Disjoint (fineSp N q) (fineS2 N q) :=
      Finset.disjoint_left.mpr fun s h1 h2 => by
        have c1 := (Finset.mem_filter.mp h1).2; have c2 := (Finset.mem_filter.mp h2).2; omega
    have hdisj_Sp_2_B1 : Disjoint (fineSp N q ∪ fineS2 N q) kB1_int := by
      apply Finset.disjoint_left.mpr; intro s h1 h2
      have hs_nc : s ∈ fineSnc N q := by
        rcases Finset.mem_union.mp h1 with hp | h2'
        · exact (Finset.mem_filter.mp hp).1
        · exact (Finset.mem_filter.mp h2').1
      exact (Finset.mem_sdiff.mp hs_nc).2 (hkB1_sub_K h2)
    have hnot_TA1 : ∀ s ∈ squareSources N, ∀ t ∈ fineTe1 N q, s < t → t ∣ s ^ 2 + s + 1 → t ∉ T_A1 := by
      intro s hs_sq t _ hst hdvd ht_A1
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp ht_A1
      have hwK := (Finset.mem_filter.mp hw).1
      have hw_lg := (Finset.mem_filter.mp (hK_mem w hwK).1).1
      have hw_mem := (Finset.mem_filter.mp hw_lg).1
      have hw_odd : Odd w := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hw_mem)
      have hw53 := (hlg_prop w hw_lg).2.2.1
      have ht_prime := cardFactors_eq_one_iff_prime.mp (Finset.mem_filter.mp hw).2
      have hs_mem := (Finset.mem_filter.mp hs_sq).1
      have hs_odd : Odd s := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hs_mem)
      have h_empty := sq_add_self_add_one_no_odd_roots_lt_of_quarticFirstFactor_prime
        hw_odd (by omega) ht_prime
      have hmem : s ∈ (Finset.range (quarticFirstFactor w)).filter
          (fun s => Odd s ∧ quarticFirstFactor w ∣ s ^ 2 + s + 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hst, hs_odd, hdvd⟩
      rw [h_empty] at hmem; simp at hmem
    have hup_lb : (fineSp N q).card + (fineS2 N q).card + (fineKB1 N q).card ≤ upPhi3.card := by
      have hfib : upPhi3.card = ∑ s ∈ squareSources N, (upPhi3.filter (fun st => st.1 = s)).card :=
        Finset.card_eq_sum_card_fiberwise fun st hst =>
          (Finset.mem_product.mp (Finset.mem_filter.mp hst).1).1
      have hex_ge1 : ∀ s ∈ fineSp N q ∪ fineS2 N q ∪ kB1_int,
          1 ≤ (upPhi3.filter (fun st => st.1 = s)).card := by
        intro s hs
        rcases Finset.mem_union.mp hs with hs_p2 | hs_B1
        · rcases Finset.mem_union.mp hs_p2 with hs_p | hs_2
          · have hs_sq := hSp_sub_sq hs_p
            have hs_prime := (hsq_prop s hs_sq).1
            have ht_prime : (sigma 1 (s ^ 2)).Prime :=
              cardFactors_eq_one_iff_prime.mp (Finset.mem_filter.mp hs_p).2
            let t := sigma 1 (s ^ 2)
            have ht_eq : t = s ^ 2 + s + 1 := sigma_one_sq_local hs_prime
            have hst : s < t := by rw [ht_eq]; nlinarith only [hs_prime.two_le]
            have ht_e1 : t ∈ fineTe1 N q := by
              have ht_pf : t ∈ (sigma 1 (s ^ 2)).primeFactors :=
                Nat.mem_primeFactors.mpr ⟨ht_prime, dvd_rfl, ht_prime.ne_zero⟩
              exact Finset.mem_filter.mpr
                ⟨sq_sigma_primeFactors_subset ho hN hq hq4 he hev hfree hs_sq ht_pf,
                  s, hs_sq, ht_prime.factorization_self⟩
            have ht_notA1 := hnot_TA1 s hs_sq t ht_e1 hst (ht_eq ▸ dvd_rfl)
            exact Finset.card_pos.mpr ⟨(s, t), Finset.mem_filter.mpr
              ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hs_sq, Finset.mem_sdiff.mpr ⟨ht_e1, ht_notA1⟩⟩,
                hst, ht_eq ▸ dvd_rfl⟩, rfl⟩⟩
          · have hs_sq := hS2_sub_sq hs_2
            have hs_prime := (hsq_prop s hs_sq).1
            have hsig_eq : sigma 1 (s ^ 2) = s ^ 2 + s + 1 := sigma_one_sq_local hs_prime
            have hsig_ne0 : sigma 1 (s ^ 2) ≠ 0 := by rw [hsig_eq]; positivity
            have hcf2 : cardFactors (sigma 1 (s ^ 2)) = 2 := (Finset.mem_filter.mp hs_2).2
            have hnsq : ¬ IsSquare (sigma 1 (s ^ 2)) := by
              rw [hsig_eq]; rintro ⟨y, hy⟩
              have hlo : s ^ 2 < s ^ 2 + s + 1 := by omega
              have hhi : s ^ 2 + s + 1 < (s + 1) ^ 2 := by nlinarith only [hs_prime.two_le]
              exact Nat.not_exists_sq' hlo hhi ⟨y, by simpa [pow_two] using hy.symm⟩
            have hcop_s : s.Coprime (s ^ 2 + s + 1) := by
              apply Nat.coprime_of_dvd; intro p hp hps hpd
              exact hp.not_dvd_one ((Nat.dvd_add_right (hps.mul_right (s + 1))).mp
                (by simpa [show s ^ 2 + s = s * (s + 1) by ring] using hpd))
            have hex_t : ∃ t ∈ (sigma 1 (s ^ 2)).primeFactors, s < t := by
              by_contra! hall
              have hall_lt : ∀ p ∈ (sigma 1 (s ^ 2)).primeFactors, p ≤ s - 1 := by
                intro p hp
                have hp_le := hall p hp
                have hp_ne : p ≠ s := fun he => by
                  subst he
                  have hp_p := Nat.prime_of_mem_primeFactors hp
                  exact hp_p.not_dvd_one
                    (hcop_s ▸ Nat.dvd_gcd dvd_rfl (hsig_eq ▸ Nat.dvd_of_mem_primeFactors hp))
                omega
              have hprod_le : sigma 1 (s ^ 2) ≤ (s - 1) ^ 2 := by
                calc sigma 1 (s ^ 2)
                    = ∏ p ∈ (sigma 1 (s ^ 2)).primeFactors, p ^ (sigma 1 (s ^ 2)).factorization p :=
                      Nat.prod_primeFactors_pow_factorization hsig_ne0
                  _ ≤ ∏ p ∈ (sigma 1 (s ^ 2)).primeFactors,
                        (s - 1) ^ (sigma 1 (s ^ 2)).factorization p :=
                      Finset.prod_le_prod fun p hp => Nat.pow_le_pow_left (hall_lt p hp) _
                  _ = (s - 1) ^ (∑ p ∈ (sigma 1 (s ^ 2)).primeFactors, (sigma 1 (s ^ 2)).factorization p) :=
                      Finset.prod_pow_eq_pow_sum _ _ _
                  _ = (s - 1) ^ cardFactors (sigma 1 (s ^ 2)) := by
                      rw [cardFactors_eq_sum_factorization, Finsupp.sum]; rfl
                  _ = (s - 1) ^ 2 := by rw [hcf2]
              have hlt : (s - 1) ^ 2 < sigma 1 (s ^ 2) := by
                rw [hsig_eq]; have h2s := hs_prime.two_le
                zify [(by omega : 1 ≤ s)]; nlinarith only [h2s]
              omega
            obtain ⟨t, ht_pf, hst⟩ := hex_t
            have hfac1 : (sigma 1 (s ^ 2)).factorization t = 1 := by
              have hpos : 0 < (sigma 1 (s ^ 2)).factorization t :=
                Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ht_pf)
              have hle_sum : (sigma 1 (s ^ 2)).factorization t ≤ cardFactors (sigma 1 (s ^ 2)) := by
                have hs_sum : cardFactors (sigma 1 (s ^ 2)) =
                    ∑ p ∈ (sigma 1 (s ^ 2)).primeFactors, (sigma 1 (s ^ 2)).factorization p := by
                  rw [cardFactors_eq_sum_factorization, Finsupp.sum]; rfl
                rw [hs_sum]
                exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) ht_pf
              have hne2 : (sigma 1 (s ^ 2)).factorization t ≠ 2 := by
                intro h2
                have hdiv_all :
                    ∑ p ∈ (sigma 1 (s ^ 2)).primeFactors, (sigma 1 (s ^ 2)).factorization p = 2 := by
                  have hs_sum : cardFactors (sigma 1 (s ^ 2)) =
                      ∑ p ∈ (sigma 1 (s ^ 2)).primeFactors, (sigma 1 (s ^ 2)).factorization p := by
                    rw [cardFactors_eq_sum_factorization, Finsupp.sum]; rfl
                  rw [← hs_sum, hcf2]
                have heq_t : sigma 1 (s ^ 2) = t ^ 2 := by
                  have hzero_other : ∀ p ∈ (sigma 1 (s ^ 2)).primeFactors, p ≠ t →
                      (sigma 1 (s ^ 2)).factorization p = 0 := by
                    intro p hp hpt
                    have h2sum : (sigma 1 (s ^ 2)).factorization t + (sigma 1 (s ^ 2)).factorization p ≤
                        ∑ x ∈ (sigma 1 (s ^ 2)).primeFactors, (sigma 1 (s ^ 2)).factorization x := by
                      rw [← Finset.sum_pair hpt.symm]
                      exact Finset.sum_le_sum_of_subset (by
                        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                        rcases hx with rfl | rfl <;> assumption)
                    omega
                  calc sigma 1 (s ^ 2)
                      = ∏ p ∈ (sigma 1 (s ^ 2)).primeFactors, p ^ (sigma 1 (s ^ 2)).factorization p :=
                        Nat.prod_primeFactors_pow_factorization hsig_ne0
                    _ = t ^ (sigma 1 (s ^ 2)).factorization t := by
                        rw [← Finset.mul_prod_erase _ _ ht_pf]
                        have hprod1 : ∏ p ∈ (sigma 1 (s ^ 2)).primeFactors.erase t,
                            p ^ (sigma 1 (s ^ 2)).factorization p = 1 :=
                          Finset.prod_eq_one fun p hp => by
                            rw [hzero_other p (Finset.mem_of_mem_erase hp) (Finset.mem_erase.mp hp).1,
                              pow_zero]
                        rw [hprod1, mul_one]
                    _ = t ^ 2 := by rw [h2]
                exact hnsq ⟨t, by rw [heq_t, pow_two]⟩
              omega
            have ht_e1 : t ∈ fineTe1 N q := Finset.mem_filter.mpr
              ⟨sq_sigma_primeFactors_subset ho hN hq hq4 he hev hfree hs_sq ht_pf, s, hs_sq, hfac1⟩
            have ht_dvd : t ∣ s ^ 2 + s + 1 := hsig_eq ▸ Nat.dvd_of_mem_primeFactors ht_pf
            have ht_notA1 := hnot_TA1 s hs_sq t ht_e1 hst ht_dvd
            exact Finset.card_pos.mpr ⟨(s, t), Finset.mem_filter.mpr
              ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hs_sq, Finset.mem_sdiff.mpr ⟨ht_e1, ht_notA1⟩⟩,
                hst, ht_dvd⟩, rfl⟩⟩
        · obtain ⟨w, hwB1, rfl⟩ := Finset.mem_image.mp hs_B1
          have hwK := (Finset.mem_filter.mp hwB1).1
          have hw_lg := (Finset.mem_filter.mp (hK_mem w hwK).1).1
          have hw_prime := (hlg_prop w hw_lg).1
          have hs_sq := hkB1_sub_sq hs_B1
          have hs_prime := (hsq_prop (sigma 1 (w ^ 4)) hs_sq).1
          let t := quarticSecondFactor w
          have ht_prime : t.Prime := cardFactors_eq_one_iff_prime.mp (Finset.mem_filter.mp hwB1).2
          obtain ⟨hcop, hA0, hB0, hprod_eq⟩ := hK_cop w hwK
          have hst : sigma 1 (w ^ 4) < t := by
            rw [sigma_one_four_local hw_prime]
            dsimp [t, quarticSecondFactor]
            have hw53 := (hlg_prop w hw_lg).2.2.1
            have hw12 : w ≤ w ^ 2 := by nlinarith only [hw53]
            have hw23 : 2 * w ^ 2 ≤ w ^ 3 := by
              rw [show w ^ 3 = w * w ^ 2 by ring]
              exact Nat.mul_le_mul_right _ (by omega)
            have hw34 : 2 * w ^ 3 ≤ w ^ 4 := by
              rw [show w ^ 4 = w * w ^ 3 by ring]
              exact Nat.mul_le_mul_right _ (by omega)
            have hw45 : 2 * w ^ 4 ≤ w ^ 5 := by
              rw [show w ^ 5 = w * w ^ 4 by ring]
              exact Nat.mul_le_mul_right _ (by omega)
            have hw56 : 3 * w ^ 5 ≤ w ^ 6 := by
              rw [show w ^ 6 = w * w ^ 5 by ring]
              exact Nat.mul_le_mul_right _ (by omega)
            omega
          have hfac1 : (sigma 1 ((sigma 1 (w ^ 4)) ^ 2)).factorization t = 1 := by
            rw [hprod_eq, Nat.factorization_mul hA0 hB0, Finsupp.add_apply, ht_prime.factorization_self]
            have hndvd : ¬ t ∣ quarticFirstFactor w := fun hd =>
              ht_prime.not_dvd_one (hcop ▸ Nat.dvd_gcd hd dvd_rfl)
            rw [Nat.factorization_eq_zero_of_not_dvd hndvd, zero_add]
          have ht_pf : t ∈ (sigma 1 ((sigma 1 (w ^ 4)) ^ 2)).primeFactors :=
            Finsupp.mem_support_iff.mpr (by rw [hfac1]; decide)
          have ht_e1 : t ∈ fineTe1 N q := Finset.mem_filter.mpr
            ⟨sq_sigma_primeFactors_subset ho hN hq hq4 he hev hfree hs_sq ht_pf,
              sigma 1 (w ^ 4), hs_sq, hfac1⟩
          have ht_dvd : t ∣ (sigma 1 (w ^ 4)) ^ 2 + sigma 1 (w ^ 4) + 1 := by
            rw [← sigma_one_sq_local hs_prime, hprod_eq]
            exact dvd_mul_left t _
          have ht_notA1 := hnot_TA1 (sigma 1 (w ^ 4)) hs_sq t ht_e1 hst ht_dvd
          exact Finset.card_pos.mpr ⟨(sigma 1 (w ^ 4), t), Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hs_sq, Finset.mem_sdiff.mpr ⟨ht_e1, ht_notA1⟩⟩,
              hst, ht_dvd⟩, rfl⟩⟩
      calc (fineSp N q).card + (fineS2 N q).card + (fineKB1 N q).card
          = (fineSp N q ∪ fineS2 N q ∪ kB1_int).card := by
              rw [Finset.card_union_of_disjoint hdisj_Sp_2_B1,
                Finset.card_union_of_disjoint hS_p_2_disj, hkB1_card]
        _ = ∑ _s ∈ fineSp N q ∪ fineS2 N q ∪ kB1_int, 1 := by simp [Finset.sum_const]
        _ ≤ ∑ s ∈ fineSp N q ∪ fineS2 N q ∪ kB1_int, (upPhi3.filter (fun st => st.1 = s)).card :=
            Finset.sum_le_sum hex_ge1
        _ ≤ ∑ s ∈ squareSources N, (upPhi3.filter (fun st => st.1 = s)).card :=
            Finset.sum_le_sum_of_subset
              (Finset.union_subset (Finset.union_subset hSp_sub_sq hS2_sub_sq) hkB1_sub_sq)
        _ = upPhi3.card := hfib.symm
    have hTA1_le : (fineKA1 N q).card ≤ (fineTe1 N q).card := by
      rw [← hTA1_card]; exact Finset.card_le_card hTA1_sub
    omega
  have hU_up_A_TSp2 :
      (fineKA1 N q).card + (fineKA2 N q).card + 2 * (fineSp N q).card ≤
        2 * ((fineSqQ N q).card + (fineT31 N q).card + (fineT211 N q).card + (fineT1111 N q).card) := by
    let T_Sp := (fineSp N q).image (fun s => sigma 1 (s ^ 2))
    have hTSp_inj : Set.InjOn (fun s => sigma 1 (s ^ 2)) (fineSp N q : Set ℕ) := by
      intro s₁ hs₁ s₂ hs₂ heq
      have hs₁_p := (hsq_prop s₁ (hSp_sub_sq hs₁)).1
      have hs₂_p := (hsq_prop s₂ (hSp_sub_sq hs₂)).1
      dsimp only at heq
      rw [sigma_one_sq_local hs₁_p, sigma_one_sq_local hs₂_p] at heq
      rcases lt_trichotomy s₁ s₂ with hlt | rfl | hgt
      · have : s₁ ^ 2 < s₂ ^ 2 := Nat.pow_lt_pow_left hlt (by decide); omega
      · rfl
      · have : s₂ ^ 2 < s₁ ^ 2 := Nat.pow_lt_pow_left hgt (by decide); omega
    have hTSp_card : T_Sp.card = (fineSp N q).card := Finset.card_image_of_injOn hTSp_inj
    have hTSp_sub : T_Sp ⊆ fineTe1 N q := by
      intro t ht
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
      have hs_sq := hSp_sub_sq hs
      have ht_prime := cardFactors_eq_one_iff_prime.mp (Finset.mem_filter.mp hs).2
      have ht_pf : sigma 1 (s ^ 2) ∈ (sigma 1 (s ^ 2)).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨ht_prime, dvd_rfl, ht_prime.ne_zero⟩
      exact Finset.mem_filter.mpr
        ⟨sq_sigma_primeFactors_subset ho hN hq hq4 he hev hfree hs_sq ht_pf,
          s, hs_sq, ht_prime.factorization_self⟩
    have hdisj_A12 : Disjoint (fineKA1 N q) (fineKA2 N q) :=
      Finset.disjoint_left.mpr fun w h1 h2 => by
        have c1 := (Finset.mem_filter.mp h1).2; have c2 := (Finset.mem_filter.mp h2).2; omega
    let upA := ((fineKA1 N q ∪ fineKA2 N q) ×ˢ (fineTe1 N q \ T_Sp)).filter
      (fun wt => wt.1 < wt.2 ∧ wt.2 ∣ quarticFirstFactor wt.1)
    have hupA_ub : upA.card ≤ 2 * ((fineTe1 N q).card - (fineSp N q).card) := by
      have hfib : upA.card =
          ∑ t ∈ fineTe1 N q \ T_Sp, (upA.filter (fun wt => wt.2 = t)).card :=
        Finset.card_eq_sum_card_fiberwise fun wt hwt =>
          (Finset.mem_product.mp (Finset.mem_filter.mp hwt).1).2
      rw [hfib]
      calc ∑ t ∈ fineTe1 N q \ T_Sp, (upA.filter (fun wt => wt.2 = t)).card
          ≤ ∑ _t ∈ fineTe1 N q \ T_Sp, 2 := by
            refine Finset.sum_le_sum fun t ht => ?_
            have ht_e1 := (Finset.mem_sdiff.mp ht).1
            have ht_ins := (Finset.mem_filter.mp ht_e1).1
            have ht_prime : t.Prime := by
              rcases Finset.mem_insert.mp ht_ins with rfl | ht_Q13
              · exact hq_prime
              · exact (hlg_prop t (Finset.mem_filter.mp ht_Q13).1).1
            have hle : (upA.filter (fun wt => wt.2 = t)).card ≤
                ((Finset.range t).filter (fun w => t ∣ quarticFirstFactor w)).card := by
              refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
              · intro wt hwt
                obtain ⟨hwt_up, rfl⟩ := Finset.mem_filter.mp hwt
                obtain ⟨_, hlt, hdvd⟩ := Finset.mem_filter.mp hwt_up
                exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hdvd⟩
              · intro ⟨w₁, t₁⟩ h1 ⟨w₂, t₂⟩ h2 heq
                have ht1 : t₁ = t := (Finset.mem_filter.mp h1).2
                have ht2 : t₂ = t := (Finset.mem_filter.mp h2).2
                dsimp only at heq; ext <;> simp [heq, ht1, ht2]
            exact hle.trans (card_range_dvd_quarticFirstFactor_le_two ht_prime)
        _ = 2 * (fineTe1 N q \ T_Sp).card := by simp [Finset.sum_const, Nat.mul_comm]
        _ = 2 * ((fineTe1 N q).card - (fineSp N q).card) := by
            rw [Finset.card_sdiff_of_subset hTSp_sub, hTSp_card]
    have hupA_lb : (fineKA1 N q).card + (fineKA2 N q).card ≤ upA.card := by
      have hfib : upA.card = ∑ w ∈ fineKA1 N q ∪ fineKA2 N q, (upA.filter (fun wt => wt.1 = w)).card :=
        Finset.card_eq_sum_card_fiberwise fun wt hwt =>
          (Finset.mem_product.mp (Finset.mem_filter.mp hwt).1).1
      have hex_ge1 : ∀ w ∈ fineKA1 N q ∪ fineKA2 N q, 1 ≤ (upA.filter (fun wt => wt.1 = w)).card := by
        intro w hw
        have hwK : w ∈ quarticChainSources N q := by
          rcases Finset.mem_union.mp hw with h1 | h2
          · exact (Finset.mem_filter.mp h1).1
          · exact (Finset.mem_filter.mp h2).1
        have hw_lg := (Finset.mem_filter.mp (hK_mem w hwK).1).1
        have hw_mem := (Finset.mem_filter.mp hw_lg).1
        have hw_odd : Odd w := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hw_mem)
        have hw53 := (hlg_prop w hw_lg).2.2.1
        have hcf_le2 : cardFactors (quarticFirstFactor w) ≤ 2 := by
          rcases Finset.mem_union.mp hw with h1 | h2
          · have := (Finset.mem_filter.mp h1).2; omega
          · have := (Finset.mem_filter.mp h2).2; omega
        obtain ⟨t, ht_pf, hwt, hA_fac1⟩ :=
          quarticFirstFactor_exists_prime_gt_of_cardFactors_le_two (by omega : 2 ≤ w) hcf_le2
        have ht_prime := Nat.prime_of_mem_primeFactors ht_pf
        obtain ⟨hcop, hA0, hB0, hprod_eq⟩ := hK_cop w hwK
        let s := sigma 1 (w ^ 4)
        have hs_sq : s ∈ squareSources N := hK_int_sq (Finset.mem_image.mpr ⟨w, hwK, rfl⟩)
        have ht_fac1 : (sigma 1 (s ^ 2)).factorization t = 1 := by
          rw [hprod_eq, Nat.factorization_mul hA0 hB0, Finsupp.add_apply, hA_fac1]
          have hndvd : ¬ t ∣ quarticSecondFactor w := fun hd =>
            ht_prime.not_dvd_one (hcop ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors ht_pf) hd)
          rw [Nat.factorization_eq_zero_of_not_dvd hndvd, add_zero]
        have ht_sig_pf : t ∈ (sigma 1 (s ^ 2)).primeFactors :=
          Finsupp.mem_support_iff.mpr (by rw [ht_fac1]; decide)
        have ht_e1 : t ∈ fineTe1 N q := Finset.mem_filter.mpr
          ⟨sq_sigma_primeFactors_subset ho hN hq hq4 he hev hfree hs_sq ht_sig_pf, s, hs_sq, ht_fac1⟩
        have ht_notSp : t ∉ T_Sp := by
          intro ht_sp
          obtain ⟨s₀, hs₀, rfl⟩ := Finset.mem_image.mp ht_sp
          have hs₀_sq := hSp_sub_sq hs₀
          have hs₀_mem := (Finset.mem_filter.mp hs₀_sq).1
          have hs₀_prime := (hsq_prop s₀ hs₀_sq).1
          have hs₀_odd : Odd s₀ := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hs₀_mem)
          have ht_sig_prime : (s₀ ^ 2 + s₀ + 1).Prime := by
            rw [← sigma_one_sq_local hs₀_prime]
            exact cardFactors_eq_one_iff_prime.mp (Finset.mem_filter.mp hs₀).2
          have h_empty := quarticFirstFactor_no_odd_roots_lt_of_sq_add_self_add_one_prime
            hs₀_odd ht_sig_prime
          have ht_dvd : s₀ ^ 2 + s₀ + 1 ∣ quarticFirstFactor w := by
            rw [← sigma_one_sq_local hs₀_prime]
            exact Nat.dvd_of_mem_primeFactors ht_pf
          have hwt' : w < s₀ ^ 2 + s₀ + 1 := by
            rw [← sigma_one_sq_local hs₀_prime]; exact hwt
          have hmem : w ∈ (Finset.range (s₀ ^ 2 + s₀ + 1)).filter
              (fun w => Odd w ∧ s₀ ^ 2 + s₀ + 1 ∣ quarticFirstFactor w) :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hwt', hw_odd, ht_dvd⟩
          rw [h_empty] at hmem; simp at hmem
        have ht_dvd : t ∣ quarticFirstFactor w := Nat.dvd_of_mem_primeFactors ht_pf
        exact Finset.card_pos.mpr ⟨(w, t), Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hw, Finset.mem_sdiff.mpr ⟨ht_e1, ht_notSp⟩⟩,
            hwt, ht_dvd⟩, rfl⟩⟩
      calc (fineKA1 N q).card + (fineKA2 N q).card
          = (fineKA1 N q ∪ fineKA2 N q).card := (Finset.card_union_of_disjoint hdisj_A12).symm
        _ = ∑ _w ∈ fineKA1 N q ∪ fineKA2 N q, 1 := by simp [Finset.sum_const]
        _ ≤ ∑ w ∈ fineKA1 N q ∪ fineKA2 N q, (upA.filter (fun wt => wt.1 = w)).card :=
            Finset.sum_le_sum hex_ge1
        _ = upA.card := hfib.symm
    have hTSp_le : (fineSp N q).card ≤ (fineTe1 N q).card := by
      rw [← hTSp_card]; exact Finset.card_le_card hTSp_sub
    omega
  exact ⟨hU_up_Phi3_TA1, hU_up_A_TSp2⟩

/-- **Prime-Target Reuse Obstruction on Sixth-Power-Free Odd Perfect Numbers**:
Derives the full suite of target-reuse bounds (`Q₁₃ + 2 * Q₂₃ ≤ 2 * S₅₁_col`,
`Q₂₃ ≤ Q₁₃ + 1`, `2 * ω(N) ≤ 7 * Q₁₃ + 6`, `126 ≤ Q₁₃`, `5 * ω(N) ≤ 16 * S₅₁ + 16`,
`138 ≤ S₅₁`, `ω(N) ≤ 6 * S₅₁_col + 2`, `74 ≤ S₅₁_col`, `13 * ω(N) ≤ 20 * E + 38`,
`287 ≤ E`, the assessment-family killer `9 * Q₁₃ ≤ 8 * (EQ₁₃ + S₅₁_rep + Q₂₃ + S₅₀) + 10`,
and the coupled rank pinch `ω(N) + 20 * Q₁₃ ≤ 20 * (EQ₁₃ + S₅₁_rep + Q₂₃ + S₅₀) + 26`). -/
theorem sixth_power_free_prime_target_reuse_obstruction {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S₅₀ := (squareSources N).filter (· % 5 ≠ 1)
    let S₅₁ := (squareSources N).filter (· % 5 = 1)
    let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
    let S₅₁_rep := S₅₁.filter (fun r => indegAt N q r = 1)
    let Q₁₃ := oneModThreeLargeSources N q
    let Q₂₃ := twoModThreeLargeSources N q
    Q₁₃.card + 2 * Q₂₃.card ≤ 2 * S₅₁_col.card ∧
    Q₂₃.card ≤ Q₁₃.card + 1 ∧
    2 * N.primeFactors.card ≤ 7 * Q₁₃.card + 6 ∧
    126 ≤ Q₁₃.card ∧
    5 * N.primeFactors.card ≤ 16 * S₅₁.card + 16 ∧
    138 ≤ S₅₁.card ∧
    N.primeFactors.card ≤ 6 * S₅₁_col.card + 2 ∧
    74 ≤ S₅₁_col.card ∧
    13 * N.primeFactors.card ≤ 20 * collisionExcess N q + 38 ∧
    287 ≤ collisionExcess N q ∧
    9 * Q₁₃.card ≤
      8 * (∑ r ∈ Q₁₃, (indegAt N q r - 1)) + 8 * S₅₁_rep.card + 8 * Q₂₃.card + 8 * S₅₀.card + 10 ∧
    9 * Q₁₃.card + 8 * S₅₁_col.card ≤
      8 * collisionExcess N q + 8 * S₅₁_rep.card + 8 * Q₂₃.card + 8 * S₅₀.card + 10 ∧
    N.primeFactors.card + 20 * Q₁₃.card ≤
      20 * (∑ r ∈ Q₁₃, (indegAt N q r - 1)) + 20 * S₅₁_rep.card + 20 * Q₂₃.card + 20 * S₅₀.card + 26 := by
  intro S₅₀ S₅₁ S₅₁_col S₅₁_rep Q₁₃ Q₂₃
  obtain ⟨hω_eq, _, _⟩ := sixth_power_free_omega_and_total_identities ho hN hq hq4 he hev hfree
  have h443 : 443 ≤ N.primeFactors.card :=
    (sixth_power_free_collision_excess_ge_221 ho hN hq hq4 he hev hfree).1
  obtain ⟨_, _, hS51_card, hcol_split, _, _⟩ :=
    sixth_power_free_S51_collision_repeat_split ho hN hq hq4 he hev hfree
  change S₅₁.card = S₅₁_col.card + S₅₁_rep.card at hS51_card
  change collisionExcess N q = S₅₁_col.card + ∑ r ∈ Q₁₃, (indegAt N q r - 1) at hcol_split
  have hU_Q_e1 : Q₁₃.card + 2 * Q₂₃.card ≤ 2 * S₅₁_col.card :=
    sixth_power_free_quartic_to_S51_col_bound ho hN hq hq4 he hev hfree
  obtain ⟨hE1_q, hE2_Q13, hE2_Q23, hU_Q_Om, hU_up_Phi5⟩ :=
    fine_Q_partition_and_bounds ho hN hq hq4 he hev hfree
  obtain ⟨hE3_Snc, hE3_chA, hE3_chB, hE3_tgt, hEQ13_eq, hE4_e1, hE4_e2, hE4_e3, hE4_e4,
      hS3p_inv, hA3p_inv, hB26_inv, hB7p_inv⟩ :=
    fine_block_and_target_conservation ho hN hq hq4 he hev hfree
  obtain ⟨hU_up_Phi3_TA1, hU_up_A_TSp2⟩ :=
    fine_upward_reuse_bounds ho hN hq hq4 he hev hfree
  have hω_parts :
      N.primeFactors.card = 1 + (S₅₀.card + S₅₁_col.card + S₅₁_rep.card + Q₂₃.card + Q₁₃.card) := by
    omega
  obtain ⟨h1_z, h2_z, h3_z, h4_z, h5_z, h6_z, h7_z⟩ :=
    farkas_int_reductions
      (S₅₀.card : ℤ) S₅₁_col.card S₅₁_rep.card Q₂₃.card Q₁₃.card
      (∑ r ∈ Q₁₃, (indegAt N q r - 1))
      (quarticChainSources N q).card (fineQ13q N q).card (fineQ13_3 N q).card (fineQ13_5p N q).card
      (fineQ23_2 N q).card (fineQ23_4p N q).card
      (fineSp N q).card (fineS2 N q).card (fineS3p N q).card
      (fineKA1 N q).card (fineKA2 N q).card (fineKA3p N q).card
      (fineKB1 N q).card (fineKB26 N q).card (fineKB7p N q).card
      (fineT4 N q).card (fineT31 N q).card (fineT22 N q).card (fineT211 N q).card (fineT1111 N q).card
      (fineSqQ N q).card
      (fineHQe N q 1) (fineHQe N q 2) (fineHQe N q 3) (fineHQe N q 4)
      (fineS3pe N q 1) (fineS3pe N q 2) (fineS3pe N q 3) (fineS3pe N q 4)
      (fineA3pe N q 1) (fineA3pe N q 2) (fineA3pe N q 3) (fineA3pe N q 4)
      (fineB26e N q 1) (fineB26e N q 2) (fineB26e N q 3) (fineB26e N q 4)
      (fineB7pe N q 1) (fineB7pe N q 2) (fineB7pe N q 3) (fineB7pe N q 4)
      (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
      (by positivity)
      (by positivity) (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) (by positivity) (by positivity)
      (by exact_mod_cast hE1_q)
      (by exact_mod_cast hE2_Q13)
      (by exact_mod_cast hE2_Q23)
      (by exact_mod_cast hE3_Snc)
      (by exact_mod_cast hE3_chA)
      (by exact_mod_cast hE3_chB)
      (by exact_mod_cast hE3_tgt.symm)
      (by exact_mod_cast hEQ13_eq)
      (by exact_mod_cast hE4_e1)
      (by exact_mod_cast hE4_e2)
      (by exact_mod_cast hE4_e3)
      (by exact_mod_cast hE4_e4)
      (by exact_mod_cast hU_Q_Om)
      (by exact_mod_cast hU_Q_e1)
      (by exact_mod_cast hU_up_Phi5)
      (by exact_mod_cast hS3p_inv.1)
      (by exact_mod_cast hS3p_inv.2.1)
      (by exact_mod_cast hS3p_inv.2.2)
      (by exact_mod_cast hA3p_inv.1)
      (by exact_mod_cast hA3p_inv.2.1)
      (by exact_mod_cast hA3p_inv.2.2)
      (by exact_mod_cast hB26_inv.1)
      (by exact_mod_cast hB26_inv.2.1)
      (by exact_mod_cast hB26_inv.2.2)
      (by exact_mod_cast hB7p_inv.1)
      (by exact_mod_cast hB7p_inv.2)
      (by exact_mod_cast hU_up_Phi3_TA1)
      (by exact_mod_cast hU_up_A_TSp2)
  have hQ23_le : Q₂₃.card ≤ Q₁₃.card + 1 := by exact_mod_cast h1_z
  have h2om_le : 2 * N.primeFactors.card ≤ 7 * Q₁₃.card + 6 := by
    rw [hω_parts]; exact_mod_cast h2_z
  have hQ13_126 : 126 ≤ Q₁₃.card := by omega
  have h5om_le : 5 * N.primeFactors.card ≤ 16 * S₅₁.card + 16 := by
    rw [hω_parts, hS51_card]; exact_mod_cast h3_z
  have hS51_138 : 138 ≤ S₅₁.card := by omega
  have hom_le6 : N.primeFactors.card ≤ 6 * S₅₁_col.card + 2 := by
    rw [hω_parts]; exact_mod_cast h4_z
  have hS51_col_74 : 74 ≤ S₅₁_col.card := by omega
  have h13om_le : 13 * N.primeFactors.card ≤ 20 * collisionExcess N q + 38 := by
    rw [hω_parts, hcol_split]; exact_mod_cast h5_z
  have hE_287 : 287 ≤ collisionExcess N q := by omega
  have h9Q13_le : 9 * Q₁₃.card ≤
      8 * (∑ r ∈ Q₁₃, (indegAt N q r - 1)) + 8 * S₅₁_rep.card + 8 * Q₂₃.card + 8 * S₅₀.card + 10 := by
    exact_mod_cast h6_z
  have h9Q13_col : 9 * Q₁₃.card + 8 * S₅₁_col.card ≤
      8 * collisionExcess N q + 8 * S₅₁_rep.card + 8 * Q₂₃.card + 8 * S₅₀.card + 10 := by
    rw [hcol_split]; omega
  have hcoupled : N.primeFactors.card + 20 * Q₁₃.card ≤
      20 * (∑ r ∈ Q₁₃, (indegAt N q r - 1)) + 20 * S₅₁_rep.card + 20 * Q₂₃.card + 20 * S₅₀.card + 26 := by
    rw [hω_parts]; exact_mod_cast h7_z
  exact ⟨hU_Q_e1, hQ23_le, h2om_le, hQ13_126, h5om_le, hS51_138, hom_le6, hS51_col_74,
    h13om_le, hE_287, h9Q13_le, h9Q13_col, hcoupled⟩

/-- **Master Profile Wrapper**: Unpacks `euler_exponents` and `sixth_power_free_euler_exponent_one`
so callers need only `ho : Odd N`, `hN : N.Perfect`, and `hfree`. -/
theorem sixth_power_free_prime_target_reuse_master_profile {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    ∃ q ∈ N.primeFactors,
      q % 4 = 1 ∧
      N.factorization q = 1 ∧
      (∀ r : ℕ, r ≠ q → Even (N.factorization r)) ∧
      let S₅₀ := (squareSources N).filter (· % 5 ≠ 1)
      let S₅₁ := (squareSources N).filter (· % 5 = 1)
      let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
      let S₅₁_rep := S₅₁.filter (fun r => indegAt N q r = 1)
      let Q₁₃ := oneModThreeLargeSources N q
      let Q₂₃ := twoModThreeLargeSources N q
      Q₁₃.card + 2 * Q₂₃.card ≤ 2 * S₅₁_col.card ∧
      Q₂₃.card ≤ Q₁₃.card + 1 ∧
      2 * N.primeFactors.card ≤ 7 * Q₁₃.card + 6 ∧
      126 ≤ Q₁₃.card ∧
      5 * N.primeFactors.card ≤ 16 * S₅₁.card + 16 ∧
      138 ≤ S₅₁.card ∧
      N.primeFactors.card ≤ 6 * S₅₁_col.card + 2 ∧
      74 ≤ S₅₁_col.card ∧
      13 * N.primeFactors.card ≤ 20 * collisionExcess N q + 38 ∧
      287 ≤ collisionExcess N q ∧
      9 * Q₁₃.card ≤
        8 * (∑ r ∈ Q₁₃, (indegAt N q r - 1)) + 8 * S₅₁_rep.card + 8 * Q₂₃.card + 8 * S₅₀.card + 10 ∧
      9 * Q₁₃.card + 8 * S₅₁_col.card ≤
        8 * collisionExcess N q + 8 * S₅₁_rep.card + 8 * Q₂₃.card + 8 * S₅₀.card + 10 ∧
      N.primeFactors.card + 20 * Q₁₃.card ≤
        20 * (∑ r ∈ Q₁₃, (indegAt N q r - 1)) + 20 * S₅₁_rep.card + 20 * Q₂₃.card + 20 * S₅₀.card + 26 := by
  obtain ⟨q, hq, hq4, he, hev⟩ := euler_exponents ho hN
  have hq1 := sixth_power_free_euler_exponent_one ho hN hq he hfree
  exact ⟨q, hq, hq4, hq1, hev,
    sixth_power_free_prime_target_reuse_obstruction ho hN hq hq4 he hev hfree⟩

/-- **Assessment-Regime Obstruction**:
Eliminates the unbounded assessment regime (`S₅₀ = ∅`, `S₅₁_rep = ∅`, `Q₂₃ = ∅`,
`collisionExcess N q ≤ S₅₁_col.card + Q₁₃.card`) unconditionally! -/
theorem no_sixth_power_free_odd_perfect_of_assessment_regime {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hS50 : (squareSources N).filter (· % 5 ≠ 1) = ∅)
    (hS51_rep : ((squareSources N).filter (· % 5 = 1)).filter (fun r => indegAt N q r = 1) = ∅)
    (hQ23 : twoModThreeLargeSources N q = ∅)
    (hcol : collisionExcess N q ≤
      (((squareSources N).filter (· % 5 = 1)).filter (fun r => indegAt N q r = 2)).card +
        (oneModThreeLargeSources N q).card) :
    False := by
  obtain ⟨_, _, _, h126, _, _, _, _, _, _, _, h9col, _⟩ :=
    sixth_power_free_prime_target_reuse_obstruction ho hN hq hq4 he hev hfree
  rw [hS50, hS51_rep, hQ23, Finset.card_empty] at h9col
  omega

/-! ## 5. Explicit Separation & Surviving Count-Family Theorems -/

/-- Wave K + Wave N + slack count-tuple predicate on `(S50, S51_col, S51_rep, Q23, Q13, EQ13)`. -/
@[expose] def SatisfiesWaveKAndSlackBounds (S50 S51_col S51_rep Q23 Q13 EQ13 : ℕ) : Prop :=
  let ω := 1 + S50 + S51_col + S51_rep + Q23 + Q13
  let Ω := 1 + 2 * (S50 + S51_col + S51_rep) + 4 * (Q23 + Q13)
  let E := S51_col + EQ13
  EQ13 ≤ 3 * Q13 ∧
  443 ≤ ω ∧
  1179 ≤ Ω ∧
  221 ≤ E ∧
  ω ≤ 2 * E + 2 ∧
  8 * ω + 4 * Q23 ≤ 3 * Ω + 7 ∧
  221 ≤ S51_col + 3 * Q13 ∧
  2 * Q23 ≤ 5 * Q13 + 7 ∧
  2 * ω ≤ 11 * Q13 + 11 ∧
  80 ≤ Q13 ∧
  ω ≤ 2 * S51_col + 6 * Q13 + 2 ∧
  S50 + S51_rep + Q23 ≤ S51_col + 5 * Q13 + 1 ∧
  3 * Q13 + 2 * Q23 ≤ 4 * S51_col + 2 * S51_rep + 3 ∧
  219 ≤ 2 * S51_col + S51_rep ∧
  ω ≤ 4 * S51_col + 2 * S51_rep + 5

/-- Target-reuse count-tuple predicate capturing all bounds of
`sixth_power_free_prime_target_reuse_obstruction`. -/
@[expose] def SatisfiesTargetReuseBounds (S50 S51_col S51_rep Q23 Q13 EQ13 : ℕ) : Prop :=
  let ω := 1 + S50 + S51_col + S51_rep + Q23 + Q13
  let E := S51_col + EQ13
  Q13 + 2 * Q23 ≤ 2 * S51_col ∧
  Q23 ≤ Q13 + 1 ∧
  2 * ω ≤ 7 * Q13 + 6 ∧
  126 ≤ Q13 ∧
  5 * ω ≤ 16 * (S51_col + S51_rep) + 16 ∧
  138 ≤ S51_col + S51_rep ∧
  ω ≤ 6 * S51_col + 2 ∧
  74 ≤ S51_col ∧
  13 * ω ≤ 20 * E + 38 ∧
  287 ≤ E ∧
  9 * Q13 ≤ 8 * EQ13 + 8 * S51_rep + 8 * Q23 + 8 * S50 + 10 ∧
  ω + 20 * Q13 ≤ 20 * EQ13 + 20 * S51_rep + 20 * Q23 + 20 * S50 + 26

theorem assessment_count_family_passes_waveK_fails_target_reuse (t : ℕ) (ht : 221 ≤ t) :
    SatisfiesWaveKAndSlackBounds 0 t 0 0 t t ∧ ¬ SatisfiesTargetReuseBounds 0 t 0 0 t t := by
  unfold SatisfiesWaveKAndSlackBounds SatisfiesTargetReuseBounds
  refine ⟨by omega, fun h => by omega⟩

theorem high_Q23_count_family_passes_waveK_fails_target_reuse (m : ℕ) (hm : 41 ≤ m) :
    SatisfiesWaveKAndSlackBounds 0 (4 * m) 0 (5 * m) (2 * m) (6 * m) ∧
    ¬ SatisfiesTargetReuseBounds 0 (4 * m) 0 (5 * m) (2 * m) (6 * m) := by
  unfold SatisfiesWaveKAndSlackBounds SatisfiesTargetReuseBounds
  refine ⟨by omega, fun h => by omega⟩

theorem low_collision_count_family_passes_waveK_fails_target_reuse (n : ℕ) (hn : 45 ≤ n) :
    SatisfiesWaveKAndSlackBounds 0 (2 * n) (4 * n) 0 (4 * n) (3 * n) ∧
    ¬ SatisfiesTargetReuseBounds 0 (2 * n) (4 * n) 0 (4 * n) (3 * n) := by
  unfold SatisfiesWaveKAndSlackBounds SatisfiesTargetReuseBounds
  refine ⟨by omega, fun h => by omega⟩

theorem surviving_square_ramified_count_family_satisfies_all (m : ℕ) (hm : 64 ≤ m) :
    SatisfiesWaveKAndSlackBounds 0 (2 * m + 1) (2 * m) m (2 * m) (4 * m) ∧
    SatisfiesTargetReuseBounds 0 (2 * m + 1) (2 * m) m (2 * m) (4 * m) := by
  unfold SatisfiesWaveKAndSlackBounds SatisfiesTargetReuseBounds
  omega

end OddPerfect

