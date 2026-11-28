module

public import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

namespace OddPerfect

/-- Coordinates of the odd powers of √(x+1)+√x, after removing the
corresponding square root from each coordinate. -/
@[expose] def alternatingPellCoordinates (x : ℤ) : ℕ → ℤ × ℤ
  | 0 => (1, 1)
  | j+1 =>
    let (y,z) := alternatingPellCoordinates x j
    ((2*x+1)*y+2*x*z, 2*(x+1)*y+(2*x+1)*z)

private theorem alternatingPellCoordinates_pos {x : ℤ} (hx : 0 < x) (j : ℕ) :
    0 < (alternatingPellCoordinates x j).1 ∧ 0 < (alternatingPellCoordinates x j).2 := by
  induction j with
  | zero => simp [alternatingPellCoordinates]
  | succ j ih =>
    obtain ⟨hy,hz⟩ := ih
    simp only [alternatingPellCoordinates]
    constructor <;> positivity

theorem alternatingPellCoordinates_gt_length {x : ℤ} (hx : 0<x) (j : ℕ) :
    (2*j+1:ℤ) ≤ (alternatingPellCoordinates x j).2 ∧
      (0<j → (2*j+1:ℤ) < (alternatingPellCoordinates x j).2) := by
  induction j with
  | zero => simp [alternatingPellCoordinates]
  | succ j ih =>
    obtain ⟨hy,hz⟩ := alternatingPellCoordinates_pos hx j
    simp only [alternatingPellCoordinates,Nat.cast_succ]
    have h : 2*((j:ℤ)+1)+1 <
        2*(x+1)*(alternatingPellCoordinates x j).1+(2*x+1)*(alternatingPellCoordinates x j).2 := by
      nlinarith [mul_pos hx hy, mul_pos hx hz, ih.1]
    exact ⟨h.le,fun _ => h⟩

/-- Every positive solution of (x+1)y²−xz²=1 occurs in the recurrence.
The inverse recurrence strictly decreases z unless (y,z)=(1,1). -/
theorem exists_alternatingPellCoordinates {x y z : ℤ} (hx : 0<x) (hy : 0<y) (hz : 0<z)
    (he : (x+1)*y^2-x*z^2=1) : ∃ j, alternatingPellCoordinates x j=(y,z) := by
  suffices H : ∀ (k : ℕ) (y z : ℤ), z.toNat=k → 0<y → 0<z → (x+1)*y^2-x*z^2=1 →
      ∃ j, alternatingPellCoordinates x j=(y,z) by exact H _ _ _ rfl hy hz he
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro y z hk hy hz he
    by_cases hbase : z=1
    · subst z
      have hys : y^2=1 := by
        have h : (x+1)*(y^2-1)=0 := by nlinarith
        rcases mul_eq_zero.mp h with e|e <;> omega
      have hy1 : y=1 := by nlinarith
      subst y
      exact ⟨0,rfl⟩
    have hz1 : 1<z := by omega
    have hyz : y<z := by
      by_contra! hn
      have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz.le hn 2) (by omega : 0 ≤ x+1)
      nlinarith [sq_nonneg (z-2)]
    have hh : x*(z+y) ≤ x*(z+y)*(z-y) := by
      have ht : 0 ≤ x*(z+y)*(z-y-1) := mul_nonneg (by positivity) (by omega)
      linarith [show x*(z+y)*(z-y-1)=x*(z+y)*(z-y)-x*(z+y) by ring]
    have hyX : 2*x < y := by
      by_contra! hn
      have ht := mul_le_mul_of_nonneg_right hn hy.le
      nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hyz.le)]
    have hz2 : 4*(x+1)<z^2 := by
      have hzz : 2*x+2 ≤ z := by omega
      have ht := pow_le_pow_left₀ (by omega : 0≤2*x+2) hzz 2
      nlinarith [sq_nonneg x]
    let Y := (2*x+1)*y-2*x*z
    let Z := (2*x+1)*z-2*(x+1)*y
    have hY : 0<Y := by
      have heq : ((2*x+1)*y)^2-(2*x*z)^2=y^2+4*x := by
        linear_combination 4*x*he
      have hn : 0 ≤ (2*x+1)*y := by positivity
      have ht : 0 ≤ 2*x*z := by positivity
      dsimp only [Y]
      by_contra! h
      have hs := pow_le_pow_left₀ hn (sub_nonpos.mp h) 2
      nlinarith [sq_nonneg y]
    have hZ : 0<Z := by
      have heq : ((2*x+1)*z)^2-(2*(x+1)*y)^2=z^2-4*(x+1) := by
        linear_combination -4*(x+1)*he
      dsimp only [Z]
      by_contra! h
      have hs := pow_le_pow_left₀ (by positivity : 0≤(2*x+1)*z) (sub_nonpos.mp h) 2
      nlinarith
    have hlt : Z<z := by
      have hh : (x*z)^2 < ((x+1)*y)^2 := by
        have ht : ((x+1)*y)^2-(x*z)^2=(x+1)*y^2+x := by linear_combination x*he
        nlinarith [mul_nonneg (by omega : 0≤x+1) (sq_nonneg y)]
      have hs : x*z < (x+1)*y := by
        by_contra! h
        exact hh.not_ge (pow_le_pow_left₀ (by positivity) h 2)
      dsimp only [Z]
      linarith
    have hnorm : (x+1)*Y^2-x*Z^2=1 := by
      dsimp only [Y,Z]
      linear_combination he
    obtain ⟨j,hj⟩ := ih Z.toNat (by omega) Y Z rfl hY hZ hnorm
    refine ⟨j+1,?_⟩
    simp only [alternatingPellCoordinates,hj]
    congr 1 <;> dsimp [Y,Z] <;> ring

end OddPerfect
