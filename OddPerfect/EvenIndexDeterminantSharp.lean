module

public import OddPerfect.EvenIndexEffective
import Mathlib.Algebra.Order.Ring.Abs

public section
namespace OddPerfect
open Finset Matrix

/-- An anchored set of deterministic transitions imposes f(o)=0 at
its root and equality between neighboring entries in every other row. -/
@[expose] def transitionMatrix (R : Type*) [CommRing R] {α : Type*} [DecidableEq α]
    (o : α) (T : α→α) : Matrix α α R := fun i j =>
  (if j=i then 1 else 0) - (if i=o then 0 else if j=T i then 1 else 0)

private theorem transitionMatrix_mulVec {R α : Type*} [CommRing R] [Fintype α] [DecidableEq α]
    (o : α) (T : α→α) (v : α→R) (i : α) :
    (transitionMatrix R o T *ᵥ v) i=if i=o then v o else v i-v (T i) := by
  by_cases h : i=o <;> simp [transitionMatrix,Matrix.mulVec,dotProduct,sub_mul,ite_mul,Finset.sum_sub_distrib,h]

/-- Each deterministic matrix has determinant zero or a unit over the
integers. A nonzero modular kernel vector lifts to an integer kernel
vector simply by taking canonical representatives coordinatewise. -/
theorem transitionMatrix_natAbs_det_le_one {α : Type*} [DecidableEq α] [Fintype α]
    (o : α) (T : α→α) : (transitionMatrix ℤ o T).det.natAbs≤1 := by
  let A := transitionMatrix ℤ o T
  by_contra! big
  change 1<A.det.natAbs at big
  obtain ⟨r,hr,hd⟩ := Nat.exists_prime_and_dvd big.ne'
  let : Fact r.Prime := ⟨hr⟩
  let φ := Int.castRingHom (ZMod r)
  have hmap : φ.mapMatrix A=transitionMatrix (ZMod r) o T := by
    ext i j
    simp only [A,transitionMatrix,RingHom.mapMatrix_apply,Matrix.map_apply]
    split_ifs <;> norm_num [φ]
  have hint := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hd)
  have hzero := (ZMod.intCast_zmod_eq_zero_iff_dvd A.det r).mpr hint
  change φ A.det=0 at hzero
  rw [RingHom.map_det,hmap] at hzero
  obtain ⟨v,hne,hk⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hzero
  let w (i : α) : ℤ := (v i).val
  have hw : w≠0 := by
    intro he
    apply hne
    funext i
    have hh := congrFun he i
    change ((v i).val:ℤ)=0 at hh
    exact (ZMod.val_eq_zero _).mp (by exact_mod_cast hh)
  have hker : A *ᵥ w=0 := by
    funext i
    change (transitionMatrix ℤ o T *ᵥ w) i=0
    rw [transitionMatrix_mulVec]
    have hh := congrFun hk i
    change (transitionMatrix (ZMod r) o T *ᵥ v) i=0 at hh
    rw [transitionMatrix_mulVec] at hh
    by_cases hi : i=o
    · rw [ite_eq_left hi] at hh ⊢
      simp [w,hh]
    · rw [ite_eq_right hi] at hh ⊢
      simp [w,sub_eq_zero.mp hh]
  have hz := Matrix.exists_mulVec_eq_zero_iff.mp ⟨w,hw,hker⟩
  simp [hz] at big

/-- The binary choice of a neighbor gives the sharp exponential bound
on the anchored determinant. No assumptions on the step are required. -/
theorem returnDeterminant_le_two_pow_pred (β n : ℕ) : returnDeterminant β n≤2^(β-1) := by
  cases β with
  | zero => simp [returnDeterminant]
  | succ b =>
    let I := ZMod (b+1)
    let A : Matrix I I ℤ := transitionMatrix ℤ 0 (fun i => i+1)
    let B : Matrix I I ℤ := transitionMatrix ℤ 0 (fun i => i+n)
    let M := returnMatrix ℤ b n
    have hrow : A+B=M.updateRow 0 ((2:ℤ) • M 0) := by
      ext i j
      change A i j+B i j=(M.updateRow 0 ((2:ℤ) • M 0)) i j
      by_cases hi : i=0
      · subst i
        simp [A,B,M,transitionMatrix,returnMatrix,Matrix.updateRow_self]
        split_ifs <;> decide
      · simp only [Matrix.updateRow_ne hi,A,B,M,transitionMatrix,returnMatrix,ite_eq_right hi]
        split_ifs <;> decide
    have hdet : (A+B).det=2*M.det := by
      rw [hrow,Matrix.det_updateRow_smul,Matrix.updateRow_eq_self]
    have hpiece (S : Finset I) : |Matrix.det (S.piecewise A B)|≤1 := by
      let T (i : I) := if i∈S then i+1 else i+n
      have hmat : S.piecewise A B=transitionMatrix ℤ 0 T := by
        ext i j
        by_cases hi : i∈S <;> simp [A,B,T,transitionMatrix,hi,Finset.piecewise]
      have hc := transitionMatrix_natAbs_det_le_one (0:I) T
      rw [hmat,←Int.natCast_natAbs]
      exact_mod_cast hc
    have hm := (Matrix.detRowAlternating (R:=ℤ) (n:=I)).toMultilinearMap.map_add_univ A B
    change (A+B).det=∑ S : Finset I, Matrix.det (S.piecewise A B) at hm
    have H : |(A+B).det|≤(2:ℤ)^(b+1) := by
      calc |(A+B).det| = |∑ S : Finset I, Matrix.det (S.piecewise A B)| := congrArg abs hm
           _ ≤ ∑ S : Finset I, |Matrix.det (S.piecewise A B)| := Finset.abs_sum_le_sum_abs _ _
           _ ≤ ∑ _S : Finset I, (1:ℤ) := Finset.sum_le_sum (fun S _ => hpiece S)
           _ = (2:ℤ)^(b+1) := by simp [I]
    rw [hdet,abs_mul,abs_of_pos (by decide : (0:ℤ)<2),pow_succ] at H
    change M.det.natAbs≤2^b
    rw [←Nat.cast_le (α:=ℤ),Int.natCast_natAbs,Nat.cast_pow,Nat.cast_ofNat]
    omega

end OddPerfect
