module

public import OddPerfect.EvenIndexRoots
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.LinearCombination

public section
namespace OddPerfect
open Finset ArithmeticFunction Matrix

/-- The nonzero rows impose the cyclic average relation with steps 1
and n. The row at zero anchors the constant functions. The cycle has b+1
vertices, corresponding to a positive return multiplicity. -/
@[expose] def returnMatrix (R : Type*) [CommRing R] (b n : ℕ) :
    Matrix (ZMod (b+1)) (ZMod (b+1)) R :=
  fun i j => if i=0 then (if j=0 then 1 else 0) else
    (if j=i then 2 else 0) - (if j=i+1 then 1 else 0) - (if j=i+n then 1 else 0)

private theorem returnMatrix_mulVec {R : Type*} [CommRing R] {b n : ℕ}
    (v : ZMod (b+1) → R) (i : ZMod (b+1)) :
    (returnMatrix R b n *ᵥ v) i = if i=0 then v 0 else 2*v i-v (i+1)-v (i+n) := by
  by_cases h : i=0 <;> simp [returnMatrix,Matrix.mulVec,dotProduct,sub_mul,ite_mul,
    Finset.sum_sub_distrib,h]

/-- The integer matrix is nonsingular. A positive maximum of a kernel
vector would propagate around the cycle by unit steps to the anchored
row. Applying the same argument to its negative eliminates all entries. -/
theorem returnMatrix_det_ne_zero (b n : ℕ) : (returnMatrix ℤ b n).det≠0 := by
  intro hz
  obtain ⟨v,hne,hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  have bound (f : ZMod (b+1) → ℤ) (hf : returnMatrix ℤ b n *ᵥ f=0) :
      ∀ t, f t≤0 := by
    obtain ⟨j,_,hj⟩ := Finset.exists_max_image univ f univ_nonempty
    intro t
    by_contra! hp
    have hpos : 0<f j := hp.trans_le (hj t (mem_univ _))
    have step (i : ZMod (b+1)) (hi : f i=f j) : f (i+1)=f j ∧ i≠0 := by
      have hh := congrFun hf i
      rw [returnMatrix_mulVec] at hh
      change _=0 at hh
      have h1 := hj (i+1) (mem_univ _)
      have hN := hj (i+n) (mem_univ _)
      by_cases he : i=0
      · rw [ite_eq_left he,←he] at hh
        omega
      · rw [ite_eq_right he] at hh
        exact ⟨by omega,he⟩
    have H (k : ℕ) : f (j+k)=f j := by
      induction k with
      | zero => simp
      | succ k ih => simpa [Nat.cast_succ,←add_assoc] using (step (j+k) ih).1
    have h0 : f 0=f j := by simpa using H (-j).val
    exact (step 0 h0).2 rfl
  have H := bound v hv
  have K := bound (-v) (by rw [Matrix.mulVec_neg,hv,neg_zero])
  apply hne
  funext i
  have h1 := H i
  have h2 := K i
  change -(v i)≤0 at h2
  change v i=0
  omega

/-- The positive integer determinant for a chosen exponent step. -/
@[expose] def returnDeterminant : ℕ → ℕ → ℕ
  | 0, _ => 1
  | b+1, n => (returnMatrix ℤ b n).det.natAbs

theorem returnDeterminant_pos (β n : ℕ) : 0<returnDeterminant β n := by
  cases β with
  | zero => simp [returnDeterminant]
  | succ b => exact Int.natAbs_pos.mpr (returnMatrix_det_ne_zero b n)

/-- A genuinely nonconstant root modulo r forces r to divide the
integer determinant. -/
theorem prime_dvd_returnDeterminant {r β n : ℕ} (hr : r.Prime) (hb : 0<β)
    {x : ZMod r} (hx : x≠1) (hpow : x^β=1) (hret : x^n+x=2) :
    r ∣ returnDeterminant β n := by
  cases β with
  | zero => omega
  | succ b =>
    let : Fact r.Prime := ⟨hr⟩
    let v : ZMod (b+1) → ZMod r := fun i => x^i.val-1
    have period (z : ℕ) : x^(z%(b+1))=x^z := by
      conv_rhs => rw [←Nat.div_add_mod z (b+1),pow_add,pow_mul,hpow,one_pow,one_mul]
    have addPow (i : ZMod (b+1)) (k : ℕ) : x^((i+k).val) = x^i.val*x^k := by
      rw [ZMod.val_add,ZMod.val_natCast,Nat.add_mod_mod,period,pow_add]
    have hzero : v 0=0 := by simp [v]
    have hne : v≠0 := by
      intro hz
      have hh := congrFun hz (1 : ZMod (b+1))
      change x^(1 : ZMod (b+1)).val-1=0 at hh
      have h1 : x^(1 : ZMod (b+1)).val=x := by
        change x^(((1:ℕ):ZMod (b+1)).val)=x
        rw [ZMod.val_natCast,period,pow_one]
      exact hx (sub_eq_zero.mp (h1 ▸ hh))
    have hker : returnMatrix (ZMod r) b n *ᵥ v=0 := by
      funext i
      rw [returnMatrix_mulVec]
      by_cases hi : i=0
      · change (if i=0 then v 0 else _) = (0:ZMod r)
        simpa only [ite_eq_left hi] using hzero
      rw [ite_eq_right hi]
      have h1 := addPow i 1
      simp only [Nat.cast_one,pow_one] at h1
      change 2*(x^i.val-1)-(x^(i+1).val-1)-(x^(i+n).val-1)=0
      rw [h1,addPow]
      linear_combination -(x^i.val)*hret
    have hdet := Matrix.exists_mulVec_eq_zero_iff.mp ⟨v,hne,hker⟩
    let φ := Int.castRingHom (ZMod r)
    have hmap : φ.mapMatrix (returnMatrix ℤ b n)=returnMatrix (ZMod r) b n := by
      ext i j
      simp only [returnMatrix,RingHom.mapMatrix_apply,Matrix.map_apply]
      split_ifs <;> norm_num [φ]
    have hd : (((returnMatrix ℤ b n).det : ℤ) : ZMod r)=0 := by
      change φ _=0
      rw [RingHom.map_det,hmap,hdet]
    exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mp hd))

/-- A finite obstruction depending only on the return multiplicity.
The exponent's residue ranges over all possible cyclic steps. -/
@[expose] def returnMultiplicityModulus (β : ℕ) : ℕ :=
  ∏ n ∈ Finset.range β,returnDeterminant β n

theorem returnMultiplicityModulus_pos (β : ℕ) : 0<returnMultiplicityModulus β :=
  Finset.prod_pos fun n _ => returnDeterminant_pos β n

/-- Every cofactor prime in an even prime-power index either divides
u+1 or belongs to the finite set of prime divisors of the positive
integer attached solely to its own return multiplicity. -/
theorem even_index_source_finite_prime_divisors {q p s u r β : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hro : Odd r) (hrs : r ∣ s) (hb : 0<β)
    (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2)
    (hout : sigma 1 (r^(2*s.factorization r))=p^β) :
    r ∣ u+1 ∨ r ∣ returnMultiplicityModulus β := by
  obtain ⟨hpow,hrel,hone⟩ := even_index_source_root_equations hp hr hrs hσq hplus hout
  by_cases hx : (p:ZMod r)=1
  · left
    apply (Nat.coprime_two_right.mpr hro).dvd_of_dvd_mul_left
    simpa only [Nat.mul_add,Nat.mul_one] using hone hx
  · right
    have hper : (p:ZMod r)^((2*u+1)%β)=(p:ZMod r)^(2*u+1) := by
      conv_rhs => rw [←Nat.div_add_mod (2*u+1) β,pow_add,pow_mul,hpow,one_pow,one_mul]
    exact (prime_dvd_returnDeterminant hr hb hx hpow (hper ▸ hrel)).trans
      (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (Nat.mod_lt _ hb)))

end OddPerfect
