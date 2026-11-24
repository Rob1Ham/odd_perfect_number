module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! An affine elliptic primality certificate with a conservative point-count bound. -/
public section

namespace OddPerfect.EllipticPrime
open WeierstrassCurve.Affine

@[expose] def short {R : Type*} [CommRing R] (a b : R) : WeierstrassCurve.Affine R := ⟨0,0,0,a,b⟩
abbrev Raw (R : Type*) := Option (R × R)

@[expose] def finish {R : Type*} [CommRing R] [Inv R] [DecidableEq R]
    (a b x z y numerator denominator : R) : Option (Raw R) :=
  if denominator * denominator⁻¹ = 1 then
    let slope := numerator * denominator⁻¹
    some (some ((short a b).addX x z slope, (short a b).addY x z y slope))
  else none

/-- An outer `none` means that the attempted affine inverse failed its check.
An inner `none` represents the group identity. -/
@[expose] def add {R : Type*} [CommRing R] [Inv R] [DecidableEq R]
    (a b : R) : Raw R → Raw R → Option (Raw R)
  | none, Q => some Q
  | P, none => some P
  | some (x,y), some (z,w) =>
    if x=z then
      if y = -w then some none else
        if y=w then finish a b x x y (3*x^2+a) (2*y) else none
    else finish a b x z y (y-w) (x-z)

@[expose] def scale {R : Type*} [CommRing R] [Inv R] [DecidableEq R]
    (a b : R) (P : Raw R) (k : ℕ) : Option (Raw R) :=
  if k=0 then some none else do
    let H ← scale a b P (k/2)
    let D ← add a b H H
    if k%2=0 then some D else add a b D P
termination_by k
decreasing_by omega

private def Represents {R K : Type*} [CommRing R] [Field K]
    (f : R →+* K) (a b : R) (P : Raw R) (T : (short (f a) (f b)).Point) : Prop :=
  match P with
  | none => T=0
  | some (x,y) => ∃ h, T=.some (f x) (f y) h

private theorem map_inverse_checked {R K : Type*} [CommRing R] [Inv R] [Field K]
    (f : R →+* K) {d : R} (h : d*d⁻¹=1) : f d ≠ 0 ∧ f d⁻¹=(f d)⁻¹ := by
  have hh : f d * f d⁻¹=1 := by rw [← map_mul,h,map_one]
  have hn : f d≠0 := fun hz => by simp [hz] at hh
  exact ⟨hn, (mul_left_cancel₀ hn) (hh.trans (mul_inv_cancel₀ hn).symm)⟩

private theorem finish_maps {R K : Type*} [CommRing R] [Inv R] [DecidableEq R] [Field K]
    (f : R →+* K) (a b x z y n d : R) (Q : Raw R) (ℓ : K)
    (h : finish a b x z y n d = some Q)
    (hs : f d≠0 → f n / f d = ℓ) :
    let W := short (f a) (f b)
    ∀ hh : W.Nonsingular (W.addX (f x) (f z) ℓ) (W.addY (f x) (f z) (f y) ℓ),
      Represents f a b Q (.some _ _ hh) := by
  unfold finish at h
  split at h
  next hinv =>
    obtain rfl := Option.some.inj h
    obtain ⟨hne,hi⟩ := map_inverse_checked f hinv
    have hsl : f (n*d⁻¹)=ℓ := by rw [map_mul,hi,←div_eq_mul_inv,hs hne]
    dsimp only
    intro hh
    dsimp only [Represents]
    have hx : f ((short a b).addX x z (n*d⁻¹)) = (short (f a) (f b)).addX (f x) (f z) ℓ := by
      simp [addX,short,hsl]
    have hy : f ((short a b).addY x z y (n*d⁻¹)) = (short (f a) (f b)).addY (f x) (f z) (f y) ℓ := by
      simp [addY,negY,negAddY,addX,short,hsl]
    rw [hx,hy]
    exact ⟨hh,rfl⟩
  next => contradiction

private theorem add_maps {R K : Type*} [CommRing R] [Inv R] [DecidableEq R] [Field K] [DecidableEq K]
    (f : R →+* K) (a b : R) {P Q S : Raw R} {T U : (short (f a) (f b)).Point}
    (hP : Represents f a b P T) (hQ : Represents f a b Q U) (h : add a b P Q = some S) :
    Represents f a b S (T+U) := by
  let W := short (f a) (f b)
  rcases P with _ | ⟨x,y⟩
  · cases h
    simpa [show T=0 from hP] using hQ
  rcases Q with _ | ⟨z,w⟩
  · cases h
    simpa [show U=0 from hQ] using hP
  obtain ⟨hp,rfl⟩ := hP
  obtain ⟨hq,rfl⟩ := hQ
  dsimp only [add] at h
  split at h
  next hx =>
    subst z
    split at h
    next hy =>
      obtain rfl := Option.some.inj h
      apply Point.add_of_Y_eq rfl
      simp [hy,short,negY]
    next _ =>
      split at h
      next hy =>
        subst w
        have hun : (2*y)*(2*y)⁻¹=1 := by
          by_contra hn
          simp [finish,hn] at h
        have hd := (map_inverse_checked f hun).1
        have hneg : f y ≠ W.negY (f x) (f y) := by
          simp [W,short,negY]
          intro he
          apply hd
          rw [map_mul,map_ofNat]
          linear_combination he
        rw [Point.add_self_of_Y_ne hneg]
        apply finish_maps f a b _ _ _ _ _ _ _ h
        intro _
        rw [W.slope_of_Y_ne rfl hneg]
        simp [W,short,negY,two_mul,map_ofNat f 3]
      next => contradiction
  next _ =>
    have hun : (x-z)*(x-z)⁻¹=1 := by
      by_contra hn
      simp [finish,hn] at h
    have hd := (map_inverse_checked f hun).1
    have hx : f x ≠ f z := sub_ne_zero.mp (by simpa only [map_sub] using hd)
    rw [Point.add_of_X_ne hx]
    apply finish_maps f a b _ _ _ _ _ _ _ h
    intro _
    rw [W.slope_of_X_ne hx]
    simp

private theorem scale_maps {R K : Type*} [CommRing R] [Inv R] [DecidableEq R] [Field K] [DecidableEq K]
    (f : R →+* K) (a b : R) (P : Raw R) (T : (short (f a) (f b)).Point)
    (hP : Represents f a b P T) (k : ℕ) {Q : Raw R} (h : scale a b P k = some Q) :
    Represents f a b Q (k • T) := by
  induction k using Nat.strong_induction_on generalizing Q with
  | ind k ih =>
    rw [scale] at h
    split at h
    next hz => subst k; cases h; simp [Represents]
    next hz =>
      cases hh : scale a b P (k/2) with
      | none => simp [hh] at h
      | some H =>
        have hH := ih (k/2) (by omega) hh
        cases hd : add a b H H with
        | none => simp [hh,hd] at h
        | some D =>
          have hD := add_maps f a b hH hH hd
          by_cases he : k%2=0
          · have hresult : D=Q := by simpa [hh,hd,he] using h
            subst Q
            have hk : k=k/2+k/2 := by omega
            rw [show k • T = (k/2)•T+(k/2)•T by conv_lhs => rw [hk,add_nsmul]]
            exact hD
          · have hstep : add a b D P = some Q := by simpa [hh,hd,he] using h
            have hk : k=k/2+k/2+1 := by omega
            rw [show k • T = ((k/2)•T+(k/2)•T)+T by conv_lhs => rw [hk,add_nsmul,add_nsmul,one_nsmul]]
            exact add_maps f a b hD hP hstep

/-- Use the supplied inverse for this affine operation. `finish` verifies its product
with the denominator before accepting the result. -/
@[expose] def addUsing {R : Type*} [CommRing R] [DecidableEq R] (inverse a b : R)
    (P Q : Raw R) : Option (Raw R) :=
  letI : Inv R := ⟨fun _ => inverse⟩
  add a b P Q

private theorem addUsing_maps {R K : Type*} [CommRing R] [DecidableEq R] [Field K] [DecidableEq K]
    (f : R →+* K) (v a b : R) {P Q S : Raw R} {T U : (short (f a) (f b)).Point}
    (hP : Represents f a b P T) (hQ : Represents f a b Q U) (h : addUsing v a b P Q = some S) :
    Represents f a b S (T+U) := by
  let : Inv R := ⟨fun _ => v⟩
  exact add_maps f a b hP hQ h

/-- A binary scalar ladder with independently verified affine inverses for the doubling
and optional addition at each bit. The transcript starts at the low bit. -/
@[expose] def scaleTrace {n : ℕ} (a b : ZMod n) (P : Raw (ZMod n)) :
    ℕ → List (ℕ × ℕ) → Option (Raw (ZMod n))
  | k, [] => if k=0 then some none else none
  | k, (dbl,join)::xs => do
    let H ← scaleTrace a b P (k/2) xs
    let D ← addUsing (dbl : ZMod n) a b H H
    if k%2=0 then some D else addUsing (join : ZMod n) a b D P

private theorem scaleTrace_maps {n : ℕ} {K : Type*} [Field K] [DecidableEq K]
    (f : ZMod n →+* K) (a b : ZMod n) (P : Raw (ZMod n)) (T : (short (f a) (f b)).Point)
    (hP : Represents f a b P T) (k : ℕ) (xs : List (ℕ × ℕ)) {Q : Raw (ZMod n)}
    (h : scaleTrace a b P k xs = some Q) : Represents f a b Q (k • T) := by
  induction xs generalizing k Q with
  | nil =>
    simp only [scaleTrace] at h
    split at h
    next h0 => subst k; cases h; simp [Represents]
    next => contradiction
  | cons head tail ih =>
    rcases head with ⟨dbl,join⟩
    simp only [scaleTrace] at h
    cases hh : scaleTrace a b P (k/2) tail with
    | none => simp [hh] at h
    | some H =>
      have hH := ih (k/2) hh
      cases hd : addUsing (dbl : ZMod n) a b H H with
      | none => simp [hh,hd] at h
      | some D =>
        have hD := addUsing_maps f _ a b hH hH hd
        by_cases he : k%2=0
        · have hresult : D=Q := by simpa [hh,hd,he] using h
          subst Q
          have hk : k=k/2+k/2 := by omega
          rw [show k • T = (k/2)•T+(k/2)•T by conv_lhs => rw [hk,add_nsmul]]
          exact hD
        · have hstep : addUsing (join : ZMod n) a b D P = some Q := by simpa [hh,hd,he] using h
          have hk : k=k/2+k/2+1 := by omega
          rw [show k • T = ((k/2)•T+(k/2)•T)+T by conv_lhs => rw [hk,add_nsmul,add_nsmul,one_nsmul]]
          exact addUsing_maps f _ a b hD hP hstep

private def encode {r : ℕ} [Fact r.Prime] (a b : ZMod r) :
    (short a b).Point → Option (ZMod r × Bool)
  | .zero => none
  | .some x y _ => some (x,decide (y.val ≤ (-y).val))

private theorem encode_injective {r : ℕ} [Fact r.Prime] (a b : ZMod r) :
    Function.Injective (encode a b) := by
  rintro (_ | ⟨x,y,h⟩) (_ | ⟨z,w,k⟩) he
  · rfl
  · contradiction
  · contradiction
  dsimp [encode] at he
  obtain ⟨rfl,hsign⟩ := Prod.mk.inj (Option.some.inj he)
  have h₁ := ((short a b).equation_iff _ _).mp h.1
  have h₂ := ((short a b).equation_iff _ _).mp k.1
  simp [short] at h₁ h₂
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (h₁.trans h₂.symm) with hy | hy
  · subst w; rfl
  · have hw : w= -y := by rw [hy,neg_neg]
    subst w
    simp only [neg_neg] at hsign
    have hle : y.val ≤ (-y).val ↔ (-y).val ≤ y.val := by
      exact ⟨fun h => of_decide_eq_true (hsign.symm.trans (decide_eq_true h)),
        fun h => of_decide_eq_true (hsign.trans (decide_eq_true h))⟩
    have eqv : y.val=(-y).val := by omega
    have heq : y= -y := ZMod.val_injective _ eqv
    congr 1

private theorem order_bound {r : ℕ} [Fact r.Prime] (a b : ZMod r) (P : (short a b).Point) :
    addOrderOf P ≤ 2*r+1 := by
  let : Finite (short a b).Point := Finite.of_injective _ (encode_injective a b)
  let := Fintype.ofFinite (short a b).Point
  have hc := Fintype.card_le_of_injective _ (encode_injective a b)
  have hh := addOrderOf_le_card (x := P)
  rw [Nat.card_eq_fintype_card] at hh
  simp at hc
  omega

/-- The claimed elliptic point has prime order greater than the maximum number
of points over a field with at most √n elements. -/
@[expose] def ellipticCheck (n a b x y q : ℕ) : Bool :=
  let A : ZMod n := a
  let B : ZMod n := b
  let X : ZMod n := x
  let Y : ZMod n := y
  decide (1<n ∧ 2*n.sqrt+1<q ∧ Y^2=X^3+A*X+B ∧ (2*Y)*(2*Y)⁻¹=1 ∧
    scale A B (some (X,Y)) q = some none)

theorem prime_of_ellipticCheck {n a b x y q : ℕ} (hq : q.Prime)
    (hc : ellipticCheck n a b x y q = true) : n.Prime := by
  let A : ZMod n := a
  let B : ZMod n := b
  let X : ZMod n := x
  let Y : ZMod n := y
  have ⟨hn,hsize,hcurve,hunit,hscale⟩ : 1<n ∧ 2*n.sqrt+1<q ∧ Y^2=X^3+A*X+B ∧
      (2*Y)*(2*Y)⁻¹=1 ∧ scale A B (some (X,Y)) q = some none := of_decide_eq_true hc
  by_contra hcomp
  let r := n.minFac
  let : Fact r.Prime := ⟨Nat.minFac_prime (by omega)⟩
  let : Fact q.Prime := ⟨hq⟩
  let f : ZMod n →+* ZMod r := ZMod.castHom (Nat.minFac_dvd n) _
  let W := short (f A) (f B)
  have hpoint : W.Nonsingular (f X) (f Y) := by
    rw [W.nonsingular_iff', W.equation_iff]
    refine ⟨?_,Or.inr ?_⟩
    · simpa [W,short] using congrArg f hcurve
    · have htwo : f 2=(2 : ZMod r) := map_ofNat f 2
      simpa [W,short,htwo] using (map_inverse_checked f hunit).1
  let P : W.Point := .some _ _ hpoint
  have hstart : Represents f A B (some (X,Y)) P := ⟨hpoint,rfl⟩
  have hzero : q • P = 0 := scale_maps f A B _ _ hstart q hscale
  have hpord : addOrderOf P = q := addOrderOf_eq_prime hzero (by intro h; contradiction)
  have hle := order_bound (f A) (f B) P
  rw [hpord] at hle
  have hr : r≤n.sqrt := Nat.le_sqrt.mpr (by simpa [r,sq] using Nat.minFac_sq_le_self (by omega : 0<n) hcomp)
  omega

/-- An elliptic certificate with checked scalar-multiplication transcript. -/
@[expose] def ellipticTraceCheck (n a b x y q : ℕ) (trace : List (ℕ × ℕ)) : Bool :=
  let A : ZMod n := a
  let B : ZMod n := b
  let X : ZMod n := x
  let Y : ZMod n := y
  decide (1<n ∧ 2*n.sqrt+1<q ∧ Y^2=X^3+A*X+B ∧ (2*Y)*(2*Y)⁻¹=1 ∧
    scaleTrace A B (some (X,Y)) q trace = some none)

theorem prime_of_ellipticTraceCheck {n a b x y q : ℕ} {trace : List (ℕ × ℕ)} (hq : q.Prime)
    (hc : ellipticTraceCheck n a b x y q trace = true) : n.Prime := by
  let A : ZMod n := a
  let B : ZMod n := b
  let X : ZMod n := x
  let Y : ZMod n := y
  have ⟨hn,hsize,hcurve,hunit,hscale⟩ : 1<n ∧ 2*n.sqrt+1<q ∧ Y^2=X^3+A*X+B ∧
      (2*Y)*(2*Y)⁻¹=1 ∧ scaleTrace A B (some (X,Y)) q trace = some none := of_decide_eq_true hc
  by_contra hcomp
  let r := n.minFac
  let : Fact r.Prime := ⟨Nat.minFac_prime (by omega)⟩
  let : Fact q.Prime := ⟨hq⟩
  let f : ZMod n →+* ZMod r := ZMod.castHom (Nat.minFac_dvd n) _
  let W := short (f A) (f B)
  have hpoint : W.Nonsingular (f X) (f Y) := by
    rw [W.nonsingular_iff', W.equation_iff]
    refine ⟨?_,Or.inr ?_⟩
    · simpa [W,short] using congrArg f hcurve
    · have htwo : f 2=(2 : ZMod r) := map_ofNat f 2
      simpa [W,short,htwo] using (map_inverse_checked f hunit).1
  let P : W.Point := .some _ _ hpoint
  have hstart : Represents f A B (some (X,Y)) P := ⟨hpoint,rfl⟩
  have hzero : q • P = 0 := scaleTrace_maps f A B _ _ hstart q trace hscale
  have hpord : addOrderOf P = q := addOrderOf_eq_prime hzero (by intro h; contradiction)
  have hle := order_bound (f A) (f B) P
  rw [hpord] at hle
  have hr : r≤n.sqrt := Nat.le_sqrt.mpr (by simpa [r,sq] using Nat.minFac_sq_le_self (by omega : 0<n) hcomp)
  omega

end OddPerfect.EllipticPrime
