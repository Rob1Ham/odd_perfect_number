module

public import OddPerfect.PositiveHalfReturn
public import OddPerfect.OddIndexPowerResidue
import all OddPerfect.OddIndexPowerResidue
import all OddPerfect.OddIndexLocal
import Mathlib.FieldTheory.Finite.Basic

public section
namespace OddPerfect.IndexObstruction
open Mathlib.Tactic.Primality ArithmeticFunction

@[expose] def missesBlockSquares (p d r b : ℕ) : Bool :=
  nonSquareTest r (2*d*(b+1)) || nonSquareTest r (2*(powMod b d r+1)) ||
    nonSquareTest r (p*geomResidue r b d)

/-- The first, second and fourth block equations share one reduced
Euler base. All three indicated quantities must be squares in its field. -/
theorem block_squares_possible {p q d w y v r : ℕ} (hr : r.Prime) (hro : Odd r)
    (hw : q+1=2*d*w^2) (hy : q^d+1=2*y^2) (hv : geometricBlock q d=p*v^2) :
    missesBlockSquares p d r (q%r)=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [missesBlockSquares,Bool.or_eq_true] at h
  have hw' := congrArg (fun z : ℕ => (z:ZMod r)) hw
  have hy' := congrArg (fun z : ℕ => (z:ZMod r)) hy
  have hv' := congrArg (fun z : ℕ => (z:ZMod r)) hv
  push_cast at hw' hy' hv'
  rcases h with (h|h)|h
  · apply nonSquareTest_sound hr hro h
    refine ⟨2*d*w,?_⟩
    push_cast
    rw [ZMod.natCast_mod,hw']
    ring
  · apply nonSquareTest_sound hr hro h
    refine ⟨2*y,?_⟩
    push_cast
    rw [cast_powMod,ZMod.natCast_mod,hy']
    ring
  · apply nonSquareTest_sound hr hro h
    refine ⟨(p:ZMod r)*v,?_⟩
    rw [geomResidue_correct hr,Nat.cast_mul,ZMod.natCast_mod,hv']
    ring

/-- The empty-residue test for a prime-times-square index uses only
the three equations common to arbitrary such indices. -/
@[expose] def squarefreeBaseTest (p d r : ℕ) : Bool :=
  (List.range r).all fun b => b==0 || missesBlockSquares p d r b

theorem squarefreeBaseTest_excludes {p q d w y v r : ℕ} (hr : r.Prime) (hro : Odd r)
    (hq : q.Prime) (hrq : r<q) (ht : squarefreeBaseTest p d r=true)
    (hw : q+1=2*d*w^2) (hy : q^d+1=2*y^2) (hv : geometricBlock q d=p*v^2) : False := by
  have hq0 : q%r≠0 := fun h => hrq.ne ((Nat.prime_dvd_prime_iff_eq hr hq).mp (Nat.dvd_of_mod_eq_zero h))
  have hc := List.all_eq_true.mp ht (q%r) (List.mem_range.mpr (Nat.mod_lt _ hr.pos))
  simp [hq0,block_squares_possible hr hro hw hy hv] at hc

@[expose] def fixedBaseTest (p d r : ℕ) : Bool :=
  (List.range r).all fun b => b==0 || missesBlockSquares p d r b ||
    (p%r != 1 && (List.range (r-1)).all fun k => geomResidue r (p%r) (16*k+1)  !=  powMod b d r)

/-- For an odd prime-power index the exponent length is one modulo
sixteen. At a base different from one, each residue class of the
quotient modulo r−1 determines the geometric sum. -/
theorem fixedBaseTest_excludes {p q n d w y v r : ℕ} (hr : r.Prime) (hro : Odd r)
    (hq : q.Prime) (hrq : r<q) (hn : 0<n) (h16 : 16∣n-1) (ht : fixedBaseTest p d r=true)
    (hw : q+1=2*d*w^2) (hy : q^d+1=2*y^2) (hv : geometricBlock q d=p*v^2)
    (hrep : geometricBlock p n=q^d) : False := by
  let : Fact r.Prime := ⟨hr⟩
  have hc := List.all_eq_true.mp ht (q%r) (List.mem_range.mpr (Nat.mod_lt _ hr.pos))
  have hq0 : q%r≠0 := fun h => hrq.ne ((Nat.prime_dvd_prime_iff_eq hr hq).mp (Nat.dvd_of_mod_eq_zero h))
  have hp' : p%r≠1 ∧ ((List.range (r-1)).all fun k => geomResidue r (p%r) (16*k+1)  !=  powMod (q%r) d r)=true := by
    simpa [hq0,block_squares_possible hr hro hw hy hv] using hc
  obtain ⟨k,hk⟩ := h16
  let k' := k%(r-1)
  have hk' : k'<r-1 := Nat.mod_lt _ (by have := hr.one_lt; omega)
  have hbad := List.all_eq_true.mp hp'.2 k' (List.mem_range.mpr hk')
  simp only [bne_iff_ne] at hbad
  apply hbad
  rw [geomResidue_correct hr,powMod_def,←Nat.pow_mod]
  have hcast : (geometricBlock p (16*k'+1):ZMod r)=(geometricBlock p n:ZMod r) := by
    have hp1 : (p:ZMod r)≠1 := by
      intro h
      have H := congrArg ZMod.val h
      exact hp'.1 (by simpa only [ZMod.val_natCast,ZMod.val_one'' hr.ne_one] using H)
    have hn' : n=16*k+1 := by omega
    have hpow := field_pow_residue (b:=p) hr (by omega : 0<16*k'+1) hn
      (hn' ▸ ((Nat.mod_modEq k (r-1)).mul_left 16).add_right 1)
    apply mul_right_cancel₀ (sub_ne_zero.mpr hp1)
    simp only [geometricBlock,Nat.cast_sum,Nat.cast_pow,geom_sum_mul,hpow]
  rw [hrep] at hcast
  exact (ZMod.natCast_eq_natCast_iff _ _ r).mp hcast

end OddPerfect.IndexObstruction
