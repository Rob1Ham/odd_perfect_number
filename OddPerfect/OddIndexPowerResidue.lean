module

public import OddPerfect.OddIndexLocal
import all OddPerfect.OddIndexLocal
import Mathlib.FieldTheory.Finite.Basic

public section
namespace OddPerfect.IndexObstruction
open ArithmeticFunction Mathlib.Tactic.Primality

private theorem field_pow_residue {r b n e : ℕ} (hr : r.Prime) (hn : 0<n) (he : 0<e)
    (h : n ≡ e [MOD r-1]) : (b:ZMod r)^n=(b:ZMod r)^e := by
  let : Fact r.Prime := ⟨hr⟩
  by_cases hb : (b:ZMod r)=0
  · simp [hb,zero_pow hn.ne',zero_pow he.ne']
  exact pow_eq_pow_of_modEq h (ZMod.pow_card_sub_one_eq_one hb)

private theorem geometric_two_residues {r p n : ℕ} (hr : r.Prime) (hn : 0<n)
    (h : n ≡ 1 [MOD r-1]) :
    (geometricBlock p n:ZMod r)=1 ∨ (geometricBlock p n:ZMod r)=n := by
  let : Fact r.Prime := ⟨hr⟩
  by_cases hp : (p:ZMod r)=1
  · right; simp [geometricBlock,hp]
  left
  apply mul_right_cancel₀ (sub_ne_zero.mpr hp)
  have hpow := field_pow_residue (b:=p) hr hn (by decide : 0<1) h
  simpa [geometricBlock,hpow] using geom_sum_mul (p:ZMod r) n

@[expose] def nonSquareTest (r z : ℕ) : Bool :=
  z%r != 0 && powMod z ((r-1)/2) r != 1

private theorem nonSquareTest_sound {r z : ℕ} (hr : r.Prime) (ho : Odd r)
    (h : nonSquareTest r z=true) : ¬IsSquare (z:ZMod r) := by
  let : Fact r.Prime := ⟨hr⟩
  obtain ⟨hz,hn⟩ := (show z%r≠0 ∧ powMod z ((r-1)/2) r≠1 by simpa [nonSquareTest] using h)
  rintro ⟨v,hv⟩
  have hv0 : v≠0 := by
    intro he
    rw [he,mul_zero] at hv
    exact hz (Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp hv))
  have h2 : 2*((r-1)/2)=r-1 := by have := Nat.odd_iff.mp ho; omega
  have he : (z:ZMod r)^((r-1)/2)=1 := by
    rw [hv,←pow_two,←pow_mul,h2,ZMod.pow_card_sub_one_eq_one hv0]
  have H := congrArg ZMod.val he
  rw [←Nat.cast_pow,ZMod.val_natCast,ZMod.val_one'' hr.ne_one] at H
  exact hn (by rwa [powMod_def])

@[expose] def twoValueTest (d n r inv : ℕ) : Bool :=
  let misses (z : ℕ) := nonSquareTest r (2*(z+1)) ||
    nonSquareTest r (2*d*(powMod z inv r+1))
  decide (2<r ∧ 0<n ∧ 0<d ∧ 0 < inv ∧ n%(r-1)=1 ∧ d*inv%(r-1)=1) &&
    misses 1 && misses (n%r)

/-- If n is one modulo r−1 the geometric sum has only two residues.
Inverting d on the field multiplicative group tests both possible
values against the two square equations. -/
theorem twoValueTest_excludes {d n r inv : ℕ} (hr : r.Prime)
    (ht : twoValueTest d n r inv=true) {p q w y : ℕ}
    (hbase : q+1=2*d*w^2) (hsq : q^d+1=2*y^2) (hrep : geometricBlock p n=q^d) : False := by
  let : Fact r.Prime := ⟨hr⟩
  have H := ht
  simp only [twoValueTest,Bool.and_eq_true,decide_eq_true_eq] at H
  obtain ⟨⟨⟨hr2,hn,hd,hi,h1,h2⟩,hfirst⟩,hsecond⟩ := H
  have ho := hr.odd_of_ne_two (by omega)
  have hrem : 1%(r-1)=1 := Nat.mod_eq_of_lt (by omega)
  have hG := geometric_two_residues (p:=p) hr hn (h1.trans hrem.symm)
  rw [hrep,Nat.cast_pow] at hG
  have hqin : ((q:ZMod r)^d)^inv=q := by
    rw [←pow_mul]
    simpa using field_pow_residue (b:=q) hr (Nat.mul_pos hd hi) (by decide : 0<1) (h2.trans hrem.symm)
  have hy' := congrArg (fun v : ℕ => (v:ZMod r)) hsq
  have hw' := congrArg (fun v : ℕ => (v:ZMod r)) hbase
  push_cast at hy' hw'
  have contradiction (z : ℕ) (hz : (q:ZMod r)^d=z)
      (bad : (nonSquareTest r (2*(z+1)) || nonSquareTest r (2*d*(powMod z inv r+1)))=true) : False := by
    rcases Bool.or_eq_true_iff.mp bad with hy | hw
    · apply nonSquareTest_sound hr ho hy
      refine ⟨2*y,?_⟩
      push_cast
      rw [←hz,hy']
      ring
    · apply nonSquareTest_sound hr ho hw
      refine ⟨2*d*w,?_⟩
      push_cast
      rw [cast_powMod,←hz,hqin,hw']
      ring
  rcases hG with h|h
  · exact contradiction 1 (by simpa using h) hfirst
  · exact contradiction (n%r) (by simpa only [ZMod.natCast_mod] using h) hsecond

/-- Any sound test on each covered pair of lengths yields the exponent
bound, independent of the choice of residue test for that pair. -/
theorem exponent_bound_of_pair_exclusions {K : ℕ} {tests : List LocalTest}
    (hcover : cover K tests=true)
    (htests : ∀ c∈tests, ∀ {p q w y : ℕ}, q+1=2*c.d*w^2 → q^c.d+1=2*y^2 →
      geometricBlock p c.n=q^c.d → False)
    {N q a m p j : ℕ} (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1)
    (hqm : ¬q∣m) (hform : N=q^a*m^2) (hp : p.Prime) (hj : Odd j)
    (hi : sigma 1 (m^2)/q^a=p^j) : 16*K+15≤j := by
  obtain ⟨_,_,_,hjp,h16,_⟩ := odd_prime_power_euler_index_constraints hN ho hq hq4 ha4 hqm hform hp hj hi
  let d := (a+1)/2
  obtain ⟨hd,hd8,hdj,_,_,_⟩ := odd_prime_power_euler_index_return hN ho hq hq4 ha4 hqm hform hp hj hi
  change d.Prime at hd
  change d%8=1 at hd8
  change d∣j+3 at hdj
  by_contra! hlt
  let k := j/16
  have hk : k<K := by dsimp [k]; omega
  have hn : 16*k+17=j+2 := by dsimp [k]; omega
  have hc := List.all_eq_true.mp hcover k (List.mem_range.mpr hk)
  dsimp only at hc
  rw [hn] at hc
  simp only [decide_eq_true hjp,Bool.not_true,Bool.false_or] at hc
  have hmem := Nat.mem_primeFactorsList'.mpr (show d.Prime ∧ d∣(j+2)+1 ∧ (j+2)+1≠0 from ⟨hd,hdj,by omega⟩)
  have ht := List.all_eq_true.mp hc d hmem
  rw [hd8] at ht
  change (tests.any fun c => c.d==d && c.n==(j+2))=true at ht
  obtain ⟨c,hc,he⟩ := List.any_eq_true.mp ht
  simp only [Bool.and_eq_true,beq_iff_eq] at he
  obtain ⟨w,y,hbase,hsq,hrep⟩ := odd_prime_power_index_three_equations hN ho hq hq4 ha4 hqm hform hp hj hi
  apply htests c hc (p:=p) (q:=q) (w:=w) (y:=y)
  · rw [he.1]; exact hbase
  · rw [he.1]; exact hsq
  · rw [he.1,he.2]; exact hrep

end OddPerfect.IndexObstruction
