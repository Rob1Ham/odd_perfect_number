module

public import OddPerfect.OddPrimePowerBound
public import OddPerfect.ExceptionalNonresidues
public import Mathlib.Tactic.Primality.Lucas
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.LinearCombination

public section
namespace OddPerfect
open Finset ArithmeticFunction

/-- The three equations used to test an odd prime-power Euler index in
each residue field. -/
theorem odd_prime_power_index_three_equations {N q a m p j : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1)
    (hqm : ¬q∣m) (hform : N=q^a*m^2) (hp : p.Prime) (hj : Odd j)
    (hi : sigma 1 (m^2)/q^a=p^j) :
    let d := (a+1)/2
    ∃ w y, q+1=2*d*w^2 ∧ q^d+1=2*y^2 ∧ geometricBlock p (j+2)=q^d := by
  let d := (a+1)/2
  obtain ⟨ha,_,_,_,_,_⟩ := odd_prime_power_euler_index_constraints hN ho hq hq4 ha4 hqm hform hp hj hi
  obtain ⟨k,hk⟩ := hj
  have hshape : sigma 1 (m^2)/q^a=p*(p^k)^2 := by rw [hi,show j=k*2+1 by omega,pow_succ,pow_mul,mul_comm]
  obtain ⟨_,_,hq16,w,hw⟩ := prime_mul_square_index_forces_exceptional_prime_length
    hN ho hq hq4 ha4 ha hqm hform (Or.inr hp) hshape
  have hB : IsSquare ((q^d+1)/2) := Classical.byContradiction
    (fun h => euler_index_ne_prime_mul_square_of_second_block hN ho hq hq4 ha4 ha hqm hform h p (p^k) (Or.inr hp) hshape)
  obtain ⟨y,hy⟩ := hB
  have hpodd : q^d%2=1 := by simpa [Nat.ModEq] using (show q ≡ 1 [MOD 2] from (by change q%2=1; omega)).pow d
  obtain ⟨_,_,_,_,_,hret⟩ := odd_prime_power_euler_index_return hN ho hq hq4 ha4 hqm hform hp ⟨k,hk⟩ hi
  rw [sigma_one_apply_prime_pow hp] at hret
  exact ⟨w,y,by rw [mul_assoc,←hw]; omega,by change q^d+1=2*y^2; rw [pow_two]; omega,hret⟩

namespace IndexObstruction
open Mathlib.Tactic.Primality

/-- Geometric sum at a reduced base modulo a prime, using Fermat's
inverse when the reduced base differs from one. -/
@[expose] def geomResidue (r b n : ℕ) : ℕ :=
  if b=1 then n%r else
    ((powMod b n r+r-1)*powMod (b+r-1) (r-2) r)%r

private theorem cast_shift (z : ℕ) {r : ℕ} (hr : 0<r) :
    ((z+r-1:ℕ):ZMod r)=(z:ZMod r)-1 := by
  rw [Nat.cast_sub (by omega),Nat.cast_add,ZMod.natCast_self,add_zero,Nat.cast_one]

private theorem cast_powMod (b n r : ℕ) : (powMod b n r:ZMod r)=(b:ZMod r)^n := by
  rw [powMod_def,ZMod.natCast_mod,Nat.cast_pow]

private theorem geomResidue_correct {r b n : ℕ} (hr : r.Prime) :
    geomResidue r (b%r) n=geometricBlock b n%r := by
  let : Fact r.Prime := ⟨hr⟩
  have hcast : (geomResidue r (b%r) n:ZMod r)=((geometricBlock b n:ℕ):ZMod r) := by
    rw [geomResidue]
    by_cases hb : b%r=1
    · have hone : (b:ZMod r)=1 := by rw [←ZMod.natCast_mod b r,hb,Nat.cast_one]
      simp [hb,geometricBlock,hone,ZMod.natCast_mod]
    · have hh : (b:ZMod r)-1≠0 := by
        intro hz
        have hone := sub_eq_zero.mp hz
        have hval := congrArg ZMod.val hone
        rw [ZMod.val_natCast,ZMod.val_one'' hr.ne_one] at hval
        exact hb hval
      have hinv : ((b:ZMod r)-1)*((b:ZMod r)-1)^(r-2)=1 := by
        rw [←pow_succ',show r-2+1=r-1 by have := hr.two_le; omega,ZMod.pow_card_sub_one_eq_one hh]
      have hgeom : ((geometricBlock b n:ℕ):ZMod r)*((b:ZMod r)-1)=(b:ZMod r)^n-1 := by
        simpa [geometricBlock] using geom_sum_mul (b:ZMod r) n
      rw [ite_eq_right hb,ZMod.natCast_mod,Nat.cast_mul,cast_shift _ hr.pos,cast_powMod,ZMod.natCast_mod,
        cast_powMod,cast_shift _ hr.pos,ZMod.natCast_mod,←hgeom,mul_assoc,hinv,mul_one]
  have hmod := (ZMod.natCast_eq_natCast_iff _ _ r).mp hcast
  have hlt : geomResidue r (b%r) n<r := by
    unfold geomResidue
    split <;> exact Nat.mod_lt _ hr.pos
  exact (Nat.mod_eq_of_lt hlt).symm.trans hmod

/-- A residue-field certificate stores masks covering geometric sums and
twice-square-minus-one values. The Euler shape misses their intersection. -/
structure LocalTest where
  d : ℕ
  n : ℕ
  r : ℕ
  sums : ℕ
  squares : ℕ
  deriving DecidableEq, Repr

@[expose] def LocalTest.ok (c : LocalTest) : Bool :=
  (List.range c.r).all fun b =>
    let z := powMod (2*c.d*b^2+c.r-1) c.d c.r
    c.sums.testBit (geomResidue c.r b c.n) &&
      c.squares.testBit ((2*b^2+c.r-1)%c.r) && !(c.sums.testBit z && c.squares.testBit z)

theorem LocalTest.excludes (c : LocalTest) (hr : c.r.Prime) (hc : c.ok=true) {p q w y : ℕ}
    (hbase : q+1=2*c.d*w^2) (hsq : q^c.d+1=2*y^2) (hrep : geometricBlock p c.n=q^c.d) : False := by
  let v := q^c.d%c.r
  have check := List.all_eq_true.mp hc
  have hP := check (p%c.r) (List.mem_range.mpr (Nat.mod_lt _ hr.pos))
  have hY := check (y%c.r) (List.mem_range.mpr (Nat.mod_lt _ hr.pos))
  have hW := check (w%c.r) (List.mem_range.mpr (Nat.mod_lt _ hr.pos))
  simp only [Bool.and_eq_true,Bool.not_eq_true'] at hP hY hW
  have hgeom := hP.1.1
  rw [geomResidue_correct hr,hrep] at hgeom
  have hB : (2*(y%c.r)^2+c.r-1)%c.r = v := by
    change _ = q^c.d%c.r
    apply (ZMod.natCast_eq_natCast_iff _ _ c.r).mp
    rw [cast_shift _ hr.pos,Nat.cast_mul,Nat.cast_pow,ZMod.natCast_mod,Nat.cast_ofNat,Nat.cast_pow]
    have h := congrArg (fun u : ℕ => (u:ZMod c.r)) hsq
    push_cast at h
    linear_combination -h
  have hWv : powMod (2*c.d*(w%c.r)^2+c.r-1) c.d c.r=v := by
    rw [powMod_def]
    apply (ZMod.natCast_eq_natCast_iff _ _ c.r).mp
    rw [Nat.cast_pow,cast_shift _ hr.pos,Nat.cast_mul,Nat.cast_mul,Nat.cast_pow,
      ZMod.natCast_mod,Nat.cast_ofNat,Nat.cast_pow]
    apply congrArg (·^c.d)
    have h := congrArg (fun u : ℕ => (u:ZMod c.r)) hbase
    push_cast at h
    linear_combination -h
  have hs := hY.1.2
  rw [hB] at hs
  have hn := hW.2
  rw [hWv] at hn
  simp [hgeom,hs,v] at hn


/-- Every preliminary (prime length, prime half-length) pair below the
cutoff occurs among the supplied exact residue tests. -/
@[expose] def cover (K : ℕ) (tests : List LocalTest) : Bool :=
  (List.range K).all fun k =>
    let n := 16*k+17
    !(decide n.Prime) || (n+1).primeFactorsList.all fun d =>
      d%8 != 1 || tests.any fun c => c.d==d && c.n==n

/-- Residue obstructions and an independently checked list of possible
lengths give a lower bound without a size limit on any prime base. -/
theorem exponent_bound_of_cover {K : ℕ} {tests : List LocalTest}
    (hcover : cover K tests=true) (htests : ∀ c∈tests, c.r.Prime ∧ c.ok=true)
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
  have prop := htests c hc
  apply c.excludes prop.1 prop.2 (p:=p) (q:=q) (w:=w) (y:=y)
  · rw [he.1]; exact hbase
  · rw [he.1]; exact hsq
  · rw [he.1,he.2]; exact hrep

theorem component_index_ne_of_cover {K : ℕ} {tests : List LocalTest}
    (hcover : cover K tests=true) (htests : ∀ c∈tests, c.r.Prime ∧ c.ok=true)
    {N q a b i p j : ℕ} (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0<a)
    (hform : N=q^a*b) (hqb : ¬q∣b) (hl : sigma 1 b=q^a*i) (hr : sigma 1 (q^a)*i=2*b)
    (hp : p.Prime) (hj : Odd j) (hlim : j<16*K+15) : i≠p^j := by
  intro heq
  by_cases hsmall : j<191
  · exact component_index_ne_small_odd_prime_power hN ho hq ha hform hqb hl hr hp hj hsmall heq
  subst i
  have hp2 : p≠2 := by
    rintro rfl
    have h4 : 4∣2*b := hr ▸ (show 2^2∣2^j from pow_dvd_pow 2 (by omega)).trans (dvd_mul_left _ _)
    have hodd := (ho.of_dvd_nat (hform ▸ dvd_mul_left b _)).not_two_dvd_nat
    omega
  obtain ⟨m,hq4,ha4,hqm,rfl⟩ := euler_form_of_odd_component_index hN ho hq ha hform hqb hl hr (hp.odd_of_ne_two hp2).pow
  have hi : sigma 1 (m^2)/q^a=p^j := by rw [hl,Nat.mul_div_cancel_left _ (Nat.pow_pos hq.pos)]
  exact hlim.not_ge (exponent_bound_of_cover hcover htests hN ho hq hq4 ha4 hqm hform hp hj hi)

end IndexObstruction
end OddPerfect
