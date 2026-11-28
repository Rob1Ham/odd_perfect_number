module

public import OddPerfect.Spoof
public import OddPerfect.NearPerfect
public import OddPerfect.Cuts
public import OddPerfect.SpoofAbundancy
public import OddPerfect.AbundancyLimit
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- Tóth's deficient cofactors, retaining the integer x in
2n/σ(n) − 1 = 1/x. Clearing denominators also covers the even-x cases. -/
@[expose] def TothPair (n x : ℕ) : Prop :=
  Odd n ∧ 0<x ∧ sigma 1 n*(x+1)=2*(n*x)

theorem tothPair_iff_reciprocal {n x : ℕ} (hn : Odd n) (hx : 0<x) :
    TothPair n x ↔ (2*(n:ℚ)/(sigma 1 n:ℚ))-1=1/(x:ℚ) := by
  have hs : (0:ℚ)<sigma 1 n := by exact_mod_cast sigma_pos 1 n hn.pos.ne'
  have hp : (0:ℚ)<x := by exact_mod_cast hx
  constructor
  · intro h
    have hq : (sigma 1 n:ℚ)*((x:ℚ)+1)=2*((n:ℚ)*x) := by exact_mod_cast h.2.2
    apply (eq_div_iff hp.ne').mpr
    field_simp
    linarith
  · intro he
    refine ⟨hn,hx,?_⟩
    have hq : (sigma 1 n:ℚ)*((x:ℚ)+1)=2*((n:ℚ)*x) := by
      field_simp at he
      linarith
    exact_mod_cast hq

/-- For an odd multiplier the cofactor is a square and the multiplier
is one modulo four. No coprimality or primality hypothesis is needed. -/
theorem toth_odd_cofactor_square {n x : ℕ} (h : TothPair n x) (hx : Odd x) :
    IsSquare n ∧ x%4=1 := by
  have hn := Nat.odd_iff.mp h.1
  have hxo := Nat.odd_iff.mp hx
  have hres := congrArg (· % 4) h.2.2
  rw [Nat.mul_mod,Nat.mul_mod 2 (n*x),Nat.mul_mod n x,Nat.add_mod] at hres
  have hnm := Nat.mod_lt n (by decide : 0<4)
  have hxm := Nat.mod_lt x (by decide : 0<4)
  have hsm := Nat.mod_lt (sigma 1 n) (by decide : 0<4)
  have hnum : ∀ i j k : Fin 4, i.val%2=1 → j.val%2=1 →
      (k.val*((j.val+1%4)%4))%4=(2%4*((i.val*j.val)%4))%4 → k.val%2=1 ∧ j.val=1 := by decide
  have r := hnum ⟨n%4,hnm⟩ ⟨x%4,hxm⟩ ⟨sigma 1 n%4,hsm⟩ (by dsimp; omega) (by dsimp; omega) hres
  exact ⟨(odd_sigma_iff_square_of_odd h.1).mp (Nat.odd_iff.mpr (by dsimp at r; omega)),r.2⟩

/-- For every odd candidate multiplier with x>1, the square root range
and prime bounds can be tested using ordinary geometric divisor sums. -/
theorem toth_odd_square_root {n x B : ℕ} (h : TothPair n x) (hx : Odd x) (h1 : 1<x)
    (hB : n≤B^2) : ∃ m, Odd m ∧ m≤B ∧ n=m^2 ∧ 5≤x ∧ x%4=1 := by
  obtain ⟨⟨m,hm⟩,hr⟩ := toth_odd_cofactor_square h hx
  have hsq : n=m^2 := by simpa [pow_two] using hm
  have ho : Odd m := (show Odd n from h.1).of_dvd_nat (hsq ▸ dvd_pow_self _ (by decide : 2≠0))
  refine ⟨m,ho,?_,hsq,by omega,hr⟩
  by_contra! hl
  exact hB.not_gt (hsq ▸ Nat.pow_lt_pow_left hl (by decide : 2≠0))

/-- Tóth's odd-multiplier set contains the (square cofactor, Euler prime)
pair of every odd perfect number whose special exponent is one. -/
theorem tothPair_of_linear_euler {n p : ℕ} (ho : Odd n) (hp : p.Prime) (hc : n.Coprime p)
    (hN : (n*p).Perfect) : TothPair n p := by
  refine ⟨ho,hp.pos,?_⟩
  have h := (Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN
  have hsp : sigma 1 p = p+1 := by
    rw [sigma_one_apply,Nat.sum_divisors_eq_sum_properDivisors_add_self,
      Nat.sum_properDivisors_eq_one_iff_prime.mpr hp,Nat.add_comm]
  rwa [← sigma_one_apply,isMultiplicative_sigma.map_mul_of_coprime hc,hsp] at h

/-- Primality is the precise condition on a coprime nontrivial multiplier
that turns a cleared balance equation into true perfection. -/
theorem toth_coprime_perfect_iff_prime {n x : ℕ} (h : TothPair n x) (hx : 1<x) (hc : n.Coprime x) :
    (n*x).Perfect ↔ x.Prime := perfect_iff_prime_of_spoof_balance h.1.pos hx hc h.2.2

end OddPerfect

namespace OddPerfect.Toth

open Finset ArithmeticFunction

structure Candidate (B D S a m x : ℕ) : Prop where
  pos : 0<m
  prefix_pos : 0<D
  sumpos : 0<S
  large : 5≤x
  residue : x%4=1
  least : ∀ p ∈ m.primeFactors, a≤p
  bound : D*m≤B
  balance : S*sigma 1 (m^2)*(x+1)=2*(D*m)^2*x

@[expose] def Closed (B D S a : ℕ) : Prop :=
  ∀ m x, Candidate B D S a m x → D*m=3003 ∧ x=22021

/-- The possible multiplier is fixed by the numerator and the deficiency. -/
@[expose] def checkPoint (root S : ℕ) : Bool :=
  let d := 2*root^2-S
  let x := S/d
  decide (d=0 ∨ S≠d*x ∨ x<5 ∨ x%4≠1 ∨ root=3003 ∧ x=22021)

theorem checkPoint_sound {root S x : ℕ} (hs : 0<S) (hl : 5≤x) (ho : x%4=1)
    (he : S*(x+1)=2*root^2*x) (h : checkPoint root S) : root=3003 ∧ x=22021 := by
  let d := 2*root^2-S
  have hb : S<2*root^2 := by
    by_contra! hn
    have := Nat.mul_le_mul_right x hn
    nlinarith
  have hd : 0<d := Nat.sub_pos_of_lt hb
  have hdS : d+S=2*root^2 := Nat.sub_add_cancel hb.le
  have hv : S=d*x := by nlinarith [congrArg (· * x) hdS]
  have hx : S/d=x := by calc
    S/d = d*x/d := congrArg (· / d) hv
    _ = x := Nat.mul_div_cancel_left x hd
  change decide (d=0 ∨ S≠d*(S/d) ∨ S/d<5 ∨ (S/d)%4≠1 ∨ root=3003 ∧ S/d=22021)=true at h
  rw [hx] at h
  rcases of_decide_eq_true h with z|z|z|z|z
  · omega
  · exact (z hv).elim
  · omega
  · exact (z ho).elim
  · exact z

theorem at_one {B D S a x : ℕ} (h : Candidate B D S a 1 x) (hc : checkPoint D S) :
    D*1=3003 ∧ x=22021 := by
  simpa using checkPoint_sound h.sumpos h.large h.residue (by simpa using h.balance) hc

theorem closed_oversize {B D S a : ℕ} (hc : B<D) : Closed B D S a := by
  intro m x h
  exact (hc.not_ge ((Nat.le_mul_of_pos_right D h.pos).trans h.bound)).elim

/-- A nontrivial suffix has its least prime factor at least a. -/
theorem closed_root_only {B D S a : ℕ} (hD : B<D*a) (check : checkPoint D S) : Closed B D S a := by
  intro m x h
  by_cases hm : m=1
  · subst m; exact at_one h check
  · have hp := Nat.minFac_prime hm
    have hmem := Nat.mem_primeFactors.mpr ⟨hp,Nat.minFac_dvd _,h.pos.ne'⟩
    have hmin := h.least _ hmem
    exact (hD.not_ge ((Nat.mul_le_mul_left D (hmin.trans (Nat.minFac_le h.pos))).trans h.bound)).elim

/-- If there is room for at most one remaining prime factor counted with
multiplicity, the true sum is the quadratic polynomial at that prime.
The numeric leaf may check a larger interval containing composite values. -/
theorem closed_last_prime {B D S a : ℕ} (limit : B<D*a^2)
    (empty : checkPoint D S)
    (points : ∀ j : Fin (B/D+1-a), checkPoint (D*(a+j.val)) (S*((a+j.val)^2+(a+j.val)+1))) :
    Closed B D S a := by
  intro m x h
  by_cases hm : m=1
  · subst m; exact at_one h empty
  · have hp := Nat.minFac_prime hm
    have hmem := Nat.mem_primeFactors.mpr ⟨hp,Nat.minFac_dvd _,h.pos.ne'⟩
    have hmin := h.least _ hmem
    have hprime : m.Prime := by
      by_contra hn
      have hsq := (Nat.pow_le_pow_left hmin 2).trans (Nat.minFac_sq_le_self h.pos hn)
      exact limit.not_ge ((Nat.mul_le_mul_left D hsq).trans h.bound)
    have hma := h.least m (Nat.mem_primeFactors.mpr ⟨hprime,dvd_rfl,h.pos.ne'⟩)
    have hmb : m≤B/D := (Nat.le_div_iff_mul_le h.prefix_pos).mpr (by simpa [mul_comm] using h.bound)
    let j : Fin (B/D+1-a) := ⟨m-a,by omega⟩
    have he : a+j.val=m := by dsimp [j]; omega
    have ht := points j
    rw [he] at ht
    have hsig : sigma 1 (m^2)=m^2+m+1 := by rw [sigma_one_apply_prime_pow hprime]; simp [sum_range_succ]; ring
    exact checkPoint_sound (Nat.mul_pos h.sumpos (by positivity)) h.large h.residue
      (by simpa only [←hsig] using h.balance) ht

end OddPerfect.Toth
