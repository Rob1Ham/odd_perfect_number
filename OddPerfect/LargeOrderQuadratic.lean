module
public import OddPerfect.LargeOrderPrime
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
/-! Norm-one quadratic and mixed order certificates for large prime divisors. -/

public section

namespace OddPerfect
open QuadraticAlgebra

private theorem quadratic_frobenius {r : ℕ} [Fact r.Prime] (hr : Odd r)
    {D : ZMod r} (hD : D ≠ 0) (x y : ZMod r) :
    let z : QuadraticAlgebra (ZMod r) D 0 := ⟨x,y⟩
    z^r=z ∨ z^r=star z := by
  let A := QuadraticAlgebra (ZMod r) D 0
  let f := algebraMap (ZMod r) A
  let w : A := QuadraticAlgebra.omega
  let : CharP A r := charP_of_injective_algebraMap QuadraticAlgebra.algebraMap_injective r
  let k := r/2
  have he : r=2*k+1 := by have := Nat.odd_iff.mp hr; dsimp [k]; omega
  have hsplit : D^k=1 ∨ D^k= -1 := by
    apply sq_eq_one_iff.mp
    rw [←pow_mul, show k*2=r-1 by omega, ZMod.pow_card_sub_one_eq_one hD]
  have hw : w^2=f D := by
    change (QuadraticAlgebra.omega : QuadraticAlgebra (ZMod r) D 0)^2=_
    rw [sq, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp [f,A]
  have hwr : w^r=f (D^k)*w := by
    calc w^r = w^(2*k+1) := congrArg (fun e : ℕ => w^e) he
         _ = f (D^k)*w := by rw [pow_succ,pow_mul,hw,map_pow]
  let z : A := ⟨x,y⟩
  change z^r=z ∨ z^r=star z
  have hdecomp : z=f x+f y*w := by
    change (⟨x,y⟩ : QuadraticAlgebra (ZMod r) D 0)=_
    rw [QuadraticAlgebra.mk_eq_add_smul_omega, Algebra.smul_def]
  have hz : z^r=f x+f y*(f (D^k)*w) := by
    rw [hdecomp, add_pow_char, mul_pow, ←map_pow, ←map_pow, ZMod.pow_card, ZMod.pow_card, hwr]
  rcases hsplit with h1 | hneg
  · left
    rw [hz,h1,map_one,one_mul]
    exact hdecomp.symm
  · right
    rw [hz,hneg,map_neg,map_one]
    ext <;> simp [f,z,w,A]

private theorem quadratic_order_bound {r : ℕ} [Fact r.Prime] (hr : Odd r)
    {D : ZMod r} (hD : D ≠ 0) (x y : ZMod r)
    (hu : (⟨x,y⟩ : QuadraticAlgebra (ZMod r) D 0) * star ⟨x,y⟩ = 1) :
    let z : QuadraticAlgebra (ZMod r) D 0 := ⟨x,y⟩
    orderOf z ∣ r-1 ∨ orderOf z ∣ r+1 := by
  let z : QuadraticAlgebra (ZMod r) D 0 := ⟨x,y⟩
  change z*star z=1 at hu
  change orderOf z ∣ r-1 ∨ orderOf z ∣ r+1
  rcases quadratic_frobenius hr hD x y with h | h
  · left
    apply orderOf_dvd_of_pow_eq_one
    have hrpos := (Fact.out : r.Prime).pos
    calc z^(r-1) = z^(r-1)*(z*star z) := by rw [hu,mul_one]
         _ = z^r*star z := by rw [←mul_assoc, ←pow_succ, Nat.sub_add_cancel hrpos]
         _ = 1 := by rw [show z^r=z from h,hu]
  · right
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_succ,show z^r=star z from h,mul_comm,hu])

@[expose] def quadMul (n D : ℕ) (u v : ℕ × ℕ) : ℕ × ℕ :=
  ((u.1*v.1+D*u.2*v.2)%n, (u.1*v.2+u.2*v.1)%n)

@[expose] def quadPow (n D : ℕ) (u : ℕ × ℕ) (e : ℕ) : ℕ × ℕ :=
  if e=0 then (1,0) else
    let h := quadPow n D u (e/2)
    let s := quadMul n D h h
    if e%2=0 then s else quadMul n D s u
termination_by e
decreasing_by omega

private def quadCast (r D : ℕ) (u : ℕ × ℕ) : QuadraticAlgebra (ZMod r) (D : ZMod r) 0 :=
  ⟨u.1,u.2⟩

private theorem cast_mod_of_dvd {n r : ℕ} (hd : r∣n) (x : ℕ) :
    ((x%n : ℕ) : ZMod r) = x := by
  rw [ZMod.natCast_eq_natCast_iff]
  exact Nat.ModEq.of_dvd hd (Nat.mod_modEq _ _)

private theorem quadCast_mul {n r D : ℕ} (hd : r∣n) (u v : ℕ × ℕ) :
    quadCast r D (quadMul n D u v) = quadCast r D u * quadCast r D v := by
  ext <;> simp [quadCast,quadMul,cast_mod_of_dvd hd]

private theorem quadCast_pow {n r D : ℕ} (hd : r∣n) (u : ℕ × ℕ) (e : ℕ) :
    quadCast r D (quadPow n D u e) = (quadCast r D u)^e := by
  induction e using Nat.strong_induction_on with
  | ind e ih =>
    rw [quadPow]
    split_ifs with hz he
    · subst e
      ext <;> simp [quadCast]
    · rw [quadCast_mul hd,ih _ (by omega),←pow_add]
      congr 1
      omega
    · rw [quadCast_mul hd,quadCast_mul hd,ih _ (by omega),←pow_add,←pow_succ]
      congr 1
      omega

@[expose] def quadOrderTests (n D x y : ℕ) (factors : List (ℕ × ℕ)) : Bool :=
  let F := knownOrder factors
  let z := (x,y)
  n%2 == 1 && D.gcd n == 1 && (x*x)%n == (1+D*y*y)%n &&
    quadPow n D z F == (1,0) && factors.all fun pe =>
      let v := quadPow n D z (F/pe.1)
      ((v.1+(n-1)).gcd v.2).gcd n == 1

/-- The norm-one element and its nontrivial quotient powers give the same
order after reduction modulo every prime divisor of the candidate. -/
theorem quadOrder_dvd_prime_adjacent {n D x y r : ℕ} {factors : List (ℕ × ℕ)}
    (hn : 1<n) (hp : ∀ f ∈ factors, f.1.Prime) (h : quadOrderTests n D x y factors=true)
    (hr : r.Prime) (hd : r∣n) : knownOrder factors ∣ r-1 ∨ knownOrder factors ∣ r+1 := by
  let F := knownOrder factors
  let v : ℕ × ℕ := (x,y)
  let z := quadCast r D v
  let : Fact r.Prime := ⟨hr⟩
  simp only [quadOrderTests,Bool.and_eq_true,beq_iff_eq,List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hodd,hcop⟩,hnorm⟩,hclose⟩,hchecks⟩ := h
  have hrOdd : Odd r := by
    rcases hr.eq_two_or_odd with h2 | ho
    · subst r
      have := Nat.mod_eq_zero_of_dvd hd
      omega
    · exact Nat.odd_iff.mpr ho
  have hD : (D : ZMod r) ≠ 0 := by
    intro h0
    exact hr.not_dvd_one (hcop ▸ Nat.dvd_gcd ((ZMod.natCast_eq_zero_iff _ _).mp h0) hd)
  have hquad : (x : ZMod r)*(x : ZMod r) = 1+(D : ZMod r)*(y : ZMod r)*(y : ZMod r) := by
    have hnat := Nat.ModEq.of_dvd hd (show x*x ≡ 1+D*y*y [MOD n] from hnorm)
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hnat
  have hu : z*star z=1 := by
    ext
    · simp [z,quadCast,v]
      linear_combination hquad
    · simp [z,quadCast,v]; ring
  have ho : orderOf z=F := by
    apply orderOf_eq_of_pow_and_pow_div_prime
    · change z^F=1
      rw [show z^F=quadCast r D (quadPow n D v F) from (quadCast_pow hd v F).symm,
        show quadPow n D v F = (1,0) from hclose]
      ext <;> simp [quadCast]
    · intro q hq hqF he
      obtain ⟨_,hx,hdiv⟩ := hq.prime.dvd_prod_iff.mp hqF
      obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hx
      obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (hp f hf)).mp (hq.dvd_of_dvd_pow hdiv)
      let val := quadPow n D v (F/f.1)
      have hv : quadCast r D val=1 := (quadCast_pow hd v (F/f.1)).trans he
      have hre : (val.1 : ZMod r)=1 := congrArg QuadraticAlgebra.re hv
      have him : (val.2 : ZMod r)=0 := congrArg QuadraticAlgebra.im hv
      have hsum : ((val.1+(n-1) : ℕ) : ZMod r)=0 := by
        rw [Nat.cast_add,hre,Nat.cast_sub (by omega : 1≤n),Nat.cast_one,(ZMod.natCast_eq_zero_iff n r).mpr hd]
        simp
      have hden := Nat.dvd_gcd (Nat.dvd_gcd ((ZMod.natCast_eq_zero_iff _ _).mp hsum)
        ((ZMod.natCast_eq_zero_iff _ _).mp him)) hd
      exact hr.not_dvd_one (hchecks _ hf ▸ hden)
  change F ∣ r-1 ∨ F ∣ r+1
  rw [← ho]
  exact quadratic_order_bound hrOdd hD x y hu

@[expose] def largeOrderPlusCheck (n D x y : ℕ) (factors : List (ℕ × ℕ)) : Bool :=
  let F := knownOrder factors
  decide (1<n ∧ 1<F ∧ n<(F-1)^2) && quadOrderTests n D x y factors

theorem prime_of_largeOrderPlusCheck {n D x y : ℕ} {factors : List (ℕ × ℕ)}
    (hp : ∀ f ∈ factors, f.1.Prime) (h : largeOrderPlusCheck n D x y factors=true) : n.Prime := by
  simp only [largeOrderPlusCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨hn,hF,hs⟩,hc⟩ := h
  have hr : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hle : knownOrder factors-1 ≤ n.minFac := by
    rcases quadOrder_dvd_prime_adjacent hn hp hc hr (Nat.minFac_dvd n) with h | h
    · have := Nat.le_of_dvd (by have := hr.one_lt; omega : 0<n.minFac-1) h
      omega
    · have := Nat.le_of_dvd (Nat.succ_pos _) h
      omega
  by_contra hn'
  exact hs.not_ge ((Nat.pow_le_pow_left hle 2).trans (Nat.minFac_sq_le_self (by omega) hn'))


/-- The two orders force each prime divisor into one of two residue classes.
The supplied offset is the first possible prime in the negative class. -/
@[expose] def mixedOrderCheck (n b D x y offset : ℕ) (minusFactors plusFactors : List (ℕ × ℕ)) : Bool :=
  let F := knownOrder minusFactors
  let G := knownOrder plusFactors
  decide (1<n ∧ 1<F ∧ 1<G ∧ 1<offset ∧ offset ≤ F.lcm G+1 ∧
    F∣offset-1 ∧ G∣offset+1 ∧ n<offset^2) &&
    orderTests n b minusFactors && quadOrderTests n D x y plusFactors

theorem prime_of_mixedOrderCheck {n b D x y offset : ℕ} {minusFactors plusFactors : List (ℕ × ℕ)}
    (hm : ∀ f ∈ minusFactors, f.1.Prime) (hp : ∀ f ∈ plusFactors, f.1.Prime)
    (h : mixedOrderCheck n b D x y offset minusFactors plusFactors=true) : n.Prime := by
  let F := knownOrder minusFactors
  let G := knownOrder plusFactors
  let r := n.minFac
  simp only [mixedOrderCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨hn,hF,hG,hoff,hmax,hFo,hGo,hs⟩,hmtest⟩,hptest⟩ := h
  change offset ≤ F.lcm G+1 at hmax
  change F∣offset-1 at hFo
  change G∣offset+1 at hGo
  have hr : r.Prime := Nat.minFac_prime (by omega)
  have hd : r∣n := Nat.minFac_dvd n
  have hFr : F∣r-1 := knownOrder_dvd_prime_pred hn (by omega) hm hmtest hr hd
  have hr1 := hr.one_lt
  have hle : offset ≤ r := by
    rcases quadOrder_dvd_prime_adjacent hn hp hptest hr hd with hm | hp
    · have hL : F.lcm G ∣ r-1 := Nat.lcm_dvd hFr hm
      have := Nat.le_of_dvd (by omega : 0<r-1) hL
      omega
    · by_contra! hlt
      have hf : F∣offset-r := (show (offset-1)-(r-1)=offset-r by omega) ▸ Nat.dvd_sub hFo hFr
      have hg : G∣offset-r := (show (offset+1)-(r+1)=offset-r by omega) ▸ Nat.dvd_sub hGo hp
      have hh := Nat.le_of_dvd (by omega : 0<offset-r) (Nat.lcm_dvd hf hg)
      omega
  by_contra hc
  exact hs.not_ge ((Nat.pow_le_pow_left hle 2).trans (Nat.minFac_sq_le_self (by omega) hc))

end OddPerfect
