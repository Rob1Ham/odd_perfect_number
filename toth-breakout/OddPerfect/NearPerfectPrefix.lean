module

public import OddPerfect.NearPerfect
public import OddPerfect.ProductGap
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect.NearPrefix
open Finset ArithmeticFunction

/-- Clear the two labels for each completed prime power. The coefficients u and v
also account for whether the extra label 2(n/d)+1 has been encountered. -/
theorem clear_completed {ι : Type*} [DecidableEq ι] (l c : Finset ι) (p e : ι → ℕ)
    (u v : ℕ) (incl : c⊆l) (gt : ∀ i∈c, 1<p i) :
    u*(l.prod p * ∏ i∈c,(p i^(e i+1)-1)) = v*((∏ i∈l,(p i-1)) * ∏ i∈c,p i^(e i+1)) ↔
      u*((∏ i∈c,∑ j∈range (e i+1), p i^j) * (l \ c).prod p) =
        v*((∏ i∈c,p i^e i) * ∏ i∈l \ c,(p i-1)) := by
  let f := fun i => p i^e i
  let g := fun i => ∑ j∈range (e i+1),p i^j
  let pred := fun i => p i-1
  have a : (∏ i∈c,(p i^(e i+1)-1)) = c.prod g * c.prod pred := by
    rw [←prod_mul_distrib]
    apply prod_congr rfl
    intro i hi
    have h := geom_sum_mul_add (p i-1) (e i+1)
    rw [Nat.sub_add_cancel (gt i hi).le] at h
    change p i^(e i+1)-1=(∑ j∈range (e i+1),p i^j)*(p i-1)
    omega
  have b : (∏ i∈c,p i^(e i+1)) = c.prod f * c.prod p := by
    rw [←prod_mul_distrib]
    exact prod_congr rfl (fun i _ => pow_succ _ _)
  have pos : 0<c.prod p * c.prod pred := mul_pos (prod_pos (fun i hi => (gt i hi).le))
    (prod_pos (fun i hi => Nat.sub_pos_of_lt (gt i hi)))
  change u*(l.prod p * _) = v*(l.prod pred * _) ↔
    u*(c.prod g * (l \ c).prod p)=v*(c.prod f * (l \ c).prod pred)
  rw [a,b,←prod_sdiff (f:=p) incl,←prod_sdiff (f:=pred) incl]
  have rearrangeL : u*((l \ c).prod p * c.prod p * (c.prod g * c.prod pred)) =
      (u*(c.prod g*(l \ c).prod p))*(c.prod p*c.prod pred) := by ring
  have rearrangeR : v*((l \ c).prod pred * c.prod pred * (c.prod f * c.prod p)) =
      (v*(c.prod f*(l \ c).prod pred))*(c.prod p*c.prod pred) := by ring
  rw [rearrangeL,rearrangeR]
  exact Nat.mul_left_inj pos.ne'

/-- When the extra closing label is absent from a prefix, its numerator is odd
and cannot equal twice the denominator. -/
theorem without_extra {P c o : Finset ℕ} {g : ℕ → ℕ} (godd : Odd (P.prod g))
    (cs : c⊆P) (oddp : ∀ p∈o, Odd p) (D : ℕ) : c.prod g * o.prod id ≠ 2*D := by
  have hg := godd.of_dvd_nat (prod_dvd_prod_of_subset c P g cs)
  have hp : Odd (o.prod id) := prod_induction id Odd (fun _ _ => Odd.mul) odd_one oddp
  exact fun eq => (hg.mul hp).not_two_dvd_nat ⟨D,eq⟩

/-- After including the extra label x=2t+1, exact balance is impossible
at a proper prefix. An open prime supplies an even denominator, while
with no open primes each missing genuine component strictly raises abundancy. -/
theorem with_extra {P c o : Finset ℕ} {f g : ℕ → ℕ} {t : ℕ} (ht : Odd t)
    (cs : c ⊂ P) (os : o ⊆ P) (godd : Odd (P.prod g)) (oddp : ∀ p∈P, Odd p)
    (comp : ∀ p∈P, 0 < f p ∧ f p < g p)
    (full : t * P.prod g = (2*t+1) * P.prod f) :
    t*(c.prod g * o.prod id) ≠ (2*t+1)*(c.prod f * ∏ p∈o,(p-1)) := by
  rcases o.eq_empty_or_nonempty with rfl|⟨p,hp⟩
  · simp only [prod_empty,mul_one]
    intro eq
    let r := P \ c
    have rest : r.Nonempty := sdiff_nonempty.mpr cs.not_superset
    have lt : r.prod f < r.prod g := prod_lt_prod_of_nonempty₀
      (fun p hp => (comp p (mem_sdiff.mp hp).1).1)
      (fun p hp => (comp p (mem_sdiff.mp hp).1).2) rest
    have fg : 0<t*c.prod g := mul_pos ht.pos
      (prod_pos fun p hp => (comp p (cs.subset hp)).1.trans (comp p (cs.subset hp)).2)
    have left : r.prod g * c.prod g=P.prod g := prod_sdiff cs.subset
    have right : r.prod f * c.prod f=P.prod f := prod_sdiff cs.subset
    rw [←left,←right] at full
    have same : (t*c.prod g)*r.prod g = (t*c.prod g)*r.prod f := by
      calc (t*c.prod g)*r.prod g = t*(r.prod g*c.prod g) := by ring
           _ = (2*t+1)*(r.prod f*c.prod f) := full
           _ = (t*c.prod g)*r.prod f := by rw [eq]; ring
    exact lt.ne' (Nat.eq_of_mul_eq_mul_left fg same)
  · have hcg := godd.of_dvd_nat (prod_dvd_prod_of_subset c P g cs.subset)
    have hob : Odd (o.prod id) := prod_induction id Odd (fun _ _ => Odd.mul)
      odd_one (fun p hp => oddp p (os hp))
    have even : 2∣p-1 := by have := Nat.odd_iff.mp (oddp p (os hp)); omega
    have d := even.trans (dvd_prod_of_mem (fun q => q-1) hp)
    intro eq
    exact (ht.mul (hcg.mul hob)).not_two_dvd_nat (eq ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_right d _) _)

end OddPerfect.NearPrefix
