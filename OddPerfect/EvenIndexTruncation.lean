module

public import OddPerfect.EvenIndexRadical
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Order.Ring.Abs

public section
namespace OddPerfect
open ArithmeticFunction Finset
namespace ReturnLift

/-- Pairs giving one term of the product of the return polynomial and
its truncated geometric multiplier. -/
@[expose] def terms (S : Finset ℕ) (k : ℕ) : Finset (Finset ℕ × ℕ) := S.powerset ×ˢ range (k+1)
@[expose] def weight (k : ℕ) (t : Finset ℕ × ℕ) : ℕ := (∏r ∈ t.1,(r-1))*2^(k-t.2)
@[expose] def degree (v : ℕ→ℕ) (t : Finset ℕ × ℕ) : ℕ := (∑ r ∈ t.1,v r)+t.2

/-- The shifted term of degree at most k with nonnegative coefficients. -/
@[expose] def term (v : ℕ→ℕ) (k shift p : ℕ) (t : Finset ℕ × ℕ) : ℕ :=
  if degree v t+shift≤k then weight k t*p^(degree v t+shift) else 0

@[expose] def truncatedSum (S : Finset ℕ) (v : ℕ→ℕ) (k shift p : ℕ) : ℕ :=
  ∑ t ∈ terms S k,term v k shift p t

/-- Expanding the return polynomial and binomial weights gives an
identity over every commutative ring, including finite residue rings. -/
theorem sum_weighted_powers {R : Type*} [CommRing R] (x : R) (S : Finset ℕ) (v : ℕ→ℕ) (k : ℕ) :
    (∑ t ∈ terms S k,(weight k t:R)*x^(degree v t)) =
      (∏r ∈ S,(1+((r-1:ℕ):R)*x^(v r)))*(∑a ∈ range (k+1),x^a*2^(k-a)) := by
  rw [terms,Finset.sum_product,Finset.prod_one_add,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [weight,degree,Nat.cast_mul,Nat.cast_prod,Nat.cast_pow,Nat.cast_ofNat,pow_add,
    Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  ring

/-- In a residue ring of modulus p^(k+1) all omitted terms vanish. -/
theorem cast_truncatedSum (p k shift : ℕ) (S : Finset ℕ) (v : ℕ→ℕ) :
    let R := ZMod (p^(k+1))
    let x : R := p
    (truncatedSum S v k shift p:R)=x^shift*
      ((∏r ∈ S,(1+((r-1:ℕ):R)*x^(v r)))*(∑a ∈ range (k+1),x^a*2^(k-a))) := by
  let R := ZMod (p^(k+1))
  let x : R := p
  have hz : x^(k+1)=0 := by change (p:ZMod (p^(k+1)))^(k+1)=0; rw [←Nat.cast_pow,ZMod.natCast_self]
  change (truncatedSum S v k shift p:R)=x^shift*_
  rw [←sum_weighted_powers,Finset.mul_sum,truncatedSum,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases h : degree v t+shift≤k
  · simp only [term,ite_eq_left h,Nat.cast_mul,Nat.cast_pow,pow_add]
    change _=x^shift*((weight k t:R)*x^(degree v t))
    ring
  · have hN : degree v t+shift=(k+1)+(degree v t+shift-(k+1)) := by omega
    have H : x^(degree v t+shift)=0 := by rw [hN,pow_add,hz,zero_mul]
    simp only [term,ite_eq_right h,Nat.cast_zero]
    calc (0:R) = (weight k t:R)*x^(degree v t+shift) := by rw [H,mul_zero]
         _ = x^shift*((weight k t:R)*x^(degree v t)) := by rw [pow_add x (degree v t) shift]; ring

private theorem nonterminal_term_even {S : Finset ℕ} {v : ℕ→ℕ} {k shift p : ℕ}
    (hv : ∀r∈S,0<v r) {t : Finset ℕ × ℕ} (ht : t∈terms S k)
    (hterm : t≠(∅,k) ∨ 0<shift) : 2∣term v k shift p t := by
  obtain ⟨T,a⟩ := t
  obtain ⟨hT,ha⟩ := Finset.mem_product.mp ht
  have hsub := Finset.mem_powerset.mp hT
  have ha' := Finset.mem_range.mp ha
  unfold term
  split_ifs with hd
  · have hlt : a<k := by
      by_contra! hge
      have haeq : a=k := by omega
      have H : (∑ r ∈ T,v r)+a+shift≤k := hd
      have he : T=∅ := by
        by_contra hn
        obtain ⟨r,hr⟩ := Finset.nonempty_iff_ne_empty.mpr hn
        have hsingle := Finset.single_le_sum (fun r _ => Nat.zero_le (v r)) hr
        have := hv r (hsub hr)
        omega
      rcases hterm with h|h
      · exact h (by simp [he,haeq])
      · omega
    exact ((dvd_pow_self 2 (by omega : k-a≠0)).trans (dvd_mul_left _ _)).trans (dvd_mul_right _ _)
  · exact dvd_zero _

/-- The unshifted truncation is odd and the unit-shifted truncation is
even. This provides a nonzero difference for every lift k≥1. -/
theorem truncatedSum_parity {S : Finset ℕ} {v : ℕ→ℕ} {k p : ℕ}
    (hp : Odd p) (hv : ∀r∈S,0<v r) :
    Odd (truncatedSum S v k 0 p) ∧ Even (truncatedSum S v k 1 p) := by
  let last : Finset ℕ × ℕ := (∅,k)
  have hm : last∈terms S k := Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _),
    Finset.mem_range.mpr (by dsimp [last]; omega)⟩
  have hu : term v k 0 p last=p^k := by simp [term,weight,degree,last]
  constructor
  · have hdiv : 2∣∑t ∈ (terms S k).erase last,term v k 0 p t := by
      apply Finset.dvd_sum
      intro t ht
      obtain ⟨hneq,hmem⟩ := Finset.mem_erase.mp ht
      exact nonterminal_term_even hv hmem (.inl hneq)
    have H := Finset.sum_erase_add (terms S k) (term v k 0 p) hm
    rw [hu] at H
    rw [truncatedSum, ← H]
    exact (even_iff_two_dvd.mpr hdiv).add_odd hp.pow
  · apply even_iff_two_dvd.mpr
    exact Finset.dvd_sum (fun t ht => nonterminal_term_even hv ht (.inr (by decide)))

end ReturnLift
end OddPerfect
