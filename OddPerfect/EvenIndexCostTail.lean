module

public import OddPerfect.EvenIndexEnvelope
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.LinearCombination

public section
namespace OddPerfect
open ArithmeticFunction

/-- Short return multiplicities at index exponent 112 force a source
prime below 245. The four polynomial identities are integral. -/
theorem even_index_112_tail_multiplicity {q p s r β : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hrs : r ∣ s) (hcut : 245≤r) (hb : Odd β)
    (hσq : sigma 1 (p^(2*56))=q) (hplus : q+1=2*s^2)
    (hout : sigma 1 (r^(2*s.factorization r))=p^β) : 11≤β := by
  let : Fact r.Prime := ⟨hr⟩
  let x : ZMod r := p
  obtain ⟨hv,hret,hone⟩ := even_index_source_root_equations hp hr hrs hσq hplus hout
  change x^β=1 at hv
  change x^113+x=2 at hret
  have hx : x≠1 := fun h => (by omega : ¬r≤114) (Nat.le_of_dvd (by decide) (hone h))
  have cert (c : ℕ) (hc : 0<c) (hsmall : c<245) (hh : (x-1)*(c:ZMod r)=0) : False := by
    have hd := (ZMod.natCast_eq_zero_iff c r).mp ((mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hx))
    have := Nat.le_of_dvd hc hd
    omega
  have red (b t m : ℕ) (hn : 113=b*t+m) (h : x^b=1) : x^m+x=2 := by
    rw [hn,pow_add,pow_mul,h,one_pow,one_mul] at hret
    exact hret
  by_contra! hh
  have hβ := Nat.odd_iff.mp hb
  obtain h|h|h|h|h : β=1 ∨ β=3 ∨ β=5 ∨ β=7 ∨ β=9 := by omega
  · exact hx (by simpa [h] using hv)
  · rw [h] at hv
    have h2 := red 3 37 2 (by decide) hv
    apply cert 3 (by decide) (by decide)
    push_cast
    linear_combination hv+(1-x)*h2
  · rw [h] at hv
    have h3 := red 5 22 3 (by decide) hv
    apply cert 11 (by decide) (by decide)
    push_cast
    linear_combination (1-2*x)*hv+(5-2*x-x^2+2*x^3)*h3
  · rw [h] at hv
    have h1 := red 7 16 1 (by decide) hv
    apply cert 2 (by decide) (by decide)
    push_cast
    linear_combination h1
  · rw [h] at hv
    have h5 := red 9 12 5 (by decide) hv
    apply cert 171 (by decide) (by decide)
    push_cast
    linear_combination (1-42*x-10*x^2-2*x^3)*hv+(85-22*x-6*x^2-2*x^3-x^4+42*x^5+10*x^6+2*x^7)*h5

/-- A prime larger than j+2 cannot account for a single return copy. -/
theorem three_le_even_index_large_source_multiplicity {q p s u r β : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hrs : r ∣ s) (hcut : 2*u+2<r) (hb : Odd β)
    (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2)
    (hout : sigma 1 (r^(2*s.factorization r))=p^β) : 3≤β := by
  obtain ⟨hv,_,hone⟩ := even_index_source_root_equations hp hr hrs hσq hplus hout
  by_contra! h
  have h1 : β=1 := by have := Nat.odd_iff.mp hb; omega
  rw [h1,pow_one] at hv
  exact hcut.not_ge (Nat.le_of_dvd (by omega) (hone hv))

end OddPerfect
