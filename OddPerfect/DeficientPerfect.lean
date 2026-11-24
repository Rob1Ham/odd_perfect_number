module

public import OddPerfect.TothCandidates
import Mathlib.Tactic.Ring

public section

namespace OddPerfect
open ArithmeticFunction

/-- The deficient divisor in the sense of Tang et al. and Yang–Togbé. -/
@[expose] def DeficientPerfectWith (n d : ℕ) : Prop :=
  d ∈ n.properDivisors ∧ sigma 1 n + d = 2*n

theorem tothPair_one_iff {n : ℕ} : TothPair n 1 ↔ n=1 := by
  constructor
  · intro h
    have eq := h.2.2
    rw [sigma_one_apply,Nat.sum_divisors_eq_sum_properDivisors_add_self] at eq
    by_contra hn
    have hgt : 1<n := by have := h.1.pos; omega
    have hpos : 0 < ∑ i ∈ n.properDivisors, i := Finset.sum_pos' (by intros; omega)
      ⟨1,Nat.one_mem_properDivisors_iff_one_lt.mpr hgt,by decide⟩
    omega
  · rintro rfl
    exact ⟨by decide,by decide,by simp⟩

/-- A nontrivial odd multiplier gives a proper deficient divisor. Its
complementary divisor is exactly half of x+1. -/
theorem TothPair.deficientDivisor {n x : ℕ} (h : TothPair n x) (hx : Odd x) (h1 : 1<x) :
    ∃ d t, DeficientPerfectWith n d ∧ n=d*t ∧ x+1=2*t := by
  obtain ⟨k,hk⟩ := hx
  let t := k+1
  have ht : 1<t := by dsimp [t]; omega
  have hx' : x+1=2*t := by dsimp [t]; omega
  have balance := h.2.2
  have half : sigma 1 n*t=n*x := by rw [hx'] at balance; nlinarith
  have hn := h.1.pos
  have hsmall : sigma 1 n < 2*n := by
    by_contra! hl
    have hm := Nat.mul_le_mul_right t hl
    nlinarith [congrArg (n*·) hx']
  let d := 2*n-sigma 1 n
  have hd : 0<d := Nat.sub_pos_of_lt hsmall
  have hsum : sigma 1 n+d=2*n := Nat.add_sub_of_le hsmall.le
  have hn' : n=d*t := by
    nlinarith [congrArg (· * t) hsum,congrArg (n*·) hx']
  have hlt : d<n := by
    calc d = d*1 := (Nat.mul_one _).symm
         _ < d*t := Nat.mul_lt_mul_of_pos_left ht hd
         _ = n := hn'.symm
  exact ⟨d,t,⟨Nat.mem_properDivisors.mpr ⟨⟨t,hn'⟩,hlt⟩,hsum⟩,hn',hx'⟩

/-- Every odd deficient-perfect number gives a nontrivial odd multiplier
of Tóth's cleared equation, with no primality assumption on that multiplier. -/
theorem DeficientPerfectWith.tothPair {n d : ℕ} (h : DeficientPerfectWith n d) (ho : Odd n) :
    ∃ x, Odd x ∧ 1<x ∧ TothPair n x ∧ x+1=2*(n/d) := by
  obtain ⟨⟨t,ht⟩,hlt⟩ := Nat.mem_properDivisors.mp h.1
  have hd := Nat.pos_of_mem_properDivisors h.1
  have htwo : 1<t := by
    by_contra! he
    exact hlt.not_ge (ht ▸ (Nat.mul_le_mul_left d he).trans_eq (Nat.mul_one _))
  let x := 2*t-1
  have hx : x+1=2*t := by dsimp [x]; omega
  have h1 : 1<x := by omega
  have oddx : Odd x := Nat.odd_iff.mpr (by omega)
  have hbal : sigma 1 n*(x+1)=2*(n*x) := by
    have := congrArg (· * t) h.2
    nlinarith [congrArg (n*·) hx]
  refine ⟨x,oddx,h1,⟨ho,by omega,hbal⟩,?_⟩
  rwa [ht,Nat.mul_div_cancel_left _ hd]

/-- Equality of the two projected candidate sets, including exact treatment
of the trivial multiplier. -/
theorem odd_deficientPerfect_iff_toth {n : ℕ} (ho : Odd n) :
    (∃ d, DeficientPerfectWith n d) ↔ ∃ x, Odd x ∧ 1<x ∧ TothPair n x := by
  constructor
  · rintro ⟨d,h⟩
    obtain ⟨x,hx,h1,hpair,_⟩ := h.tothPair ho
    exact ⟨x,hx,h1,hpair⟩
  · rintro ⟨x,hx,h1,h⟩
    obtain ⟨d,_,hd,_,_⟩ := h.deficientDivisor hx h1
    exact ⟨d,hd⟩

theorem descartes_cofactor_deficientPerfect : DeficientPerfectWith 9018009 819 := by
  have h := descartes_singleCompositeSpoof.balance
  constructor
  · exact Nat.mem_properDivisors.mpr ⟨by decide,by decide⟩
  · change sigma 1 9018009*(22021+1)=2*(9018009*22021) at h
    have hs := congrArg (· / (22021+1)) h
    simp only [Nat.mul_div_cancel _ (by decide : 0 < 22021+1)] at hs
    rw [hs]

end OddPerfect
