module

public import OddPerfect.TothTrillion.Part38
public import OddPerfect.DeficientPerfect

public section

namespace OddPerfect

/-- Tóth (2021), Theorem 1, in a stronger cofactor formulation. Among
positive odd cofactors n≤10¹² and nontrivial odd multipliers x, the equation
σ(n)(x+1)=2nx holds only for Descartes's pair. -/
theorem toth_unique_odd_pair_below_trillion {n x : ℕ} (hn : n≤10^12) (hx : Odd x) (h1 : 1<x) :
    TothPair n x ↔ n=9018009 ∧ x=22021 := by
  constructor
  · intro h
    exact Toth.small_odd_pair_of_closed Toth.case753 h hx h1 hn
  · rintro ⟨rfl,rfl⟩
    exact ⟨descartes_singleCompositeSpoof.odd_left,by decide,descartes_singleCompositeSpoof.balance⟩

/-- Every distinct Descartes number with a single coprime composite
pseudo-prime has non-pseudo-prime cofactor exceeding a trillion. -/
theorem trillion_lt_spoof_cofactor {n x : ℕ} (h : SingleCompositeSpoof n x)
    (different : n*x≠198585576189) : 10^12<n := by
  by_contra! hb
  obtain ⟨rfl,rfl⟩ := (toth_unique_odd_pair_below_trillion hb h.odd_right h.one_lt).mp
    ⟨h.odd_left,by have := h.one_lt; omega,h.balance⟩
  exact different (by decide)

/-- The bounded odd, nontrivial portion of Tóth's set of pairs is a
singleton. Projection onto the cofactor or multiplier loses no case here. -/
theorem toth_odd_pair_set_below_trillion :
    {z : ℕ × ℕ | z.1≤10^12 ∧ Odd z.2 ∧ 1<z.2 ∧ TothPair z.1 z.2} = {(9018009,22021)} := by
  ext z
  obtain ⟨n,x⟩ := z
  simp only [Set.mem_ofPred_eq,Set.mem_singleton_iff,Prod.mk.injEq]
  constructor
  · rintro ⟨hn,ho,h1,h⟩
    exact (toth_unique_odd_pair_below_trillion hn ho h1).mp h
  · rintro ⟨rfl,rfl⟩
    exact ⟨by decide,by decide,by decide,⟨descartes_singleCompositeSpoof.odd_left,
      by decide,descartes_singleCompositeSpoof.balance⟩⟩

/-- Projection of the bounded classification to odd deficient-perfect numbers,
including the value of the omitted divisor. -/
theorem deficientPerfect_below_trillion_iff {n d : ℕ} (ho : Odd n) (hb : n ≤ 10^12) :
    DeficientPerfectWith n d ↔ n = 9018009 ∧ d = 819 := by
  constructor
  · intro h
    obtain ⟨x,hx,h1,hpair,_⟩ := h.tothPair ho
    obtain ⟨rfl,_⟩ := (toth_unique_odd_pair_below_trillion hb hx h1).mp hpair
    exact ⟨rfl, Nat.add_left_cancel (h.2.trans descartes_cofactor_deficientPerfect.2.symm)⟩
  · rintro ⟨rfl,rfl⟩
    exact descartes_cofactor_deficientPerfect

end OddPerfect
