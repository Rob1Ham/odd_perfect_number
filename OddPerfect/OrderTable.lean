module

public import OddPerfect.LargeOrderPrime
public import OddPerfect.PrimeBank

public section

namespace OddPerfect

/-- A batch of Pocklington witnesses arranged for fast lookup of the
smaller primes used in their order factorizations. -/
abbrev OrderRow := ℕ × ℕ × List (ℕ × ℕ)

inductive OrderTable where
  | leaf (rows : List OrderRow)
  | branch (pivot : ℕ) (left right : OrderTable)

@[expose] def OrderTable.bank : OrderTable → PrimeBank
  | .leaf rows => .leaf (rows.map Prod.fst)
  | .branch k l r => .branch k l.bank r.bank

@[expose] def OrderTable.rowOK (bank : PrimeBank) (row : OrderRow) : Bool :=
  if row.1<512 then decide row.1.Prime else
    largeOrderCheck row.1 row.2.1 row.2.2 && row.2.2.all fun pe =>
      if pe.1<512 then decide pe.1.Prime else decide (pe.1<row.1) && bank.contains pe.1

@[expose] def OrderTable.check (bank : PrimeBank) : OrderTable → Bool
  | .leaf rows => rows.all (rowOK bank)
  | .branch _ l r => l.check bank && r.check bank

private def All (P : ℕ→Prop) : PrimeBank → Prop
  | .leaf ps => ∀ p ∈ ps, P p
  | .branch _ l r => All P l ∧ All P r

private theorem of_contains {P : ℕ→Prop} (s : PrimeBank) (h : All P s) {p : ℕ}
    (hp : s.contains p) : P p := by
  induction s with
  | leaf ps => exact h _ (List.contains_iff_mem.mp hp)
  | branch k l r il ir =>
    by_cases lt : p<k
    · exact il h.1 (by simpa [PrimeBank.contains,lt] using hp)
    · exact ir h.2 (by simpa [PrimeBank.contains,lt] using hp)

private def Conditional (B : PrimeBank) (p : ℕ) : Prop :=
  (∀ q, q<p → B.contains q → q.Prime) → p.Prime

private theorem conditional_of_check (B : PrimeBank) (t : OrderTable) (h : t.check B) :
    All (Conditional B) t.bank := by
  induction t with
  | branch _ l r il ir =>
    have h' : l.check B = true ∧ r.check B = true := by
      simpa only [OrderTable.check,Bool.and_eq_true] using h
    exact ⟨il h'.1,ir h'.2⟩
  | leaf rows =>
    intro p hp ih
    obtain ⟨row,hm,rfl⟩ := List.mem_map.mp hp
    have ht := List.all_eq_true.mp h row hm
    by_cases small : row.1<512
    · simpa [OrderTable.rowOK,small] using ht
    · simp only [OrderTable.rowOK,ite_eq_right small,Bool.and_eq_true,List.all_eq_true] at ht
      apply prime_of_largeOrderCheck _ ht.1
      intro f hf
      have hv := ht.2 f hf
      by_cases hsmall : f.1<512
      · simpa [hsmall] using hv
      · simp only [ite_eq_right hsmall,Bool.and_eq_true,decide_eq_true_eq] at hv
        exact ih f.1 hv.1 hv.2

private theorem discharge (B s : PrimeBank) (h : All (Conditional B) s)
    (known : ∀ q, B.contains q → q.Prime) : s.Certified := by
  induction s with
  | leaf ps => exact fun p hp => h p hp (fun q _ hq => known q hq)
  | branch _ l r il ir => exact ⟨il h.1,ir h.2⟩

/-- Closure of the supplied order dependencies follows by strong
induction in the prime candidate. All modulus and gcd tests run once. -/
theorem OrderTable.certified_of_check (t : OrderTable) (h : t.check t.bank) : t.bank.Certified := by
  have all := conditional_of_check t.bank t h
  apply discharge t.bank t.bank all
  intro p
  induction p using Nat.strong_induction_on with
  | ind p ih =>
    intro hp
    exact (of_contains _ all hp) ih

end OddPerfect
