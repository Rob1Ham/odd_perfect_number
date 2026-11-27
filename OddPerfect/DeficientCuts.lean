module

public import OddPerfect.DeficientSlots

public section
namespace OddPerfect.DeficientSlots
open SpoofBox

theorem closed_leaf {rows : Vector Slot 5} {g : ℕ}
    (test : acceptedLeaf (fun i : Fin 5 => rows[i]) [historical]) : Closed rows g := by
  intro z h fit _
  simpa using acceptedLeaf_sound _ _ z fit h.balance test

theorem closed_last {rows : Vector Slot 5} {g : ℕ} (i : Fin 5)
    (test : lastLeaf (fun j : Fin 5 => rows[j]) i [historical]) : Closed rows g := by
  intro z h fit _
  simpa using lastLeaf_sound _ i _ z fit h.balance test

/-- A bound on the multiplier has no effect on the ordered prime bases. -/
@[expose] def lowerBase (rows : Vector Slot 5) (i : Fin 5) (lo : ℕ) : Vector Slot 5 :=
  setBase rows i (max rows[i].baseLo lo) rows[i].baseHi

@[expose] def upperBase (rows : Vector Slot 5) (i : Fin 5) (hi : ℕ) : Vector Slot 5 :=
  setBase rows i rows[i].baseLo (cap rows[i].baseHi hi)

theorem closed_split_base {rows : Vector Slot 5} {g : ℕ} (i : Fin 5) (cut : ℕ)
    (lo : Closed (upperBase rows i cut) g) (hi : Closed (lowerBase rows i (cut+1)) g) :
    Closed rows g := by
  intro z h fit hd
  by_cases low : (z i).1≤cut
  · apply lo z h _ hd
    apply fits_set_base rows i fit (fit i).baseLo
    by_cases openBound : rows[i].baseHi=0
    · exact .inr (by change _ ≤ if rows[i].baseHi=0 then cut else min rows[i].baseHi cut; rw [if_pos openBound]; exact low)
    · exact .inr (by change _ ≤ if rows[i].baseHi=0 then cut else min rows[i].baseHi cut; rw [if_neg openBound]; exact le_min ((fit i).baseHi.resolve_left openBound) low)
  · exact hi z h (fits_set_base rows i fit (max_le (fit i).baseLo (by omega)) (fit i).baseHi) hd

@[expose] def setExp (rows : Vector Slot 5) (i : Fin 4) (lo hi : ℕ) : Vector Slot 5 :=
  Vector.ofFn fun j => if j=i.castSucc then {rows[j] with expLo:=lo,expHi:=hi} else rows[j]

theorem closed_split_exp {rows : Vector Slot 5} {g : ℕ} (i : Fin 4) (c : ℕ) (even : c%2=0)
    (lo : Closed (setExp rows i rows[i.castSucc].expLo c) g)
    (hi : Closed (setExp rows i (c+2) rows[i.castSucc].expHi) g) : Closed rows g := by
  intro z h fit hd
  by_cases low : (z i.castSucc).2≤c
  · apply lo z h _ hd
    intro j
    by_cases e : j=i.castSucc
    · subst j
      have hfit : ({rows[i.castSucc] with expHi:=c} : Slot).Fits (z i.castSucc) :=
        {fit i.castSucc with expHi := .inr low}
      simp [setExp, Fin.ext_iff]
      convert hfit <;> rfl
    · simpa [setExp,e] using fit j
  · apply hi z h _ hd
    intro j
    by_cases e : j=i.castSucc
    · subst j
      have residue := Nat.even_iff.mp (h.evenExp i)
      have hfit : ({rows[i.castSucc] with expLo:=c+2} : Slot).Fits (z i.castSucc) :=
        {fit i.castSucc with expLo := (by omega : c+2 ≤ (z i.castSucc).2)}
      simp [setExp, Fin.ext_iff]
      convert hfit <;> rfl
    · simpa [setExp,e] using fit j

@[expose] def setSpecialExp (rows : Vector Slot 5) (lo hi : ℕ) : Vector Slot 5 :=
  Vector.ofFn fun j => if j=(4:Fin 5) then {rows[j] with expLo:=lo,expHi:=hi} else rows[j]

theorem closed_split_special {rows : Vector Slot 5} {g : ℕ} (c : ℕ) (hc : c%4=1)
    (lo : Closed (setSpecialExp rows rows[4].expLo c) g)
    (hi : Closed (setSpecialExp rows (c+4) rows[4].expHi) g) : Closed rows g := by
  intro z h fit hd
  by_cases low : (z 4).2≤c
  · apply lo z h _ hd
    intro j
    by_cases e : j=4
    · subst j
      simpa [setSpecialExp] using (show ({rows[4] with expHi:=c} : Slot).Fits (z 4) from
        {fit 4 with expHi := .inr low})
    · simpa [setSpecialExp,e] using fit j
  · apply hi z h _ hd
    intro j
    by_cases e : j=4
    · subst j
      have := h.specialExponent
      simpa [setSpecialExp] using (show ({rows[4] with expLo:=c+4} : Slot).Fits (z 4) from
        {fit 4 with expLo := (by omega : c+4≤(z 4).2)})
    · simpa [setSpecialExp,e] using fit j

theorem closed_prime_lower {rows : Vector Slot 5} {g : ℕ} (i : Fin 4) (lo start : ℕ)
    (hs : start≤rows[i.castSucc].baseLo ∨ ∃ j : Fin 4, j < i ∧ start≤rows[j.castSucc].baseLo+1)
    (gap : primeGap start (lo-start) rows[i.castSucc].stride 0)
    (next : Closed (setBase rows i.castSucc lo rows[i.castSucc].baseHi) g) : Closed rows g := by
  intro z h fit hd
  have base := (fit i.castSucc).base
  have hstart : start≤(z i.castSucc).1 := by
    rcases hs with low|⟨j,lt,low⟩
    · exact low.trans (fit i.castSucc).baseLo
    · have step : (z j.castSucc).1 < (z i.castSucc).1 := h.increasing lt; have := (fit j.castSucc).baseLo; omega
  have := outside_prime_gap gap (h.prime i) (fit i.castSucc).baseResidue (by omega)
  exact next z h (fits_set_base rows i.castSucc fit (by omega) (fit i.castSucc).baseHi) hd

theorem closed_prime_upper {rows : Vector Slot 5} {g : ℕ} (i : Fin 4) (hi stop : ℕ)
    (hs : (0<rows[i.castSucc].baseHi ∧ rows[i.castSucc].baseHi≤stop) ∨
      ∃ j : Fin 4, i < j ∧ 0<rows[j.castSucc].baseHi ∧ rows[j.castSucc].baseHi≤stop+1)
    (gap : primeGap (hi+1) (stop-hi) rows[i.castSucc].stride 0)
    (next : Closed (setBase rows i.castSucc rows[i.castSucc].baseLo hi) g) : Closed rows g := by
  intro z h fit hd
  have base := (fit i.castSucc).base
  have hstop : (z i.castSucc).1≤stop := by
    rcases hs with ⟨pos,le⟩|⟨j,lt,pos,le⟩
    · exact ((fit i.castSucc).baseHi.resolve_left pos.ne').trans le
    · have step : (z i.castSucc).1 < (z j.castSucc).1 := h.increasing lt; have := (fit j.castSucc).baseHi.resolve_left pos.ne'; omega
  have := outside_prime_gap gap (h.prime i) (fit i.castSucc).baseResidue (by omega)
  exact next z h (fits_set_base rows i.castSucc fit (fit i.castSucc).baseLo (.inr (by omega))) hd

/-- If g divides the multiplier and the multiplier is one modulo four,
its quotient by g is congruent to g modulo four. -/
@[expose] def firstMultiplier (g start : ℕ) : ℕ :=
  let q := (start+g-1)/g
  g*(q + (g%4+4-q%4)%4)

theorem firstMultiplier_le {g start x : ℕ} (gd : g∣x) (hx : x%4=1) (low : start≤x) :
    firstMultiplier g start ≤ x := by
  obtain ⟨a,rfl⟩ := gd
  have gh : 0<g := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at hx
  have quot : (start+g-1)/g ≤ a := by
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul gh).mpr
    rw [Nat.succ_mul,mul_comm a g]
    omega
  rw [Nat.mul_mod] at hx
  have tbl : ∀ a b : Fin 4, (a.val*b.val)%4=1 → a.val=b.val := by decide
  have same := tbl ⟨g%4,Nat.mod_lt _ (by decide)⟩ ⟨a%4,Nat.mod_lt _ (by decide)⟩ hx
  change g%4=a%4 at same
  unfold firstMultiplier
  apply Nat.mul_le_mul_left
  omega

@[expose] def noMultiplier (s : Slot) (g : ℕ) : Bool :=
  decide (0<s.baseHi ∧ s.baseHi < firstMultiplier g s.baseLo)

theorem noMultiplier_sound {s : Slot} {g x e : ℕ} (fit : s.Fits (x,e)) (hx : x%4=1)
    (test : noMultiplier s g) : ¬g∣x := by
  obtain ⟨pos,lt⟩ := of_decide_eq_true test
  intro hd
  exact lt.not_ge ((firstMultiplier_le hd hx fit.baseLo).trans (fit.baseHi.resolve_left pos.ne'))

theorem closed_multiplier_bounds {rows : Vector Slot 5} {g lo hi : ℕ}
    (low : lo≤firstMultiplier g rows[4].baseLo)
    (high : hi=0 ∨ (0<rows[4].baseHi ∧ rows[4].baseHi < firstMultiplier g (hi+1)))
    (next : Closed (setBase rows 4 lo hi) g) : Closed rows g := by
  intro z h fit hd
  apply next z h _ hd
  apply fits_set_base rows 4 fit (low.trans (firstMultiplier_le hd h.multiplier (fit 4).baseLo))
  rcases high with zero|⟨pos,lt⟩
  · exact .inl zero
  · right
    by_contra! large
    exact lt.not_ge ((firstMultiplier_le hd h.multiplier large).trans ((fit 4).baseHi.resolve_left pos.ne'))

theorem closed_no_multiplier {rows : Vector Slot 5} {g : ℕ} (test : noMultiplier rows[4] g) :
    Closed rows g := by
  intro z h fit hd
  exact (noMultiplier_sound (fit 4) h.multiplier test hd).elim

end OddPerfect.DeficientSlots
