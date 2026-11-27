module

public import OddPerfect.PrimeSlots
public import OddPerfect.SpoofCover
import Mathlib.Tactic.Linarith

public section

namespace OddPerfect.SpoofBox

open Finset

@[expose] def fixedBase (s : Slot) : Bool := decide (0 < s.baseHi ∧ s.baseLo=s.baseHi)
@[expose] def fixedExponent (s : Slot) : Bool := decide (0 < s.expHi ∧ s.expLo=s.expHi)
@[expose] def admitsBase (s : Slot) (b : ℕ) : Bool :=
  decide (s.baseLo≤b ∧ (s.baseHi=0 ∨ b≤s.baseHi) ∧ b%s.stride=1)

theorem fixedBase_eq {s : Slot} {z : ℕ × ℕ} (h : s.Fits z) (hf : fixedBase s) : z.1=s.baseLo := by
  obtain ⟨_,_⟩ := of_decide_eq_true hf
  have := h.baseHi
  have := h.baseLo
  omega

theorem fixedExponent_eq {s : Slot} {z : ℕ × ℕ} (h : s.Fits z) (hf : fixedExponent s) : z.2=s.expLo := by
  obtain ⟨_,_⟩ := of_decide_eq_true hf
  have := h.expHi
  have := h.expLo
  omega

theorem admitsBase_of_fits {s : Slot} {z : ℕ × ℕ} (h : s.Fits z) : admitsBase s z.1 :=
  decide_eq_true ⟨h.baseLo,h.baseHi,h.baseResidue⟩

/-- At a fixed base and exponent the geometric sum is exact. A special
slot also guarantees the factor b+1 for every allowed exponent. -/
@[expose] def delivers (s : Slot) (r : ℕ) : Bool :=
  fixedBase s && ((fixedExponent s && decide (r ∣ ∑ j ∈ range (s.expLo+1), s.baseLo^j)) ||
    (s.special && decide (r ∣ s.baseLo+1)))

theorem delivers_sound {s : Slot} {z : ℕ × ℕ} {r : ℕ} (hx : s.Fits z) (h : delivers s r) :
    r ∣ ∑ j ∈ range (z.2+1), z.1^j := by
  obtain ⟨hf,hz⟩ := Bool.and_eq_true_iff.mp h
  rw [fixedBase_eq hx hf]
  rcases Bool.or_eq_true_iff.mp hz with h | h
  · obtain ⟨he,hd⟩ := Bool.and_eq_true_iff.mp h
    rw [fixedExponent_eq hx he]
    exact of_decide_eq_true hd
  · obtain ⟨hs,hd⟩ := Bool.and_eq_true_iff.mp h
    have hr := hx.expResidue
    simp [Slot.expResidue,Slot.stride,hs] at hr
    rw [show z.2+1=2*((z.2+1)/2) by omega]
    exact (of_decide_eq_true hd).trans (succ_dvd_sum_even _ _)

@[expose] def noOddDivisorFrom (n d : ℕ) : ℕ → Bool
  | 0 => true
  | fuel + 1 =>
    if Nat.blt n (d * d) then true
    else if n % d == 0 then false
    else noOddDivisorFrom n (d + 2) fuel

private theorem noOddDivisorFrom_iff {n d fuel : ℕ} (hn3 : 3 ≤ n) (hno : Odd n)
    (hd3 : 3 ≤ d) (hdo : Odd d) (hbound : n < (d + 2 * fuel) ^ 2)
    (hnone : ∀ m, 2 ≤ m → m < d → ¬ m ∣ n) :
    noOddDivisorFrom n d fuel = true ↔ n.Prime := by
  induction fuel generalizing d with
  | zero =>
    simp only [noOddDivisorFrom, true_iff]
    by_contra hnp
    have hmp : n.minFac.Prime := Nat.minFac_prime (by omega)
    have hmd : n.minFac ∣ n := Nat.minFac_dvd n
    have hmsq := Nat.minFac_sq_le_self (by omega) hnp
    have hmlt : n.minFac < d := by nlinarith
    exact hnone n.minFac hmp.two_le hmlt hmd
  | succ fuel ih =>
    unfold noOddDivisorFrom
    cases hlt : Nat.blt n (d * d)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hle : d * d ≤ n := Nat.le_of_not_lt fun h => by
        rw [Nat.blt_eq.mpr h] at hlt; contradiction
      cases hdvd : (n % d == 0)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        apply ih (by omega) ⟨(d + 2) / 2, by have := Nat.odd_iff.mp hdo; omega⟩
          (by convert hbound using 2; omega)
        intro m hm2 hmlt hmd
        rcases (by omega : m < d ∨ m = d ∨ m = d + 1) with hlt' | rfl | rfl
        · exact hnone m hm2 hlt' hmd
        · rw [beq_iff_eq.mpr (Nat.mod_eq_zero_of_dvd hmd)] at hdvd; contradiction
        · have h2d : 2 ∣ d + 1 := ⟨(d + 1) / 2, by have := Nat.odd_iff.mp hdo; omega⟩
          exact hno.not_two_dvd_nat (h2d.trans hmd)
      · simp only [↓reduceIte, Bool.false_eq_true, false_iff]
        intro hp
        have hd_dvd : d ∣ n := Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp hdvd)
        have hd_lt : d < n := by nlinarith
        rcases hp.eq_one_or_self_of_dvd d hd_dvd with h1 | h2 <;> omega
    · simp only [↓reduceIte, true_iff]
      have hlt' : n < d * d := Nat.blt_eq.mp hlt
      by_contra hnp
      have hmp : n.minFac.Prime := Nat.minFac_prime (by omega)
      have hmd : n.minFac ∣ n := Nat.minFac_dvd n
      have hmsq := Nat.minFac_sq_le_self (by omega) hnp
      have hmlt : n.minFac < d := by nlinarith
      exact hnone n.minFac hmp.two_le hmlt hmd

@[expose] def fastPrimeBool (n : ℕ) : Bool :=
  if Nat.blt n 1048576 then
    (n == 2) || (Nat.ble 3 n && (n % 2 == 1) && noOddDivisorFrom n 3 512)
  else
    decide n.Prime

theorem fastPrimeBool_eq_true_iff {n : ℕ} : fastPrimeBool n = true ↔ n.Prime := by
  unfold fastPrimeBool
  cases hbig : Nat.blt n 1048576
  · simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
  · simp only [↓reduceIte]
    have hn_lt : n < 1048576 := Nat.blt_eq.mp hbig
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n) with rfl | rfl | rfl | hn3
    · simp [Nat.not_prime_zero]
    · simp [Nat.not_prime_one]
    · simp [Nat.prime_two]
    · have hne2 : (n == 2) = false := beq_eq_false_iff_ne.mpr (by omega)
      have hble3 : Nat.ble 3 n = true := Nat.ble_eq.mpr hn3
      rw [hne2, hble3, Bool.false_or, Bool.true_and]
      rcases Nat.mod_two_eq_zero_or_one n with hev | hodd
      · have hmod : (n % 2 == 1) = false := by rw [hev]; rfl
        rw [hmod, Bool.false_and]
        simp only [Bool.false_eq_true, false_iff]
        intro hp
        rcases hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero hev) with h | h <;> omega
      · have hmod : (n % 2 == 1) = true := by rw [hodd]; rfl
        rw [hmod, Bool.true_and]
        apply noOddDivisorFrom_iff hn3 (Nat.odd_iff.mpr hodd) (by decide) ⟨1, rfl⟩ (by omega)
        intro m hm2 hmlt
        have hm_eq : m = 2 := by omega
        rw [hm_eq]
        exact (Nat.odd_iff.mpr hodd).not_two_dvd_nat

@[expose] def forcesMissing {k : ℕ} (s : Fin k → Slot) (r : ℕ) : Bool :=
  decide (fastPrimeBool r = true ∧ Odd r ∧ (∀ j, admitsBase (s j) r = false) ∧ (∃ i, delivers (s i) r = true))

theorem covered_missing_prime {k : ℕ} (rows : Vector Slot k) (r : ℕ)
    (h : forcesMissing (fun i : Fin k => rows[i]) r) :
    Covered (fun x => ¬ GenuineSlots x) rows := by
  intro x _ hx hb hg
  obtain ⟨hr_b,ho,hmiss,i,hi⟩ := of_decide_eq_true h
  obtain ⟨j,hj⟩ := prime_slot_forcing (fastPrimeBool_eq_true_iff.mp hr_b) ho hg.prime i (delivers_sound (hx i) hi) hb
  have hj' := admitsBase_of_fits (hx j)
  rw [hj,hmiss j] at hj'
  contradiction

/-- The three clauses detect a composite exact base, an impossible
strict ordering, or the simultaneously forced bases 3, 5 and 7. -/
@[expose] def impossiblePrimeRows {k : ℕ} (s : Fin k → Slot) : Bool :=
  let occurs := fun b => ∃ i, fixedBase (s i) = true ∧ (s i).baseLo=b
  decide ((∃ i, fixedBase (s i) = true ∧ fastPrimeBool (s i).baseLo = false) ∨
    (∃ i j, i<j ∧ 0<(s j).baseHi ∧ (s j).baseHi≤(s i).baseLo) ∨
    (occurs 3 ∧ occurs 5 ∧ occurs 7))

theorem covered_impossible_prime_rows {k : ℕ} (rows : Vector Slot k)
    (h : impossiblePrimeRows (fun i : Fin k => rows[i])) :
    Covered (fun x => ¬ GenuineSlots x) rows := by
  intro x _ hx _ hg
  rcases of_decide_eq_true h with ⟨i,hi,hp_b⟩|⟨i,j,hij,hpos,hbound⟩|h
  · have hp : ¬(rows[i]).baseLo.Prime := fun hp' => by
      rw [fastPrimeBool_eq_true_iff.mpr hp'] at hp_b; contradiction
    exact hp (fixedBase_eq (hx i) hi ▸ hg.prime i)
  · have hu := (hx j).baseHi.resolve_left (show rows[j].baseHi≠0 from hpos.ne')
    exact (hg.strict hij).not_ge (hu.trans (hbound.trans (hx i).baseLo))
  · have take (b : ℕ) (z : ∃ i : Fin k, fixedBase rows[i] = true ∧ rows[i].baseLo=b) :
        ∃ i, (x i).1=b := by
      obtain ⟨i,hi,hb⟩ := z
      exact ⟨i,(fixedBase_eq (hx i) hi).trans hb⟩
    exact hg.no105 ⟨take 3 h.1,take 5 h.2.1,take 7 h.2.2⟩

end OddPerfect.SpoofBox
