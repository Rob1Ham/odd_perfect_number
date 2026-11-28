module

public import OddPerfect.SpoofFactors
public import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open Finset

/-- A geometric sum at a base congruent to one is congruent to its length. -/
theorem geom_modEq_of_one {b d : ℕ} (hb : b ≡ 1 [MOD d]) (k : ℕ) :
    (∑ j ∈ range k, b^j) ≡ k [MOD d] := by
  induction k with
  | zero => simp [Nat.ModEq]
  | succ k ih =>
    rw [sum_range_succ]
    exact ih.add (by simpa using hb.pow k)

/-- Pair consecutive powers in a geometric sum of even length. -/
theorem succ_dvd_sum_even (p k : ℕ) :
    p + 1 ∣ ∑ i ∈ range (2 * k), p ^ i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, sum_range_succ, sum_range_succ, add_assoc,
      pow_succ p (2 * k), add_comm (p ^ (2 * k)) _, ← Nat.mul_succ]
    exact dvd_add ih (dvd_mul_left _ _)

/-- Dittmer's Lemma 1.5 for arbitrary indexed odd natural bases.
The distinguished slot is unique even when some bases are repeated. -/
theorem formal_euler_exponents {ι : Type*} [DecidableEq ι] (s : Finset ι) (b e : ι → ℕ)
    (hb : ∀ i ∈ s, Odd (b i))
    (hbal : formalSigma s b e = 2 * ∏ i ∈ s, b i ^ e i) :
    ∃ i ∈ s, b i % 4 = 1 ∧ e i % 4 = 1 ∧ ∀ j ∈ s, j ≠ i → Even (e j) := by
  let N := ∏ i ∈ s, b i ^ e i
  let f := fun i => ∑ j ∈ range (e i+1), b i ^ j
  have hN : Odd N := prod_induction _ Odd (fun _ _ => Odd.mul) odd_one (fun i hi => (hb i hi).pow)
  change s.prod f = 2*N at hbal
  have h4 : ¬4 ∣ 2*N := by have := hN.not_two_dvd_nat; omega
  obtain ⟨i, hi, h2⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff f).mp
    (show 2 ∣ s.prod f by rw [hbal]; exact dvd_mul_right _ _)
  have hlocal : ¬4 ∣ f i := fun hd => h4 (hd.trans (hbal ▸ dvd_prod_of_mem f hi))
  have parity (j : ι) (hj : j ∈ s) : f j % 2 = (e j + 1) % 2 :=
    geom_modEq_of_one (Nat.odd_iff.mp (hb j hj)) _
  have he2 : e i % 2 = 1 := by have := parity i hi; omega
  have hi4 : b i % 4 = 1 := by
    by_contra hn
    have := Nat.odd_iff.mp (hb i hi)
    have hd : 4 ∣ b i + 1 := by omega
    obtain ⟨t, ht⟩ := Nat.odd_iff.mpr he2
    apply hlocal
    change 4 ∣ ∑ j ∈ range (e i + 1), b i ^ j
    rw [show e i + 1 = 2*(t+1) by omega]
    exact hd.trans (succ_dvd_sum_even _ _)
  have hres : f i % 4 = (e i+1) % 4 := geom_modEq_of_one hi4 _
  refine ⟨i, hi, hi4, by omega, ?_⟩
  intro j hj hji
  have hodd : ¬2 ∣ f j := by
    intro h
    apply h4
    rw [← hbal, ← mul_prod_erase _ _ hi]
    exact Nat.mul_dvd_mul h2 (h.trans (dvd_prod_of_mem f (mem_erase.mpr ⟨hji,hj⟩)))
  have := parity j hj
  exact Nat.even_iff.mpr (by omega)

end OddPerfect
