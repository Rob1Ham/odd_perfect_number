module

public import OddPerfect.EulerIndexSieve
public import OddPerfect.IndexBound165
import OddPerfect.Abundance
import OddPerfect.Cuts
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction Finset

private def indexRows : List IndexSieve.Row := [
  ⟨165,5,5⟩, ⟨171,3,3⟩, ⟨175,5,5⟩, ⟨189,3,7⟩, ⟨195,5,5⟩, ⟨207,3,3⟩,
  ⟨231,3,7⟩, ⟨243,3,3⟩, ⟨245,5,5⟩, ⟨255,5,5⟩, ⟨261,3,3⟩, ⟨273,7,13⟩,
  ⟨275,5,5⟩, ⟨279,3,3⟩, ⟨285,5,5⟩, ⟨297,3,11⟩, ⟨325,5,5⟩, ⟨333,3,3⟩]

set_option maxRecDepth 10000 in
private theorem indexRows_valid : ∀ z : Fin indexRows.length, (indexRows.get z).valid := by decide +kernel

/-- The two-source index sieve gives the unconditional Euler index bound 343
and the strict size inequality `343 q^a < 2 m²`. -/
theorem euler_component_index_ge_343 {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (hqm : ¬q ∣ m) (hform : N=q^a*m^2) :
    343*q^a < 2*m^2 ∧ 343 ≤ sigma 1 (m^2)/q^a := by
  have hao : Odd a := Nat.odd_iff.mpr (by omega)
  have hqb : ¬q ∣ m^2 := fun h => hqm (hq.dvd_of_dvd_pow h)
  obtain ⟨i,_,hl,hr,_⟩ := exists_component_index hN hq hform hqb
  have hquot : sigma 1 (m^2)/q^a=i := by rw [hl,Nat.mul_div_cancel_left i (Nat.pow_pos hq.pos)]
  have hio : Odd i := by
    rcases component_index_parity_bound hN ho hq hao.pos hform hqb hl hr with h|h
    · exact h.2.1
    · have := Nat.even_iff.mp h.1; omega
  have hω := three_le_euler_index_total_prime_count hN ho hq ha4 hqm hform
  have h165 := (euler_component_index_ge_165 hN ho hq hq4 ha4 hqm hform).2
  rw [hquot] at hω h165 ⊢
  have h343 : 343 ≤ i := by
    by_contra! hsmall
    have ha : 1<a := by
      by_contra! h
      have h1 : a=1 := by omega
      have := euler_exponent_one_index_ge_22971 hN ho hq hqm (by simpa [h1] using hform)
      simp only [h1,pow_one] at hquot
      omega
    have check : ∀ z : Fin 343, Odd (z:ℕ) → 165 ≤ (z:ℕ) → 3 ≤ cardFactors (z:ℕ) →
        105 ∣ (z:ℕ) ∨ (z:ℕ)=225 ∨ ∃ t : Fin indexRows.length, (z:ℕ)=(indexRows.get t).index := by decide +kernel
    rcases check ⟨i,hsmall⟩ hio h165 hω with hd|heq|⟨z,hz⟩
    · have hiD : i ∣ m^2 := (Nat.coprime_two_right.mpr hio).dvd_of_dvd_mul_left (hr ▸ dvd_mul_left _ _)
      exact not_dvd_105_of_odd_perfect hN ho (hd.trans (hiD.trans (hform ▸ dvd_mul_left _ _)))
    · exact euler_index_not_square_of_exponent_gt_one hN ho hq hq4 ha4 ha hqm hform ⟨15,hquot.trans heq⟩
    · exact IndexSieve.excludes_of_valid_row hN ho hq hq4 ha4 ha hqm hform hl hr hio _ (indexRows_valid z) hz
  refine ⟨?_,h343⟩
  calc
    343*q^a < 343*sigma 1 (q^a) := Nat.mul_lt_mul_of_pos_left (self_lt_sigma_of_one_lt (one_lt_pow₀ hq.one_lt hao.pos.ne')) (by decide)
    _ ≤ sigma 1 (q^a)*i := by rw [Nat.mul_comm 343]; exact Nat.mul_le_mul_left _ h343
    _ = _ := hr

end OddPerfect
