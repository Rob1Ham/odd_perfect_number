module

public import OddPerfect.SmallIndexWitnesses
public import OddPerfect.FermatSmallBound
public import OddPerfect.FermatIndexDivisorCount
import OddPerfect.Cuts
import OddPerfect.Abundance
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- The Euler index 135 would require at least sixteen divisors of its length,
while its prime-factor weight allows at most nine. -/
theorem euler_index_ne_135 {N q a m i : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (hqm : ¬q ∣ m) (hform : N=q^a*m^2)
    (hl : sigma 1 (m^2)=q^a*i) (hr : sigma 1 (q^a)*i=2*m^2) : i ≠ 135 := by
  rintro rfl
  have ha : Odd a := Nat.odd_iff.mpr (by omega)
  have hs : ∀ p ∈ (135:ℕ).primeFactors, ∃ k : ℕ, p-1=2^k := by
    intro p hp
    have hF : (135:ℕ).primeFactors={3,5} := by decide +kernel
    rw [hF,Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl|rfl
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
  have hu := euler_index_weight_bounds (B:=6) (T:=4) hN ho hq ha hqm hform hl hr (by decide +kernel) (by decide)
  have hd := sixteen_le_euler_length_divisors_of_fermat_valuations (p:=5) (r:=3) ho hq hq4 ha hform
    (by decide) hs hl hr (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  omega

/-- The product bound and the small-index certificates leave the Euler index
at least 165. -/
theorem euler_component_index_ge_165 {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (hqm : ¬q ∣ m) (hform : N=q^a*m^2) :
    165*q^a < 2*m^2 ∧ 165 ≤ sigma 1 (m^2)/q^a := by
  have ha : Odd a := Nat.odd_iff.mpr (by omega)
  have hqb : ¬q ∣ m^2 := fun h => hqm (hq.dvd_of_dvd_pow h)
  obtain ⟨i,_,hl,hr,_⟩ := exists_component_index hN hq hform hqb
  have hquot : sigma 1 (m^2)/q^a=i := by rw [hl,Nat.mul_div_cancel_left i (Nat.pow_pos hq.pos)]
  have hio : Odd i := by
    rcases component_index_parity_bound hN ho hq ha.pos hform hqb hl hr with h|h
    · exact h.2.1
    · have := Nat.even_iff.mp h.1; omega
  have hω := three_le_euler_index_total_prime_count hN ho hq ha4 hqm hform
  have h63 := (euler_component_index_ge_sixty_three hN ho hq hq4 ha4 hqm hform).2
  rw [hquot] at hω h63 ⊢
  have h165 : 165 ≤ i := by
    by_contra! hsmall
    have hcases : ∀ z : Fin 165, Odd (z:ℕ) → 63 ≤ (z:ℕ) → 3 ≤ cardFactors (z:ℕ) →
        (z:ℕ) ∈ ({45,75,99,117,153,171,261,275,279}:Finset ℕ) ∨ (z:ℕ) ∈ ({63,147,175,245}:Finset ℕ) ∨
          (z:ℕ)=81 ∨ (z:ℕ)=105 ∨ (z:ℕ)=125 ∨ (z:ℕ)=135 := by decide +kernel
    rcases hcases ⟨i,hsmall⟩ hio h63 hω with h|h|h|h|h|h
    · exact euler_index_avoids_two_component_witnesses hN ho hq hq4 ha4 hqm hform hl hr h
    · exact euler_index_avoids_pure_sources_mod_seven hN ho hq hq4 ha4 hqm hform hl hr h
    · have hag : 1<a := by
        by_contra! h1
        have ha1 : a=1 := by omega
        have := euler_exponent_one_index_ge_22971 hN ho hq hqm (by simpa [ha1] using hform)
        simp only [ha1,pow_one] at hquot
        omega
      exact euler_index_not_square_of_exponent_gt_one hN ho hq hq4 ha4 hag hqm hform ⟨9,hquot.trans h⟩
    · have hd : i ∣ m^2 := (Nat.coprime_two_right.mpr hio).dvd_of_dvd_mul_left (hr ▸ dvd_mul_left _ _)
      exact not_dvd_105_of_odd_perfect hN ho (h ▸ hd.trans (hform ▸ dvd_mul_left _ _))
    · exact euler_component_index_ne_fermat_prime_cube hN ho hq ha4 hqm hform (p:=5) (k:=2)
        (by decide) (by decide) (by decide) hl hr h
    · exact euler_index_ne_135 hN ho hq hq4 ha4 hqm hform hl hr h
  refine ⟨?_,h165⟩
  calc
    165*q^a < 165*sigma 1 (q^a) := Nat.mul_lt_mul_of_pos_left (self_lt_sigma_of_one_lt (one_lt_pow₀ hq.one_lt ha.pos.ne')) (by decide)
    _ ≤ sigma 1 (q^a)*i := by rw [Nat.mul_comm 165]; exact Nat.mul_le_mul_left _ h165
    _ = _ := hr

end OddPerfect
