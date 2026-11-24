module

public import OddPerfect.SemiprimeIndex
import OddPerfect.Cuts

public section

namespace OddPerfect

open ArithmeticFunction

/-- The Euler index has at least three prime factors counted with multiplicity. -/
theorem three_le_euler_index_total_prime_count {N q a m : ℕ} (hN : Nat.Perfect N)
    (ho : Odd N) (hq : q.Prime) (ha4 : a % 4 = 1) (hqm : ¬ q ∣ m) (hform : N=q^a*m^2) :
    3 ≤ cardFactors (sigma 1 (m^2) / q^a) := by
  have hao : Odd a := Nat.odd_iff.mpr (by omega)
  have hqb : ¬ q ∣ m^2 := fun h => hqm (hq.dvd_of_dvd_pow h)
  obtain ⟨i, _, hleft, hright, _⟩ := exists_component_index hN hq hform hqb
  rw [hleft, Nat.mul_div_cancel_left i (Nat.pow_pos hq.pos)]
  obtain ⟨hio,hi3⟩ : Odd i ∧ 3 ≤ i := by
    rcases component_index_parity_bound hN ho hq hao.pos hform hqb hleft hright with h | h
    · exact h.2
    · have := Nat.even_iff.mp h.1
      omega
  have hnot := component_index_not_prime hN ho hq hao.pos hform hqb hleft hright
  obtain ⟨p, hp, hpi⟩ := Nat.exists_prime_and_dvd (by omega : i ≠ 1)
  obtain ⟨r, heq⟩ := hpi
  have hrpos : 0 < r := by by_contra! h; simp [show r=0 by omega] at heq; omega
  have hr1 : 1 < r := by
    by_contra! h
    apply hnot
    simpa [heq, show r=1 by omega] using hp
  by_contra! hc
  rw [heq, cardFactors_mul hp.ne_zero hrpos.ne', cardFactors_apply_prime hp] at hc
  have hr := cardFactors_eq_one_iff_prime.mp (by have := cardFactors_pos_iff_one_lt.mpr hr1; omega : cardFactors r=1)
  by_cases hpr : p=r
  · exact component_index_ne_prime_square hN ho hq hao.pos hform hqb hleft hright hp (by simpa [pow_two, ← hpr] using heq)
  · exact euler_component_index_ne_semiprime hN ho hq ha4 hqm hform hp hr
      (hio.of_dvd_nat (heq ▸ dvd_mul_right _ _)) (hio.of_dvd_nat (heq ▸ dvd_mul_left _ _)) hpr hleft hright heq

/-- The Euler index is at least 27, giving the strict size inequality `27 q^a < 2 m²`. -/
theorem euler_component_index_ge_twenty_seven {N q a m : ℕ} (hN : Nat.Perfect N)
    (ho : Odd N) (hq : q.Prime) (ha4 : a % 4 = 1) (hqm : ¬ q ∣ m) (hform : N=q^a*m^2) :
    27 * q^a < 2*m^2 ∧ 27 ≤ sigma 1 (m^2) / q^a := by
  have hao : Odd a := Nat.odd_iff.mpr (by omega)
  have hqb : ¬ q ∣ m^2 := fun h => hqm (hq.dvd_of_dvd_pow h)
  obtain ⟨i, _, hleft, hright, _⟩ := exists_component_index hN hq hform hqb
  have hdiv : sigma 1 (m^2) / q^a = i := by rw [hleft, Nat.mul_div_cancel_left i (Nat.pow_pos hq.pos)]
  have hc := three_le_euler_index_total_prime_count hN ho hq ha4 hqm hform
  rw [hdiv] at hc ⊢
  have hi : Odd i := by
    rcases component_index_parity_bound hN ho hq hao.pos hform hqb hleft hright with h | h
    · exact h.2.1
    · have := Nat.even_iff.mp h.1; omega
  have h27 : 27 ≤ i := by
    by_contra! h
    have hcheck : ∀ z : Fin 27, Odd (z:ℕ) → cardFactors (z:ℕ) < 3 := by decide +kernel
    exact (hcheck ⟨i,h⟩ hi).not_ge hc
  refine ⟨?_, h27⟩
  calc
    27 * q^a < 27 * sigma 1 (q^a) := Nat.mul_lt_mul_of_pos_left
      (self_lt_sigma_of_one_lt (one_lt_pow₀ hq.one_lt hao.pos.ne')) (by decide)
    _ ≤ sigma 1 (q^a)*i := by rw [Nat.mul_comm 27]; exact Nat.mul_le_mul_left _ h27
    _ = _ := hright

end OddPerfect
