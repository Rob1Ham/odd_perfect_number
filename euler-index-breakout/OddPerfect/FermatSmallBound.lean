module

public import OddPerfect.EulerIndexMultiplicity
public import OddPerfect.FermatCubeIndex
public import OddPerfect.FermatMixedIndex
import OddPerfect.Cuts

public section

namespace OddPerfect

open ArithmeticFunction

/-- The smallest two odd numbers with at least three prime factors are
27 and 45. Their Fermat-supported exclusions raise the Euler bound to 63. -/
theorem euler_component_index_ge_sixty_three {N q a m : ℕ} (hN : Nat.Perfect N)
    (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (hqm : ¬q ∣ m) (hform : N=q^a*m^2) :
    63*q^a < 2*m^2 ∧ 63 ≤ sigma 1 (m^2)/q^a := by
  have ha : Odd a := Nat.odd_iff.mpr (by omega)
  have hqb : ¬q ∣ m^2 := fun h => hqm (hq.dvd_of_dvd_pow h)
  obtain ⟨i,_,hl,hr,_⟩ := exists_component_index hN hq hform hqb
  have hquot : sigma 1 (m^2)/q^a=i := by rw [hl,Nat.mul_div_cancel_left i (Nat.pow_pos hq.pos)]
  have hω := three_le_euler_index_total_prime_count hN ho hq ha4 hqm hform
  rw [hquot] at hω ⊢
  have hio : Odd i := by
    rcases component_index_parity_bound hN ho hq ha.pos hform hqb hl hr with h | h
    · exact h.2.1
    · have := Nat.even_iff.mp h.1; omega
  have hi : 63 ≤ i := by
    by_contra! h
    have check : ∀ z : Fin 63, Odd (z:ℕ) → 3 ≤ cardFactors (z:ℕ) → (z:ℕ)=3^3 ∨ (z:ℕ)=3^2*5 := by decide +kernel
    rcases check ⟨i,h⟩ hio hω with h | h
    · exact euler_component_index_ne_fermat_prime_cube hN ho hq ha4 hqm hform (p:=3) (k:=1) (by decide) (by decide) (by decide) hl hr h
    · exact euler_component_index_ne_fermat_square_times_prime hN ho hq hq4 ha4 hqm hform (p:=3) (r:=5) (k:=1) (j:=2)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hl hr h
  refine ⟨?_, hi⟩
  calc
    63*q^a < 63*sigma 1 (q^a) := Nat.mul_lt_mul_of_pos_left (self_lt_sigma_of_one_lt (one_lt_pow₀ hq.one_lt ha.pos.ne')) (by decide)
    _ ≤ sigma 1 (q^a)*i := by rw [Nat.mul_comm 63]; exact Nat.mul_le_mul_left _ hi
    _ = _ := hr

end OddPerfect
