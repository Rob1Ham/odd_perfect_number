module

public import OddPerfect.IndexSupport
public import OddPerfect.Dickson
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! Dris–Luca Theorem 1.2 via component-length divisor counts and a constructive
uniform bound for fixed prime-support size. -/

public section

namespace OddPerfect

open ArithmeticFunction

/-- An explicit bound for odd perfect numbers having a component index at
most `K`. The recursion defining `productLabelBound` is computable. -/
def componentIndexBound (K : ℕ) : ℕ :=
  let k := 4 * Nat.log 2 K + 4
  (max 1 (productLabelBound (2*k) (2*k) 1)) ^ k

/-- The effective bound in Dris–Luca Theorem 1.2, with an inclusive integral
threshold. The selected exact component can have either parity of exponent. -/
theorem le_of_bounded_component_index {N q a K : ℕ} (hN : Nat.Perfect N) (ho : Odd N)
    (hq : Nat.Prime q) (ha : 0 < a) (hd : q^a ∣ N) (hex : ¬ q^(a+1) ∣ N)
    (hK : sigma 1 (N / q^a) / q^a ≤ K) : N ≤ componentIndexBound K := by
  obtain ⟨b, hb⟩ := hd
  have hqb : ¬ q ∣ b := by
    intro h
    apply hex
    rw [hb, pow_succ]
    exact Nat.mul_dvd_mul_left _ h
  obtain ⟨i, _, hleft, hright, _⟩ := exists_component_index hN hq hb hqb
  rw [hb, Nat.mul_div_cancel_left b (Nat.pow_pos hq.pos), hleft,
    Nat.mul_div_cancel_left i (Nat.pow_pos hq.pos)] at hK
  have hc := prime_count_le_of_component_index hN ho hq ha hb hqb hleft hright
  have hlog := Nat.log_mono_right (b := 2) hK
  exact le_of_bounded_prime_count ho hN (by omega : N.primeFactors.card ≤ 4 * Nat.log 2 K + 4)

/-- Dris–Luca Theorem 1.2, with arbitrary real threshold and any exact
positive prime-power component. -/
theorem finite_of_bounded_component_index (K : ℝ) :
    Set.Finite {N : ℕ | Odd N ∧ Nat.Perfect N ∧ ∃ q a : ℕ,
      Nat.Prime q ∧ 0 < a ∧ q^a ∣ N ∧ ¬ q^(a+1) ∣ N ∧
        ((sigma 1 (N / q^a) / q^a : ℕ) : ℝ) < K} := by
  apply (Set.finite_le_nat (componentIndexBound ⌈K⌉₊)).subset
  rintro N ⟨ho, hN, q, a, hq, ha, hd, hex, hK⟩
  apply le_of_bounded_component_index hN ho hq ha hd hex
  exact_mod_cast hK.le.trans (Nat.le_ceil K)

end OddPerfect
