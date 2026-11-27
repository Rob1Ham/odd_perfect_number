module

public import TothAnalytic
public import OddPerfect.TothTrillion

/-!
# Tóth's Theorem (`Tóth 2021, Theorem 1`)

Combines the analytical abundancy/multiplier engine (`TothAnalytic`) with the
verified finite branch cover up to `m ≤ 10^6` (`n = m² ≤ 10^12`) in
`OddPerfect/TothTrillion.lean` (`Part01`–`Part38`) to establish:

1. `toth_unique_odd_pair_below_trillion`:
   Among odd `n ≤ 10^12` and odd `x > 1`, `σ(n)(x + 1) = 2nx` holds iff
   `(n, x) = (9018009, 22021)` (Descartes's cofactor and composite pseudoprime).
2. `descartes_non_example_factor_gt_ten_pow_twelve`:
   Stated purely in terms of Mathlib predicates (matching Google DeepMind
   `formal-conjectures` `DescartesNumber.lean`), every odd Descartes factorization
   `m * w ≠ 198585576189` with composite `w > 1` coprime to `m` satisfies `10^12 < m`.
3. `deficientPerfect_below_trillion_iff`:
   Among odd `n ≤ 10^12`, `DeficientPerfectWith n d` holds iff `(n, d) = (9018009, 819)`.
-/

public section

namespace TothBreakout.Theorem

open OddPerfect ArithmeticFunction

/-- **Tóth (2021), Theorem 1 (stronger odd-multiplier singleton form)**:
Among odd `n ≤ 10^12` and odd `x > 1` (no coprimality or compositeness assumption),
`σ(n)(x + 1) = 2nx` holds if and only if `n = 9018009` and `x = 22021`. -/
theorem toth_unique_odd_pair_below_trillion {n x : ℕ}
    (hn : n ≤ 10 ^ 12) (hx : Odd x) (h1 : 1 < x) :
    TothPair n x ↔ n = 9018009 ∧ x = 22021 :=
  OddPerfect.toth_unique_odd_pair_below_trillion hn hx h1

/-- Singleton set characterization of all nontrivial odd Tóth pairs up to `10^12`. -/
theorem toth_odd_pair_set_below_trillion :
    {z : ℕ × ℕ | z.1 ≤ 10 ^ 12 ∧ Odd z.2 ∧ 1 < z.2 ∧ TothPair z.1 z.2} =
      {(9018009, 22021)} :=
  OddPerfect.toth_odd_pair_set_below_trillion

/-- **Tóth (2021), Theorem 1 (pure Mathlib Descartes-cofactor formulation)**:
For any odd Descartes factorization `m * w` with composite spoof factor `w > 1`
coprime to `m` and `σ(m) * (w + 1) = 2 * m * w`, if `m * w ≠ 198585576189` then
`10 ^ 12 < m`. -/
theorem descartes_non_example_factor_gt_ten_pow_twelve (m w : ℕ)
    (hf : (1 < w ∧ ¬ w.Prime) ∧ Odd (m * w) ∧ Nat.Coprime m w ∧
      ArithmeticFunction.sigma 1 m * (w + 1) = 2 * m * w)
    (hne : m * w ≠ 198585576189) : 10 ^ 12 < m := by
  obtain ⟨⟨hw, hnp⟩, hodd, hcop, hbal⟩ := hf
  obtain ⟨hm, hwo⟩ := Nat.odd_mul.mp hodd
  exact OddPerfect.trillion_lt_spoof_cofactor
    ⟨hm, hwo, hw, hnp, hcop, by simpa only [Nat.mul_assoc] using hbal⟩ hne

/-- Classification of all odd deficient-perfect numbers `(n, d)` with `n ≤ 10^12`. -/
theorem deficientPerfect_below_trillion_iff {n d : ℕ} (ho : Odd n) (hb : n ≤ 10 ^ 12) :
    DeficientPerfectWith n d ↔ n = 9018009 ∧ d = 819 :=
  OddPerfect.deficientPerfect_below_trillion_iff ho hb

end TothBreakout.Theorem
