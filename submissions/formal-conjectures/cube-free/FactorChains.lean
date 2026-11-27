module

public import Mathlib.Tactic.NormNum.Prime

/-!
# Finite factor chains when the exceptional factor is a prime square

Let `S p` mean that the prime `p` belongs to the support of a Descartes number.
In the cube-free square case, every ordinary prime contributes `p² + p + 1`
to the divisor sum. The exceptional prime `r` contributes `(r² + 1) / 2`
to the odd part of the balance equation. Three distinct ordinary primes
congruent to 1 modulo 3 would contribute at least three factors of 3.
-/

public section

namespace DescartesSubmission

set_option maxRecDepth 4096 in
private theorem prime_1155061 : Nat.Prime 1155061 := by norm_num

set_option maxRecDepth 4096 in
/-- Starting from 3, ordinary and exceptional divisibility force more
ordinary sources of 3 than the cube-free balance equation can accommodate. -/
theorem factor_chain_contradiction {S : ℕ → Prop} {r : ℕ} (h3 : S 3)
    (ordinary : ∀ {p q : ℕ}, S p → p ≠ r → q.Prime → q ≠ 2 → q ∣ p^2 + p + 1 → S q)
    (exceptional : ∀ {q : ℕ}, q.Prime → q ≠ 2 → q ∣ (r^2 + 1) / 2 → S q)
    (capacity : ∀ {a b c : ℕ}, S a → S b → S c → a ≠ r → b ≠ r → c ≠ r →
      a ≠ b → a ≠ c → b ≠ c → a % 3 = 1 → b % 3 = 1 → c % 3 = 1 → False) : False := by
  by_cases h3r : 3 = r
  · subst r
    have h5 : S 5 := exceptional (by norm_num) (by decide) (by decide)
    have h31 : S 31 := ordinary h5 (by decide) (by norm_num) (by decide) (by decide)
    have h331 : S 331 := ordinary h31 (by decide) (by norm_num) (by decide) (by decide)
    have h7 : S 7 := ordinary h331 (by decide) (by norm_num) (by decide) (by decide)
    apply capacity h31 h331 h7 <;> decide

  have h13 : S 13 := ordinary h3 h3r (by decide) (by decide) (by decide)
  by_cases h13r : 13 = r
  · subst r
    have h5 : S 5 := exceptional (by norm_num) (by decide) (by decide)
    have h17 : S 17 := exceptional (by norm_num) (by decide) (by decide)
    have h31 : S 31 := ordinary h5 (by decide) (by norm_num) (by decide) (by decide)
    have h307 : S 307 := ordinary h17 (by decide) (by norm_num) (by decide) (by decide)
    have h331 : S 331 := ordinary h31 (by decide) (by norm_num) (by decide) (by decide)
    apply capacity h31 h307 h331 <;> decide

  have h61 : S 61 := ordinary h13 h13r (by decide) (by decide) (by decide)
  by_cases h61r : 61 = r
  · subst r
    have h1861 : S 1861 := exceptional (by norm_num) (by decide) (by decide)
    have h1155061 : S 1155061 := ordinary h1861 (by decide) prime_1155061 (by decide) (by decide)
    apply capacity h13 h1861 h1155061 <;> decide

  have h97 : S 97 := ordinary h61 h61r (by decide) (by decide) (by decide)
  by_cases h97r : 97 = r
  · subst r
    have h5 : S 5 := exceptional (by norm_num) (by decide) (by decide)
    have h31 : S 31 := ordinary h5 (by decide) (by norm_num) (by decide) (by decide)
    apply capacity h13 h61 h31 <;> decide

  exact capacity h13 h61 h97 h13r h61r h97r
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end DescartesSubmission
