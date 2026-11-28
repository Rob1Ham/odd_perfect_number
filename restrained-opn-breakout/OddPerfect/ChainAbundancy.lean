module

public import OddPerfect.FactorBudget
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Ring.Abs

/-! Bounding the smallest unassigned prime by the remaining abundancy and count. -/

public section

namespace OddPerfect.FactorBudget

open ArithmeticFunction Finset

/-- The limiting product strictly dominates the exact abundancy of any m > 1. -/
theorem abundancy_lt_prod_limits {m : ℕ} (hm : 1 < m) :
    ((sigma 1 m : ℕ) : ℚ) / (m : ℚ) < m.primeFactors.prod primeAbundancyLimit := by
  let f (p : ℕ) : ℚ := ((sigma 1 (p ^ m.factorization p) : ℕ) : ℚ) / (p ^ m.factorization p : ℕ)
  have hm0 : m ≠ 0 := by omega
  have heq : m.primeFactors.prod f = ((sigma 1 m : ℕ) : ℚ) / (m : ℚ) := by
    unfold f
    have hsum : (∏ p ∈ m.primeFactors, sigma 1 (p ^ m.factorization p)) = sigma 1 m :=
      (isMultiplicative_sigma.multiplicative_factorization _ hm0).symm
    rw [prod_div_distrib, ← Nat.cast_prod, ← Nat.cast_prod, ← Nat.prod_primeFactors_pow_factorization hm0, hsum]
  rw [← heq]
  apply prod_lt_prod_of_nonempty₀ _ _ (Nat.nonempty_primeFactors.mpr hm)
  · intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    exact div_pos (by exact_mod_cast sigma_pos 1 _ (pow_ne_zero _ hprime.ne_zero))
      (by exact_mod_cast Nat.pow_pos hprime.pos)
  · intro p hp
    have hr := Nat.prime_of_mem_primeFactors hp
    have hc := geom_sum_mul_add (p - 1) (m.factorization p + 1)
    rw [Nat.sub_add_cancel hr.one_lt.le, pow_succ, ← sigma_one_apply_prime_pow hr] at hc
    unfold primeAbundancyLimit
    rw [div_lt_div_iff₀ (by exact_mod_cast Nat.pow_pos hr.pos) (by exact_mod_cast Nat.sub_pos_of_lt hr.one_lt)]
    exact_mod_cast (show sigma 1 (p ^ m.factorization p) * (p - 1) < p * p ^ m.factorization p by
      rw [Nat.mul_comm p]
      omega)

private theorem product_le_with_large_prime {a L k m q : ℕ} (ha : 1 < a) (hL : 1 < L)
    (hq : q ∈ m.primeFactors) (hbig : L ≤ q) (hall : ∀ p ∈ m.primeFactors, a ≤ p)
    (hcard : m.primeFactors.card ≤ k) :
    m.primeFactors.prod primeAbundancyLimit ≤ primeAbundancyLimit L * primeAbundancyLimit a ^ (k-1) := by
  have hnon (p : ℕ) : 0 ≤ primeAbundancyLimit p := by unfold primeAbundancyLimit; positivity
  have hge : 1 ≤ primeAbundancyLimit a := by
    rw [primeAbundancyLimit, le_div_iff₀ (by exact_mod_cast Nat.sub_pos_of_lt ha), one_mul]
    exact_mod_cast Nat.sub_le a 1
  let t := m.primeFactors.erase q
  have ht : t.card ≤ k-1 := by have := card_erase_add_one hq; dsimp [t]; omega
  have hrest : t.prod primeAbundancyLimit ≤ primeAbundancyLimit a ^ (k-1) := by
    calc
      _ ≤ ∏ _ ∈ t, primeAbundancyLimit a := prod_le_prod₀ (fun p _ => hnon p)
        (fun p hp => primeAbundancyLimit_antitone ha (hall p (mem_of_mem_erase hp)))
      _ = primeAbundancyLimit a ^ t.card := by simp
      _ ≤ _ := pow_le_pow_right₀ hge ht
  rw [← mul_prod_erase m.primeFactors primeAbundancyLimit hq]
  exact mul_le_mul (primeAbundancyLimit_antitone hL hbig) hrest
    (prod_nonneg fun p _ => hnon p) (hnon L)

/-- The parity-adjusted maximum number of unassigned distinct primes. -/
@[expose] def Node.residualCap (s : Node) (budget : ℕ) : ℕ := (budget+1-s.spent-s.spent%2)/2

/-- If every remaining prime were at least a, and one were at least L, these
numerical tests would make the remaining abundancy too small. -/
@[expose] def Node.validAbundancyCut (s : Node) (budget a L g : ℕ) : Bool :=
  let n := s.residualCap budget - 1
  decide (1 < a ∧ 1 < L ∧ s.divisorSum < 2*s.component ∧
    (L ≤ a ∨ (1 < g ∧ g ∣ s.forcedPart ∧ g.Coprime (L-1).factorial)) ∧
    s.divisorSum * L * a ^ n ≤ 2*s.component*(L-1)*(a-1)^n)

/-- A valid cut forces a genuine unassigned prime strictly below the cutoff.
A coprime divisor g of the residual divisor sum can witness one large prime. -/
theorem exists_prime_below_abundancy_cut {s : Node} {N m B w a L g : ℕ}
    (H : Conditions N B w) (h : Realizes s N m) (test : s.validAbundancyCut B a L g = true) :
    ∃ p ∈ m.primeFactors, p < a := by
  obtain ⟨ha, hL, hdef, hgroup, hnum⟩ := of_decide_eq_true test
  have h0 : s.component ≠ 0 ∧ m ≠ 0 := mul_ne_zero_iff.mp (h.value ▸ H.odd.pos.ne')
  have hσ : s.divisorSum * sigma 1 m = 2*s.component*m := by
    rw [← h.sigma, ← isMultiplicative_sigma.map_mul_of_coprime h.coprime, ← h.value,
      sigma_one_apply, (Nat.perfect_iff_sum_divisors_eq_two_mul H.perfect.2).mp H.perfect,
      h.value, Nat.mul_assoc]
  have hm : 1 < m := by
    by_contra! hle
    have hm1 : m = 1 := by omega
    simp [hm1] at hσ
    omega
  by_contra! hall
  obtain ⟨q, hq, hbig⟩ : ∃ q ∈ m.primeFactors, L ≤ q := by
    rcases hgroup with hweak | ⟨hg, hgd, hcop⟩
    · obtain ⟨q, hq⟩ := Nat.nonempty_primeFactors.mpr hm
      exact ⟨q, hq, hweak.trans (hall q hq)⟩
    · obtain ⟨q, hprime, hqg⟩ := Nat.exists_prime_and_dvd (by omega : g ≠ 1)
      have hqm := hqg.trans (hgd.trans (forcedPart_dvd h H.perfect))
      refine ⟨q, Nat.mem_primeFactors.mpr ⟨hprime, hqm, h0.2⟩, ?_⟩
      by_contra! hlt
      have hd := Nat.dvd_gcd hqg (Nat.dvd_factorial hprime.pos (show q ≤ L-1 by omega))
      exact hprime.not_dvd_one (hcop.gcd_eq_one ▸ hd)
  have hcap : m.primeFactors.card ≤ s.residualCap B := by
    have hc := budget_bound H h (k := m.primeFactors.card) le_rfl
    have := le_max_left m.primeFactors.card (w-s.closed)
    unfold Node.residualCap
    omega
  have upper := (abundancy_lt_prod_limits hm).trans_le (product_le_with_large_prime ha hL hq hbig hall hcap)
  have hA : 0 < s.divisorSum := h.sigma ▸ sigma_pos 1 _ h0.1
  have hexact : ((sigma 1 m : ℕ) : ℚ) / m = (2*s.component : ℚ) / s.divisorSum := by
    rw [div_eq_div_iff (by exact_mod_cast h0.2) (by exact_mod_cast hA.ne')]
    exact_mod_cast (show sigma 1 m * s.divisorSum = 2*s.component*m by rw [mul_comm, hσ])
  rw [hexact] at upper
  apply upper.not_ge
  unfold primeAbundancyLimit
  rw [div_pow, div_mul_div_comm, div_le_div_iff₀ (mul_pos (by exact_mod_cast Nat.sub_pos_of_lt hL)
    (pow_pos (by exact_mod_cast Nat.sub_pos_of_lt ha) _)) (by exact_mod_cast hA)]
  exact_mod_cast (show L * a ^ (s.residualCap B-1) * s.divisorSum ≤
    2*s.component*((L-1)*(a-1)^(s.residualCap B-1)) by simpa only [mul_assoc, mul_comm, mul_left_comm] using hnum)

end OddPerfect.FactorBudget
