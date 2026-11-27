module

public import OddPerfect.EvenIndexCostTail
import Mathlib.Algebra.Order.Ring.Abs

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- The four remaining multiples of 16 below 256 and their
cost and exceptional-prime budgets. -/
@[expose] def indexCost (j : ℕ) : ℕ := if j=112 then 2400 else if j=240 then 510 else 400

@[expose] def indexCostExceptions (j : ℕ) : Finset ℕ :=
  if j=96 then {7,11,19} else if j=112 then {3,11,19,23,43}
  else if j=192 then {11,19,43,97} else {11,19,29}

set_option maxRecDepth 10000
set_option maxHeartbeats 0

private theorem costCheck96 : SourceCostCheck 96 400 245 {7,11,19} := by decide +kernel
private theorem costCheck112 : SourceCostCheck 112 2400 245 {3,11,19,23,43} := by decide +kernel
private theorem costCheck192 : SourceCostCheck 192 400 245 {11,19,43,97} := by decide +kernel
private theorem costCheck240 : SourceCostCheck 240 510 245 {11,19,29} := by decide +kernel

private theorem costCheck_of_case {j : ℕ} (h : j=96 ∨ j=112 ∨ j=192 ∨ j=240) :
    SourceCostCheck j (indexCost j) 245 (indexCostExceptions j) := by
  rcases h with rfl|rfl|rfl|rfl
  · exact costCheck96
  · exact costCheck112
  · exact costCheck192
  · exact costCheck240

theorem low_even_index_source_cost {q p s u r v : ℕ} (hp : p.Prime) (hs : Odd s)
    (hr : r ∈ s.primeFactors) (he : r∉indexCostExceptions (2*u)) (hv : Odd v) (hle : v≤2*u)
    (hj : 2*u=96 ∨ 2*u=112 ∨ 2*u=192 ∨ 2*u=240)
    (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2)
    (hout : sigma 1 (r^(2*s.factorization r))=p^v) : indexCost (2*u)≤v*(r-1) := by
  have hp' := Nat.prime_of_mem_primeFactors hr
  have hd := Nat.dvd_of_mem_primeFactors hr
  by_cases hcut : r<245
  · exact source_cost_of_check _ (costCheck_of_case hj) hp hp' (hs.of_dvd_nat hd) hd he hcut hv hle hσq hplus hout
  have hv3 := three_le_even_index_large_source_multiplicity hp hp' hd (by omega) hv hσq hplus hout
  by_cases h112 : 2*u=112
  · have hu : u=56 := by omega
    subst u
    have hv11 := even_index_112_tail_multiplicity hp hp' hd (by omega) hv hσq hplus hout
    change 2400≤_
    exact (by decide : 2400≤11*244).trans (Nat.mul_le_mul hv11 (by omega))
  · have hmax : indexCost (2*u)≤510 := by simp [indexCost,h112]; split <;> decide
    exact hmax.trans ((by decide : 510≤3*244).trans (Nat.mul_le_mul hv3 (by omega)))

/-- The limiting product of all exceptional sources, both distinguished
bases, and the regular-source budget is strictly below two in each case. -/
theorem low_even_index_envelope_values {j : ℕ} (h : j=96 ∨ j=112 ∨ j=192 ∨ j=240) :
    primeAbundancyLimit 61*primeAbundancyLimit 3721*
      ((∏ r ∈ indexCostExceptions j,primeAbundancyLimit r)*(1+1/(indexCost j:ℚ))^j)<2 := by
  rcases h with rfl|rfl|rfl|rfl <;> decide +kernel

end OddPerfect
