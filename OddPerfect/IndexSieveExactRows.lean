module

public import OddPerfect.IndexSieveBudget
public import OddPerfect.IndexSieveFastLengths
import OddPerfect.FewPrimes
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect.IndexSieve

open ArithmeticFunction Finset

/-- A support bound based on the index weight, with the smaller threshold
three available for weights at most four. -/
@[expose] def supportBound (i : ℕ) : ℕ :=
  let B := i.primeFactors.card+cardFactors i
  (if B≤4 then 2 else 3)+B

/-- With at most seven prime divisors, an odd perfect number must contain
three, which cannot be the Euler prime. -/
@[expose] def EligibleBase (i p : ℕ) : Prop :=
  p ∈ i.primeFactors ∨ p=3 ∧ supportBound i<8

instance (i p : ℕ) : Decidable (EligibleBase i p) :=
  inferInstanceAs (Decidable (p ∈ i.primeFactors ∨ p=3 ∧ supportBound i<8))

/-- A row for the exact-length two-source criterion. -/
@[expose] def Row.exactValid (w : Row) : Prop :=
  EligibleBase w.index w.firstPrime ∧ EligibleBase w.index w.secondPrime ∧
    4+(w.index.primeFactors.card+cardFactors w.index)<2^4 ∧
    ¬BudgetCompatible w.index w.firstPrime w.secondPrime (supportBound w.index/2) (residueModulus w.index)

instance (w : Row) : Decidable w.exactValid :=
  inferInstanceAs (Decidable (EligibleBase w.index w.firstPrime ∧ EligibleBase w.index w.secondPrime ∧
    4+(w.index.primeFactors.card+cardFactors w.index)<2^4 ∧
    ¬BudgetCompatible w.index w.firstPrime w.secondPrime (supportBound w.index/2) (residueModulus w.index)))

/-- Fast variant of `sourceOptions` using `fastFullLengths`. -/
@[expose] def fastSourceOptions (i p H M : ℕ) : Finset (ℕ × ℕ) :=
  ((fastFullLengths i p H).image fun d =>
    let b := repunit p d
    (b.gcd i, residual b i)).filter fun z =>
      z.2.Coprime i ∧ z.2 % M = 1 ∧ (z.2 ≤ 100000 → z.2.primeFactors.card ≤ 1) ∧
      ∀ u : Fin 14, (u : ℕ).Prime → (u : ℕ) ∣ z.2 → (u : ℕ) % M = 1

theorem fastSourceOptions_eq (i p H M : ℕ) :
    fastSourceOptions i p H M = sourceOptions i p H M := by
  simp only [fastSourceOptions, sourceOptions, fastFullLengths_eq]

/-- Fast boolean check equivalent to `Row.exactValid`, precomputing `primeFactors`,
`supportBound`, and reusing `sp` when `firstPrime = secondPrime`. -/
@[expose] def Row.fastExactValidBool (w : Row) : Bool :=
  let pf := w.index.primeFactors
  let B := pf.card + cardFactors w.index
  let sb := (if B ≤ 4 then 2 else 3) + B
  let elig (p : ℕ) : Bool := decide (p ∈ pf) || decide (p = 3 ∧ sb < 8)
  let H := sb / 2
  let M := residueModulus w.index
  let sp := fastSourceOptions w.index w.firstPrime H M
  let sr := if w.firstPrime = w.secondPrime then sp else fastSourceOptions w.index w.secondPrime H M
  let compat : Bool := decide (∃ x ∈ sp, ∃ y ∈ sr,
    (w.firstPrime = w.secondPrime ∨ x.1 * y.1 ∣ w.index) ∧
    (x.2 = 1 ∨ y.2 = 1 ∨ x.2.gcd y.2 ≠ 1))
  elig w.firstPrime && elig w.secondPrime && decide (4 + B < 2^4) && !compat

theorem Row.fastExactValidBool_eq (w : Row) :
    w.fastExactValidBool = true ↔ w.exactValid := by
  unfold Row.fastExactValidBool Row.exactValid EligibleBase supportBound BudgetCompatible
  dsimp only
  by_cases h : w.firstPrime = w.secondPrime <;>
    simp only [h, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_true_eq, decide_eq_false_iff_not, fastSourceOptions_eq, and_assoc]

theorem excludes_of_exact_valid_row {N q a m i : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (ha : 1<a) (hqm : ¬q ∣ m) (hform : N=q^a*m^2)
    (hl : sigma 1 (m^2)=q^a*i) (hr : sigma 1 (q^a)*i=2*m^2) (hio : Odd i)
    (w : Row) (hw : w.exactValid) : i ≠ w.index := by
  intro heq
  obtain ⟨hpE,hrE,hweight,hbad⟩ := hw
  rw [←heq] at hpE hrE hweight hbad
  have hao : Odd a := Nat.odd_iff.mpr (by omega)
  have hmo := ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2≠0)).trans (dvd_mul_left _ _))
  have hqo := ho.of_dvd_nat (hform ▸ (dvd_pow_self q hao.pos.ne').trans (dvd_mul_right _ _))
  have hqi : q.Coprime i := hq.coprime_iff_not_dvd.mpr (fun h => hqm (hq.dvd_of_dvd_pow
    ((Nat.coprime_two_right.mpr hqo).dvd_of_dvd_mul_left (hr ▸ h.trans (dvd_mul_left _ _)))))
  have hbound : (a+1).divisors.card ≤ supportBound i ∧ N.primeFactors.card ≤ supportBound i := by
    unfold supportBound
    dsimp only
    split_ifs with h
    · have h3 : 3+(i.primeFactors.card+cardFactors i)<2^3 := by omega
      have := euler_index_weight_bounds hN ho hq hao hqm hform hl hr (Nat.le_refl _) h3
      omega
    · have := euler_index_weight_bounds hN ho hq hao hqm hform hl hr (Nat.le_refl _) hweight
      omega
  have eligible (p : ℕ) (hp : EligibleBase i p) : p ∈ m.primeFactors := by
    rcases hp with hp|⟨rfl,h⟩
    · have hpr := Nat.prime_of_mem_primeFactors hp
      have hd := Nat.dvd_of_mem_primeFactors hp
      have hdm : p ∣ m := hpr.dvd_of_dvd_pow ((Nat.coprime_two_right.mpr (hio.of_dvd_nat hd)).dvd_of_dvd_mul_left
        (hr ▸ hd.trans (dvd_mul_left _ _)))
      exact Nat.mem_primeFactors.mpr ⟨hpr,hdm,hmo.pos.ne'⟩
    · have h3 : 3 ∣ N := by
        by_contra h3
        have := eight_le_distinct_prime_factor_count_of_three_free ho hN h3
        omega
      have hpr : Nat.Prime 3 := by decide
      have h3m := (hpr.dvd_mul.mp (hform ▸ h3)).resolve_left
        (fun h => by have := (Nat.prime_dvd_prime_iff_eq hpr hq).mp (hpr.dvd_of_dvd_pow h); omega)
      exact Nat.mem_primeFactors.mpr ⟨hpr,hpr.dvd_of_dvd_pow h3m,hmo.pos.ne'⟩
  obtain ⟨hM,hqM⟩ := euler_modulus hN ho hq hq4 ha4 ha hqm hform hl
  exact hbad (budget_compatible_of_euler_index hq hao hmo.pos hmo hio hqi hM hqM (eligible _ hpE)
    (eligible _ hrE) (by omega) hl hr)

end OddPerfect.IndexSieve
