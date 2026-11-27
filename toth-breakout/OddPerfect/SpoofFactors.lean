module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.FactorisationProperties

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- The formal divisor sum of the specified factorization, using BYU's geometric sum for
each base regardless of primality. -/
@[expose] def formalSigma {ι : Type*} (s : Finset ι) (b e : ι → ℕ) : ℕ :=
  ∏ i ∈ s, ∑ j ∈ range (e i + 1), b i ^ j

/-- A composite base supplies divisors outside its geometric progression, at every
positive exponent. Its smallest prime factor is one such divisor. -/
theorem geom_sum_lt_sigma_pow_of_composite {b e : ℕ} (hb : 1 < b) (hc : ¬ Nat.Prime b)
    (he : 0 < e) : (∑ j ∈ range (e + 1), b ^ j) < sigma 1 (b ^ e) := by
  let powers := (range (e + 1)).image (fun j => b ^ j)
  have hsub : powers ⊆ (b ^ e).divisors := by
    apply image_subset_iff.mpr
    intro j hj
    exact Nat.mem_divisors.mpr ⟨pow_dvd_pow _ (by simpa using hj), pow_ne_zero _ (by omega)⟩
  have hp := Nat.minFac_prime hb.ne'
  have hlt := (Nat.not_prime_iff_minFac_lt hb).mp hc
  have hmem : b.minFac ∈ (b ^ e).divisors :=
    Nat.mem_divisors.mpr ⟨(Nat.minFac_dvd b).trans (dvd_pow_self b he.ne'), pow_ne_zero _ (by omega)⟩
  have hskip : b.minFac ∉ powers := by
    intro hin
    obtain ⟨j, _, hj⟩ := mem_image.mp hin
    cases j with
    | zero => exact hp.ne_one (by simpa using hj.symm)
    | succ k =>
      have hle : b ≤ b ^ (k + 1) := by
        simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < b)
          (by omega : 1 ≤ k + 1)
      omega
  calc
    (∑ j ∈ range (e + 1), b ^ j) = ∑ x ∈ powers, x :=
      (sum_image (f := fun n : ℕ => n) (Nat.pow_right_injective hb).injOn).symm
    _ < ∑ x ∈ (b ^ e).divisors, x :=
      sum_lt_sum_of_subset hsub hmem hskip hp.pos (fun x _ _ => x.zero_le)
    _ = sigma 1 (b ^ e) := (sigma_one_apply _).symm

variable {ι : Type*} {s : Finset ι} {b e : ι → ℕ}

private theorem sigma_prod_coprime_powers (hcop : (s : Set ι).Pairwise (fun i j => (b i).Coprime (b j))) :
    sigma 1 (∏ i ∈ s, b i ^ e i) = ∏ i ∈ s, sigma 1 (b i ^ e i) :=
  isMultiplicative_sigma.map_prod _ _ (fun _ hi _ hj hij => (hcop hi hj hij).pow _ _)

/-- Any composite base strictly increases the true divisor sum of a positive pairwise
coprime factorization over its formal divisor sum. -/
theorem formalSigma_lt_of_composite
    (hb : ∀ i ∈ s, 1 < b i) (he : ∀ i ∈ s, 0 < e i)
    (hcop : (s : Set ι).Pairwise (fun i j => (b i).Coprime (b j)))
    (hc : ∃ i ∈ s, ¬ Nat.Prime (b i)) :
    formalSigma s b e < sigma 1 (∏ i ∈ s, b i ^ e i) := by
  rw [formalSigma, sigma_prod_coprime_powers hcop]
  apply prod_lt_prod₀
  · intro i hi
    exact sum_pos' (fun _ _ => Nat.zero_le _)
      ⟨0, mem_range.mpr (Nat.zero_lt_succ _), by simp⟩
  · intro i hi
    by_cases hp : Nat.Prime (b i)
    · exact (sigma_one_apply_prime_pow hp).symm.le
    · exact (geom_sum_lt_sigma_pow_of_composite (hb i hi) hp (he i hi)).le
  · obtain ⟨i, hi, hc'⟩ := hc
    exact ⟨i, hi, geom_sum_lt_sigma_pow_of_composite (hb i hi) hc' (he i hi)⟩

/-- With positive exponents and pairwise coprime bases exceeding one, primality of every
base characterizes agreement of the formal and true divisor sums. -/
theorem formalSigma_eq_iff_prime
    (hb : ∀ i ∈ s, 1 < b i) (he : ∀ i ∈ s, 0 < e i)
    (hcop : (s : Set ι).Pairwise (fun i j => (b i).Coprime (b j))) :
    formalSigma s b e = sigma 1 (∏ i ∈ s, b i ^ e i) ↔ ∀ i ∈ s, Nat.Prime (b i) := by
  constructor
  · intro h i hi
    by_contra hc
    exact (formalSigma_lt_of_composite hb he hcop ⟨i, hi, hc⟩).ne h
  · intro h
    rw [formalSigma, sigma_prod_coprime_powers hcop]
    exact prod_congr rfl (fun i hi => (sigma_one_apply_prime_pow (h i hi)).symm)

/-- Every formally perfect factorization in the coprime positive class with a composite
base evaluates to an abundant integer. -/
theorem abundant_of_formalSigma_eq_two_mul_of_composite
    (hb : ∀ i ∈ s, 1 < b i) (he : ∀ i ∈ s, 0 < e i)
    (hcop : (s : Set ι).Pairwise (fun i j => (b i).Coprime (b j)))
    (hbal : formalSigma s b e = 2 * ∏ i ∈ s, b i ^ e i)
    (hc : ∃ i ∈ s, ¬ Nat.Prime (b i)) : Nat.Abundant (∏ i ∈ s, b i ^ e i) := by
  apply Nat.abundant_iff_sum_divisors.mpr
  rw [← sigma_one_apply, ← hbal]
  exact formalSigma_lt_of_composite hb he hcop hc

/-- Coprimality matters even for prime bases. Treating the two threes in nine separately
overcounts its true divisor sum. -/
theorem repeated_prime_overcounts : sigma 1 (3 * 3) < (1 + 3) * (1 + 3) := by
  decide +kernel

end OddPerfect
