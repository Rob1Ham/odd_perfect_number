module

public import Mathlib.Data.Finset.NatDivisors
public import OddPerfect.SpoofFactors

public section

namespace OddPerfect

open ArithmeticFunction Finset
open scoped Pointwise

private theorem pair_sum (a b : ℕ) :
    (∑ z ∈ a.divisors ×ˢ b.divisors, z.1 * z.2) = sigma 1 a * sigma 1 b := by
  rw [sum_product, sigma_one_apply, sigma_one_apply, sum_mul_sum]

/-- Multiplying two divisor sums counts every divisor of the product at least once. -/
theorem sigma_mul_le (a b : ℕ) : sigma 1 (a * b) ≤ sigma 1 a * sigma 1 b := by
  rw [← pair_sum, sigma_one_apply, Nat.divisors_mul, Finset.mul_def]
  exact sum_image_le_of_nonneg (f := fun d : ℕ => d) (fun d _ => d.zero_le)

/-- A nontrivial common divisor `d` produces a collision from `(d,1)` and `(1,d)`. -/
theorem sigma_mul_lt_of_common_divisor {a b d : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hd : 1 < d) (hda : d ∣ a) (hdb : d ∣ b) : sigma 1 (a * b) < sigma 1 a * sigma 1 b := by
  let pairs := a.divisors ×ˢ b.divisors
  let mulPair (z : ℕ × ℕ) := z.1 * z.2
  have hleft : (d, 1) ∈ pairs := mem_product.mpr
    ⟨Nat.mem_divisors.mpr ⟨hda, ha.ne'⟩, Nat.one_mem_divisors.mpr hb.ne'⟩
  have hright : (1, d) ∈ pairs := mem_product.mpr
    ⟨Nat.one_mem_divisors.mpr ha.ne', Nat.mem_divisors.mpr ⟨hdb, hb.ne'⟩⟩
  have hsub : pairs.image mulPair ⊆ (pairs.erase (d, 1)).image mulPair := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
    by_cases h : z = (d, 1)
    · subst z
      refine mem_image.mpr ⟨(1, d), mem_erase.mpr ⟨?_, hright⟩, by simp [mulPair]⟩
      intro hpair
      exact hd.ne (congrArg Prod.fst hpair)
    · exact mem_image.mpr ⟨z, mem_erase.mpr ⟨h, hz⟩, rfl⟩
  calc
    sigma 1 (a * b) = ∑ x ∈ pairs.image mulPair, x := by
      rw [sigma_one_apply, Nat.divisors_mul, Finset.mul_def]
    _ ≤ ∑ x ∈ (pairs.erase (d, 1)).image mulPair, x := sum_le_sum_of_subset hsub
    _ ≤ ∑ z ∈ pairs.erase (d, 1), mulPair z :=
      sum_image_le_of_nonneg (f := fun x : ℕ => x) (fun x _ => x.zero_le)
    _ < ∑ z ∈ pairs, mulPair z := sum_lt_sum_of_subset (erase_subset _ _) hleft
      (notMem_erase _ _) (by simpa [mulPair] using Nat.zero_lt_of_lt hd)
      (fun _ _ _ => Nat.zero_le _)
    _ = sigma 1 a * sigma 1 b := pair_sum a b

private theorem sigma_prod_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    sigma 1 (∏ i ∈ s, f i) ≤ ∏ i ∈ s, sigma 1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [prod_insert hi, prod_insert hi]
    exact (sigma_mul_le _ _).trans (Nat.mul_le_mul_left _ ih)

/-- For positive powers of genuine primes, repeating a base causes a strict overcount
of the true divisor sum. The other bases may also repeat. -/
theorem sigma_lt_formalSigma_of_repeated_prime {ι : Type*} {s : Finset ι} {b e : ι → ℕ}
    (hp : ∀ i ∈ s, Nat.Prime (b i)) (he : ∀ i ∈ s, 0 < e i)
    (hr : ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ b i = b j) :
    sigma 1 (∏ i ∈ s, b i ^ e i) < formalSigma s b e := by
  classical
  obtain ⟨i, hi, j, hj, hij, hbase⟩ := hr
  let f (k : ι) := b k ^ e k
  let rest := ∏ k ∈ s.erase i, f k
  have hrest : 0 < rest :=
    prod_pos (fun k hk => pow_pos (hp k (mem_of_mem_erase hk)).pos _)
  have hcommon : b i ∣ rest := by
    rw [hbase]
    exact (dvd_pow_self _ (he j hj).ne').trans (dvd_prod_of_mem f (mem_erase.mpr ⟨hij.symm, hj⟩))
  calc
    sigma 1 (∏ k ∈ s, f k) = sigma 1 (f i * rest) := congrArg _ (s.mul_prod_erase f hi).symm
    _ < sigma 1 (f i) * sigma 1 rest :=
      sigma_mul_lt_of_common_divisor (pow_pos (hp i hi).pos _) hrest (hp i hi).one_lt
        (dvd_pow_self _ (he i hi).ne') hcommon
    _ ≤ sigma 1 (f i) * ∏ k ∈ s.erase i, sigma 1 (f k) := Nat.mul_le_mul_left _ (sigma_prod_le _ f)
    _ = ∏ k ∈ s, sigma 1 (f k) := s.mul_prod_erase (fun k => sigma 1 (f k)) hi
    _ = formalSigma s b e := by
      rw [formalSigma]
      exact prod_congr rfl (fun k hk => sigma_one_apply_prime_pow (i := e k) (hp k hk))

/-- A formally perfect factorization with positive exponents and only prime bases
evaluates to a deficient integer if any base occurs twice. -/
theorem deficient_of_repeated_prime_spoof {ι : Type*} {s : Finset ι} {b e : ι → ℕ}
    (hp : ∀ i ∈ s, Nat.Prime (b i)) (he : ∀ i ∈ s, 0 < e i)
    (hbal : formalSigma s b e = 2 * ∏ i ∈ s, b i ^ e i)
    (hr : ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ b i = b j) :
    Nat.Deficient (∏ i ∈ s, b i ^ e i) := by
  have h := sigma_lt_formalSigma_of_repeated_prime hp he hr
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, hbal] at h
  unfold Nat.Deficient
  omega

end OddPerfect
