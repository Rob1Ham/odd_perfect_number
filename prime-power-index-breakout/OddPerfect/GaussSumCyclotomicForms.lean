module

public import OddPerfect.UniversalCyclotomicRoots
public import OddPerfect.ZelinskyFullSlope
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Gauss-Sum Quadratic Reciprocity, Explicit Cyclotomic Quadratic Forms, and Selberg Sieve Bound

1. `quadratic_gaussSum_sq_eq_signed_prime`: Gauss-sum identity
   `(gaussSum χ ψ) ^ 2 = (-1 : R') ^ (d / 2) * (d : R')` for odd primes `d`.
2. `signed_prime_isSquare_of_dvd_geometricBlock`: Gauss-sum quadratic reciprocity obstruction
   on arbitrary odd prime cyclotomic blocks `w ∣ geometricBlock x d`.
3. `four_mul_cyclotomic_3_5_7_11_13` & `four_mul_geometricBlock_7_11_13`: Gauss's explicit
   cyclotomic quadratic forms `4 * Φ_p(X) = A_p(X)^2 ± p * B_p(X)^2` for `p ∈ {3, 5, 7, 11, 13}`.
4. `selberg_diagonalized_sifted_upper_bound`: diagonalized Selberg `Λ²` upper bound on
   `BoundingSieve.siftedSum`.
-/

public section

namespace OddPerfect

/-! ## 1. Quadratic Gauss Sum Identity -/

/-- For an odd prime `d` and a primitive additive character `ψ : AddChar (ZMod d) R'` into a
characteristic-zero domain `R'`, the quadratic Gauss sum squares to `(-1) ^ (d / 2) * d`. -/
theorem quadratic_gaussSum_sq_eq_signed_prime
    {d : ℕ} [Fact d.Prime] (hd2 : d ≠ 2)
    {R' : Type*} [CommRing R'] [IsDomain R'] [CharZero R']
    {ψ : AddChar (ZMod d) R'} (hψ : ψ.IsPrimitive) :
    let χ : MulChar (ZMod d) R' := (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom R')
    (gaussSum χ ψ) ^ 2 = (-1 : R') ^ (d / 2) * (d : R') := by
  intro χ
  have hchar : ringChar (ZMod d) ≠ 2 := by
    simpa [ZMod.ringChar_zmod_n] using hd2
  have hχ_quad : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod d)).comp (Int.castRingHom R')
  have hχ_ne : χ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr (quadraticChar_ne_one hchar)
  have hgs : gaussSum χ ψ ^ 2 = χ (-1) * Fintype.card (ZMod d) :=
    gaussSum_sq hχ_ne hχ_quad hψ
  have hd_odd : d % 2 = 1 := by
    rcases (Fact.out : d.Prime).eq_two_or_odd with rfl | hodd
    · exact absurd rfl hd2
    · exact hodd
  have hneg : quadraticChar (ZMod d) (-1) = (-1 : ℤ) ^ (d / 2) := by
    rw [quadraticChar_neg_one hchar, ZMod.card d, ZMod.χ₄_eq_neg_one_pow hd_odd]
  have hχ_neg : χ (-1) = (-1 : R') ^ (d / 2) := by
    change ((quadraticChar (ZMod d) (-1) : ℤ) : R') = (-1 : R') ^ (d / 2)
    rw [hneg]
    push_cast
    rfl
  rw [hgs, hχ_neg, ZMod.card d]

/-! ## 2. Gauss-Sum Quadratic Reciprocity Obstruction on Prime Cyclotomic Blocks -/

/-- If distinct odd primes `w ≠ d` satisfy `w ∣ geometricBlock x d` with `1 ≤ x`, then `d ∣ w - 1`
and `(-1) ^ (d / 2) * d` is a square modulo `w` (hence `d` is a square mod `w` when `d ≡ 1 [MOD 4]`
and `-d` is a square mod `w` when `d ≡ 3 [MOD 4]`). -/
theorem signed_prime_isSquare_of_dvd_geometricBlock
    {d w x : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    (hw : w.Prime) (hw2 : w ≠ 2) (hwd : w ≠ d)
    (hx : 1 ≤ x) (hdvd : w ∣ geometricBlock x d) :
    d ∣ w - 1 ∧
      IsSquare ((-1 : ZMod w) ^ (d / 2) * (d : ZMod w)) ∧
      (d % 4 = 1 → IsSquare (d : ZMod w)) ∧
      (d % 4 = 3 → IsSquare (-(d : ZMod w))) := by
  have _ := hx
  let _ : Fact d.Prime := ⟨hd⟩
  let _ : Fact w.Prime := ⟨hw⟩
  have hx_sum : (∑ j ∈ Finset.range d, (x : ZMod w) ^ j) = 0 := by
    have h0 : (geometricBlock x d : ZMod w) = 0 :=
      (ZMod.natCast_eq_zero_iff (geometricBlock x d) w).mpr hdvd
    simpa [geometricBlock] using h0
  have hx_ne1 : (x : ZMod w) ≠ 1 := by
    intro hx1
    have hd0 : (d : ZMod w) = 0 := by simpa [hx1] using hx_sum
    have hwd_dvd : w ∣ d := (ZMod.natCast_eq_zero_iff d w).mp hd0
    exact hwd ((Nat.prime_dvd_prime_iff_eq hw hd).mp hwd_dvd)
  have hx_pow : (x : ZMod w) ^ d = 1 := by
    apply sub_eq_zero.mp
    rw [← geom_sum_mul (x : ZMod w) d, hx_sum, zero_mul]
  have hx_ne0 : (x : ZMod w) ≠ 0 := by
    intro hx0
    rw [hx0, zero_pow hd.ne_zero] at hx_pow
    exact zero_ne_one hx_pow
  have hord : orderOf (x : ZMod w) = d := by
    have hdvd_ord : orderOf (x : ZMod w) ∣ d := orderOf_dvd_iff_pow_eq_one.mpr hx_pow
    rcases hd.eq_one_or_self_of_dvd _ hdvd_ord with h1 | hself
    · exact absurd (orderOf_eq_one_iff.mp h1) hx_ne1
    · exact hself
  have hd_dvd : d ∣ w - 1 := by
    simpa [hord] using ZMod.orderOf_dvd_card_sub_one hx_ne0
  have hw_cast_d : (w : ZMod d) = 1 := by
    obtain ⟨k, hk⟩ := hd_dvd
    have hw_eq : w = d * k + 1 := by
      have hw1 : 1 ≤ w := hw.one_lt.le
      omega
    rw [hw_eq]
    simp
  have hw_char : ringChar (ZMod w) ≠ 2 := by
    simpa [ZMod.ringChar_zmod_n] using hw2
  have hd_char : ringChar (ZMod d) ≠ 2 := by
    simpa [ZMod.ringChar_zmod_n] using hd2
  have hwd_char : ringChar (ZMod w) ≠ d := by
    simpa [ZMod.ringChar_zmod_n] using hwd
  have hw_odd : w % 2 = 1 := by
    rcases hw.eq_two_or_odd with rfl | hodd
    · exact absurd rfl hw2
    · exact hodd
  have hd_odd : d % 2 = 1 := by
    rcases hd.eq_two_or_odd with rfl | hodd
    · exact absurd rfl hd2
    · exact hodd
  have hquad_d : quadraticChar (ZMod w) d = ((-1 : ℤ) ^ (d / 2)) ^ (w / 2) := by
    rw [quadraticChar_odd_prime hw_char hd2 hwd_char, ZMod.card w, hw_cast_d, mul_one,
      ZMod.χ₄_eq_neg_one_pow hw_odd]
    push_cast
    rw [map_pow, quadraticChar_neg_one hd_char, ZMod.card d, ZMod.χ₄_eq_neg_one_pow hd_odd]
  have hquad_neg1 : quadraticChar (ZMod w) (-1) = (-1 : ℤ) ^ (w / 2) := by
    rw [quadraticChar_neg_one hw_char, ZMod.card w, ZMod.χ₄_eq_neg_one_pow hw_odd]
  have hquad_prod :
      quadraticChar (ZMod w) ((-1 : ZMod w) ^ (d / 2) * (d : ZMod w)) = 1 := by
    rw [map_mul, map_pow, hquad_neg1, hquad_d]
    rw [← pow_mul, ← pow_mul, mul_comm (w / 2) (d / 2), ← pow_add, ← two_mul, pow_mul,
      neg_one_sq, one_pow]
  have hprod_ne0 : (-1 : ZMod w) ^ (d / 2) * (d : ZMod w) ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) ?_
    intro hd0
    have hwd_dvd : w ∣ d := (ZMod.natCast_eq_zero_iff d w).mp hd0
    exact hwd ((Nat.prime_dvd_prime_iff_eq hw hd).mp hwd_dvd)
  have hsq : IsSquare ((-1 : ZMod w) ^ (d / 2) * (d : ZMod w)) :=
    (quadraticChar_one_iff_isSquare hprod_ne0).mp hquad_prod
  refine ⟨hd_dvd, hsq, ?_, ?_⟩
  · intro hd1
    have hpow : (-1 : ZMod w) ^ (d / 2) = 1 := by
      have hdiv : d / 2 = 2 * (d / 4) := by omega
      rw [hdiv, pow_mul, neg_one_sq, one_pow]
    simpa [hpow] using hsq
  · intro hd3
    have hpow : (-1 : ZMod w) ^ (d / 2) = -1 := by
      have hdiv : d / 2 = 2 * (d / 4) + 1 := by omega
      rw [hdiv, pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
    simpa [hpow] using hsq

/-! ## 3. Gauss's Explicit Cyclotomic Quadratic Forms -/

private lemma cyclotomic_prime_three_int :
    Polynomial.cyclotomic 3 ℤ = Polynomial.X ^ 2 + Polynomial.X + 1 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [Polynomial.cyclotomic_prime]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, pow_zero,
    pow_one]
  ring

private lemma cyclotomic_prime_five_int :
    Polynomial.cyclotomic 5 ℤ =
      Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + 1 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [Polynomial.cyclotomic_prime]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, pow_zero,
    pow_one]
  ring

private lemma cyclotomic_prime_seven_int :
    Polynomial.cyclotomic 7 ℤ =
      Polynomial.X ^ 6 + Polynomial.X ^ 5 + Polynomial.X ^ 4 + Polynomial.X ^ 3 +
        Polynomial.X ^ 2 + Polynomial.X + 1 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  rw [Polynomial.cyclotomic_prime]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, pow_zero,
    pow_one]
  ring

private lemma cyclotomic_prime_eleven_int :
    Polynomial.cyclotomic 11 ℤ =
      Polynomial.X ^ 10 + Polynomial.X ^ 9 + Polynomial.X ^ 8 + Polynomial.X ^ 7 +
        Polynomial.X ^ 6 + Polynomial.X ^ 5 + Polynomial.X ^ 4 + Polynomial.X ^ 3 +
        Polynomial.X ^ 2 + Polynomial.X + 1 := by
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  rw [Polynomial.cyclotomic_prime]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, pow_zero,
    pow_one]
  ring

private lemma cyclotomic_prime_thirteen_int :
    Polynomial.cyclotomic 13 ℤ =
      Polynomial.X ^ 12 + Polynomial.X ^ 11 + Polynomial.X ^ 10 + Polynomial.X ^ 9 +
        Polynomial.X ^ 8 + Polynomial.X ^ 7 + Polynomial.X ^ 6 + Polynomial.X ^ 5 +
        Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + 1 := by
  have : Fact (Nat.Prime 13) := ⟨by decide⟩
  rw [Polynomial.cyclotomic_prime]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, pow_zero,
    pow_one]
  ring

/-- Gauss's explicit cyclotomic quadratic identities `4 * Φ_p(X) = A_p(X)^2 ± p * B_p(X)^2`
in `Polynomial ℤ` for `p ∈ {3, 5, 7, 11, 13}`. -/
theorem four_mul_cyclotomic_3_5_7_11_13 :
    (4 * Polynomial.cyclotomic 3 ℤ = (2 * Polynomial.X + 1) ^ 2 + 3 * (1 : Polynomial ℤ) ^ 2) ∧
    (4 * Polynomial.cyclotomic 5 ℤ =
      (2 * Polynomial.X ^ 2 + Polynomial.X + 2) ^ 2 - 5 * Polynomial.X ^ 2) ∧
    (4 * Polynomial.cyclotomic 7 ℤ =
      (2 * Polynomial.X ^ 3 + Polynomial.X ^ 2 - Polynomial.X - 2) ^ 2 +
        7 * (Polynomial.X ^ 2 + Polynomial.X) ^ 2) ∧
    (4 * Polynomial.cyclotomic 11 ℤ =
      (2 * Polynomial.X ^ 5 + Polynomial.X ^ 4 - 2 * Polynomial.X ^ 3 +
        2 * Polynomial.X ^ 2 - Polynomial.X - 2) ^ 2 +
        11 * (Polynomial.X ^ 4 + Polynomial.X) ^ 2) ∧
    (4 * Polynomial.cyclotomic 13 ℤ =
      (2 * Polynomial.X ^ 6 + Polynomial.X ^ 5 + 4 * Polynomial.X ^ 4 - Polynomial.X ^ 3 +
        4 * Polynomial.X ^ 2 + Polynomial.X + 2) ^ 2 -
        13 * (Polynomial.X ^ 5 + Polynomial.X ^ 3 + Polynomial.X) ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [cyclotomic_prime_three_int]; ring
  · rw [cyclotomic_prime_five_int]; ring
  · rw [cyclotomic_prime_seven_int]; ring
  · rw [cyclotomic_prime_eleven_int]; ring
  · rw [cyclotomic_prime_thirteen_int]; ring

private lemma eval_cyclotomic_prime_eq_geometricBlock (p x : ℕ) [Fact p.Prime] :
    Polynomial.eval (x : ℤ) (Polynomial.cyclotomic p ℤ) = (geometricBlock x p : ℤ) := by
  rw [Polynomial.cyclotomic_prime, Polynomial.eval_finsetSum]
  simp [geometricBlock]

/-- Integer `geometricBlock` specializations of Gauss's cyclotomic quadratic forms for
`d ∈ {7, 11, 13}`. -/
theorem four_mul_geometricBlock_7_11_13 (x : ℕ) :
    (4 * (geometricBlock x 7 : ℤ) =
      (2 * (x : ℤ) ^ 3 + (x : ℤ) ^ 2 - (x : ℤ) - 2) ^ 2 +
        7 * ((x : ℤ) ^ 2 + (x : ℤ)) ^ 2) ∧
    (4 * (geometricBlock x 11 : ℤ) =
      (2 * (x : ℤ) ^ 5 + (x : ℤ) ^ 4 - 2 * (x : ℤ) ^ 3 +
        2 * (x : ℤ) ^ 2 - (x : ℤ) - 2) ^ 2 +
        11 * ((x : ℤ) ^ 4 + (x : ℤ)) ^ 2) ∧
    (4 * (geometricBlock x 13 : ℤ) =
      (2 * (x : ℤ) ^ 6 + (x : ℤ) ^ 5 + 4 * (x : ℤ) ^ 4 - (x : ℤ) ^ 3 +
        4 * (x : ℤ) ^ 2 + (x : ℤ) + 2) ^ 2 -
        13 * ((x : ℤ) ^ 5 + (x : ℤ) ^ 3 + (x : ℤ)) ^ 2) := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  have : Fact (Nat.Prime 13) := ⟨by decide⟩
  obtain ⟨_, _, h7, h11, h13⟩ := four_mul_cyclotomic_3_5_7_11_13
  refine ⟨?_, ?_, ?_⟩
  · have h := congrArg (Polynomial.eval (x : ℤ)) h7
    simpa [eval_cyclotomic_prime_eq_geometricBlock] using h
  · have h := congrArg (Polynomial.eval (x : ℤ)) h11
    simpa [eval_cyclotomic_prime_eq_geometricBlock] using h
  · have h := congrArg (Polynomial.eval (x : ℤ)) h13
    simpa [eval_cyclotomic_prime_eq_geometricBlock] using h

/-! ## 4. Diagonalized Selberg Sieve Upper Bound -/

/-- Diagonalized Selberg `Λ²` upper bound on `BoundingSieve.siftedSum` for any weight sequence
`w` normalized by `w 1 = 1`. -/
theorem selberg_diagonalized_sifted_upper_bound
    (s : BoundingSieve) (w : ℕ → ℝ) (hw : w 1 = 1) :
    s.siftedSum ≤
      s.totalMass *
        (∑ l ∈ s.prodPrimes.divisors,
          (s.selbergTerms l)⁻¹ *
            (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * w d else 0) ^ 2) +
        s.errSum (BoundingSieve.lambdaSquared w) := by
  calc
    s.siftedSum ≤
        s.totalMass * s.mainSum (BoundingSieve.lambdaSquared w) +
          s.errSum (BoundingSieve.lambdaSquared w) :=
      s.siftedSum_le_mainSum_errSum_of_upperMoebius (BoundingSieve.lambdaSquared w)
        (BoundingSieve.upperMoebius_lambdaSquared w hw)
    _ =
        s.totalMass *
          (∑ l ∈ s.prodPrimes.divisors,
            (s.selbergTerms l)⁻¹ *
              (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * w d else 0) ^ 2) +
          s.errSum (BoundingSieve.lambdaSquared w) := by
      rw [s.mainSum_lambdaSquared_eq_sum_mul_sum_sq w]

end OddPerfect
