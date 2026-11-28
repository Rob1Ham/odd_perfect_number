module

public import OddPerfect.ExceptionalFermatReduction
public import OddPerfect.HalfLengthSupport
import all OddPerfect.ExceptionalFermatReduction
import all OddPerfect.EulerSquareClass
import all OddPerfect.AlternatingBlock
import all OddPerfect.HalfLengthSupport
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# High Euler Half-Sum Reduction

BRANCH_MAP: A_GT1
Closure: Conditionally closes the entire (q^d + 1)/2 = □ half of A_GT1 (prime and composite d) on PrimePowerFermatObstruction (Ivorra 2003 / Bennett–Skinner 2004), unconditionally forces d prime on Subcase B of I = ℓ₁ ℓ₂ t², and forces d prime on unrestricted I = ℓ₁ ℓ₂ t² under PrimePowerFermatObstruction.
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- Generalized Fermat obstruction on prime-power bases in the residual
congruence classes modulo 16 and 7 with prime exponent `p ≥ 17`, `p ≡ 1 (mod 8)`. -/
@[expose] def PrimePowerFermatObstruction : Prop :=
  ∀ x p y : ℕ, IsPrimePow x → x % 16 = 1 → x % 7 ≠ 2 → x % 7 ≠ 4 →
    p.Prime → 17 ≤ p → p % 8 = 1 → 0 < y → x.Coprime y → x ^ p + 1 ≠ 2 * y ^ 2

/-- The prime-power Fermat hypothesis implies the prime-base hypothesis
from `OddPerfect.ExceptionalFermatReduction`. -/
theorem primePowerFermatObstruction_implies_exceptional (hF : PrimePowerFermatObstruction) :
    ExceptionalFermatObstruction := by
  intro q d y hq hq16 h2 h4 hd hd17 hd8 hy hcop
  exact hF q d y hq.isPrimePow hq16 h2 h4 hd hd17 hd8 hy hcop

/-- Whenever `(q ^ d + 1) / 2` is a square for an odd exponent `d > 1` and a
prime `q ≡ 1 (mod 4)`, every prime factor of `d` is `1 mod 8` and at least `17`,
and `p = d.minFac` supplies a prime-power generalized Fermat witness `(q ^ (d / p), p, y)`
together with `p ∣ q + 1`. -/
theorem half_pow_succ_square_forces_minFac_fermat_witness {q d : ℕ}
    (hq : q.Prime) (hq4 : q % 4 = 1) (hd_odd : Odd d) (hd1 : 1 < d)
    (hsq : IsSquare ((q ^ d + 1) / 2)) :
    q % 16 = 1 ∧ q % 7 ≠ 2 ∧ q % 7 ≠ 4 ∧ ¬ 3 ∣ d ∧ ¬ 5 ∣ d ∧
    (∀ p ∈ d.primeFactors, 17 ≤ p ∧ p % 8 = 1) ∧
    17 ≤ d ∧ d % 8 = 1 ∧ (¬ d.Prime → 289 ≤ d) ∧
    let p := d.minFac
    let k := d / p
    let x := q ^ k
    p.Prime ∧ 17 ≤ p ∧ p % 8 = 1 ∧ p ∣ q + 1 ∧
    IsPrimePow x ∧ x % 16 = 1 ∧ x % 7 ≠ 2 ∧ x % 7 ≠ 4 ∧
    ∃ y : ℕ, 0 < y ∧ x.Coprime y ∧ x ^ p + 1 = 2 * y ^ 2 := by
  have hq16 : q % 16 = 1 := by
    by_contra h
    exact half_pow_succ_not_square_of_mod_sixteen hq4 hd_odd h hsq
  have h3 : ¬ 3 ∣ d := fun h =>
    half_pow_succ_not_square_of_factor hq.one_lt hq4 hd_odd.pos h
      (fun _ hx hx4 => half_cube_succ_not_square hx hx4) hsq
  have h5 : ¬ 5 ∣ d := fun h =>
    half_pow_succ_not_square_of_factor hq.one_lt hq4 hd_odd.pos h
      (fun _ hx hx4 => half_fifth_succ_not_square hx hx4) hsq
  have ⟨y, hy⟩ := hsq
  have hq_odd : Odd q := Nat.odd_iff.mpr (by omega)
  have hqd_odd : Odd (q ^ d) := hq_odd.pow
  have hqd_two : 2 ∣ q ^ d + 1 :=
    Nat.dvd_of_mod_eq_zero (by have := Nat.odd_iff.mp hqd_odd; omega)
  have hpow_eq : q ^ d + 1 = 2 * y ^ 2 := by
    rw [pow_two, ← hy, Nat.mul_div_cancel' hqd_two]
  have hy_pos : 0 < y := by
    by_contra hy0
    have hyz : y = 0 := by omega
    rw [hyz, zero_pow (by decide : 2 ≠ 0), mul_zero] at hpow_eq
    omega
  have hq7_2 : q % 7 ≠ 2 := fun h =>
    pow_add_one_ne_twice_sq_of_mod_seven (Or.inl h) h3 hpow_eq
  have hq7_4 : q % 7 ≠ 4 := fun h =>
    pow_add_one_ne_twice_sq_of_mod_seven (Or.inr h) h3 hpow_eq
  have hp_prop : ∀ r ∈ d.primeFactors, 17 ≤ r ∧ r % 8 = 1 ∧ r ∣ q ^ (d / r) + 1 := by
    intro r hr_mem
    have hr : r.Prime := Nat.prime_of_mem_primeFactors hr_mem
    have hr_dvd : r ∣ d := Nat.dvd_of_mem_primeFactors hr_mem
    let k' := d / r
    have hk'_mul : k' * r = d := Nat.div_mul_cancel hr_dvd
    have hk'_pos : 0 < k' := Nat.div_pos (Nat.le_of_dvd hd_odd.pos hr_dvd) hr.pos
    have hr_odd : Odd r := hd_odd.of_dvd_nat hr_dvd
    let x' := q ^ k'
    have hx'1 : 1 < x' := one_lt_pow₀ hq.one_lt hk'_pos.ne'
    have hx'16 : x' % 16 = 1 := by
      simpa [x', Nat.ModEq] using (show q ≡ 1 [MOD 16] from hq16).pow k'
    have hx'8 : x' % 8 = 1 := by omega
    have hx'_sq : IsSquare ((x' ^ r + 1) / 2) := by
      dsimp [x']
      rw [← pow_mul, hk'_mul]
      exact hsq
    have hnsq_alt : ¬ IsSquare (alternatingBlock x' r) :=
      alternatingBlock_not_square hx'1 hr.one_lt hr_odd
    have hnot_sep : ¬ (r % 8 ≠ 1 ∨ ¬ r ∣ x' + 1) := fun hsep =>
      half_sum_not_square_of_alternatingBlock hx'8 hr hr_odd hnsq_alt hsep hx'_sq
    have hr8 : r % 8 = 1 := by
      by_contra h
      exact hnot_sep (Or.inl h)
    have hr_plus : r ∣ x' + 1 := by
      by_contra h
      exact hnot_sep (Or.inr h)
    have hr17 : 17 ≤ r := by
      by_contra hr_lt
      have : r = 1 ∨ r = 9 := by omega
      rcases this with rfl | rfl <;> exact absurd hr (by decide)
    exact ⟨hr17, hr8, hr_plus⟩
  have hd8 : d % 8 = 1 := by
    have hprod : (∏ r ∈ d.primeFactors, r ^ d.factorization r) ≡ 1 [MOD 8] := by
      apply Nat.ModEq.prod_one
      intro r hr_mem
      have hr8 : r % 8 = 1 := (hp_prop r hr_mem).2.1
      simpa [Nat.ModEq] using (show r ≡ 1 [MOD 8] from hr8).pow (d.factorization r)
    rw [← Nat.prod_primeFactors_pow_factorization hd_odd.pos.ne'] at hprod
    simpa [Nat.ModEq] using hprod
  let p := d.minFac
  let k := d / p
  let x := q ^ k
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hp_dvd : p ∣ d := Nat.minFac_dvd d
  have hp_mem : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hp_dvd, hd_odd.pos.ne'⟩
  have hp17 : 17 ≤ p := (hp_prop p hp_mem).1
  have hp8 : p % 8 = 1 := (hp_prop p hp_mem).2.1
  have hp_dvd_xk1 : p ∣ x + 1 := (hp_prop p hp_mem).2.2
  have hd17 : 17 ≤ d := hp17.trans (Nat.le_of_dvd hd_odd.pos hp_dvd)
  have hk_mul : k * p = d := Nat.div_mul_cancel hp_dvd
  have hk_pos : 0 < k := Nat.div_pos (Nat.le_of_dvd hd_odd.pos hp_dvd) hp.pos
  have hcomp : ¬ d.Prime → 289 ≤ d := by
    intro hd_np
    have hk1 : 1 < k := by
      by_contra hkle
      have hkeq : k = 1 := by omega
      rw [hkeq, one_mul] at hk_mul
      exact hd_np (hk_mul ▸ hp)
    let r := k.minFac
    have hr : r.Prime := Nat.minFac_prime (by omega)
    have hr_dvd_k : r ∣ k := Nat.minFac_dvd k
    have hr_dvd_d : r ∣ d := hr_dvd_k.trans ⟨p, hk_mul.symm⟩
    have hr_mem : r ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hr, hr_dvd_d, hd_odd.pos.ne'⟩
    have hr17 : 17 ≤ r := (hp_prop r hr_mem).1
    have hk17 : 17 ≤ k := hr17.trans (Nat.le_of_dvd hk_pos hr_dvd_k)
    calc
      289 = 17 * 17 := by decide
      _ ≤ k * p := Nat.mul_le_mul hk17 hp17
      _ = d := hk_mul
  have hx_primePow : IsPrimePow x := hq.isPrimePow.pow hk_pos.ne'
  have hx16 : x % 16 = 1 := by
    simpa [x, Nat.ModEq] using (show q ≡ 1 [MOD 16] from hq16).pow k
  have hx_pow_eq : x ^ p + 1 = 2 * y ^ 2 := by
    dsimp [x]
    rw [← pow_mul, hk_mul]
    exact hpow_eq
  have hp3 : ¬ 3 ∣ p := fun h => h3 (h.trans hp_dvd)
  have hx7_2 : x % 7 ≠ 2 := fun h =>
    pow_add_one_ne_twice_sq_of_mod_seven (Or.inl h) hp3 hx_pow_eq
  have hx7_4 : x % 7 ≠ 4 := fun h =>
    pow_add_one_ne_twice_sq_of_mod_seven (Or.inr h) hp3 hx_pow_eq
  have hx_cop : x.Coprime y := by
    by_contra hnc
    obtain ⟨r, hr, hrx, hry⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    have hr_xp : r ∣ x ^ p := hrx.trans (dvd_pow_self x hp.ne_zero)
    have hr_2y2 : r ∣ 2 * y ^ 2 := dvd_mul_of_dvd_right (hry.trans (dvd_pow_self y (by decide))) 2
    rw [← hx_pow_eq] at hr_2y2
    exact hr.not_dvd_one ((Nat.dvd_add_right hr_xp).mp hr_2y2)
  have hp_dvd_q1 : p ∣ q + 1 := by
    have hcop_kp : k.Coprime (p - 1) := by
      by_contra hnc
      obtain ⟨r, hr, hrk, hrp1⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
      have hrd : r ∣ d := hrk.trans ⟨p, hk_mul.symm⟩
      have hle : p ≤ r := Nat.minFac_le_of_dvd hr.two_le hrd
      have hrle : r ≤ p - 1 := Nat.le_of_dvd (by omega) hrp1
      omega
    have : Fact p.Prime := ⟨hp⟩
    have hqk_neg : (q : ZMod p) ^ k = -1 := by
      have hz : ((q ^ k + 1 : ℕ) : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff (q ^ k + 1) p).mpr hp_dvd_xk1
      push_cast at hz
      exact eq_neg_iff_add_eq_zero.mpr hz
    have hq_ne : (q : ZMod p) ≠ 0 := by
      intro h0
      rw [h0, zero_pow hk_pos.ne'] at hqk_neg
      have h1 : (1 : ZMod p) = 0 := by
        calc
          (1 : ZMod p) = -(-1 : ZMod p) := (neg_neg 1).symm
          _ = -0 := congrArg Neg.neg hqk_neg.symm
          _ = 0 := neg_zero
      exact one_ne_zero h1
    obtain ⟨m, _, hm_mod⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop_kp (by omega : 1 < p - 1)
    let t := (k * m) / (p - 1)
    have hkm : k * m = (p - 1) * t + 1 := by
      have h := Nat.div_add_mod (k * m) (p - 1)
      rw [hm_mod] at h
      exact h.symm
    have hm_odd : Odd m := by
      have hpe : (p - 1) % 2 = 0 := by omega
      have hkm2 : (k * m) % 2 = 1 := by
        rw [hkm, Nat.add_mod, Nat.mul_mod, hpe]
        simp
      exact (Nat.odd_mul.mp (Nat.odd_iff.mpr hkm2)).2
    have hq_neg : (q : ZMod p) = -1 := by
      calc
        (q : ZMod p) = 1 ^ t * (q : ZMod p) := by simp
        _ = ((q : ZMod p) ^ (p - 1)) ^ t * (q : ZMod p) := by
          rw [ZMod.pow_card_sub_one_eq_one hq_ne]
        _ = (q : ZMod p) ^ ((p - 1) * t + 1) := by
          rw [pow_succ, pow_mul]
        _ = (q : ZMod p) ^ (k * m) := by rw [← hkm]
        _ = ((q : ZMod p) ^ k) ^ m := by rw [pow_mul]
        _ = (-1 : ZMod p) ^ m := by rw [hqk_neg]
        _ = -1 := hm_odd.neg_one_pow
    apply (ZMod.natCast_eq_zero_iff (q + 1) p).mp
    push_cast
    rw [hq_neg]
    ring
  exact ⟨hq16, hq7_2, hq7_4, h3, h5, fun r hr => ⟨(hp_prop r hr).1, (hp_prop r hr).2.1⟩,
    hd17, hd8, hcomp, hp, hp17, hp8, hp_dvd_q1, hx_primePow, hx16, hx7_2, hx7_4,
    ⟨y, hy_pos, hx_cop, hx_pow_eq⟩⟩

/-- Under `PrimePowerFermatObstruction`, for every odd perfect number with
Euler exponent `a > 1`, the second half-length block `(q ^ ((a + 1) / 2) + 1) / 2`
is never a square, and the Euler component index has at least two distinct
primes of odd valuation. -/
theorem high_euler_half_sum_not_square_of_prime_power_fermat (hF : PrimePowerFermatObstruction)
    {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2) :
    ¬ IsSquare ((q ^ ((a + 1) / 2) + 1) / 2) ∧
    2 ≤ (oddValuationPrimes (sigma 1 (m ^ 2) / q ^ a)).card := by
  let d := (a + 1) / 2
  have hd_odd : Odd d := Nat.odd_iff.mpr (by dsimp [d]; omega)
  have hd1 : 1 < d := by dsimp [d]; omega
  have hnsq : ¬ IsSquare ((q ^ d + 1) / 2) := by
    intro hsq
    have hw := half_pow_succ_square_forces_minFac_fermat_witness hq hq4 hd_odd hd1 hsq
    dsimp only at hw
    obtain ⟨_, _, _, _, _, _, _, _, _, hp, hp17, hp8, _, hxpp, hx16, hx7_2, hx7_4, y, hy, hcop, hpow⟩ := hw
    exact hF _ _ y hxpp hx16 hx7_2 hx7_4 hp hp17 hp8 hy hcop hpow
  refine ⟨hnsq, ?_⟩
  obtain ⟨i, _, hleft, hright, _⟩ :=
    exists_component_index hN hq hform (fun h => hqm (hq.dvd_of_dvd_pow h))
  rw [hleft, Nat.mul_div_cancel_left i (pow_pos hq.pos _)]
  have hm := (ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _)).pos
  have hcard_eq : (oddValuationPrimes i).card =
      (oddValuationPrimes (geometricBlock q d)).card +
      (oddValuationPrimes ((q ^ d + 1) / 2)).card :=
    oddValuationPrimes_in_index hq hq4 ha4 hm.ne' hright
  rw [hcard_eq]
  have h1 := oddValuationPrimes_pos (geometricBlock_not_square_of_prime_one_mod_four hq hq4 hd1)
  have h2 := oddValuationPrimes_pos hnsq
  omega

/-- Unconditionally, if the Euler component index has exactly two distinct primes
of odd valuation (e.g. `I = ℓ₁ ℓ₂ t²`) and the second half-length block is nonsquare,
then the half-length `(a + 1) / 2` must be prime. -/
theorem two_odd_valuations_nonsquare_half_sum_forces_prime_half_length
    {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hcard : (oddValuationPrimes (sigma 1 (m ^ 2) / q ^ a)).card = 2)
    (hnsq : ¬ IsSquare ((q ^ ((a + 1) / 2) + 1) / 2)) :
    ((a + 1) / 2).Prime := by
  let d := (a + 1) / 2
  have hd_odd : Odd d := Nat.odd_iff.mpr (by dsimp [d]; omega)
  have hd1 : 1 < d := by dsimp [d]; omega
  obtain ⟨i, _, hleft, hright, _⟩ :=
    exists_component_index hN hq hform (fun h => hqm (hq.dvd_of_dvd_pow h))
  have hm := (ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _)).pos
  rw [hleft, Nat.mul_div_cancel_left i (pow_pos hq.pos _)] at hcard
  have hsum : (oddValuationPrimes i).card =
      (oddValuationPrimes (geometricBlock q d)).card +
      (oddValuationPrimes ((q ^ d + 1) / 2)).card :=
    oddValuationPrimes_in_index hq hq4 ha4 hm.ne' hright
  have hA_pos : 0 < (oddValuationPrimes (geometricBlock q d)).card :=
    oddValuationPrimes_pos (geometricBlock_not_square_of_prime_one_mod_four hq hq4 hd1)
  have hB_pos : 0 < (oddValuationPrimes ((q ^ d + 1) / 2)).card :=
    oddValuationPrimes_pos (show ¬ IsSquare ((q ^ d + 1) / 2) from hnsq)
  have hA_one : (oddValuationPrimes (geometricBlock q d)).card = 1 := by omega
  have hB_one : (oddValuationPrimes ((q ^ d + 1) / 2)).card = 1 := by omega
  have hlen : d.primeFactors.card ≤ (oddValuationPrimes (geometricBlock q d)).card := by
    simpa using distinct_primes_length_le_odd_valuations hq (by decide : 0 < 1)
      (by simpa using hq4) d hd_odd.pos
  have hpos : 0 < d.primeFactors.card := Finset.card_pos.mpr ⟨d.minFac, Nat.mem_primeFactors.mpr
    ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd d, (by omega)⟩⟩
  obtain ⟨s, k, hsp, hk, hpow⟩ :=
    (isPrimePow_nat_iff d).mp (isPrimePow_iff_card_primeFactors_eq_one.mpr (by omega : d.primeFactors.card = 1))
  have htotal : cardFactors d ≤ 2 * (oddValuationPrimes (geometricBlock q d)).card := by
    simpa using length_factor_count_le_twice_odd_valuations hq (by decide : 0 < 1)
      (by simpa using hq4) hd_odd
  have heval : cardFactors d = k := by rw [← hpow, cardFactors_apply_prime_pow hsp]
  have hk2 : k ≤ 2 := by omega
  by_cases hk1 : k = 1
  · change d.Prime
    rw [← hpow, hk1, pow_one]
    exact hsp
  exfalso
  have hk_eq : k = 2 := by omega
  have hso : Odd s := hd_odd.of_dvd_nat (hpow ▸ dvd_pow_self s hk.ne')
  have hsm : s ∣ q - 1 := by
    by_contra hn
    have hbound : k ≤ (oddValuationPrimes (geometricBlock q (s ^ k))).card := by
      simpa using prime_pow_length_le_odd_valuations hq (by decide : 0 < 1)
        (by simpa using hq4) hsp (by simpa using hn) k
    rw [hpow] at hbound
    omega
  let X := q ^ s
  let H := (X + 1) / 2
  let C := alternatingBlock X s
  have hX1 : 1 < X := one_lt_pow₀ hq.one_lt hsp.ne_zero
  have hX_odd : Odd X := (Nat.odd_iff.mpr (by omega) : Odd q).pow
  have hH0 : H ≠ 0 := by dsimp [H]; omega
  have hmul_alt := alternatingBlock_mul (x := X) hso
  have hC0 : C ≠ 0 := by
    intro h
    dsimp [C] at h
    rw [h, zero_mul] at hmul_alt
    omega
  have hH_mul : 2 * H = X + 1 := by
    dsimp [H]
    have := Nat.odd_iff.mp hX_odd
    omega
  have hqd_eq : q ^ d = X ^ s := by
    dsimp [X]
    rw [← hpow, hk_eq, pow_two, pow_mul]
  have hprod : H * C = (q ^ d + 1) / 2 := by
    rw [hqd_eq]
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
    have hdiv2 : 2 ∣ X ^ s + 1 := by
      have hXs_odd : Odd (X ^ s) := hX_odd.pow
      exact Nat.dvd_of_mod_eq_zero (by have := Nat.odd_iff.mp hXs_odd; omega)
    dsimp [C]
    rw [Nat.mul_div_cancel' hdiv2, ← hmul_alt, ← mul_assoc, hH_mul, mul_comm]
  have hcop : H.Coprime C := by
    by_contra hnc
    obtain ⟨r, hr, hrH, hrC⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    have hr_plus : r ∣ X + 1 := hrH.trans ⟨2, by linarith⟩
    have hrs : r ∣ s := common_prime_alternatingBlock hso hr_plus hrC
    have hrs_eq : r = s := (Nat.prime_dvd_prime_iff_eq hr hsp).mp hrs
    rw [hrs_eq] at hr_plus
    have hqone : q ≡ 1 [MOD s] := (Nat.modEq_iff_dvd' hq.one_le).mpr hsm |>.symm
    have hXone : X ≡ 1 [MOD s] := by simpa [X] using hqone.pow s
    have hmod2 : (2 : ℕ) ≡ 0 [MOD s] := by
      calc
        2 = 1 + 1 := rfl
        _ ≡ X + 1 [MOD s] := hXone.symm.add_right 1
        _ ≡ 0 [MOD s] := Nat.modEq_zero_iff_dvd.mpr hr_plus
    have hs2 : s ∣ 2 := Nat.modEq_zero_iff_dvd.mp hmod2
    have hs_eq : s = 2 := (Nat.prime_dvd_prime_iff_eq hsp Nat.prime_two).mp hs2
    have := Nat.odd_iff.mp hso
    omega
  have hcard_prod : (oddValuationPrimes ((q ^ d + 1) / 2)).card =
      (oddValuationPrimes H).card + (oddValuationPrimes C).card := by
    rw [← hprod]
    exact oddValuationPrimes_card_mul hH0 hC0 hcop
  have hC_pos : 0 < (oddValuationPrimes C).card :=
    oddValuationPrimes_pos (alternatingBlock_not_square hX1 hsp.one_lt hso)
  have hH_zero : (oddValuationPrimes H).card = 0 := by omega
  have hH_sq : IsSquare H := by
    by_contra hnsq_H
    have := oddValuationPrimes_pos hnsq_H
    omega
  have hw := half_pow_succ_square_forces_minFac_fermat_witness hq hq4 hso hsp.one_lt hH_sq
  dsimp only at hw
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs_plus, _⟩ := hw
  rw [hsp.minFac_eq] at hs_plus
  have hs2 : s ∣ 2 := by
    have hsub := Nat.dvd_sub hs_plus hsm
    rwa [show q + 1 - (q - 1) = 2 by have := hq.two_le; omega] at hsub
  have hs_le : s ≤ 2 := Nat.le_of_dvd (by decide) hs2
  have := hsp.two_le
  have := Nat.odd_iff.mp hso
  omega

/-- Under `PrimePowerFermatObstruction`, if the Euler component index has
exactly two distinct primes of odd valuation, then the half-length `(a + 1) / 2`
must be prime. -/
theorem two_odd_valuations_forces_prime_half_length_of_prime_power_fermat
    (hF : PrimePowerFermatObstruction) {N q a m : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hcard : (oddValuationPrimes (sigma 1 (m ^ 2) / q ^ a)).card = 2) :
    ((a + 1) / 2).Prime :=
  two_odd_valuations_nonsquare_half_sum_forces_prime_half_length hN ho hq hq4 ha4 ha hqm hform hcard
    (high_euler_half_sum_not_square_of_prime_power_fermat hF hN ho hq hq4 ha4 ha hqm hform).1

end OddPerfect
