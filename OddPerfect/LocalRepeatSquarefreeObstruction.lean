module

public import OddPerfect.DoubleCollisionExcessObstruction
public import OddPerfect.ZelinskyFullSlope
public import OddPerfect.CountBound37
public import OddPerfect.CountExcessSeven
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Local Repeat & Squarefree Component Obstruction (`OddPerfect.LocalRepeatSquarefreeObstruction`)

Formalizes non-square ramification of `Φ₃` and `Φ₅`, exact equivalence between vanishing local
repeat excess and squarefreeness of all odd divisor-sum components, and global cyclotomic slope
and factor-count lower bounds on `localRepeatExcess N q + collisionExcess N q`:

1. `not_nine_dvd_sq_add_self_add_one` & `not_twenty_five_dvd_quartic_sum`:
   `¬ (9 ∣ p ^ 2 + p + 1)` and `¬ (25 ∣ p ^ 4 + p ^ 3 + p ^ 2 + p + 1)` for all `p : ℕ`, with
   prime-square divisibility consequences for `sigma 1 (p ^ 2)` (`r ≠ 3 ∧ r % 3 = 1 ∧ 7 ≤ r`)
   and `sigma 1 (p ^ 4)` (`r ≠ 5 ∧ r % 5 = 1 ∧ 11 ≤ r`).
2. `localRepeatExcess_eq_zero_iff_all_squarefree`:
   `localRepeatExcess N q = 0 ↔ ∀ p ∈ N.primeFactors, Squarefree (oddComponentSigma N q p)`.
3. `cyclotomic_slope_excess_bounds`:
   Couples `cardFactors_eq_primeFactors_add_localRepeat_add_collisionExcess` with
   `sharpened_cyclotomic_prime_factor_count`, `sharpened_cyclotomic_slope_three_free`, and the
   sixth-power-free `443 ≤ N.primeFactors.card` bound (`736 ≤ localRepeatExcess N q + collisionExcess N q`).
4. `squarefree_components_force_22_collisions`:
   Couples `thirty_seven_le_total_prime_factor_count` and `seven_le_prime_factor_count_excess` with
   `sharpened_cyclotomic_slope_three_free` to prove `22 ≤ localRepeatExcess N q + collisionExcess N q`
   (`23` when `¬ 3 ∣ N`), forcing `22 ≤ collisionExcess N q` (`23` when `¬ 3 ∣ N`) whenever all
   odd components are squarefree.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-! ## 1. Non-Square Ramification of `Φ₃` and `Φ₅` -/

/-- For every `p : ℕ`, `9` never divides `p ^ 2 + p + 1`. -/
theorem not_nine_dvd_sq_add_self_add_one (p : ℕ) : ¬ (9 ∣ p ^ 2 + p + 1) := by
  have hmod9 : ∀ x : ZMod 9, x ^ 2 + x + 1 ≠ 0 := by decide
  intro hdvd
  have hz : ((p : ZMod 9) ^ 2 + (p : ZMod 9) + 1) = 0 := by
    have h := (ZMod.natCast_eq_zero_iff (p ^ 2 + p + 1) 9).mpr hdvd
    push_cast at h
    exact h
  exact hmod9 (p : ZMod 9) hz

/-- For every `p : ℕ`, `25` never divides `p ^ 4 + p ^ 3 + p ^ 2 + p + 1`. -/
theorem not_twenty_five_dvd_quartic_sum (p : ℕ) :
    ¬ (25 ∣ p ^ 4 + p ^ 3 + p ^ 2 + p + 1) := by
  have hmod25 : ∀ x : ZMod 25, x ^ 4 + x ^ 3 + x ^ 2 + x + 1 ≠ 0 := by decide
  intro hdvd
  have hz :
      ((p : ZMod 25) ^ 4 + (p : ZMod 25) ^ 3 + (p : ZMod 25) ^ 2 + (p : ZMod 25) + 1) = 0 := by
    have h := (ZMod.natCast_eq_zero_iff (p ^ 4 + p ^ 3 + p ^ 2 + p + 1) 25).mpr hdvd
    push_cast at h
    exact h
  exact hmod25 (p : ZMod 25) hz

/-- Any prime `r` whose square divides `sigma 1 (p ^ 2)` satisfies `r ≠ 3`, `r % 3 = 1`, `7 ≤ r`,
and `49 ≤ r ^ 2`. -/
theorem sigma_prime_sq_sq_dvd_prime_mod_three {p r : ℕ} (hp : p.Prime) (_hp_odd : Odd p)
    (hr : r.Prime) (hdvd : r ^ 2 ∣ sigma 1 (p ^ 2)) :
    r ≠ 3 ∧ r % 3 = 1 ∧ 7 ≤ r ∧ 49 ≤ r ^ 2 := by
  have hsig : sigma 1 (p ^ 2) = p ^ 2 + p + 1 := by
    rw [sigma_one_apply_prime_pow hp]
    simp [Finset.sum_range_succ]
    ring
  rw [hsig] at hdvd
  have hrd : r ∣ p ^ 2 + p + 1 := (dvd_pow_self r (by decide : 2 ≠ 0)).trans hdvd
  have hne3 : r ≠ 3 := by
    rintro rfl
    exact not_nine_dvd_sq_add_self_add_one p (by simpa using hdvd)
  have hmod3 : r % 3 = 1 := (prime_dvd_sq_add_self_add_one hr hrd).resolve_left hne3
  have hr2 : 2 ≤ r := hr.two_le
  have hr_ne4 : r ≠ 4 := by
    rintro rfl
    exact (by decide : ¬ Nat.Prime 4) hr
  have hr7 : 7 ≤ r := by omega
  exact ⟨hne3, hmod3, hr7, by nlinarith⟩

/-- Any prime `r` whose square divides `sigma 1 (p ^ 4)` (for odd prime `p`) satisfies `r ≠ 5`,
`r % 5 = 1`, `11 ≤ r`, and `121 ≤ r ^ 2`. -/
theorem sigma_prime_pow_four_sq_dvd_prime_mod_five {p r : ℕ} (hp : p.Prime) (hp_odd : Odd p)
    (hr : r.Prime) (hdvd : r ^ 2 ∣ sigma 1 (p ^ 4)) :
    r ≠ 5 ∧ r % 5 = 1 ∧ 11 ≤ r ∧ 121 ≤ r ^ 2 := by
  have hsig : sigma 1 (p ^ 4) = p ^ 4 + p ^ 3 + p ^ 2 + p + 1 := by
    rw [sigma_one_apply_prime_pow hp]
    simp [Finset.sum_range_succ]
    ring
  rw [hsig] at hdvd
  have hrd : r ∣ p ^ 4 + p ^ 3 + p ^ 2 + p + 1 := (dvd_pow_self r (by decide : 2 ≠ 0)).trans hdvd
  have hne5 : r ≠ 5 := by
    rintro rfl
    exact not_twenty_five_dvd_quartic_sum p (by simpa using hdvd)
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    have := hp_odd.not_two_dvd_nat
    omega
  have hprops := quartic_sigma_properties hp hp3
  have hr_norm : r ∣ normalizedQuarticSum p := by
    by_cases hp5 : p % 5 = 1
    · have h5dvd : 5 ∣ p ^ 4 + p ^ 3 + p ^ 2 + p + 1 := by
        have hc : p ≡ 1 [MOD 5] := hp5
        have hpoly : p ^ 4 + p ^ 3 + p ^ 2 + p + 1 ≡ 1 ^ 4 + 1 ^ 3 + 1 ^ 2 + 1 + 1 [MOD 5] :=
          ((((hc.pow 4).add (hc.pow 3)).add (hc.pow 2)).add hc).add (Nat.ModEq.refl 1)
        exact Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using hpoly)
      have hmul : 5 * normalizedQuarticSum p = p ^ 4 + p ^ 3 + p ^ 2 + p + 1 := by
        simp only [normalizedQuarticSum, ite_eq_left hp5]
        exact Nat.mul_div_cancel' h5dvd
      rw [← hmul] at hrd
      refine (hr.dvd_mul.mp hrd).resolve_left fun h5 => ?_
      exact hne5 (((Nat.dvd_prime (by decide : Nat.Prime 5)).mp h5).resolve_left hr.ne_one)
    · simpa [normalizedQuarticSum, ite_eq_right hp5] using hrd
  have hmod5 : r % 5 = 1 := hprops.2.2.2 r hr hr_norm
  have hodd_sum : Odd (p ^ 4 + p ^ 3 + p ^ 2 + p + 1) := by
    rcases Nat.odd_iff.mp hp_odd with hp_mod
    have hpow4 : (p ^ 4) % 2 = 1 := by simp [Nat.pow_mod, hp_mod]
    have hpow3 : (p ^ 3) % 2 = 1 := by simp [Nat.pow_mod, hp_mod]
    have hpow2 : (p ^ 2) % 2 = 1 := by simp [Nat.pow_mod, hp_mod]
    exact Nat.odd_iff.mpr (by omega)
  have hne2 : r ≠ 2 := by
    rintro rfl
    exact hodd_sum.not_two_dvd_nat hrd
  have hr_odd : Odd r := hr.odd_of_ne_two hne2
  have hr_mod2 : r % 2 = 1 := Nat.odd_iff.mp hr_odd
  have hr_gt1 := hr.one_lt
  have hr11 : 11 ≤ r := by omega
  exact ⟨hne5, hmod5, hr11, by nlinarith⟩

/-! ## 2. Vanishing Local Repeat Excess ↔ All Components Squarefree -/

private theorem cardFactors_eq_primeFactors_card_iff_squarefree {n : ℕ} (hn : n ≠ 0) :
    cardFactors n = n.primeFactors.card ↔ Squarefree n := by
  have hsum : cardFactors n = ∑ r ∈ n.primeFactors, n.factorization r := by
    rw [cardFactors_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
  have hcard : n.primeFactors.card = ∑ _r ∈ n.primeFactors, 1 := by
    simp
  have hpos : ∀ r ∈ n.primeFactors, 1 ≤ n.factorization r := fun r hr =>
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
  have hiff1 : cardFactors n = n.primeFactors.card ↔ ∀ r ∈ n.primeFactors, n.factorization r = 1 := by
    rw [hsum, hcard]
    constructor
    · intro heq r hr
      by_contra hne1
      have hr2 : 2 ≤ n.factorization r := by
        have := hpos r hr
        omega
      have hsplit_n :
          (∑ x ∈ n.primeFactors, n.factorization x) =
            n.factorization r + ∑ x ∈ n.primeFactors.erase r, n.factorization x :=
        (Finset.add_sum_erase n.primeFactors n.factorization hr).symm
      have hsplit_1 :
          (∑ _x ∈ n.primeFactors, (1 : ℕ)) =
            1 + ∑ _x ∈ n.primeFactors.erase r, (1 : ℕ) :=
        (Finset.add_sum_erase n.primeFactors (fun _ => (1 : ℕ)) hr).symm
      have hrest :
          ∑ _x ∈ n.primeFactors.erase r, (1 : ℕ) ≤
            ∑ x ∈ n.primeFactors.erase r, n.factorization x :=
        Finset.sum_le_sum fun x hx => hpos x (Finset.mem_of_mem_erase hx)
      omega
    · intro h1
      exact Finset.sum_congr rfl h1
  rw [hiff1, Nat.squarefree_iff_prime_squarefree]
  constructor
  · intro h1 x hx hxx
    have hx_mem : x ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hx, (dvd_mul_right x x).trans hxx, hn⟩
    have hx_pow : x ^ 2 ∣ n := by simpa [pow_two] using hxx
    have h2le : 2 ≤ n.factorization x := (hx.pow_dvd_iff_le_factorization hn).mp hx_pow
    have := h1 x hx_mem
    omega
  · intro hsq r hr
    have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hnot_sq : ¬ r * r ∣ n := hsq r hr_prime
    have hnot_pow : ¬ r ^ 2 ∣ n := by simpa [pow_two] using hnot_sq
    have hlt2 : n.factorization r < 2 := by
      by_contra! hge2
      exact hnot_pow ((hr_prime.pow_dvd_iff_le_factorization hn).mpr hge2)
    have := hpos r hr
    omega

/-- Under the Euler decomposition of an odd perfect number `N`, the local repeat excess vanishes
if and only if every odd component `oddComponentSigma N q p` (`p ∈ N.primeFactors`) is squarefree. -/
theorem localRepeatExcess_eq_zero_iff_all_squarefree {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    localRepeatExcess N q = 0 ↔
      ∀ p ∈ N.primeFactors, Squarefree (oddComponentSigma N q p) := by
  obtain ⟨hprops, _, _, _⟩ := prod_oddComponentSigma_eq_self ho hN hq hq4 he hev
  unfold localRepeatExcess
  rw [Finset.sum_eq_zero_iff]
  refine forall₂_congr fun p hp => ?_
  have hp0 : oddComponentSigma N q p ≠ 0 := by
    have := (hprops p hp).2.2
    omega
  have hle : (oddComponentSigma N q p).primeFactors.card ≤ cardFactors (oddComponentSigma N q p) :=
    primeFactors_card_le_cardFactors (oddComponentSigma N q p)
  rw [← cardFactors_eq_primeFactors_card_iff_squarefree hp0]
  omega

/-! ## 3. Cyclotomic Slope Excess Bounds -/

/-- Combines `cardFactors_eq_primeFactors_add_localRepeat_add_collisionExcess` with
`sharpened_cyclotomic_prime_factor_count`, `sharpened_cyclotomic_slope_three_free`, and the
sixth-power-free `443 ≤ N.primeFactors.card` bound to bound `localRepeatExcess N q + collisionExcess N q`
from below. -/
theorem cyclotomic_slope_excess_bounds {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    13 * N.primeFactors.card + 11 * (twoModThreeLargeSources N q).card ≤
        8 * (localRepeatExcess N q + collisionExcess N q) + 39 ∧
      (¬ 3 ∣ N →
        5 * N.primeFactors.card + 4 * (twoModThreeLargeSources N q).card ≤
          3 * (localRepeatExcess N q + collisionExcess N q) + 7) ∧
      ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
        736 ≤ localRepeatExcess N q + collisionExcess N q) := by
  have hdecomp := cardFactors_eq_primeFactors_add_localRepeat_add_collisionExcess ho hN hq hq4 he hev
  have hlen : cardFactors N = N.primeFactorsList.length := cardFactors_apply
  have h21 := sharpened_cyclotomic_prime_factor_count ho hN hq hq4 he hev
  have h13 :
      13 * N.primeFactors.card + 11 * (twoModThreeLargeSources N q).card ≤
        8 * (localRepeatExcess N q + collisionExcess N q) + 39 := by
    omega
  have h3free :
      ¬ 3 ∣ N →
        5 * N.primeFactors.card + 4 * (twoModThreeLargeSources N q).card ≤
          3 * (localRepeatExcess N q + collisionExcess N q) + 7 := by
    intro h3
    have h8 := (sharpened_cyclotomic_slope_three_free ho hN hq hq4 he hev h3).2
    omega
  refine ⟨h13, h3free, ?_⟩
  intro hfree
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have h443 : 443 ≤ N.primeFactors.card := by
    rcases sixth_power_or_large_support ho hN with ⟨p, hp, hpow⟩ | ⟨hcard, _, _⟩
    · exact (hfree p hp hpow).elim
    · exact hcard
  have h5 := h3free h3
  omega

/-! ## 4. Unconditional 22-Collision Lower Bound & Squarefree Components -/

/-- Combines `thirty_seven_le_total_prime_factor_count`, `seven_le_prime_factor_count_excess`, and
`cyclotomic_slope_excess_bounds` to show `22 ≤ localRepeatExcess N q + collisionExcess N q`
unconditionally (`23` when `¬ 3 ∣ N`), and hence `22 ≤ collisionExcess N q` (`23` when `¬ 3 ∣ N`)
whenever every odd component `oddComponentSigma N q p` is squarefree. -/
theorem squarefree_components_force_22_collisions {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    22 ≤ localRepeatExcess N q + collisionExcess N q ∧
      (¬ 3 ∣ N → 23 ≤ localRepeatExcess N q + collisionExcess N q) ∧
      ((∀ p ∈ N.primeFactors, Squarefree (oddComponentSigma N q p)) →
        22 ≤ collisionExcess N q ∧ (¬ 3 ∣ N → 23 ≤ collisionExcess N q)) := by
  have hdecomp := cardFactors_eq_primeFactors_add_localRepeat_add_collisionExcess ho hN hq hq4 he hev
  have hlen : cardFactors N = N.primeFactorsList.length := cardFactors_apply
  have h37 := thirty_seven_le_total_prime_factor_count ho hN
  have h7 := seven_le_prime_factor_count_excess ho hN
  have h22 : 22 ≤ localRepeatExcess N q + collisionExcess N q := by
    by_cases h15 : N.primeFactors.card ≤ 15
    · omega
    · omega
  have h23 : ¬ 3 ∣ N → 23 ≤ localRepeatExcess N q + collisionExcess N q := by
    intro h3
    have h3slope := (cyclotomic_slope_excess_bounds ho hN hq hq4 he hev).2.1 h3
    by_cases h14 : N.primeFactors.card ≤ 14
    · omega
    · omega
  refine ⟨h22, h23, ?_⟩
  intro hsq
  have hM0 : localRepeatExcess N q = 0 :=
    (localRepeatExcess_eq_zero_iff_all_squarefree ho hN hq hq4 he hev).mpr hsq
  rw [hM0, zero_add] at h22 h23
  exact ⟨h22, h23⟩

end OddPerfect
