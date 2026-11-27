module

public import OddPerfect.CyclotomicOrders
public import OddPerfect.Euler
public import OddPerfect.PrimeReciprocalLog
public import OddPerfect.Harmonic
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Totient identities, radical envelopes, and order-tower obstructions

This module develops four unconditional toolkits for odd perfect numbers `N`:
1. Exact totient–radical and Möbius divisor-sum identities (`odd_perfect_totient_radical_and_moebius_identities`).
2. Two-sided rational/integer totient bounds (`odd_perfect_totient_two_sided_bounds`).
3. Divisibility of the Carmichael function `ArithmeticFunction.carmichael N` by the LCM of component
   lengths `e_p + 1` (`odd_perfect_length_lcm_dvd_carmichael`).
4. Extremal valuation traps, length-drop at unique maximal `(r - 1)`-valuations, 2-adic length
   export from the Euler prime, and divisor-count prime lower bounds.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- Exact totient–radical and Möbius divisor-sum identities for any odd perfect number `N`. -/
theorem odd_perfect_totient_radical_and_moebius_identities {N : ℕ} (_ho : Odd N) (hN : N.Perfect) :
    (∏ p ∈ N.primeFactors, (p ^ (N.factorization p + 1) - 1) =
        2 * (∏ p ∈ N.primeFactors, p) * N.totient) ∧
      ((2 * (N.totient : ℚ)) / (N : ℚ) =
        ∏ p ∈ N.primeFactors, (1 - 1 / ((p : ℚ) ^ (N.factorization p + 1)))) ∧
      ((N.totient : ℚ) / (N : ℚ) =
        ∑ d ∈ N.divisors, (ArithmeticFunction.moebius d : ℚ) / (d : ℚ)) := by
  have hn0 : N ≠ 0 := hN.2.ne'
  have hsig : sigma 1 N = 2 * N :=
    (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN)
  have hprod_sig : (∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p)) = 2 * N := by
    calc ∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p)
        = sigma 1 N := (isMultiplicative_sigma.multiplicative_factorization _ hn0).symm
      _ = 2 * N := hsig
  have hloc : ∀ p ∈ N.primeFactors,
      sigma 1 (p ^ N.factorization p) * (p - 1) = p ^ (N.factorization p + 1) - 1 := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    rw [sigma_one_apply_prime_pow hp_prime]
    have hgeom := geom_sum_mul_add (p - 1) (N.factorization p + 1)
    rw [Nat.sub_add_cancel hp_prime.one_lt.le] at hgeom
    omega
  have hid1 : ∏ p ∈ N.primeFactors, (p ^ (N.factorization p + 1) - 1) =
      2 * (∏ p ∈ N.primeFactors, p) * N.totient := by
    calc ∏ p ∈ N.primeFactors, (p ^ (N.factorization p + 1) - 1)
        = ∏ p ∈ N.primeFactors, (sigma 1 (p ^ N.factorization p) * (p - 1)) :=
          Finset.prod_congr rfl fun p hp => (hloc p hp).symm
      _ = (∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p)) *
            ∏ p ∈ N.primeFactors, (p - 1) := Finset.prod_mul_distrib
      _ = 2 * (N * ∏ p ∈ N.primeFactors, (p - 1)) := by rw [hprod_sig]; ring
      _ = 2 * (N.totient * ∏ p ∈ N.primeFactors, p) := by rw [Nat.totient_mul_prod_primeFactors]
      _ = 2 * (∏ p ∈ N.primeFactors, p) * N.totient := by ring
  have hid2 : (2 * (N.totient : ℚ)) / (N : ℚ) =
      ∏ p ∈ N.primeFactors, (1 - 1 / ((p : ℚ) ^ (N.factorization p + 1))) := by
    have hcast1 : (∏ p ∈ N.primeFactors, ((p : ℚ) ^ (N.factorization p + 1) - 1)) =
        2 * (∏ p ∈ N.primeFactors, (p : ℚ)) * (N.totient : ℚ) := by
      have h := congrArg (Nat.cast (R := ℚ)) hid1
      push_cast at h
      refine Eq.trans ?_ h
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp_pos : 1 ≤ p ^ (N.factorization p + 1) :=
        Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors hp).pos
      rw [Nat.cast_sub hp_pos]
      push_cast
      rfl
    have hden : (∏ p ∈ N.primeFactors, (p : ℚ) ^ (N.factorization p + 1)) =
        (∏ p ∈ N.primeFactors, (p : ℚ)) * (N : ℚ) := by
      calc ∏ p ∈ N.primeFactors, (p : ℚ) ^ (N.factorization p + 1)
          = ∏ p ∈ N.primeFactors, ((p : ℚ) * (p : ℚ) ^ N.factorization p) :=
            Finset.prod_congr rfl fun p _ => by rw [pow_succ']
        _ = (∏ p ∈ N.primeFactors, (p : ℚ)) *
              ∏ p ∈ N.primeFactors, (p : ℚ) ^ N.factorization p := Finset.prod_mul_distrib
        _ = (∏ p ∈ N.primeFactors, (p : ℚ)) * (N : ℚ) := by
            congr 1
            have h := congrArg (Nat.cast (R := ℚ)) (Nat.prod_primeFactors_pow_factorization hn0)
            push_cast at h
            exact h.symm
    have hN_ne : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
    have hrad_ne : (∏ p ∈ N.primeFactors, (p : ℚ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun p hp =>
        Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
    calc (2 * (N.totient : ℚ)) / (N : ℚ)
        = (2 * (∏ p ∈ N.primeFactors, (p : ℚ)) * (N.totient : ℚ)) /
            ((∏ p ∈ N.primeFactors, (p : ℚ)) * (N : ℚ)) := by
          field_simp
      _ = (∏ p ∈ N.primeFactors, ((p : ℚ) ^ (N.factorization p + 1) - 1)) /
            (∏ p ∈ N.primeFactors, (p : ℚ) ^ (N.factorization p + 1)) := by
          rw [hcast1, hden]
      _ = ∏ p ∈ N.primeFactors,
            (((p : ℚ) ^ (N.factorization p + 1) - 1) / (p : ℚ) ^ (N.factorization p + 1)) := by
          rw [Finset.prod_div_distrib]
      _ = ∏ p ∈ N.primeFactors, (1 - 1 / ((p : ℚ) ^ (N.factorization p + 1))) := by
          refine Finset.prod_congr rfl fun p hp => ?_
          have hp_ne : (p : ℚ) ≠ 0 :=
            Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
          field_simp
  have hid3 : (N.totient : ℚ) / (N : ℚ) =
      ∑ d ∈ N.divisors, (ArithmeticFunction.moebius d : ℚ) / (d : ℚ) := by
    let f : ArithmeticFunction ℚ := ⟨fun d => if d = 0 then 0 else (d : ℚ)⁻¹, by simp⟩
    have hf_apply (d : ℕ) : f d = if d = 0 then 0 else (d : ℚ)⁻¹ := rfl
    have hf : f.IsMultiplicative := by
      rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
      refine ⟨by simp [hf_apply], fun {a b} ha hb _ => ?_⟩
      rw [hf_apply, hf_apply, hf_apply,
        ite_eq_right_iff.mpr (fun h => False.elim (mul_ne_zero ha hb h)),
        ite_eq_right_iff.mpr (fun h => False.elim (ha h)),
        ite_eq_right_iff.mpr (fun h => False.elim (hb h))]
      rw [Nat.cast_mul, mul_inv]
    have hmob := hf.prodPrimeFactors_one_sub f hn0
    have hlhs : ∏ p ∈ N.primeFactors, (1 - f p) = (N.totient : ℚ) / (N : ℚ) := by
      have hN_ne : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
      have htot := Nat.totient_eq_mul_prod_factors N
      rw [htot, mul_div_cancel_left₀ _ hN_ne]
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp0 : p ≠ 0 := (Nat.prime_of_mem_primeFactors hp).ne_zero
      simp [f, hp0]
    have hrhs : ∑ d ∈ N.divisors, (ArithmeticFunction.moebius d : ℚ) * f d =
        ∑ d ∈ N.divisors, (ArithmeticFunction.moebius d : ℚ) / (d : ℚ) := by
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
      simp [f, hd0, div_eq_mul_inv]
    rw [hlhs, hrhs] at hmob
    exact hmob
  exact ⟨hid1, hid2, hid3⟩

private lemma prod_one_sub_inv_sq_lower_bound (M : ℕ) :
    (3 * (M : ℚ) + 5) / (4 * (M : ℚ) + 5) ≤
      ∏ k ∈ Finset.range M, (1 - 1 / ((2 * (k : ℚ) + 3) ^ 2)) := by
  induction M with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ]
    have hfac_pos : 0 < 1 - 1 / ((2 * (m : ℚ) + 3) ^ 2) := by
      have hm : (0 : ℚ) ≤ m := Nat.cast_nonneg m
      have hden : (1 : ℚ) < (2 * (m : ℚ) + 3) ^ 2 := by nlinarith
      rw [sub_pos, div_lt_one (by positivity)]
      exact hden
    have hstep : ((3 * (m : ℚ) + 5) / (4 * (m : ℚ) + 5)) *
        (1 - 1 / ((2 * (m : ℚ) + 3) ^ 2)) ≤
        (∏ k ∈ Finset.range m, (1 - 1 / ((2 * (k : ℚ) + 3) ^ 2))) *
          (1 - 1 / ((2 * (m : ℚ) + 3) ^ 2)) :=
      mul_le_mul_of_nonneg_right ih hfac_pos.le
    refine le_trans ?_ hstep
    push_cast
    have hm : (0 : ℚ) ≤ m := Nat.cast_nonneg m
    have hd1 : (0 : ℚ) < 4 * ((m : ℚ) + 1) + 5 := by linarith
    have hd2 : (0 : ℚ) < 4 * (m : ℚ) + 5 := by linarith
    have hd3 : (0 : ℚ) < (2 * (m : ℚ) + 3) ^ 2 := by positivity
    have hid : 1 - 1 / ((2 * (m : ℚ) + 3) ^ 2) =
        (4 * ((m : ℚ) + 1) * ((m : ℚ) + 2)) / ((2 * (m : ℚ) + 3) ^ 2) := by
      field_simp
      ring
    rw [hid, div_mul_div_comm, div_le_div_iff₀ hd1 (mul_pos hd2 hd3)]
    have hdiff : (3 * (m : ℚ) + 5) * (4 * ((m : ℚ) + 1) * ((m : ℚ) + 2)) *
          (4 * ((m : ℚ) + 1) + 5) -
        (3 * ((m : ℚ) + 1) + 5) * ((4 * (m : ℚ) + 5) * (2 * (m : ℚ) + 3) ^ 2) =
        (m : ℚ) * (8 * (m : ℚ) + 13) := by
      ring
    have hnn : 0 ≤ (m : ℚ) * (8 * (m : ℚ) + 13) := by positivity
    linarith

/-- Sharp two-sided rational and integer bounds on `N.totient` for any odd perfect number `N`. -/
theorem odd_perfect_totient_two_sided_bounds {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    2 * N.totient < N ∧
      (3 * N.primeFactors.card + 5) * N < 2 * (4 * N.primeFactors.card + 5) * N.totient ∧
      3 * N < 8 * N.totient ∧
      (¬ 3 ∣ N → 27 * N < 64 * N.totient) := by
  have hN_gt1 : 1 < N := by
    by_contra! hle
    have hN1 : N = 1 := by have := hN.2; omega
    subst hN1
    exact (by decide : ¬ Nat.Perfect 1) hN
  have hne : N.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hN_gt1
  have hN_pos : (0 : ℚ) < (N : ℚ) := Nat.cast_pos.mpr hN.2
  have hid := (odd_perfect_totient_radical_and_moebius_identities ho hN).2.1
  have hlt1 : 2 * N.totient < N := by
    have hprod_lt :
        ∏ p ∈ N.primeFactors, (1 - 1 / ((p : ℚ) ^ (N.factorization p + 1))) <
          ∏ _p ∈ N.primeFactors, (1 : ℚ) := by
      apply Finset.prod_lt_prod_of_nonempty₀
      · intro p hp
        have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
        have hpow : (1 : ℚ) < (p : ℚ) ^ (N.factorization p + 1) :=
          one_lt_pow₀ hp1 (Nat.succ_ne_zero _)
        have hdiv : 1 / ((p : ℚ) ^ (N.factorization p + 1)) < 1 := by
          rw [div_lt_one (by positivity)]
          exact hpow
        linarith
      · intro p hp
        have hp1 : 1 < p := (Nat.prime_of_mem_primeFactors hp).one_lt
        have hpow : (1 : ℚ) < (p : ℚ) ^ (N.factorization p + 1) :=
          one_lt_pow₀ (by exact_mod_cast hp1) (Nat.succ_ne_zero _)
        have hinv : 0 < 1 / ((p : ℚ) ^ (N.factorization p + 1)) := by positivity
        linarith
      · exact hne
    simp only [Finset.prod_const_one] at hprod_lt
    rw [← hid, div_lt_one hN_pos] at hprod_lt
    exact_mod_cast hprod_lt
  obtain ⟨q, hq_mem, _, _, h_even⟩ := euler_exponents ho hN
  have hq_not_singleton : (N.primeFactors.erase q).Nonempty := by
    by_contra h_empty
    rw [Finset.not_nonempty_iff_eq_empty] at h_empty
    have hsub : N.primeFactors ⊆ {q} := by
      intro p hp
      by_contra hpq
      have : p ∈ N.primeFactors.erase q := Finset.mem_erase.mpr ⟨Finset.mem_singleton.not.mp hpq, hp⟩
      rw [h_empty] at this
      simp at this
    have hcard1 : N.primeFactors = {q} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨hq_mem, fun p hp => Finset.mem_singleton.mp (hsub hp)⟩
    have hsup := perfect_support_product_bound hN
    rw [hcard1, Finset.prod_singleton, Finset.prod_singleton] at hsup
    have hq_prime := Nat.prime_of_mem_primeFactors hq_mem
    have := hq_prime.two_le
    omega
  obtain ⟨r, hr_er⟩ := hq_not_singleton
  have hr_mem : r ∈ N.primeFactors := Finset.mem_of_mem_erase hr_er
  have hr_ne : r ≠ q := (Finset.mem_erase.mp hr_er).1
  have hr_even : Even (N.factorization r) := h_even r hr_ne
  have hr_pos : 0 < N.factorization r := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr_mem)
  have hr_ge2 : 2 ≤ N.factorization r := by
    obtain ⟨t, ht⟩ := hr_even
    omega
  have hprod_sq_lt :
      ∏ p ∈ N.primeFactors, (1 - 1 / ((p : ℚ) ^ 2)) <
        ∏ p ∈ N.primeFactors, (1 - 1 / ((p : ℚ) ^ (N.factorization p + 1))) := by
    rw [← Finset.mul_prod_erase N.primeFactors (fun p => 1 - 1 / ((p : ℚ) ^ 2)) hr_mem,
      ← Finset.mul_prod_erase N.primeFactors
        (fun p => 1 - 1 / ((p : ℚ) ^ (N.factorization p + 1))) hr_mem]
    have hr1 : (1 : ℚ) < (r : ℚ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hr_mem).one_lt
    have hr_lhs_pos : 0 < 1 - 1 / ((r : ℚ) ^ 2) := by
      have hpow : (1 : ℚ) < (r : ℚ) ^ 2 := by nlinarith
      rw [sub_pos, div_lt_one (by positivity)]
      exact hpow
    have hr_lt : 1 - 1 / ((r : ℚ) ^ 2) < 1 - 1 / ((r : ℚ) ^ (N.factorization r + 1)) := by
      have hpow_lt : (r : ℚ) ^ 2 < (r : ℚ) ^ (N.factorization r + 1) :=
        pow_lt_pow_right₀ hr1 (by omega)
      have hdiv_lt : 1 / ((r : ℚ) ^ (N.factorization r + 1)) < 1 / ((r : ℚ) ^ 2) :=
        one_div_lt_one_div_of_lt (by positivity) hpow_lt
      linarith
    have hrest_pos : 0 < ∏ p ∈ N.primeFactors.erase r, (1 - 1 / ((p : ℚ) ^ 2)) := by
      apply Finset.prod_pos
      intro p hp
      have hp1 : (1 : ℚ) < (p : ℚ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).one_lt
      have hpow : (1 : ℚ) < (p : ℚ) ^ 2 := by nlinarith
      rw [sub_pos, div_lt_one (by positivity)]
      exact hpow
    have hrest_le :
        ∏ p ∈ N.primeFactors.erase r, (1 - 1 / ((p : ℚ) ^ 2)) ≤
          ∏ p ∈ N.primeFactors.erase r, (1 - 1 / ((p : ℚ) ^ (N.factorization p + 1))) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        have hp1 : (1 : ℚ) < (p : ℚ) := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).one_lt
        have hpow : (1 : ℚ) < (p : ℚ) ^ 2 := by nlinarith
        rw [sub_nonneg, div_le_one (by positivity)]
        exact hpow.le
      · intro p hp
        have hp_mem := Finset.mem_of_mem_erase hp
        have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp_mem).one_lt
        have hpe : 1 ≤ N.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp_mem)
        have hpow_le : (p : ℚ) ^ 2 ≤ (p : ℚ) ^ (N.factorization p + 1) :=
          pow_le_pow_right₀ hp1.le (by omega)
        have hdiv_le : 1 / ((p : ℚ) ^ (N.factorization p + 1)) ≤ 1 / ((p : ℚ) ^ 2) :=
          one_div_le_one_div_of_le (by positivity) hpow_le
        linarith
    have hrest_pos' :
        0 < ∏ p ∈ N.primeFactors.erase r, (1 - 1 / ((p : ℚ) ^ (N.factorization p + 1))) :=
      lt_of_lt_of_le hrest_pos hrest_le
    calc (1 - 1 / ((r : ℚ) ^ 2)) * ∏ p ∈ N.primeFactors.erase r, (1 - 1 / ((p : ℚ) ^ 2))
        ≤ (1 - 1 / ((r : ℚ) ^ 2)) *
            ∏ p ∈ N.primeFactors.erase r, (1 - 1 / ((p : ℚ) ^ (N.factorization p + 1))) :=
          mul_le_mul_of_nonneg_left hrest_le hr_lhs_pos.le
      _ < (1 - 1 / ((r : ℚ) ^ (N.factorization r + 1))) *
            ∏ p ∈ N.primeFactors.erase r, (1 - 1 / ((p : ℚ) ^ (N.factorization p + 1))) :=
          mul_lt_mul_of_pos_right hr_lt hrest_pos'
  let ω := N.primeFactors.card
  let emb := N.primeFactors.orderEmbOfFin (rfl : N.primeFactors.card = ω)
  have hemb_odd : ∀ i : Fin ω, Odd (emb i) := fun i =>
    ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors (Finset.orderEmbOfFin_mem _ _ i))
  have hemb_ge3 : ∀ i : Fin ω, 3 ≤ emb i := by
    intro i
    have hi_mem := Finset.orderEmbOfFin_mem N.primeFactors (rfl : N.primeFactors.card = ω) i
    have hi_prime : (emb i).Prime := Nat.prime_of_mem_primeFactors hi_mem
    have hi_odd := hemb_odd i
    have hi2 : emb i ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hi_odd)
    have h2le : 2 ≤ emb i := hi_prime.two_le
    omega
  have hemb_lower : ∀ (k : ℕ) (hk : k < ω), 2 * k + 3 ≤ emb ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk
      simpa using hemb_ge3 ⟨0, hk⟩
    | succ m ihm =>
      intro hk
      have hlt : emb ⟨m, Nat.lt_of_succ_lt hk⟩ < emb ⟨m + 1, hk⟩ :=
        emb.strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self m))
      have hm := ihm (Nat.lt_of_succ_lt hk)
      have hodd := hemb_odd ⟨m + 1, hk⟩
      obtain ⟨t, ht⟩ := hodd
      omega
  have hprod_emb :
      ∏ p ∈ N.primeFactors, (1 - 1 / ((p : ℚ) ^ 2)) =
        ∏ i : Fin ω, (1 - 1 / ((emb i : ℚ) ^ 2)) := by
    nth_rw 1 [← Finset.map_orderEmbOfFin_univ N.primeFactors (rfl : N.primeFactors.card = ω)]
    rw [Finset.prod_map]
    rfl
  have hprod_range_le :
      ∏ k ∈ Finset.range ω, (1 - 1 / ((2 * (k : ℚ) + 3) ^ 2)) ≤
        ∏ p ∈ N.primeFactors, (1 - 1 / ((p : ℚ) ^ 2)) := by
    rw [hprod_emb, ← Fin.prod_univ_eq_prod_range]
    apply Finset.prod_le_prod₀
    · intro i _
      have hi : (0 : ℚ) ≤ (i : ℕ) := Nat.cast_nonneg _
      have hden : (1 : ℚ) < (2 * ((i : ℕ) : ℚ) + 3) ^ 2 := by nlinarith
      rw [sub_nonneg, div_le_one (by positivity)]
      exact hden.le
    · intro i _
      have hle : 2 * (i : ℕ) + 3 ≤ emb i := hemb_lower i.1 i.2
      have hle_q : 2 * ((i : ℕ) : ℚ) + 3 ≤ (emb i : ℚ) := by exact_mod_cast hle
      have hpos : (0 : ℚ) < 2 * ((i : ℕ) : ℚ) + 3 := by positivity
      have hsq : (2 * ((i : ℕ) : ℚ) + 3) ^ 2 ≤ (emb i : ℚ) ^ 2 := by nlinarith
      have hdiv : 1 / ((emb i : ℚ) ^ 2) ≤ 1 / ((2 * ((i : ℕ) : ℚ) + 3) ^ 2) :=
        one_div_le_one_div_of_le (by positivity) hsq
      linarith
  have hmain_q :
      (3 * (ω : ℚ) + 5) / (4 * (ω : ℚ) + 5) < (2 * (N.totient : ℚ)) / (N : ℚ) := by
    calc (3 * (ω : ℚ) + 5) / (4 * (ω : ℚ) + 5)
        ≤ ∏ k ∈ Finset.range ω, (1 - 1 / ((2 * (k : ℚ) + 3) ^ 2)) :=
          prod_one_sub_inv_sq_lower_bound ω
      _ ≤ ∏ p ∈ N.primeFactors, (1 - 1 / ((p : ℚ) ^ 2)) := hprod_range_le
      _ < ∏ p ∈ N.primeFactors, (1 - 1 / ((p : ℚ) ^ (N.factorization p + 1))) := hprod_sq_lt
      _ = (2 * (N.totient : ℚ)) / (N : ℚ) := hid.symm
  have hmain : (3 * ω + 5) * N < 2 * (4 * ω + 5) * N.totient := by
    have hden : (0 : ℚ) < 4 * (ω : ℚ) + 5 := by positivity
    rw [div_lt_div_iff₀ hden hN_pos] at hmain_q
    exact_mod_cast (show ((3 * ω + 5 : ℕ) : ℚ) * (N : ℚ) <
        ((2 * (4 * ω + 5) * N.totient : ℕ) : ℚ) by
      push_cast
      linarith)
  have h3_8 : 3 * N < 8 * N.totient := by
    have hstep1 : 3 * (4 * ω + 5) * N < 4 * ((3 * ω + 5) * N) := by
      have hmul : 3 * (4 * ω + 5) < 4 * (3 * ω + 5) := by omega
      calc 3 * (4 * ω + 5) * N < 4 * (3 * ω + 5) * N := Nat.mul_lt_mul_of_pos_right hmul hN.2
        _ = 4 * ((3 * ω + 5) * N) := by ring
    have hstep2 : 4 * ((3 * ω + 5) * N) < 4 * (2 * (4 * ω + 5) * N.totient) :=
      Nat.mul_lt_mul_of_pos_left hmain (by decide)
    have hcomb : (4 * ω + 5) * (3 * N) < (4 * ω + 5) * (8 * N.totient) := by
      have hlt := hstep1.trans hstep2
      linarith
    exact Nat.lt_of_mul_lt_mul_left hcomb
  have hnot3 : ¬ 3 ∣ N → 27 * N < 64 * N.totient := by
    intro hn3
    have hemb_ge5 : ∀ i : Fin ω, 5 ≤ emb i := by
      intro i
      have hi_mem := Finset.orderEmbOfFin_mem N.primeFactors (rfl : N.primeFactors.card = ω) i
      have hi_ne3 : emb i ≠ 3 := fun h => hn3 (h ▸ Nat.dvd_of_mem_primeFactors hi_mem)
      have hge3 := hemb_ge3 i
      have hodd := hemb_odd i
      obtain ⟨t, ht⟩ := hodd
      omega
    have hemb_lower5 : ∀ (k : ℕ) (hk : k < ω), 2 * k + 5 ≤ emb ⟨k, hk⟩ := by
      intro k
      induction k with
      | zero =>
        intro hk
        simpa using hemb_ge5 ⟨0, hk⟩
      | succ m ihm =>
        intro hk
        have hlt : emb ⟨m, Nat.lt_of_succ_lt hk⟩ < emb ⟨m + 1, hk⟩ :=
          emb.strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self m))
        have hm := ihm (Nat.lt_of_succ_lt hk)
        have hodd := hemb_odd ⟨m + 1, hk⟩
        obtain ⟨t, ht⟩ := hodd
        omega
    have hprod5_le :
        ∏ k ∈ Finset.range ω, (1 - 1 / ((2 * (k : ℚ) + 5) ^ 2)) ≤
          ∏ p ∈ N.primeFactors, (1 - 1 / ((p : ℚ) ^ 2)) := by
      rw [hprod_emb, ← Fin.prod_univ_eq_prod_range]
      apply Finset.prod_le_prod₀
      · intro i _
        have hi : (0 : ℚ) ≤ (i : ℕ) := Nat.cast_nonneg _
        have hden : (1 : ℚ) < (2 * ((i : ℕ) : ℚ) + 5) ^ 2 := by nlinarith
        rw [sub_nonneg, div_le_one (by positivity)]
        exact hden.le
      · intro i _
        have hle : 2 * (i : ℕ) + 5 ≤ emb i := hemb_lower5 i.1 i.2
        have hle_q : 2 * ((i : ℕ) : ℚ) + 5 ≤ (emb i : ℚ) := by exact_mod_cast hle
        have hpos : (0 : ℚ) < 2 * ((i : ℕ) : ℚ) + 5 := by positivity
        have hsq : (2 * ((i : ℕ) : ℚ) + 5) ^ 2 ≤ (emb i : ℚ) ^ 2 := by nlinarith
        have hdiv : 1 / ((emb i : ℚ) ^ 2) ≤ 1 / ((2 * ((i : ℕ) : ℚ) + 5) ^ 2) :=
          one_div_le_one_div_of_le (by positivity) hsq
        linarith
    have hshift :
        (8 / 9 : ℚ) * ∏ k ∈ Finset.range ω, (1 - 1 / ((2 * (k : ℚ) + 5) ^ 2)) =
          ∏ k ∈ Finset.range (ω + 1), (1 - 1 / ((2 * (k : ℚ) + 3) ^ 2)) := by
      rw [Finset.prod_range_succ']
      have h0 : (1 - 1 / ((2 * ((0 : ℕ) : ℚ) + 3) ^ 2)) = (8 / 9 : ℚ) := by norm_num
      rw [h0, mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      push_cast
      ring_nf
    have h34_lt : (3 / 4 : ℚ) <
        (3 * ((ω + 1 : ℕ) : ℚ) + 5) / (4 * ((ω + 1 : ℕ) : ℚ) + 5) := by
      have hω : (0 : ℚ) ≤ ω := Nat.cast_nonneg ω
      rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
      push_cast
      linarith
    have hbound5 :
        (27 / 32 : ℚ) < ∏ k ∈ Finset.range ω, (1 - 1 / ((2 * (k : ℚ) + 5) ^ 2)) := by
      have hlow := h34_lt.trans_le (prod_one_sub_inv_sq_lower_bound (ω + 1))
      rw [← hshift] at hlow
      linarith
    have hq27 : (27 / 32 : ℚ) < (2 * (N.totient : ℚ)) / (N : ℚ) := by
      calc (27 / 32 : ℚ)
          < ∏ k ∈ Finset.range ω, (1 - 1 / ((2 * (k : ℚ) + 5) ^ 2)) := hbound5
        _ ≤ ∏ p ∈ N.primeFactors, (1 - 1 / ((p : ℚ) ^ 2)) := hprod5_le
        _ < ∏ p ∈ N.primeFactors, (1 - 1 / ((p : ℚ) ^ (N.factorization p + 1))) := hprod_sq_lt
        _ = (2 * (N.totient : ℚ)) / (N : ℚ) := hid.symm
    rw [div_lt_div_iff₀ (by norm_num) hN_pos] at hq27
    exact_mod_cast (show ((27 * N : ℕ) : ℚ) < ((64 * N.totient : ℕ) : ℚ) by
      push_cast
      linarith)
  exact ⟨hlt1, hmain, h3_8, hnot3⟩

/-- The LCM of component lengths `e_p + 1` divides the LCM of `r - 1`, which in turn divides
`ArithmeticFunction.carmichael N`. -/
theorem odd_perfect_length_lcm_dvd_carmichael {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    (N.primeFactors.lcm fun p => N.factorization p + 1) ∣
        (N.primeFactors.lcm fun r => r - 1) ∧
      (N.primeFactors.lcm fun r => r - 1) ∣ ArithmeticFunction.carmichael N ∧
      (N.primeFactors.lcm fun p => N.factorization p + 1) ∣ ArithmeticFunction.carmichael N ∧
      ∀ p ∈ N.primeFactors, N.factorization p + 1 ∣ ArithmeticFunction.carmichael N := by
  have hdvd1 : (N.primeFactors.lcm fun p => N.factorization p + 1) ∣
      (N.primeFactors.lcm fun r => r - 1) := by
    apply Finset.lcm_dvd
    intro p hp
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro l k hl hlk
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · simp
    · have h1 : 1 < l ^ k := one_lt_pow₀ hl.one_lt hk_pos.ne'
      obtain ⟨r, hr_er, _, hdr⟩ := exists_forced_order_of_length hN ho
        (Nat.prime_of_mem_primeFactors hp) rfl h1 hlk
      exact hdr.trans (Finset.dvd_lcm (Finset.mem_of_mem_erase hr_er))
  have hdvd2 : (N.primeFactors.lcm fun r => r - 1) ∣ ArithmeticFunction.carmichael N := by
    apply Finset.lcm_dvd
    intro r hr
    have hr_prime := Nat.prime_of_mem_primeFactors hr
    rw [← ArithmeticFunction.carmichael_of_prime hr_prime]
    exact ArithmeticFunction.carmichael_dvd (Nat.dvd_of_mem_primeFactors hr)
  have hdvd3 : (N.primeFactors.lcm fun p => N.factorization p + 1) ∣
      ArithmeticFunction.carmichael N := hdvd1.trans hdvd2
  have hdvd4 : ∀ p ∈ N.primeFactors, N.factorization p + 1 ∣ ArithmeticFunction.carmichael N :=
    fun _ hp => (Finset.dvd_lcm hp).trans hdvd3
  exact ⟨hdvd1, hdvd2, hdvd3, hdvd4⟩

/-- Extremal valuation trap: for every `r ∈ N.primeFactors` and prime `l`, the `l`-adic valuation
of `N.factorization r + 1` cannot exceed the supremum of `(s - 1).factorization l` over
`s ∈ N.primeFactors.erase r`. -/
theorem extremal_sub_one_valuation_trap {N : ℕ} (ho : Odd N) (hN : N.Perfect) (l : ℕ)
    (hl : l.Prime) (r : ℕ) (hr : r ∈ N.primeFactors) :
    (N.factorization r + 1).factorization l ≤
      (N.primeFactors.erase r).sup (fun s => (s - 1).factorization l) := by
  set v := (N.factorization r + 1).factorization l
  rcases Nat.eq_zero_or_pos v with hv0 | hv_pos
  · rw [hv0]
    exact Nat.zero_le _
  · have h1 : 1 < l ^ v := one_lt_pow₀ hl.one_lt hv_pos.ne'
    have hdvd : l ^ v ∣ N.factorization r + 1 := Nat.ordProj_dvd _ _
    obtain ⟨s, hs_er, _, hds⟩ := exists_forced_order_of_length hN ho
      (Nat.prime_of_mem_primeFactors hr) rfl h1 hdvd
    have hs_mem : s ∈ N.primeFactors := Finset.mem_of_mem_erase hs_er
    have hs_prime := Nat.prime_of_mem_primeFactors hs_mem
    have hs1_ne0 : s - 1 ≠ 0 := (Nat.sub_pos_of_lt hs_prime.one_lt).ne'
    have hv_le : v ≤ (s - 1).factorization l :=
      (hl.pow_dvd_iff_le_factorization hs1_ne0).mp hds
    exact hv_le.trans (Finset.le_sup (f := fun s => (s - 1).factorization l) hs_er)

/-- If `r ∈ N.primeFactors` has the strictly largest `(r - 1).factorization l` (and it is positive),
then `N.factorization r + 1` has strictly smaller `l`-adic valuation. -/
theorem unique_max_sub_one_valuation_length_drop {N : ℕ} (ho : Odd N) (hN : N.Perfect)
    (l : ℕ) (hl : l.Prime) (r : ℕ) (hr : r ∈ N.primeFactors)
    (hpos : 0 < (r - 1).factorization l)
    (hmax : ∀ s ∈ N.primeFactors, s ≠ r → (s - 1).factorization l < (r - 1).factorization l) :
    (N.factorization r + 1).factorization l < (r - 1).factorization l ∧
      ¬ l ^ (r - 1).factorization l ∣ N.factorization r + 1 ∧
      ((r - 1).factorization l = 1 → ¬ l ∣ N.factorization r + 1) := by
  have htrap := extremal_sub_one_valuation_trap ho hN l hl r hr
  have hsup_lt : (N.primeFactors.erase r).sup (fun s => (s - 1).factorization l) <
      (r - 1).factorization l := by
    rw [Finset.sup_lt_iff hpos]
    intro s hs_er
    exact hmax s (Finset.mem_of_mem_erase hs_er) (Finset.mem_erase.mp hs_er).1
  have hlt : (N.factorization r + 1).factorization l < (r - 1).factorization l :=
    lt_of_le_of_lt htrap hsup_lt
  have hndvd_pow : ¬ l ^ (r - 1).factorization l ∣ N.factorization r + 1 := by
    intro hd
    have hle := (hl.pow_dvd_iff_le_factorization (Nat.succ_ne_zero _)).mp hd
    rw [Nat.succ_eq_add_one] at hle
    omega
  have hndvd_one : (r - 1).factorization l = 1 → ¬ l ∣ N.factorization r + 1 := by
    intro h1 hd
    apply hndvd_pow
    rw [h1, pow_one]
    exact hd
  exact ⟨hlt, hndvd_pow, hndvd_one⟩

/-- In Euler form, the 2-adic valuation of `N.factorization q + 1` is at least `1` and is exported
to some non-Euler prime `s ∈ N.primeFactors.erase q`. -/
theorem euler_two_adic_length_exported_to_non_euler {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (_hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (_hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    1 ≤ (N.factorization q + 1).factorization 2 ∧
      ∃ s ∈ N.primeFactors.erase q,
        2 ^ (N.factorization q + 1).factorization 2 ∣ s - 1 ∧
          (N.factorization q + 1).factorization 2 ≤ (s - 1).factorization 2 := by
  have h2dvd : 2 ∣ N.factorization q + 1 := by omega
  have hv1 : 1 ≤ (N.factorization q + 1).factorization 2 :=
    (Nat.prime_two.dvd_iff_one_le_factorization (Nat.succ_ne_zero _)).mp h2dvd
  have h1 : 1 < 2 ^ (N.factorization q + 1).factorization 2 :=
    one_lt_pow₀ (by decide : 1 < 2) (by omega)
  obtain ⟨s, hs_er, _, hds⟩ := exists_forced_order_of_length hN ho
    (Nat.prime_of_mem_primeFactors hq) rfl h1 (Nat.ordProj_dvd _ _)
  have hs_prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hs_er)
  have hs1_ne0 : s - 1 ≠ 0 := (Nat.sub_pos_of_lt hs_prime.one_lt).ne'
  have hv_le : (N.factorization q + 1).factorization 2 ≤ (s - 1).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hs1_ne0).mp hds
  exact ⟨hv1, s, hs_er, hds, hv_le⟩

/-- Every odd prime dividing `N.divisors.card` divides some component length `N.factorization p + 1`
and forces a prime `r ∈ N.primeFactors` with `l ∣ r - 1` and `2 * l + 1 ≤ r`. -/
theorem odd_prime_dvd_divisor_count_lt_half_max_prime {N l : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hl : l.Prime) (hlo : Odd l) (hldvd : l ∣ N.divisors.card) :
    (∃ p ∈ N.primeFactors, l ∣ N.factorization p + 1) ∧
      (∃ r ∈ N.primeFactors, l ∣ r - 1 ∧ 2 * l + 1 ≤ r) := by
  rw [Nat.card_divisors hN.2.ne'] at hldvd
  have hp_ex : ∃ p ∈ N.primeFactors, l ∣ N.factorization p + 1 := by
    classical
    revert hldvd
    refine Finset.induction_on N.primeFactors ?_ ?_
    · intro h1
      simp only [Finset.prod_empty] at h1
      exact (hl.not_dvd_one h1).elim
    · intro a s has ih hprod
      rw [Finset.prod_insert has] at hprod
      rcases hl.dvd_mul.mp hprod with ha | hs
      · exact ⟨a, Finset.mem_insert_self a s, ha⟩
      · obtain ⟨p, hp_mem, hlp⟩ := ih hs
        exact ⟨p, Finset.mem_insert_of_mem hp_mem, hlp⟩
  obtain ⟨p, hp_mem, hlp⟩ := hp_ex
  obtain ⟨r, hr_er, _, hlr⟩ := exists_forced_order_of_length hN ho
    (Nat.prime_of_mem_primeFactors hp_mem) rfl hl.one_lt hlp
  have hr_mem : r ∈ N.primeFactors := Finset.mem_of_mem_erase hr_er
  have hr_prime := Nat.prime_of_mem_primeFactors hr_mem
  have hr_odd : Odd r := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr_mem)
  have hr_sub_pos : 0 < r - 1 := Nat.sub_pos_of_lt hr_prime.one_lt
  have h2_dvd : 2 ∣ r - 1 := by
    obtain ⟨t, ht⟩ := hr_odd
    omega
  have hcop : Nat.Coprime 2 l := Nat.prime_two.coprime_iff_not_dvd.mpr hlo.not_two_dvd_nat
  have h2l_dvd : 2 * l ∣ r - 1 := hcop.mul_dvd_of_dvd_of_dvd h2_dvd hlr
  have h2l_le : 2 * l ≤ r - 1 := Nat.le_of_dvd hr_sub_pos h2l_dvd
  exact ⟨⟨p, hp_mem, hlp⟩, ⟨r, hr_mem, hlr, by omega⟩⟩

end OddPerfect
