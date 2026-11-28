module

public import OddPerfect.TotientOrderTower
public import OddPerfect.Harmonic
public import OddPerfect.NearPerfect
public import OddPerfect.DeficientPerfect
public import OddPerfect.LinearEulerSquareDescent
public import OddPerfect.GlobalObstruction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Universal `σ(n) · φ(n)` Rational/Integer Envelope and Specializations

Develops the universal odd `sigma 1 n * n.totient` radical identity and two-sided envelope
across odd integers `n > 1`, with strict strengthening when `n` is non-squarefree, and
specializes it to:
1. Odd Ore-harmonic integers (`odd_oreHarmonic_totient_divisor_envelope`).
2. Odd near-perfect pairs (`odd_nearPerfect_totient_obstruction`).
3. Odd deficient-perfect pairs (`odd_deficientPerfect_totient_bounds`) and linear Euler
   odd perfect squares `N = q * m ^ 2` (`odd_deficientPerfect_and_linear_euler_square_totient_bounds`).
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

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

private lemma odd_prod_one_sub_inv_sq_lower_bound {n : ℕ} (ho : Odd n) :
    (3 * (n.primeFactors.card : ℚ) + 5) / (4 * (n.primeFactors.card : ℚ) + 5) ≤
        ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℚ) ^ 2)) ∧
      (¬ 3 ∣ n → (27 / 32 : ℚ) < ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℚ) ^ 2))) := by
  let ω := n.primeFactors.card
  let emb := n.primeFactors.orderEmbOfFin (rfl : n.primeFactors.card = ω)
  have hemb_odd : ∀ i : Fin ω, Odd (emb i) := fun i =>
    ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors (Finset.orderEmbOfFin_mem _ _ i))
  have hemb_ge3 : ∀ i : Fin ω, 3 ≤ emb i := by
    intro i
    have hi_mem := Finset.orderEmbOfFin_mem n.primeFactors (rfl : n.primeFactors.card = ω) i
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
      ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℚ) ^ 2)) =
        ∏ i : Fin ω, (1 - 1 / ((emb i : ℚ) ^ 2)) := by
    nth_rw 1 [← Finset.map_orderEmbOfFin_univ n.primeFactors (rfl : n.primeFactors.card = ω)]
    rw [Finset.prod_map]
    rfl
  have hprod_range_le :
      ∏ k ∈ Finset.range ω, (1 - 1 / ((2 * (k : ℚ) + 3) ^ 2)) ≤
        ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℚ) ^ 2)) := by
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
  have hlow3 : (3 * (ω : ℚ) + 5) / (4 * (ω : ℚ) + 5) ≤
      ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℚ) ^ 2)) :=
    (prod_one_sub_inv_sq_lower_bound ω).trans hprod_range_le
  have hnot3 : ¬ 3 ∣ n → (27 / 32 : ℚ) < ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℚ) ^ 2)) := by
    intro hn3
    have hemb_ge5 : ∀ i : Fin ω, 5 ≤ emb i := by
      intro i
      have hi_mem := Finset.orderEmbOfFin_mem n.primeFactors (rfl : n.primeFactors.card = ω) i
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
          ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℚ) ^ 2)) := by
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
    exact hbound5.trans_le hprod5_le
  exact ⟨hlow3, hnot3⟩

private lemma prod_one_sub_inv_sq_le_factorization (n : ℕ) :
    ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℚ) ^ 2)) ≤
      ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℚ) ^ (n.factorization p + 1))) := by
  apply Finset.prod_le_prod₀
  · intro p hp
    have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    have hpow : (1 : ℚ) < (p : ℚ) ^ 2 := by nlinarith
    rw [sub_nonneg, div_le_one (by positivity)]
    exact hpow.le
  · intro p hp
    have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    have hpe : 1 ≤ n.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    have hpow_le : (p : ℚ) ^ 2 ≤ (p : ℚ) ^ (n.factorization p + 1) :=
      pow_le_pow_right₀ hp1.le (by omega)
    have hdiv_le : 1 / ((p : ℚ) ^ (n.factorization p + 1)) ≤ 1 / ((p : ℚ) ^ 2) :=
      one_div_le_one_div_of_le (by positivity) hpow_le
    linarith

private lemma prod_one_sub_inv_sq_lt_factorization_of_non_squarefree {n : ℕ}
    (hnsq : ∃ p ∈ n.primeFactors, 2 ≤ n.factorization p) :
    ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℚ) ^ 2)) <
      ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℚ) ^ (n.factorization p + 1))) := by
  obtain ⟨r, hr_mem, hr_ge2⟩ := hnsq
  rw [← Finset.mul_prod_erase n.primeFactors (fun p => 1 - 1 / ((p : ℚ) ^ 2)) hr_mem,
    ← Finset.mul_prod_erase n.primeFactors
      (fun p => 1 - 1 / ((p : ℚ) ^ (n.factorization p + 1))) hr_mem]
  have hr1 : (1 : ℚ) < (r : ℚ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hr_mem).one_lt
  have hr_lhs_pos : 0 < 1 - 1 / ((r : ℚ) ^ 2) := by
    have hpow : (1 : ℚ) < (r : ℚ) ^ 2 := by nlinarith
    rw [sub_pos, div_lt_one (by positivity)]
    exact hpow
  have hr_lt : 1 - 1 / ((r : ℚ) ^ 2) < 1 - 1 / ((r : ℚ) ^ (n.factorization r + 1)) := by
    have hpow_lt : (r : ℚ) ^ 2 < (r : ℚ) ^ (n.factorization r + 1) :=
      pow_lt_pow_right₀ hr1 (by omega)
    have hdiv_lt : 1 / ((r : ℚ) ^ (n.factorization r + 1)) < 1 / ((r : ℚ) ^ 2) :=
      one_div_lt_one_div_of_lt (by positivity) hpow_lt
    linarith
  have hrest_pos : 0 < ∏ p ∈ n.primeFactors.erase r, (1 - 1 / ((p : ℚ) ^ 2)) := by
    apply Finset.prod_pos
    intro p hp
    have hp1 : (1 : ℚ) < (p : ℚ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).one_lt
    have hpow : (1 : ℚ) < (p : ℚ) ^ 2 := by nlinarith
    rw [sub_pos, div_lt_one (by positivity)]
    exact hpow
  have hrest_le :
      ∏ p ∈ n.primeFactors.erase r, (1 - 1 / ((p : ℚ) ^ 2)) ≤
        ∏ p ∈ n.primeFactors.erase r, (1 - 1 / ((p : ℚ) ^ (n.factorization p + 1))) := by
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
      have hpe : 1 ≤ n.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp_mem)
      have hpow_le : (p : ℚ) ^ 2 ≤ (p : ℚ) ^ (n.factorization p + 1) :=
        pow_le_pow_right₀ hp1.le (by omega)
      have hdiv_le : 1 / ((p : ℚ) ^ (n.factorization p + 1)) ≤ 1 / ((p : ℚ) ^ 2) :=
        one_div_le_one_div_of_le (by positivity) hpow_le
      linarith
  have hrest_pos' :
      0 < ∏ p ∈ n.primeFactors.erase r, (1 - 1 / ((p : ℚ) ^ (n.factorization p + 1))) :=
    lt_of_lt_of_le hrest_pos hrest_le
  calc (1 - 1 / ((r : ℚ) ^ 2)) * ∏ p ∈ n.primeFactors.erase r, (1 - 1 / ((p : ℚ) ^ 2))
      ≤ (1 - 1 / ((r : ℚ) ^ 2)) *
          ∏ p ∈ n.primeFactors.erase r, (1 - 1 / ((p : ℚ) ^ (n.factorization p + 1))) :=
        mul_le_mul_of_nonneg_left hrest_le hr_lhs_pos.le
    _ < (1 - 1 / ((r : ℚ) ^ (n.factorization r + 1))) *
          ∏ p ∈ n.primeFactors.erase r, (1 - 1 / ((p : ℚ) ^ (n.factorization p + 1))) :=
        mul_lt_mul_of_pos_right hr_lt hrest_pos'

private lemma totient_sq (m : ℕ) : (m ^ 2).totient = m * m.totient := by
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · simp
  · have h := Nat.totient_gcd_mul_totient_mul m m
    rw [Nat.gcd_self, ← sq] at h
    have hphi_pos : 0 < m.totient := Nat.totient_pos.mpr hm_pos
    have h' : m.totient * (m ^ 2).totient = m.totient * (m * m.totient) := by
      rw [h]; ring
    exact Nat.mul_left_cancel hphi_pos h'

/-- **1. Universal Odd `σ(n) · φ(n)` Identities and Two-Sided Envelope**:
For every odd integer `n > 1`, proves the exact radical product identity
`n * ∏ p ∈ n.primeFactors, (p ^ (n.factorization p + 1) - 1) = sigma 1 n * (∏ p ∈ n.primeFactors, p) * n.totient`,
its rational form `((sigma 1 n : ℚ) * (n.totient : ℚ)) / ((n : ℚ) ^ 2) = ∏ p ∈ n.primeFactors, (1 - 1 / p ^ (e_p + 1))`,
and the universal two-sided bounds on `sigma 1 n * n.totient`. -/
theorem odd_sigma_mul_totient_identities_and_bounds {n : ℕ} (ho : Odd n) (hn1 : 1 < n) :
    (n * ∏ p ∈ n.primeFactors, (p ^ (n.factorization p + 1) - 1) =
        sigma 1 n * (∏ p ∈ n.primeFactors, p) * n.totient) ∧
      (((sigma 1 n : ℚ) * (n.totient : ℚ)) / ((n : ℚ) ^ 2) =
        ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℚ) ^ (n.factorization p + 1)))) ∧
      sigma 1 n * n.totient < n ^ 2 ∧
      (3 * n.primeFactors.card + 5) * n ^ 2 ≤
        (4 * n.primeFactors.card + 5) * (sigma 1 n * n.totient) ∧
      3 * n ^ 2 < 4 * (sigma 1 n * n.totient) ∧
      (¬ 3 ∣ n → 27 * n ^ 2 < 32 * (sigma 1 n * n.totient)) := by
  have hn_pos : 0 < n := by omega
  have hn0 : n ≠ 0 := hn_pos.ne'
  have hprod_sig : (∏ p ∈ n.primeFactors, sigma 1 (p ^ n.factorization p)) = sigma 1 n :=
    (isMultiplicative_sigma.multiplicative_factorization _ hn0).symm
  have hloc : ∀ p ∈ n.primeFactors,
      sigma 1 (p ^ n.factorization p) * (p - 1) = p ^ (n.factorization p + 1) - 1 := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    rw [sigma_one_apply_prime_pow hp_prime]
    have hgeom := geom_sum_mul_add (p - 1) (n.factorization p + 1)
    rw [Nat.sub_add_cancel hp_prime.one_lt.le] at hgeom
    omega
  have hid1 : n * ∏ p ∈ n.primeFactors, (p ^ (n.factorization p + 1) - 1) =
      sigma 1 n * (∏ p ∈ n.primeFactors, p) * n.totient := by
    calc n * ∏ p ∈ n.primeFactors, (p ^ (n.factorization p + 1) - 1)
        = n * ∏ p ∈ n.primeFactors, (sigma 1 (p ^ n.factorization p) * (p - 1)) := by
            congr 1
            exact Finset.prod_congr rfl fun p hp => (hloc p hp).symm
      _ = n * ((∏ p ∈ n.primeFactors, sigma 1 (p ^ n.factorization p)) *
            ∏ p ∈ n.primeFactors, (p - 1)) := by rw [Finset.prod_mul_distrib]
      _ = sigma 1 n * (n * ∏ p ∈ n.primeFactors, (p - 1)) := by rw [hprod_sig]; ring
      _ = sigma 1 n * (n.totient * ∏ p ∈ n.primeFactors, p) := by
            rw [Nat.totient_mul_prod_primeFactors]
      _ = sigma 1 n * (∏ p ∈ n.primeFactors, p) * n.totient := by ring
  have hid2 : ((sigma 1 n : ℚ) * (n.totient : ℚ)) / ((n : ℚ) ^ 2) =
      ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℚ) ^ (n.factorization p + 1))) := by
    have hcast1 : (n : ℚ) * (∏ p ∈ n.primeFactors, ((p : ℚ) ^ (n.factorization p + 1) - 1)) =
        (sigma 1 n : ℚ) * (∏ p ∈ n.primeFactors, (p : ℚ)) * (n.totient : ℚ) := by
      have h := congrArg (Nat.cast (R := ℚ)) hid1
      push_cast at h
      refine Eq.trans ?_ h
      congr 1
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp_pos : 1 ≤ p ^ (n.factorization p + 1) :=
        Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors hp).pos
      rw [Nat.cast_sub hp_pos]
      push_cast
      rfl
    have hden : (∏ p ∈ n.primeFactors, (p : ℚ) ^ (n.factorization p + 1)) =
        (∏ p ∈ n.primeFactors, (p : ℚ)) * (n : ℚ) := by
      calc ∏ p ∈ n.primeFactors, (p : ℚ) ^ (n.factorization p + 1)
          = ∏ p ∈ n.primeFactors, ((p : ℚ) * (p : ℚ) ^ n.factorization p) :=
            Finset.prod_congr rfl fun p _ => by rw [pow_succ']
        _ = (∏ p ∈ n.primeFactors, (p : ℚ)) *
              ∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p := Finset.prod_mul_distrib
        _ = (∏ p ∈ n.primeFactors, (p : ℚ)) * (n : ℚ) := by
            congr 1
            have h := congrArg (Nat.cast (R := ℚ)) (Nat.prod_primeFactors_pow_factorization hn0)
            push_cast at h
            exact h.symm
    have hn_ne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
    have hrad_ne : (∏ p ∈ n.primeFactors, (p : ℚ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun p hp =>
        Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
    calc ((sigma 1 n : ℚ) * (n.totient : ℚ)) / ((n : ℚ) ^ 2)
        = ((sigma 1 n : ℚ) * (∏ p ∈ n.primeFactors, (p : ℚ)) * (n.totient : ℚ)) /
            ((n : ℚ) * ((∏ p ∈ n.primeFactors, (p : ℚ)) * (n : ℚ))) := by
          field_simp
      _ = ((n : ℚ) * ∏ p ∈ n.primeFactors, ((p : ℚ) ^ (n.factorization p + 1) - 1)) /
            ((n : ℚ) * ∏ p ∈ n.primeFactors, (p : ℚ) ^ (n.factorization p + 1)) := by
          rw [hcast1, hden]
      _ = (∏ p ∈ n.primeFactors, ((p : ℚ) ^ (n.factorization p + 1) - 1)) /
            (∏ p ∈ n.primeFactors, (p : ℚ) ^ (n.factorization p + 1)) := by
          rw [mul_div_mul_left _ _ hn_ne]
      _ = ∏ p ∈ n.primeFactors,
            (((p : ℚ) ^ (n.factorization p + 1) - 1) / (p : ℚ) ^ (n.factorization p + 1)) := by
          rw [Finset.prod_div_distrib]
      _ = ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℚ) ^ (n.factorization p + 1))) := by
          refine Finset.prod_congr rfl fun p hp => ?_
          have hp_ne : (p : ℚ) ≠ 0 :=
            Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
          field_simp
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn1
  have hn2_pos_q : (0 : ℚ) < (n : ℚ) ^ 2 := by
    have : (0 : ℚ) < n := Nat.cast_pos.mpr hn_pos
    positivity
  have hlt1 : sigma 1 n * n.totient < n ^ 2 := by
    have hprod_lt :
        ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℚ) ^ (n.factorization p + 1))) <
          ∏ _p ∈ n.primeFactors, (1 : ℚ) := by
      apply Finset.prod_lt_prod_of_nonempty₀
      · intro p hp
        have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
        have hpow : (1 : ℚ) < (p : ℚ) ^ (n.factorization p + 1) :=
          one_lt_pow₀ hp1 (Nat.succ_ne_zero _)
        have hdiv : 1 / ((p : ℚ) ^ (n.factorization p + 1)) < 1 := by
          rw [div_lt_one (by positivity)]
          exact hpow
        linarith
      · intro p hp
        have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
        have hpow : (1 : ℚ) < (p : ℚ) ^ (n.factorization p + 1) :=
          one_lt_pow₀ hp1 (Nat.succ_ne_zero _)
        have hinv : 0 < 1 / ((p : ℚ) ^ (n.factorization p + 1)) := by positivity
        linarith
      · exact hne
    simp only [Finset.prod_const_one] at hprod_lt
    rw [← hid2, div_lt_one hn2_pos_q] at hprod_lt
    exact_mod_cast (show ((sigma 1 n * n.totient : ℕ) : ℚ) < ((n ^ 2 : ℕ) : ℚ) by
      push_cast
      exact hprod_lt)
  obtain ⟨hlow3, hnot3_prod⟩ := odd_prod_one_sub_inv_sq_lower_bound ho
  have hle_fac := prod_one_sub_inv_sq_le_factorization n
  let ω := n.primeFactors.card
  have hmain_q :
      (3 * (ω : ℚ) + 5) / (4 * (ω : ℚ) + 5) ≤
        ((sigma 1 n : ℚ) * (n.totient : ℚ)) / ((n : ℚ) ^ 2) := by
    calc (3 * (ω : ℚ) + 5) / (4 * (ω : ℚ) + 5)
        ≤ ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℚ) ^ 2)) := hlow3
      _ ≤ ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℚ) ^ (n.factorization p + 1))) := hle_fac
      _ = ((sigma 1 n : ℚ) * (n.totient : ℚ)) / ((n : ℚ) ^ 2) := hid2.symm
  have hmain : (3 * ω + 5) * n ^ 2 ≤ (4 * ω + 5) * (sigma 1 n * n.totient) := by
    have hden : (0 : ℚ) < 4 * (ω : ℚ) + 5 := by positivity
    rw [div_le_div_iff₀ hden hn2_pos_q] at hmain_q
    exact_mod_cast (show ((3 * ω + 5 : ℕ) : ℚ) * ((n ^ 2 : ℕ) : ℚ) ≤
        ((4 * ω + 5 : ℕ) : ℚ) * ((sigma 1 n * n.totient : ℕ) : ℚ) by
      push_cast
      linarith)
  have h3_4 : 3 * n ^ 2 < 4 * (sigma 1 n * n.totient) := by
    have hn2_pos : 0 < n ^ 2 := pow_pos hn_pos 2
    have hstep1 : 3 * (4 * ω + 5) * n ^ 2 < 4 * ((3 * ω + 5) * n ^ 2) := by
      have hmul : 3 * (4 * ω + 5) < 4 * (3 * ω + 5) := by omega
      calc 3 * (4 * ω + 5) * n ^ 2 < 4 * (3 * ω + 5) * n ^ 2 :=
            Nat.mul_lt_mul_of_pos_right hmul hn2_pos
        _ = 4 * ((3 * ω + 5) * n ^ 2) := by ring
    have hstep2 : 4 * ((3 * ω + 5) * n ^ 2) ≤ 4 * ((4 * ω + 5) * (sigma 1 n * n.totient)) :=
      Nat.mul_le_mul_left 4 hmain
    have hcomb : (4 * ω + 5) * (3 * n ^ 2) < (4 * ω + 5) * (4 * (sigma 1 n * n.totient)) := by
      have hlt := lt_of_lt_of_le hstep1 hstep2
      linarith
    exact Nat.lt_of_mul_lt_mul_left hcomb
  have hnot3 : ¬ 3 ∣ n → 27 * n ^ 2 < 32 * (sigma 1 n * n.totient) := by
    intro hn3
    have hq27 : (27 / 32 : ℚ) < ((sigma 1 n : ℚ) * (n.totient : ℚ)) / ((n : ℚ) ^ 2) := by
      calc (27 / 32 : ℚ)
          < ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℚ) ^ 2)) := hnot3_prod hn3
        _ ≤ ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℚ) ^ (n.factorization p + 1))) := hle_fac
        _ = ((sigma 1 n : ℚ) * (n.totient : ℚ)) / ((n : ℚ) ^ 2) := hid2.symm
    rw [div_lt_div_iff₀ (by norm_num) hn2_pos_q] at hq27
    exact_mod_cast (show ((27 * n ^ 2 : ℕ) : ℚ) < ((32 * (sigma 1 n * n.totient) : ℕ) : ℚ) by
      push_cast
      linarith)
  exact ⟨hid1, hid2, hlt1, hmain, h3_4, hnot3⟩

/-- **1b. Strict Non-Squarefree Strengthening**:
Whenever an odd integer `n > 1` has at least one prime factor of multiplicity `≥ 2`,
the lower envelope `(3 * ω(n) + 5) * n ^ 2 < (4 * ω(n) + 5) * (sigma 1 n * n.totient)` is strict. -/
theorem odd_sigma_mul_totient_strict_of_not_squarefree {n : ℕ} (ho : Odd n) (hn1 : 1 < n)
    (hnsq : ∃ p ∈ n.primeFactors, 2 ≤ n.factorization p) :
    (3 * n.primeFactors.card + 5) * n ^ 2 <
        (4 * n.primeFactors.card + 5) * (sigma 1 n * n.totient) ∧
      (¬ 3 ∣ n → 27 * n ^ 2 < 32 * (sigma 1 n * n.totient)) := by
  have hid := odd_sigma_mul_totient_identities_and_bounds ho hn1
  have hid2 := hid.2.1
  have hnot3 := hid.2.2.2.2.2
  have hlow3 := (odd_prod_one_sub_inv_sq_lower_bound ho).1
  have hlt_fac := prod_one_sub_inv_sq_lt_factorization_of_non_squarefree hnsq
  let ω := n.primeFactors.card
  have hn2_pos_q : (0 : ℚ) < (n : ℚ) ^ 2 := by
    have : (0 : ℚ) < n := Nat.cast_pos.mpr (by omega)
    positivity
  have hmain_q :
      (3 * (ω : ℚ) + 5) / (4 * (ω : ℚ) + 5) <
        ((sigma 1 n : ℚ) * (n.totient : ℚ)) / ((n : ℚ) ^ 2) := by
    calc (3 * (ω : ℚ) + 5) / (4 * (ω : ℚ) + 5)
        ≤ ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℚ) ^ 2)) := hlow3
      _ < ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℚ) ^ (n.factorization p + 1))) := hlt_fac
      _ = ((sigma 1 n : ℚ) * (n.totient : ℚ)) / ((n : ℚ) ^ 2) := hid2.symm
  have hmain : (3 * ω + 5) * n ^ 2 < (4 * ω + 5) * (sigma 1 n * n.totient) := by
    have hden : (0 : ℚ) < 4 * (ω : ℚ) + 5 := by positivity
    rw [div_lt_div_iff₀ hden hn2_pos_q] at hmain_q
    exact_mod_cast (show ((3 * ω + 5 : ℕ) : ℚ) * ((n ^ 2 : ℕ) : ℚ) <
        ((4 * ω + 5 : ℕ) : ℚ) * ((sigma 1 n * n.totient : ℕ) : ℚ) by
      push_cast
      linarith)
  exact ⟨hmain, hnot3⟩

/-- Specialization of `odd_sigma_mul_totient_strict_of_not_squarefree` to odd squares `n > 1`. -/
theorem odd_sigma_mul_totient_strict_of_isSquare {n : ℕ} (ho : Odd n) (hn1 : 1 < n)
    (hsq : IsSquare n) :
    (3 * n.primeFactors.card + 5) * n ^ 2 <
        (4 * n.primeFactors.card + 5) * (sigma 1 n * n.totient) ∧
      (¬ 3 ∣ n → 27 * n ^ 2 < 32 * (sigma 1 n * n.totient)) := by
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hn1
  have hev : Even (n.factorization p) :=
    (Nat.isSquare_iff_even_factorization.mp hsq) p (Nat.prime_of_mem_primeFactors hp)
  have hpos : 0 < n.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  obtain ⟨k, hk⟩ := hev
  have hge2 : 2 ≤ n.factorization p := by omega
  exact odd_sigma_mul_totient_strict_of_not_squarefree ho hn1 ⟨p, hp, hge2⟩

/-- **2. Ore-Harmonic Totient-Divisor Envelope**:
For every odd Ore-harmonic integer `N` with integral harmonic divisor mean
`H := N * N.divisors.card / sigma 1 N`, bounds `N.divisors.card * N.totient` against `H * N`. -/
theorem odd_oreHarmonic_totient_divisor_envelope {N : ℕ} (ho : Odd N) (hore : OreHarmonic N) :
    let H := N * N.divisors.card / sigma 1 N
    sigma 1 N * H = N * N.divisors.card ∧
      0 < H ∧
      N.divisors.card * N.totient < H * N ∧
      (3 * N.primeFactors.card + 5) * H * N ≤
        (4 * N.primeFactors.card + 5) * N.divisors.card * N.totient ∧
      3 * H * N < 4 * N.divisors.card * N.totient ∧
      (¬ 3 ∣ N → 27 * H * N < 32 * N.divisors.card * N.totient) := by
  let H := N * N.divisors.card / sigma 1 N
  have hN1 : 1 < N := hore.1
  have hN_pos : 0 < N := by omega
  have hsig_H : sigma 1 N * H = N * N.divisors.card := Nat.mul_div_cancel' hore.2
  have hdiv_pos : 0 < N.divisors.card :=
    Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hN_pos.ne'⟩
  have hH_pos : 0 < H := by
    have hprod_pos : 0 < sigma 1 N * H := by
      rw [hsig_H]
      exact Nat.mul_pos hN_pos hdiv_pos
    exact Nat.pos_of_mul_pos_left hprod_pos
  obtain ⟨_, _, hlt1, hmain, h3_4, hnot3⟩ := odd_sigma_mul_totient_identities_and_bounds ho hN1
  have hb1 : N.divisors.card * N.totient < H * N := by
    have hmul : H * (sigma 1 N * N.totient) < H * N ^ 2 := Nat.mul_lt_mul_of_pos_left hlt1 hH_pos
    have hmul' : N * (N.divisors.card * N.totient) < N * (H * N) := by
      calc N * (N.divisors.card * N.totient)
          = (N * N.divisors.card) * N.totient := by ring
        _ = (sigma 1 N * H) * N.totient := by rw [hsig_H]
        _ = H * (sigma 1 N * N.totient) := by ring
        _ < H * N ^ 2 := hmul
        _ = N * (H * N) := by ring
    exact Nat.lt_of_mul_lt_mul_left hmul'
  have hb2 : (3 * N.primeFactors.card + 5) * H * N ≤
      (4 * N.primeFactors.card + 5) * N.divisors.card * N.totient := by
    have hmul : H * ((3 * N.primeFactors.card + 5) * N ^ 2) ≤
        H * ((4 * N.primeFactors.card + 5) * (sigma 1 N * N.totient)) :=
      Nat.mul_le_mul_left H hmain
    have hmul' : N * ((3 * N.primeFactors.card + 5) * H * N) ≤
        N * ((4 * N.primeFactors.card + 5) * N.divisors.card * N.totient) := by
      calc N * ((3 * N.primeFactors.card + 5) * H * N)
          = H * ((3 * N.primeFactors.card + 5) * N ^ 2) := by ring
        _ ≤ H * ((4 * N.primeFactors.card + 5) * (sigma 1 N * N.totient)) := hmul
        _ = (4 * N.primeFactors.card + 5) * (sigma 1 N * H) * N.totient := by ring
        _ = (4 * N.primeFactors.card + 5) * (N * N.divisors.card) * N.totient := by rw [hsig_H]
        _ = N * ((4 * N.primeFactors.card + 5) * N.divisors.card * N.totient) := by ring
    exact Nat.le_of_mul_le_mul_left hmul' hN_pos
  have hb3 : 3 * H * N < 4 * N.divisors.card * N.totient := by
    have hmul : H * (3 * N ^ 2) < H * (4 * (sigma 1 N * N.totient)) :=
      Nat.mul_lt_mul_of_pos_left h3_4 hH_pos
    have hmul' : N * (3 * H * N) < N * (4 * N.divisors.card * N.totient) := by
      calc N * (3 * H * N)
          = H * (3 * N ^ 2) := by ring
        _ < H * (4 * (sigma 1 N * N.totient)) := hmul
        _ = 4 * (sigma 1 N * H) * N.totient := by ring
        _ = 4 * (N * N.divisors.card) * N.totient := by rw [hsig_H]
        _ = N * (4 * N.divisors.card * N.totient) := by ring
    exact Nat.lt_of_mul_lt_mul_left hmul'
  have hb4 : ¬ 3 ∣ N → 27 * H * N < 32 * N.divisors.card * N.totient := by
    intro hn3
    have hmul : H * (27 * N ^ 2) < H * (32 * (sigma 1 N * N.totient)) :=
      Nat.mul_lt_mul_of_pos_left (hnot3 hn3) hH_pos
    have hmul' : N * (27 * H * N) < N * (32 * N.divisors.card * N.totient) := by
      calc N * (27 * H * N)
          = H * (27 * N ^ 2) := by ring
        _ < H * (32 * (sigma 1 N * N.totient)) := hmul
        _ = 32 * (sigma 1 N * H) * N.totient := by ring
        _ = 32 * (N * N.divisors.card) * N.totient := by rw [hsig_H]
        _ = N * (32 * N.divisors.card * N.totient) := by ring
    exact Nat.lt_of_mul_lt_mul_left hmul'
  exact ⟨hsig_H, hH_pos, hb1, hb2, hb3, hb4⟩

/-- **3. Odd Near-Perfect Totient Obstruction**:
Every odd near-perfect pair `NearPerfectWith n d` has `1 < n` and `IsSquare n`, hence obeys
strict universal totient bounds `(2 * n + d) * n.totient < n ^ 2`, `2 * n.totient < n`, and
strict lower bounds with `3 * n ^ 2 < 4 * (2 * n + d) * n.totient`. -/
theorem odd_nearPerfect_totient_obstruction {n d : ℕ} (ho : Odd n)
    (hnp : NearPerfectWith n d) :
    1 < n ∧
      IsSquare n ∧
      (2 * n + d) * n.totient < n ^ 2 ∧
      2 * n.totient < n ∧
      (3 * n.primeFactors.card + 5) * n ^ 2 <
        (4 * n.primeFactors.card + 5) * (2 * n + d) * n.totient ∧
      3 * n ^ 2 < 4 * (2 * n + d) * n.totient := by
  obtain ⟨hnp_mem, hnp_erase⟩ := nearPerfectWith_iff_erase.mp hnp
  have hd_pos : 0 < d := Nat.pos_of_mem_properDivisors hnp_mem
  have hd_lt : d < n := (Nat.mem_properDivisors.mp hnp_mem).2
  have hn1 : 1 < n := by omega
  have hsq : IsSquare n := hnp.isSquare_of_odd ho
  have hsig : sigma 1 n = 2 * n + d := by
    have hsum := Finset.add_sum_erase n.properDivisors (fun i => i) hnp_mem
    rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, ← hsum, hnp_erase]
    omega
  have hb := odd_sigma_mul_totient_identities_and_bounds ho hn1
  have hstrict := odd_sigma_mul_totient_strict_of_isSquare ho hn1 hsq
  have h1 : (2 * n + d) * n.totient < n ^ 2 := by
    rw [← hsig]
    exact hb.2.2.1
  have h2 : 2 * n.totient < n := by
    have hphi_pos : 0 < n.totient := Nat.totient_pos.mpr ho.pos
    have hlt : n * (2 * n.totient) < n * n := by
      calc n * (2 * n.totient)
          = (2 * n) * n.totient := by ring
        _ < (2 * n + d) * n.totient := Nat.mul_lt_mul_of_pos_right (by omega) hphi_pos
        _ < n ^ 2 := h1
        _ = n * n := sq n
    exact Nat.lt_of_mul_lt_mul_left hlt
  have h3 : (3 * n.primeFactors.card + 5) * n ^ 2 <
      (4 * n.primeFactors.card + 5) * (2 * n + d) * n.totient := by
    have h := hstrict.1
    rw [hsig] at h
    linarith
  have h4 : 3 * n ^ 2 < 4 * (2 * n + d) * n.totient := by
    have h := hb.2.2.2.2.1
    rw [hsig] at h
    linarith
  exact ⟨hn1, hsq, h1, h2, h3, h4⟩

/-- **4a. Odd Deficient-Perfect Totient Bounds**:
For every odd `DeficientPerfectWith n d`, proves `1 < n` and the universal bounds on
`(2 * n - d) * n.totient`. -/
theorem odd_deficientPerfect_totient_bounds {n d : ℕ} (ho : Odd n)
    (hdp : DeficientPerfectWith n d) :
    1 < n ∧
      (2 * n - d) * n.totient < n ^ 2 ∧
      3 * n ^ 2 < 4 * (2 * n - d) * n.totient ∧
      (3 * n.primeFactors.card + 5) * n ^ 2 ≤
        (4 * n.primeFactors.card + 5) * (2 * n - d) * n.totient := by
  have hd_pos : 0 < d := Nat.pos_of_mem_properDivisors hdp.1
  have hd_lt : d < n := (Nat.mem_properDivisors.mp hdp.1).2
  have hn1 : 1 < n := by omega
  have hsig : sigma 1 n = 2 * n - d := by
    have := hdp.2
    omega
  have hb := odd_sigma_mul_totient_identities_and_bounds ho hn1
  have h1 : (2 * n - d) * n.totient < n ^ 2 := by
    rw [← hsig]
    exact hb.2.2.1
  have h2 : 3 * n ^ 2 < 4 * (2 * n - d) * n.totient := by
    have h := hb.2.2.2.2.1
    rw [hsig] at h
    linarith
  have h3 : (3 * n.primeFactors.card + 5) * n ^ 2 ≤
      (4 * n.primeFactors.card + 5) * (2 * n - d) * n.totient := by
    have h := hb.2.2.2.1
    rw [hsig] at h
    linarith
  exact ⟨hn1, h1, h2, h3⟩

/-- **4b. Linear Euler Square Totient Bounds**:
Specializes to any linear Euler odd perfect number `N = q * m ^ 2`, identifying
`componentIndex N q = sigma 1 (m ^ 2) / q` as a deficient divisor of the odd square `m ^ 2`
and proving the strict `m ^ 3` totient envelope. -/
theorem odd_deficientPerfect_and_linear_euler_square_totient_bounds {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    DeficientPerfectWith (m ^ 2) (componentIndex N q) ∧
      (m ^ 2).totient = m * m.totient ∧
      (2 * m ^ 2 - componentIndex N q) * m.totient < m ^ 3 ∧
      (3 * m.primeFactors.card + 5) * m ^ 3 <
        (4 * m.primeFactors.card + 5) * (2 * m ^ 2 - componentIndex N q) * m.totient ∧
      3 * m ^ 3 < 4 * (2 * m ^ 2 - componentIndex N q) * m.totient ∧
      (¬ 3 ∣ N → 27 * m ^ 3 < 32 * (2 * m ^ 2 - componentIndex N q) * m.totient) := by
  have hmodd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hm_pos : 0 < m := hmodd.pos
  have hm2_odd : Odd (m ^ 2) := hmodd.pow
  have hq_ndvd_m2 : ¬ q ∣ m ^ 2 := fun h => hqm (hq.dvd_of_dvd_pow h)
  have hm2_fac_q : (m ^ 2).factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hq_ndvd_m2
  have hN_fac_q : N.factorization q = 1 := by
    rw [hform, Nat.factorization_mul hq.ne_zero (pow_ne_zero 2 hm_pos.ne'), Finsupp.add_apply,
      hq.factorization_self, hm2_fac_q, add_zero]
  have hordProj : ordProj[q] N = q := by
    rw [hN_fac_q, pow_one]
  have hordCompl : ordCompl[q] N = m ^ 2 := by
    have hmul : q * ordCompl[q] N = q * m ^ 2 := by
      calc q * ordCompl[q] N
          = ordProj[q] N * ordCompl[q] N := by rw [hordProj]
        _ = N := Nat.ordProj_mul_ordCompl_eq_self N q
        _ = q * m ^ 2 := hform
    exact Nat.mul_left_cancel hq.pos hmul
  have hci : componentIndex N q = sigma 1 (m ^ 2) / q := by
    rw [componentIndex, hordCompl, hordProj]
  have hdef_raw := (linear_euler_half_succ_mul_index_and_deficient_square ho hN hq hqm hform).2.2
  have hdef : DeficientPerfectWith (m ^ 2) (componentIndex N q) := by
    simpa only [← hci] using hdef_raw
  have htot_sq : (m ^ 2).totient = m * m.totient := totient_sq m
  have hm2_gt1 : 1 < m ^ 2 := by
    have hd_pos : 0 < componentIndex N q := Nat.pos_of_mem_properDivisors hdef.1
    have hd_lt : componentIndex N q < m ^ 2 := (Nat.mem_properDivisors.mp hdef.1).2
    omega
  have hsig_m2 : sigma 1 (m ^ 2) = 2 * m ^ 2 - componentIndex N q := by
    have := hdef.2
    omega
  have hpf_m2 : (m ^ 2).primeFactors = m.primeFactors := Nat.primeFactors_pow m (by decide : 2 ≠ 0)
  have hb := odd_sigma_mul_totient_identities_and_bounds hm2_odd hm2_gt1
  have hstrict := odd_sigma_mul_totient_strict_of_isSquare hm2_odd hm2_gt1 ⟨m, by ring⟩
  have h1 : (2 * m ^ 2 - componentIndex N q) * m.totient < m ^ 3 := by
    have h := hb.2.2.1
    rw [hsig_m2, htot_sq] at h
    have hmul : m * ((2 * m ^ 2 - componentIndex N q) * m.totient) < m * m ^ 3 := by
      calc m * ((2 * m ^ 2 - componentIndex N q) * m.totient)
          = (2 * m ^ 2 - componentIndex N q) * (m * m.totient) := by ring
        _ < (m ^ 2) ^ 2 := h
        _ = m * m ^ 3 := by ring
    exact Nat.lt_of_mul_lt_mul_left hmul
  have h2 : (3 * m.primeFactors.card + 5) * m ^ 3 <
      (4 * m.primeFactors.card + 5) * (2 * m ^ 2 - componentIndex N q) * m.totient := by
    have h := hstrict.1
    rw [hpf_m2, hsig_m2, htot_sq] at h
    have hmul : m * ((3 * m.primeFactors.card + 5) * m ^ 3) <
        m * ((4 * m.primeFactors.card + 5) * (2 * m ^ 2 - componentIndex N q) * m.totient) := by
      calc m * ((3 * m.primeFactors.card + 5) * m ^ 3)
          = (3 * m.primeFactors.card + 5) * (m ^ 2) ^ 2 := by ring
        _ < (4 * m.primeFactors.card + 5) *
              ((2 * m ^ 2 - componentIndex N q) * (m * m.totient)) := h
        _ = m * ((4 * m.primeFactors.card + 5) * (2 * m ^ 2 - componentIndex N q) * m.totient) := by
            ring
    exact Nat.lt_of_mul_lt_mul_left hmul
  have h3 : 3 * m ^ 3 < 4 * (2 * m ^ 2 - componentIndex N q) * m.totient := by
    have h := hb.2.2.2.2.1
    rw [hsig_m2, htot_sq] at h
    have hmul : m * (3 * m ^ 3) < m * (4 * (2 * m ^ 2 - componentIndex N q) * m.totient) := by
      calc m * (3 * m ^ 3)
          = 3 * (m ^ 2) ^ 2 := by ring
        _ < 4 * ((2 * m ^ 2 - componentIndex N q) * (m * m.totient)) := h
        _ = m * (4 * (2 * m ^ 2 - componentIndex N q) * m.totient) := by ring
    exact Nat.lt_of_mul_lt_mul_left hmul
  have h4 : ¬ 3 ∣ N → 27 * m ^ 3 < 32 * (2 * m ^ 2 - componentIndex N q) * m.totient := by
    intro hn3
    have hn3_m2 : ¬ 3 ∣ m ^ 2 := fun h => hn3 (h.trans ⟨q, by rw [hform]; ring⟩)
    have h := hb.2.2.2.2.2 hn3_m2
    rw [hsig_m2, htot_sq] at h
    have hmul : m * (27 * m ^ 3) < m * (32 * (2 * m ^ 2 - componentIndex N q) * m.totient) := by
      calc m * (27 * m ^ 3)
          = 27 * (m ^ 2) ^ 2 := by ring
        _ < 32 * ((2 * m ^ 2 - componentIndex N q) * (m * m.totient)) := h
        _ = m * (32 * (2 * m ^ 2 - componentIndex N q) * m.totient) := by ring
    exact Nat.lt_of_mul_lt_mul_left hmul
  exact ⟨hdef, htot_sq, h1, h2, h3, h4⟩

end OddPerfect
