module

public import OddPerfect.Question
import all OddPerfect.Question
public import OddPerfect.CandidateSets
public import OddPerfect.Dickson
public import OddPerfect.BoundedIndex
public import OddPerfect.BoundedIndexWeight
public import OddPerfect.EulerIndexMultiplicity
public import OddPerfect.CountExcessSeven
public import OddPerfect.OddGraphWeight
public import OddPerfect.FourthPowerSpoof
public import OddPerfect.CubeFreeSpoof
public import OddPerfect.TothTrillion
public import OddPerfect.NearPerfect
public import OddPerfect.PrimePowerObstruction
public import OddPerfect.DrisRegimes
public import OddPerfect.ZelinskySlope
public import OddPerfect.SixthPowerBounds
public import OddPerfect.Harmonic
public import OddPerfect.Reciprocity
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Global Obstruction Synthesis (`OddPerfect.GlobalObstruction`)

Tier 2 global synthesis of:
1. Global component-index conservation laws (Bridges `B2` & `B3`).
2. Global closed-graph Jacobi reciprocity conservation laws (`I1` + `I2`).
3. Counterexample filter bank separation theorem.
4. Four-bridge master reductions (`B1`–`B3` → `¬ existsOddPerfect`) and
   unified global obstruction profile.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction
open scoped NumberTheorySymbols

/-! ## 1. Global Component-Index Conservation Laws (Bridges `B2` & `B3`) -/

/-- The component index `σ(N / p^v_p(N)) / p^v_p(N)` associated to an exact
prime-power component of `N`. -/
@[expose] def componentIndex (N p : ℕ) : ℕ :=
  sigma 1 (ordCompl[p] N) / ordProj[p] N

theorem componentIndex_mul_eq_two_mul {N p : ℕ} (hN : N.Perfect) (hp : p ∈ N.primeFactors) :
    componentIndex N p * ordProj[p] N * sigma 1 (ordProj[p] N) = 2 * N ∧ 0 < componentIndex N p := by
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hNb : N = p ^ N.factorization p * ordCompl[p] N := (Nat.ordProj_mul_ordCompl_eq_self N p).symm
  have hpb : ¬ p ∣ ordCompl[p] N := Nat.not_dvd_ordCompl hp_prime hN.2.ne'
  obtain ⟨i, hi_pos, hleft, hright, _⟩ := exists_component_index hN hp_prime hNb hpb
  have hci : componentIndex N p = i := by
    rw [componentIndex, hleft]
    exact Nat.mul_div_cancel_left i (pow_pos hp_prime.pos _)
  refine ⟨?_, hci ▸ hi_pos⟩
  rw [hci]
  calc
    i * ordProj[p] N * sigma 1 (ordProj[p] N)
        = p ^ N.factorization p * (sigma 1 (p ^ N.factorization p) * i) := by ring
    _ = p ^ N.factorization p * (2 * ordCompl[p] N) := by rw [hright]
    _ = 2 * (p ^ N.factorization p * ordCompl[p] N) := by ring
    _ = 2 * N := by rw [← hNb]

theorem prod_componentIndex_eq {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    (∏ p ∈ N.primeFactors, componentIndex N p) =
      2 ^ (N.primeFactors.card - 1) * N ^ (N.primeFactors.card - 2) := by
  have hω : 5 ≤ N.primeFactors.card := five_le_distinct_prime_factor_count ho hN
  have hprod_eq :
      (∏ p ∈ N.primeFactors, (componentIndex N p * ordProj[p] N * sigma 1 (ordProj[p] N))) =
        ∏ _p ∈ N.primeFactors, (2 * N) :=
    Finset.prod_congr rfl fun p hp => (componentIndex_mul_eq_two_mul hN hp).1
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const] at hprod_eq
  have hord : (∏ p ∈ N.primeFactors, ordProj[p] N) = N :=
    (Nat.prod_primeFactors_pow_factorization hN.2.ne').symm
  have hsig_prod : (∏ p ∈ N.primeFactors, sigma 1 (ordProj[p] N)) = sigma 1 N :=
    (isMultiplicative_sigma.multiplicative_factorization (sigma 1) hN.2.ne').symm
  have hsig : sigma 1 N = 2 * N :=
    (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN)
  rw [hord, hsig_prod, hsig] at hprod_eq
  let ω := N.primeFactors.card
  have h2pow : 2 ^ ω = 2 ^ (ω - 1) * 2 := by
    have hω1 : ω = (ω - 1) + 1 := by omega
    conv_lhs => rw [hω1, pow_add, pow_one]
  have hNpow : N ^ ω = N ^ (ω - 2) * N * N := by
    have hω2 : ω = (ω - 2) + 2 := by omega
    conv_lhs => rw [hω2, pow_add, pow_two]
    ring
  have hrhs : (2 * N) ^ ω = 2 ^ (ω - 1) * N ^ (ω - 2) * (N * (2 * N)) := by
    rw [mul_pow, h2pow, hNpow]
    ring
  change (∏ p ∈ N.primeFactors, componentIndex N p) * N * (2 * N) = (2 * N) ^ ω at hprod_eq
  rw [mul_assoc, hrhs] at hprod_eq
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hN.2 (Nat.mul_pos (by decide) hN.2)) hprod_eq

theorem cardFactors_componentIndex_add_eq {N p : ℕ} (hN : N.Perfect) (hp : p ∈ N.primeFactors) :
    cardFactors (componentIndex N p) + N.factorization p + cardFactors (sigma 1 (ordProj[p] N)) =
      1 + cardFactors N := by
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  obtain ⟨hmul, hpos⟩ := componentIndex_mul_eq_two_mul hN hp
  have hord_ne : ordProj[p] N ≠ 0 := pow_ne_zero _ hp_prime.ne_zero
  have hsig_ne : sigma 1 (ordProj[p] N) ≠ 0 := (sigma_pos 1 _ hord_ne).ne'
  have hcard := congrArg cardFactors hmul
  rw [cardFactors_mul (mul_ne_zero hpos.ne' hord_ne) hsig_ne,
    cardFactors_mul hpos.ne' hord_ne,
    cardFactors_apply_prime_pow hp_prime,
    cardFactors_mul (by decide : (2 : ℕ) ≠ 0) hN.2.ne',
    cardFactors_apply_prime Nat.prime_two] at hcard
  exact hcard

private theorem cardFactors_finset_prod {s : Finset ℕ} (f : ℕ → ℕ) (h : ∀ p ∈ s, 0 < f p) :
    cardFactors (∏ p ∈ s, f p) = ∑ p ∈ s, cardFactors (f p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    have hpos : ∀ p ∈ s, 0 < f p := fun p hp => h p (Finset.mem_insert_of_mem hp)
    rw [Finset.prod_insert hx, Finset.sum_insert hx,
      cardFactors_mul (h x (Finset.mem_insert_self ..)).ne' (Finset.prod_pos hpos).ne', ih hpos]

theorem sum_cardFactors_componentIndex {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    (∑ p ∈ N.primeFactors, cardFactors (componentIndex N p)) =
      (N.primeFactors.card - 1) + (N.primeFactors.card - 2) * cardFactors N := by
  have hpos : ∀ p ∈ N.primeFactors, 0 < componentIndex N p :=
    fun p hp => (componentIndex_mul_eq_two_mul hN hp).2
  have hcard := congrArg cardFactors (prod_componentIndex_eq ho hN)
  rw [cardFactors_finset_prod (componentIndex N) hpos,
    cardFactors_mul (pow_ne_zero _ (by decide)) (pow_ne_zero _ hN.2.ne'),
    cardFactors_apply_prime_pow Nat.prime_two,
    cardFactors_pow] at hcard
  exact hcard

theorem exists_componentIndex_cardFactors_add_four_le {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 4 ≤ cardFactors N := by
  by_contra! h
  have hω : 5 ≤ N.primeFactors.card := five_le_distinct_prime_factor_count ho hN
  have hΩ : 2 * N.primeFactors.card + 7 ≤ cardFactors N := by
    simpa [cardFactors_apply] using seven_le_prime_factor_count_excess ho hN
  have hle : ∀ p ∈ N.primeFactors, cardFactors N - 3 ≤ cardFactors (componentIndex N p) := by
    intro p hp
    have := h p hp
    omega
  have hsum_ge :
      N.primeFactors.card * (cardFactors N - 3) ≤
        ∑ p ∈ N.primeFactors, cardFactors (componentIndex N p) := by
    calc
      N.primeFactors.card * (cardFactors N - 3)
          = ∑ _p ∈ N.primeFactors, (cardFactors N - 3) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ p ∈ N.primeFactors, cardFactors (componentIndex N p) := Finset.sum_le_sum hle
  rw [sum_cardFactors_componentIndex ho hN] at hsum_ge
  zify [show 1 ≤ N.primeFactors.card by omega, show 2 ≤ N.primeFactors.card by omega,
    show 3 ≤ cardFactors N by omega] at hsum_ge hω hΩ
  nlinarith

private theorem sigma_div_pow_factorization_eq_componentIndex {N p : ℕ} (hp : p.Prime) :
    sigma 1 (N / p ^ N.factorization p) / p ^ N.factorization p = componentIndex N p := by
  have hquot : N / p ^ N.factorization p = ordCompl[p] N :=
    Nat.div_eq_of_eq_mul_right (pow_pos hp.pos _) (Nat.ordProj_mul_ordCompl_eq_self N p).symm
  rw [hquot]
  rfl

theorem finite_of_component_capturing_factors (K : ℕ) :
    Set.Finite {N : ℕ | Odd N ∧ N.Perfect ∧ ∃ p ∈ N.primeFactors,
      1 + cardFactors N ≤ N.factorization p + cardFactors (sigma 1 (ordProj[p] N)) + K} := by
  apply (finite_of_bounded_component_index_factors K).subset
  rintro N ⟨ho, hN, p, hp, hcap⟩
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have ha_pos : 0 < N.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  have hd : p ^ N.factorization p ∣ N := Nat.ordProj_dvd N p
  have hex : ¬ p ^ (N.factorization p + 1) ∣ N :=
    (hp_prime.pow_dvd_iff_le_factorization hN.2.ne').not.mpr (by omega)
  have hdiv := sigma_div_pow_factorization_eq_componentIndex (N := N) hp_prime
  have hcons := cardFactors_componentIndex_add_eq hN hp
  refine ⟨ho, hN, p, N.factorization p, hp_prime, ha_pos, hd, hex, ?_⟩
  rw [hdiv]
  omega

/-! ## 2. Global Closed-Graph Jacobi Reciprocity Conservation Laws (`I1` + `I2`) -/

private theorem jacobiSym_finset_prod_left (T : Finset ℕ) (f : ℕ → ℕ) (p : ℕ) :
    J(((∏ r ∈ T, f r : ℕ) : ℤ) | p) = ∏ r ∈ T, J((f r : ℤ) | p) := by
  induction T using Finset.induction_on with
  | empty => simp [jacobiSym.one_left]
  | insert r T hr ih =>
    rw [Finset.prod_insert hr, Finset.prod_insert hr, Nat.cast_mul, jacobiSym.mul_left, ih]

private theorem jacobiSym_sq_one_of_prime_ne {r p : ℕ} (hr : r.Prime) (hp : p.Prime)
    (hne : r ≠ p) : J((r : ℤ) | p) ^ 2 = 1 := by
  apply jacobiSym.sq_one
  rw [Int.gcd_natCast_natCast]
  exact (Nat.coprime_primes hr hp).mpr hne

private theorem jacobiSym_pow_factorization_of_prime_ne {r p : ℕ} (hr : r.Prime) (hp : p.Prime)
    (hne : r ≠ p) (k : ℕ) :
    J((r : ℤ) | p) ^ k = if Odd k then J((r : ℤ) | p) else 1 := by
  have hsq : J((r : ℤ) | p) ^ 2 = 1 := jacobiSym_sq_one_of_prime_ne hr hp hne
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have hev : Even (m + m) := ⟨m, rfl⟩
    rw [ite_eq_right (Nat.not_odd_iff_even.mpr hev), ← two_mul, pow_mul, hsq, one_pow]
  · have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
    rw [ite_eq_left hodd, pow_add, pow_mul, hsq, one_pow, one_mul, pow_one]

private theorem jacobiSym_oddValuationPrimes_eq {H p : ℕ} (hH0 : H ≠ 0) (hp : p.Prime)
    (hp_ndvd : ¬ p ∣ H) :
    J((H : ℤ) | p) = ∏ r ∈ oddValuationPrimes H, J((r : ℤ) | p) := by
  have hprod : (∏ r ∈ H.primeFactors, r ^ H.factorization r) = H :=
    (Nat.prod_primeFactors_pow_factorization hH0).symm
  calc
    J((H : ℤ) | p)
        = J(((∏ r ∈ H.primeFactors, r ^ H.factorization r : ℕ) : ℤ) | p) := by rw [hprod]
    _ = ∏ r ∈ H.primeFactors, J(((r ^ H.factorization r : ℕ) : ℤ) | p) :=
      jacobiSym_finset_prod_left H.primeFactors (fun r => r ^ H.factorization r) p
    _ = ∏ r ∈ H.primeFactors, J((r : ℤ) | p) ^ H.factorization r := by
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [Nat.cast_pow, jacobiSym.pow_left]
    _ = ∏ r ∈ H.primeFactors, (if Odd (H.factorization r) then J((r : ℤ) | p) else 1) := by
      refine Finset.prod_congr rfl fun r hr => ?_
      have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr
      have hne : r ≠ p := by
        rintro rfl
        exact hp_ndvd (Nat.dvd_of_mem_primeFactors hr)
      exact jacobiSym_pow_factorization_of_prime_ne hr_prime hp hne (H.factorization r)
    _ = (∏ r ∈ H.primeFactors.filter (fun r => Odd (H.factorization r)), J((r : ℤ) | p)) *
          (∏ _r ∈ H.primeFactors.filter (fun r => ¬ Odd (H.factorization r)), (1 : ℤ)) := by
      rw [← Finset.prod_filter_mul_prod_filter_not H.primeFactors (fun r => Odd (H.factorization r))]
      congr 1
      · refine Finset.prod_congr rfl fun r hr => ite_eq_left (Finset.mem_filter.mp hr).2
      · refine Finset.prod_congr rfl fun r hr => ite_eq_right (Finset.mem_filter.mp hr).2
    _ = ∏ r ∈ oddValuationPrimes H, J((r : ℤ) | p) := by
      simp [oddValuationPrimes]

theorem jacobi_prod_oddSigmaTargets_of_even {N p : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hp : p ∈ N.primeFactors) (he : Even (N.factorization p)) :
    (∏ r ∈ oddSigmaTargets N p, J((r : ℤ) | p)) = 1 := by
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  let S := sigma 1 (p ^ N.factorization p)
  have hS0 : S ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hp_prime.ne_zero)).ne'
  have hS_mod : S % p = 1 := sigma_prime_pow_mod_self hp_prime (N.factorization p)
  have hp_ndvd : ¬ p ∣ S := by
    rw [Nat.dvd_iff_mod_eq_zero, hS_mod]
    decide
  have hJS : J((S : ℤ) | p) = 1 := by
    have hmod : (S : ℤ) % (p : ℤ) = (1 : ℤ) % (p : ℤ) := by
      exact_mod_cast (show S % p = 1 % p by rw [hS_mod, Nat.mod_eq_of_lt hp_prime.one_lt])
    rw [jacobiSym.mod_left' hmod, jacobiSym.one_left]
  rw [oddSigmaTargets_eq_of_even hN ho hp he]
  exact (jacobiSym_oddValuationPrimes_eq hS0 hp_prime hp_ndvd).symm.trans hJS

theorem jacobi_prod_oddSigmaTargets_euler {N q : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (ha4 : N.factorization q % 4 = 1) :
    (∏ r ∈ oddSigmaTargets N q, J((r : ℤ) | q)) = ZMod.χ₈ q := by
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqo : Odd q := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)
  let S := sigma 1 (q ^ N.factorization q)
  have hS4 := sigma_modEq_of_one hq_prime (show q ≡ 1 [MOD 4] from hq4) (N.factorization q)
  change S % 4 = (N.factorization q + 1) % 4 at hS4
  have hS2 : S % 4 = 2 := by omega
  let H := S / 2
  have hSH : S = 2 * H := by omega
  have hH_odd : Odd H := Nat.odd_iff.mpr (by omega)
  have hH0 : H ≠ 0 := hH_odd.pos.ne'
  have hS_mod : S % q = 1 := sigma_prime_pow_mod_self hq_prime (N.factorization q)
  have hq_ndvd_S : ¬ q ∣ S := by
    rw [Nat.dvd_iff_mod_eq_zero, hS_mod]
    decide
  have hq_ndvd_H : ¬ q ∣ H := fun hd => hq_ndvd_S (hd.trans (by rw [hSH]; exact dvd_mul_left H 2))
  have hJS : J((S : ℤ) | q) = 1 := by
    have hmod : (S : ℤ) % (q : ℤ) = (1 : ℤ) % (q : ℤ) := by
      exact_mod_cast (show S % q = 1 % q by rw [hS_mod, Nat.mod_eq_of_lt hq_prime.one_lt])
    rw [jacobiSym.mod_left' hmod, jacobiSym.one_left]
  have hS_dvd : S ∣ 2 * N := by
    have hsplit : N = ordProj[q] N * ordCompl[q] N := (Nat.ordProj_mul_ordCompl_eq_self N q).symm
    have hcop : Nat.Coprime (ordProj[q] N) (ordCompl[q] N) :=
      (hq_prime.coprime_iff_not_dvd.mpr (Nat.not_dvd_ordCompl hq_prime hN.2.ne')).pow_left _
    have hsig_N : sigma 1 N = 2 * N :=
      (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN)
    rw [← hsig_N]
    conv_rhs => rw [hsplit]
    rw [isMultiplicative_sigma.map_mul_of_coprime hcop]
    exact dvd_mul_right _ _
  have htargets : oddSigmaTargets N q = oddValuationPrimes H := by
    ext r
    simp only [oddSigmaTargets, mem_filter, mem_oddValuationPrimes]
    constructor
    · rintro ⟨hrN, hr_odd⟩
      have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hrN
      have hro : Odd r := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hrN)
      have hn2 : ¬ r ∣ 2 := fun hd =>
        hro.not_two_dvd_nat (((Nat.prime_dvd_prime_iff_eq hr_prime Nat.prime_two).mp hd) ▸ dvd_rfl)
      have hfac : S.factorization r = H.factorization r := by
        rw [hSH, Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) hH0, Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd hn2, zero_add]
      rwa [← hfac]
    · intro hr_odd
      have hrH : r ∈ H.primeFactors := Finsupp.mem_support_iff.mpr hr_odd.pos.ne'
      have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hrH
      have hro : Odd r := hH_odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hrH)
      have hn2 : ¬ r ∣ 2 := fun hd =>
        hro.not_two_dvd_nat (((Nat.prime_dvd_prime_iff_eq hr_prime Nat.prime_two).mp hd) ▸ dvd_rfl)
      have hrS : r ∣ S := (Nat.dvd_of_mem_primeFactors hrH).trans (by rw [hSH]; exact dvd_mul_left H 2)
      have hrN : r ∣ N :=
        (hr_prime.coprime_iff_not_dvd.mpr hn2).dvd_of_dvd_mul_left (hrS.trans hS_dvd)
      have hfac : S.factorization r = H.factorization r := by
        rw [hSH, Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) hH0, Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd hn2, zero_add]
      exact ⟨Nat.mem_primeFactors.mpr ⟨hr_prime, hrN, hN.2.ne'⟩, hfac ▸ hr_odd⟩
  have hmul : (1 : ℤ) = ZMod.χ₈ q * ∏ r ∈ oddSigmaTargets N q, J((r : ℤ) | q) := by
    calc
      (1 : ℤ) = J((S : ℤ) | q) := hJS.symm
      _ = J((2 : ℤ) * (H : ℤ) | q) := by rw [hSH, Nat.cast_mul]; rfl
      _ = J((2 : ℤ) | q) * J((H : ℤ) | q) := jacobiSym.mul_left 2 (H : ℤ) q
      _ = ZMod.χ₈ q * ∏ r ∈ oddValuationPrimes H, J((r : ℤ) | q) := by
        rw [jacobiSym.at_two hqo, jacobiSym_oddValuationPrimes_eq hH0 hq_prime hq_ndvd_H]
      _ = ZMod.χ₈ q * ∏ r ∈ oddSigmaTargets N q, J((r : ℤ) | q) := by rw [htargets]
  have hχ8_sq : ZMod.χ₈ q * ZMod.χ₈ q = 1 := by
    rw [ZMod.χ₈_nat_eq_if_mod_eight, ite_eq_right (Nat.mod_two_ne_zero.mpr (Nat.odd_iff.mp hqo))]
    split_ifs <;> decide
  calc
    (∏ r ∈ oddSigmaTargets N q, J((r : ℤ) | q))
        = (ZMod.χ₈ q * ZMod.χ₈ q) * ∏ r ∈ oddSigmaTargets N q, J((r : ℤ) | q) := by
          rw [hχ8_sq, one_mul]
    _ = ZMod.χ₈ q * (ZMod.χ₈ q * ∏ r ∈ oddSigmaTargets N q, J((r : ℤ) | q)) := by ring
    _ = ZMod.χ₈ q * 1 := by rw [← hmul]
    _ = ZMod.χ₈ q := mul_one _

theorem euler_five_mod_eight_forces_nonresidue_odd_target {N q : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q ∈ N.primeFactors) (hq8 : q % 8 = 5) (ha4 : N.factorization q % 4 = 1) :
    ∃ r ∈ oddSigmaTargets N q, J((r : ℤ) | q) = -1 ∧ J((q : ℤ) | r) = -1 := by
  have hq4 : q % 4 = 1 := by omega
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hprod := jacobi_prod_oddSigmaTargets_euler hN ho hq hq4 ha4
  have hχ8 : ZMod.χ₈ q = -1 := by
    rw [ZMod.χ₈_nat_eq_if_mod_eight, ite_eq_right (by omega), ite_eq_right (by omega)]
  rw [hχ8] at hprod
  have hex : ∃ r ∈ oddSigmaTargets N q, J((r : ℤ) | q) ≠ 1 := by
    by_contra! hall
    have hone : (∏ r ∈ oddSigmaTargets N q, J((r : ℤ) | q)) = 1 := Finset.prod_eq_one hall
    rw [hone] at hprod
    norm_num at hprod
  obtain ⟨r, hr, hne1⟩ := hex
  have hrN : r ∈ N.primeFactors := (Finset.mem_filter.mp hr).1
  have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hrN
  have hro : Odd r := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hrN)
  have hr_odd_val : Odd ((sigma 1 (q ^ N.factorization q)).factorization r) :=
    (Finset.mem_filter.mp hr).2
  have hr_dvd : r ∣ sigma 1 (q ^ N.factorization q) :=
    Nat.dvd_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hr_odd_val.pos.ne')
  have hrq : r ≠ q := by
    intro heq
    rw [heq, Nat.dvd_iff_mod_eq_zero, sigma_prime_pow_mod_self hq_prime (N.factorization q)] at hr_dvd
    exact Nat.one_ne_zero hr_dvd
  have hcop : ((r : ℤ)).gcd q = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes hr_prime hq_prime).mpr hrq
  have hJr : J((r : ℤ) | q) = -1 := (jacobiSym.eq_one_or_neg_one hcop).resolve_left hne1
  have hJq : J((q : ℤ) | r) = -1 :=
    ((jacobiSym.quadratic_reciprocity_one_mod_four' hro hq4).symm).trans hJr
  exact ⟨r, hr, hJr, hJq⟩

/-! ## 3. Counterexample Filter Bank Separation Theorem -/

theorem counterexample_filter_bank_verified :
    (198585576189 ∈ classicalCandidates ∧
      ¬ Nat.Perfect 198585576189 ∧
      198585576189 ∉ fourthPowerCandidates ∧
      198585576189 ∉ normalizedSpoofCandidates ∧
      ¬ OreHarmonic 198585576189) ∧
    (DeficientPerfectWith 9018009 819 ∧ ¬ Nat.Perfect 9018009) ∧
    (Odd 173369889 ∧ NearPerfectWith 173369889 2751903 ∧
      IsSquare 173369889 ∧ ¬ Nat.Perfect 173369889) ∧
    ((11 ∣ sigma 1 (3 ^ 4) ∧ 7 ∣ sigma 1 (11 ^ 2) ∧ 3 ∣ sigma 1 (7 ^ 2)) ∧
      ¬ Nat.Perfect (3 ^ 4 * 11 ^ 2 * 7 ^ 2)) := by
  refine ⟨⟨descartes_mem_classicalCandidates, ?_, descartes_not_mem_fourthPowerCandidates,
      descartes_not_mem_normalized_spoof, descartes_not_oreHarmonic⟩,
    ⟨descartes_cofactor_deficientPerfect, ?_⟩,
    ⟨johnson_nearPerfect.1, johnson_nearPerfect.2,
      johnson_nearPerfect.2.isSquare_of_odd johnson_nearPerfect.1, ?_⟩,
    ⟨even_sigma_three_cycle, ?_⟩⟩
  · intro hp
    exact descartes_not_mem_fourthPowerCandidates
      (oddPerfectNumbers_subset_fourthPowerCandidates ⟨by decide, hp⟩)
  · intro hp
    have hsig : sigma 1 9018009 = 2 * 9018009 :=
      (sigma_one_apply _).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul hp.2).mp hp)
    have hdef := descartes_cofactor_deficientPerfect.2
    omega
  · intro hp
    exact odd_perfect_not_square johnson_nearPerfect.1 hp
      (johnson_nearPerfect.2.isSquare_of_odd johnson_nearPerfect.1)
  · intro hp
    have hsig : sigma 1 (3 ^ 4 * 11 ^ 2 * 7 ^ 2) = 2 * (3 ^ 4 * 11 ^ 2 * 7 ^ 2) :=
      (sigma_one_apply _).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul hp.2).mp hp)
    have hdef := even_sigma_three_cycle_deficient
    omega

/-! ## 4. Four-Bridge Master Reductions (`B1`–`B3` → `¬ existsOddPerfect`) & Unified Global Profile -/

theorem not_existsOddPerfect_of_rank_cap {K₀ : ℕ}
    (hcap : ∀ N : ℕ, Odd N → N.Perfect → N.primeFactors.card ≤ K₀)
    (hempty : ∀ N ≤ (max 1 (productLabelBound (2 * K₀) (2 * K₀) 1)) ^ K₀,
      ¬ (Odd N ∧ N.Perfect)) :
    ¬ existsOddPerfect := by
  unfold existsOddPerfect
  rintro ⟨N, ho, hN⟩
  exact hempty N (le_of_bounded_prime_count ho hN (hcap N ho hN)) ⟨ho, hN⟩

theorem not_existsOddPerfect_of_componentIndex_cap {K₀ : ℕ}
    (hcap : ∀ N : ℕ, Odd N → N.Perfect → ∃ p ∈ N.primeFactors, componentIndex N p ≤ K₀)
    (hempty : ∀ N ≤ componentIndexBound K₀, ¬ (Odd N ∧ N.Perfect)) :
    ¬ existsOddPerfect := by
  unfold existsOddPerfect
  rintro ⟨N, ho, hN⟩
  obtain ⟨p, hp, hK⟩ := hcap N ho hN
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have ha_pos : 0 < N.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  have hd : p ^ N.factorization p ∣ N := Nat.ordProj_dvd N p
  have hex : ¬ p ^ (N.factorization p + 1) ∣ N :=
    (hp_prime.pow_dvd_iff_le_factorization hN.2.ne').not.mpr (by omega)
  have hdiv := sigma_div_pow_factorization_eq_componentIndex (N := N) hp_prime
  exact hempty N (le_of_bounded_component_index hN ho hp_prime ha_pos hd hex (hdiv ▸ hK)) ⟨ho, hN⟩

theorem not_existsOddPerfect_of_componentIndex_multiplicity_cap {K₀ : ℕ}
    (hcap : ∀ N : ℕ, Odd N → N.Perfect → ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) ≤ K₀)
    (hempty : ∀ N ≤ (max 1 (productLabelBound (2 * (4 * K₀ + 4)) (2 * (4 * K₀ + 4)) 1)) ^ (4 * K₀ + 4),
      ¬ (Odd N ∧ N.Perfect)) :
    ¬ existsOddPerfect := by
  unfold existsOddPerfect
  rintro ⟨N, ho, hN⟩
  obtain ⟨p, hp, hK⟩ := hcap N ho hN
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have ha_pos : 0 < N.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  have hd : p ^ N.factorization p ∣ N := Nat.ordProj_dvd N p
  have hex : ¬ p ^ (N.factorization p + 1) ∣ N :=
    (hp_prime.pow_dvd_iff_le_factorization hN.2.ne').not.mpr (by omega)
  have hdiv := sigma_div_pow_factorization_eq_componentIndex (N := N) hp_prime
  exact hempty N
    (le_of_bounded_component_index_factors hN ho hp_prime ha_pos hd hex (hdiv ▸ hK)) ⟨ho, hN⟩

theorem odd_perfect_global_obstruction_profile {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    10 ^ 300 < N ∧
    5 ≤ N.primeFactors.card ∧
    2 * N.primeFactors.card + 7 ≤ cardFactors N ∧
    (∑ r ∈ N.primeFactors, (1 : ℝ) / (r : ℝ)) < Real.log 2 ∧
    (∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 4 ≤ cardFactors N) ∧
    ((∃ p, p.Prime ∧ p ^ 6 ∣ N) ∨ 443 ≤ N.primeFactors.card) ∧
    ∃ q a m, q.Prime ∧ q % 4 = 1 ∧ a % 4 = 1 ∧ ¬ q ∣ m ∧ N = q ^ a * m ^ 2 ∧
      2379 ≤ sigma 1 (m ^ 2) / q ^ a ∧
      (∏ r ∈ oddSigmaTargets N q, J((r : ℤ) | q)) = ZMod.χ₈ q := by
  refine ⟨ten_pow_three_hundred_lt_of_odd_perfect ho hN,
    five_le_distinct_prime_factor_count ho hN,
    ?_,
    sum_inv_primeFactors_lt_log_two ho hN,
    exists_componentIndex_cardFactors_add_four_le ho hN,
    (sixth_power_or_large_support ho hN).imp id And.left,
    ?_⟩
  · simpa [cardFactors_apply] using seven_le_prime_factor_count_excess ho hN
  · obtain ⟨q, a, m, hq, hq4, ha4, hqm, hform⟩ := euler_form ho hN
    have ha_pos : 0 < a := by omega
    have hm : Odd m := ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self m (by decide : 2 ≠ 0)) _)
    have hqN : q ∈ N.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq, hform ▸ dvd_mul_of_dvd_left (dvd_pow_self q ha_pos.ne') _, hN.2.ne'⟩
    have hval : N.factorization q = a := by
      rw [hform, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hm.pos.ne'),
        Finsupp.add_apply, hq.factorization_pow, Finsupp.single_eq_same, Nat.factorization_pow,
        Finsupp.smul_apply, Nat.factorization_eq_zero_of_not_dvd hqm, smul_eq_mul, mul_zero, add_zero]
    exact ⟨q, a, m, hq, hq4, ha4, hqm, hform,
      (euler_component_index_ge_2379 hN ho hq hq4 ha4 hqm hform).2,
      jacobi_prod_oddSigmaTargets_euler hN ho hqN hq4 (by simpa [hval] using ha4)⟩

end OddPerfect
