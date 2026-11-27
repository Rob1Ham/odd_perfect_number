module

public import OddPerfect.ParityDichotomy
public import OddPerfect.HarmonicComponents
public import OddPerfect.HarmonicCubic
public import OddPerfect.CohenSorli
public import OddPerfect.CyclotomicOrders
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-!
## 1. Fixed-Abundancy, Bounded-`τ(N)`, and Kanold Bounded-Mean Finiteness
-/

private lemma lt_sigma_one_of_one_lt {a : ℕ} (ha : 1 < a) : a < sigma 1 a := by
  rw [sigma_one_apply]
  have hsub : ({1, a} : Finset ℕ) ⊆ a.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Nat.one_mem_divisors.mpr (by omega)
    · exact Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩
  have hsum := Finset.sum_le_sum_of_subset (f := fun x : ℕ => x) hsub
  rw [Finset.sum_pair ha.ne] at hsum
  omega

/-- Every prime-power component of an odd integer with rational abundancy `V / U`
is bounded explicitly in terms of `max U V` and the number of distinct prime factors. -/
theorem odd_component_bound_of_rational_abundancy {N k U V : ℕ}
    (ho : Odd N) (hk : N.primeFactors.card ≤ k) (hU : 0 < U) (hV : 0 < V)
    (hbal : U * sigma 1 N = V * N) :
    ∀ p ∈ N.primeFactors,
      p ^ (N.factorization p + 1) ≤ weightedLabelBound (2 * k) (max U V) (2 * k) 1 := by
  have _ := hU
  let P := N.primeFactors
  let e := fun p => N.factorization p
  let L := fun p => p ^ (e p + 1)
  let f := fun p => p ^ e p
  let g := fun p => sigma 1 (f p)
  let S := P.disjSum P
  let label : ℕ ⊕ ℕ → ℕ := Sum.elim id L
  let aFn : ℕ ⊕ ℕ → ℕ := Sum.elim id (fun p => L p - 1)
  let bFn : ℕ ⊕ ℕ → ℕ := Sum.elim (fun p => p - 1) L
  have hgt (p) (hp : p ∈ P) : 1 < p := (Nat.prime_of_mem_primeFactors hp).one_lt
  have hoddp (p) (hp : p ∈ P) : Odd p := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
  have hless (p) (hp : p ∈ P) : p ≤ L p := by
    dsimp [L]
    rw [pow_succ']
    exact Nat.le_mul_of_pos_right p (pow_pos (hgt p hp).pos _)
  have hg_sum (p) (hp : p ∈ P) : g p = ∑ j ∈ range (e p + 1), p ^ j :=
    sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)
  have hL_sub (p) (hp : p ∈ P) : L p - 1 = (p - 1) * g p := by
    have hgeom := geom_sum_mul_add (p - 1) (e p + 1)
    rw [Nat.sub_add_cancel (hgt p hp).le, ← hg_sum p hp] at hgeom
    change g p * (p - 1) + 1 = L p at hgeom
    rw [mul_comm]
    omega
  have hL_eq (p) : L p = p * f p := pow_succ' p (e p)
  have hpf : P.prod f = N := (Nat.prod_primeFactors_pow_factorization ho.pos.ne').symm
  have hpg : P.prod g = sigma 1 N := (isMultiplicative_sigma.multiplicative_factorization _ ho.pos.ne').symm
  have hfull : U * S.prod aFn = V * S.prod bFn := by
    simp only [S, aFn, bFn, prod_disjSum, Sum.elim_inl, Sum.elim_inr, id_eq]
    have hLprod1 : (∏ p ∈ P, (L p - 1)) = (∏ p ∈ P, (p - 1)) * P.prod g := by
      rw [← prod_mul_distrib]
      exact prod_congr rfl hL_sub
    have hLprod2 : P.prod L = P.prod id * P.prod f := by
      rw [← prod_mul_distrib]
      exact prod_congr rfl (fun p _ => hL_eq p)
    rw [hLprod1, hLprod2, hpg, hpf]
    calc U * (P.prod id * ((∏ p ∈ P, (p - 1)) * sigma 1 N))
        = (U * sigma 1 N) * (P.prod id * (∏ p ∈ P, (p - 1))) := by ring
      _ = (V * N) * (P.prod id * (∏ p ∈ P, (p - 1))) := by rw [hbal]
      _ = V * ((∏ p ∈ P, (p - 1)) * (P.prod id * N)) := by ring
  have hcard : S.card ≤ 2 * k := by
    dsimp [S]
    rw [card_disjSum]
    have hP : P.card ≤ k := hk
    omega
  have hpair (i) (hi : i ∈ S) : 1 < label i ∧
      (aFn i = label i ∧ bFn i = label i - 1 ∨ aFn i = label i - 1 ∧ bFn i = label i) := by
    cases i with
    | inl p => exact ⟨hgt p (inl_mem_disjSum.mp hi), .inl ⟨rfl, rfl⟩⟩
    | inr p =>
      have hp := inr_mem_disjSum.mp hi
      exact ⟨(hgt p hp).trans_le (hless p hp), .inr ⟨rfl, rfl⟩⟩
  have hgap (T : ℕ) (hrem : ∃ i ∈ S, T < label i) :
      U * (S.filter (fun i => label i ≤ T)).prod aFn ≠
        V * (S.filter (fun i => label i ≤ T)).prod bFn := by
    intro hleft
    let left := S.filter (fun i => label i ≤ T)
    let rest := S.filter (fun i => T < label i)
    have hsplit (fn : ℕ ⊕ ℕ → ℕ) : left.prod fn * rest.prod fn = S.prod fn := by
      simpa only [left, rest, not_le] using
        S.prod_filter_mul_prod_filter_not (fun i => label i ≤ T) fn
    have hb_pos : 0 < left.prod bFn := Finset.prod_pos fun i hi => by
      change 0 < bFn i
      rcases hpair i (mem_filter.mp hi).1 with ⟨hl, ⟨_, hb⟩ | ⟨_, hb⟩⟩ <;> (rw [hb]; omega)
    have hVb_pos : 0 < V * left.prod bFn := mul_pos hV hb_pos
    have hmul : (V * left.prod bFn) * rest.prod aFn = (V * left.prod bFn) * rest.prod bFn := by
      calc (V * left.prod bFn) * rest.prod aFn
          = (U * left.prod aFn) * rest.prod aFn := by rw [hleft]
        _ = U * (left.prod aFn * rest.prod aFn) := by ring
        _ = U * S.prod aFn := by rw [hsplit]
        _ = V * S.prod bFn := hfull
        _ = V * (left.prod bFn * rest.prod bFn) := by rw [hsplit]
        _ = (V * left.prod bFn) * rest.prod bFn := by ring
    have hrest : rest.prod aFn = rest.prod bFn := Nat.eq_of_mul_eq_mul_left hVb_pos hmul
    let u := P.filter (fun p => T < p)
    let c' := P.filter (fun p => T < L p)
    let o := c' \ u
    have huc : u ⊆ c' := fun p hp =>
      mem_filter.mpr ⟨(mem_filter.mp hp).1, (mem_filter.mp hp).2.trans_le (hless p (mem_filter.mp hp).1)⟩
    have hoP : o ⊆ P := sdiff_subset.trans (filter_subset _ _)
    have huP : u ⊆ P := filter_subset _ _
    have hrest_prod (fn : ℕ ⊕ ℕ → ℕ) : rest.prod fn =
        (∏ p ∈ u, fn (.inl p)) * (∏ p ∈ c', fn (.inr p)) := by
      simp only [rest, S, prod_filter, prod_disjSum, u, c']
      rfl
    rw [hrest_prod, hrest_prod] at hrest
    have hc_a : (∏ p ∈ c', aFn (.inr p)) =
        (∏ p ∈ o, (L p - 1)) * (∏ p ∈ u, (p - 1)) * (∏ p ∈ u, g p) := by
      rw [← prod_sdiff huc]
      have h_u : (∏ p ∈ u, aFn (.inr p)) = (∏ p ∈ u, (p - 1)) * (∏ p ∈ u, g p) := by
        rw [← prod_mul_distrib]
        exact prod_congr rfl (fun p hp => hL_sub p (huP hp))
      change (∏ p ∈ o, (L p - 1)) * (∏ p ∈ u, aFn (.inr p)) = _
      rw [h_u, mul_assoc]
    have hc_b : (∏ p ∈ c', bFn (.inr p)) =
        (∏ p ∈ o, L p) * (∏ p ∈ u, p) * (∏ p ∈ u, f p) := by
      rw [← prod_sdiff huc]
      have h_u : (∏ p ∈ u, bFn (.inr p)) = (∏ p ∈ u, p) * (∏ p ∈ u, f p) := by
        rw [← prod_mul_distrib]
        exact prod_congr rfl (fun p _ => hL_eq p)
      change (∏ p ∈ o, L p) * (∏ p ∈ u, bFn (.inr p)) = _
      rw [h_u, mul_assoc]
    have hK_pos : 0 < (∏ p ∈ u, p) * (∏ p ∈ u, (p - 1)) :=
      mul_pos (prod_pos fun p hp => (hgt p (huP hp)).pos)
        (prod_pos fun p hp => Nat.sub_pos_of_lt (hgt p (huP hp)))
    have hcancel : (∏ p ∈ o, (L p - 1)) * (∏ p ∈ u, g p) =
        (∏ p ∈ o, L p) * (∏ p ∈ u, f p) := by
      apply Nat.eq_of_mul_eq_mul_right hK_pos
      have hl_a : (∏ p ∈ u, aFn (.inl p)) = ∏ p ∈ u, p := rfl
      have hl_b : (∏ p ∈ u, bFn (.inl p)) = ∏ p ∈ u, (p - 1) := rfl
      calc ((∏ p ∈ o, (L p - 1)) * (∏ p ∈ u, g p)) * ((∏ p ∈ u, p) * (∏ p ∈ u, (p - 1)))
          = (∏ p ∈ u, aFn (.inl p)) * (∏ p ∈ c', aFn (.inr p)) := by
            rw [hc_a, hl_a]; ring
        _ = (∏ p ∈ u, bFn (.inl p)) * (∏ p ∈ c', bFn (.inr p)) := hrest
        _ = ((∏ p ∈ o, L p) * (∏ p ∈ u, f p)) * ((∏ p ∈ u, p) * (∏ p ∈ u, (p - 1))) := by
            rw [hc_b, hl_b]; ring
    have hL_odd : ∀ p ∈ P, Odd (L p) := fun p hp => (hoddp p hp).pow
    have hf_odd : ∀ p ∈ P, Odd (f p) := fun p hp => (hoddp p hp).pow
    have ho_prod_odd : Odd (∏ p ∈ o, L p) :=
      prod_induction L Odd (fun _ _ => Odd.mul) odd_one (fun p hp => hL_odd p (hoP hp))
    have hu_prod_odd : Odd (∏ p ∈ u, f p) :=
      prod_induction f Odd (fun _ _ => Odd.mul) odd_one (fun p hp => hf_odd p (huP hp))
    rcases o.eq_empty_or_nonempty with ho_empty | ⟨p, hp⟩
    · have hu_ne : u.Nonempty := by
        obtain ⟨i, hiS, hTi⟩ := hrem
        cases i with
        | inl q => exact ⟨q, mem_filter.mpr ⟨inl_mem_disjSum.mp hiS, hTi⟩⟩
        | inr q =>
          have hq_c' : q ∈ c' := mem_filter.mpr ⟨inr_mem_disjSum.mp hiS, hTi⟩
          have hq_u : q ∈ u := by
            by_contra hnu
            have : q ∈ o := mem_sdiff.mpr ⟨hq_c', hnu⟩
            simp [ho_empty] at this
          exact ⟨q, hq_u⟩
      simp only [ho_empty, prod_empty, one_mul] at hcancel
      have hlt : ∏ q ∈ u, f q < ∏ q ∈ u, g q := by
        apply Finset.prod_lt_prod_of_nonempty₀
        · intro q hq
          exact pow_pos (hgt q (huP hq)).pos _
        · intro q hq
          have hqP := huP hq
          have heq : 0 < e q := (Nat.prime_of_mem_primeFactors hqP).factorization_pos_of_dvd
            ho.pos.ne' (Nat.dvd_of_mem_primeFactors hqP)
          have h1f : 1 < f q := one_lt_pow₀ (hgt q hqP) heq.ne'
          exact lt_sigma_one_of_one_lt h1f
        · exact hu_ne
      exact hlt.ne hcancel.symm
    · have hpL_odd : Odd (L p) := hL_odd p (hoP hp)
      have hpL_even : 2 ∣ L p - 1 := by
        obtain ⟨r, hr⟩ := hpL_odd
        exact ⟨r, by omega⟩
      have hlhs_even : 2 ∣ (∏ q ∈ o, (L q - 1)) * (∏ q ∈ u, g q) :=
        dvd_mul_of_dvd_left (hpL_even.trans (dvd_prod_of_mem (fun q => L q - 1) hp)) _
      have hrhs_odd : Odd ((∏ q ∈ o, L q) * (∏ q ∈ u, f q)) := ho_prod_odd.mul hu_prod_odd
      exact hrhs_odd.not_two_dvd_nat (hcancel ▸ hlhs_even)
  intro p hp
  exact labels_bounded_of_weighted_no_balanced_prefix S label aFn bFn hcard hfull hpair hgap
    (.inr p) (inr_mem_disjSum.mpr hp)

/-- Only finitely many odd integers have at most `k` distinct prime factors and
fixed rational abundancy `V / U`. -/
theorem finite_odd_of_bounded_prime_count_abundancy (k U V : ℕ) (hU : 0 < U) (hV : 0 < V) :
    Set.Finite {N : ℕ | Odd N ∧ N.primeFactors.card ≤ k ∧ U * sigma 1 N = V * N} := by
  let B := max 1 (weightedLabelBound (2 * k) (max U V) (2 * k) 1)
  apply (Set.finite_le_nat (B ^ k)).subset
  rintro N ⟨ho, hk, hbal⟩
  have hcomp := odd_component_bound_of_rational_abundancy ho hk hU hV hbal
  rw [Nat.prod_primeFactors_pow_factorization ho.pos.ne']
  have hcap (p) (hp : p ∈ N.primeFactors) : p ^ N.factorization p ≤ B :=
    (Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hp).pos (Nat.le_succ _)).trans
      ((hcomp p hp).trans (le_max_right _ _))
  have hprod := Finset.prod_le_prod₀
    (fun p (_ : p ∈ N.primeFactors) => Nat.zero_le (p ^ N.factorization p)) hcap
  rw [Finset.prod_const] at hprod
  exact hprod.trans (Nat.pow_le_pow_right (le_max_left 1 _) hk)

/-- Only finitely many odd Ore harmonic numbers have at most `T` divisors. -/
theorem finite_odd_oreHarmonic_of_bounded_divisor_count (T : ℕ) :
    Set.Finite {N : ℕ | Odd N ∧ OreHarmonic N ∧ N.divisors.card ≤ T} := by
  have hfin : (⋃ U ∈ (Finset.Icc 1 T : Set ℕ), ⋃ V ∈ (Finset.Icc 1 T : Set ℕ),
      {N : ℕ | Odd N ∧ N.primeFactors.card ≤ T ∧ U * sigma 1 N = V * N}).Finite := by
    refine (Finset.finite_toSet (Finset.Icc 1 T)).biUnion fun U _ => ?_
    refine (Finset.finite_toSet (Finset.Icc 1 T)).biUnion fun V _ => ?_
    by_cases hU : 0 < U
    · by_cases hV : 0 < V
      · exact finite_odd_of_bounded_prime_count_abundancy T U V hU hV
      · have hV0 : V = 0 := by omega
        subst hV0
        simp only [zero_mul]
        apply (Set.finite_singleton 0).subset
        rintro N ⟨ho, _, h0⟩
        exfalso
        have hs : 0 < sigma 1 N := sigma_pos_iff.mpr ho.pos
        exact (mul_pos hU hs).ne' h0
    · have hU0 : U = 0 := by omega
      subst hU0
      simp only [zero_mul]
      apply Set.finite_empty.subset
      rintro N ⟨ho, _, h0⟩
      exfalso
      have hV' : V ≠ 0 := by
        intro hV0
        have : (0 : ℕ) ∈ Finset.Icc 1 T := by assumption
        simp at this
      exact (mul_pos (Nat.pos_of_ne_zero hV') ho.pos).ne' h0.symm
  refine hfin.subset ?_
  rintro N ⟨ho, hh, hτ⟩
  obtain ⟨U, hU_eq⟩ := hh.2
  have hτ_pos : 0 < N.divisors.card := card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr ho.pos.ne'⟩
  have hU_pos : 0 < U := by
    by_contra! hU0
    have : U = 0 := by omega
    rw [this, mul_zero] at hU_eq
    exact (mul_pos ho.pos hτ_pos).ne' hU_eq
  have hσ_gt : N < sigma 1 N := lt_sigma_one_of_one_lt hh.1
  have hU_lt : U < N.divisors.card := by
    by_contra! hle
    have hmul : N * N.divisors.card < sigma 1 N * U :=
      Nat.mul_lt_mul_of_lt_of_le' hσ_gt hle hτ_pos
    omega
  have hk : N.primeFactors.card ≤ T := by
    have hsub : N.primeFactors ⊆ N.divisors := fun p hp =>
      Nat.mem_divisors.mpr ⟨Nat.dvd_of_mem_primeFactors hp, ho.pos.ne'⟩
    exact (card_le_card hsub).trans hτ
  refine Set.mem_iUnion₂.mpr ⟨U, Finset.mem_Icc.mpr ⟨hU_pos, hU_lt.le.trans hτ⟩, ?_⟩
  refine Set.mem_iUnion₂.mpr ⟨N.divisors.card, Finset.mem_Icc.mpr ⟨hτ_pos, hτ⟩, ?_⟩
  exact ⟨ho, hk, by rw [mul_comm U (sigma 1 N), ← hU_eq, mul_comm]⟩

private lemma exp_bound_four_vs_three (H : ℕ) : H * 3 ^ (3 * H + 1) < 4 ^ (3 * H + 1) := by
  induction H with
  | zero => simp
  | succ H ih =>
    rcases eq_or_ne H 0 with rfl | hH
    · decide
    · have h1 : (H + 1) * 27 < 64 * H := by omega
      calc (H + 1) * 3 ^ (3 * (H + 1) + 1)
          = (H + 1) * 27 * 3 ^ (3 * H + 1) := by
            rw [show 3 * (H + 1) + 1 = (3 * H + 1) + 3 by omega, pow_add]
            norm_num
            ring
        _ < (64 * H) * 3 ^ (3 * H + 1) :=
            Nat.mul_lt_mul_of_pos_right h1 (pow_pos (by decide) _)
        _ = 64 * (H * 3 ^ (3 * H + 1)) := by ring
        _ < 64 * 4 ^ (3 * H + 1) := Nat.mul_lt_mul_of_pos_left ih (by decide)
        _ = 4 ^ (3 * (H + 1) + 1) := by
            rw [show 3 * (H + 1) + 1 = (3 * H + 1) + 3 by omega, pow_add]
            norm_num
            ring

private lemma sigma_prime_pow_two_mul_lt_three_mul {p e : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (_he : 0 < e) : 2 * sigma 1 (p ^ e) < 3 * p ^ e := by
  have hgeom : (p - 1) * sigma 1 (p ^ e) < p * p ^ e := by
    have hsum := geom_sum_mul_add (p - 1) (e + 1)
    rw [Nat.sub_add_cancel hp.one_lt.le, ← sigma_one_apply_prime_pow hp] at hsum
    rw [← pow_succ']
    rw [mul_comm]
    omega
  have hp1 : 0 < p - 1 := by omega
  have h23 : 2 * p ≤ 3 * (p - 1) := by omega
  have hlt : (p - 1) * (2 * sigma 1 (p ^ e)) < (p - 1) * (3 * p ^ e) := by
    calc (p - 1) * (2 * sigma 1 (p ^ e))
        = 2 * ((p - 1) * sigma 1 (p ^ e)) := by ring
      _ < 2 * (p * p ^ e) := Nat.mul_lt_mul_of_pos_left hgeom (by decide)
      _ = (2 * p) * p ^ e := by ring
      _ ≤ (3 * (p - 1)) * p ^ e := Nat.mul_le_mul_right _ h23
      _ = (p - 1) * (3 * p ^ e) := by ring
  exact Nat.lt_of_mul_lt_mul_left hlt

/-- Kanold-type finiteness: only finitely many odd Ore harmonic numbers have
harmonic mean at most `H`. -/
theorem finite_odd_oreHarmonic_of_bounded_mean (H : ℕ) :
    Set.Finite {N : ℕ | Odd N ∧ OreHarmonic N ∧ N * N.divisors.card ≤ H * sigma 1 N} := by
  refine (finite_odd_oreHarmonic_of_bounded_divisor_count (H * 3 ^ (3 * H))).subset ?_
  rintro N ⟨ho, hh, hmean⟩
  refine ⟨ho, hh, ?_⟩
  let P := N.primeFactors
  let k := P.card
  have h_odd_p (p) (hp : p ∈ P) : 3 ≤ p := by
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hod := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
    have hp2 := hpr.two_le
    rcases eq_or_ne p 2 with rfl | hne
    · exact (hod.not_two_dvd_nat dvd_rfl).elim
    · omega
  have hσ_le : 2 ^ k * sigma 1 N ≤ 3 ^ k * N := by
    conv_lhs => rw [isMultiplicative_sigma.multiplicative_factorization _ ho.pos.ne']
    conv_rhs => rw [Nat.prod_primeFactors_pow_factorization ho.pos.ne']
    have h2k : 2 ^ k = ∏ _p ∈ P, 2 := by simp [k]
    have h3k : 3 ^ k = ∏ _p ∈ P, 3 := by simp [k]
    rw [h2k, h3k]
    change (∏ _p ∈ P, 2) * (∏ p ∈ P, sigma 1 (p ^ N.factorization p)) ≤
      (∏ _p ∈ P, 3) * (∏ p ∈ P, p ^ N.factorization p)
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    refine Finset.prod_le_prod fun p hp => ?_
    have hpr := Nat.prime_of_mem_primeFactors hp
    have he : 0 < N.factorization p := hpr.factorization_pos_of_dvd ho.pos.ne'
      (Nat.dvd_of_mem_primeFactors hp)
    exact (sigma_prime_pow_two_mul_lt_three_mul hpr (h_odd_p p hp) he).le
  have hτ_ge : 2 ^ k ≤ N.divisors.card := by
    rw [Nat.card_divisors ho.pos.ne']
    have h2k : 2 ^ k = ∏ _p ∈ P, 2 := by simp [k]
    rw [h2k]
    refine Finset.prod_le_prod fun p hp => ?_
    have hpr := Nat.prime_of_mem_primeFactors hp
    have he : 0 < N.factorization p := hpr.factorization_pos_of_dvd ho.pos.ne'
      (Nat.dvd_of_mem_primeFactors hp)
    omega
  have hdiv_bound : 2 ^ k * N.divisors.card ≤ H * 3 ^ k := by
    have hmul : N * (2 ^ k * N.divisors.card) ≤ N * (H * 3 ^ k) := by
      calc N * (2 ^ k * N.divisors.card)
          = 2 ^ k * (N * N.divisors.card) := by ring
        _ ≤ 2 ^ k * (H * sigma 1 N) := Nat.mul_le_mul_left _ hmean
        _ = H * (2 ^ k * sigma 1 N) := by ring
        _ ≤ H * (3 ^ k * N) := Nat.mul_le_mul_left _ hσ_le
        _ = N * (H * 3 ^ k) := by ring
    exact Nat.le_of_mul_le_mul_left hmul ho.pos
  have hk_le : k ≤ 3 * H := by
    by_contra! hgt
    have h4 : 4 ^ k ≤ H * 3 ^ k := by
      calc 4 ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
        _ ≤ 2 ^ k * N.divisors.card := Nat.mul_le_mul_left _ hτ_ge
        _ ≤ H * 3 ^ k := hdiv_bound
    have hsub : k = (3 * H + 1) + (k - (3 * H + 1)) := by omega
    have hlt : H * 3 ^ k < 4 ^ k := by
      calc H * 3 ^ k
          = H * 3 ^ ((3 * H + 1) + (k - (3 * H + 1))) := by rw [← hsub]
        _ = (H * 3 ^ (3 * H + 1)) * 3 ^ (k - (3 * H + 1)) := by rw [pow_add]; ring
        _ < 4 ^ (3 * H + 1) * 3 ^ (k - (3 * H + 1)) :=
            Nat.mul_lt_mul_of_pos_right (exp_bound_four_vs_three H) (pow_pos (by decide) _)
        _ ≤ 4 ^ (3 * H + 1) * 4 ^ (k - (3 * H + 1)) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) _)
        _ = 4 ^ ((3 * H + 1) + (k - (3 * H + 1))) := by rw [← pow_add]
        _ = 4 ^ k := by rw [← hsub]
    exact hlt.not_ge h4
  calc N.divisors.card
      ≤ 2 ^ k * N.divisors.card := Nat.le_mul_of_pos_left _ (pow_pos (by decide) _)
    _ ≤ H * 3 ^ k := hdiv_bound
    _ ≤ H * 3 ^ (3 * H) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hk_le)

/-!
## 2. Callan–Pomerance Unconditional Exclusion of `ω(N) ≤ 2` for Odd `OreHarmonic`
-/

private lemma sigma_prime_pow_mod_self' {p : ℕ} (hp : p.Prime) (a : ℕ) :
    sigma 1 (p ^ a) % p = 1 := by
  rw [sigma_one_apply_prime_pow hp, sum_range_succ', pow_zero, add_comm]
  have hd : p ∣ ∑ x ∈ range a, p ^ (x + 1) := by
    apply Finset.dvd_sum
    intro x _
    rw [pow_succ']
    exact dvd_mul_right _ _
  obtain ⟨t, ht⟩ := hd
  rw [ht, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hp.one_lt

private lemma two_mul_dvd_sub_one_of_odd_dvd {p L : ℕ} (hp : Odd p) (hL : Odd L)
    (hpL : L ∣ p - 1) (hp1 : 1 < p) : 2 * L + 1 ≤ p := by
  have h2 : 2 ∣ p - 1 := by
    obtain ⟨t, ht⟩ := hp
    exact ⟨t, by omega⟩
  have hcop : Nat.Coprime 2 L := hL.coprime_two_right.symm
  have h2L : 2 * L ∣ p - 1 := hcop.mul_dvd_of_dvd_of_dvd h2 hpL
  have hle : 2 * L ≤ p - 1 := Nat.le_of_dvd (by omega) h2L
  omega

private lemma sigma_prime_pow_four_mul_lt_five_mul {p e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (_he : 0 < e) : 4 * sigma 1 (p ^ e) < 5 * p ^ e := by
  have hgeom : (p - 1) * sigma 1 (p ^ e) < p * p ^ e := by
    have hsum := geom_sum_mul_add (p - 1) (e + 1)
    rw [Nat.sub_add_cancel hp.one_lt.le, ← sigma_one_apply_prime_pow hp] at hsum
    rw [← pow_succ']
    rw [mul_comm]
    omega
  have hp1 : 0 < p - 1 := by omega
  have h45 : 4 * p ≤ 5 * (p - 1) := by omega
  have hlt : (p - 1) * (4 * sigma 1 (p ^ e)) < (p - 1) * (5 * p ^ e) := by
    calc (p - 1) * (4 * sigma 1 (p ^ e))
        = 4 * ((p - 1) * sigma 1 (p ^ e)) := by ring
      _ < 4 * (p * p ^ e) := Nat.mul_lt_mul_of_pos_left hgeom (by decide)
      _ = (4 * p) * p ^ e := by ring
      _ ≤ (5 * (p - 1)) * p ^ e := Nat.mul_le_mul_right _ h45
      _ = (p - 1) * (5 * p ^ e) := by ring
  exact Nat.lt_of_mul_lt_mul_left hlt

private lemma geom_sum_exact_factorization_step {p q L e₂ τ : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hL : L.Prime) (hL_odd : Odd L)
    (hp_odd : Odd p) (hpq : p ≠ q)
    (hL_lt_q : L < q) (hq_ndvd_τ : ¬ q ∣ τ)
    (h_ndvd_τ : ∀ w : ℕ, w.Prime → L < w → orderOf (p : ZMod w) = L → ¬ w ∣ τ)
    (h_order : orderOf (p : ZMod q) = L)
    (h_dvd_total : sigma 1 (p ^ (L - 1)) ∣ p ^ (L - 1) * q ^ e₂ * τ) :
    ∃ ε c : ℕ, ε ≤ 1 ∧ 1 ≤ c ∧ c ≤ e₂ ∧
      sigma 1 (p ^ (L - 1)) = L ^ ε * q ^ c ∧
      (ε = 1 → L ∣ p - 1 ∧ 2 * L + 1 ≤ p) := by
  set S := sigma 1 (p ^ (L - 1))
  have hL3 : 3 ≤ L := by
    have := hL.two_le
    rcases eq_or_ne L 2 with rfl | hne
    · exact (hL_odd.not_two_dvd_nat dvd_rfl).elim
    · omega
  have hL_sub : (L - 1) + 1 = L := by omega
  have hS_pos : 0 < S := sigma_pos_iff.mpr (pow_pos hp.pos _)
  have hS_geom : S = ∑ i ∈ range L, p ^ i := by
    dsimp [S]
    rw [sigma_one_apply_prime_pow hp, hL_sub]
  have h_ndvd_p : ¬ p ∣ S := by
    intro hd
    have h1 : S % p = 1 := sigma_prime_pow_mod_self' hp (L - 1)
    obtain ⟨t, ht⟩ := hd
    rw [ht, Nat.mul_mod_right] at h1
    omega
  have hw_cases : ∀ w ∈ S.primeFactors, w = L ∨ w = q := by
    intro w hw
    have hw_pr := Nat.prime_of_mem_primeFactors hw
    have hw_S : w ∣ S := Nat.dvd_of_mem_primeFactors hw
    have hw_geom : w ∣ ∑ d ∈ (p ^ (L - 1)).divisors, d := by
      rwa [← sigma_one_apply]
    have hiff := (dvd_sum_divisors_prime_pow_iff hp hw_pr (L - 1)).mp hw_geom
    rw [hL_sub] at hiff
    let : Fact w.Prime := ⟨hw_pr⟩
    split_ifs at hiff with hp1
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hw_pr hL).mp hiff)
    · have hwp : w ≠ p := fun h => h_ndvd_p (h ▸ hw_S)
      have hp0 : (p : ZMod w) ≠ 0 := by
        intro hz
        have : w ∣ p := (ZMod.natCast_eq_zero_iff p w).mp hz
        exact hwp ((Nat.prime_dvd_prime_iff_eq hw_pr hp).mp this)
      have hord_ne1 : orderOf (p : ZMod w) ≠ 1 := fun h => hp1 (orderOf_eq_one_iff.mp h)
      have hord_eq : orderOf (p : ZMod w) = L := by
        rcases (Nat.dvd_prime hL).mp hiff with h1 | hL'
        · exact (hord_ne1 h1).elim
        · exact hL'
      have hLw : L ∣ w - 1 := hord_eq ▸ ZMod.orderOf_dvd_card_sub_one hp0
      have hLw_lt : L < w := by
        have := Nat.le_of_dvd (by have := hw_pr.one_lt; omega) hLw
        omega
      have hw_ndvd_τ : ¬ w ∣ τ := h_ndvd_τ w hw_pr hLw_lt hord_eq
      have hw_tot := hw_S.trans h_dvd_total
      rw [mul_assoc] at hw_tot
      have hw_rhs := (hw_pr.dvd_mul.mp hw_tot).resolve_left fun hd =>
        hwp ((Nat.prime_dvd_prime_iff_eq hw_pr hp).mp (hw_pr.dvd_of_dvd_pow hd))
      have hw_q := (hw_pr.dvd_mul.mp hw_rhs).resolve_right hw_ndvd_τ
      exact Or.inr ((Nat.prime_dvd_prime_iff_eq hw_pr hq).mp (hw_pr.dvd_of_dvd_pow hw_q))
  have hsub : S.primeFactors ⊆ {L, q} := fun w hw => by
    rcases hw_cases w hw with rfl | rfl <;> simp
  have hS_prod : S = L ^ S.factorization L * q ^ S.factorization q := by
    have h := (Nat.prod_primeFactors_pow_factorization hS_pos.ne').symm
    have hprod_eq : ∏ w ∈ S.primeFactors, w ^ S.factorization w =
        ∏ w ∈ ({L, q} : Finset ℕ), w ^ S.factorization w := by
      refine Finset.prod_subset hsub fun w _ hwn => ?_
      have : S.factorization w = 0 := Finsupp.notMem_support_iff.mp hwn
      simp [this]
    rw [hprod_eq, Finset.prod_pair hL_lt_q.ne] at h
    exact h.symm
  have hε : S.factorization L ≤ 1 := by
    by_contra! hge
    have hL2 : L ^ 2 ∣ S := (hL.pow_dvd_iff_le_factorization hS_pos.ne').mpr hge
    have hL1 : L ∣ S := (dvd_pow_self L (by decide : 2 ≠ 0)).trans hL2
    rw [hS_geom] at hL1 hL2
    exact not_sq_dvd_geom_sum hL hL_odd hL1 hL2
  have hc_ge : 1 ≤ S.factorization q := by
    have hq_geom : q ∣ sigma 1 (p ^ (L - 1)) := by
      rw [sigma_one_apply]
      have hiff := (dvd_sum_divisors_prime_pow_iff hp hq (L - 1)).mpr
      rw [hL_sub] at hiff
      apply hiff
      let : Fact q.Prime := ⟨hq⟩
      have hq1 : (p : ZMod q) ≠ 1 := by
        intro h1
        have := orderOf_eq_one_iff.mpr h1
        rw [h_order] at this
        omega
      simp [hq1, h_order]
    exact (hq.dvd_iff_one_le_factorization hS_pos.ne').mp hq_geom
  have hc_le : S.factorization q ≤ e₂ := by
    have hqc : q ^ S.factorization q ∣ S := Nat.ordProj_dvd S q
    have htot := hqc.trans h_dvd_total
    have hcop1 : Nat.Coprime (q ^ S.factorization q) (p ^ (L - 1)) :=
      (hq.coprime_iff_not_dvd.mpr fun hd =>
        hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp hd).symm).pow_left _ |>.pow_right _
    have htot' := hcop1.dvd_of_dvd_mul_left (by simpa only [mul_assoc] using htot)
    have hcop2 : Nat.Coprime (q ^ S.factorization q) τ :=
      (hq.coprime_iff_not_dvd.mpr hq_ndvd_τ).pow_left _
    have hpow := hcop2.dvd_of_dvd_mul_right htot'
    exact (Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp hpow
  refine ⟨S.factorization L, S.factorization q, hε, hc_ge, hc_le, hS_prod, fun hε1 => ?_⟩
  have hLS : L ∣ S := (hL.dvd_iff_one_le_factorization hS_pos.ne').mpr (by omega)
  have hpL : p ≠ L := fun h => h_ndvd_p (h ▸ hLS)
  have hL_geom : L ∣ ∑ d ∈ (p ^ (L - 1)).divisors, d := by rwa [← sigma_one_apply]
  have hiff := (dvd_sum_divisors_prime_pow_iff hp hL (L - 1)).mp hL_geom
  rw [hL_sub] at hiff
  let : Fact L.Prime := ⟨hL⟩
  have hpL1 : (p : ZMod L) = 1 := by
    by_contra hne
    simp only [hne, ↓reduceIte] at hiff
    have hp0 : (p : ZMod L) ≠ 0 := by
      intro hz
      exact hpL ((Nat.prime_dvd_prime_iff_eq hL hp).mp ((ZMod.natCast_eq_zero_iff p L).mp hz)).symm
    have hord_ne1 : orderOf (p : ZMod L) ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
    have hord_eq : orderOf (p : ZMod L) = L := by
      rcases (Nat.dvd_prime hL).mp hiff with h1 | hL'
      · exact (hord_ne1 h1).elim
      · exact hL'
    have hLL : L ∣ L - 1 := by
      have hord_dvd := ZMod.orderOf_dvd_card_sub_one hp0
      rwa [hord_eq] at hord_dvd
    have := Nat.le_of_dvd (by omega) hLL
    omega
  have hLp : L ∣ p - 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    have := congrArg (· - (1 : ZMod L)) hpL1
    simpa [Nat.cast_sub hp.pos] using this
  exact ⟨hLp, two_mul_dvd_sub_one_of_odd_dvd hp_odd hL_odd hLp hp.one_lt⟩

private lemma symm_equal_prime_length_contradiction {p q L c₁ c₂ : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hL : L.Prime) (hL_odd : Odd L) (hL3 : 3 ≤ L)
    (_hp_odd : Odd p) (_hq_odd : Odd q)
    (hLp : 2 * L ∣ p - 1) (hLq : 2 * L ∣ q - 1)
    (hc1 : 1 ≤ c₁) (_hc2 : 1 ≤ c₂) (hc1_le : c₁ ≤ L - 1) (hc2_le : c₂ ≤ L - 1)
    (hS1 : sigma 1 (p ^ (L - 1)) = L * q ^ c₁)
    (hS2 : sigma 1 (q ^ (L - 1)) = L * p ^ c₂)
    (hD : p ^ (L - 1 - c₂) * q ^ (L - 1 - c₁) < L ^ 2)
    (hD1 : 1 < p ^ (L - 1 - c₂) * q ^ (L - 1 - c₁)) : False := by
  have hp_min : 2 * L + 1 ≤ p := by
    have := Nat.le_of_dvd (by have := hp.one_lt; omega) hLp
    omega
  have hq_min : p + 2 * L ≤ q := by
    have hsub : 2 * L ∣ q - p := by
      have h1 : 2 * L ∣ q - 1 := hLq
      have h2 : 2 * L ∣ p - 1 := hLp
      have heq : q - p = (q - 1) - (p - 1) := by omega
      rw [heq]
      exact Nat.dvd_sub h1 h2
    have := Nat.le_of_dvd (by omega) hsub
    omega
  have hq_ge : 4 * L + 1 ≤ q := by omega
  have h_a_lt2 : L - 1 - c₂ < 2 := by
    by_contra! hge
    have hp2 : p ^ 2 ≤ p ^ (L - 1 - c₂) := Nat.pow_le_pow_right hp.pos hge
    have hp2_D : p ^ 2 ≤ p ^ (L - 1 - c₂) * q ^ (L - 1 - c₁) :=
      hp2.trans (Nat.le_mul_of_pos_right _ (pow_pos hq.pos _))
    have hL2 : L ^ 2 < p ^ 2 := by nlinarith
    omega
  have h_b_lt2 : L - 1 - c₁ < 2 := by
    by_contra! hge
    have hq2 : q ^ 2 ≤ q ^ (L - 1 - c₁) := Nat.pow_le_pow_right hq.pos hge
    have hq2_D : q ^ 2 ≤ p ^ (L - 1 - c₂) * q ^ (L - 1 - c₁) :=
      hq2.trans (Nat.le_mul_of_pos_left _ (pow_pos hp.pos _))
    have hL2 : L ^ 2 < q ^ 2 := by nlinarith
    omega
  have h_not_both : ¬ (1 ≤ L - 1 - c₂ ∧ 1 ≤ L - 1 - c₁) := by
    rintro ⟨ha, hb⟩
    have hpq_le : p * q ≤ p ^ (L - 1 - c₂) * q ^ (L - 1 - c₁) :=
      Nat.mul_le_mul (Nat.le_self_pow (by omega) p) (Nat.le_self_pow (by omega) q)
    have hL2 : L ^ 2 < p * q := by nlinarith
    omega
  have h_not_zero : ¬ (L - 1 - c₂ = 0 ∧ L - 1 - c₁ = 0) := by
    rintro ⟨ha, hb⟩
    simp [ha, hb] at hD1
  have hab : (L - 1 - c₂ = 1 ∧ L - 1 - c₁ = 0) ∨ (L - 1 - c₂ = 0 ∧ L - 1 - c₁ = 1) := by
    omega
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hc1_eq : c₁ = L - 1 := by omega
    rw [hc1_eq] at hS1
    have hpow_le : p ^ (L - 1) ≤ q ^ (L - 1) := Nat.pow_le_pow_left hpq.le _
    have h23 : 2 * sigma 1 (p ^ (L - 1)) < 3 * p ^ (L - 1) :=
      sigma_prime_pow_two_mul_lt_three_mul hp (by omega) (by omega)
    have h3L : 3 * p ^ (L - 1) ≤ L * q ^ (L - 1) := Nat.mul_le_mul hL3 hpow_le
    rw [hS1] at h23
    omega
  · have hc2_eq : c₂ = L - 1 := by omega
    have hc1_eq : c₁ = L - 2 := by omega
    rw [hc2_eq] at hS2
    rw [hc1_eq] at hS1
    rcases (show L = 3 ∨ 5 ≤ L by
      rcases eq_or_ne L 3 with rfl | hne3
      · exact Or.inl rfl
      · have hne4 : L ≠ 4 := fun h => hL_odd.not_two_dvd_nat (h ▸ (by decide : 2 ∣ 4))
        exact Or.inr (by omega)) with rfl | hL5
    · norm_num at hS1 hS2
      rw [sigma_one_apply_prime_pow hp] at hS1
      rw [sigma_one_apply_prime_pow hq] at hS2
      simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero, pow_one] at hS1 hS2
      have hp7 : 7 ≤ p := by omega
      have hq19 : 19 ≤ q := by nlinarith only [hp7, hS1]
      nlinarith only [hp7, hq19, hS1, hS2]
    · have h_pL : q ^ 2 ∣ p ^ L - 1 := by
        have hgeom := geom_sum_mul_add (p - 1) L
        rw [Nat.sub_add_cancel hp.one_lt.le, show ∑ i ∈ range L, p ^ i = sigma 1 (p ^ (L - 1)) from by
          rw [sigma_one_apply_prime_pow hp, show (L - 1) + 1 = L by omega], hS1] at hgeom
        have hq2 : q ^ 2 ∣ q ^ (L - 2) := pow_dvd_pow q (by omega)
        have hdvd : q ^ 2 ∣ (L * q ^ (L - 2)) * (p - 1) :=
          hq2.trans (dvd_mul_of_dvd_left (dvd_mul_left _ L) _)
        have heq : p ^ L - 1 = (L * q ^ (L - 2)) * (p - 1) := by omega
        exact heq ▸ hdvd
      have hpL_mod : p ^ L ≡ 1 [MOD q ^ 2] := by
        obtain ⟨t, ht⟩ := h_pL
        have hpow1 : 1 ≤ p ^ L := Nat.one_le_pow _ _ hp.pos
        refine (Nat.modEq_iff_dvd.mpr ⟨(t : ℤ), ?_⟩).symm
        zify [hpow1] at ht ⊢
        linarith
      have hS2_mod : sigma 1 (q ^ (L - 1)) ≡ 1 + q [MOD q ^ 2] := by
        rw [sigma_one_apply_prime_pow hq, show (L - 1) + 1 = L by omega]
        have hL_split : L = 2 + (L - 2) := by omega
        have hsplit : ∑ i ∈ range L, q ^ i = (1 + q) + q ^ 2 * ∑ j ∈ range (L - 2), q ^ j := by
          conv_lhs => rw [hL_split]
          rw [sum_range_add, sum_range_succ, sum_range_one, pow_zero, pow_one, mul_sum]
          congr 1
          refine sum_congr rfl fun j _ => ?_
          rw [← pow_add]
        rw [hsplit]
        exact (Nat.modEq_iff_dvd.mpr ⟨((∑ j ∈ range (L - 2), q ^ j : ℕ) : ℤ), by push_cast; ring⟩).symm
      rw [hS2] at hS2_mod
      have hmul_mod : p * (1 + q) ≡ p * (L * p ^ (L - 1)) [MOD q ^ 2] :=
        Nat.ModEq.mul_left p hS2_mod.symm
      have h_eq_L : p * (L * p ^ (L - 1)) = L * p ^ L := by
        calc p * (L * p ^ (L - 1)) = L * (p * p ^ (L - 1)) := by ring
          _ = L * p ^ ((L - 1) + 1) := by rw [← pow_succ']
          _ = L * p ^ L := by rw [show (L - 1) + 1 = L by omega]
      rw [h_eq_L] at hmul_mod
      have hL_mod : L * p ^ L ≡ L [MOD q ^ 2] := by
        simpa only [mul_one] using Nat.ModEq.mul_left L hpL_mod
      have h_final : p * (1 + q) ≡ L [MOD q ^ 2] := hmul_mod.trans hL_mod
      have hlt1 : p * (1 + q) < q ^ 2 := by nlinarith
      have hlt2 : L < q ^ 2 := by nlinarith
      rw [Nat.ModEq, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at h_final
      have hlt3 : L < p * (1 + q) := by nlinarith
      omega

private lemma length_eq_of_forced_prime {p q L e : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) (hL : L.Prime) (hL_odd : Odd L)
    (hL_dvd : L ∣ e + 1) (hq_ord : orderOf (p : ZMod q) = L)
    (hforce : ∀ d w : ℕ, d ∣ e + 1 → L ≤ d → w.Prime →
      orderOf (p : ZMod w) = d → d ∣ w - 1 → w = q) :
    e + 1 = L := by
  obtain ⟨u, hu⟩ := hL_dvd
  by_contra hne
  have hu1 : 1 < u := by
    rcases eq_or_ne u 0 with rfl | hu0
    · simp at hu
    · rcases eq_or_ne u 1 with rfl | hu1
      · rw [mul_one] at hu; exact (hne hu).elim
      · omega
  obtain ⟨ℓ, hℓ, hℓu⟩ := Nat.exists_prime_and_dvd hu1.ne'
  rcases eq_or_ne ℓ L with hℓ_eq | hℓL
  · have hL2_dvd : L * L ∣ e + 1 := by
      obtain ⟨t, ht⟩ := hℓu
      exact ⟨t, by rw [hu, ht, hℓ_eq]; ring⟩
    obtain ⟨w, hw, hord, hdw⟩ := exists_prime_order_prime_pow hp.one_lt hL hL_odd 1
    simp only [pow_succ, pow_zero, one_mul] at hord hdw
    have hLL2 : L ≤ L * L := Nat.le_mul_of_pos_right L hL.pos
    obtain rfl := hforce (L * L) w hL2_dvd hLL2 hw hord hdw
    rw [hq_ord] at hord
    have hlt : L < L * L := lt_mul_of_one_lt_right hL.pos hL.one_lt
    omega
  · have hℓL_dvd : ℓ * L ∣ e + 1 := by
      obtain ⟨t, ht⟩ := hℓu
      exact ⟨t, by rw [hu, ht]; ring⟩
    have hℓL_gt1 : 1 < ℓ * L := by
      have := Nat.mul_le_mul hℓ.two_le hL.two_le
      omega
    have h_not_pp : ¬ IsPrimePow (ℓ * L) := by
      intro hpp
      rw [isPrimePow_iff_unique_prime_dvd] at hpp
      obtain ⟨r, _, hr_uniq⟩ := hpp
      have h1 := hr_uniq ℓ ⟨hℓ, dvd_mul_right _ _⟩
      have h2 := hr_uniq L ⟨hL, dvd_mul_left _ _⟩
      exact hℓL (h1.trans h2.symm)
    obtain ⟨w, hw, hord, hdw⟩ := exists_prime_order_mixed hp3 hℓL_gt1 h_not_pp
    have hL_le : L ≤ ℓ * L := Nat.le_mul_of_pos_left L hℓ.pos
    obtain rfl := hforce (ℓ * L) w hℓL_dvd hL_le hw hord hdw
    rw [hq_ord] at hord
    have hlt : L < ℓ * L := lt_mul_of_one_lt_left hL.pos hℓ.one_lt
    omega

/-- No odd Ore harmonic number has exactly two distinct prime factors. -/
theorem not_odd_oreHarmonic_primeFactors_card_eq_two {N : ℕ} (ho : Odd N) (hh : OreHarmonic N) :
    N.primeFactors.card ≠ 2 := by
  intro hcard2
  have hN_pos : 0 < N := ho.pos
  set τ := N.divisors.card with hτ_def
  have hτ_pos : 0 < τ := card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hN_pos.ne'⟩
  obtain ⟨r₀, hr₀, hr₀_odd, hr₀_dvd⟩ := odd_prime_dvd_card_divisors_of_odd_harmonic ho hh
  have hr₀_mem : r₀ ∈ τ.primeFactors := Nat.mem_primeFactors.mpr ⟨hr₀, hr₀_dvd, hτ_pos.ne'⟩
  let L := τ.primeFactors.max' ⟨r₀, hr₀_mem⟩
  have hL_mem : L ∈ τ.primeFactors := Finset.max'_mem _ _
  have hL : L.Prime := Nat.prime_of_mem_primeFactors hL_mem
  have hL_dvd_τ : L ∣ τ := Nat.dvd_of_mem_primeFactors hL_mem
  have hr₀_le_L : r₀ ≤ L := Finset.le_max' _ _ hr₀_mem
  have hr₀_ge3 : 3 ≤ r₀ := by
    have := hr₀.two_le
    rcases eq_or_ne r₀ 2 with rfl | hne
    · exact (hr₀_odd.not_two_dvd_nat dvd_rfl).elim
    · omega
  have hL3 : 3 ≤ L := hr₀_ge3.trans hr₀_le_L
  have hL_odd : Odd L := hL.odd_of_ne_two (by omega)
  have hmax_τ : ∀ w : ℕ, w.Prime → w ∣ τ → w ≤ L := fun w hw hwd =>
    Finset.le_max' _ w (Nat.mem_primeFactors.mpr ⟨hw, hwd, hτ_pos.ne'⟩)
  obtain ⟨q₁, q₂, hq12, hPF⟩ := Finset.card_eq_two.mp hcard2
  have hτ_q : τ = (N.factorization q₁ + 1) * (N.factorization q₂ + 1) := by
    rw [hτ_def, Nat.card_divisors hN_pos.ne', hPF, Finset.prod_pair hq12]
  have hL_cases : L ∣ N.factorization q₁ + 1 ∨ L ∣ N.factorization q₂ + 1 :=
    hL.dvd_mul.mp (hτ_q ▸ hL_dvd_τ)
  obtain ⟨p₁, p₂, hp12, hPF', hL_dvd_e1⟩ : ∃ p₁ p₂ : ℕ,
      p₁ ≠ p₂ ∧ N.primeFactors = {p₁, p₂} ∧ L ∣ N.factorization p₁ + 1 := by
    rcases hL_cases with h | h
    · exact ⟨q₁, q₂, hq12, hPF, h⟩
    · exact ⟨q₂, q₁, hq12.symm, by rw [hPF, Finset.pair_comm], h⟩
  have hp₁_mem : p₁ ∈ N.primeFactors := by rw [hPF']; simp
  have hp₂_mem : p₂ ∈ N.primeFactors := by rw [hPF']; simp
  have hp₁ : p₁.Prime := Nat.prime_of_mem_primeFactors hp₁_mem
  have hp₂ : p₂.Prime := Nat.prime_of_mem_primeFactors hp₂_mem
  have hp₁_odd : Odd p₁ := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp₁_mem)
  have hp₂_odd : Odd p₂ := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp₂_mem)
  have hp₁_3 : 3 ≤ p₁ := by
    have := hp₁.two_le
    rcases eq_or_ne p₁ 2 with rfl | hne
    · exact (hp₁_odd.not_two_dvd_nat dvd_rfl).elim
    · omega
  have hp₂_3 : 3 ≤ p₂ := by
    have := hp₂.two_le
    rcases eq_or_ne p₂ 2 with rfl | hne
    · exact (hp₂_odd.not_two_dvd_nat dvd_rfl).elim
    · omega
  set e₁ := N.factorization p₁
  set e₂ := N.factorization p₂
  have he₁_pos : 0 < e₁ := hp₁.factorization_pos_of_dvd hN_pos.ne' (Nat.dvd_of_mem_primeFactors hp₁_mem)
  have he₂_pos : 0 < e₂ := hp₂.factorization_pos_of_dvd hN_pos.ne' (Nat.dvd_of_mem_primeFactors hp₂_mem)
  have hN_eq : N = p₁ ^ e₁ * p₂ ^ e₂ := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hN_pos.ne', hPF', Finset.prod_pair hp12]
  have hτ_eq : τ = (e₁ + 1) * (e₂ + 1) := by
    rw [hτ_def, Nat.card_divisors hN_pos.ne', hPF', Finset.prod_pair hp12]
  have hcop_N : Nat.Coprime (p₁ ^ e₁) (p₂ ^ e₂) :=
    ((hp₁.coprime_iff_not_dvd.mpr fun hd =>
      hp12 ((Nat.prime_dvd_prime_iff_eq hp₁ hp₂).mp hd)).pow_left _).pow_right _
  have hσ_eq : sigma 1 N = sigma 1 (p₁ ^ e₁) * sigma 1 (p₂ ^ e₂) := by
    conv_lhs => rw [hN_eq]
    exact isMultiplicative_sigma.map_mul_of_coprime hcop_N
  have hσ_dvd : sigma 1 N ∣ p₁ ^ e₁ * p₂ ^ e₂ * τ := by
    rw [← hN_eq]
    exact hh.2
  have forced_prime_1 : ∀ d w : ℕ, d ∣ e₁ + 1 → L ≤ d → w.Prime →
      orderOf (p₁ : ZMod w) = d → d ∣ w - 1 → w = p₂ := by
    intro d w hd_e1 hLd hw hord hdw
    have hd3 : 3 ≤ d := hL3.trans hLd
    have hdw_lt : d < w := by
      have := Nat.le_of_dvd (by have := hw.one_lt; omega) hdw
      omega
    have hLw_lt : L < w := hLd.trans_lt hdw_lt
    have hw_ndvd_τ : ¬ w ∣ τ := fun h => (hmax_τ w hw h).not_gt hLw_lt
    have hwp1 : w ≠ p₁ := by
      rintro rfl
      let : Fact w.Prime := ⟨hw⟩
      rw [ZMod.natCast_self, orderOf_zero] at hord
      omega
    have hp1_ne1 : (p₁ : ZMod w) ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hord
      omega
    have hw_S1 : w ∣ sigma 1 (p₁ ^ e₁) := by
      rw [sigma_one_apply]
      apply (dvd_sum_divisors_prime_pow_iff hp₁ hw e₁).mpr
      simp [hp1_ne1, hord, hd_e1]
    have hw_tot : w ∣ p₁ ^ e₁ * p₂ ^ e₂ * τ :=
      hw_S1.trans ((dvd_mul_right _ _).trans (hσ_eq ▸ hσ_dvd))
    rw [mul_assoc] at hw_tot
    have hw_rhs := (hw.dvd_mul.mp hw_tot).resolve_left fun hd =>
      hwp1 ((Nat.prime_dvd_prime_iff_eq hw hp₁).mp (hw.dvd_of_dvd_pow hd))
    have hw_q := (hw.dvd_mul.mp hw_rhs).resolve_right hw_ndvd_τ
    exact (Nat.prime_dvd_prime_iff_eq hw hp₂).mp (hw.dvd_of_dvd_pow hw_q)
  have hp2_ord_L : orderOf (p₁ : ZMod p₂) = L ∧ L ∣ p₂ - 1 := by
    obtain ⟨w, hw, hord, hdw⟩ := exists_prime_order_prime_pow hp₁.one_lt hL hL_odd 0
    simp only [zero_add, pow_one] at hord hdw
    obtain rfl := forced_prime_1 L w hL_dvd_e1 le_rfl hw hord hdw
    exact ⟨hord, hdw⟩
  have hL_lt_p2 : L < p₂ := by
    have := Nat.le_of_dvd (by have := hp₂.one_lt; omega) hp2_ord_L.2
    omega
  have hp2_min : 2 * L + 1 ≤ p₂ :=
    two_mul_dvd_sub_one_of_odd_dvd hp₂_odd hL_odd hp2_ord_L.2 hp₂.one_lt
  have he1_eq : e₁ + 1 = L :=
    length_eq_of_forced_prime hp₁ hp₁_3 hL hL_odd hL_dvd_e1 hp2_ord_L.1 forced_prime_1
  have he1_sub : e₁ = L - 1 := by omega
  have hp2_ndvd_τ : ¬ p₂ ∣ τ := fun h => (hmax_τ p₂ hp₂ h).not_gt hL_lt_p2
  have hS1_fact : ∃ ε c : ℕ, ε ≤ 1 ∧ 1 ≤ c ∧ c ≤ e₂ ∧
      sigma 1 (p₁ ^ (L - 1)) = L ^ ε * p₂ ^ c ∧ (ε = 1 → L ∣ p₁ - 1 ∧ 2 * L + 1 ≤ p₁) := by
    apply geom_sum_exact_factorization_step hp₁ hp₂ hL hL_odd hp₁_odd hp12 hL_lt_p2 hp2_ndvd_τ
      (fun w hw hLw _ hwd => (hmax_τ w hw hwd).not_gt hLw) hp2_ord_L.1
    rw [← he1_sub]
    exact (dvd_mul_right _ _).trans (hσ_eq ▸ hσ_dvd)
  obtain ⟨ε, c, hε, hc_ge, hc_le, hS1_eq, hε1_p1⟩ := hS1_fact
  have hp2_mod_L : (p₂ : ZMod L) = 1 := by
    have h0 : ((p₂ - 1 : ℕ) : ZMod L) = 0 := (ZMod.natCast_eq_zero_iff (p₂ - 1) L).mpr hp2_ord_L.2
    rw [Nat.cast_sub hp₂.pos, Nat.cast_one, sub_eq_zero] at h0
    exact h0
  by_cases h_odd_e2 : ∃ r : ℕ, r.Prime ∧ r ∣ e₂ + 1 ∧ r ≠ 2
  · obtain ⟨r₁, hr₁, hr₁_dvd, hr₁_ne2⟩ := h_odd_e2
    let M := (e₂ + 1).primeFactors.max'
      ⟨r₁, Nat.mem_primeFactors.mpr ⟨hr₁, hr₁_dvd, by omega⟩⟩
    have hM_mem : M ∈ (e₂ + 1).primeFactors := Finset.max'_mem _ _
    have hM : M.Prime := Nat.prime_of_mem_primeFactors hM_mem
    have hM_dvd : M ∣ e₂ + 1 := Nat.dvd_of_mem_primeFactors hM_mem
    have hr₁_le_M : r₁ ≤ M :=
      Finset.le_max' _ r₁ (Nat.mem_primeFactors.mpr ⟨hr₁, hr₁_dvd, by omega⟩)
    have hM3 : 3 ≤ M := by
      have := hr₁.two_le
      omega
    have hM_odd : Odd M := hM.odd_of_ne_two (by omega)
    have hM_le_L : M ≤ L := hmax_τ M hM (hM_dvd.trans (hτ_eq ▸ dvd_mul_left _ _))
    have hmax_e2 : ∀ w : ℕ, w.Prime → w ∣ e₂ + 1 → w ≤ M := fun w hw hwd =>
      Finset.le_max' _ w (Nat.mem_primeFactors.mpr ⟨hw, hwd, by omega⟩)
    have forced_prime_2 : ∀ d w : ℕ, d ∣ e₂ + 1 → M ≤ d → w.Prime →
        orderOf (p₂ : ZMod w) = d → d ∣ w - 1 → w = p₁ := by
      intro d w hd_e2 hMd hw hord hdw
      have hd3 : 3 ≤ d := hM3.trans hMd
      have hdw_lt : d < w := by
        have := Nat.le_of_dvd (by have := hw.one_lt; omega) hdw
        omega
      have hMw_lt : M < w := hMd.trans_lt hdw_lt
      have hw_ndvd_e2 : ¬ w ∣ e₂ + 1 := fun h => (hmax_e2 w hw h).not_gt hMw_lt
      have hwp2 : w ≠ p₂ := by
        rintro rfl
        let : Fact w.Prime := ⟨hw⟩
        rw [ZMod.natCast_self, orderOf_zero] at hord
        omega
      have hwL : w ≠ L := by
        rintro rfl
        rw [hp2_mod_L, orderOf_one] at hord
        omega
      have hp2_ne1 : (p₂ : ZMod w) ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hord
        omega
      have hw_S2 : w ∣ sigma 1 (p₂ ^ e₂) := by
        rw [sigma_one_apply]
        apply (dvd_sum_divisors_prime_pow_iff hp₂ hw e₂).mpr
        simp [hp2_ne1, hord, hd_e2]
      have hw_tot : w ∣ p₁ ^ e₁ * p₂ ^ e₂ * (L * (e₂ + 1)) := by
        rw [← he1_eq, ← hτ_eq]
        exact hw_S2.trans ((dvd_mul_left _ _).trans (hσ_eq ▸ hσ_dvd))
      have hw_1 : w ∣ p₁ ^ e₁ * p₂ ^ e₂ := by
        refine (hw.dvd_mul.mp hw_tot).resolve_right fun h => ?_
        rcases hw.dvd_mul.mp h with hL' | he2'
        · exact hwL ((Nat.prime_dvd_prime_iff_eq hw hL).mp hL')
        · exact hw_ndvd_e2 he2'
      have hw_p1 : w ∣ p₁ ^ e₁ := (hw.dvd_mul.mp hw_1).resolve_right fun hd =>
        hwp2 ((Nat.prime_dvd_prime_iff_eq hw hp₂).mp (hw.dvd_of_dvd_pow hd))
      exact (Nat.prime_dvd_prime_iff_eq hw hp₁).mp (hw.dvd_of_dvd_pow hw_p1)
    have hp1_ord_M : orderOf (p₂ : ZMod p₁) = M ∧ M ∣ p₁ - 1 := by
      obtain ⟨w, hw, hord, hdw⟩ := exists_prime_order_prime_pow hp₂.one_lt hM hM_odd 0
      simp only [zero_add, pow_one] at hord hdw
      obtain rfl := forced_prime_2 M w hM_dvd le_rfl hw hord hdw
      exact ⟨hord, hdw⟩
    have hM_lt_p1 : M < p₁ := by
      have := Nat.le_of_dvd (by have := hp₁.one_lt; omega) hp1_ord_M.2
      omega
    have hp1_min_M : 2 * M + 1 ≤ p₁ :=
      two_mul_dvd_sub_one_of_odd_dvd hp₁_odd hM_odd hp1_ord_M.2 hp₁.one_lt
    have he2_eq : e₂ + 1 = M :=
      length_eq_of_forced_prime hp₂ hp₂_3 hM hM_odd hM_dvd hp1_ord_M.1 forced_prime_2
    have he2_sub : e₂ = M - 1 := by omega
    have hp1_ne_L : p₁ ≠ L := by
      rintro rfl
      have := hp1_ord_M.1
      rw [hp2_mod_L, orderOf_one] at this
      omega
    have hp1_ndvd_τ : ¬ p₁ ∣ τ := by
      rw [hτ_eq, he1_eq, he2_eq]
      intro h
      rcases hp₁.dvd_mul.mp h with hL' | hM'
      · exact hp1_ne_L ((Nat.prime_dvd_prime_iff_eq hp₁ hL).mp hL')
      · have := Nat.le_of_dvd hM.pos hM'
        omega
    have hS2_fact : ∃ ε' c' : ℕ, ε' ≤ 1 ∧ 1 ≤ c' ∧ c' ≤ L - 1 ∧
        sigma 1 (p₂ ^ (M - 1)) = M ^ ε' * p₁ ^ c' ∧ (ε' = 1 → M ∣ p₂ - 1 ∧ 2 * M + 1 ≤ p₂) := by
      apply geom_sum_exact_factorization_step hp₂ hp₁ hM hM_odd hp₂_odd hp12.symm hM_lt_p1 hp1_ndvd_τ
        ?_ hp1_ord_M.1
      · rw [← he1_sub, ← he2_sub]
        have hmul : p₁ ^ e₁ * p₂ ^ e₂ * τ = p₂ ^ e₂ * p₁ ^ e₁ * τ := by ring
        rw [← hmul]
        exact (dvd_mul_left _ _).trans (hσ_eq ▸ hσ_dvd)
      · intro w hw hMw hord hwd
        rw [hτ_eq, he1_eq, he2_eq] at hwd
        rcases hw.dvd_mul.mp hwd with hL' | hM'
        · obtain rfl := (Nat.prime_dvd_prime_iff_eq hw hL).mp hL'
          rw [hp2_mod_L, orderOf_one] at hord
          omega
        · exact hMw.not_ge (Nat.le_of_dvd hM.pos hM')
    obtain ⟨ε', c', hε', hc'_ge, hc'_le, hS2_eq, hε'1_p2⟩ := hS2_fact
    have hc_le' : c ≤ M - 1 := by omega
    set D := p₁ ^ (L - 1 - c') * p₂ ^ (M - 1 - c)
    have hK_pos : 0 < p₁ ^ c' * p₂ ^ c := mul_pos (pow_pos hp₁.pos _) (pow_pos hp₂.pos _)
    have hN_split : N = (p₁ ^ c' * p₂ ^ c) * D := by
      rw [hN_eq, he1_sub, he2_sub]
      have h1 : p₁ ^ (L - 1) = p₁ ^ c' * p₁ ^ (L - 1 - c') := by
        rw [← pow_add, Nat.add_sub_cancel' hc'_le]
      have h2 : p₂ ^ (M - 1) = p₂ ^ c * p₂ ^ (M - 1 - c) := by
        rw [← pow_add, Nat.add_sub_cancel' hc_le']
      rw [h1, h2]
      dsimp [D]
      ring
    have hσ_split : sigma 1 N = (p₁ ^ c' * p₂ ^ c) * (L ^ ε * M ^ ε') := by
      rw [hσ_eq, he1_sub, he2_sub, hS1_eq, hS2_eq]
      ring
    have hD_lt : D < L ^ ε * M ^ ε' := by
      have hlt : N < sigma 1 N := lt_sigma_one_of_one_lt hh.1
      rw [hσ_split, hN_split] at hlt
      exact Nat.lt_of_mul_lt_mul_left hlt
    have h8σ_lt : 8 * sigma 1 N < 15 * N := by
      have h5_cases : 5 ≤ p₁ ∨ 5 ≤ p₂ := by
        by_contra! hlt
        have hp1_eq3 : p₁ = 3 := by omega
        have hp2_eq3 : p₂ = 3 := by omega
        exact hp12 (hp1_eq3.trans hp2_eq3.symm)
      rw [hσ_eq, hN_eq]
      rcases h5_cases with h5p1 | h5p2
      · have h1 := sigma_prime_pow_four_mul_lt_five_mul hp₁ h5p1 he₁_pos
        have h2 := sigma_prime_pow_two_mul_lt_three_mul hp₂ hp₂_3 he₂_pos
        calc 8 * (sigma 1 (p₁ ^ e₁) * sigma 1 (p₂ ^ e₂))
            = (4 * sigma 1 (p₁ ^ e₁)) * (2 * sigma 1 (p₂ ^ e₂)) := by ring
          _ < (5 * p₁ ^ e₁) * (3 * p₂ ^ e₂) :=
              Nat.mul_lt_mul'' h1 h2
          _ = 15 * (p₁ ^ e₁ * p₂ ^ e₂) := by ring
      · have h1 := sigma_prime_pow_two_mul_lt_three_mul hp₁ hp₁_3 he₁_pos
        have h2 := sigma_prime_pow_four_mul_lt_five_mul hp₂ h5p2 he₂_pos
        calc 8 * (sigma 1 (p₁ ^ e₁) * sigma 1 (p₂ ^ e₂))
            = (2 * sigma 1 (p₁ ^ e₁)) * (4 * sigma 1 (p₂ ^ e₂)) := by ring
          _ < (3 * p₁ ^ e₁) * (5 * p₂ ^ e₂) :=
              Nat.mul_lt_mul'' h1 h2
          _ = 15 * (p₁ ^ e₁ * p₂ ^ e₂) := by ring
    have h8_lt_15D : 8 * (L ^ ε * M ^ ε') < 15 * D := by
      rw [hσ_split, hN_split] at h8σ_lt
      have hmul : (p₁ ^ c' * p₂ ^ c) * (8 * (L ^ ε * M ^ ε')) <
          (p₁ ^ c' * p₂ ^ c) * (15 * D) := by
        calc (p₁ ^ c' * p₂ ^ c) * (8 * (L ^ ε * M ^ ε'))
            = 8 * ((p₁ ^ c' * p₂ ^ c) * (L ^ ε * M ^ ε')) := by ring
          _ < 15 * ((p₁ ^ c' * p₂ ^ c) * D) := h8σ_lt
          _ = (p₁ ^ c' * p₂ ^ c) * (15 * D) := by ring
      exact Nat.lt_of_mul_lt_mul_left hmul
    have hD_gt1 : 1 < D := by
      have hD_pos : 0 < D := mul_pos (pow_pos hp₁.pos _) (pow_pos hp₂.pos _)
      by_contra! hle
      have hD1 : D = 1 := by omega
      rw [hD1, mul_one] at h8_lt_15D
      rw [hD1] at hD_lt
      omega
    have hmin_le_D : min p₁ p₂ ≤ D := by
      by_cases h1 : 1 ≤ L - 1 - c'
      · have hp1_D : p₁ ≤ D :=
          (Nat.le_self_pow (by omega) p₁).trans (Nat.le_mul_of_pos_right _ (pow_pos hp₂.pos _))
        exact (min_le_left p₁ p₂).trans hp1_D
      · have h2 : 1 ≤ M - 1 - c := by
          by_contra! h2'
          have h01 : L - 1 - c' = 0 := by omega
          have h02 : M - 1 - c = 0 := by omega
          simp [D, h01, h02] at hD_gt1
        have hp2_D : p₂ ≤ D :=
          (Nat.le_self_pow (by omega) p₂).trans (Nat.le_mul_of_pos_left _ (pow_pos hp₁.pos _))
        exact (min_le_right p₁ p₂).trans hp2_D
    have hε_eq1 : ε = 1 := by
      by_contra hne
      have hε0 : ε = 0 := by omega
      rw [hε0, pow_zero, one_mul] at hD_lt
      have hM_pow : M ^ ε' ≤ M := by
        rcases (show ε' = 0 ∨ ε' = 1 by omega) with rfl | rfl
        · simp only [pow_zero]; exact hM.pos
        · simp only [pow_one, le_rfl]
      have hMp1 : M < p₁ := hM_lt_p1
      have hMp2 : M < p₂ := hM_le_L.trans_lt hL_lt_p2
      have hM_lt_min : M < min p₁ p₂ := lt_min hMp1 hMp2
      omega
    obtain ⟨hL_dvd_p1_sub, hp1_min_L⟩ := hε1_p1 hε_eq1
    have hε'_eq1 : ε' = 1 := by
      by_contra hne
      have hε'0 : ε' = 0 := by omega
      rw [hε_eq1, hε'0, pow_one, pow_zero, mul_one] at hD_lt
      have hLp1 : L < p₁ := by omega
      have hL_lt_min : L < min p₁ p₂ := lt_min hLp1 hL_lt_p2
      omega
    obtain ⟨hM_dvd_p2_sub, _⟩ := hε'1_p2 hε'_eq1
    rw [hε_eq1, hε'_eq1, pow_one, pow_one] at hD_lt
    rw [hε_eq1, pow_one] at hS1_eq
    rw [hε'_eq1, pow_one] at hS2_eq
    rcases hM_le_L.eq_or_lt with hML | hM_lt_L
    · dsimp [D] at hD_lt hD_gt1
      rw [hML] at hD_lt hD_gt1 hS2_eq hc_le'
      have h2L_p1 : 2 * L ∣ p₁ - 1 :=
        (hL_odd.coprime_two_right.symm).mul_dvd_of_dvd_of_dvd
          (by obtain ⟨t, ht⟩ := hp₁_odd; exact ⟨t, by omega⟩) hL_dvd_p1_sub
      have h2L_p2 : 2 * L ∣ p₂ - 1 :=
        (hL_odd.coprime_two_right.symm).mul_dvd_of_dvd_of_dvd
          (by obtain ⟨t, ht⟩ := hp₂_odd; exact ⟨t, by omega⟩) hp2_ord_L.2
      rcases lt_or_gt_of_ne hp12 with hp12_lt | hp21_lt
      · exact symm_equal_prime_length_contradiction hp₁ hp₂ hp12_lt hL hL_odd hL3
          hp₁_odd hp₂_odd h2L_p1 h2L_p2 hc_ge hc'_ge hc_le' hc'_le hS1_eq hS2_eq
          (by simpa [pow_two] using hD_lt) hD_gt1
      · have hD' : p₂ ^ (L - 1 - c) * p₁ ^ (L - 1 - c') < L ^ 2 := by
          simpa [mul_comm, pow_two] using hD_lt
        have hD1' : 1 < p₂ ^ (L - 1 - c) * p₁ ^ (L - 1 - c') := by
          simpa [mul_comm] using hD_gt1
        exact symm_equal_prime_length_contradiction hp₂ hp₁ hp21_lt hL hL_odd hL3
          hp₂_odd hp₁_odd h2L_p2 h2L_p1 hc'_ge hc_ge hc'_le hc_le' hS2_eq hS1_eq hD' hD1'
    · have hL5 : 5 ≤ L := by
        have hne4 : L ≠ 4 := fun h => hL_odd.not_two_dvd_nat (h ▸ (by decide : 2 ∣ 4))
        omega
      have h2LM_dvd : 2 * L * M ∣ p₂ - 1 := by
        have h2_dvd : 2 ∣ p₂ - 1 := by obtain ⟨t, ht⟩ := hp₂_odd; exact ⟨t, by omega⟩
        have hcop_2L : Nat.Coprime 2 L := hL_odd.coprime_two_right.symm
        have h2L_dvd : 2 * L ∣ p₂ - 1 := hcop_2L.mul_dvd_of_dvd_of_dvd h2_dvd hp2_ord_L.2
        have hcop_2_M : Nat.Coprime 2 M := hM_odd.coprime_two_right.symm
        have hcop_L_M : Nat.Coprime L M :=
          (Nat.coprime_primes hL hM).mpr hM_lt_L.ne'
        have hcop_2L_M : Nat.Coprime (2 * L) M := hcop_2_M.mul_left hcop_L_M
        exact hcop_2L_M.mul_dvd_of_dvd_of_dvd h2L_dvd hM_dvd_p2_sub
      have hp2_min_2LM : 2 * L * M + 1 ≤ p₂ := by
        have := Nat.le_of_dvd (by have := hp₂.one_lt; omega) h2LM_dvd
        omega
      have hc_eq : c = M - 1 := by
        by_contra hne
        have hc_lt : 1 ≤ M - 1 - c := by omega
        have hp2_le_D : p₂ ≤ D :=
          (Nat.le_self_pow (by omega) p₂).trans (Nat.le_mul_of_pos_left _ (pow_pos hp₁.pos _))
        rw [mul_assoc] at hp2_min_2LM
        omega
      have hc'_eq : c' = L - 2 := by
        have h_lt2 : L - 1 - c' < 2 := by
          by_contra! hge
          have hp1_sq : p₁ ^ 2 ≤ p₁ ^ (L - 1 - c') := Nat.pow_le_pow_right hp₁.pos hge
          have hp1_sq_D : p₁ ^ 2 ≤ D := hp1_sq.trans (Nat.le_mul_of_pos_right _ (pow_pos hp₂.pos _))
          have hLM_lt : L * M < p₁ ^ 2 := by nlinarith only [hp1_min_L, hM_lt_L]
          omega
        have h_pos : 1 ≤ L - 1 - c' := by
          by_contra! h0
          have h0' : L - 1 - c' = 0 := by omega
          have h0'' : M - 1 - c = 0 := by omega
          dsimp [D] at hD_gt1
          rw [h0', h0'', pow_zero, pow_zero, mul_one] at hD_gt1
          omega
        omega
      rw [hc_eq] at hS1_eq
      rw [hc'_eq] at hS2_eq
      have hS1_low : (p₁ + 1) * p₁ ^ (L - 2) < sigma 1 (p₁ ^ (L - 1)) := by
        have hL_sub1 : (L - 1) + 1 = L := by omega
        have hL_split : L = (L - 2) + 2 := by omega
        conv_rhs =>
          rw [sigma_one_apply_prime_pow hp₁, hL_sub1, hL_split, sum_range_add, sum_range_succ,
            sum_range_one]
        have hrest_pos : 0 < ∑ x ∈ range (L - 2), p₁ ^ x :=
          Finset.sum_pos (fun _ _ => pow_pos hp₁.pos _) ⟨0, Finset.mem_range.mpr (by omega)⟩
        have hpow_eq : p₁ ^ (L - 2 + 0) + p₁ ^ (L - 2 + 1) = (p₁ + 1) * p₁ ^ (L - 2) := by
          rw [add_zero, pow_succ']
          ring
        linarith
      have hS2_low : p₂ ^ (M - 1) < sigma 1 (p₂ ^ (M - 1)) := by
        have hM_sub1 : (M - 1) + 1 = M := by omega
        have hM_split : M = (M - 1) + 1 := by omega
        conv_rhs =>
          rw [sigma_one_apply_prime_pow hp₂, hM_sub1, hM_split, sum_range_succ]
        have hrest_pos : 0 < ∑ x ∈ range (M - 1), p₂ ^ x :=
          Finset.sum_pos (fun _ _ => pow_pos hp₂.pos _) ⟨0, Finset.mem_range.mpr (by omega)⟩
        linarith
      have hlow_mul : (p₁ + 1) * p₁ ^ (L - 2) * p₂ ^ (M - 1) <
          (L * M) * (p₁ ^ (L - 2) * p₂ ^ (M - 1)) := by
        calc (p₁ + 1) * p₁ ^ (L - 2) * p₂ ^ (M - 1)
            = ((p₁ + 1) * p₁ ^ (L - 2)) * p₂ ^ (M - 1) := by ring
          _ < sigma 1 (p₁ ^ (L - 1)) * sigma 1 (p₂ ^ (M - 1)) :=
              Nat.mul_lt_mul'' hS1_low hS2_low
          _ = (L * p₂ ^ (M - 1)) * (M * p₁ ^ (L - 2)) := by rw [hS1_eq, hS2_eq]
          _ = (L * M) * (p₁ ^ (L - 2) * p₂ ^ (M - 1)) := by ring
      have hp1_LM : p₁ + 2 ≤ L * M := by
        have hpow_pos : 0 < p₁ ^ (L - 2) * p₂ ^ (M - 1) :=
          mul_pos (pow_pos hp₁.pos _) (pow_pos hp₂.pos _)
        have hlow_mul' : (p₁ + 1) * (p₁ ^ (L - 2) * p₂ ^ (M - 1)) <
            (L * M) * (p₁ ^ (L - 2) * p₂ ^ (M - 1)) := by
          rw [← mul_assoc]
          exact hlow_mul
        have hlt := Nat.lt_of_mul_lt_mul_right hlow_mul'
        omega
      have hS1_up : (p₁ - 1) * sigma 1 (p₁ ^ (L - 1)) < p₁ ^ L := by
        have hgeom := geom_sum_mul_add (p₁ - 1) L
        rw [Nat.sub_add_cancel hp₁.one_lt.le] at hgeom
        have hsum_eq : ∑ i ∈ range L, p₁ ^ i = sigma 1 (p₁ ^ (L - 1)) := by
          rw [sigma_one_apply_prime_pow hp₁, show (L - 1) + 1 = L by omega]
        rw [hsum_eq] at hgeom
        rw [mul_comm]
        omega
      have hS2_up : (p₂ - 1) * sigma 1 (p₂ ^ (M - 1)) < p₂ ^ M := by
        have hgeom := geom_sum_mul_add (p₂ - 1) M
        rw [Nat.sub_add_cancel hp₂.one_lt.le] at hgeom
        have hsum_eq : ∑ i ∈ range M, p₂ ^ i = sigma 1 (p₂ ^ (M - 1)) := by
          rw [sigma_one_apply_prime_pow hp₂, show (M - 1) + 1 = M by omega]
        rw [hsum_eq] at hgeom
        rw [mul_comm]
        omega
      have hup_mul : (L * M * (p₁ - 1) * (p₂ - 1)) * (p₁ ^ (L - 2) * p₂ ^ (M - 1)) <
          (p₁ ^ 2 * p₂) * (p₁ ^ (L - 2) * p₂ ^ (M - 1)) := by
        have hp1L : p₁ ^ L = p₁ ^ 2 * p₁ ^ (L - 2) := by
          rw [← pow_add, show 2 + (L - 2) = L by omega]
        have hp2M : p₂ ^ M = p₂ * p₂ ^ (M - 1) := by
          rw [← pow_succ', show (M - 1) + 1 = M by omega]
        calc (L * M * (p₁ - 1) * (p₂ - 1)) * (p₁ ^ (L - 2) * p₂ ^ (M - 1))
            = ((p₁ - 1) * (L * p₂ ^ (M - 1))) * ((p₂ - 1) * (M * p₁ ^ (L - 2))) := by ring
          _ = ((p₁ - 1) * sigma 1 (p₁ ^ (L - 1))) * ((p₂ - 1) * sigma 1 (p₂ ^ (M - 1))) := by
              rw [hS1_eq, hS2_eq]
          _ < p₁ ^ L * p₂ ^ M := Nat.mul_lt_mul'' hS1_up hS2_up
          _ = (p₁ ^ 2 * p₂) * (p₁ ^ (L - 2) * p₂ ^ (M - 1)) := by rw [hp1L, hp2M]; ring
      have hfinal_lt : L * M * (p₁ - 1) * (p₂ - 1) < p₁ ^ 2 * p₂ :=
        Nat.lt_of_mul_lt_mul_right hup_mul
      set LM := L * M
      have hp1_11 : 11 ≤ p₁ := by omega
      have hLM_ge : p₁ + 2 ≤ LM := hp1_LM
      have hp2_ge : 2 * LM + 1 ≤ p₂ := by simpa [LM, mul_assoc] using hp2_min_2LM
      have hfinal' : LM * (p₁ - 1) * (p₂ - 1) < p₁ ^ 2 * p₂ := hfinal_lt
      zify [hp₁.pos, hp₂.pos] at hfinal' hp1_11 hLM_ge hp2_ge
      have h1 : (p₁ : ℤ) ^ 2 + p₁ - 2 ≤ LM * (p₁ - 1) := by nlinarith only [hLM_ge, hp1_11]
      have h2 : (2 : ℤ) * (p₁ + 2) ≤ p₂ - 1 := by linarith
      have h3 : (p₁ : ℤ) ^ 2 + 1 ≤ (p₁ - 2) * (p₂ - 1) := by nlinarith only [h2, hp1_11]
      have h4 : (p₁ : ℤ) ^ 2 * p₂ < (p₁ ^ 2 + p₁ - 2) * (p₂ - 1) := by
        have heq : (p₁ : ℤ) ^ 2 * p₂ + (p₁ - 2) * (p₂ - 1) - p₁ ^ 2 =
            (p₁ ^ 2 + p₁ - 2) * (p₂ - 1) := by ring
        linarith
      have h5 : (p₁ : ℤ) ^ 2 * p₂ < LM * (p₁ - 1) * (p₂ - 1) :=
        h4.trans_le (mul_le_mul_of_nonneg_right h1 (by linarith))
      linarith
  · push Not at h_odd_e2
    have he2_pf : (e₂ + 1).primeFactors ⊆ {2} := fun r hr =>
      Finset.mem_singleton.mpr (h_odd_e2 r (Nat.prime_of_mem_primeFactors hr)
        (Nat.dvd_of_mem_primeFactors hr))
    set k := (e₂ + 1).factorization 2
    have he2_pow : e₂ + 1 = 2 ^ k := by
      have h := (Nat.prod_primeFactors_pow_factorization (by omega : e₂ + 1 ≠ 0)).symm
      have hprod_eq : ∏ w ∈ (e₂ + 1).primeFactors, w ^ (e₂ + 1).factorization w =
          ∏ w ∈ ({2} : Finset ℕ), w ^ (e₂ + 1).factorization w := by
        refine Finset.prod_subset he2_pf fun w _ hwn => ?_
        have : (e₂ + 1).factorization w = 0 := Finsupp.notMem_support_iff.mp hwn
        simp [this]
      rw [hprod_eq, Finset.prod_singleton] at h
      exact h.symm
    have hk_pos : 1 ≤ k := by
      by_contra! hk0
      have hk_eq0 : k = 0 := by omega
      rw [hk_eq0, pow_zero] at he2_pow
      omega
    have he2_odd : Odd e₂ := by
      have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
      rw [← he2_pow] at h2
      obtain ⟨t, ht⟩ := h2
      exact Nat.odd_iff.mpr (by omega)
    have hp2_mod4 : p₂ % 4 = 1 := by
      have hcomp := odd_harmonic_component_one_mod_four ho hh hp₂_mem
      have hp2_odd_mod := Nat.odd_iff.mp hp₂_odd
      by_contra hne
      have hp2_3' : p₂ ≡ 3 [MOD 4] := by change p₂ % 4 = 3; omega
      obtain ⟨t, ht⟩ := he2_odd
      have hs : p₂ ^ 2 ≡ 1 [MOD 4] := (hp2_3'.pow 2).trans (by decide)
      have hpow3 : p₂ ^ e₂ ≡ 3 [MOD 4] := by
        rw [ht, pow_succ, pow_mul]
        simpa only [one_pow, one_mul] using (hs.pow t).mul hp2_3'
      change p₂ ^ e₂ % 4 = 3 at hpow3
      change p₂ ^ e₂ % 4 = 1 at hcomp
      omega
    have hL_ndvd_p2_succ : ¬ L ∣ p₂ + 1 := by
      intro hd
      have h0 : ((p₂ + 1 : ℕ) : ZMod L) = 0 := (ZMod.natCast_eq_zero_iff (p₂ + 1) L).mpr hd
      rw [Nat.cast_add, Nat.cast_one, hp2_mod_L] at h0
      have h20 : ((2 : ℕ) : ZMod L) = 0 := by simpa [one_add_one_eq_two] using h0
      have hL2 : L ∣ 2 := (ZMod.natCast_eq_zero_iff 2 L).mp h20
      have := Nat.le_of_dvd (by decide) hL2
      omega
    have hL_ndvd_p2_sq : ¬ L ∣ p₂ ^ 2 + 1 := by
      intro hd
      have h0 : ((p₂ ^ 2 + 1 : ℕ) : ZMod L) = 0 := (ZMod.natCast_eq_zero_iff (p₂ ^ 2 + 1) L).mpr hd
      rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one, hp2_mod_L, one_pow] at h0
      have h20 : ((2 : ℕ) : ZMod L) = 0 := by simpa [one_add_one_eq_two] using h0
      have hL2 : L ∣ 2 := (ZMod.natCast_eq_zero_iff 2 L).mp h20
      have := Nat.le_of_dvd (by decide) hL2
      omega
    set d₂ := (p₂ + 1) / 2
    have hd₂_eq : 2 * d₂ = p₂ + 1 := by omega
    have hd₂_odd : Odd d₂ := Nat.odd_iff.mpr (by omega)
    have hd₂_gt1 : 1 < d₂ := by omega
    have hd₂_prime_eq : ∀ w : ℕ, w.Prime → w ∣ d₂ → w = p₁ := by
      intro w hw hwd
      have hw_odd : Odd w := hd₂_odd.of_dvd_nat hwd
      have hw_p2_1 : w ∣ p₂ + 1 := hwd.trans ⟨2, by omega⟩
      have hw_S2 : w ∣ sigma 1 (p₂ ^ e₂) := hw_p2_1.trans (succ_dvd_sigma_prime_pow hp₂ he2_odd)
      have hw_tot : w ∣ p₁ ^ e₁ * p₂ ^ e₂ * (L * (e₂ + 1)) := by
        rw [← he1_eq, ← hτ_eq]
        exact hw_S2.trans ((dvd_mul_left _ _).trans (hσ_eq ▸ hσ_dvd))
      have hw_ndvd_e2 : ¬ w ∣ e₂ + 1 := fun h => by
        rcases eq_or_ne w 2 with rfl | hne
        · exact hw_odd.not_two_dvd_nat dvd_rfl
        · exact hne (h_odd_e2 w hw h)
      have hwL : w ≠ L := fun h => hL_ndvd_p2_succ (h ▸ hw_p2_1)
      have hwp2 : w ≠ p₂ := by
        rintro rfl
        have := Nat.dvd_sub hw_p2_1 (dvd_refl w)
        simp only [Nat.add_sub_cancel_left] at this
        exact hw.not_dvd_one this
      have hw_1 : w ∣ p₁ ^ e₁ * p₂ ^ e₂ := by
        refine (hw.dvd_mul.mp hw_tot).resolve_right fun h => ?_
        rcases hw.dvd_mul.mp h with hL' | he2'
        · exact hwL ((Nat.prime_dvd_prime_iff_eq hw hL).mp hL')
        · exact hw_ndvd_e2 he2'
      have hw_p1 : w ∣ p₁ ^ e₁ := (hw.dvd_mul.mp hw_1).resolve_right fun hd =>
        hwp2 ((Nat.prime_dvd_prime_iff_eq hw hp₂).mp (hw.dvd_of_dvd_pow hd))
      exact (Nat.prime_dvd_prime_iff_eq hw hp₁).mp (hw.dvd_of_dvd_pow hw_p1)
    have hp1_dvd_d₂ : p₁ ∣ d₂ := by
      let w := d₂.minFac
      have hw : w.Prime := Nat.minFac_prime hd₂_gt1.ne'
      have hwd : w ∣ d₂ := Nat.minFac_dvd d₂
      obtain rfl := hd₂_prime_eq w hw hwd
      exact hwd
    have hp1_dvd_p2_succ : p₁ ∣ p₂ + 1 := hp1_dvd_d₂.trans ⟨2, by omega⟩
    rcases (show 2 ≤ k ∨ k = 1 by omega) with hk2 | hk1
    · have h4_dvd : 4 ∣ e₂ + 1 := by
        rw [he2_pow]
        exact pow_dvd_pow 2 hk2
      obtain ⟨t, ht⟩ := h4_dvd
      have hp2_sq_dvd : p₂ ^ 2 + 1 ∣ sigma 1 (p₂ ^ e₂) := by
        rw [sigma_one_apply_prime_pow hp₂]
        change p₂ ^ 2 + 1 ∣ geometricBlock p₂ (e₂ + 1)
        rw [ht, geometricBlock_mul]
        have hblock4 : geometricBlock p₂ 4 = (1 + p₂) * (p₂ ^ 2 + 1) := by
          simp [geometricBlock, sum_range_succ]
          ring
        rw [hblock4]
        exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
      set d₄ := (p₂ ^ 2 + 1) / 2
      have hp2_sq_mod4 : (p₂ ^ 2 + 1) % 4 = 2 := by
        have h : p₂ ^ 2 ≡ 1 [MOD 4] := ((show p₂ ≡ 1 [MOD 4] from hp2_mod4).pow 2).trans (by decide)
        change p₂ ^ 2 % 4 = 1 at h
        omega
      have hd₄_eq : 2 * d₄ = p₂ ^ 2 + 1 := by omega
      have hd₄_odd : Odd d₄ := Nat.odd_iff.mpr (by omega)
      have hd₄_gt1 : 1 < d₄ := by
        have hp2_sq : 49 ≤ p₂ ^ 2 := by nlinarith only [hp2_min, hL3]
        omega
      let w₄ := d₄.minFac
      have hw₄ : w₄.Prime := Nat.minFac_prime hd₄_gt1.ne'
      have hw₄_d : w₄ ∣ d₄ := Nat.minFac_dvd d₄
      have hw₄_odd : Odd w₄ := hd₄_odd.of_dvd_nat hw₄_d
      have hw₄_sq : w₄ ∣ p₂ ^ 2 + 1 := hw₄_d.trans ⟨2, by omega⟩
      have hw₄_S2 : w₄ ∣ sigma 1 (p₂ ^ e₂) := hw₄_sq.trans hp2_sq_dvd
      have hw₄_tot : w₄ ∣ p₁ ^ e₁ * p₂ ^ e₂ * (L * (e₂ + 1)) := by
        rw [← he1_eq, ← hτ_eq]
        exact hw₄_S2.trans ((dvd_mul_left _ _).trans (hσ_eq ▸ hσ_dvd))
      have hw₄_ndvd_e2 : ¬ w₄ ∣ e₂ + 1 := fun h => by
        rcases eq_or_ne w₄ 2 with hw₄_eq2 | hne
        · exact hw₄_odd.not_two_dvd_nat (hw₄_eq2 ▸ dvd_rfl)
        · exact hne (h_odd_e2 w₄ hw₄ h)
      have hw₄L : w₄ ≠ L := fun h => hL_ndvd_p2_sq (h ▸ hw₄_sq)
      have hw₄p2 : w₄ ≠ p₂ := by
        intro hw₄_eq
        have h1 : w₄ ∣ p₂ ^ 2 := hw₄_eq ▸ dvd_pow_self p₂ (by decide : 2 ≠ 0)
        have h2 := Nat.dvd_sub hw₄_sq h1
        simp only [Nat.add_sub_cancel_left] at h2
        exact hw₄.not_dvd_one h2
      have hw₄_1 : w₄ ∣ p₁ ^ e₁ * p₂ ^ e₂ := by
        refine (hw₄.dvd_mul.mp hw₄_tot).resolve_right fun h => ?_
        rcases hw₄.dvd_mul.mp h with hL' | he2'
        · exact hw₄L ((Nat.prime_dvd_prime_iff_eq hw₄ hL).mp hL')
        · exact hw₄_ndvd_e2 he2'
      have hw₄_p1 : w₄ ∣ p₁ ^ e₁ := (hw₄.dvd_mul.mp hw₄_1).resolve_right fun hd =>
        hw₄p2 ((Nat.prime_dvd_prime_iff_eq hw₄ hp₂).mp (hw₄.dvd_of_dvd_pow hd))
      have hw₄_eq_p1 : w₄ = p₁ := (Nat.prime_dvd_prime_iff_eq hw₄ hp₁).mp (hw₄.dvd_of_dvd_pow hw₄_p1)
      have hp1_dvd_sq : p₁ ∣ p₂ ^ 2 + 1 := hw₄_eq_p1 ▸ hw₄_sq
      have hp1_dvd_2 : p₁ ∣ 2 := by
        have hmul : p₁ ∣ p₂ * (p₂ + 1) := hp1_dvd_p2_succ.mul_left p₂
        have hsum : p₁ ∣ p₂ ^ 2 + 1 + (p₂ + 1) := hp1_dvd_sq.add hp1_dvd_p2_succ
        have heq : p₂ ^ 2 + 1 + (p₂ + 1) = p₂ * (p₂ + 1) + 2 := by ring
        rw [heq] at hsum
        exact (Nat.dvd_add_right hmul).mp hsum
      have := Nat.le_of_dvd (by decide) hp1_dvd_2
      omega
    · have he2_eq1 : e₂ = 1 := by rw [hk1, pow_one] at he2_pow; omega
      have hc_eq1 : c = 1 := by omega
      rw [hc_eq1, pow_one] at hS1_eq
      set m := d₂.factorization p₁
      have hd₂_pf : d₂.primeFactors ⊆ {p₁} := fun w hw =>
        Finset.mem_singleton.mpr (hd₂_prime_eq w (Nat.prime_of_mem_primeFactors hw)
          (Nat.dvd_of_mem_primeFactors hw))
      have hd₂_pow : d₂ = p₁ ^ m := by
        have h := (Nat.prod_primeFactors_pow_factorization hd₂_odd.pos.ne').symm
        have hprod_eq : ∏ w ∈ d₂.primeFactors, w ^ d₂.factorization w =
            ∏ w ∈ ({p₁} : Finset ℕ), w ^ d₂.factorization w := by
          refine Finset.prod_subset hd₂_pf fun w _ hwn => ?_
          have : d₂.factorization w = 0 := Finsupp.notMem_support_iff.mp hwn
          simp [this]
        rw [hprod_eq, Finset.prod_singleton] at h
        exact h.symm
      have hm_pos : 1 ≤ m := by
        by_contra! hm0
        have hm_eq0 : m = 0 := by omega
        rw [hm_eq0, pow_zero] at hd₂_pow
        omega
      have hp2_succ_eq : p₂ + 1 = 2 * p₁ ^ m := by rw [← hd₂_eq, hd₂_pow]
      have hS1_sum : sigma 1 (p₁ ^ (L - 1)) + L ^ ε = L ^ ε * (2 * p₁ ^ m) := by
        calc sigma 1 (p₁ ^ (L - 1)) + L ^ ε = L ^ ε * p₂ + L ^ ε := by rw [hS1_eq]
          _ = L ^ ε * (p₂ + 1) := by ring
          _ = L ^ ε * (2 * p₁ ^ m) := by rw [hp2_succ_eq]
      have hp1_dvd_rhs : p₁ ∣ L ^ ε * (2 * p₁ ^ m) :=
        dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_pow_self p₁ (by omega)) 2) _
      rw [← hS1_sum] at hp1_dvd_rhs
      have hmod1 : sigma 1 (p₁ ^ (L - 1)) % p₁ = 1 := sigma_prime_pow_mod_self' hp₁ (L - 1)
      have hp1_dvd_1_L : p₁ ∣ 1 + L ^ ε := by
        have h0 : (sigma 1 (p₁ ^ (L - 1)) + L ^ ε) % p₁ = 0 := Nat.mod_eq_zero_of_dvd hp1_dvd_rhs
        rw [Nat.add_mod, hmod1] at h0
        have : (1 + L ^ ε) % p₁ = 0 := by
          simpa [Nat.add_mod, Nat.mod_eq_of_lt hp₁.one_lt] using h0
        exact Nat.dvd_of_mod_eq_zero this
      rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
      · norm_num at hp1_dvd_1_L
        have := Nat.le_of_dvd (by decide) hp1_dvd_1_L
        omega
      · rw [pow_one] at hp1_dvd_1_L
        have hp1_le : p₁ ≤ 1 + L := Nat.le_of_dvd (by omega) hp1_dvd_1_L
        have hp1_ge := (hε1_p1 rfl).2
        omega

/-- Every odd Ore harmonic number has at least three distinct prime factors. -/
theorem odd_oreHarmonic_three_le_primeFactors {N : ℕ} (ho : Odd N) (hh : OreHarmonic N) :
    3 ≤ N.primeFactors.card := by
  by_contra! hlt
  have h0 : N.primeFactors.card ≠ 0 := by
    intro h0
    rw [Finset.card_eq_zero] at h0
    have h1 : N = 1 := by
      conv_lhs => rw [Nat.prod_primeFactors_pow_factorization ho.pos.ne']
      rw [h0, Finset.prod_empty]
    have := hh.1
    omega
  have h1 : N.primeFactors.card ≠ 1 := by
    intro h1
    obtain ⟨p, hp_eq⟩ := Finset.card_eq_one.mp h1
    have hp_mem : p ∈ N.primeFactors := by rw [hp_eq]; simp
    have hp := Nat.prime_of_mem_primeFactors hp_mem
    have he := hp.factorization_pos_of_dvd ho.pos.ne' (Nat.dvd_of_mem_primeFactors hp_mem)
    have hN_eq : N = p ^ N.factorization p := by
      conv_lhs => rw [Nat.prod_primeFactors_pow_factorization ho.pos.ne']
      rw [hp_eq, Finset.prod_singleton]
    exact prime_pow_not_oreHarmonic hp he (hN_eq ▸ hh)
  have h2 : N.primeFactors.card = 2 := by omega
  exact not_odd_oreHarmonic_primeFactors_card_eq_two ho hh h2

end OddPerfect
