module

public import OddPerfect.ZelinskySlope
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Cyclotomic Quadratic Root-Slot Slope Upgrade

Upgrades Ochem–Rao's linear slope `18 * ω(N) ≤ 7 * Ω(N) + 31` unconditionally to:
- `8 * ω(N) ≤ 3 * Ω(N) + 7` when `¬ 3 ∣ N`, and
- `21 * ω(N) ≤ 8 * Ω(N) + 39` for all odd perfect numbers,

by counting upward cyclotomic root slots `u < w` (`w ∣ u^2 + u + 1`) on `squareSources N`,
using the fact that `x^2 + x + 1 ≡ 0 [MOD w]` has at most two solutions modulo any prime `w`
and that for `u^2 + u + 1 = w` prime the two roots in `Finset.range w` are `{u, u^2}`.
-/

public section

namespace OddPerfect

open ArithmeticFunction

/-! ## 1. Quadratic Root Cap Modulo a Prime -/

/-- The congruence `x ^ 2 + x + 1 ≡ 0 [MOD w]` has at most two solutions in `Finset.range w`
for any prime `w`. -/
theorem card_range_dvd_sq_add_self_add_one_le_two {w : ℕ} (hw : w.Prime) :
    ((Finset.range w).filter (fun x => w ∣ x ^ 2 + x + 1)).card ≤ 2 := by
  let S := (Finset.range w).filter (fun x => w ∣ x ^ 2 + x + 1)
  change S.card ≤ 2
  rcases S.eq_empty_or_nonempty with h_empty | ⟨a, ha⟩
  · rw [h_empty]
    simp
  have : Fact w.Prime := ⟨hw⟩
  have hS_eq : S.card = (S.erase a).card + 1 := (Finset.card_erase_add_one ha).symm
  have ha_mem := Finset.mem_filter.mp ha
  have ha_lt : a < w := Finset.mem_range.mp ha_mem.1
  have ha_z : (a : ZMod w) ^ 2 + (a : ZMod w) + 1 = 0 := by
    have h0 := (ZMod.natCast_eq_zero_iff (a ^ 2 + a + 1) w).mpr ha_mem.2
    push_cast at h0
    exact h0
  have herase : (S.erase a).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro b hb c hc
    have hroot : ∀ x ∈ S.erase a, (x : ZMod w) = -(a : ZMod w) - 1 := by
      intro x hx
      obtain ⟨hx_ne, hx_mem⟩ := Finset.mem_erase.mp hx
      have hx_f := Finset.mem_filter.mp hx_mem
      have hx_lt : x < w := Finset.mem_range.mp hx_f.1
      have hx_z : (x : ZMod w) ^ 2 + (x : ZMod w) + 1 = 0 := by
        have h0 := (ZMod.natCast_eq_zero_iff (x ^ 2 + x + 1) w).mpr hx_f.2
        push_cast at h0
        exact h0
      have hprod : ((x : ZMod w) - (a : ZMod w)) * ((x : ZMod w) + (a : ZMod w) + 1) = 0 := by
        calc
          ((x : ZMod w) - (a : ZMod w)) * ((x : ZMod w) + (a : ZMod w) + 1)
              = ((x : ZMod w) ^ 2 + (x : ZMod w) + 1) - ((a : ZMod w) ^ 2 + (a : ZMod w) + 1) := by
                  ring
          _ = 0 - 0 := by rw [hx_z, ha_z]
          _ = 0 := sub_zero 0
      have hne_z : (x : ZMod w) - (a : ZMod w) ≠ 0 := by
        intro hsub
        have heq_z : (x : ZMod w) = (a : ZMod w) := sub_eq_zero.mp hsub
        have hval := congrArg ZMod.val heq_z
        rw [ZMod.val_natCast_of_lt hx_lt, ZMod.val_natCast_of_lt ha_lt] at hval
        exact hx_ne hval
      have hsum_z : (x : ZMod w) + (a : ZMod w) + 1 = 0 := (mul_eq_zero.mp hprod).resolve_left hne_z
      calc
        (x : ZMod w) = ((x : ZMod w) + (a : ZMod w) + 1) - (a : ZMod w) - 1 := by ring
        _ = 0 - (a : ZMod w) - 1 := by rw [hsum_z]
        _ = -(a : ZMod w) - 1 := by ring
    have hbc_z : (b : ZMod w) = (c : ZMod w) := (hroot b hb).trans (hroot c hc).symm
    have hb_lt : b < w := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_erase.mp hb).2).1
    have hc_lt : c < w := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_erase.mp hc).2).1
    have hval := congrArg ZMod.val hbc_z
    rwa [ZMod.val_natCast_of_lt hb_lt, ZMod.val_natCast_of_lt hc_lt] at hval
  omega

/-! ## 2. Partition of `squareSources` and Local Upward-Root Helpers -/

/-- Non-3 primes of exact exponent two that are not congruent to `1` modulo `3`. -/
@[expose] def squareSourcesTwo (N : ℕ) : Finset ℕ :=
  (squareSources N).filter fun q => q % 3 ≠ 1

theorem squareSources_eq_union_one_two (N : ℕ) :
    squareSources N = squareSourcesOne N ∪ squareSourcesTwo N := by
  ext q
  simp only [squareSourcesOne, squareSourcesTwo, Finset.mem_union, Finset.mem_filter]
  by_cases h : q % 3 = 1 <;> tauto

theorem squareSourcesOne_disjoint_two (N : ℕ) :
    Disjoint (squareSourcesOne N) (squareSourcesTwo N) := by
  apply Finset.disjoint_left.mpr
  intro q h1 h2
  exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2

private lemma normalizedSquareSum_dvd_sq_add_self_add_one (v : ℕ) :
    normalizedSquareSum v ∣ v ^ 2 + v + 1 := by
  by_cases hv : v % 3 = 1
  · obtain ⟨k, rfl⟩ : ∃ k, v = 3 * k + 1 := ⟨v / 3, by omega⟩
    have hnorm : normalizedSquareSum (3 * k + 1) = 3 * k ^ 2 + 3 * k + 1 := by
      rw [normalizedSquareSum, ite_eq_left (show (3 * k + 1) % 3 = 1 by omega)]
      rw [show (3 * k + 1) ^ 2 + (3 * k + 1) + 1 = 3 * (3 * k ^ 2 + 3 * k + 1) by ring]
      simp
    rw [hnorm]
    refine ⟨3, ?_⟩
    ring
  · simp [normalizedSquareSum, hv]

private lemma le_pow_cardFactors_of_primeFactors_le {M u : ℕ} (hM : M ≠ 0)
    (h : ∀ w ∈ M.primeFactors, w ≤ u) : M ≤ u ^ cardFactors M := by
  calc
    M = ∏ w ∈ M.primeFactors, w ^ M.factorization w := Nat.prod_primeFactors_pow_factorization hM
    _ ≤ ∏ w ∈ M.primeFactors, u ^ M.factorization w :=
        Finset.prod_le_prod fun w hw => Nat.pow_le_pow_left (h w hw) _
    _ = u ^ ∑ w ∈ M.primeFactors, M.factorization w := Finset.prod_pow_eq_pow_sum _ _ _
    _ = u ^ cardFactors M := by
        rw [cardFactors_eq_sum_factorization]
        rfl

/-- If `u ∈ squareSourcesTwo N` has `w = normalizedSquareSum u = u^2 + u + 1` prime, then `u`
is the unique prime `< w` with `w ∣ normalizedSquareSum v`. -/
theorem squareSourcesTwo_prime_root_unique {u v : ℕ} (hu : u.Prime) (hu3 : 3 < u)
    (hu_mod : u % 3 ≠ 1) (hw : (normalizedSquareSum u).Prime)
    (hv : v.Prime) (hvw : v < normalizedSquareSum u) (hdvd : normalizedSquareSum u ∣ normalizedSquareSum v) :
    v = u := by
  let w := normalizedSquareSum u
  have hw_eq : w = u ^ 2 + u + 1 := by simp [w, normalizedSquareSum, hu_mod]
  have hu_lt_sq : u < u ^ 2 := by nlinarith [hu.one_lt]
  have hsq_lt_w : u ^ 2 < w := by rw [hw_eq]; omega
  have hu_lt_w : u < w := hu_lt_sq.trans hsq_lt_w
  have hw_dvd_sq : w ∣ (u ^ 2) ^ 2 + u ^ 2 + 1 := by
    have hle : u ≤ u ^ 2 := hu_lt_sq.le
    refine ⟨u ^ 2 - u + 1, ?_⟩
    rw [hw_eq]
    zify [hle]
    ring
  have hsub : ({u, u ^ 2} : Finset ℕ) ⊆ (Finset.range w).filter (fun x => w ∣ x ^ 2 + x + 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hu_lt_w, hw_eq ▸ dvd_rfl⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hsq_lt_w, hw_dvd_sq⟩
  have hcard2 : ({u, u ^ 2} : Finset ℕ).card = 2 := Finset.card_pair hu_lt_sq.ne
  have heq : ({u, u ^ 2} : Finset ℕ) = (Finset.range w).filter (fun x => w ∣ x ^ 2 + x + 1) :=
    Finset.eq_of_subset_of_card_le hsub ((card_range_dvd_sq_add_self_add_one_le_two hw).trans hcard2.ge)
  have hv_mem : v ∈ (Finset.range w).filter (fun x => w ∣ x ^ 2 + x + 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hvw, hdvd.trans (normalizedSquareSum_dvd_sq_add_self_add_one v)⟩
  rw [← heq] at hv_mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv_mem
  rcases hv_mem with rfl | rfl
  · rfl
  · exfalso
    have hdiv : u ∣ u ^ 2 := dvd_pow_self u (by decide)
    rcases hv.eq_one_or_self_of_dvd u hdiv with h1 | hself
    · exact hu.ne_one h1
    · exact hu_lt_sq.ne hself

/-- If `u ∈ squareSourcesTwo N` has `cardFactors (normalizedSquareSum u) = 2`, then
`normalizedSquareSum u` has a prime factor strictly greater than `u`. -/
theorem squareSourcesTwo_semiprime_exists_gt {u : ℕ} (hu_mod : u % 3 ≠ 1)
    (hcard : cardFactors (normalizedSquareSum u) = 2) :
    ∃ w ∈ (normalizedSquareSum u).primeFactors, u < w := by
  have hnorm : normalizedSquareSum u = u ^ 2 + u + 1 := by simp [normalizedSquareSum, hu_mod]
  by_contra! hle
  have hM_ne : normalizedSquareSum u ≠ 0 := by rw [hnorm]; positivity
  have hbound := le_pow_cardFactors_of_primeFactors_le hM_ne hle
  rw [hcard, hnorm] at hbound
  omega

/-- If `u` is a prime `> 3` with `u % 3 = 1`, then `u < normalizedSquareSum u`. -/
theorem squareSourcesOne_prime_gt {u : ℕ} (hu3 : 3 < u) (hu_mod : u % 3 = 1) :
    u < normalizedSquareSum u := by
  obtain ⟨k, rfl⟩ : ∃ k, u = 3 * k + 1 := ⟨u / 3, by omega⟩
  have hnorm : normalizedSquareSum (3 * k + 1) = 3 * k ^ 2 + 3 * k + 1 := by
    rw [normalizedSquareSum, ite_eq_left (show (3 * k + 1) % 3 = 1 by omega)]
    rw [show (3 * k + 1) ^ 2 + (3 * k + 1) + 1 = 3 * (3 * k ^ 2 + 3 * k + 1) by ring]
    simp
  rw [hnorm]
  nlinarith

/-! ## 3. Cyclotomic Root-Slot Incidence Bound -/

/-- Cyclotomic root-slot incidence inequality on `squareSources N`, sharpening Ochem–Rao's
`2 * |S| ≤ ...` to `3 * |S₂₂| + 2 * |S₂₁| ≤ ...`. -/
theorem squareSources_root_slot_incidence {N p : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) (_hp4 : p % 4 = 1) (_he : N.factorization p % 4 = 1)
    (hev : ∀ q : ℕ, q ≠ p → Even (N.factorization q)) :
    3 * (squareSourcesTwo N).card + 2 * (squareSourcesOne N).card ≤
      2 + N.factorization p + 4 * (squareSourcesOne N).card +
        2 * (largeSources N p).card + ∑ q ∈ largeSources N p, N.factorization q := by
  let T := insert p (squareSourcesOne N ∪ largeSources N p)
  let S := squareSources N
  let S₁ := squareSourcesOne N
  let S₂ := squareSourcesTwo N
  have hs : S ⊆ N.primeFactors := Finset.filter_subset _ _
  have source {u : ℕ} (hu : u ∈ S) : u.Prime ∧ 3 < u ∧ N.factorization u = 2 := by
    obtain ⟨hmem, h3, hex⟩ := Finset.mem_filter.mp hu
    have hprime := Nat.prime_of_mem_primeFactors hmem
    have hodd := Nat.odd_iff.mp (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hmem))
    have := hprime.two_le
    exact ⟨hprime, by omega, hex⟩
  have localDiv (u : ℕ) (hu : u ∈ S) :
      normalizedSquareSum u ∣ sigma 1 (u ^ N.factorization u) := by
    obtain ⟨hu', h3, h2⟩ := source hu
    rw [h2]
    exact normalizedSquareSum_dvd_sigma hu' h3
  have cover (u : ℕ) (hu : u ∈ S) : (normalizedSquareSum u).primeFactors ⊆ T := by
    intro r hr
    obtain ⟨hup, hu3, he2⟩ := source hu
    obtain ⟨hrp, hrd, _⟩ := Nat.mem_primeFactors.mp hr
    have hd := hrd.trans (localDiv u hu)
    have hpoly := hd
    rw [he2, sigma_one_apply_prime_pow hup] at hpoly
    have hmod := (prime_dvd_sq_add_self_add_one hrp (by
      simpa [Finset.sum_range_succ, add_comm, add_assoc, add_left_comm] using hpoly)).resolve_left
      (fun h => three_not_dvd_normalizedSquareSum hup hu3 (h ▸ hrd))
    have hodd := hrp.odd_of_ne_two (by omega)
    have hrN : r ∣ N := by
      apply dvd_perfect_of_exact_prime_pow hN hup (Nat.ordProj_dvd _ _) _ hrp hodd
      · rwa [← sigma_one_apply]
      · rw [hup.pow_dvd_iff_le_factorization hN.2.ne']
        omega
    have hmem := Nat.mem_primeFactors.mpr ⟨hrp, hrN, hN.2.ne'⟩
    by_cases hsp : r = p
    · exact Finset.mem_insert.mpr (Or.inl hsp)
    apply Finset.mem_insert_of_mem
    have hr3 : r ≠ 3 := by omega
    by_cases hex : N.factorization r = 2
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hmem, hr3, hex⟩, hmod⟩)
    · have hpos := (hrp.dvd_iff_one_le_factorization hN.2.ne').mp hrN
      obtain ⟨k, hk⟩ := hev r hsp
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hmem, hr3, hsp, by omega⟩)
  have targetMem : T ⊆ N.primeFactors := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | h
    · exact hp
    · rcases Finset.mem_union.mp h with h | h
      · exact hs (Finset.mem_filter.mp h).1
      · exact (Finset.mem_filter.mp h).1
  have upper := sum_cardFactors_le_target_exponents hN S T normalizedSquareSum hs localDiv cover
    (fun _ hr => ⟨Nat.prime_of_mem_primeFactors (targetMem hr),
      ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors (targetMem hr))⟩)
  have hdis_SL : Disjoint S₁ (largeSources N p) := by
    apply Finset.disjoint_left.mpr
    intro r hr hl
    have := (source (Finset.mem_filter.mp hr).1).2.2
    have := (Finset.mem_filter.mp hl).2.2.2
    omega
  have hnot_p : p ∉ S₁ ∪ largeSources N p := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · have := (source (Finset.mem_filter.mp h).1).2.2
      omega
    · exact (Finset.mem_filter.mp h).2.2.1 rfl
  have htcard : T.card = S₁.card + (largeSources N p).card + 1 := by
    dsimp only [T]
    rw [Finset.card_insert_of_notMem hnot_p, Finset.card_union_of_disjoint hdis_SL]
  have hsum_S1 : ∑ r ∈ S₁, N.factorization r = S₁.card * 2 := by
    calc
      _ = ∑ _r ∈ S₁, (2 : ℕ) := Finset.sum_congr rfl fun _ hr =>
        (source (Finset.mem_filter.mp hr).1).2.2
      _ = _ := by simp
  dsimp only [T] at upper
  rw [Finset.sum_insert hnot_p, Finset.sum_union hdis_SL, hsum_S1] at upper
  change ∑ u ∈ S, cardFactors (normalizedSquareSum u) ≤
      N.factorization p + (S₁.card * 2 + ∑ q ∈ largeSources N p, N.factorization q) at upper
  -- Partition S₂ into Ω = 1, Ω = 2, Ω ≥ 3, and S₁ into Ω = 1, Ω ≥ 2.
  let A₁₂ := S₂.filter fun u => (normalizedSquareSum u).Prime
  let A₂₂ := S₂.filter fun u => cardFactors (normalizedSquareSum u) = 2
  let A₃₂ := S₂.filter fun u => 3 ≤ cardFactors (normalizedSquareSum u)
  let A₁₁ := S₁.filter fun u => (normalizedSquareSum u).Prime
  let A₂₁ := S₁.filter fun u => 2 ≤ cardFactors (normalizedSquareSum u)
  have hS₂_part : S₂ = A₁₂ ∪ A₂₂ ∪ A₃₂ := by
    ext u
    simp only [A₁₂, A₂₂, A₃₂, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hu
      have huS : u ∈ S := (Finset.mem_filter.mp hu).1
      obtain ⟨hup, hu3, _⟩ := source huS
      have hpos := cardFactors_pos_iff_one_lt.mpr (normalizedSquareSum_one_lt hup hu3)
      by_cases h1 : cardFactors (normalizedSquareSum u) = 1
      · exact Or.inl (Or.inl ⟨hu, cardFactors_eq_one_iff_prime.mp h1⟩)
      · by_cases h2 : cardFactors (normalizedSquareSum u) = 2
        · exact Or.inl (Or.inr ⟨hu, h2⟩)
        · exact Or.inr ⟨hu, by omega⟩
    · rintro ((⟨hu, _⟩ | ⟨hu, _⟩) | ⟨hu, _⟩) <;> exact hu
  have hdis_12_22 : Disjoint A₁₂ A₂₂ := by
    apply Finset.disjoint_left.mpr
    intro u h1 h2
    have hp1 := cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp h1).2
    have hp2 := (Finset.mem_filter.mp h2).2
    omega
  have hdis_1222_32 : Disjoint (A₁₂ ∪ A₂₂) A₃₂ := by
    apply Finset.disjoint_left.mpr
    intro u h12 h3
    have hge3 := (Finset.mem_filter.mp h3).2
    rcases Finset.mem_union.mp h12 with h1 | h2
    · have hp1 := cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp h1).2
      omega
    · have hp2 := (Finset.mem_filter.mp h2).2
      omega
  have hS₂_card : S₂.card = A₁₂.card + A₂₂.card + A₃₂.card := by
    rw [hS₂_part, Finset.card_union_of_disjoint hdis_1222_32, Finset.card_union_of_disjoint hdis_12_22]
  have hS₁_part : S₁ = A₁₁ ∪ A₂₁ := by
    ext u
    simp only [A₁₁, A₂₁, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hu
      have huS : u ∈ S := (Finset.mem_filter.mp hu).1
      obtain ⟨hup, hu3, _⟩ := source huS
      have hpos := cardFactors_pos_iff_one_lt.mpr (normalizedSquareSum_one_lt hup hu3)
      by_cases h1 : cardFactors (normalizedSquareSum u) = 1
      · exact Or.inl ⟨hu, cardFactors_eq_one_iff_prime.mp h1⟩
      · exact Or.inr ⟨hu, by omega⟩
    · rintro (⟨hu, _⟩ | ⟨hu, _⟩) <;> exact hu
  have hdis_11_21 : Disjoint A₁₁ A₂₁ := by
    apply Finset.disjoint_left.mpr
    intro u h1 h2
    have hp1 := cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp h1).2
    have hge2 := (Finset.mem_filter.mp h2).2
    omega
  have hS₁_card : S₁.card = A₁₁.card + A₂₁.card := by
    rw [hS₁_part, Finset.card_union_of_disjoint hdis_11_21]
  -- Lower bound on ∑ u ∈ S, cardFactors (normalizedSquareSum u).
  have hsum_S₂ :
      A₁₂.card + 2 * A₂₂.card + 3 * A₃₂.card ≤ ∑ u ∈ S₂, cardFactors (normalizedSquareSum u) := by
    rw [hS₂_part, Finset.sum_union hdis_1222_32, Finset.sum_union hdis_12_22]
    have h1 : A₁₂.card ≤ ∑ u ∈ A₁₂, cardFactors (normalizedSquareSum u) := by
      calc
        A₁₂.card = ∑ _u ∈ A₁₂, 1 := by simp
        _ ≤ ∑ u ∈ A₁₂, cardFactors (normalizedSquareSum u) := by
            refine Finset.sum_le_sum fun u hu => ?_
            have hp_u := (Finset.mem_filter.mp hu).2
            rw [cardFactors_eq_one_iff_prime.mpr hp_u]
    have h2 : 2 * A₂₂.card ≤ ∑ u ∈ A₂₂, cardFactors (normalizedSquareSum u) := by
      calc
        2 * A₂₂.card = ∑ _u ∈ A₂₂, 2 := by simp [Nat.mul_comm]
        _ ≤ ∑ u ∈ A₂₂, cardFactors (normalizedSquareSum u) := by
            refine Finset.sum_le_sum fun u hu => ?_
            rw [(Finset.mem_filter.mp hu).2]
    have h3 : 3 * A₃₂.card ≤ ∑ u ∈ A₃₂, cardFactors (normalizedSquareSum u) := by
      calc
        3 * A₃₂.card = ∑ _u ∈ A₃₂, 3 := by simp [Nat.mul_comm]
        _ ≤ ∑ u ∈ A₃₂, cardFactors (normalizedSquareSum u) :=
            Finset.sum_le_sum fun u hu => (Finset.mem_filter.mp hu).2
    omega
  have hsum_S₁ :
      A₁₁.card + 2 * A₂₁.card ≤ ∑ u ∈ S₁, cardFactors (normalizedSquareSum u) := by
    rw [hS₁_part, Finset.sum_union hdis_11_21]
    have h1 : A₁₁.card ≤ ∑ u ∈ A₁₁, cardFactors (normalizedSquareSum u) := by
      calc
        A₁₁.card = ∑ _u ∈ A₁₁, 1 := by simp
        _ ≤ ∑ u ∈ A₁₁, cardFactors (normalizedSquareSum u) := by
            refine Finset.sum_le_sum fun u hu => ?_
            have hp_u := (Finset.mem_filter.mp hu).2
            rw [cardFactors_eq_one_iff_prime.mpr hp_u]
    have h2 : 2 * A₂₁.card ≤ ∑ u ∈ A₂₁, cardFactors (normalizedSquareSum u) := by
      calc
        2 * A₂₁.card = ∑ _u ∈ A₂₁, 2 := by simp [Nat.mul_comm]
        _ ≤ ∑ u ∈ A₂₁, cardFactors (normalizedSquareSum u) :=
            Finset.sum_le_sum fun u hu => (Finset.mem_filter.mp hu).2
    omega
  have hsum_S :
      ∑ u ∈ S, cardFactors (normalizedSquareSum u) =
        ∑ u ∈ S₁, cardFactors (normalizedSquareSum u) + ∑ u ∈ S₂, cardFactors (normalizedSquareSum u) := by
    change ∑ u ∈ squareSources N, _ = _
    rw [squareSources_eq_union_one_two N, Finset.sum_union (squareSourcesOne_disjoint_two N)]
  -- Upward incidence graph Up ⊆ S ×ˢ T.
  let Up := (S ×ˢ T).filter fun uw => uw.1 < uw.2 ∧ uw.2 ∣ normalizedSquareSum uw.1
  let U_up := A₁₂ ∪ A₁₁ ∪ A₂₂
  have hdis_12_11 : Disjoint A₁₂ A₁₁ :=
    Finset.disjoint_left.mpr fun u h1 h2 =>
      (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2
        (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2
  have hdis_1211_22 : Disjoint (A₁₂ ∪ A₁₁) A₂₂ := by
    apply Finset.disjoint_left.mpr
    intro u h12 h22
    rcases Finset.mem_union.mp h12 with h1 | h1
    · exact Finset.disjoint_left.mp hdis_12_22 h1 h22
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp h22).1).2
        (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2
  have hU_up_card : U_up.card = A₁₂.card + A₁₁.card + A₂₂.card := by
    dsimp only [U_up]
    rw [Finset.card_union_of_disjoint hdis_1211_22, Finset.card_union_of_disjoint hdis_12_11]
  have hU_up_sub : U_up ⊆ Up.image Prod.fst := by
    intro u hu
    rw [Finset.mem_image]
    rcases Finset.mem_union.mp hu with h12_11 | hu22
    · rcases Finset.mem_union.mp h12_11 with hu12 | hu11
      · obtain ⟨huS2, hwp⟩ := Finset.mem_filter.mp hu12
        obtain ⟨huS, hu_mod⟩ := Finset.mem_filter.mp huS2
        obtain ⟨hup, hu3, _⟩ := source huS
        let w := normalizedSquareSum u
        have hwT : w ∈ T := cover u huS (Nat.mem_primeFactors.mpr ⟨hwp, dvd_rfl, hwp.ne_zero⟩)
        have hlt : u < w := by
          have hnorm : w = u ^ 2 + u + 1 := by simp [w, normalizedSquareSum, hu_mod]
          rw [hnorm]
          nlinarith [hup.one_lt]
        exact ⟨(u, w), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huS, hwT⟩, hlt, dvd_rfl⟩, rfl⟩
      · obtain ⟨huS1, hwp⟩ := Finset.mem_filter.mp hu11
        obtain ⟨huS, hu_mod⟩ := Finset.mem_filter.mp huS1
        obtain ⟨_, hu3, _⟩ := source huS
        let w := normalizedSquareSum u
        have hwT : w ∈ T := cover u huS (Nat.mem_primeFactors.mpr ⟨hwp, dvd_rfl, hwp.ne_zero⟩)
        have hlt : u < w := squareSourcesOne_prime_gt hu3 hu_mod
        exact ⟨(u, w), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huS, hwT⟩, hlt, dvd_rfl⟩, rfl⟩
    · obtain ⟨huS2, hcard2⟩ := Finset.mem_filter.mp hu22
      obtain ⟨huS, hu_mod⟩ := Finset.mem_filter.mp huS2
      obtain ⟨w, hw_pf, huw⟩ := squareSourcesTwo_semiprime_exists_gt hu_mod hcard2
      have hwT : w ∈ T := cover u huS hw_pf
      have hwdvd : w ∣ normalizedSquareSum u := Nat.dvd_of_mem_primeFactors hw_pf
      exact ⟨(u, w), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huS, hwT⟩, huw, hwdvd⟩, rfl⟩
  have hUp_lower : A₁₂.card + A₁₁.card + A₂₂.card ≤ Up.card := by
    rw [← hU_up_card]
    exact (Finset.card_le_card hU_up_sub).trans Finset.card_image_le
  -- Upper bound on Up.card by fibering over T.
  let T₁₂ := A₁₂.image normalizedSquareSum
  have hT₁₂_sub : T₁₂ ⊆ T := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨huS2, hwp⟩ := Finset.mem_filter.mp hu
    have huS : u ∈ S := (Finset.mem_filter.mp huS2).1
    exact cover u huS (Nat.mem_primeFactors.mpr ⟨hwp, dvd_rfl, hwp.ne_zero⟩)
  have hT₁₂_card : T₁₂.card = A₁₂.card := by
    apply Finset.card_image_of_injOn
    intro u hu v hv heq
    obtain ⟨hup, hu3, _⟩ := source (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).1
    obtain ⟨hvp, hv3, _⟩ := source (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).1
    exact normalizedSquareSum_injective hup hu3 hvp hv3 heq
  have hUp_fiber : Up.card = ∑ w ∈ T, (Up.filter fun uw => uw.2 = w).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro uw huw
    exact (Finset.mem_product.mp (Finset.mem_filter.mp huw).1).2
  have hfiber_le (w : ℕ) (hwT : w ∈ T) :
      (Up.filter fun uw => uw.2 = w).card ≤
        (S.filter fun v => v < w ∧ w ∣ normalizedSquareSum v).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro uw huw
      obtain ⟨huw_Up, rfl⟩ := Finset.mem_filter.mp huw
      obtain ⟨huw_prod, hlt, hdvd⟩ := Finset.mem_filter.mp huw_Up
      exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp huw_prod).1, hlt, hdvd⟩
    · intro x hx y hy hxy
      obtain ⟨_, hx2⟩ := Finset.mem_filter.mp hx
      obtain ⟨_, hy2⟩ := Finset.mem_filter.mp hy
      exact Prod.ext hxy (hx2.trans hy2.symm)
  have hfiber_T₁₂ : ∀ w ∈ T₁₂, (Up.filter fun uw => uw.2 = w).card ≤ 1 := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨huS2, hwp⟩ := Finset.mem_filter.mp hu
    obtain ⟨huS, hu_mod⟩ := Finset.mem_filter.mp huS2
    obtain ⟨hup, hu3, _⟩ := source huS
    have hsub :
        (S.filter fun v => v < normalizedSquareSum u ∧ normalizedSquareSum u ∣ normalizedSquareSum v) ⊆
          {u} := by
      intro v hv
      obtain ⟨hvS, hvw, hdvd⟩ := Finset.mem_filter.mp hv
      have hvp := (source hvS).1
      rw [Finset.mem_singleton]
      exact squareSourcesTwo_prime_root_unique hup hu3 hu_mod hwp hvp hvw hdvd
    exact (hfiber_le _ (hT₁₂_sub hw)).trans ((Finset.card_le_card hsub).trans (by simp))
  have hfiber_other : ∀ w ∈ T \ T₁₂, (Up.filter fun uw => uw.2 = w).card ≤ 2 := by
    intro w hw
    have hwT : w ∈ T := (Finset.mem_sdiff.mp hw).1
    have hwp : w.Prime := Nat.prime_of_mem_primeFactors (targetMem hwT)
    have hsub :
        (S.filter fun v => v < w ∧ w ∣ normalizedSquareSum v) ⊆
          (Finset.range w).filter (fun x => w ∣ x ^ 2 + x + 1) := by
      intro v hv
      obtain ⟨_, hvw, hdvd⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hvw, hdvd.trans (normalizedSquareSum_dvd_sq_add_self_add_one v)⟩
    exact (hfiber_le w hwT).trans
      ((Finset.card_le_card hsub).trans (card_range_dvd_sq_add_self_add_one_le_two hwp))
  have hUp_upper : Up.card + A₁₂.card ≤ 2 * T.card := by
    have hsdiff := Finset.sum_sdiff hT₁₂_sub (f := fun w => (Up.filter fun uw => uw.2 = w).card)
    have h1 : ∑ w ∈ T₁₂, (Up.filter fun uw => uw.2 = w).card ≤ T₁₂.card := by
      calc
        _ ≤ ∑ _w ∈ T₁₂, 1 := Finset.sum_le_sum hfiber_T₁₂
        _ = T₁₂.card := by simp
    have h2 : ∑ w ∈ T \ T₁₂, (Up.filter fun uw => uw.2 = w).card ≤ 2 * (T \ T₁₂).card := by
      calc
        _ ≤ ∑ _w ∈ T \ T₁₂, 2 := Finset.sum_le_sum hfiber_other
        _ = 2 * (T \ T₁₂).card := by simp [Nat.mul_comm]
    have hcard_sdiff : T₁₂.card + (T \ T₁₂).card = T.card := by
      rw [← Finset.card_union_of_disjoint disjoint_sdiff_self_right,
        Finset.union_sdiff_of_subset hT₁₂_sub]
    omega
  -- Combine all inequalities.
  change 3 * S₂.card + 2 * S₁.card ≤
      2 + N.factorization p + 4 * S₁.card + 2 * (largeSources N p).card +
        ∑ q ∈ largeSources N p, N.factorization q
  omega

/-! ## 4. Global Linear Slope Upgrades and Logarithmic Pinches -/

/-- Sharpened cyclotomic root-slot linear slope retaining Euler exponent slack, `3`-exponent
slack, and higher-exponent slack. -/
theorem cyclotomic_slope_with_excess_slack {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    ∃ q ∈ N.primeFactors, q % 4 = 1 ∧ N.factorization q % 4 = 1 ∧
      (∀ r, r ≠ q → Even (N.factorization r)) ∧
      (3 ∣ N → 21 * N.primeFactors.card + 6 * (N.factorization q - 1) +
        8 * (N.factorization 3 - (squareSourcesOne N).card) +
        6 * (∑ r ∈ largeSources N q, (N.factorization r - 4)) ≤
          8 * N.primeFactorsList.length + 39) ∧
      (¬ 3 ∣ N → 8 * N.primeFactors.card + 2 * (N.factorization q - 1) +
        2 * (∑ r ∈ largeSources N q, (N.factorization r - 4)) ≤
          3 * N.primeFactorsList.length + 7) := by
  obtain ⟨q, hq, hq4, he, hev⟩ := euler_exponents ho hN
  refine ⟨q, hq, hq4, he, hev, ?_⟩
  have hincA := ochem_rao_incidence ho hN hq hq4 he hev
  have hincB := squareSources_root_slot_incidence ho hN hq hq4 he hev
  let S := (N.primeFactors.erase q).erase 3
  have hpos {r : ℕ} (hr : r ∈ N.primeFactors) : 0 < N.factorization r :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
  have hparts : S = squareSources N ∪ largeSources N q := by
    ext r
    simp only [S, Finset.mem_erase, squareSources, largeSources, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hr3, hrq, hr⟩
      obtain ⟨k, hk⟩ := hev r hrq
      have := hpos hr
      by_cases htwo : N.factorization r = 2
      · exact Or.inl ⟨hr, hr3, htwo⟩
      · exact Or.inr ⟨hr, hr3, hrq, by omega⟩
    · rintro (⟨hr, hr3, htwo⟩ | ⟨hr, hr3, hrq, _⟩)
      · exact ⟨hr3, fun h => by subst r; omega, hr⟩
      · exact ⟨hr3, hrq, hr⟩
  have hdis : Disjoint (squareSources N) (largeSources N q) := by
    apply Finset.disjoint_left.mpr
    intro r hs hl
    have htwo := (Finset.mem_filter.mp hs).2.2
    have hlarge := (Finset.mem_filter.mp hl).2.2.2
    omega
  have hcard : S.card = (squareSources N).card + (largeSources N q).card := by
    rw [hparts, Finset.card_union_of_disjoint hdis]
  have hsq_card : (squareSources N).card = (squareSourcesOne N).card + (squareSourcesTwo N).card := by
    rw [squareSources_eq_union_one_two N, Finset.card_union_of_disjoint (squareSourcesOne_disjoint_two N)]
  have hsum : (∑ r ∈ S, N.factorization r) =
      2 * (squareSources N).card + ∑ r ∈ largeSources N q, N.factorization r := by
    rw [hparts, Finset.sum_union hdis]
    congr 1
    calc
      _ = ∑ _r ∈ squareSources N, (2 : ℕ) :=
        Finset.sum_congr rfl fun _ hr => (Finset.mem_filter.mp hr).2.2
      _ = _ := by simp [Nat.mul_comm]
  have hlarge_eq : (∑ r ∈ largeSources N q, N.factorization r) =
      4 * (largeSources N q).card + ∑ r ∈ largeSources N q, (N.factorization r - 4) := by
    have hadd : (∑ r ∈ largeSources N q, N.factorization r) =
        ∑ r ∈ largeSources N q, (4 + (N.factorization r - 4)) := by
      refine Finset.sum_congr rfl fun r hr => ?_
      have hge4 : 4 ≤ N.factorization r := (Finset.mem_filter.mp hr).2.2.2
      omega
    rw [hadd, Finset.sum_add_distrib]
    simp [Nat.mul_comm]
  have htot : N.primeFactorsList.length =
      N.factorization q + ∑ r ∈ N.primeFactors.erase q, N.factorization r := by
    rw [← cardFactors_apply, cardFactors_eq_sum_factorization]
    exact (Finset.add_sum_erase N.primeFactors _ hq).symm
  have hqcount := Finset.card_erase_add_one hq
  have hbound := squareSourcesOne_card_le_three_exponent hN
  have hq_pos := hpos hq
  by_cases h3 : 3 ∈ N.primeFactors
  · have h3q : 3 ≠ q := by omega
    have h3mem := Finset.mem_erase.mpr ⟨h3q, h3⟩
    have h3card : S.card + 1 = (N.primeFactors.erase q).card := Finset.card_erase_add_one h3mem
    have h3sum : N.factorization 3 + (∑ r ∈ S, N.factorization r) =
        ∑ r ∈ N.primeFactors.erase q, N.factorization r :=
      Finset.add_sum_erase _ _ h3mem
    exact ⟨fun _ => by omega, fun hd => (hd (Nat.dvd_of_mem_primeFactors h3)).elim⟩
  · have h3zero : N.factorization 3 = 0 := Finsupp.notMem_support_iff.mp h3
    have h3erase : S = N.primeFactors.erase q :=
      Finset.erase_eq_of_notMem fun h => h3 (Finset.mem_of_mem_erase h)
    rw [← h3erase] at htot hqcount
    exact ⟨fun hd => (h3 (Nat.mem_primeFactors.mpr ⟨by decide, hd, hN.2.ne'⟩)).elim,
      fun _ => by omega⟩

/-- Upgraded linear slope for `3`-free odd perfect numbers: `8 * ω(N) ≤ 3 * Ω(N) + 7`. -/
theorem cyclotomic_slope_three_free {N : ℕ} (ho : Odd N) (hN : N.Perfect) (h3 : ¬ 3 ∣ N) :
    8 * N.primeFactors.card ≤ 3 * N.primeFactorsList.length + 7 := by
  obtain ⟨_, _, _, _, _, _, hno3⟩ := cyclotomic_slope_with_excess_slack ho hN
  have h := hno3 h3
  omega

/-- Unconditional upgraded linear slope for all odd perfect numbers:
`21 * ω(N) ≤ 8 * Ω(N) + 39`. -/
theorem cyclotomic_prime_factor_count {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    21 * N.primeFactors.card ≤ 8 * N.primeFactorsList.length + 39 := by
  obtain ⟨_, _, _, _, _, hdiv3, hno3⟩ := cyclotomic_slope_with_excess_slack ho hN
  by_cases h3 : 3 ∣ N
  · have h := hdiv3 h3
    omega
  · have h := hno3 h3
    omega

/-- Logarithmic least-prime pinch instantiated with the upgraded cyclotomic root-slot slopes
(`21/8` unconditionally and `8/3` when `¬ 3 ∣ N`). -/
theorem cyclotomic_least_prime_pinch {N p : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) (hmin : ∀ s ∈ N.primeFactors, p ≤ s) :
    (21 * ((p : ℝ) - 1) * Real.log 2 - 39) / 8 < (N.primeFactorsList.length : ℝ) ∧
      (¬ 3 ∣ N → (8 * ((p : ℝ) - 1) * Real.log 2 - 7) / 3 < (N.primeFactorsList.length : ℝ)) ∧
      p ^ N.primeFactorsList.length ≤ N := by
  have hmain := total_prime_factors_and_size_of_slope_and_least_prime ho hN hp hmin
    (by decide : 0 < 8) (cyclotomic_prime_factor_count ho hN)
  have hno3 : ¬ 3 ∣ N →
      (8 * ((p : ℝ) - 1) * Real.log 2 - 7) / 3 < (N.primeFactorsList.length : ℝ) := by
    intro h3
    have h := (total_prime_factors_and_size_of_slope_and_least_prime ho hN hp hmin
      (by decide : 0 < 3) (cyclotomic_slope_three_free ho hN h3)).1
    simpa using h
  refine ⟨?_, hno3, hmain.2⟩
  simpa using hmain.1

end OddPerfect
