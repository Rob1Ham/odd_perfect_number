module

public import OddPerfect.CyclotomicRootSlope
public import OddPerfect.UniversalCyclotomicRoots
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Zelinsky Full-Slope Multi-Block Synthesis & Vieta Mod-3 Refinement

Stepping Stone S6:
1. Mod-12 / Mod-20 identities, `Φ₃(Φ₅(w))` composite-chain exclusion, and cross-normalization
   disjointness between `normalizedSquareSum` and `normalizedQuarticSum`.
2. Vieta mod-3 root-slot cap (`card_twoModThree_dvd_sq_add_self_add_one_le_one`) and
   sharpened quadratic root-slot incidence restricting targets to `oneModThreeLargeSources`.
3. Sharpened quartic (`5/2`) root-slot incidence and sextic (`l = 7`) root-slot incidence.
4. Multi-block coupled slope combining `l = 3` and `l = 5` in the `3, 5`-free,
   `S₂ ∩ T₅ = ∅` regime, yielding `554 * ω(N) ≤ 199 * Ω(N) + 595` (`554/199 ≈ 2.7839 > 302/113`).
-/

public section

namespace OddPerfect

open ArithmeticFunction

/-! ## 1. Mod-12 / Mod-20 Identities & Cross-Normalization Exclusions -/

/-- Quadratic-quintic norm identity `4 * Φ₅(x) + 5 * x^2 = (2 * x^2 + x + 2)^2`. -/
theorem four_mul_phi5_eq_sq_sub_five_mul_sq (x : ℕ) :
    4 * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) + 5 * x ^ 2 = (2 * x ^ 2 + x + 2) ^ 2 := by
  ring

/-- Algebraic factorization of `Φ₃(Φ₅(w))` showing `Φ₃(Φ₅(w))` is composite for `2 ≤ w`. -/
theorem phi3_comp_phi5_factorization (w : ℕ) :
    let z := w ^ 4 + w ^ 3 + w ^ 2 + w + 1
    z ^ 2 + z + 1 =
      (w ^ 2 - w + 1) *
        (w ^ 6 + 3 * w ^ 5 + 5 * w ^ 4 + 6 * w ^ 3 + 7 * w ^ 2 + 6 * w + 3) := by
  dsimp only
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · decide
  · have hle : w ≤ w ^ 2 := Nat.le_self_pow (by decide) w
    zify [hle]
    ring

/-- Composite-chain exclusion: `Φ₃(Φ₅(w))` is never prime for `2 ≤ w`. -/
theorem not_prime_sq_add_self_add_one_of_phi5 {w : ℕ} (hw : 2 ≤ w) :
    ¬ ((w ^ 4 + w ^ 3 + w ^ 2 + w + 1) ^ 2 +
        (w ^ 4 + w ^ 3 + w ^ 2 + w + 1) + 1).Prime := by
  rw [phi3_comp_phi5_factorization w]
  have h1 : 1 < w ^ 2 - w + 1 := by
    have hsq : 2 * w ≤ w ^ 2 := by nlinarith
    omega
  have h2 : 1 < w ^ 6 + 3 * w ^ 5 + 5 * w ^ 4 + 6 * w ^ 3 + 7 * w ^ 2 + 6 * w + 3 := by
    omega
  exact Nat.not_prime_mul h1.ne' h2.ne'

private theorem five_mul_normalizedQuarticSum' {u : ℕ} (h : u % 5 = 1) :
    5 * normalizedQuarticSum u = u ^ 4 + u ^ 3 + u ^ 2 + u + 1 := by
  have hdvd : 5 ∣ u ^ 4 + u ^ 3 + u ^ 2 + u + 1 := by
    have hc : u ≡ 1 [MOD 5] := h
    have hpoly : u ^ 4 + u ^ 3 + u ^ 2 + u + 1 ≡ 1 ^ 4 + 1 ^ 3 + 1 ^ 2 + 1 + 1 [MOD 5] :=
      ((((hc.pow 4).add (hc.pow 3)).add (hc.pow 2)).add hc).add (Nat.ModEq.refl 1)
    exact Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using hpoly)
  simp only [normalizedQuarticSum, ite_eq_left h]
  exact Nat.mul_div_cancel' hdvd

/-- For any odd `v`, `normalizedQuarticSum v ≡ 1 [MOD 4]`. -/
theorem normalizedQuarticSum_mod_four {v : ℕ} (hv : Odd v) :
    normalizedQuarticSum v % 4 = 1 := by
  have hv4 : v % 4 = 1 ∨ v % 4 = 3 := by
    have := Nat.odd_iff.mp hv
    omega
  have hpoly4 : (v ^ 4 + v ^ 3 + v ^ 2 + v + 1) % 4 = 1 := by
    have hc : v ≡ v % 4 [MOD 4] := (Nat.mod_modEq v 4).symm
    have hp : v ^ 4 + v ^ 3 + v ^ 2 + v + 1 ≡
        (v % 4) ^ 4 + (v % 4) ^ 3 + (v % 4) ^ 2 + (v % 4) + 1 [MOD 4] :=
      ((((hc.pow 4).add (hc.pow 3)).add (hc.pow 2)).add hc).add (Nat.ModEq.refl 1)
    rcases hv4 with h | h <;> rw [h] at hp <;>
      change (v ^ 4 + v ^ 3 + v ^ 2 + v + 1) % 4 = _ at hp <;> omega
  by_cases h5 : v % 5 = 1
  · have h5mul := five_mul_normalizedQuarticSum' h5
    omega
  · simp only [normalizedQuarticSum, ite_eq_right h5]
    exact hpoly4

/-- Every prime value of `normalizedQuarticSum v` for an odd prime `v ≥ 3` satisfies
`w ≡ 1 [MOD 20]`. -/
theorem quartic_prime_target_one_mod_twenty {v : ℕ} (hv_prime : v.Prime) (hv3 : 3 ≤ v)
    (hw : (normalizedQuarticSum v).Prime) : normalizedQuarticSum v % 20 = 1 := by
  have hv_odd : Odd v := hv_prime.odd_of_ne_two (by omega)
  have hmod4 : normalizedQuarticSum v % 4 = 1 := normalizedQuarticSum_mod_four hv_odd
  have hmod5 : normalizedQuarticSum v % 5 = 1 :=
    (quartic_sigma_properties hv_prime hv3).2.2.2 _ hw dvd_rfl
  omega

/-- When `(u % 3 = 2 ∧ u % 4 = 1) ∨ (u % 3 = 1 ∧ u % 4 = 3)`, `normalizedSquareSum u ≡ 3 [MOD 4]`. -/
theorem normalizedSquareSum_mod_four_three {u : ℕ}
    (h : (u % 3 = 2 ∧ u % 4 = 1) ∨ (u % 3 = 1 ∧ u % 4 = 3)) :
    normalizedSquareSum u % 4 = 3 := by
  rcases h with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · have hne : u % 3 ≠ 1 := by omega
    simp only [normalizedSquareSum, ite_eq_right hne]
    have hc : u ≡ 1 [MOD 4] := h4
    have hp := ((hc.pow 2).add hc).add (Nat.ModEq.refl 1)
    change (u ^ 2 + u + 1) % 4 = _ at hp
    omega
  · have h3mul : 3 * normalizedSquareSum u = u ^ 2 + u + 1 := by
      have hdvd : 3 ∣ u ^ 2 + u + 1 := by
        have hc : u ≡ 1 [MOD 3] := h3
        have hp := ((hc.pow 2).add hc).add (Nat.ModEq.refl 1)
        exact Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using hp)
      simp only [normalizedSquareSum, ite_eq_left h3]
      exact Nat.mul_div_cancel' hdvd
    have hc : u ≡ 3 [MOD 4] := h4
    have hp := ((hc.pow 2).add hc).add (Nat.ModEq.refl 1)
    change (u ^ 2 + u + 1) % 4 = _ at hp
    omega

/-- Cross-normalization exclusion: `normalizedSquareSum u ≠ normalizedQuarticSum v` under the
mod-12 / unnormalized congruence conditions. -/
theorem normalizedSquareSum_ne_normalizedQuarticSum_of_cases {u v : ℕ}
    (_hu_odd : Odd u) (hv_odd : Odd v) (hv3 : 3 ≤ v)
    (h : (u % 3 = 2 ∧ u % 4 = 1) ∨ (u % 3 = 1 ∧ u % 4 = 3) ∨
      (u % 3 ≠ 1 ∧ v % 5 ≠ 1)) :
    normalizedSquareSum u ≠ normalizedQuarticSum v := by
  rcases h with h12 | h12 | ⟨hu3, hv5⟩
  · have hq := normalizedQuarticSum_mod_four hv_odd
    have hs := normalizedSquareSum_mod_four_three (Or.inl h12)
    omega
  · have hq := normalizedQuarticSum_mod_four hv_odd
    have hs := normalizedSquareSum_mod_four_three (Or.inr h12)
    omega
  · intro heq
    simp only [normalizedSquareSum, ite_eq_right hu3, normalizedQuarticSum, ite_eq_right hv5] at heq
    have hsq : (2 * u + 1) ^ 2 = 4 * v ^ 4 + 4 * v ^ 3 + 4 * v ^ 2 + 4 * v + 1 := by
      nlinarith
    have hlow : (2 * v ^ 2 + v) ^ 2 < (2 * u + 1) ^ 2 := by
      rw [hsq]
      have : 0 < 3 * v ^ 2 + 4 * v + 1 := by positivity
      nlinarith
    have hhigh : (2 * u + 1) ^ 2 < (2 * v ^ 2 + v + 1) ^ 2 := by
      rw [hsq]
      have hv_sq : 2 * v < v ^ 2 := by nlinarith
      nlinarith
    have h1 : 2 * v ^ 2 + v < 2 * u + 1 := by
      by_contra! hle
      have : (2 * u + 1) ^ 2 ≤ (2 * v ^ 2 + v) ^ 2 := Nat.pow_le_pow_left hle 2
      omega
    have h2 : 2 * u + 1 < 2 * v ^ 2 + v + 1 := by
      by_contra! hle
      have : (2 * v ^ 2 + v + 1) ^ 2 ≤ (2 * u + 1) ^ 2 := Nat.pow_le_pow_left hle 2
      omega
    omega

/-! ## 2. Vieta Mod-3 Root-Slot Refinement & `oneModThreeLargeSources` -/

/-- For any prime `w ≡ 1 [MOD 3]`, there is at most one `x < w` with `x ≡ 2 [MOD 3]`
and `w ∣ x^2 + x + 1` (because distinct roots satisfy `a + b + 1 = w`, impossible mod 3). -/
theorem card_twoModThree_dvd_sq_add_self_add_one_le_one {w : ℕ} (hw : w.Prime)
    (hw1 : w % 3 = 1) :
    ((Finset.range w).filter (fun x => x % 3 = 2 ∧ w ∣ x ^ 2 + x + 1)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hab
  have ha_mem := Finset.mem_filter.mp ha
  have hb_mem := Finset.mem_filter.mp hb
  have ha_lt : a < w := Finset.mem_range.mp ha_mem.1
  have hb_lt : b < w := Finset.mem_range.mp hb_mem.1
  have ha_mod : a % 3 = 2 := ha_mem.2.1
  have hb_mod : b % 3 = 2 := hb_mem.2.1
  have : Fact w.Prime := ⟨hw⟩
  have ha_z : (a : ZMod w) ^ 2 + (a : ZMod w) + 1 = 0 := by
    have h0 := (ZMod.natCast_eq_zero_iff (a ^ 2 + a + 1) w).mpr ha_mem.2.2
    push_cast at h0
    exact h0
  have hb_z : (b : ZMod w) ^ 2 + (b : ZMod w) + 1 = 0 := by
    have h0 := (ZMod.natCast_eq_zero_iff (b ^ 2 + b + 1) w).mpr hb_mem.2.2
    push_cast at h0
    exact h0
  have hprod : ((a : ZMod w) - (b : ZMod w)) * ((a : ZMod w) + (b : ZMod w) + 1) = 0 := by
    calc
      ((a : ZMod w) - (b : ZMod w)) * ((a : ZMod w) + (b : ZMod w) + 1)
          = ((a : ZMod w) ^ 2 + (a : ZMod w) + 1) - ((b : ZMod w) ^ 2 + (b : ZMod w) + 1) := by
              ring
      _ = 0 - 0 := by rw [ha_z, hb_z]
      _ = 0 := sub_zero 0
  have hne_z : (a : ZMod w) - (b : ZMod w) ≠ 0 := by
    intro hsub
    have heq_z : (a : ZMod w) = (b : ZMod w) := sub_eq_zero.mp hsub
    have hval := congrArg ZMod.val heq_z
    rw [ZMod.val_natCast_of_lt ha_lt, ZMod.val_natCast_of_lt hb_lt] at hval
    exact hab hval
  have hsum_z : (a : ZMod w) + (b : ZMod w) + 1 = 0 := (mul_eq_zero.mp hprod).resolve_left hne_z
  have hdvd : w ∣ a + b + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    exact hsum_z
  obtain ⟨k, hk⟩ := hdvd
  have hk_eq : k = 1 := by nlinarith
  subst hk_eq
  omega

/-- Large non-Euler prime factors (`v_r(N) ≥ 4`, `r ≠ 3`) congruent to `1 [MOD 3]`. -/
@[expose] def oneModThreeLargeSources (N p : ℕ) : Finset ℕ :=
  (largeSources N p).filter (fun r => r % 3 = 1)

/-- Large non-Euler prime factors (`v_r(N) ≥ 4`, `r ≠ 3`) not congruent to `1 [MOD 3]`. -/
@[expose] def twoModThreeLargeSources (N p : ℕ) : Finset ℕ :=
  (largeSources N p).filter (fun r => r % 3 ≠ 1)

/-- Square sources `u ≡ 2 [MOD 3]` whose normalized square sum is semiprime (`Ω = 2`). -/
@[expose] def squareSourcesSemiprimeTwo (N : ℕ) : Finset ℕ :=
  (squareSourcesTwo N).filter (fun u => cardFactors (normalizedSquareSum u) = 2)

private lemma largeSources_eq_union_one_two (N p : ℕ) :
    largeSources N p = oneModThreeLargeSources N p ∪ twoModThreeLargeSources N p := by
  ext r
  simp only [oneModThreeLargeSources, twoModThreeLargeSources, Finset.mem_union, Finset.mem_filter]
  by_cases h : r % 3 = 1 <;> tauto

private lemma oneModThreeLargeSources_disjoint_two (N p : ℕ) :
    Disjoint (oneModThreeLargeSources N p) (twoModThreeLargeSources N p) := by
  apply Finset.disjoint_left.mpr
  intro r h1 h2
  exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2

private lemma normalizedSquareSum_dvd_sq_add_self_add_one' (v : ℕ) :
    normalizedSquareSum v ∣ v ^ 2 + v + 1 := by
  by_cases hv : v % 3 = 1
  · obtain ⟨k, rfl⟩ : ∃ k, v = 3 * k + 1 := ⟨v / 3, by omega⟩
    have hnorm : normalizedSquareSum (3 * k + 1) = 3 * k ^ 2 + 3 * k + 1 := by
      rw [normalizedSquareSum, ite_eq_left (show (3 * k + 1) % 3 = 1 by omega)]
      rw [show (3 * k + 1) ^ 2 + (3 * k + 1) + 1 = 3 * (3 * k ^ 2 + 3 * k + 1) by ring]
      simp
    rw [hnorm]
    exact ⟨3, by ring⟩
  · simp [normalizedSquareSum, hv]

/-- Unconditional quadratic root-slot incidence with target set restricted to
`insert p (squareSourcesOne N ∪ oneModThreeLargeSources N p)`. -/
theorem squareSources_vieta_root_slot_incidence_uncond {N p : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) (_hp4 : p % 4 = 1) (_he : N.factorization p % 4 = 1)
    (hev : ∀ q : ℕ, q ≠ p → Even (N.factorization q)) :
    3 * (squareSourcesTwo N).card + 2 * (squareSourcesOne N).card ≤
      2 + N.factorization p + 4 * (squareSourcesOne N).card +
        2 * (oneModThreeLargeSources N p).card +
        ∑ q ∈ oneModThreeLargeSources N p, N.factorization q := by
  let L₁ := oneModThreeLargeSources N p
  let T := insert p (squareSourcesOne N ∪ L₁)
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
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hmem, hr3, hsp, by omega⟩, hmod⟩)
  have targetMem : T ⊆ N.primeFactors := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | h
    · exact hp
    · rcases Finset.mem_union.mp h with h | h
      · exact hs (Finset.mem_filter.mp h).1
      · exact (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1
  have upper := sum_cardFactors_le_target_exponents hN S T normalizedSquareSum hs localDiv cover
    (fun _ hr => ⟨Nat.prime_of_mem_primeFactors (targetMem hr),
      ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors (targetMem hr))⟩)
  have hdis_SL : Disjoint S₁ L₁ := by
    apply Finset.disjoint_left.mpr
    intro r hr hl
    have := (source (Finset.mem_filter.mp hr).1).2.2
    have := (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).2.2.2
    omega
  have hnot_p : p ∉ S₁ ∪ L₁ := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · have := (source (Finset.mem_filter.mp h).1).2.2
      omega
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2.2.1 rfl
  have htcard : T.card = S₁.card + L₁.card + 1 := by
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
      N.factorization p + (S₁.card * 2 + ∑ q ∈ L₁, N.factorization q) at upper
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
  have hsum_S₂ :
      A₁₂.card + 2 * A₂₂.card + 3 * A₃₂.card ≤ ∑ u ∈ S₂, cardFactors (normalizedSquareSum u) := by
    rw [hS₂_part, Finset.sum_union hdis_1222_32, Finset.sum_union hdis_12_22]
    have h1 : A₁₂.card ≤ ∑ u ∈ A₁₂, cardFactors (normalizedSquareSum u) := by
      calc
        A₁₂.card = ∑ _u ∈ A₁₂, 1 := by simp
        _ ≤ ∑ u ∈ A₁₂, cardFactors (normalizedSquareSum u) := by
            refine Finset.sum_le_sum fun u hu => ?_
            rw [cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp hu).2]
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
            rw [cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp hu).2]
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
  have hfiber_le (w : ℕ) :
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
    exact (hfiber_le _).trans ((Finset.card_le_card hsub).trans (by simp))
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
        ⟨Finset.mem_range.mpr hvw, hdvd.trans (normalizedSquareSum_dvd_sq_add_self_add_one' v)⟩
    exact (hfiber_le w).trans
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
  change 3 * S₂.card + 2 * S₁.card ≤
      2 + N.factorization p + 4 * S₁.card + 2 * L₁.card + ∑ q ∈ L₁, N.factorization q
  omega

/-- When `¬ 3 ∣ N`, `squareSourcesOne N = ∅` and every target prime in `T` has at most one
root in `squareSourcesTwo N`, giving the extra `+ (squareSourcesSemiprimeTwo N).card` slack. -/
theorem squareSources_vieta_root_slot_incidence_three_free {N p : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) (_hp4 : p % 4 = 1) (_he : N.factorization p % 4 = 1)
    (hev : ∀ q : ℕ, q ≠ p → Even (N.factorization q)) (h3 : ¬ 3 ∣ N) :
    3 * (squareSourcesTwo N).card + (squareSourcesSemiprimeTwo N).card ≤
      2 + N.factorization p + 2 * (oneModThreeLargeSources N p).card +
        ∑ q ∈ oneModThreeLargeSources N p, N.factorization q := by
  let L₁ := oneModThreeLargeSources N p
  let T := insert p L₁
  let S₂ := squareSourcesTwo N
  have hS1_zero : (squareSourcesOne N).card = 0 := by
    have hb := squareSourcesOne_card_le_three_exponent hN
    have hz : N.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd h3
    omega
  have hS1_empty : squareSourcesOne N = ∅ := Finset.card_eq_zero.mp hS1_zero
  have hs2 : S₂ ⊆ squareSources N := Finset.filter_subset _ _
  have hs : squareSources N ⊆ N.primeFactors := Finset.filter_subset _ _
  have source {u : ℕ} (hu : u ∈ S₂) : u.Prime ∧ 3 < u ∧ N.factorization u = 2 ∧ u % 3 = 2 := by
    obtain ⟨huS, hu_mod⟩ := Finset.mem_filter.mp hu
    obtain ⟨hmem, h3ne, hex⟩ := Finset.mem_filter.mp huS
    have hprime := Nat.prime_of_mem_primeFactors hmem
    have hodd := Nat.odd_iff.mp (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hmem))
    have := hprime.two_le
    have hu3_ndvd : u % 3 ≠ 0 := fun hz =>
      h3ne ((Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) hprime).mp
        (Nat.dvd_of_mod_eq_zero hz)).symm
    exact ⟨hprime, by omega, hex, by omega⟩
  have localDiv (u : ℕ) (hu : u ∈ S₂) :
      normalizedSquareSum u ∣ sigma 1 (u ^ N.factorization u) := by
    obtain ⟨hu', h3gt, h2, _⟩ := source hu
    rw [h2]
    exact normalizedSquareSum_dvd_sigma hu' h3gt
  have cover_mod (u : ℕ) (hu : u ∈ S₂) (r : ℕ) (hr : r ∈ (normalizedSquareSum u).primeFactors) :
      r % 3 = 1 ∧ r ∈ T := by
    obtain ⟨hup, hu3, he2, _⟩ := source hu
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
    refine ⟨hmod, ?_⟩
    by_cases hsp : r = p
    · exact Finset.mem_insert.mpr (Or.inl hsp)
    apply Finset.mem_insert_of_mem
    have hr3 : r ≠ 3 := by omega
    by_cases hex : N.factorization r = 2
    · exfalso
      have hrS1 : r ∈ squareSourcesOne N :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hmem, hr3, hex⟩, hmod⟩
      rw [hS1_empty] at hrS1
      exact Finset.notMem_empty _ hrS1
    · have hpos := (hrp.dvd_iff_one_le_factorization hN.2.ne').mp hrN
      obtain ⟨k, hk⟩ := hev r hsp
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hmem, hr3, hsp, by omega⟩, hmod⟩
  have cover (u : ℕ) (hu : u ∈ S₂) : (normalizedSquareSum u).primeFactors ⊆ T :=
    fun r hr => (cover_mod u hu r hr).2
  have targetMem : T ⊆ N.primeFactors := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | h
    · exact hp
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1
  have upper := sum_cardFactors_le_target_exponents hN S₂ T normalizedSquareSum
    (hs2.trans hs) localDiv cover
    (fun _ hr => ⟨Nat.prime_of_mem_primeFactors (targetMem hr),
      ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors (targetMem hr))⟩)
  have hnot_p : p ∉ L₁ := fun h =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2.2.1 rfl
  have htcard : T.card = L₁.card + 1 := Finset.card_insert_of_notMem hnot_p
  dsimp only [T] at upper
  rw [Finset.sum_insert hnot_p] at upper
  let A₁₂ := S₂.filter fun u => (normalizedSquareSum u).Prime
  let A₂₂ := squareSourcesSemiprimeTwo N
  let A₃₂ := S₂.filter fun u => 3 ≤ cardFactors (normalizedSquareSum u)
  have hS₂_part : S₂ = A₁₂ ∪ A₂₂ ∪ A₃₂ := by
    ext u
    simp only [A₁₂, A₂₂, squareSourcesSemiprimeTwo, A₃₂, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hu
      obtain ⟨hup, hu3, _⟩ := source hu
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
  have hsum_S₂ :
      A₁₂.card + 2 * A₂₂.card + 3 * A₃₂.card ≤ ∑ u ∈ S₂, cardFactors (normalizedSquareSum u) := by
    rw [hS₂_part, Finset.sum_union hdis_1222_32, Finset.sum_union hdis_12_22]
    have h1 : A₁₂.card ≤ ∑ u ∈ A₁₂, cardFactors (normalizedSquareSum u) := by
      calc
        A₁₂.card = ∑ _u ∈ A₁₂, 1 := by simp
        _ ≤ ∑ u ∈ A₁₂, cardFactors (normalizedSquareSum u) := by
            refine Finset.sum_le_sum fun u hu => ?_
            rw [cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp hu).2]
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
  let Up₂ := (S₂ ×ˢ T).filter fun uw => uw.1 < uw.2 ∧ uw.2 ∣ normalizedSquareSum uw.1
  let U_up := A₁₂ ∪ A₂₂
  have hU_up_card : U_up.card = A₁₂.card + A₂₂.card := Finset.card_union_of_disjoint hdis_12_22
  have hU_up_sub : U_up ⊆ Up₂.image Prod.fst := by
    intro u hu
    rw [Finset.mem_image]
    rcases Finset.mem_union.mp hu with hu12 | hu22
    · obtain ⟨huS2, hwp⟩ := Finset.mem_filter.mp hu12
      obtain ⟨hup, _, _, _⟩ := source huS2
      have hu_mod : u % 3 ≠ 1 := (Finset.mem_filter.mp huS2).2
      let w := normalizedSquareSum u
      have hwT : w ∈ T := cover u huS2 (Nat.mem_primeFactors.mpr ⟨hwp, dvd_rfl, hwp.ne_zero⟩)
      have hlt : u < w := by
        have hnorm : w = u ^ 2 + u + 1 := by simp [w, normalizedSquareSum, hu_mod]
        rw [hnorm]
        nlinarith [hup.one_lt]
      exact ⟨(u, w), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huS2, hwT⟩, hlt, dvd_rfl⟩, rfl⟩
    · obtain ⟨huS2, hcard2⟩ := Finset.mem_filter.mp hu22
      have hu_mod : u % 3 ≠ 1 := (Finset.mem_filter.mp huS2).2
      obtain ⟨w, hw_pf, huw⟩ := squareSourcesTwo_semiprime_exists_gt hu_mod hcard2
      have hwT : w ∈ T := cover u huS2 hw_pf
      have hwdvd : w ∣ normalizedSquareSum u := Nat.dvd_of_mem_primeFactors hw_pf
      exact ⟨(u, w), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huS2, hwT⟩, huw, hwdvd⟩, rfl⟩
  have hUp_lower : A₁₂.card + A₂₂.card ≤ Up₂.card := by
    rw [← hU_up_card]
    exact (Finset.card_le_card hU_up_sub).trans Finset.card_image_le
  have hUp_fiber : Up₂.card = ∑ w ∈ T, (Up₂.filter fun uw => uw.2 = w).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro uw huw
    exact (Finset.mem_product.mp (Finset.mem_filter.mp huw).1).2
  have hfiber_le_one : ∀ w ∈ T, (Up₂.filter fun uw => uw.2 = w).card ≤ 1 := by
    intro w hwT
    have hwp : w.Prime := Nat.prime_of_mem_primeFactors (targetMem hwT)
    have hfiber_le :
        (Up₂.filter fun uw => uw.2 = w).card ≤
          (S₂.filter fun v => v < w ∧ w ∣ normalizedSquareSum v).card := by
      apply Finset.card_le_card_of_injOn Prod.fst
      · intro uw huw
        obtain ⟨huw_Up, rfl⟩ := Finset.mem_filter.mp huw
        obtain ⟨huw_prod, hlt, hdvd⟩ := Finset.mem_filter.mp huw_Up
        exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp huw_prod).1, hlt, hdvd⟩
      · intro x hx y hy hxy
        obtain ⟨_, hx2⟩ := Finset.mem_filter.mp hx
        obtain ⟨_, hy2⟩ := Finset.mem_filter.mp hy
        exact Prod.ext hxy (hx2.trans hy2.symm)
    by_cases hw1 : w % 3 = 1
    · have hsub :
          (S₂.filter fun v => v < w ∧ w ∣ normalizedSquareSum v) ⊆
            (Finset.range w).filter (fun x => x % 3 = 2 ∧ w ∣ x ^ 2 + x + 1) := by
        intro v hv
        obtain ⟨hvS2, hvw, hdvd⟩ := Finset.mem_filter.mp hv
        have hv_mod := (source hvS2).2.2.2
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hvw, hv_mod, hdvd.trans (normalizedSquareSum_dvd_sq_add_self_add_one' v)⟩
      exact hfiber_le.trans ((Finset.card_le_card hsub).trans
        (card_twoModThree_dvd_sq_add_self_add_one_le_one hwp hw1))
    · have hempty : (S₂.filter fun v => v < w ∧ w ∣ normalizedSquareSum v) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro v hv
        obtain ⟨hvS2, _, hdvd⟩ := Finset.mem_filter.mp hv
        have hpf : w ∈ (normalizedSquareSum v).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hwp, hdvd, by
            obtain ⟨hvp, hv3, _, _⟩ := source hvS2
            have := normalizedSquareSum_one_lt hvp hv3
            omega⟩
        exact hw1 (cover_mod v hvS2 w hpf).1
      exact hfiber_le.trans (by rw [hempty]; simp)
  have hUp_upper : Up₂.card ≤ T.card := by
    calc
      Up₂.card = ∑ w ∈ T, (Up₂.filter fun uw => uw.2 = w).card := hUp_fiber
      _ ≤ ∑ _w ∈ T, 1 := Finset.sum_le_sum hfiber_le_one
      _ = T.card := by simp
  change 3 * S₂.card + A₂₂.card ≤
      2 + N.factorization p + 2 * L₁.card + ∑ q ∈ L₁, N.factorization q
  omega

/-- Combined quadratic Vieta root-slot incidence inequality retaining
`(squareSourcesSemiprimeTwo N).card` when `¬ 3 ∣ N` and restricting all large targets to
`oneModThreeLargeSources N p`. -/
theorem squareSources_vieta_root_slot_incidence {N p : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) (hp4 : p % 4 = 1) (he : N.factorization p % 4 = 1)
    (hev : ∀ q : ℕ, q ≠ p → Even (N.factorization q)) :
    3 * (squareSourcesTwo N).card +
        (if 3 ∣ N then 0 else (squareSourcesSemiprimeTwo N).card) +
        2 * (squareSourcesOne N).card ≤
      2 + N.factorization p + 4 * (squareSourcesOne N).card +
        2 * (oneModThreeLargeSources N p).card +
        ∑ q ∈ oneModThreeLargeSources N p, N.factorization q := by
  by_cases h3 : 3 ∣ N
  · simp only [ite_eq_left h3, add_zero]
    exact squareSources_vieta_root_slot_incidence_uncond ho hN hp hp4 he hev
  · simp only [ite_eq_right h3]
    have h := squareSources_vieta_root_slot_incidence_three_free ho hN hp hp4 he hev h3
    omega

/-- Sharpened `3`-free linear slope retaining `twoModThreeLargeSources` and
`squareSourcesSemiprimeTwo` slack. -/
theorem sharpened_cyclotomic_slope_three_free {N p : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) (hp4 : p % 4 = 1) (he : N.factorization p % 4 = 1)
    (hev : ∀ q : ℕ, q ≠ p → Even (N.factorization q)) (h3 : ¬ 3 ∣ N) :
    24 * N.primeFactors.card + 12 * (twoModThreeLargeSources N p).card +
        2 * (squareSourcesSemiprimeTwo N).card ≤
      9 * N.primeFactorsList.length + 21 ∧
      8 * N.primeFactors.card + 4 * (twoModThreeLargeSources N p).card ≤
        3 * N.primeFactorsList.length + 7 := by
  have hinc := squareSources_vieta_root_slot_incidence_three_free ho hN hp hp4 he hev h3
  let S := (N.primeFactors.erase p).erase 3
  let L₁ := oneModThreeLargeSources N p
  let L₂ := twoModThreeLargeSources N p
  have hpos {r : ℕ} (hr : r ∈ N.primeFactors) : 0 < N.factorization r :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
  have hparts : S = squareSources N ∪ largeSources N p := by
    ext r
    simp only [S, Finset.mem_erase, squareSources, largeSources, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hr3, hrp, hr⟩
      obtain ⟨k, hk⟩ := hev r hrp
      have := hpos hr
      by_cases htwo : N.factorization r = 2
      · exact Or.inl ⟨hr, hr3, htwo⟩
      · exact Or.inr ⟨hr, hr3, hrp, by omega⟩
    · rintro (⟨hr, hr3, htwo⟩ | ⟨hr, hr3, hrp, _⟩)
      · exact ⟨hr3, fun h => by subst r; omega, hr⟩
      · exact ⟨hr3, hrp, hr⟩
  have hdis : Disjoint (squareSources N) (largeSources N p) := by
    apply Finset.disjoint_left.mpr
    intro r hs hl
    have htwo := (Finset.mem_filter.mp hs).2.2
    have hlarge := (Finset.mem_filter.mp hl).2.2.2
    omega
  have hcard : S.card = (squareSources N).card + (largeSources N p).card := by
    rw [hparts, Finset.card_union_of_disjoint hdis]
  have hS1_zero : (squareSourcesOne N).card = 0 := by
    have hb := squareSourcesOne_card_le_three_exponent hN
    have hz : N.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd h3
    omega
  have hsq_card : (squareSources N).card = (squareSourcesTwo N).card := by
    rw [squareSources_eq_union_one_two N, Finset.card_union_of_disjoint (squareSourcesOne_disjoint_two N),
      hS1_zero, zero_add]
  have hL_card : (largeSources N p).card = L₁.card + L₂.card := by
    rw [largeSources_eq_union_one_two N p, Finset.card_union_of_disjoint (oneModThreeLargeSources_disjoint_two N p)]
  have hsum : (∑ r ∈ S, N.factorization r) =
      2 * (squareSourcesTwo N).card +
        (∑ r ∈ L₁, N.factorization r + ∑ r ∈ L₂, N.factorization r) := by
    rw [hparts, Finset.sum_union hdis, largeSources_eq_union_one_two N p,
      Finset.sum_union (oneModThreeLargeSources_disjoint_two N p)]
    congr 1
    rw [squareSources_eq_union_one_two N, Finset.sum_union (squareSourcesOne_disjoint_two N),
      Finset.card_eq_zero.mp hS1_zero, Finset.sum_empty, zero_add]
    calc
      _ = ∑ _r ∈ squareSourcesTwo N, (2 : ℕ) :=
        Finset.sum_congr rfl fun _ hr => (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.2
      _ = _ := by simp [Nat.mul_comm]
  have hL1_ge : 4 * L₁.card ≤ ∑ r ∈ L₁, N.factorization r := by
    calc
      4 * L₁.card = ∑ _r ∈ L₁, (4 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ ∑ r ∈ L₁, N.factorization r := Finset.sum_le_sum fun r hr =>
          (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.2.2
  have hL2_ge : 4 * L₂.card ≤ ∑ r ∈ L₂, N.factorization r := by
    calc
      4 * L₂.card = ∑ _r ∈ L₂, (4 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ ∑ r ∈ L₂, N.factorization r := Finset.sum_le_sum fun r hr =>
          (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.2.2
  have htot : N.primeFactorsList.length =
      N.factorization p + ∑ r ∈ N.primeFactors.erase p, N.factorization r := by
    rw [← cardFactors_apply, cardFactors_eq_sum_factorization]
    exact (Finset.add_sum_erase N.primeFactors _ hp).symm
  have hpcount := Finset.card_erase_add_one hp
  have hp_pos := hpos hp
  have h3not : 3 ∉ N.primeFactors := fun hmem => h3 (Nat.dvd_of_mem_primeFactors hmem)
  have h3erase : S = N.primeFactors.erase p :=
    Finset.erase_eq_of_notMem fun h => h3not (Finset.mem_of_mem_erase h)
  rw [← h3erase] at htot hpcount
  change 3 * (squareSourcesTwo N).card + (squareSourcesSemiprimeTwo N).card ≤
      2 + N.factorization p + 2 * L₁.card + ∑ q ∈ L₁, N.factorization q at hinc
  change 24 * N.primeFactors.card + 12 * L₂.card +
        2 * (squareSourcesSemiprimeTwo N).card ≤
      9 * N.primeFactorsList.length + 21 ∧
      8 * N.primeFactors.card + 4 * L₂.card ≤
        3 * N.primeFactorsList.length + 7
  constructor <;> omega

private theorem ochem_rao_restricted_incidence {N p : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) (_hp4 : p % 4 = 1) (_he : N.factorization p % 4 = 1)
    (hev : ∀ q : ℕ, q ≠ p → Even (N.factorization q)) :
    2 * (squareSources N).card ≤ 1 + N.factorization p +
      3 * (squareSourcesOne N).card + (oneModThreeLargeSources N p).card +
      ∑ q ∈ oneModThreeLargeSources N p, N.factorization q := by
  let L₁ := oneModThreeLargeSources N p
  let T := insert p (squareSourcesOne N ∪ L₁)
  let S := squareSources N
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
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hmem, hr3, hsp, by omega⟩, hmod⟩)
  have targetMem : T ⊆ N.primeFactors := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | h
    · exact hp
    · rcases Finset.mem_union.mp h with h | h
      · exact hs (Finset.mem_filter.mp h).1
      · exact (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1
  have upper := sum_cardFactors_le_target_exponents hN S T normalizedSquareSum hs localDiv cover
    (fun _ hr => ⟨Nat.prime_of_mem_primeFactors (targetMem hr),
      ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors (targetMem hr))⟩)
  let A := S.filter fun u => (normalizedSquareSum u).Prime
  have singletons : A.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn normalizedSquareSum
    · intro u hu
      obtain ⟨huS, hup⟩ := Finset.mem_filter.mp hu
      exact cover u huS (Nat.mem_primeFactors.mpr ⟨hup, dvd_rfl, hup.ne_zero⟩)
    · intro u hu v hv h
      obtain ⟨hup, hu3, _⟩ := source (Finset.mem_filter.mp hu).1
      obtain ⟨hvp, hv3, _⟩ := source (Finset.mem_filter.mp hv).1
      exact normalizedSquareSum_injective hup hu3 hvp hv3 h
  have hdis : Disjoint (squareSourcesOne N) L₁ := by
    apply Finset.disjoint_left.mpr
    intro r hr hl
    have := (source (Finset.mem_filter.mp hr).1).2.2
    have := (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).2.2.2
    omega
  have hnot : p ∉ squareSourcesOne N ∪ L₁ := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · have := (source (Finset.mem_filter.mp h).1).2.2
      omega
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2.2.1 rfl
  have htcard : T.card = (squareSourcesOne N).card + L₁.card + 1 := by
    dsimp only [T]
    rw [Finset.card_insert_of_notMem hnot, Finset.card_union_of_disjoint hdis]
  have hsum : ∑ r ∈ squareSourcesOne N, N.factorization r = (squareSourcesOne N).card * 2 := by
    calc
      _ = ∑ _r ∈ squareSourcesOne N, (2 : ℕ) :=
        Finset.sum_congr rfl fun _ hr => (source (Finset.mem_filter.mp hr).1).2.2
      _ = _ := by simp
  dsimp only [T] at upper
  rw [Finset.sum_insert hnot, Finset.sum_union hdis, hsum] at upper
  have hcount := squareSources_count_le_normalized_count ho
  change 2 * S.card ≤ (∑ u ∈ S, cardFactors (normalizedSquareSum u)) + A.card at hcount
  change 2 * S.card ≤ 1 + N.factorization p +
    3 * (squareSourcesOne N).card + L₁.card + ∑ q ∈ L₁, N.factorization q
  omega

/-- Unconditional sharpened linear slope retaining `twoModThreeLargeSources` slack:
`21 * ω(N) + 11 * |twoModThreeLargeSources N p| ≤ 8 * Ω(N) + 39`. -/
theorem sharpened_cyclotomic_prime_factor_count {N p : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) (hp4 : p % 4 = 1) (he : N.factorization p % 4 = 1)
    (hev : ∀ q : ℕ, q ≠ p → Even (N.factorization q)) :
    21 * N.primeFactors.card + 11 * (twoModThreeLargeSources N p).card ≤
      8 * N.primeFactorsList.length + 39 := by
  by_cases h3 : 3 ∣ N
  · have hincA := ochem_rao_restricted_incidence ho hN hp hp4 he hev
    have hincB := squareSources_vieta_root_slot_incidence_uncond ho hN hp hp4 he hev
    let S := (N.primeFactors.erase p).erase 3
    let L₁ := oneModThreeLargeSources N p
    let L₂ := twoModThreeLargeSources N p
    have hpos {r : ℕ} (hr : r ∈ N.primeFactors) : 0 < N.factorization r :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
    have hparts : S = squareSources N ∪ largeSources N p := by
      ext r
      simp only [S, Finset.mem_erase, squareSources, largeSources, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ⟨hr3, hrp, hr⟩
        obtain ⟨k, hk⟩ := hev r hrp
        have := hpos hr
        by_cases htwo : N.factorization r = 2
        · exact Or.inl ⟨hr, hr3, htwo⟩
        · exact Or.inr ⟨hr, hr3, hrp, by omega⟩
      · rintro (⟨hr, hr3, htwo⟩ | ⟨hr, hr3, hrp, _⟩)
        · exact ⟨hr3, fun h => by subst r; omega, hr⟩
        · exact ⟨hr3, hrp, hr⟩
    have hdis : Disjoint (squareSources N) (largeSources N p) := by
      apply Finset.disjoint_left.mpr
      intro r hs hl
      have htwo := (Finset.mem_filter.mp hs).2.2
      have hlarge := (Finset.mem_filter.mp hl).2.2.2
      omega
    have hcard : S.card = (squareSources N).card + (largeSources N p).card := by
      rw [hparts, Finset.card_union_of_disjoint hdis]
    have hsq_card : (squareSources N).card = (squareSourcesOne N).card + (squareSourcesTwo N).card := by
      rw [squareSources_eq_union_one_two N, Finset.card_union_of_disjoint (squareSourcesOne_disjoint_two N)]
    have hL_card : (largeSources N p).card = L₁.card + L₂.card := by
      rw [largeSources_eq_union_one_two N p,
        Finset.card_union_of_disjoint (oneModThreeLargeSources_disjoint_two N p)]
    have hsumL : ∑ r ∈ largeSources N p, N.factorization r =
        ∑ r ∈ L₁, N.factorization r + ∑ r ∈ L₂, N.factorization r := by
      rw [largeSources_eq_union_one_two N p,
        Finset.sum_union (oneModThreeLargeSources_disjoint_two N p)]
    have hsum : (∑ r ∈ S, N.factorization r) =
        2 * (squareSources N).card + (∑ r ∈ L₁, N.factorization r + ∑ r ∈ L₂, N.factorization r) := by
      rw [hparts, Finset.sum_union hdis, hsumL]
      congr 1
      calc
        _ = ∑ _r ∈ squareSources N, (2 : ℕ) :=
          Finset.sum_congr rfl fun _ hr => (Finset.mem_filter.mp hr).2.2
        _ = _ := by simp [Nat.mul_comm]
    have hL1_ge : 4 * L₁.card ≤ ∑ r ∈ L₁, N.factorization r := by
      calc
        4 * L₁.card = ∑ _r ∈ L₁, (4 : ℕ) := by simp [Nat.mul_comm]
        _ ≤ ∑ r ∈ L₁, N.factorization r := Finset.sum_le_sum fun r hr =>
            (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.2.2
    have hL2_ge : 4 * L₂.card ≤ ∑ r ∈ L₂, N.factorization r := by
      calc
        4 * L₂.card = ∑ _r ∈ L₂, (4 : ℕ) := by simp [Nat.mul_comm]
        _ ≤ ∑ r ∈ L₂, N.factorization r := Finset.sum_le_sum fun r hr =>
            (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.2.2
    have htot : N.primeFactorsList.length =
        N.factorization p + ∑ r ∈ N.primeFactors.erase p, N.factorization r := by
      rw [← cardFactors_apply, cardFactors_eq_sum_factorization]
      exact (Finset.add_sum_erase N.primeFactors _ hp).symm
    have hpcount := Finset.card_erase_add_one hp
    have hbound := squareSourcesOne_card_le_three_exponent hN
    have hp_pos := hpos hp
    have h3mem_pf : 3 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, h3, hN.2.ne'⟩
    have h3p : 3 ≠ p := by omega
    have h3mem := Finset.mem_erase.mpr ⟨h3p, h3mem_pf⟩
    have h3card : S.card + 1 = (N.primeFactors.erase p).card := Finset.card_erase_add_one h3mem
    have h3sum : N.factorization 3 + (∑ r ∈ S, N.factorization r) =
        ∑ r ∈ N.primeFactors.erase p, N.factorization r := Finset.add_sum_erase _ _ h3mem
    change 2 * (squareSources N).card ≤ 1 + N.factorization p +
      3 * (squareSourcesOne N).card + L₁.card + ∑ q ∈ L₁, N.factorization q at hincA
    change 3 * (squareSourcesTwo N).card + 2 * (squareSourcesOne N).card ≤
      2 + N.factorization p + 4 * (squareSourcesOne N).card + 2 * L₁.card +
        ∑ q ∈ L₁, N.factorization q at hincB
    change 21 * N.primeFactors.card + 11 * L₂.card ≤ 8 * N.primeFactorsList.length + 39
    linarith [hincA, hincB, hcard, hsq_card, hL_card, hsum, hL1_ge, hL2_ge, htot,
      hpcount, hbound, hp_pos, h3card, h3sum]
  · have hno3 := (sharpened_cyclotomic_slope_three_free ho hN hp hp4 he hev h3).2
    have hL2_sub : twoModThreeLargeSources N p ⊆ N.primeFactors.erase p := by
      intro r hr
      have hrL := (Finset.mem_filter.mp hr).1
      have hrF := Finset.mem_filter.mp hrL
      exact Finset.mem_erase.mpr ⟨hrF.2.2.1, hrF.1⟩
    have hL2_lt : (twoModThreeLargeSources N p).card + 1 ≤ N.primeFactors.card := by
      calc
        (twoModThreeLargeSources N p).card + 1 ≤ (N.primeFactors.erase p).card + 1 :=
          Nat.succ_le_succ (Finset.card_le_card hL2_sub)
        _ = N.primeFactors.card := Finset.card_erase_add_one hp
    omega

/-! ## 3. Sharpened Quartic (`5/2`) & Sextic (`l = 7`) Root-Slot Incidence -/

private lemma geometricBlock_five_eq' (x : ℕ) :
    geometricBlock x 5 = x ^ 4 + x ^ 3 + x ^ 2 + x + 1 := by
  simp [geometricBlock, Finset.sum_range_succ]
  ring

private lemma normalizedQuarticSum_dvd_geometricBlock' (x : ℕ) :
    normalizedQuarticSum x ∣ geometricBlock x 5 := by
  rw [geometricBlock_five_eq']
  by_cases hx : x % 5 = 1
  · rw [← five_mul_normalizedQuarticSum' hx]
    exact dvd_mul_left _ _
  · simp [normalizedQuarticSum, hx]

private lemma normalizedQuarticSum_one_lt' {u : ℕ} (hu3 : 3 ≤ u) :
    1 < normalizedQuarticSum u := by
  by_cases h5 : u % 5 = 1
  · have := five_mul_normalizedQuarticSum' h5
    have h2 : 9 ≤ u ^ 2 := by nlinarith
    have h4 : 81 ≤ u ^ 4 := by nlinarith
    omega
  · simp only [normalizedQuarticSum, ite_eq_right h5]
    have h2 : 9 ≤ u ^ 2 := by nlinarith
    omega

private lemma normalizedQuarticSum_gt_self_of_mod_one' {u : ℕ} (hu3 : 3 ≤ u) (hu_mod : u % 5 = 1) :
    u < normalizedQuarticSum u := by
  have := five_mul_normalizedQuarticSum' hu_mod
  have h2 : 3 * u ≤ u ^ 2 := by nlinarith
  have h3 : 9 * u ≤ u ^ 3 := by nlinarith
  have h4 : 27 * u ≤ u ^ 4 := by nlinarith
  omega

private lemma le_pow_cardFactors_of_primeFactors_le'' {M u : ℕ} (hM : M ≠ 0)
    (h : ∀ w ∈ M.primeFactors, w ≤ u) : M ≤ u ^ cardFactors M := by
  calc
    M = ∏ w ∈ M.primeFactors, w ^ M.factorization w := Nat.prod_primeFactors_pow_factorization hM
    _ ≤ ∏ w ∈ M.primeFactors, u ^ M.factorization w :=
        Finset.prod_le_prod fun w hw => Nat.pow_le_pow_left (h w hw) _
    _ = u ^ ∑ w ∈ M.primeFactors, M.factorization w := Finset.prod_pow_eq_pow_sum _ _ _
    _ = u ^ cardFactors M := by
        rw [cardFactors_eq_sum_factorization]
        rfl

private lemma quartic_zero_exists_gt_of_cardFactors_le_three' {u : ℕ} (hu3 : 3 ≤ u)
    (hu_mod : u % 5 ≠ 1) (hcard : cardFactors (normalizedQuarticSum u) ≤ 3) :
    ∃ w ∈ (normalizedQuarticSum u).primeFactors, u < w := by
  have hnorm : normalizedQuarticSum u = u ^ 4 + u ^ 3 + u ^ 2 + u + 1 := by
    simp [normalizedQuarticSum, hu_mod]
  by_contra! hle
  have hM_ne : normalizedQuarticSum u ≠ 0 := by rw [hnorm]; positivity
  have hbound := le_pow_cardFactors_of_primeFactors_le'' hM_ne hle
  have hpow : u ^ cardFactors (normalizedQuarticSum u) ≤ u ^ 3 :=
    Nat.pow_le_pow_right (by omega) hcard
  have h34 : u ^ 3 ≤ u ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hle_pow : u ^ 4 + u ^ 3 + u ^ 2 + u + 1 ≤ u ^ 4 := by
    calc
      u ^ 4 + u ^ 3 + u ^ 2 + u + 1 = normalizedQuarticSum u := hnorm.symm
      _ ≤ u ^ cardFactors (normalizedQuarticSum u) := hbound
      _ ≤ u ^ 3 := hpow
      _ ≤ u ^ 4 := h34
  have hpos : 0 < u ^ 3 + u ^ 2 + u + 1 := by positivity
  omega

private lemma normalizedQuarticSum_strictMono_of_mod_ne_one' {u v : ℕ}
    (hu_mod : u % 5 ≠ 1) (hv_mod : v % 5 ≠ 1)
    (heq : normalizedQuarticSum u = normalizedQuarticSum v) : u = v := by
  simp only [normalizedQuarticSum, ite_eq_right hu_mod, ite_eq_right hv_mod] at heq
  have hmono : StrictMono (fun x : ℕ => x ^ 4 + x ^ 3 + x ^ 2 + x + 1) := by
    intro a b hab
    have h2 : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hab.le 2
    have h3 : a ^ 3 ≤ b ^ 3 := Nat.pow_le_pow_left hab.le 3
    have h4 : a ^ 4 ≤ b ^ 4 := Nat.pow_le_pow_left hab.le 4
    dsimp
    omega
  exact hmono.injective heq

/-- **Sharpened Quartic Root-Slot Incidence Bound (`l = 5`)**:
Separating `B₂` (`cardFactors = 2`) and `B₃` (`cardFactors = 3`) improves `7/3` to `5/2`:
`5 * |Q₀| + 3 * |Q₁| ≤ 2 * ∑ r ∈ T₅, N.factorization r + 4 * |T₅|`. -/
theorem quarticSources_sharpened_incidence {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) :
    5 * (quarticSourcesZero N q).card + 3 * (quarticSourcesOne N q).card ≤
      2 * (∑ r ∈ oneModFiveTargets N q, N.factorization r) +
        4 * (oneModFiveTargets N q).card := by
  let Q₀ := quarticSourcesZero N q
  let Q₁ := quarticSourcesOne N q
  let Q := Q₀ ∪ Q₁
  let T₅ := oneModFiveTargets N q
  have hdis_Q : Disjoint Q₀ Q₁ := by
    apply Finset.disjoint_left.mpr
    intro r h0 h1
    exact (Finset.mem_filter.mp h0).2.2 (Finset.mem_filter.mp h1).2.2
  have hQ_sub : Q ⊆ N.primeFactors := by
    intro r hr
    rcases Finset.mem_union.mp hr with h0 | h1
    · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp h0).1
    · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp h1).1
  have hsource {u : ℕ} (hu : u ∈ Q) : u.Prime ∧ 3 ≤ u ∧ N.factorization u = 4 := by
    have huN : u ∈ N.primeFactors := hQ_sub hu
    have hup := Nat.prime_of_mem_primeFactors huN
    have huo := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors huN)
    have hu_ge2 := hup.two_le
    have hu_ne2 : u ≠ 2 := fun h => by subst h; exact (by decide : ¬ Odd 2) huo
    have hu_fac : N.factorization u = 4 := by
      rcases Finset.mem_union.mp hu with h0 | h1
      · exact (Finset.mem_filter.mp h0).2.1
      · exact (Finset.mem_filter.mp h1).2.1
    exact ⟨hup, by omega, hu_fac⟩
  have hlocalDiv (u : ℕ) (hu : u ∈ Q) :
      normalizedQuarticSum u ∣ sigma 1 (u ^ N.factorization u) := by
    obtain ⟨hup, hu3, h4⟩ := hsource hu
    rw [h4]
    exact (quartic_sigma_properties hup hu3).2.1
  have hcover (u : ℕ) (hu : u ∈ Q) : (normalizedQuarticSum u).primeFactors ⊆ T₅ := by
    intro w hw
    obtain ⟨hup, hu3, h4⟩ := hsource hu
    obtain ⟨hwp, hwdvd, _⟩ := Nat.mem_primeFactors.mp hw
    have hprops := quartic_sigma_properties hup hu3
    have hw_mod : w % 5 = 1 := hprops.2.2.2 w hwp hwdvd
    have hw_odd : Odd w := hwp.odd_of_ne_two (by omega)
    have hw_sig : w ∣ ∑ d ∈ (u ^ 4).divisors, d := by
      rw [← sigma_one_apply]
      exact hwdvd.trans hprops.2.1
    have hu4_dvd : u ^ 4 ∣ N := by simpa [h4] using Nat.ordProj_dvd N u
    have hw_dvd_N : w ∣ N := by
      apply dvd_perfect_of_exact_prime_pow hN hup hu4_dvd _ hwp hw_odd hw_sig
      rw [hup.pow_dvd_iff_le_factorization hN.2.ne']
      omega
    have hw_mem := Nat.mem_primeFactors.mpr ⟨hwp, hw_dvd_N, hN.2.ne'⟩
    by_cases hwq : w = q
    · exact Finset.mem_insert.mpr (Or.inl hwq)
    · exact Finset.mem_insert_of_mem
        (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hwq, hw_mem⟩, hw_mod⟩)
  have hT_sub : T₅ ⊆ N.primeFactors := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | h
    · exact hq
    · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp h).1
  have hupper := sum_cardFactors_le_target_exponents hN Q T₅ normalizedQuarticSum
    hQ_sub hlocalDiv hcover (fun r hr =>
      ⟨Nat.prime_of_mem_primeFactors (hT_sub hr),
        ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors (hT_sub hr))⟩)
  let B₁ := Q₀.filter fun u => (normalizedQuarticSum u).Prime
  let B₂ := Q₀.filter fun u => cardFactors (normalizedQuarticSum u) = 2
  let B₃ := Q₀.filter fun u => cardFactors (normalizedQuarticSum u) = 3
  let B₄ := Q₀.filter fun u => 4 ≤ cardFactors (normalizedQuarticSum u)
  let C₁ := Q₁.filter fun u => (normalizedQuarticSum u).Prime
  let C₂ := Q₁.filter fun u => 2 ≤ cardFactors (normalizedQuarticSum u)
  have hQ₀_part : Q₀ = B₁ ∪ B₂ ∪ B₃ ∪ B₄ := by
    ext u
    simp only [B₁, B₂, B₃, B₄, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hu
      have hu3 := (hsource (Finset.mem_union_left _ hu)).2.1
      have hpos := cardFactors_pos_iff_one_lt.mpr (normalizedQuarticSum_one_lt' hu3)
      by_cases h1 : cardFactors (normalizedQuarticSum u) = 1
      · exact Or.inl (Or.inl (Or.inl ⟨hu, cardFactors_eq_one_iff_prime.mp h1⟩))
      · by_cases h2 : cardFactors (normalizedQuarticSum u) = 2
        · exact Or.inl (Or.inl (Or.inr ⟨hu, h2⟩))
        · by_cases h3 : cardFactors (normalizedQuarticSum u) = 3
          · exact Or.inl (Or.inr ⟨hu, h3⟩)
          · exact Or.inr ⟨hu, by omega⟩
    · rintro (((⟨hu, _⟩ | ⟨hu, _⟩) | ⟨hu, _⟩) | ⟨hu, _⟩) <;> exact hu
  have hdis_B₁_B₂ : Disjoint B₁ B₂ := by
    apply Finset.disjoint_left.mpr
    intro u h1 h2
    have hp1 := cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp h1).2
    have hp2 := (Finset.mem_filter.mp h2).2
    omega
  have hdis_B₁₂_B₃ : Disjoint (B₁ ∪ B₂) B₃ := by
    apply Finset.disjoint_left.mpr
    intro u h12 h3
    have hp3 := (Finset.mem_filter.mp h3).2
    rcases Finset.mem_union.mp h12 with h1 | h2
    · have hp1 := cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp h1).2
      omega
    · have hp2 := (Finset.mem_filter.mp h2).2
      omega
  have hdis_B₁₂₃_B₄ : Disjoint (B₁ ∪ B₂ ∪ B₃) B₄ := by
    apply Finset.disjoint_left.mpr
    intro u h123 h4
    have hge4 := (Finset.mem_filter.mp h4).2
    rcases Finset.mem_union.mp h123 with h12 | h3
    · rcases Finset.mem_union.mp h12 with h1 | h2
      · have hp1 := cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp h1).2
        omega
      · have hp2 := (Finset.mem_filter.mp h2).2
        omega
    · have hp3 := (Finset.mem_filter.mp h3).2
      omega
  have hQ₀_card : Q₀.card = B₁.card + B₂.card + B₃.card + B₄.card := by
    rw [hQ₀_part, Finset.card_union_of_disjoint hdis_B₁₂₃_B₄,
      Finset.card_union_of_disjoint hdis_B₁₂_B₃, Finset.card_union_of_disjoint hdis_B₁_B₂]
  have hQ₁_part : Q₁ = C₁ ∪ C₂ := by
    ext u
    simp only [C₁, C₂, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hu
      have hu3 := (hsource (Finset.mem_union_right _ hu)).2.1
      have hpos := cardFactors_pos_iff_one_lt.mpr (normalizedQuarticSum_one_lt' hu3)
      by_cases h1 : cardFactors (normalizedQuarticSum u) = 1
      · exact Or.inl ⟨hu, cardFactors_eq_one_iff_prime.mp h1⟩
      · exact Or.inr ⟨hu, by omega⟩
    · rintro (⟨hu, _⟩ | ⟨hu, _⟩) <;> exact hu
  have hdis_C₁_C₂ : Disjoint C₁ C₂ := by
    apply Finset.disjoint_left.mpr
    intro u h1 h2
    have hp1 := cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp h1).2
    have hge2 := (Finset.mem_filter.mp h2).2
    omega
  have hQ₁_card : Q₁.card = C₁.card + C₂.card := by
    rw [hQ₁_part, Finset.card_union_of_disjoint hdis_C₁_C₂]
  have hsum_Q₀ :
      B₁.card + 2 * B₂.card + 3 * B₃.card + 4 * B₄.card ≤
        ∑ u ∈ Q₀, cardFactors (normalizedQuarticSum u) := by
    rw [hQ₀_part, Finset.sum_union hdis_B₁₂₃_B₄, Finset.sum_union hdis_B₁₂_B₃,
      Finset.sum_union hdis_B₁_B₂]
    have h1 : B₁.card ≤ ∑ u ∈ B₁, cardFactors (normalizedQuarticSum u) := by
      calc
        B₁.card = ∑ _u ∈ B₁, 1 := by simp
        _ ≤ ∑ u ∈ B₁, cardFactors (normalizedQuarticSum u) := by
            refine Finset.sum_le_sum fun u hu => ?_
            rw [cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp hu).2]
    have h2 : 2 * B₂.card ≤ ∑ u ∈ B₂, cardFactors (normalizedQuarticSum u) := by
      calc
        2 * B₂.card = ∑ _u ∈ B₂, 2 := by simp [Nat.mul_comm]
        _ ≤ ∑ u ∈ B₂, cardFactors (normalizedQuarticSum u) := by
            refine Finset.sum_le_sum fun u hu => ?_
            rw [(Finset.mem_filter.mp hu).2]
    have h3 : 3 * B₃.card ≤ ∑ u ∈ B₃, cardFactors (normalizedQuarticSum u) := by
      calc
        3 * B₃.card = ∑ _u ∈ B₃, 3 := by simp [Nat.mul_comm]
        _ ≤ ∑ u ∈ B₃, cardFactors (normalizedQuarticSum u) := by
            refine Finset.sum_le_sum fun u hu => ?_
            rw [(Finset.mem_filter.mp hu).2]
    have h4 : 4 * B₄.card ≤ ∑ u ∈ B₄, cardFactors (normalizedQuarticSum u) := by
      calc
        4 * B₄.card = ∑ _u ∈ B₄, 4 := by simp [Nat.mul_comm]
        _ ≤ ∑ u ∈ B₄, cardFactors (normalizedQuarticSum u) :=
            Finset.sum_le_sum fun u hu => (Finset.mem_filter.mp hu).2
    omega
  have hsum_Q₁ :
      C₁.card + 2 * C₂.card ≤ ∑ u ∈ Q₁, cardFactors (normalizedQuarticSum u) := by
    rw [hQ₁_part, Finset.sum_union hdis_C₁_C₂]
    have h1 : C₁.card ≤ ∑ u ∈ C₁, cardFactors (normalizedQuarticSum u) := by
      calc
        C₁.card = ∑ _u ∈ C₁, 1 := by simp
        _ ≤ ∑ u ∈ C₁, cardFactors (normalizedQuarticSum u) := by
            refine Finset.sum_le_sum fun u hu => ?_
            rw [cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp hu).2]
    have h2 : 2 * C₂.card ≤ ∑ u ∈ C₂, cardFactors (normalizedQuarticSum u) := by
      calc
        2 * C₂.card = ∑ _u ∈ C₂, 2 := by simp [Nat.mul_comm]
        _ ≤ ∑ u ∈ C₂, cardFactors (normalizedQuarticSum u) :=
            Finset.sum_le_sum fun u hu => (Finset.mem_filter.mp hu).2
    omega
  have hsum_Q :
      ∑ u ∈ Q, cardFactors (normalizedQuarticSum u) =
        ∑ u ∈ Q₀, cardFactors (normalizedQuarticSum u) +
          ∑ u ∈ Q₁, cardFactors (normalizedQuarticSum u) :=
    Finset.sum_union hdis_Q
  let Up₅ := (Q ×ˢ T₅).filter fun uw => uw.1 < uw.2 ∧ uw.2 ∣ normalizedQuarticSum uw.1
  let U_up := B₁ ∪ B₂ ∪ B₃ ∪ C₁
  have hdis_B₁₂₃_C₁ : Disjoint (B₁ ∪ B₂ ∪ B₃) C₁ := by
    apply Finset.disjoint_left.mpr
    intro u h123 hc1
    have huQ₁ := (Finset.mem_filter.mp hc1).1
    rcases Finset.mem_union.mp h123 with h12 | h3
    · rcases Finset.mem_union.mp h12 with h1 | h2
      · exact Finset.disjoint_left.mp hdis_Q (Finset.mem_filter.mp h1).1 huQ₁
      · exact Finset.disjoint_left.mp hdis_Q (Finset.mem_filter.mp h2).1 huQ₁
    · exact Finset.disjoint_left.mp hdis_Q (Finset.mem_filter.mp h3).1 huQ₁
  have hU_up_card : U_up.card = B₁.card + B₂.card + B₃.card + C₁.card := by
    dsimp only [U_up]
    rw [Finset.card_union_of_disjoint hdis_B₁₂₃_C₁, Finset.card_union_of_disjoint hdis_B₁₂_B₃,
      Finset.card_union_of_disjoint hdis_B₁_B₂]
  have hU_up_sub : U_up ⊆ Up₅.image Prod.fst := by
    intro u hu
    rw [Finset.mem_image]
    rcases Finset.mem_union.mp hu with hB123 | hC₁
    · rcases Finset.mem_union.mp hB123 with hB12 | huB₃
      · rcases Finset.mem_union.mp hB12 with huB₁ | huB₂
        · obtain ⟨huQ₀, hwp⟩ := Finset.mem_filter.mp huB₁
          have huQ : u ∈ Q := Finset.mem_union_left _ huQ₀
          have hu_mod : u % 5 ≠ 1 := (Finset.mem_filter.mp huQ₀).2.2
          have hu3 := (hsource huQ).2.1
          let w := normalizedQuarticSum u
          have hwT : w ∈ T₅ := hcover u huQ (Nat.mem_primeFactors.mpr ⟨hwp, dvd_rfl, hwp.ne_zero⟩)
          have hlt : u < w := by
            have hnorm : w = u ^ 4 + u ^ 3 + u ^ 2 + u + 1 := by simp [w, normalizedQuarticSum, hu_mod]
            have hsq : 3 * u ≤ u ^ 2 := by nlinarith
            rw [hnorm]
            omega
          exact ⟨(u, w), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huQ, hwT⟩, hlt, dvd_rfl⟩, rfl⟩
        · obtain ⟨huQ₀, h2⟩ := Finset.mem_filter.mp huB₂
          have huQ : u ∈ Q := Finset.mem_union_left _ huQ₀
          have hu3 := (hsource huQ).2.1
          have hu_mod : u % 5 ≠ 1 := (Finset.mem_filter.mp huQ₀).2.2
          obtain ⟨w, hw_pf, huw⟩ :=
            quartic_zero_exists_gt_of_cardFactors_le_three' hu3 hu_mod (by omega)
          exact ⟨(u, w), Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨huQ, hcover u huQ hw_pf⟩, huw, Nat.dvd_of_mem_primeFactors hw_pf⟩, rfl⟩
      · obtain ⟨huQ₀, h3⟩ := Finset.mem_filter.mp huB₃
        have huQ : u ∈ Q := Finset.mem_union_left _ huQ₀
        have hu3 := (hsource huQ).2.1
        have hu_mod : u % 5 ≠ 1 := (Finset.mem_filter.mp huQ₀).2.2
        obtain ⟨w, hw_pf, huw⟩ :=
          quartic_zero_exists_gt_of_cardFactors_le_three' hu3 hu_mod (by omega)
        exact ⟨(u, w), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨huQ, hcover u huQ hw_pf⟩, huw, Nat.dvd_of_mem_primeFactors hw_pf⟩, rfl⟩
    · obtain ⟨huQ₁, hwp⟩ := Finset.mem_filter.mp hC₁
      have huQ : u ∈ Q := Finset.mem_union_right _ huQ₁
      have hu3 := (hsource huQ).2.1
      have hu_mod : u % 5 = 1 := (Finset.mem_filter.mp huQ₁).2.2
      let w := normalizedQuarticSum u
      have hwT : w ∈ T₅ := hcover u huQ (Nat.mem_primeFactors.mpr ⟨hwp, dvd_rfl, hwp.ne_zero⟩)
      have hlt : u < w := normalizedQuarticSum_gt_self_of_mod_one' hu3 hu_mod
      exact ⟨(u, w), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huQ, hwT⟩, hlt, dvd_rfl⟩, rfl⟩
  have hUp_lower : B₁.card + B₂.card + B₃.card + C₁.card ≤ Up₅.card := by
    rw [← hU_up_card]
    exact (Finset.card_le_card hU_up_sub).trans Finset.card_image_le
  let T_B₁ := B₁.image normalizedQuarticSum
  have hT_B₁_sub : T_B₁ ⊆ T₅ := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨huQ₀, hwp⟩ := Finset.mem_filter.mp hu
    exact hcover u (Finset.mem_union_left _ huQ₀)
      (Nat.mem_primeFactors.mpr ⟨hwp, dvd_rfl, hwp.ne_zero⟩)
  have hT_B₁_card : T_B₁.card = B₁.card := by
    apply Finset.card_image_of_injOn
    intro u hu v hv heq
    have hu_mod : u % 5 ≠ 1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2.2
    have hv_mod : v % 5 ≠ 1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2.2
    exact normalizedQuarticSum_strictMono_of_mod_ne_one' hu_mod hv_mod heq
  have hUp_fiber : Up₅.card = ∑ w ∈ T₅, (Up₅.filter fun uw => uw.2 = w).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro uw huw
    exact (Finset.mem_product.mp (Finset.mem_filter.mp huw).1).2
  have hfiber_le (w : ℕ) :
      (Up₅.filter fun uw => uw.2 = w).card ≤
        (Q.filter fun v => v < w ∧ w ∣ normalizedQuarticSum v).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro uw huw
      obtain ⟨huw_Up, rfl⟩ := Finset.mem_filter.mp huw
      obtain ⟨huw_prod, hlt, hdvd⟩ := Finset.mem_filter.mp huw_Up
      exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp huw_prod).1, hlt, hdvd⟩
    · intro x hx y hy hxy
      obtain ⟨_, hx2⟩ := Finset.mem_filter.mp hx
      obtain ⟨_, hy2⟩ := Finset.mem_filter.mp hy
      exact Prod.ext hxy (hx2.trans hy2.symm)
  have hfiber_T_B₁ : ∀ w ∈ T_B₁, (Up₅.filter fun uw => uw.2 = w).card ≤ 1 := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨huQ₀, hwp⟩ := Finset.mem_filter.mp hu
    have huQ : u ∈ Q := Finset.mem_union_left _ huQ₀
    have hup := (hsource huQ).1
    have hu_mod : u % 5 ≠ 1 := (Finset.mem_filter.mp huQ₀).2.2
    have hw_eq : normalizedQuarticSum u = geometricBlock u 5 := by
      rw [geometricBlock_five_eq']
      simp [normalizedQuarticSum, hu_mod]
    have hsub :
        (Q.filter fun v => v < normalizedQuarticSum u ∧ normalizedQuarticSum u ∣ normalizedQuarticSum v) ⊆
          {u} := by
      intro v hv
      obtain ⟨hvQ, hvw, hdvd⟩ := Finset.mem_filter.mp hv
      have hvp := (hsource hvQ).1
      rw [Finset.mem_singleton]
      rw [hw_eq] at hvw hdvd hwp
      exact geometricBlock_prime_root_unique hup (by decide : Nat.Prime 5) (by decide : 3 ≤ 5)
        hwp hvp hvw (hdvd.trans (normalizedQuarticSum_dvd_geometricBlock' v))
    exact (hfiber_le _).trans ((Finset.card_le_card hsub).trans (by simp))
  have hfiber_other : ∀ w ∈ T₅ \ T_B₁, (Up₅.filter fun uw => uw.2 = w).card ≤ 4 := by
    intro w hw
    have hwT : w ∈ T₅ := (Finset.mem_sdiff.mp hw).1
    have hwp : w.Prime := Nat.prime_of_mem_primeFactors (hT_sub hwT)
    by_cases hw5 : w = 5
    · subst hw5
      have hempty : Q.filter (fun v => v < 5 ∧ 5 ∣ normalizedQuarticSum v) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro v hv
        obtain ⟨hvQ, _, hdvd⟩ := Finset.mem_filter.mp hv
        obtain ⟨hvp, hv3, _⟩ := hsource hvQ
        exact (quartic_sigma_properties hvp hv3).2.2.1 hdvd
      exact (hfiber_le 5).trans (by rw [hempty]; simp)
    · have hsub :
          (Q.filter fun v => v < w ∧ w ∣ normalizedQuarticSum v) ⊆
            (Finset.range w).filter (fun x => w ∣ geometricBlock x 5) := by
        intro v hv
        obtain ⟨_, hvw, hdvd⟩ := Finset.mem_filter.mp hv
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hvw, hdvd.trans (normalizedQuarticSum_dvd_geometricBlock' v)⟩
      exact (hfiber_le w).trans
        ((Finset.card_le_card hsub).trans
          (card_range_dvd_geometricBlock_le_pred (by decide : Nat.Prime 5) hwp hw5))
  have hUp_upper : Up₅.card + 3 * B₁.card ≤ 4 * T₅.card := by
    have hsdiff := Finset.sum_sdiff hT_B₁_sub (f := fun w => (Up₅.filter fun uw => uw.2 = w).card)
    have h1 : ∑ w ∈ T_B₁, (Up₅.filter fun uw => uw.2 = w).card ≤ T_B₁.card := by
      calc
        _ ≤ ∑ _w ∈ T_B₁, 1 := Finset.sum_le_sum hfiber_T_B₁
        _ = T_B₁.card := by simp
    have h2 : ∑ w ∈ T₅ \ T_B₁, (Up₅.filter fun uw => uw.2 = w).card ≤ 4 * (T₅ \ T_B₁).card := by
      calc
        _ ≤ ∑ _w ∈ T₅ \ T_B₁, 4 := Finset.sum_le_sum hfiber_other
        _ = 4 * (T₅ \ T_B₁).card := by simp [Nat.mul_comm]
    have hcard_sdiff : T_B₁.card + (T₅ \ T_B₁).card = T₅.card := by
      rw [← Finset.card_union_of_disjoint disjoint_sdiff_self_right,
        Finset.union_sdiff_of_subset hT_B₁_sub]
    omega
  change 5 * Q₀.card + 3 * Q₁.card ≤ 2 * (∑ r ∈ T₅, N.factorization r) + 4 * T₅.card
  omega

/-- The sextic divisor sum `geometricBlock u 7 = u^6 + ... + 1` with its factor of `7` removed
when `u ≡ 1 [MOD 7]`. -/
@[expose] def normalizedSexticSum (u : ℕ) : ℕ :=
  if u % 7 = 1 then (geometricBlock u 7) / 7 else geometricBlock u 7

/-- Non-Euler primes with exact exponent 6 that are not congruent to 1 modulo 7. -/
@[expose] def sexticSourcesZero (N q : ℕ) : Finset ℕ :=
  (N.primeFactors.erase q).filter (fun r => N.factorization r = 6 ∧ r % 7 ≠ 1)

/-- Non-Euler primes with exact exponent 6 that are congruent to 1 modulo 7. -/
@[expose] def sexticSourcesOne (N q : ℕ) : Finset ℕ :=
  (N.primeFactors.erase q).filter (fun r => N.factorization r = 6 ∧ r % 7 = 1)

/-- Potential target primes for sextic component sums: `q` together with all non-Euler prime
factors congruent to 1 modulo 7. -/
@[expose] def oneModSevenTargets (N q : ℕ) : Finset ℕ :=
  insert q ((N.primeFactors.erase q).filter (fun r => r % 7 = 1))

private lemma geometricBlock_seven_eq (x : ℕ) :
    geometricBlock x 7 = x ^ 6 + x ^ 5 + x ^ 4 + x ^ 3 + x ^ 2 + x + 1 := by
  simp [geometricBlock, Finset.sum_range_succ]
  ring

private lemma seven_mul_normalizedSexticSum {u : ℕ} (h : u % 7 = 1) :
    7 * normalizedSexticSum u = geometricBlock u 7 := by
  have hdvd : 7 ∣ geometricBlock u 7 := by
    rw [geometricBlock_seven_eq]
    have hc : u ≡ 1 [MOD 7] := h
    have hp := ((((((hc.pow 6).add (hc.pow 5)).add (hc.pow 4)).add (hc.pow 3)).add
      (hc.pow 2)).add hc).add (Nat.ModEq.refl 1)
    exact Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using hp)
  simp only [normalizedSexticSum, ite_eq_left h]
  exact Nat.mul_div_cancel' hdvd

private lemma normalizedSexticSum_dvd_geometricBlock (x : ℕ) :
    normalizedSexticSum x ∣ geometricBlock x 7 := by
  by_cases hx : x % 7 = 1
  · rw [← seven_mul_normalizedSexticSum hx]
    exact dvd_mul_left _ _
  · simp [normalizedSexticSum, hx]

/-- Core arithmetic properties of `sigma 1 (r ^ 6)` and `normalizedSexticSum r`:
1. `normalizedSexticSum r ∣ sigma 1 (r ^ 6)`
2. `7 ∤ normalizedSexticSum r`
3. Every prime divisor `w` of `normalizedSexticSum r` satisfies `w ≡ 1 [MOD 7]`. -/
theorem sextic_sigma_properties {r : ℕ} (hr : r.Prime) (_hr3 : 3 ≤ r) :
    normalizedSexticSum r ∣ sigma 1 (r ^ 6) ∧
      ¬ 7 ∣ normalizedSexticSum r ∧ (∀ w, w.Prime → w ∣ normalizedSexticSum r → w % 7 = 1) := by
  have hsig : sigma 1 (r ^ 6) = geometricBlock r 7 := by
    rw [sigma_one_apply_prime_pow hr, geometricBlock]
  have hdvd : normalizedSexticSum r ∣ sigma 1 (r ^ 6) := by
    rw [hsig]
    exact normalizedSexticSum_dvd_geometricBlock r
  have hnot7 : ¬ 7 ∣ normalizedSexticSum r := by
    by_cases h7 : r % 7 = 1
    · have hmul : 7 * normalizedSexticSum r = ∑ i ∈ Finset.range 7, r ^ i := by
        rw [seven_mul_normalizedSexticSum h7, geometricBlock]
      have h7dvd : 7 ∣ ∑ i ∈ Finset.range 7, r ^ i := by
        rw [← hmul]
        exact dvd_mul_right _ _
      have h72 := not_sq_dvd_geom_sum (b := r) (l := 7) (by decide) (by decide) h7dvd
      intro hdiv
      apply h72
      rw [← hmul, pow_two]
      exact Nat.mul_dvd_mul_left 7 hdiv
    · simp only [normalizedSexticSum, ite_eq_right h7, geometricBlock_seven_eq]
      have hc : r ≡ r % 7 [MOD 7] := (Nat.mod_modEq r 7).symm
      have hpoly : r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1 ≡
          (r % 7) ^ 6 + (r % 7) ^ 5 + (r % 7) ^ 4 + (r % 7) ^ 3 +
            (r % 7) ^ 2 + (r % 7) + 1 [MOD 7] :=
        (((((((hc.pow 6).add (hc.pow 5)).add (hc.pow 4)).add (hc.pow 3)).add
          (hc.pow 2)).add hc).add (Nat.ModEq.refl 1))
      have hrem : r % 7 = 0 ∨ r % 7 = 2 ∨ r % 7 = 3 ∨ r % 7 = 4 ∨ r % 7 = 5 ∨ r % 7 = 6 := by
        omega
      rcases hrem with h | h | h | h | h | h <;> rw [h] at hpoly <;>
        change (r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1) % 7 = _ at hpoly <;> omega
  have hw_mod : ∀ w, w.Prime → w ∣ normalizedSexticSum r → w % 7 = 1 := by
    intro w hw hwn
    let : Fact w.Prime := ⟨hw⟩
    have hw_sig : w ∣ ∑ d ∈ (r ^ 6).divisors, d := by
      rw [← sigma_one_apply]
      exact hwn.trans hdvd
    have hiff := (dvd_sum_divisors_prime_pow_iff hr hw 6).mp hw_sig
    split_ifs at hiff with hrz
    · have hw7 : w ∣ 7 := by simpa using hiff
      have heq : w = 7 := ((Nat.dvd_prime (by decide : Nat.Prime 7)).mp hw7).resolve_left hw.ne_one
      subst heq
      exact (hnot7 hwn).elim
    · have hord_dvd : orderOf (r : ZMod w) ∣ 7 := by simpa using hiff
      rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hord_dvd with h1 | h7
      · exact (hrz (orderOf_eq_one_iff.mp h1)).elim
      · have hr_ne0 : (r : ZMod w) ≠ 0 := by
          intro hz
          rw [hz, orderOf_zero] at h7
          omega
        have hsub : orderOf (r : ZMod w) ∣ w - 1 := ZMod.orderOf_dvd_card_sub_one hr_ne0
        rw [h7] at hsub
        have hw_gt1 := hw.one_lt
        omega
  exact ⟨hdvd, hnot7, hw_mod⟩

/-- The cardinality of sextic components `r ≠ q` with `v_r(N) = 6` and `r ≡ 1 [MOD 7]`
is bounded above by `N.factorization 7`. -/
theorem sexticSourcesOne_card_le_seven_exponent {N q : ℕ} (hN : N.Perfect) :
    (sexticSourcesOne N q).card ≤ N.factorization 7 := by
  apply card_le_factorization_of_sigma_sources hN (by decide) (by decide)
  · exact (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  · intro r hr
    obtain ⟨hmem, hsix, hmod⟩ := Finset.mem_filter.mp hr
    have hrp := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hmem)
    rw [hsix, sigma_one_apply_prime_pow hrp, ← geometricBlock, ← seven_mul_normalizedSexticSum hmod]
    exact dvd_mul_right _ _

private lemma normalizedSexticSum_one_lt {u : ℕ} (hu3 : 3 ≤ u) :
    1 < normalizedSexticSum u := by
  by_cases h7 : u % 7 = 1
  · have hmul := seven_mul_normalizedSexticSum h7
    rw [geometricBlock_seven_eq] at hmul
    have h2 : 9 ≤ u ^ 2 := by nlinarith
    have h4 : 81 ≤ u ^ 4 := by nlinarith
    omega
  · simp only [normalizedSexticSum, ite_eq_right h7, geometricBlock_seven_eq]
    have h2 : 9 ≤ u ^ 2 := by nlinarith
    omega

private lemma normalizedSexticSum_gt_self_of_mod_one {u : ℕ} (hu3 : 3 ≤ u) (hu_mod : u % 7 = 1) :
    u < normalizedSexticSum u := by
  have hmul := seven_mul_normalizedSexticSum hu_mod
  rw [geometricBlock_seven_eq] at hmul
  have h2 : 3 * u ≤ u ^ 2 := by nlinarith
  have h3 : 9 * u ≤ u ^ 3 := by nlinarith
  have h4 : 27 * u ≤ u ^ 4 := by nlinarith
  omega

private lemma sextic_zero_exists_gt_of_cardFactors_le_five {u : ℕ} (hu3 : 3 ≤ u)
    (hu_mod : u % 7 ≠ 1) (hcard : cardFactors (normalizedSexticSum u) ≤ 5) :
    ∃ w ∈ (normalizedSexticSum u).primeFactors, u < w := by
  have hnorm : normalizedSexticSum u = u ^ 6 + u ^ 5 + u ^ 4 + u ^ 3 + u ^ 2 + u + 1 := by
    simp [normalizedSexticSum, hu_mod, geometricBlock_seven_eq]
  by_contra! hle
  have hM_ne : normalizedSexticSum u ≠ 0 := by rw [hnorm]; positivity
  have hbound := le_pow_cardFactors_of_primeFactors_le'' hM_ne hle
  have hpow : u ^ cardFactors (normalizedSexticSum u) ≤ u ^ 5 :=
    Nat.pow_le_pow_right (by omega) hcard
  have h56 : u ^ 5 ≤ u ^ 6 := Nat.pow_le_pow_right (by omega) (by decide)
  have hle_pow : u ^ 6 + u ^ 5 + u ^ 4 + u ^ 3 + u ^ 2 + u + 1 ≤ u ^ 6 := by
    calc
      u ^ 6 + u ^ 5 + u ^ 4 + u ^ 3 + u ^ 2 + u + 1 = normalizedSexticSum u := hnorm.symm
      _ ≤ u ^ cardFactors (normalizedSexticSum u) := hbound
      _ ≤ u ^ 5 := hpow
      _ ≤ u ^ 6 := h56
  have hpos : 0 < u ^ 5 + u ^ 4 + u ^ 3 + u ^ 2 + u + 1 := by positivity
  omega

private lemma normalizedSexticSum_strictMono_of_mod_ne_one {u v : ℕ}
    (hu_mod : u % 7 ≠ 1) (hv_mod : v % 7 ≠ 1)
    (heq : normalizedSexticSum u = normalizedSexticSum v) : u = v := by
  simp only [normalizedSexticSum, ite_eq_right hu_mod, ite_eq_right hv_mod,
    geometricBlock_seven_eq] at heq
  have hmono : StrictMono (fun x : ℕ => x ^ 6 + x ^ 5 + x ^ 4 + x ^ 3 + x ^ 2 + x + 1) := by
    intro a b hab
    have h2 : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hab.le 2
    have h3 : a ^ 3 ≤ b ^ 3 := Nat.pow_le_pow_left hab.le 3
    have h4 : a ^ 4 ≤ b ^ 4 := Nat.pow_le_pow_left hab.le 4
    have h5 : a ^ 5 ≤ b ^ 5 := Nat.pow_le_pow_left hab.le 5
    have h6 : a ^ 6 ≤ b ^ 6 := Nat.pow_le_pow_left hab.le 6
    dsimp
    omega
  exact hmono.injective heq

/-- **Sextic Root-Slot Incidence Bound (`l = 7`)**:
`11 * |S₀| + 6 * |S₁| ≤ 5 * ∑ r ∈ T₇, N.factorization r + 6 * |T₇|`. -/
theorem sexticSources_root_slot_incidence {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) :
    11 * (sexticSourcesZero N q).card + 6 * (sexticSourcesOne N q).card ≤
      5 * (∑ r ∈ oneModSevenTargets N q, N.factorization r) +
        6 * (oneModSevenTargets N q).card := by
  let S₀ := sexticSourcesZero N q
  let S₁ := sexticSourcesOne N q
  let Q := S₀ ∪ S₁
  let T₇ := oneModSevenTargets N q
  have hdis_Q : Disjoint S₀ S₁ := by
    apply Finset.disjoint_left.mpr
    intro r h0 h1
    exact (Finset.mem_filter.mp h0).2.2 (Finset.mem_filter.mp h1).2.2
  have hQ_sub : Q ⊆ N.primeFactors := by
    intro r hr
    rcases Finset.mem_union.mp hr with h0 | h1
    · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp h0).1
    · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp h1).1
  have hsource {u : ℕ} (hu : u ∈ Q) : u.Prime ∧ 3 ≤ u ∧ N.factorization u = 6 := by
    have huN : u ∈ N.primeFactors := hQ_sub hu
    have hup := Nat.prime_of_mem_primeFactors huN
    have huo := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors huN)
    have hu_ge2 := hup.two_le
    have hu_ne2 : u ≠ 2 := fun h => by subst h; exact (by decide : ¬ Odd 2) huo
    have hu_fac : N.factorization u = 6 := by
      rcases Finset.mem_union.mp hu with h0 | h1
      · exact (Finset.mem_filter.mp h0).2.1
      · exact (Finset.mem_filter.mp h1).2.1
    exact ⟨hup, by omega, hu_fac⟩
  have hlocalDiv (u : ℕ) (hu : u ∈ Q) :
      normalizedSexticSum u ∣ sigma 1 (u ^ N.factorization u) := by
    obtain ⟨hup, hu3, h6⟩ := hsource hu
    rw [h6]
    exact (sextic_sigma_properties hup hu3).1
  have hcover (u : ℕ) (hu : u ∈ Q) : (normalizedSexticSum u).primeFactors ⊆ T₇ := by
    intro w hw
    obtain ⟨hup, hu3, h6⟩ := hsource hu
    obtain ⟨hwp, hwdvd, _⟩ := Nat.mem_primeFactors.mp hw
    have hprops := sextic_sigma_properties hup hu3
    have hw_mod : w % 7 = 1 := hprops.2.2 w hwp hwdvd
    have hw_odd : Odd w := hwp.odd_of_ne_two (by omega)
    have hw_sig : w ∣ ∑ d ∈ (u ^ 6).divisors, d := by
      rw [← sigma_one_apply]
      exact hwdvd.trans hprops.1
    have hu6_dvd : u ^ 6 ∣ N := by simpa [h6] using Nat.ordProj_dvd N u
    have hw_dvd_N : w ∣ N := by
      apply dvd_perfect_of_exact_prime_pow hN hup hu6_dvd _ hwp hw_odd hw_sig
      rw [hup.pow_dvd_iff_le_factorization hN.2.ne']
      omega
    have hw_mem := Nat.mem_primeFactors.mpr ⟨hwp, hw_dvd_N, hN.2.ne'⟩
    by_cases hwq : w = q
    · exact Finset.mem_insert.mpr (Or.inl hwq)
    · exact Finset.mem_insert_of_mem
        (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hwq, hw_mem⟩, hw_mod⟩)
  have hT_sub : T₇ ⊆ N.primeFactors := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | h
    · exact hq
    · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp h).1
  have hupper := sum_cardFactors_le_target_exponents hN Q T₇ normalizedSexticSum
    hQ_sub hlocalDiv hcover (fun r hr =>
      ⟨Nat.prime_of_mem_primeFactors (hT_sub hr),
        ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors (hT_sub hr))⟩)
  let D₁ := S₀.filter fun u => (normalizedSexticSum u).Prime
  let D₂₅ := S₀.filter fun u =>
    2 ≤ cardFactors (normalizedSexticSum u) ∧ cardFactors (normalizedSexticSum u) ≤ 5
  let D₆ := S₀.filter fun u => 6 ≤ cardFactors (normalizedSexticSum u)
  let E₁ := S₁.filter fun u => (normalizedSexticSum u).Prime
  let E₂ := S₁.filter fun u => 2 ≤ cardFactors (normalizedSexticSum u)
  have hS₀_part : S₀ = D₁ ∪ D₂₅ ∪ D₆ := by
    ext u
    simp only [D₁, D₂₅, D₆, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hu
      have hu3 := (hsource (Finset.mem_union_left _ hu)).2.1
      have hpos := cardFactors_pos_iff_one_lt.mpr (normalizedSexticSum_one_lt hu3)
      by_cases h1 : cardFactors (normalizedSexticSum u) = 1
      · exact Or.inl (Or.inl ⟨hu, cardFactors_eq_one_iff_prime.mp h1⟩)
      · by_cases h5 : cardFactors (normalizedSexticSum u) ≤ 5
        · exact Or.inl (Or.inr ⟨hu, by omega, h5⟩)
        · exact Or.inr ⟨hu, by omega⟩
    · rintro ((⟨hu, _⟩ | ⟨hu, _⟩) | ⟨hu, _⟩) <;> exact hu
  have hdis_D₁_D₂₅ : Disjoint D₁ D₂₅ := by
    apply Finset.disjoint_left.mpr
    intro u h1 h25
    have hp1 := cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp h1).2
    have hge2 := (Finset.mem_filter.mp h25).2.1
    omega
  have hdis_D₁₂₅_D₆ : Disjoint (D₁ ∪ D₂₅) D₆ := by
    apply Finset.disjoint_left.mpr
    intro u h125 h6
    have hge6 := (Finset.mem_filter.mp h6).2
    rcases Finset.mem_union.mp h125 with h1 | h25
    · have hp1 := cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp h1).2
      omega
    · have hle5 := (Finset.mem_filter.mp h25).2.2
      omega
  have hS₀_card : S₀.card = D₁.card + D₂₅.card + D₆.card := by
    rw [hS₀_part, Finset.card_union_of_disjoint hdis_D₁₂₅_D₆, Finset.card_union_of_disjoint hdis_D₁_D₂₅]
  have hS₁_part : S₁ = E₁ ∪ E₂ := by
    ext u
    simp only [E₁, E₂, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hu
      have hu3 := (hsource (Finset.mem_union_right _ hu)).2.1
      have hpos := cardFactors_pos_iff_one_lt.mpr (normalizedSexticSum_one_lt hu3)
      by_cases h1 : cardFactors (normalizedSexticSum u) = 1
      · exact Or.inl ⟨hu, cardFactors_eq_one_iff_prime.mp h1⟩
      · exact Or.inr ⟨hu, by omega⟩
    · rintro (⟨hu, _⟩ | ⟨hu, _⟩) <;> exact hu
  have hdis_E₁_E₂ : Disjoint E₁ E₂ := by
    apply Finset.disjoint_left.mpr
    intro u h1 h2
    have hp1 := cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp h1).2
    have hge2 := (Finset.mem_filter.mp h2).2
    omega
  have hS₁_card : S₁.card = E₁.card + E₂.card := by
    rw [hS₁_part, Finset.card_union_of_disjoint hdis_E₁_E₂]
  have hsum_S₀ :
      D₁.card + 2 * D₂₅.card + 6 * D₆.card ≤ ∑ u ∈ S₀, cardFactors (normalizedSexticSum u) := by
    rw [hS₀_part, Finset.sum_union hdis_D₁₂₅_D₆, Finset.sum_union hdis_D₁_D₂₅]
    have h1 : D₁.card ≤ ∑ u ∈ D₁, cardFactors (normalizedSexticSum u) := by
      calc
        D₁.card = ∑ _u ∈ D₁, 1 := by simp
        _ ≤ ∑ u ∈ D₁, cardFactors (normalizedSexticSum u) := by
            refine Finset.sum_le_sum fun u hu => ?_
            rw [cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp hu).2]
    have h25 : 2 * D₂₅.card ≤ ∑ u ∈ D₂₅, cardFactors (normalizedSexticSum u) := by
      calc
        2 * D₂₅.card = ∑ _u ∈ D₂₅, 2 := by simp [Nat.mul_comm]
        _ ≤ ∑ u ∈ D₂₅, cardFactors (normalizedSexticSum u) :=
            Finset.sum_le_sum fun u hu => (Finset.mem_filter.mp hu).2.1
    have h6 : 6 * D₆.card ≤ ∑ u ∈ D₆, cardFactors (normalizedSexticSum u) := by
      calc
        6 * D₆.card = ∑ _u ∈ D₆, 6 := by simp [Nat.mul_comm]
        _ ≤ ∑ u ∈ D₆, cardFactors (normalizedSexticSum u) :=
            Finset.sum_le_sum fun u hu => (Finset.mem_filter.mp hu).2
    omega
  have hsum_S₁ :
      E₁.card + 2 * E₂.card ≤ ∑ u ∈ S₁, cardFactors (normalizedSexticSum u) := by
    rw [hS₁_part, Finset.sum_union hdis_E₁_E₂]
    have h1 : E₁.card ≤ ∑ u ∈ E₁, cardFactors (normalizedSexticSum u) := by
      calc
        E₁.card = ∑ _u ∈ E₁, 1 := by simp
        _ ≤ ∑ u ∈ E₁, cardFactors (normalizedSexticSum u) := by
            refine Finset.sum_le_sum fun u hu => ?_
            rw [cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp hu).2]
    have h2 : 2 * E₂.card ≤ ∑ u ∈ E₂, cardFactors (normalizedSexticSum u) := by
      calc
        2 * E₂.card = ∑ _u ∈ E₂, 2 := by simp [Nat.mul_comm]
        _ ≤ ∑ u ∈ E₂, cardFactors (normalizedSexticSum u) :=
            Finset.sum_le_sum fun u hu => (Finset.mem_filter.mp hu).2
    omega
  have hsum_Q :
      ∑ u ∈ Q, cardFactors (normalizedSexticSum u) =
        ∑ u ∈ S₀, cardFactors (normalizedSexticSum u) +
          ∑ u ∈ S₁, cardFactors (normalizedSexticSum u) :=
    Finset.sum_union hdis_Q
  let Up₇ := (Q ×ˢ T₇).filter fun uw => uw.1 < uw.2 ∧ uw.2 ∣ normalizedSexticSum uw.1
  let U_up := D₁ ∪ D₂₅ ∪ E₁
  have hdis_D₁₂₅_E₁ : Disjoint (D₁ ∪ D₂₅) E₁ := by
    apply Finset.disjoint_left.mpr
    intro u h125 he1
    have huS₁ := (Finset.mem_filter.mp he1).1
    rcases Finset.mem_union.mp h125 with h1 | h25
    · exact Finset.disjoint_left.mp hdis_Q (Finset.mem_filter.mp h1).1 huS₁
    · exact Finset.disjoint_left.mp hdis_Q (Finset.mem_filter.mp h25).1 huS₁
  have hU_up_card : U_up.card = D₁.card + D₂₅.card + E₁.card := by
    dsimp only [U_up]
    rw [Finset.card_union_of_disjoint hdis_D₁₂₅_E₁, Finset.card_union_of_disjoint hdis_D₁_D₂₅]
  have hU_up_sub : U_up ⊆ Up₇.image Prod.fst := by
    intro u hu
    rw [Finset.mem_image]
    rcases Finset.mem_union.mp hu with hD | hE₁
    · rcases Finset.mem_union.mp hD with huD₁ | huD₂₅
      · obtain ⟨huS₀, hwp⟩ := Finset.mem_filter.mp huD₁
        have huQ : u ∈ Q := Finset.mem_union_left _ huS₀
        have hu3 := (hsource huQ).2.1
        have hu_mod : u % 7 ≠ 1 := (Finset.mem_filter.mp huS₀).2.2
        let w := normalizedSexticSum u
        have hwT : w ∈ T₇ := hcover u huQ (Nat.mem_primeFactors.mpr ⟨hwp, dvd_rfl, hwp.ne_zero⟩)
        have hlt : u < w := by
          have hnorm : w = u ^ 6 + u ^ 5 + u ^ 4 + u ^ 3 + u ^ 2 + u + 1 := by
            simp [w, normalizedSexticSum, hu_mod, geometricBlock_seven_eq]
          have hsq : 3 * u ≤ u ^ 2 := by nlinarith
          rw [hnorm]
          omega
        exact ⟨(u, w), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huQ, hwT⟩, hlt, dvd_rfl⟩, rfl⟩
      · obtain ⟨huS₀, h25⟩ := Finset.mem_filter.mp huD₂₅
        have huQ : u ∈ Q := Finset.mem_union_left _ huS₀
        have hu3 := (hsource huQ).2.1
        have hu_mod : u % 7 ≠ 1 := (Finset.mem_filter.mp huS₀).2.2
        obtain ⟨w, hw_pf, huw⟩ := sextic_zero_exists_gt_of_cardFactors_le_five hu3 hu_mod h25.2
        exact ⟨(u, w), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨huQ, hcover u huQ hw_pf⟩, huw, Nat.dvd_of_mem_primeFactors hw_pf⟩, rfl⟩
    · obtain ⟨huS₁, hwp⟩ := Finset.mem_filter.mp hE₁
      have huQ : u ∈ Q := Finset.mem_union_right _ huS₁
      have hu3 := (hsource huQ).2.1
      have hu_mod : u % 7 = 1 := (Finset.mem_filter.mp huS₁).2.2
      let w := normalizedSexticSum u
      have hwT : w ∈ T₇ := hcover u huQ (Nat.mem_primeFactors.mpr ⟨hwp, dvd_rfl, hwp.ne_zero⟩)
      have hlt : u < w := normalizedSexticSum_gt_self_of_mod_one hu3 hu_mod
      exact ⟨(u, w), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huQ, hwT⟩, hlt, dvd_rfl⟩, rfl⟩
  have hUp_lower : D₁.card + D₂₅.card + E₁.card ≤ Up₇.card := by
    rw [← hU_up_card]
    exact (Finset.card_le_card hU_up_sub).trans Finset.card_image_le
  let T_D₁ := D₁.image normalizedSexticSum
  have hT_D₁_sub : T_D₁ ⊆ T₇ := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨huS₀, hwp⟩ := Finset.mem_filter.mp hu
    exact hcover u (Finset.mem_union_left _ huS₀)
      (Nat.mem_primeFactors.mpr ⟨hwp, dvd_rfl, hwp.ne_zero⟩)
  have hT_D₁_card : T_D₁.card = D₁.card := by
    apply Finset.card_image_of_injOn
    intro u hu v hv heq
    have hu_mod : u % 7 ≠ 1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2.2
    have hv_mod : v % 7 ≠ 1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2.2
    exact normalizedSexticSum_strictMono_of_mod_ne_one hu_mod hv_mod heq
  have hUp_fiber : Up₇.card = ∑ w ∈ T₇, (Up₇.filter fun uw => uw.2 = w).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro uw huw
    exact (Finset.mem_product.mp (Finset.mem_filter.mp huw).1).2
  have hfiber_le (w : ℕ) :
      (Up₇.filter fun uw => uw.2 = w).card ≤
        (Q.filter fun v => v < w ∧ w ∣ normalizedSexticSum v).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro uw huw
      obtain ⟨huw_Up, rfl⟩ := Finset.mem_filter.mp huw
      obtain ⟨huw_prod, hlt, hdvd⟩ := Finset.mem_filter.mp huw_Up
      exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp huw_prod).1, hlt, hdvd⟩
    · intro x hx y hy hxy
      obtain ⟨_, hx2⟩ := Finset.mem_filter.mp hx
      obtain ⟨_, hy2⟩ := Finset.mem_filter.mp hy
      exact Prod.ext hxy (hx2.trans hy2.symm)
  have hfiber_T_D₁ : ∀ w ∈ T_D₁, (Up₇.filter fun uw => uw.2 = w).card ≤ 1 := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨huS₀, hwp⟩ := Finset.mem_filter.mp hu
    have huQ : u ∈ Q := Finset.mem_union_left _ huS₀
    have hup := (hsource huQ).1
    have hu_mod : u % 7 ≠ 1 := (Finset.mem_filter.mp huS₀).2.2
    have hw_eq : normalizedSexticSum u = geometricBlock u 7 := by
      simp [normalizedSexticSum, hu_mod]
    have hsub :
        (Q.filter fun v => v < normalizedSexticSum u ∧ normalizedSexticSum u ∣ normalizedSexticSum v) ⊆
          {u} := by
      intro v hv
      obtain ⟨hvQ, hvw, hdvd⟩ := Finset.mem_filter.mp hv
      have hvp := (hsource hvQ).1
      rw [Finset.mem_singleton]
      rw [hw_eq] at hvw hdvd hwp
      exact geometricBlock_prime_root_unique hup (by decide : Nat.Prime 7) (by decide : 3 ≤ 7)
        hwp hvp hvw (hdvd.trans (normalizedSexticSum_dvd_geometricBlock v))
    exact (hfiber_le _).trans ((Finset.card_le_card hsub).trans (by simp))
  have hfiber_other : ∀ w ∈ T₇ \ T_D₁, (Up₇.filter fun uw => uw.2 = w).card ≤ 6 := by
    intro w hw
    have hwT : w ∈ T₇ := (Finset.mem_sdiff.mp hw).1
    have hwp : w.Prime := Nat.prime_of_mem_primeFactors (hT_sub hwT)
    by_cases hw7 : w = 7
    · subst hw7
      have hempty : Q.filter (fun v => v < 7 ∧ 7 ∣ normalizedSexticSum v) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro v hv
        obtain ⟨hvQ, _, hdvd⟩ := Finset.mem_filter.mp hv
        obtain ⟨hvp, hv3, _⟩ := hsource hvQ
        exact (sextic_sigma_properties hvp hv3).2.1 hdvd
      exact (hfiber_le 7).trans (by rw [hempty]; simp)
    · have hsub :
          (Q.filter fun v => v < w ∧ w ∣ normalizedSexticSum v) ⊆
            (Finset.range w).filter (fun x => w ∣ geometricBlock x 7) := by
        intro v hv
        obtain ⟨_, hvw, hdvd⟩ := Finset.mem_filter.mp hv
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hvw, hdvd.trans (normalizedSexticSum_dvd_geometricBlock v)⟩
      exact (hfiber_le w).trans
        ((Finset.card_le_card hsub).trans
          (card_range_dvd_geometricBlock_le_pred (by decide : Nat.Prime 7) hwp hw7))
  have hUp_upper : Up₇.card + 5 * D₁.card ≤ 6 * T₇.card := by
    have hsdiff := Finset.sum_sdiff hT_D₁_sub (f := fun w => (Up₇.filter fun uw => uw.2 = w).card)
    have h1 : ∑ w ∈ T_D₁, (Up₇.filter fun uw => uw.2 = w).card ≤ T_D₁.card := by
      calc
        _ ≤ ∑ _w ∈ T_D₁, 1 := Finset.sum_le_sum hfiber_T_D₁
        _ = T_D₁.card := by simp
    have h2 : ∑ w ∈ T₇ \ T_D₁, (Up₇.filter fun uw => uw.2 = w).card ≤ 6 * (T₇ \ T_D₁).card := by
      calc
        _ ≤ ∑ _w ∈ T₇ \ T_D₁, 6 := Finset.sum_le_sum hfiber_other
        _ = 6 * (T₇ \ T_D₁).card := by simp [Nat.mul_comm]
    have hcard_sdiff : T_D₁.card + (T₇ \ T_D₁).card = T₇.card := by
      rw [← Finset.card_union_of_disjoint disjoint_sdiff_self_right,
        Finset.union_sdiff_of_subset hT_D₁_sub]
    omega
  change 11 * S₀.card + 6 * S₁.card ≤ 5 * (∑ r ∈ T₇, N.factorization r) + 6 * T₇.card
  omega

/-! ## 4. Multi-Block Coupled Slope (`l = 3` + `l = 5`) Above Zelinsky `302/113` -/

private theorem multi_block_source_counts {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) (h5 : ¬ 5 ∣ N) :
    (554 * N.primeFactors.card ≤
      199 * N.primeFactorsList.length + 595 +
        112 * ((squareSources N).filter (· % 5 = 1)).card) ∧
    ((∀ r ∈ largeSources N q, N.factorization r = 4) →
      5 * (largeSources N q).card ≤ 4 + 2 * N.factorization q +
        8 * ((squareSources N).filter (· % 5 = 1)).card ∧
      3 * (squareSources N).card ≤ 2 + N.factorization q + 6 * (largeSources N q).card ∧
      N.primeFactors.card = 1 + (squareSources N).card + (largeSources N q).card) := by
  let S := squareSources N
  let Q₀ := quarticSourcesZero N q
  let Q₁ := quarticSourcesOne N q
  let L := largeSources N q
  let R := L.filter fun r => 6 ≤ N.factorization r
  let R₅ := R.filter fun r => r % 5 = 1
  let R₀ := R.filter fun r => r % 5 ≠ 1
  let S₅₁ := S.filter fun r => r % 5 = 1
  let T₅ := oneModFiveTargets N q
  have hpos {r : ℕ} (hr : r ∈ N.primeFactors) : 0 < N.factorization r :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
  have hQ₁_zero : Q₁.card = 0 := by
    have hb : Q₁.card ≤ N.factorization 5 :=
      quarticSourcesOne_card_le_five_exponent (N := N) (q := q) hN
    have hz : N.factorization 5 = 0 := Nat.factorization_eq_zero_of_not_dvd h5
    omega
  have hQ₁_empty : Q₁ = ∅ := Finset.card_eq_zero.mp hQ₁_zero
  have hS1_zero : (squareSourcesOne N).card = 0 := by
    have hb := squareSourcesOne_card_le_three_exponent hN
    have hz : N.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd h3
    omega
  have hS_eq_S2 : S = squareSourcesTwo N := by
    dsimp only [S]
    rw [squareSources_eq_union_one_two N, Finset.card_eq_zero.mp hS1_zero, Finset.empty_union]
  have h3not : 3 ∉ N.primeFactors := fun h => h3 (Nat.dvd_of_mem_primeFactors h)
  have h5not : 5 ∉ N.primeFactors := fun h => h5 (Nat.dvd_of_mem_primeFactors h)
  have hL_part : L = Q₀ ∪ R := by
    ext r
    simp only [L, largeSources, Q₀, quarticSourcesZero, R, Finset.mem_union, Finset.mem_filter,
      Finset.mem_erase]
    constructor
    · intro ⟨hr, hr3, hrq, hge4⟩
      obtain ⟨k, hk⟩ := hev r hrq
      by_cases h4 : N.factorization r = 4
      · by_cases hm5 : r % 5 = 1
        · exfalso
          have hmem : r ∈ Q₁ := Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hrq, hr⟩, h4, hm5⟩
          rw [hQ₁_empty] at hmem
          exact Finset.notMem_empty _ hmem
        · exact Or.inl ⟨⟨hrq, hr⟩, h4, hm5⟩
      · exact Or.inr ⟨⟨hr, hr3, hrq, hge4⟩, by omega⟩
    · rintro (⟨⟨hrq, hr⟩, h4, _⟩ | ⟨⟨hr, hr3, hrq, hge4⟩, _⟩)
      · exact ⟨hr, fun h => by subst r; exact h3not hr, hrq, by omega⟩
      · exact ⟨hr, hr3, hrq, hge4⟩
  have hdis_QR : Disjoint Q₀ R := by
    apply Finset.disjoint_left.mpr
    intro r hq0 hr
    have h4 := (Finset.mem_filter.mp hq0).2.1
    have h6 := (Finset.mem_filter.mp hr).2
    omega
  have hR_part : R = R₅ ∪ R₀ := by
    ext r
    simp only [R₅, R₀, Finset.mem_union, Finset.mem_filter]
    by_cases h : r % 5 = 1 <;> tauto
  have hdis_R : Disjoint R₅ R₀ := by
    apply Finset.disjoint_left.mpr
    intro r h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hSL_parts : N.primeFactors.erase q = S ∪ L := by
    ext r
    simp only [Finset.mem_erase, S, squareSources, L, largeSources, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hrq, hr⟩
      have hr3 : r ≠ 3 := fun h => by subst r; exact h3not hr
      have := hpos hr
      obtain ⟨k, hk⟩ := hev r hrq
      by_cases h2 : N.factorization r = 2
      · exact Or.inl ⟨hr, hr3, h2⟩
      · exact Or.inr ⟨hr, hr3, hrq, by omega⟩
    · rintro (⟨hr, _, h2⟩ | ⟨hr, _, hrq, _⟩)
      · exact ⟨fun h => by subst r; omega, hr⟩
      · exact ⟨hrq, hr⟩
  have hdis_SL : Disjoint S L := by
    apply Finset.disjoint_left.mpr
    intro r hs hl
    have h2 := (Finset.mem_filter.mp hs).2.2
    have h4 := (Finset.mem_filter.mp hl).2.2.2
    omega
  have hT5_sub : T₅ ⊆ insert q (S₅₁ ∪ R₅) := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | h
    · exact Finset.mem_insert.mpr (Or.inl rfl)
    apply Finset.mem_insert_of_mem
    obtain ⟨hr_er, hm5⟩ := Finset.mem_filter.mp h
    rw [hSL_parts, Finset.mem_union] at hr_er
    rcases hr_er with hrS | hrL
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hrS, hm5⟩)
    · rw [hL_part, Finset.mem_union] at hrL
      rcases hrL with hrQ0 | hrR
      · exfalso
        exact (Finset.mem_filter.mp hrQ0).2.2 hm5
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hrR, hm5⟩)
  have hT5_card_le : T₅.card ≤ 1 + S₅₁.card + R₅.card := by
    have hle := Finset.card_le_card hT5_sub
    have h1 := Finset.card_insert_le q (S₅₁ ∪ R₅)
    have h2 := Finset.card_union_le S₅₁ R₅
    omega
  have hT5_sum_le : ∑ r ∈ T₅, N.factorization r ≤
      N.factorization q + ∑ r ∈ S₅₁, N.factorization r + ∑ r ∈ R₅, N.factorization r := by
    calc
      ∑ r ∈ T₅, N.factorization r ≤ ∑ r ∈ insert q (S₅₁ ∪ R₅), N.factorization r :=
          Finset.sum_le_sum_of_subset hT5_sub
      _ ≤ N.factorization q + ∑ r ∈ S₅₁ ∪ R₅, N.factorization r := by
          by_cases hq_mem : q ∈ S₅₁ ∪ R₅
          · rw [Finset.insert_eq_of_mem hq_mem]
            omega
          · rw [Finset.sum_insert hq_mem]
      _ ≤ N.factorization q + (∑ r ∈ S₅₁, N.factorization r + ∑ r ∈ R₅, N.factorization r) := by
          have := Finset.sum_union_inter (f := N.factorization) (s₁ := S₅₁) (s₂ := R₅)
          omega
      _ = N.factorization q + ∑ r ∈ S₅₁, N.factorization r + ∑ r ∈ R₅, N.factorization r := by
          ring
  have hS51_sum : ∑ r ∈ S₅₁, N.factorization r = 2 * S₅₁.card := by
    calc
      ∑ r ∈ S₅₁, N.factorization r = ∑ _r ∈ S₅₁, (2 : ℕ) :=
        Finset.sum_congr rfl fun r hr => (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.2
      _ = 2 * S₅₁.card := by simp [Nat.mul_comm]
  have hQ5 := quarticSources_sharpened_incidence ho hN hq
  change 5 * Q₀.card + 3 * Q₁.card ≤
    2 * (∑ r ∈ T₅, N.factorization r) + 4 * T₅.card at hQ5
  rw [hQ₁_zero, mul_zero, add_zero] at hQ5
  have hQ5_bound : 5 * Q₀.card ≤
      4 + 2 * N.factorization q + 8 * S₅₁.card + 2 * (∑ r ∈ R₅, N.factorization r) + 4 * R₅.card := by
    omega
  have h3inc := squareSources_vieta_root_slot_incidence_three_free ho hN hq hq4 he hev h3
  have hL1_sub : oneModThreeLargeSources N q ⊆ L := Finset.filter_subset _ _
  have hL1_card_le : (oneModThreeLargeSources N q).card ≤ L.card := Finset.card_le_card hL1_sub
  have hL1_sum_le : ∑ r ∈ oneModThreeLargeSources N q, N.factorization r ≤
      ∑ r ∈ L, N.factorization r := Finset.sum_le_sum_of_subset hL1_sub
  have hQ0_sum : ∑ r ∈ Q₀, N.factorization r = 4 * Q₀.card := by
    calc
      ∑ r ∈ Q₀, N.factorization r = ∑ _r ∈ Q₀, (4 : ℕ) :=
        Finset.sum_congr rfl fun r hr => (Finset.mem_filter.mp hr).2.1
      _ = 4 * Q₀.card := by simp [Nat.mul_comm]
  have hL_card : L.card = Q₀.card + R₅.card + R₀.card := by
    rw [hL_part, Finset.card_union_of_disjoint hdis_QR, hR_part, Finset.card_union_of_disjoint hdis_R]
    ring
  have hL_sum : ∑ r ∈ L, N.factorization r =
      4 * Q₀.card + ∑ r ∈ R₅, N.factorization r + ∑ r ∈ R₀, N.factorization r := by
    rw [hL_part, Finset.sum_union hdis_QR, hQ0_sum, hR_part, Finset.sum_union hdis_R]
    ring
  have hS_sum : ∑ r ∈ S, N.factorization r = 2 * S.card := by
    calc
      ∑ r ∈ S, N.factorization r = ∑ _r ∈ S, (2 : ℕ) :=
        Finset.sum_congr rfl fun r hr => (Finset.mem_filter.mp hr).2.2
      _ = 2 * S.card := by simp [Nat.mul_comm]
  have hR5_ge : 6 * R₅.card ≤ ∑ r ∈ R₅, N.factorization r := by
    calc
      6 * R₅.card = ∑ _r ∈ R₅, (6 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ ∑ r ∈ R₅, N.factorization r := Finset.sum_le_sum fun r hr =>
          (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2
  have hR0_ge : 6 * R₀.card ≤ ∑ r ∈ R₀, N.factorization r := by
    calc
      6 * R₀.card = ∑ _r ∈ R₀, (6 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ ∑ r ∈ R₀, N.factorization r := Finset.sum_le_sum fun r hr =>
          (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2
  have hcard_tot : N.primeFactors.card = 1 + S.card + L.card := by
    have := Finset.card_erase_add_one hq
    rw [hSL_parts, Finset.card_union_of_disjoint hdis_SL] at this
    omega
  have htot : N.primeFactorsList.length =
      N.factorization q + 2 * S.card + ∑ r ∈ L, N.factorization r := by
    have htot1 : N.primeFactorsList.length =
        N.factorization q + ∑ r ∈ N.primeFactors.erase q, N.factorization r := by
      rw [← cardFactors_apply, cardFactors_eq_sum_factorization]
      exact (Finset.add_sum_erase N.primeFactors _ hq).symm
    rw [hSL_parts, Finset.sum_union hdis_SL, hS_sum] at htot1
    omega
  have hS_bound : 3 * S.card ≤
      2 + N.factorization q + 6 * Q₀.card + 2 * R₅.card + 2 * R₀.card +
        ∑ r ∈ R₅, N.factorization r + ∑ r ∈ R₀, N.factorization r := by
    rw [← hS_eq_S2] at h3inc
    linarith [h3inc, hL1_card_le, hL1_sum_le, hL_card, hL_sum]
  have hq_ge1 : 1 ≤ N.factorization q := hpos hq
  have hscaled : 5 * (554 * N.primeFactors.card) ≤
      5 * (199 * N.primeFactorsList.length + 595 + 112 * S₅₁.card) := by
    linarith [hS_bound, hQ5_bound, hR5_ge, hR0_ge, hcard_tot, hL_card, htot, hL_sum, hq_ge1]
  constructor
  · change 554 * N.primeFactors.card ≤ 199 * N.primeFactorsList.length + 595 + 112 * S₅₁.card
    omega
  · intro hfour
    have hR : R = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      obtain ⟨hrL, hr6⟩ := Finset.mem_filter.mp hr
      have hr4 := hfour r hrL
      omega
    have hR₅ : R₅ = ∅ := by simp [R₅, hR]
    have hR₀ : R₀ = ∅ := by simp [R₀, hR]
    simp only [hR₅, hR₀, Finset.card_empty, Finset.sum_empty, mul_zero, add_zero]
      at hQ5_bound hS_bound hL_card
    change 5 * L.card ≤ 4 + 2 * N.factorization q + 8 * S₅₁.card ∧
      3 * S.card ≤ 2 + N.factorization q + 6 * L.card ∧
      N.primeFactors.card = 1 + S.card + L.card
    exact ⟨by omega, by omega, hcard_tot⟩

/-- Coupled `3, 5`-free multi-block slope retaining `((squareSources N).filter (· % 5 = 1)).card`
and `quarticSourcesZero N q` slack. -/
theorem multi_block_coupled_three_five_free {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) (h5 : ¬ 5 ∣ N) :
    554 * N.primeFactors.card ≤
      199 * N.primeFactorsList.length + 595 +
        112 * ((squareSources N).filter (· % 5 = 1)).card :=
  (multi_block_source_counts ho hN hq hq4 he hev h3 h5).1

/-- When the non-Euler exponents are two or four, the quartic and square
incidences also bound the number of exact-square sources congruent to one
modulo five from below. -/
theorem three_five_free_quartic_source_bounds {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) (h5 : ¬ 5 ∣ N)
    (hfour : ∀ r ∈ largeSources N q, N.factorization r = 4) :
    5 * (largeSources N q).card ≤ 4 + 2 * N.factorization q +
        8 * ((squareSources N).filter (· % 5 = 1)).card ∧
      3 * (squareSources N).card ≤ 2 + N.factorization q + 6 * (largeSources N q).card ∧
      N.primeFactors.card = 1 + (squareSources N).card + (largeSources N q).card :=
  (multi_block_source_counts ho hN hq hq4 he hev h3 h5).2 hfour

/-- When `¬ 3 ∣ N`, `¬ 5 ∣ N`, and `∀ u ∈ squareSources N, u % 5 ≠ 1`, the coupled `l = 3` and
`l = 5` root-slot bounds yield **`554 * ω(N) ≤ 199 * Ω(N) + 595`** (slope `554/199 ≈ 2.7839`,
strictly exceeding Zelinsky's `302/113 ≈ 2.6726`). -/
theorem multi_block_slope_above_zelinsky {N : ℕ} (ho : Odd N) (hN : N.Perfect)
    (h3 : ¬ 3 ∣ N) (h5 : ¬ 5 ∣ N)
    (hdisj : ∀ u ∈ squareSources N, u % 5 ≠ 1) :
    554 * N.primeFactors.card ≤ 199 * N.primeFactorsList.length + 595 := by
  obtain ⟨q, hq, hq4, he, hev⟩ := euler_exponents ho hN
  have hcoupled := multi_block_coupled_three_five_free ho hN hq hq4 he hev h3 h5
  have hempty : (squareSources N).filter (· % 5 = 1) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro u hu
    obtain ⟨huS, hm5⟩ := Finset.mem_filter.mp hu
    exact hdisj u huS hm5
  rw [hempty, Finset.card_empty, mul_zero, add_zero] at hcoupled
  exact hcoupled

/-- Least-prime logarithmic and exponential size pinch instantiated for the coupled
multi-block slope `554 * ω(N) ≤ 199 * Ω(N) + 595`. -/
theorem multi_block_least_prime_pinch_above_zelinsky {N p : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) (hmin : ∀ s ∈ N.primeFactors, p ≤ s)
    (h3 : ¬ 3 ∣ N) (h5 : ¬ 5 ∣ N) (hdisj : ∀ u ∈ squareSources N, u % 5 ≠ 1) :
    (554 * ((p : ℝ) - 1) * Real.log 2 - 595) / 199 < (N.primeFactorsList.length : ℝ) ∧
      p ^ N.primeFactorsList.length ≤ N := by
  simpa using total_prime_factors_and_size_of_slope_and_least_prime ho hN hp hmin
    (by decide : 0 < 199) (multi_block_slope_above_zelinsky ho hN h3 h5 hdisj)

end OddPerfect
