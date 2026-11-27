module

public import OddPerfect.ZelinskySlope
public import OddPerfect.Transfer
public import OddPerfect.GeometricSquareClass
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Universal Cyclotomic Root-Saturation and Quartic Incidence Bound

Proves the universal cyclotomic root-saturation theorem across all odd prime lengths `l ≥ 3`:
1. `card_range_dvd_geometricBlock_le_pred`: for primes `l ≠ w`, at most `l - 1` residues
   `x ∈ Finset.range w` satisfy `w ∣ geometricBlock x l`.
2. `geometricBlock_prime_root_unique`: if `u` is prime, `l ≥ 3` is prime, and
   `w = geometricBlock u l` is prime, then `u` is the unique prime `v < w` satisfying
   `w ∣ geometricBlock v l`.
3. `quarticSources_root_slot_incidence`: instantiation at `l = 5` on `quarticSourcesZero N q`
   and `quarticSourcesOne N q`, yielding
   `7 * |Q₀| + 4 * |Q₁| ≤ 3 * ∑ r ∈ T₅, N.factorization r + 4 * |T₅|`.
-/

public section

namespace OddPerfect

open ArithmeticFunction

/-! ## 1. Universal Cyclotomic Root Cap and Prime-Root Uniqueness -/

/-- For distinct primes `l` and `w`, the congruence `geometricBlock x l ≡ 0 [MOD w]` has at most
`l - 1` solutions in `Finset.range w`. -/
theorem card_range_dvd_geometricBlock_le_pred {l w : ℕ}
    (hl : l.Prime) (hw : w.Prime) (hwl : w ≠ l) :
    ((Finset.range w).filter (fun x => w ∣ geometricBlock x l)).card ≤ l - 1 := by
  let : Fact w.Prime := ⟨hw⟩
  let P : Polynomial (ZMod w) := Polynomial.X ^ l - Polynomial.C 1
  have hP_ne : P ≠ 0 := Polynomial.X_pow_sub_C_ne_zero hl.pos (1 : ZMod w)
  have hroots_le : P.roots.toFinset.card ≤ l :=
    (Multiset.toFinset_card_le _).trans (Polynomial.card_roots_X_pow_sub_C hl.pos (1 : ZMod w))
  have h1_mem : (1 : ZMod w) ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP_ne, Polynomial.IsRoot]
    simp [P]
  have herase_card : (P.roots.toFinset.erase 1).card + 1 = P.roots.toFinset.card :=
    Finset.card_erase_add_one h1_mem
  have hle : ((Finset.range w).filter (fun x => w ∣ geometricBlock x l)).card ≤
      (P.roots.toFinset.erase 1).card := by
    apply Finset.card_le_card_of_injOn (fun x : ℕ => (x : ZMod w))
    · intro x hx
      obtain ⟨hx_range, hx_dvd⟩ := Finset.mem_filter.mp hx
      have hx_geom : (geometricBlock x l : ZMod w) = 0 :=
        (ZMod.natCast_eq_zero_iff (geometricBlock x l) w).mpr hx_dvd
      have hx_sum : (∑ j ∈ Finset.range l, (x : ZMod w) ^ j) = 0 := by
        simpa [geometricBlock] using hx_geom
      have hx_ne1 : (x : ZMod w) ≠ 1 := by
        intro hx1
        have hl_zero : (l : ZMod w) = 0 := by
          simpa [hx1] using hx_sum
        have hwl_dvd : w ∣ l := (ZMod.natCast_eq_zero_iff l w).mp hl_zero
        exact hwl ((Nat.prime_dvd_prime_iff_eq hw hl).mp hwl_dvd)
      have hx_root : P.IsRoot (x : ZMod w) := by
        rw [Polynomial.IsRoot]
        simp only [P, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
        rw [← geom_sum_mul (x : ZMod w) l, hx_sum, zero_mul]
      exact Finset.mem_erase.mpr
        ⟨hx_ne1, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP_ne).mpr hx_root)⟩
    · intro x hx y hy hxy
      have hx_lt : x < w := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
      have hy_lt : y < w := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
      have hval := congrArg ZMod.val hxy
      rwa [ZMod.val_natCast_of_lt hx_lt, ZMod.val_natCast_of_lt hy_lt] at hval
  omega

private lemma lt_sum_range_two_pow {n : ℕ} (hn : 3 ≤ n) : n < ∑ j ∈ Finset.range n, 2 ^ j := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
      rw [Finset.sum_range_succ]
      have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
      omega

/-- If `u` is prime, `l ≥ 3` is prime, and `w = geometricBlock u l` is prime, then `u` is the
unique prime `v < w` satisfying `w ∣ geometricBlock v l`. -/
theorem geometricBlock_prime_root_unique {u l v : ℕ}
    (hu : u.Prime) (hl : l.Prime) (hl3 : 3 ≤ l)
    (hw : (geometricBlock u l).Prime)
    (hv : v.Prime) (hvw : v < geometricBlock u l)
    (hdvd : geometricBlock u l ∣ geometricBlock v l) :
    v = u := by
  let w := geometricBlock u l
  have hw_ne_l : w ≠ l := by
    have hlt : l < w := by
      calc
        l < ∑ j ∈ Finset.range l, 2 ^ j := lt_sum_range_two_pow hl3
        _ ≤ ∑ j ∈ Finset.range l, u ^ j :=
            Finset.sum_le_sum fun j _ => Nat.pow_le_pow_left hu.two_le j
        _ = w := rfl
    exact hlt.ne'
  let S_roots := (Finset.Icc 1 (l - 1)).image (fun k => u ^ k)
  let F := (Finset.range w).filter (fun x => w ∣ geometricBlock x l)
  have hS_card : S_roots.card = l - 1 := by
    rw [Finset.card_image_of_injective _ (Nat.pow_right_injective hu.two_le), Nat.card_Icc]
    omega
  have hS_sub : S_roots ⊆ F := by
    let : Fact w.Prime := ⟨hw⟩
    have hu_pow_l : (u : ZMod w) ^ l = 1 := by
      have hw_geom : (geometricBlock u l : ZMod w) = 0 :=
        (ZMod.natCast_eq_zero_iff (geometricBlock u l) w).mpr dvd_rfl
      have hsum : (∑ j ∈ Finset.range l, (u : ZMod w) ^ j) = 0 := by
        simpa [geometricBlock] using hw_geom
      apply sub_eq_zero.mp
      rw [← geom_sum_mul (u : ZMod w) l, hsum, zero_mul]
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hk1, hkl⟩ := Finset.mem_Icc.mp hk
    have hk_lt_l : k < l := by omega
    have hpow_gt1 : 1 < u ^ k := by
      calc
        1 < u := hu.one_lt
        _ = u ^ 1 := (pow_one u).symm
        _ ≤ u ^ k := Nat.pow_le_pow_right hu.pos hk1
    have hpow_lt_w : u ^ k < w := by
      have hsub_range : ({0, k} : Finset ℕ) ⊆ Finset.range l := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        · exact Finset.mem_range.mpr hl.pos
        · exact Finset.mem_range.mpr hk_lt_l
      have hsum_le := Finset.sum_le_sum_of_subset hsub_range (f := fun j => u ^ j)
      rw [Finset.sum_pair (by omega : 0 ≠ k), pow_zero] at hsum_le
      change 1 + u ^ k ≤ w at hsum_le
      omega
    have hx_ne1 : ((u ^ k : ℕ) : ZMod w) ≠ 1 := by
      intro h1
      have hval := congrArg ZMod.val h1
      rw [ZMod.val_natCast_of_lt hpow_lt_w, ZMod.val_one] at hval
      omega
    have hpow_k_l : ((u ^ k : ℕ) : ZMod w) ^ l = 1 := by
      push_cast
      rw [← pow_mul, mul_comm k l, pow_mul, hu_pow_l, one_pow]
    have hgeom_zero : (geometricBlock (u ^ k) l : ZMod w) = 0 := by
      have hprod : (∑ j ∈ Finset.range l, ((u ^ k : ℕ) : ZMod w) ^ j) *
          (((u ^ k : ℕ) : ZMod w) - 1) = 0 := by
        rw [geom_sum_mul, hpow_k_l, sub_self]
      have hsub_ne : ((u ^ k : ℕ) : ZMod w) - 1 ≠ 0 := sub_ne_zero.mpr hx_ne1
      simpa [geometricBlock] using (mul_eq_zero.mp hprod).resolve_right hsub_ne
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hpow_lt_w, (ZMod.natCast_eq_zero_iff _ w).mp hgeom_zero⟩
  have hF_card : F.card ≤ l - 1 := card_range_dvd_geometricBlock_le_pred hl hw hw_ne_l
  have heq : S_roots = F := Finset.eq_of_subset_of_card_le hS_sub (hF_card.trans hS_card.ge)
  have hv_mem : v ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hvw, hdvd⟩
  rw [← heq] at hv_mem
  obtain ⟨k, hk, hkv⟩ := Finset.mem_image.mp hv_mem
  obtain ⟨hk1, _⟩ := Finset.mem_Icc.mp hk
  by_cases hk_eq : k = 1
  · subst hk_eq
    simpa using hkv.symm
  · exfalso
    have hk2 : 2 ≤ k := by omega
    have hdiv : u ∣ v := by
      rw [← hkv]
      exact dvd_pow_self u (by omega)
    rcases hv.eq_one_or_self_of_dvd u hdiv with h1 | huv
    · exact hu.ne_one h1
    · have hlt : u < u ^ k := by
        calc
          u < u * u := lt_mul_of_one_lt_right hu.pos hu.one_lt
          _ = u ^ 2 := (pow_two u).symm
          _ ≤ u ^ k := Nat.pow_le_pow_right hu.pos hk2
      rw [hkv] at hlt
      exact huv.not_lt hlt

/-! ## 2. Quartic Root-Slot Incidence Bound (`l = 5`) -/

/-- Non-Euler primes with exact exponent 4 that are not congruent to 1 modulo 5. -/
@[expose] def quarticSourcesZero (N q : ℕ) : Finset ℕ :=
  (N.primeFactors.erase q).filter (fun r => N.factorization r = 4 ∧ r % 5 ≠ 1)

/-- Potential target primes for quartic component sums: the Euler prime `q` together with
all non-Euler prime factors congruent to 1 modulo 5. -/
@[expose] def oneModFiveTargets (N q : ℕ) : Finset ℕ :=
  insert q ((N.primeFactors.erase q).filter (fun r => r % 5 = 1))

private lemma geometricBlock_five_eq (x : ℕ) :
    geometricBlock x 5 = x ^ 4 + x ^ 3 + x ^ 2 + x + 1 := by
  simp [geometricBlock, Finset.sum_range_succ]
  ring

private lemma normalizedQuarticSum_dvd_geometricBlock (x : ℕ) :
    normalizedQuarticSum x ∣ geometricBlock x 5 := by
  rw [geometricBlock_five_eq]
  by_cases hx : x % 5 = 1
  · obtain ⟨k, rfl⟩ : ∃ k, x = 5 * k + 1 := ⟨x / 5, by omega⟩
    have hnorm : normalizedQuarticSum (5 * k + 1) =
        125 * k ^ 4 + 125 * k ^ 3 + 50 * k ^ 2 + 10 * k + 1 := by
      rw [normalizedQuarticSum, ite_eq_left (show (5 * k + 1) % 5 = 1 by omega)]
      rw [show (5 * k + 1) ^ 4 + (5 * k + 1) ^ 3 + (5 * k + 1) ^ 2 + (5 * k + 1) + 1 =
          5 * (125 * k ^ 4 + 125 * k ^ 3 + 50 * k ^ 2 + 10 * k + 1) by ring]
      simp
    rw [hnorm]
    refine ⟨5, ?_⟩
    ring
  · simp [normalizedQuarticSum, hx]

private lemma normalizedQuarticSum_one_lt {u : ℕ} (hu3 : 3 ≤ u) :
    1 < normalizedQuarticSum u := by
  by_cases h5 : u % 5 = 1
  · simp only [normalizedQuarticSum, ite_eq_left h5]
    have hge : 10 ≤ u ^ 4 + u ^ 3 + u ^ 2 + u + 1 := by
      have h1 : 3 ≤ u := hu3
      have h2 : 9 ≤ u ^ 2 := by nlinarith
      omega
    omega
  · simp only [normalizedQuarticSum, ite_eq_right h5]
    have h2 : 9 ≤ u ^ 2 := by nlinarith
    omega

private lemma normalizedQuarticSum_gt_self_of_mod_one {u : ℕ} (hu3 : 3 ≤ u) (hu_mod : u % 5 = 1) :
    u < normalizedQuarticSum u := by
  simp only [normalizedQuarticSum, ite_eq_left hu_mod]
  have hsq : 3 * u ≤ u ^ 2 := by nlinarith
  have hcub : 9 * u ≤ u ^ 3 := by nlinarith
  have hfour : 27 * u ≤ u ^ 4 := by nlinarith
  omega

private lemma le_pow_cardFactors_of_primeFactors_le' {M u : ℕ} (hM : M ≠ 0)
    (h : ∀ w ∈ M.primeFactors, w ≤ u) : M ≤ u ^ cardFactors M := by
  calc
    M = ∏ w ∈ M.primeFactors, w ^ M.factorization w := Nat.prod_primeFactors_pow_factorization hM
    _ ≤ ∏ w ∈ M.primeFactors, u ^ M.factorization w :=
        Finset.prod_le_prod fun w hw => Nat.pow_le_pow_left (h w hw) _
    _ = u ^ ∑ w ∈ M.primeFactors, M.factorization w := Finset.prod_pow_eq_pow_sum _ _ _
    _ = u ^ cardFactors M := by
        rw [cardFactors_eq_sum_factorization]
        rfl

private lemma quartic_zero_exists_gt_of_cardFactors_le_three {u : ℕ} (hu3 : 3 ≤ u)
    (hu_mod : u % 5 ≠ 1) (hcard : cardFactors (normalizedQuarticSum u) ≤ 3) :
    ∃ w ∈ (normalizedQuarticSum u).primeFactors, u < w := by
  have hnorm : normalizedQuarticSum u = u ^ 4 + u ^ 3 + u ^ 2 + u + 1 := by
    simp [normalizedQuarticSum, hu_mod]
  by_contra! hle
  have hM_ne : normalizedQuarticSum u ≠ 0 := by rw [hnorm]; positivity
  have hbound := le_pow_cardFactors_of_primeFactors_le' hM_ne hle
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

private lemma normalizedQuarticSum_strictMono_of_mod_ne_one {u v : ℕ}
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

/-- **Quartic Root-Slot Incidence Bound (`l = 5`)**:
For an odd perfect number `N` with Euler prime `q`, partitioning non-Euler quartic components
into `Q₀ = quarticSourcesZero N q` (`r ≢ 1 [MOD 5]`) and `Q₁ = quarticSourcesOne N q`
(`r ≡ 1 [MOD 5]`) yields
`7 * |Q₀| + 4 * |Q₁| ≤ 3 * ∑ r ∈ T₅, N.factorization r + 4 * |T₅|`. -/
theorem quarticSources_root_slot_incidence {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) :
    7 * (quarticSourcesZero N q).card + 4 * (quarticSourcesOne N q).card ≤
      3 * (∑ r ∈ oneModFiveTargets N q, N.factorization r) +
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
  have hsource {u : ℕ} (hu : u ∈ Q) :
      u.Prime ∧ 3 ≤ u ∧ N.factorization u = 4 := by
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
    have hu4_dvd : u ^ 4 ∣ N := by
      simpa [h4] using Nat.ordProj_dvd N u
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
  -- Partition Q₀ into Ω = 1 (B₁), Ω ∈ {2, 3} (B₂₃), Ω ≥ 4 (B₄), and Q₁ into Ω = 1 (C₁), Ω ≥ 2 (C₂).
  let B₁ := Q₀.filter fun u => (normalizedQuarticSum u).Prime
  let B₂₃ := Q₀.filter fun u =>
    cardFactors (normalizedQuarticSum u) = 2 ∨ cardFactors (normalizedQuarticSum u) = 3
  let B₄ := Q₀.filter fun u => 4 ≤ cardFactors (normalizedQuarticSum u)
  let C₁ := Q₁.filter fun u => (normalizedQuarticSum u).Prime
  let C₂ := Q₁.filter fun u => 2 ≤ cardFactors (normalizedQuarticSum u)
  have hQ₀_part : Q₀ = B₁ ∪ B₂₃ ∪ B₄ := by
    ext u
    simp only [B₁, B₂₃, B₄, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hu
      have hu3 := (hsource (Finset.mem_union_left _ hu)).2.1
      have hpos := cardFactors_pos_iff_one_lt.mpr (normalizedQuarticSum_one_lt hu3)
      by_cases h1 : cardFactors (normalizedQuarticSum u) = 1
      · exact Or.inl (Or.inl ⟨hu, cardFactors_eq_one_iff_prime.mp h1⟩)
      · by_cases h23 : cardFactors (normalizedQuarticSum u) = 2 ∨
            cardFactors (normalizedQuarticSum u) = 3
        · exact Or.inl (Or.inr ⟨hu, h23⟩)
        · exact Or.inr ⟨hu, by omega⟩
    · rintro ((⟨hu, _⟩ | ⟨hu, _⟩) | ⟨hu, _⟩) <;> exact hu
  have hdis_B₁_B₂₃ : Disjoint B₁ B₂₃ := by
    apply Finset.disjoint_left.mpr
    intro u h1 h23
    have hp1 := cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp h1).2
    rcases (Finset.mem_filter.mp h23).2 with h2 | h3 <;> omega
  have hdis_B₁₂₃_B₄ : Disjoint (B₁ ∪ B₂₃) B₄ := by
    apply Finset.disjoint_left.mpr
    intro u h123 h4
    have hge4 := (Finset.mem_filter.mp h4).2
    rcases Finset.mem_union.mp h123 with h1 | h23
    · have hp1 := cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp h1).2
      omega
    · rcases (Finset.mem_filter.mp h23).2 with h2 | h3 <;> omega
  have hQ₀_card : Q₀.card = B₁.card + B₂₃.card + B₄.card := by
    rw [hQ₀_part, Finset.card_union_of_disjoint hdis_B₁₂₃_B₄, Finset.card_union_of_disjoint hdis_B₁_B₂₃]
  have hQ₁_part : Q₁ = C₁ ∪ C₂ := by
    ext u
    simp only [C₁, C₂, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hu
      have hu3 := (hsource (Finset.mem_union_right _ hu)).2.1
      have hpos := cardFactors_pos_iff_one_lt.mpr (normalizedQuarticSum_one_lt hu3)
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
      B₁.card + 2 * B₂₃.card + 4 * B₄.card ≤ ∑ u ∈ Q₀, cardFactors (normalizedQuarticSum u) := by
    rw [hQ₀_part, Finset.sum_union hdis_B₁₂₃_B₄, Finset.sum_union hdis_B₁_B₂₃]
    have h1 : B₁.card ≤ ∑ u ∈ B₁, cardFactors (normalizedQuarticSum u) := by
      calc
        B₁.card = ∑ _u ∈ B₁, 1 := by simp
        _ ≤ ∑ u ∈ B₁, cardFactors (normalizedQuarticSum u) := by
            refine Finset.sum_le_sum fun u hu => ?_
            rw [cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp hu).2]
    have h23 : 2 * B₂₃.card ≤ ∑ u ∈ B₂₃, cardFactors (normalizedQuarticSum u) := by
      calc
        2 * B₂₃.card = ∑ _u ∈ B₂₃, 2 := by simp [Nat.mul_comm]
        _ ≤ ∑ u ∈ B₂₃, cardFactors (normalizedQuarticSum u) := by
            refine Finset.sum_le_sum fun u hu => ?_
            rcases (Finset.mem_filter.mp hu).2 with h2 | h3 <;> omega
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
  -- Upward incidence graph Up₅ ⊆ Q ×ˢ T₅.
  let Up₅ := (Q ×ˢ T₅).filter fun uw => uw.1 < uw.2 ∧ uw.2 ∣ normalizedQuarticSum uw.1
  let U_up := B₁ ∪ B₂₃ ∪ C₁
  have hdis_B₁_C₁ : Disjoint B₁ C₁ :=
    Finset.disjoint_left.mpr fun u h1 h2 =>
      Finset.disjoint_left.mp hdis_Q (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2).1
  have hdis_B₁₂₃_C₁ : Disjoint (B₁ ∪ B₂₃) C₁ := by
    apply Finset.disjoint_left.mpr
    intro u h123 hc1
    have huQ₁ := (Finset.mem_filter.mp hc1).1
    rcases Finset.mem_union.mp h123 with h1 | h23
    · exact Finset.disjoint_left.mp hdis_Q (Finset.mem_filter.mp h1).1 huQ₁
    · exact Finset.disjoint_left.mp hdis_Q (Finset.mem_filter.mp h23).1 huQ₁
  have hU_up_card : U_up.card = B₁.card + B₂₃.card + C₁.card := by
    dsimp only [U_up]
    rw [Finset.card_union_of_disjoint hdis_B₁₂₃_C₁, Finset.card_union_of_disjoint hdis_B₁_B₂₃]
  have hU_up_sub : U_up ⊆ Up₅.image Prod.fst := by
    intro u hu
    rw [Finset.mem_image]
    rcases Finset.mem_union.mp hu with hB | hC₁
    · rcases Finset.mem_union.mp hB with huB₁ | huB₂₃
      · obtain ⟨huQ₀, hwp⟩ := Finset.mem_filter.mp huB₁
        have huQ : u ∈ Q := Finset.mem_union_left _ huQ₀
        have hu3 := (hsource huQ).2.1
        have hu_mod : u % 5 ≠ 1 := (Finset.mem_filter.mp huQ₀).2.2
        let w := normalizedQuarticSum u
        have hwT : w ∈ T₅ := hcover u huQ (Nat.mem_primeFactors.mpr ⟨hwp, dvd_rfl, hwp.ne_zero⟩)
        have hlt : u < w := by
          have hnorm : w = u ^ 4 + u ^ 3 + u ^ 2 + u + 1 := by simp [w, normalizedQuarticSum, hu_mod]
          have hsq : 3 * u ≤ u ^ 2 := by nlinarith
          rw [hnorm]
          omega
        exact ⟨(u, w), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huQ, hwT⟩, hlt, dvd_rfl⟩, rfl⟩
      · obtain ⟨huQ₀, h23⟩ := Finset.mem_filter.mp huB₂₃
        have huQ : u ∈ Q := Finset.mem_union_left _ huQ₀
        have hu3 := (hsource huQ).2.1
        have hu_mod : u % 5 ≠ 1 := (Finset.mem_filter.mp huQ₀).2.2
        have hle3 : cardFactors (normalizedQuarticSum u) ≤ 3 := by rcases h23 with h2 | h3 <;> omega
        obtain ⟨w, hw_pf, huw⟩ := quartic_zero_exists_gt_of_cardFactors_le_three hu3 hu_mod hle3
        have hwT : w ∈ T₅ := hcover u huQ hw_pf
        have hwdvd : w ∣ normalizedQuarticSum u := Nat.dvd_of_mem_primeFactors hw_pf
        exact ⟨(u, w), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huQ, hwT⟩, huw, hwdvd⟩, rfl⟩
    · obtain ⟨huQ₁, hwp⟩ := Finset.mem_filter.mp hC₁
      have huQ : u ∈ Q := Finset.mem_union_right _ huQ₁
      have hu3 := (hsource huQ).2.1
      have hu_mod : u % 5 = 1 := (Finset.mem_filter.mp huQ₁).2.2
      let w := normalizedQuarticSum u
      have hwT : w ∈ T₅ := hcover u huQ (Nat.mem_primeFactors.mpr ⟨hwp, dvd_rfl, hwp.ne_zero⟩)
      have hlt : u < w := normalizedQuarticSum_gt_self_of_mod_one hu3 hu_mod
      exact ⟨(u, w), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huQ, hwT⟩, hlt, dvd_rfl⟩, rfl⟩
  have hUp_lower : B₁.card + B₂₃.card + C₁.card ≤ Up₅.card := by
    rw [← hU_up_card]
    exact (Finset.card_le_card hU_up_sub).trans Finset.card_image_le
  -- Upper bound on Up₅.card by fibering over T₅.
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
    exact normalizedQuarticSum_strictMono_of_mod_ne_one hu_mod hv_mod heq
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
      rw [geometricBlock_five_eq]
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
        hwp hvp hvw (hdvd.trans (normalizedQuarticSum_dvd_geometricBlock v))
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
          ⟨Finset.mem_range.mpr hvw, hdvd.trans (normalizedQuarticSum_dvd_geometricBlock v)⟩
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
  change 7 * Q₀.card + 4 * Q₁.card ≤ 3 * (∑ r ∈ T₅, N.factorization r) + 4 * T₅.card
  omega

end OddPerfect
