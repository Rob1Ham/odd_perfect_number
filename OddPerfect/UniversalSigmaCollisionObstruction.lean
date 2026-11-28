module

public import OddPerfect.FewPrimes
public import OddPerfect.OddGeometricSquares
public import OddPerfect.SixthPowerFreeEuler
public import OddPerfect.GlobalWave6Obstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Universal Sigma-Collision Obstruction (`OddPerfect.UniversalSigmaCollisionObstruction`)

Formalizes the universal multiplicative component-factorization decomposition
`N = ∏ p ∈ N.primeFactors, oddComponentSigma N q p` and the combinatorial + Ljunggren
collision excess bounds across every odd perfect number `N`:

1. `oddComponentSigma` & `prod_oddComponentSigma_eq_self`: Every component `oddComponentSigma N q p`
   is odd and `≥ 3`, their product equals `N`, and their prime factors cover `N.primeFactors`.
2. `odd_perfect_collision_excess_bound`: Combinatorial double-counting + Ljunggren (`3^4`)
   classification of isolated square components yields `ω(N) ≤ 3 * E + 3` unconditionally and
   `ω(N) ≤ 3 * E + 2` whenever `v_3(N) ≠ 4` (in particular when `¬ 3 ∣ N`).
3. `odd_perfect_exists_odd_prime_sigma_collision`: Combines Sylvester's `5 ≤ ω(N)` (and
   `8 ≤ ω(N)` for `3 ∤ N`) with (2) to deduce `1 ≤ E` (`2 ≤ E` for `3 ∤ N`) and an odd prime
   `r ∈ N.primeFactors` dividing `σ(p₁^{v_{p₁}(N)})` and `σ(p₂^{v_{p₂}(N)})` for two distinct
   primes `p₁ ≠ p₂` in `N.primeFactors`.
4. `sixth_power_free_collision_excess_ge_147`: Combines `443 ≤ ω(N)` and `3 ∤ N` with (2)
   to prove `147 ≤ E` and `590 ≤ ∑ p ∈ N.primeFactors, (oddComponentSigma N q p).primeFactors.card`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- The odd component divisor sum attached to a prime `p ∈ N.primeFactors` relative to the
Euler prime `q`: halves `σ(q^{v_q(N)})` at `p = q` and preserves `σ(p^{v_p(N)})` elsewhere. -/
@[expose] def oddComponentSigma (N q p : ℕ) : ℕ :=
  if p = q then sigma 1 (ordProj[q] N) / 2 else sigma 1 (ordProj[p] N)

private theorem primeFactors_finset_prod (s : Finset ℕ) (f : ℕ → ℕ)
    (hf : ∀ x ∈ s, f x ≠ 0) :
    (∏ x ∈ s, f x).primeFactors = s.biUnion fun x => (f x).primeFactors := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ha0 : f a ≠ 0 := hf a (Finset.mem_insert_self a s)
    have hs0 : ∀ x ∈ s, f x ≠ 0 := fun x hx => hf x (Finset.mem_insert_of_mem hx)
    have hprod0 : (∏ x ∈ s, f x) ≠ 0 := Finset.prod_ne_zero_iff.mpr hs0
    rw [Finset.prod_insert ha, Nat.primeFactors_mul ha0 hprod0, ih hs0, Finset.biUnion_insert]

private theorem sum_sub_one_eq_sum_sub_card {s : Finset ℕ} (g : ℕ → ℕ)
    (hg : ∀ x ∈ s, 1 ≤ g x) :
    (∑ x ∈ s, (g x - 1)) = (∑ x ∈ s, g x) - s.card := by
  have hsum : (∑ x ∈ s, (g x - 1)) + s.card = ∑ x ∈ s, g x := by
    calc
      (∑ x ∈ s, (g x - 1)) + s.card
          = (∑ x ∈ s, (g x - 1)) + ∑ _x ∈ s, 1 := by simp
      _ = ∑ x ∈ s, ((g x - 1) + 1) := by rw [← Finset.sum_add_distrib]
      _ = ∑ x ∈ s, g x := Finset.sum_congr rfl fun x hx => Nat.sub_add_cancel (hg x hx)
  omega

private theorem euler_sigma_mod_four {N q : ℕ}
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1) :
    sigma 1 (ordProj[q] N) % 4 = 2 ∧ 6 ≤ sigma 1 (ordProj[q] N) := by
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hq5 : 5 ≤ q := by
    have := hq_prime.two_le
    omega
  have hS4 := sigma_modEq_of_one hq_prime (show q ≡ 1 [MOD 4] from hq4) (N.factorization q)
  change sigma 1 (ordProj[q] N) % 4 = (N.factorization q + 1) % 4 at hS4
  have hmod : sigma 1 (ordProj[q] N) % 4 = 2 := by omega
  have ha_pos : 1 ≤ N.factorization q :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hq)
  have hsum : ∑ i ∈ Finset.range 2, q ^ i ≤ sigma 1 (ordProj[q] N) := by
    rw [sigma_one_apply_prime_pow hq_prime]
    exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega : 2 ≤ N.factorization q + 1))
  have h2 : ∑ i ∈ Finset.range 2, q ^ i = 1 + q := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    ring
  exact ⟨hmod, by omega⟩

private theorem oddComponentSigma_dvd_sigma {N q p : ℕ}
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1) :
    oddComponentSigma N q p ∣ sigma 1 (ordProj[p] N) := by
  unfold oddComponentSigma
  split_ifs with hpq
  · subst hpq
    have hmod := (euler_sigma_mod_four hq hq4 he).1
    exact Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero (by omega))
  · exact dvd_rfl

/-- **1. Universal Odd Component Factorization**:
Under the Euler decomposition of an odd perfect number `N` with special prime `q`, every
component `oddComponentSigma N q p` (`p ∈ N.primeFactors`) is odd and at least `3`, their product
equals `N`, their prime factors partition-cover `N.primeFactors`, and each component has at least
one prime factor. -/
theorem prod_oddComponentSigma_eq_self {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    (∀ p ∈ N.primeFactors,
      Odd (oddComponentSigma N q p) ∧ 1 < oddComponentSigma N q p ∧ 3 ≤ oddComponentSigma N q p) ∧
    (∏ p ∈ N.primeFactors, oddComponentSigma N q p) = N ∧
    N.primeFactors.biUnion (fun p => (oddComponentSigma N q p).primeFactors) = N.primeFactors ∧
    (∀ p ∈ N.primeFactors, 1 ≤ (oddComponentSigma N q p).primeFactors.card) := by
  have hprops : ∀ p ∈ N.primeFactors,
      Odd (oddComponentSigma N q p) ∧ 1 < oddComponentSigma N q p ∧ 3 ≤ oddComponentSigma N q p := by
    intro p hp
    unfold oddComponentSigma
    split_ifs with hpq
    · subst hpq
      obtain ⟨hmod, hge6⟩ := euler_sigma_mod_four hq hq4 he
      have hodd : Odd (sigma 1 (ordProj[p] N) / 2) := Nat.odd_iff.mpr (by omega)
      have hge3 : 3 ≤ sigma 1 (ordProj[p] N) / 2 := by omega
      exact ⟨hodd, by omega, hge3⟩
    · have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hp_odd : Odd p := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
      have hp3 : 3 ≤ p := by
        have := hp_prime.two_le
        have := hp_odd.not_two_dvd_nat
        omega
      have he_pos : 0 < N.factorization p :=
        Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
      obtain ⟨k, hk⟩ := hev p hpq
      have he2 : 2 ≤ N.factorization p := by omega
      have hord_sq : IsSquare (ordProj[p] N) := ⟨p ^ k, by rw [hk, pow_add]⟩
      have hord_odd : Odd (ordProj[p] N) := ho.of_dvd_nat (Nat.ordProj_dvd N p)
      have hsig_odd : Odd (sigma 1 (ordProj[p] N)) :=
        (odd_sigma_iff_square_of_odd hord_odd).mpr hord_sq
      have hsum : ∑ i ∈ Finset.range 3, p ^ i ≤ sigma 1 (ordProj[p] N) := by
        rw [sigma_one_apply_prime_pow hp_prime]
        exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega : 3 ≤ N.factorization p + 1))
      have h3 : ∑ i ∈ Finset.range 3, p ^ i = 1 + p + p ^ 2 := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
        ring
      have hp2_ge9 : 9 ≤ p ^ 2 := by nlinarith
      exact ⟨hsig_odd, by omega, by omega⟩
  have hprod : (∏ p ∈ N.primeFactors, oddComponentSigma N q p) = N := by
    have hq_mod := (euler_sigma_mod_four hq hq4 he).1
    have hq_twice : 2 * oddComponentSigma N q q = sigma 1 (ordProj[q] N) := by
      unfold oddComponentSigma
      simp only [ite_true]
      omega
    have herase :
        (∏ p ∈ N.primeFactors.erase q, oddComponentSigma N q p) =
          ∏ p ∈ N.primeFactors.erase q, sigma 1 (ordProj[p] N) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      have hpq : p ≠ q := (Finset.mem_erase.mp hp).1
      unfold oddComponentSigma
      simp only [hpq, ite_false]
    have htwice :
        2 * (∏ p ∈ N.primeFactors, oddComponentSigma N q p) = 2 * N := by
      calc
        2 * (∏ p ∈ N.primeFactors, oddComponentSigma N q p)
            = 2 * (oddComponentSigma N q q * ∏ p ∈ N.primeFactors.erase q, oddComponentSigma N q p) := by
              rw [Finset.mul_prod_erase _ _ hq]
        _ = (2 * oddComponentSigma N q q) * ∏ p ∈ N.primeFactors.erase q, oddComponentSigma N q p := by ring
        _ = sigma 1 (ordProj[q] N) * ∏ p ∈ N.primeFactors.erase q, sigma 1 (ordProj[p] N) := by
              rw [hq_twice, herase]
        _ = ∏ p ∈ N.primeFactors, sigma 1 (ordProj[p] N) :=
              Finset.mul_prod_erase N.primeFactors (fun p => sigma 1 (ordProj[p] N)) hq
        _ = sigma 1 N := (isMultiplicative_sigma.multiplicative_factorization (sigma 1) hN.2.ne').symm
        _ = 2 * N := (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN)
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) htwice
  have hbi : N.primeFactors.biUnion (fun p => (oddComponentSigma N q p).primeFactors) = N.primeFactors := by
    conv_rhs => rw [← hprod]
    symm
    exact primeFactors_finset_prod N.primeFactors (oddComponentSigma N q) fun p hp =>
      by have := (hprops p hp).2.2; omega
  have hcard : ∀ p ∈ N.primeFactors, 1 ≤ (oddComponentSigma N q p).primeFactors.card := by
    intro p hp
    have hgt1 : 1 < oddComponentSigma N q p := (hprops p hp).2.1
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hgt1.ne'
    exact Finset.card_pos.mpr ⟨r, Nat.mem_primeFactors.mpr ⟨hr, hrd, by omega⟩⟩
  exact ⟨hprops, hprod, hbi, hcard⟩

private theorem oddComponentSigma_double_counting {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    let indeg : ℕ → ℕ := fun r =>
      (N.primeFactors.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors)).card
    let totalIncidences := ∑ p ∈ N.primeFactors, (oddComponentSigma N q p).primeFactors.card
    totalIncidences = ∑ r ∈ N.primeFactors, indeg r ∧
    (∀ r ∈ N.primeFactors, 1 ≤ indeg r) ∧
    totalIncidences - N.primeFactors.card =
      ∑ p ∈ N.primeFactors, ((oddComponentSigma N q p).primeFactors.card - 1) ∧
    totalIncidences - N.primeFactors.card =
      ∑ r ∈ N.primeFactors, (indeg r - 1) := by
  obtain ⟨_, _, hbi, hcard⟩ := prod_oddComponentSigma_eq_self ho hN hq hq4 he hev
  let S := N.primeFactors
  let f : ℕ → Finset ℕ := fun p => (oddComponentSigma N q p).primeFactors
  let indeg : ℕ → ℕ := fun r => (S.filter (fun p => r ∈ f p)).card
  have hsub : ∀ p ∈ S, f p ⊆ S := by
    intro p hp r hr
    dsimp only [S]
    rw [← hbi]
    exact Finset.mem_biUnion.mpr ⟨p, hp, hr⟩
  have hdouble : (∑ p ∈ S, (f p).card) = ∑ r ∈ S, indeg r := by
    have h1 : ∀ p ∈ S, (f p).card = ∑ r ∈ S, (if r ∈ f p then 1 else 0) := by
      intro p hp
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (hsub p hp)]
    have h2 : ∀ r ∈ S, indeg r = ∑ p ∈ S, (if r ∈ f p then 1 else 0) := by
      intro r _
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    calc
      ∑ p ∈ S, (f p).card
          = ∑ p ∈ S, ∑ r ∈ S, (if r ∈ f p then 1 else 0) := Finset.sum_congr rfl h1
      _ = ∑ r ∈ S, ∑ p ∈ S, (if r ∈ f p then 1 else 0) := Finset.sum_comm
      _ = ∑ r ∈ S, indeg r := Finset.sum_congr rfl fun r hr => (h2 r hr).symm
  have hindeg_pos : ∀ r ∈ S, 1 ≤ indeg r := by
    intro r hr
    have hr' : r ∈ S.biUnion f := hbi.symm ▸ hr
    obtain ⟨p, hp, hrp⟩ := Finset.mem_biUnion.mp hr'
    exact Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hrp⟩⟩
  have hE1 : (∑ p ∈ S, (f p).card) - S.card = ∑ p ∈ S, ((f p).card - 1) :=
    (sum_sub_one_eq_sum_sub_card (fun p => (f p).card) hcard).symm
  have hE2 : (∑ p ∈ S, (f p).card) - S.card = ∑ r ∈ S, (indeg r - 1) := by
    rw [hdouble]
    exact (sum_sub_one_eq_sum_sub_card indeg hindeg_pos).symm
  exact ⟨hdouble, hindeg_pos, hE1, hE2⟩

/-- **2. Combinatorial + Ljunggren Collision Excess Bound**:
With `totalIncidences = ∑ p ∈ N.primeFactors, (oddComponentSigma N q p).primeFactors.card` and
`E = totalIncidences - N.primeFactors.card`, every non-Euler prime component with a single
prime factor either collides (`r = q` or `2 ≤ indeg r`) or isolates a square component
`σ(p^{v_p(N)}) = r^{v_r(N)}`, which Ljunggren's theorem restricts solely to `p = 3, v_3(N) = 4`.
Consequently:
- `ω(N) ≤ 3 * E + 3` unconditionally, and
- `ω(N) ≤ 3 * E + 2` whenever `v_3(N) ≠ 4` (in particular whenever `¬ 3 ∣ N`). -/
theorem odd_perfect_collision_excess_bound {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    let totalIncidences := ∑ p ∈ N.primeFactors, (oddComponentSigma N q p).primeFactors.card
    let E := totalIncidences - N.primeFactors.card
    N.primeFactors.card ≤ totalIncidences ∧
    N.primeFactors.card ≤ 3 * E + 3 ∧
    (N.factorization 3 ≠ 4 → N.primeFactors.card ≤ 3 * E + 2) ∧
    (¬ 3 ∣ N → N.primeFactors.card ≤ 3 * E + 2) := by
  obtain ⟨hprops, hprod, hbi, hcard⟩ := prod_oddComponentSigma_eq_self ho hN hq hq4 he hev
  obtain ⟨hdouble, hindeg_pos, hE1, hE2⟩ :=
    oddComponentSigma_double_counting ho hN hq hq4 he hev
  let S := N.primeFactors
  let f : ℕ → Finset ℕ := fun p => (oddComponentSigma N q p).primeFactors
  let indeg : ℕ → ℕ := fun r => (S.filter (fun p => r ∈ f p)).card
  let totalIncidences := ∑ p ∈ S, (f p).card
  let E := totalIncidences - S.card
  have hle_inc : S.card ≤ totalIncidences := by
    calc
      S.card = ∑ _p ∈ S, 1 := by simp
      _ ≤ ∑ p ∈ S, (f p).card := Finset.sum_le_sum hcard
  let S' := S.erase q
  let A := S'.filter (fun p => 2 ≤ (f p).card)
  let B := S'.filter (fun p => (f p).card = 1)
  have hAB_disj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro p hpA hpB
    have h2 : 2 ≤ (f p).card := (Finset.mem_filter.mp hpA).2
    have h1 : (f p).card = 1 := (Finset.mem_filter.mp hpB).2
    omega
  have hAB_union : A ∪ B = S' := by
    ext p
    simp only [A, B, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    · intro hp
      have hpS : p ∈ S := Finset.mem_of_mem_erase hp
      have h1 : 1 ≤ (f p).card := hcard p hpS
      rcases eq_or_lt_of_le h1 with h1' | h1'
      · exact Or.inr ⟨hp, h1'.symm⟩
      · exact Or.inl ⟨hp, h1'⟩
  have hA_le_E : A.card ≤ E := by
    have h1 : A.card ≤ ∑ p ∈ A, ((f p).card - 1) := by
      calc
        A.card = ∑ _p ∈ A, 1 := by simp
        _ ≤ ∑ p ∈ A, ((f p).card - 1) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have h2 : 2 ≤ (f p).card := (Finset.mem_filter.mp hp).2
          omega
    have h2 : ∑ p ∈ A, ((f p).card - 1) ≤ ∑ p ∈ S, ((f p).card - 1) :=
      Finset.sum_le_sum_of_subset fun p hp => Finset.mem_of_mem_erase (Finset.mem_filter.mp hp).1
    exact h1.trans (h2.trans_eq hE1.symm)
  let B_coll := B.filter (fun p => ∀ r ∈ f p, r = q ∨ 2 ≤ indeg r)
  let B_iso := B.filter (fun p => ¬ (∀ r ∈ f p, r = q ∨ 2 ≤ indeg r))
  have hB_split : B_coll.card + B_iso.card = B.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext p
      simp only [B_coll, B_iso, Finset.mem_union, Finset.mem_filter]
      tauto
    · rw [Finset.disjoint_left]
      intro p hp1 hp2
      exact (Finset.mem_filter.mp hp2).2 (Finset.mem_filter.mp hp1).2
  have hBiso_char : ∀ p ∈ B_iso, p = 3 ∧ N.factorization 3 = 4 := by
    intro p hp
    obtain ⟨hpB, hnot⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpS', hfp1⟩ := Finset.mem_filter.mp hpB
    have hpq : p ≠ q := (Finset.mem_erase.mp hpS').1
    have hpS : p ∈ S := Finset.mem_of_mem_erase hpS'
    obtain ⟨r, hfr⟩ := Finset.card_eq_one.mp hfp1
    have hnot_r : ¬ (r = q ∨ 2 ≤ indeg r) := by
      intro hok
      apply hnot
      intro x hx
      rw [hfr, Finset.mem_singleton] at hx
      subst hx
      exact hok
    have hrq : r ≠ q := fun h => hnot_r (Or.inl h)
    have hr_fp : r ∈ f p := by rw [hfr]; exact Finset.mem_singleton_self r
    have hrS : r ∈ S := by
      dsimp only [S]
      rw [← hbi]
      exact Finset.mem_biUnion.mpr ⟨p, hpS, hr_fp⟩
    have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hrS
    have hr_indeg1 : indeg r = 1 := by
      have h1 : 1 ≤ indeg r := hindeg_pos r hrS
      omega
    have hr_not_other : ∀ x ∈ S.erase p, r ∉ f x := by
      intro x hx hrx
      have hxp : x ≠ p := (Finset.mem_erase.mp hx).1
      have hxS : x ∈ S := Finset.mem_of_mem_erase hx
      have hsub2 : ({x, p} : Finset ℕ) ⊆ S.filter (fun y => r ∈ f y) := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hxS, hrx⟩
        · exact Finset.mem_filter.mpr ⟨hpS, hr_fp⟩
      have h2le : 2 ≤ indeg r := by
        calc
          2 = ({x, p} : Finset ℕ).card := (Finset.card_pair hxp).symm
          _ ≤ indeg r := Finset.card_le_card hsub2
      omega
    have hfac_zero : ∀ x ∈ S.erase p, (oddComponentSigma N q x).factorization r = 0 := by
      intro x hx
      have hne0 : oddComponentSigma N q x ≠ 0 := by
        have := (hprops x (Finset.mem_of_mem_erase hx)).2.2
        omega
      have hndvd : ¬ r ∣ oddComponentSigma N q x := by
        intro hd
        exact hr_not_other x hx (Nat.mem_primeFactors.mpr ⟨hr_prime, hd, hne0⟩)
      exact Nat.factorization_eq_zero_of_not_dvd hndvd
    have hfac_eq : (oddComponentSigma N q p).factorization r = N.factorization r := by
      have hmul_eq :
          oddComponentSigma N q p * ∏ x ∈ S.erase p, oddComponentSigma N q x = N := by
        rw [Finset.mul_prod_erase _ _ hpS]
        exact hprod
      have hp0 : oddComponentSigma N q p ≠ 0 := by
        have := (hprops p hpS).2.2
        omega
      have hrest0 : (∏ x ∈ S.erase p, oddComponentSigma N q x) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun x hx => by
          have := (hprops x (Finset.mem_of_mem_erase hx)).2.2
          omega
      have hfac := congrArg (fun n => n.factorization r) hmul_eq
      rw [Nat.factorization_mul hp0 hrest0, Finsupp.add_apply,
        Nat.factorization_prod_apply fun x hx => by
          have := (hprops x (Finset.mem_of_mem_erase hx)).2.2
          omega] at hfac
      have hsum0 : (∑ x ∈ S.erase p, (oddComponentSigma N q x).factorization r) = 0 :=
        Finset.sum_eq_zero hfac_zero
      omega
    have hcomp_eq : oddComponentSigma N q p = r ^ N.factorization r := by
      have hp0 : oddComponentSigma N q p ≠ 0 := by
        have := (hprops p hpS).2.2
        omega
      have hpf : oddComponentSigma N q p =
          (oddComponentSigma N q p).factorization.prod (· ^ ·) :=
        (Nat.prod_factorization_pow_eq_self hp0).symm
      rw [hpf]
      unfold Finsupp.prod
      rw [Nat.support_factorization]
      change (∏ x ∈ f p, x ^ (oddComponentSigma N q p).factorization x) = r ^ N.factorization r
      rw [hfr, Finset.prod_singleton, hfac_eq]
    have hsig_eq : sigma 1 (p ^ N.factorization p) = r ^ N.factorization r := by
      have h1 : oddComponentSigma N q p = sigma 1 (ordProj[p] N) := by
        unfold oddComponentSigma
        simp only [hpq, ite_false]
      rw [← h1]
      exact hcomp_eq
    obtain ⟨m, hm⟩ := hev r hrq
    have hsq : IsSquare (sigma 1 (p ^ N.factorization p)) := by
      rw [hsig_eq]
      exact ⟨r ^ m, by rw [hm, pow_add]⟩
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hpS
    have hp_pos : 0 < N.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hpS)
    have hp_even : Even (N.factorization p) := hev p hpq
    have hlj := (sigma_prime_pow_isSquare_iff_of_even hp_prime hp_pos hp_even).mp hsq
    rcases hlj with ⟨rfl, h4⟩
    exact ⟨rfl, h4⟩
  have hBiso_le1 : B_iso.card ≤ 1 := by
    have hsub : B_iso ⊆ {3} := by
      intro p hp
      rw [Finset.mem_singleton]
      exact (hBiso_char p hp).1
    exact (Finset.card_le_card hsub).trans (by simp)
  have hBiso_zero : N.factorization 3 ≠ 4 → B_iso.card = 0 := by
    intro hne4
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro p hp
    exact hne4 (hBiso_char p hp).2
  let C := S.filter (fun r => r = q ∨ 2 ≤ indeg r)
  have hqC : q ∈ C := Finset.mem_filter.mpr ⟨hq, Or.inl rfl⟩
  have hC_erase_le : (C.erase q).card ≤ E := by
    have h1 : (C.erase q).card ≤ ∑ r ∈ C.erase q, (indeg r - 1) := by
      calc
        (C.erase q).card = ∑ _r ∈ C.erase q, 1 := by simp
        _ ≤ ∑ r ∈ C.erase q, (indeg r - 1) := by
          refine Finset.sum_le_sum fun r hr => ?_
          have hrq : r ≠ q := (Finset.mem_erase.mp hr).1
          have hrC := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hr)).2
          rcases hrC with rfl | h2
          · exact (hrq rfl).elim
          · omega
    have h2 : ∑ r ∈ C.erase q, (indeg r - 1) ≤ ∑ r ∈ S, (indeg r - 1) :=
      Finset.sum_le_sum_of_subset fun r hr => (Finset.mem_filter.mp (Finset.mem_of_mem_erase hr)).1
    exact h1.trans (h2.trans_eq hE2.symm)
  have hC_le : C.card ≤ E + 1 := by
    have h := Finset.card_erase_add_one hqC
    omega
  have hsum_C_indeg : ∑ r ∈ C, indeg r ≤ 2 * E + 1 := by
    have hC_sub : C ⊆ S := Finset.filter_subset _ _
    have hsub_le : ∑ r ∈ C, (indeg r - 1) ≤ E :=
      (Finset.sum_le_sum_of_subset hC_sub).trans_eq hE2.symm
    have hC_eq : ∑ r ∈ C, (indeg r - 1) = (∑ r ∈ C, indeg r) - C.card :=
      sum_sub_one_eq_sum_sub_card indeg fun r hr => hindeg_pos r (hC_sub hr)
    have hC_pos : C.card ≤ ∑ r ∈ C, indeg r := by
      calc
        C.card = ∑ _r ∈ C, 1 := by simp
        _ ≤ ∑ r ∈ C, indeg r := Finset.sum_le_sum fun r hr => hindeg_pos r (hC_sub hr)
    omega
  have hBcoll_le : B_coll.card ≤ 2 * E + 1 := by
    have h1 : B_coll.card ≤ ∑ p ∈ B_coll, ∑ r ∈ C, (if r ∈ f p then 1 else 0) := by
      calc
        B_coll.card = ∑ _p ∈ B_coll, 1 := by simp
        _ ≤ ∑ p ∈ B_coll, ∑ r ∈ C, (if r ∈ f p then 1 else 0) := by
          refine Finset.sum_le_sum fun p hp => ?_
          obtain ⟨hpB, hp_all⟩ := Finset.mem_filter.mp hp
          have hpS : p ∈ S := Finset.mem_of_mem_erase (Finset.mem_filter.mp hpB).1
          have hfp1 : (f p).card = 1 := (Finset.mem_filter.mp hpB).2
          have hfp_sub : f p ⊆ C := by
            intro r hr
            have hrS : r ∈ S := by
              dsimp only [S]
              rw [← hbi]
              exact Finset.mem_biUnion.mpr ⟨p, hpS, hr⟩
            exact Finset.mem_filter.mpr ⟨hrS, hp_all r hr⟩
          rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one,
            Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hfp_sub, hfp1]
    have h2 :
        ∑ p ∈ B_coll, ∑ r ∈ C, (if r ∈ f p then 1 else 0) ≤ ∑ r ∈ C, indeg r := by
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun r _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      refine Finset.card_le_card fun p hp => ?_
      obtain ⟨hpBcoll, hrf⟩ := Finset.mem_filter.mp hp
      have hpS : p ∈ S :=
        Finset.mem_of_mem_erase (Finset.mem_filter.mp (Finset.mem_filter.mp hpBcoll).1).1
      exact Finset.mem_filter.mpr ⟨hpS, hrf⟩
    exact h1.trans (h2.trans hsum_C_indeg)
  have hS'_eq : S'.card + 1 = S.card := Finset.card_erase_add_one hq
  have hAB_sum : A.card + B.card = S'.card := by
    rw [← Finset.card_union_of_disjoint hAB_disj, hAB_union]
  have hS_ub : S.card ≤ 3 * E + 2 + B_iso.card := by omega
  have h3_uncond : S.card ≤ 3 * E + 3 := by omega
  have h3_ne4 : N.factorization 3 ≠ 4 → S.card ≤ 3 * E + 2 := by
    intro hne4
    have hz := hBiso_zero hne4
    omega
  have h3_not3 : ¬ 3 ∣ N → S.card ≤ 3 * E + 2 := by
    intro hnd3
    apply h3_ne4
    rw [Nat.factorization_eq_zero_of_not_dvd hnd3]
    omega
  exact ⟨hle_inc, h3_uncond, h3_ne4, h3_not3⟩

/-- **3. Universal Existence of an Odd-Prime Sigma Collision**:
For every odd perfect number `N` (with no extra hypotheses):
- The collision excess is at least `1` (and at least `2` when `¬ 3 ∣ N`).
- There exists an odd prime `r ∈ N.primeFactors` and two distinct primes `p₁ ≠ p₂` in
  `N.primeFactors` such that `r ∣ σ(p₁^{v_{p₁}(N)})` and `r ∣ σ(p₂^{v_{p₂}(N)})`. -/
theorem odd_perfect_exists_odd_prime_sigma_collision {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) :
    (∃ r : ℕ, r.Prime ∧ Odd r ∧ r ∈ N.primeFactors ∧
      ∃ p₁ ∈ N.primeFactors, ∃ p₂ ∈ N.primeFactors, p₁ ≠ p₂ ∧
        r ∣ sigma 1 (ordProj[p₁] N) ∧ r ∣ sigma 1 (ordProj[p₂] N)) ∧
    (∃ q ∈ N.primeFactors, q % 4 = 1 ∧ N.factorization q % 4 = 1 ∧
      (∀ r : ℕ, r ≠ q → Even (N.factorization r)) ∧
      N.primeFactors.card + 1 ≤ ∑ p ∈ N.primeFactors, (oddComponentSigma N q p).primeFactors.card ∧
      (¬ 3 ∣ N →
        N.primeFactors.card + 2 ≤ ∑ p ∈ N.primeFactors, (oddComponentSigma N q p).primeFactors.card)) := by
  obtain ⟨q, hq, hq4, he, hev⟩ := euler_exponents ho hN
  obtain ⟨hle, h3, _, hnot3⟩ := odd_perfect_collision_excess_bound ho hN hq hq4 he hev
  have h5 : 5 ≤ N.primeFactors.card := five_le_distinct_prime_factor_count ho hN
  have hE1 : 1 ≤ (∑ p ∈ N.primeFactors, (oddComponentSigma N q p).primeFactors.card) -
      N.primeFactors.card := by omega
  have hE2 : ¬ 3 ∣ N →
      2 ≤ (∑ p ∈ N.primeFactors, (oddComponentSigma N q p).primeFactors.card) -
        N.primeFactors.card := by
    intro h3nd
    have h8 := eight_le_distinct_prime_factor_count_of_three_free ho hN h3nd
    have := hnot3 h3nd
    omega
  obtain ⟨_, _, _, hE_indeg⟩ := oddComponentSigma_double_counting ho hN hq hq4 he hev
  let indeg : ℕ → ℕ := fun r =>
    (N.primeFactors.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors)).card
  have hsum_pos : 1 ≤ ∑ r ∈ N.primeFactors, (indeg r - 1) := by
    have hE_eq :
        (∑ p ∈ N.primeFactors, (oddComponentSigma N q p).primeFactors.card) - N.primeFactors.card =
          ∑ r ∈ N.primeFactors, (indeg r - 1) := hE_indeg
    omega
  have hex_r : ∃ r ∈ N.primeFactors, 2 ≤ indeg r := by
    by_contra! hall
    have hzero : ∀ r ∈ N.primeFactors, indeg r - 1 = 0 := fun r hr => by
      have := hall r hr
      omega
    have hsum0 : (∑ r ∈ N.primeFactors, (indeg r - 1)) = 0 := Finset.sum_eq_zero hzero
    omega
  obtain ⟨r, hr, hr2⟩ := hex_r
  have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr
  have hr_odd : Odd r := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr)
  have h1lt : 1 < (N.primeFactors.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors)).card := by
    dsimp only [indeg] at hr2
    omega
  obtain ⟨p₁, p₂, hp₁, hp₂, hpne⟩ := Finset.one_lt_card_iff.mp h1lt
  obtain ⟨hp₁N, hrp₁⟩ := Finset.mem_filter.mp hp₁
  obtain ⟨hp₂N, hrp₂⟩ := Finset.mem_filter.mp hp₂
  have hdvd₁ : r ∣ sigma 1 (ordProj[p₁] N) :=
    (Nat.dvd_of_mem_primeFactors hrp₁).trans (oddComponentSigma_dvd_sigma hq hq4 he)
  have hdvd₂ : r ∣ sigma 1 (ordProj[p₂] N) :=
    (Nat.dvd_of_mem_primeFactors hrp₂).trans (oddComponentSigma_dvd_sigma hq hq4 he)
  refine ⟨⟨r, hr_prime, hr_odd, hr, p₁, hp₁N, p₂, hp₂N, hpne, hdvd₁, hdvd₂⟩,
    ⟨q, hq, hq4, he, hev, by omega, fun h3nd => by have := hE2 h3nd; omega⟩⟩

/-- **4. Sixth-Power-Free Collision Excess Lower Bound (`147 ≤ E`)**:
On any sixth-power-free odd perfect number `N`, combining `¬ 3 ∣ N` and `443 ≤ ω(N)` with
`odd_perfect_collision_excess_bound` yields `147 ≤ E` and
`590 ≤ ∑ p ∈ N.primeFactors, (oddComponentSigma N q p).primeFactors.card`. -/
theorem sixth_power_free_collision_excess_ge_147 {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let totalIncidences := ∑ p ∈ N.primeFactors, (oddComponentSigma N q p).primeFactors.card
    let E := totalIncidences - N.primeFactors.card
    443 ≤ N.primeFactors.card ∧ 147 ≤ E ∧ 590 ≤ totalIncidences := by
  have h443 : 443 ≤ N.primeFactors.card := by
    rcases sixth_power_or_large_support ho hN with ⟨p, hp, hpow⟩ | ⟨hcard, _, _⟩
    · exact (hfree p hp hpow).elim
    · exact hcard
  have hnot3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  obtain ⟨hle, _, _, hbound⟩ := odd_perfect_collision_excess_bound ho hN hq hq4 he hev
  have h3E2 := hbound hnot3
  dsimp only
  omega

end OddPerfect
