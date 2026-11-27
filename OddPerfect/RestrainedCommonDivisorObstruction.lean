module

public import OddPerfect.GlobalWave8Obstruction
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Three-Free Restrained Common-Divisor & Cycle Obstruction (`OddPerfect.RestrainedCommonDivisorObstruction`)

Strengthens the three-free restrained odd perfect branch (`¬ 3 ∣ N`, `(largeSources N q).card ≤ 1`):
1. `restrained_three_free_twenty_four_factor_drop`: Lifts the Euler component drop to
   `cardFactors (componentIndex N q) + 24 ≤ cardFactors N` using `21 ≤ N.factorization q` and
   `4 ≤ cardFactors (sigma 1 (ordProj[q] N))` from the cyclotomic factorization
   `2 * ((q + 1) / 2) * B₁ * B₂ ∣ sigma 1 (q ^ a)`.
2. `restrained_three_free_square_source_oddSigma_pairing`: Proves that every `u ∈ squareSources N`
   satisfies `2 = (sigma 1 (q ^ N.factorization q)).factorization u + (sigma 1 (r₀ ^ N.factorization r₀)).factorization u`,
   so `oddSigmaSources N u = ∅` or `oddSigmaSources N u = {q, r₀}` with both valuations equal to `1`
   and `u ∣ Nat.gcd (sigma 1 (q ^ N.factorization q)) (sigma 1 (r₀ ^ N.factorization r₀))`.
3. `restrained_three_free_cycle_two_or_gcd_witness`: Forces either the direct 2-cycle
   `oddSigmaEdge N q r₀ ∧ oddSigmaEdge N r₀ q` or a square-source witness `u ∈ squareSources N`
   with `oddSigmaSources N u = {q, r₀}`, `u ∣ Nat.gcd (sigma 1 (q ^ N.factorization q)) (sigma 1 (r₀ ^ N.factorization r₀))`,
   and `oddSigmaEdge N u q ∨ oddSigmaEdge N u r₀`.
4. `restrained_three_free_mod_four_square_sources`: Shows that if additionally `r₀ % 4 = 1`, then
   every `u ∈ squareSources N` satisfies `u % 12 = 11`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private theorem sigma_one_sq_rcd {p : ℕ} (hp : p.Prime) : sigma 1 (p ^ 2) = p ^ 2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

private theorem restrained_three_free_invariants {N q r₀ : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) (hr₀ : largeSources N q = {r₀}) :
    q.Prime ∧ Odd q ∧ q % 12 = 1 ∧ 13 ≤ q ∧
    r₀ ∈ N.primeFactors ∧ r₀.Prime ∧ Odd r₀ ∧ r₀ ≠ 3 ∧ r₀ ≠ q ∧
    r₀ % 3 = 1 ∧ 7 ≤ r₀ ∧ 4 ≤ N.factorization r₀ ∧ Even (N.factorization r₀) ∧
    N.primeFactors = insert q (insert r₀ (squareSources N)) ∧
    r₀ ∉ squareSources N ∧ q ∉ insert r₀ (squareSources N) ∧
    (∀ u ∈ squareSources N,
      u.Prime ∧ Odd u ∧ u ≠ 3 ∧ u ≠ q ∧ u ≠ r₀ ∧ N.factorization u = 2 ∧
      u % 3 = 2 ∧ 5 ≤ u ∧ sigma 1 (u ^ N.factorization u) = u ^ 2 + u + 1) ∧
    (∀ s ∈ squareSources N, ∀ u ∈ squareSources N,
      ¬ u ∣ sigma 1 (s ^ N.factorization s)) := by
  have hle : (largeSources N q).card ≤ 1 := by rw [hr₀, Finset.card_singleton]
  obtain ⟨r₁, hr₁, hq12, hr₁3, _, hq13, hr₁7, _⟩ :=
    restrained_three_free_euler_exp_ge_17 ho hN hq hq4 he hev h3 hle
  have hr_eq : r₁ = r₀ := by
    have : r₁ ∈ ({r₀} : Finset ℕ) := by rw [← hr₀, hr₁]; exact Finset.mem_singleton_self r₁
    exact Finset.mem_singleton.mp this
  subst r₁
  have hr₀_mem_large : r₀ ∈ largeSources N q := by rw [hr₀]; exact Finset.mem_singleton_self r₀
  obtain ⟨hr₀_mem, hr₀3, hr₀q, hr₀_exp⟩ := Finset.mem_filter.mp hr₀_mem_large
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hq_odd : Odd q := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_mem
  have hr₀_odd : Odd r₀ := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr₀_mem)
  have hr₀_even : Even (N.factorization r₀) := hev r₀ hr₀q
  have h3not : 3 ∉ N.primeFactors := fun h => h3 (Nat.dvd_of_mem_primeFactors h)
  have hsq1_zero : (squareSourcesOne N).card = 0 := by
    have h3zero : N.factorization 3 = 0 := Finsupp.notMem_support_iff.mp h3not
    have := squareSourcesOne_card_le_three_exponent hN
    omega
  have hpart : N.primeFactors = insert q (insert r₀ (squareSources N)) := by
    ext r
    simp only [Finset.mem_insert, squareSources, Finset.mem_filter]
    constructor
    · intro hr
      by_cases hrq : r = q
      · exact Or.inl hrq
      · have hr3 : r ≠ 3 := fun h => h3not (h ▸ hr)
        have hpos : 0 < N.factorization r := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
        obtain ⟨k, hk⟩ := hev r hrq
        by_cases htwo : N.factorization r = 2
        · exact Or.inr (Or.inr ⟨hr, hr3, htwo⟩)
        · have hlarge_r : r ∈ largeSources N q :=
            Finset.mem_filter.mpr ⟨hr, hr3, hrq, by omega⟩
          rw [hr₀, Finset.mem_singleton] at hlarge_r
          exact Or.inr (Or.inl hlarge_r)
    · rintro (rfl | rfl | ⟨hr, _, _⟩)
      · exact hq
      · exact hr₀_mem
      · exact hr
  have hr₀_not_S : r₀ ∉ squareSources N := by
    intro h
    have := (Finset.mem_filter.mp h).2.2
    omega
  have hq_not_ins : q ∉ insert r₀ (squareSources N) := by
    intro h
    rcases Finset.mem_insert.mp h with hqr | hqS
    · exact hr₀q hqr.symm
    · have := (Finset.mem_filter.mp hqS).2.2
      omega
  have hS_prop : ∀ u ∈ squareSources N,
      u.Prime ∧ Odd u ∧ u ≠ 3 ∧ u ≠ q ∧ u ≠ r₀ ∧ N.factorization u = 2 ∧
      u % 3 = 2 ∧ 5 ≤ u ∧ sigma 1 (u ^ N.factorization u) = u ^ 2 + u + 1 := by
    intro u hu
    obtain ⟨hu_mem, hu3, hu_exp2⟩ := Finset.mem_filter.mp hu
    have hup := Nat.prime_of_mem_primeFactors hu_mem
    have hu_odd := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hu_mem)
    have huq : u ≠ q := fun h => by subst h; omega
    have hur₀ : u ≠ r₀ := fun h => by subst h; omega
    have hu_mod3 : u % 3 = 2 := by
      by_contra! hne2
      have h0or1 : u % 3 = 0 ∨ u % 3 = 1 := by omega
      rcases h0or1 with h0 | h1
      · have hd3 : 3 ∣ u := Nat.dvd_of_mod_eq_zero h0
        have heq3 := (Nat.dvd_prime hup).mp hd3
        have := hup.two_le
        omega
      · have hu_sq1 : u ∈ squareSourcesOne N := Finset.mem_filter.mpr ⟨hu, h1⟩
        have hpos : 0 < (squareSourcesOne N).card := Finset.card_pos.mpr ⟨u, hu_sq1⟩
        omega
    have hu5 : 5 ≤ u := by
      have := hup.two_le
      have := Nat.odd_iff.mp hu_odd
      omega
    have hsig : sigma 1 (u ^ N.factorization u) = u ^ 2 + u + 1 := by
      rw [hu_exp2, sigma_one_sq_rcd hup]
    exact ⟨hup, hu_odd, hu3, huq, hur₀, hu_exp2, hu_mod3, hu5, hsig⟩
  have hsq_ndvd : ∀ s ∈ squareSources N, ∀ u ∈ squareSources N,
      ¬ u ∣ sigma 1 (s ^ N.factorization s) := by
    intro s hs u hu hdvd
    obtain ⟨_, _, _, _, _, _, _, _, hsig_s⟩ := hS_prop s hs
    obtain ⟨hu_prime, _, _, _, _, _, hu_mod3, _, _⟩ := hS_prop u hu
    rw [hsig_s] at hdvd
    have hmod := prime_dvd_sq_add_self_add_one hu_prime hdvd
    omega
  exact ⟨hq_prime, hq_odd, hq12, hq13, hr₀_mem, hr₀_prime, hr₀_odd, hr₀3, hr₀q, hr₁3, hr₁7,
    hr₀_exp, hr₀_even, hpart, hr₀_not_S, hq_not_ins, hS_prop, hsq_ndvd⟩

/-- **24-Factor Component-Index Drop on Three-Free Restrained Candidates**:
On any three-free restrained odd perfect number (`¬ 3 ∣ N`, `(largeSources N q).card ≤ 1`),
combining `21 ≤ N.factorization q` with `4 ≤ cardFactors (sigma 1 (ordProj[q] N))` from
`2 * ((q + 1) / 2) * B₁ * B₂ ∣ sigma 1 (q ^ N.factorization q)` yields
`cardFactors (componentIndex N q) + 24 ≤ cardFactors N`. -/
theorem restrained_three_free_twenty_four_factor_drop {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) (hle : (largeSources N q).card ≤ 1) :
    cardFactors (componentIndex N q) + 24 ≤ cardFactors N := by
  obtain ⟨_, _, _, _, _, hq13, _, _⟩ :=
    restrained_three_free_euler_exp_ge_17 ho hN hq hq4 he hev h3 hle
  obtain ⟨h21, hndvd3, hd11⟩ :=
    restrained_three_free_euler_exp_ge_21 ho hN hq hq4 he hev h3 hle
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  let a := N.factorization q
  let d := (a + 1) / 2
  let l := d.minFac
  have hl_prime : l.Prime := Nat.minFac_prime (by omega)
  have hl_dvd : l ∣ d := Nat.minFac_dvd d
  have hd_odd : Odd d := Nat.odd_iff.mpr (by dsimp [d]; omega)
  have hl_odd : Odd l := hd_odd.of_dvd_nat hl_dvd
  have hl_ne3 : l ≠ 3 := fun h => hndvd3 (h ▸ hl_dvd)
  have hl3 : 3 ≤ l := by
    have := hl_prime.two_le
    have := Nat.odd_iff.mp hl_odd
    omega
  let B₁ := geometricBlock q l
  let B₂ := (q ^ l + 1) / (q + 1)
  obtain ⟨hB₂_eq, hB₁_gt1, _, hB₂_gt1, _, _, _⟩ :=
    odd_prime_cyclotomic_pair_dvd_sigma hq_prime hq4 he hl_prime hl3 hl_dvd
  have h2l : 2 * l ∣ a + 1 := by
    obtain ⟨k, hk⟩ := hl_dvd
    refine ⟨k, ?_⟩
    calc
      a + 1 = 2 * d := by dsimp [d]; omega
      _ = 2 * (l * k) := by rw [hk]
      _ = (2 * l) * k := by ring
  have hblock2l : geometricBlock q (2 * l) = (q + 1) * (B₁ * B₂) := by
    have hmul := geometricBlock_mul q l 2
    rw [show l * 2 = 2 * l by ring] at hmul
    have hg2 : geometricBlock (q ^ l) 2 = q ^ l + 1 := by
      rw [geometricBlock, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      ring
    rw [hmul, hg2, ← hB₂_eq]
    change B₁ * ((q + 1) * B₂) = (q + 1) * (B₁ * B₂)
    ring
  have hprod_dvd : (q + 1) * (B₁ * B₂) ∣ sigma 1 (q ^ a) := by
    obtain ⟨k, hk⟩ := h2l
    rw [← hblock2l, sigma_one_apply_prime_pow hq_prime]
    change geometricBlock q (2 * l) ∣ geometricBlock q (a + 1)
    rw [hk, geometricBlock_mul q (2 * l) k]
    exact dvd_mul_right _ _
  let H := (q + 1) / 2
  have hq1_eq : q + 1 = 2 * H := by dsimp [H]; omega
  have hH_gt1 : 1 < H := by dsimp [H]; omega
  obtain ⟨m, hm⟩ := hprod_dvd
  have hsig_ne0 : sigma 1 (q ^ a) ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hq_prime.ne_zero)).ne'
  have hm_ne0 : m ≠ 0 := fun h => hsig_ne0 (by rw [hm, h, mul_zero])
  have hsig_eq : sigma 1 (q ^ a) = 2 * H * B₁ * B₂ * m := by
    rw [hm, hq1_eq]
    ring
  have h4_le : 4 ≤ cardFactors (sigma 1 (ordProj[q] N)) := by
    change 4 ≤ cardFactors (sigma 1 (q ^ a))
    rw [hsig_eq,
      cardFactors_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (by decide) (by omega)) (by omega))
        (by omega)) hm_ne0,
      cardFactors_mul (mul_ne_zero (mul_ne_zero (by decide) (by omega)) (by omega)) (by omega),
      cardFactors_mul (mul_ne_zero (by decide) (by omega)) (by omega),
      cardFactors_mul (by decide : (2 : ℕ) ≠ 0) (by omega)]
    have c2 : 0 < cardFactors 2 := cardFactors_pos_iff_one_lt.mpr (by decide)
    have cH : 0 < cardFactors H := cardFactors_pos_iff_one_lt.mpr hH_gt1
    have cB1 : 0 < cardFactors B₁ := cardFactors_pos_iff_one_lt.mpr hB₁_gt1
    have cB2 : 0 < cardFactors B₂ := cardFactors_pos_iff_one_lt.mpr hB₂_gt1
    omega
  have hcomp := cardFactors_componentIndex_add_eq hN hq
  omega

/-- **Square-Source Odd-Valuation Pairing on Three-Free Restrained Candidates**:
For every `u ∈ squareSources N`, `N.factorization u = 2` is split entirely between the
Euler prime `q` and the unique large source `r₀`, so either `oddSigmaSources N u = ∅` or
`oddSigmaSources N u = {q, r₀}` with both valuations equal to `1` and
`u ∣ Nat.gcd (sigma 1 (q ^ N.factorization q)) (sigma 1 (r₀ ^ N.factorization r₀))`. -/
theorem restrained_three_free_square_source_oddSigma_pairing {N q r₀ : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) (hr₀ : largeSources N q = {r₀}) :
    ∀ u ∈ squareSources N,
      2 = (sigma 1 (q ^ N.factorization q)).factorization u +
          (sigma 1 (r₀ ^ N.factorization r₀)).factorization u ∧
      (oddSigmaSources N u = ∅ ∨
        (oddSigmaSources N u = {q, r₀} ∧
          (sigma 1 (q ^ N.factorization q)).factorization u = 1 ∧
          (sigma 1 (r₀ ^ N.factorization r₀)).factorization u = 1 ∧
          u ∣ Nat.gcd (sigma 1 (q ^ N.factorization q))
            (sigma 1 (r₀ ^ N.factorization r₀)))) := by
  obtain ⟨hq_prime, _, _, _, hr₀_mem, hr₀_prime, _, _, hr₀q, _, _, _, _,
      hpart, hr₀_not_S, hq_not_ins, hS_prop, hsq_ndvd⟩ :=
    restrained_three_free_invariants ho hN hq hq4 he hev h3 hr₀
  intro u hu
  obtain ⟨hu_prime, hu_odd, _, _, _, hu_exp2, _, _, _⟩ := hS_prop u hu
  have hsum_eq :
      2 = (sigma 1 (q ^ N.factorization q)).factorization u +
          (sigma 1 (r₀ ^ N.factorization r₀)).factorization u := by
    have hfac := factorization_eq_sum_sigma_factorizations hN hu_odd hu_prime
    rw [hu_exp2, hpart, Finset.sum_insert hq_not_ins, Finset.sum_insert hr₀_not_S] at hfac
    have hS_zero :
        (∑ s ∈ squareSources N, (sigma 1 (s ^ N.factorization s)).factorization u) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro s hs
      exact Nat.factorization_eq_zero_of_not_dvd (hsq_ndvd s hs u hu)
    rw [hS_zero, add_zero] at hfac
    exact hfac
  refine ⟨hsum_eq, ?_⟩
  have hsub : oddSigmaSources N u ⊆ ({q, r₀} : Finset ℕ) := by
    intro p hp
    obtain ⟨hp_mem, hp_odd⟩ := Finset.mem_filter.mp hp
    rw [hpart] at hp_mem
    rcases Finset.mem_insert.mp hp_mem with rfl | hp_ins
    · exact Finset.mem_insert_self _ _
    · rcases Finset.mem_insert.mp hp_ins with rfl | hp_S
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · exfalso
        have hzero : (sigma 1 (p ^ N.factorization p)).factorization u = 0 :=
          Nat.factorization_eq_zero_of_not_dvd (hsq_ndvd p hp_S u hu)
        rw [hzero] at hp_odd
        exact (by decide : ¬ Odd 0) hp_odd
  have hcard_le : (oddSigmaSources N u).card ≤ 2 := by
    calc
      (oddSigmaSources N u).card ≤ ({q, r₀} : Finset ℕ).card := Finset.card_le_card hsub
      _ = 2 := Finset.card_pair hr₀q.symm
  have heven_card : Even (oddSigmaSources N u).card :=
    (even_oddSigmaSources_iff hN hu_prime hu_odd).mpr (by rw [hu_exp2]; exact even_two)
  have hcard_cases : (oddSigmaSources N u).card = 0 ∨ (oddSigmaSources N u).card = 2 := by
    obtain ⟨k, hk⟩ := heven_card
    omega
  rcases hcard_cases with h0 | h2
  · exact Or.inl (Finset.card_eq_zero.mp h0)
  · right
    have heq_pair : oddSigmaSources N u = {q, r₀} :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hr₀q.symm, h2])
    have hq_in : q ∈ oddSigmaSources N u := by rw [heq_pair]; exact Finset.mem_insert_self _ _
    have hr₀_in : r₀ ∈ oddSigmaSources N u := by
      rw [heq_pair]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hq_odd_val : Odd ((sigma 1 (q ^ N.factorization q)).factorization u) :=
      (Finset.mem_filter.mp hq_in).2
    have hr₀_odd_val : Odd ((sigma 1 (r₀ ^ N.factorization r₀)).factorization u) :=
      (Finset.mem_filter.mp hr₀_in).2
    have hq_pos : 0 < (sigma 1 (q ^ N.factorization q)).factorization u := hq_odd_val.pos
    have hr₀_pos : 0 < (sigma 1 (r₀ ^ N.factorization r₀)).factorization u := hr₀_odd_val.pos
    have hq_val1 : (sigma 1 (q ^ N.factorization q)).factorization u = 1 := by omega
    have hr₀_val1 : (sigma 1 (r₀ ^ N.factorization r₀)).factorization u = 1 := by omega
    have hu_dvd_q : u ∣ sigma 1 (q ^ N.factorization q) :=
      Nat.dvd_of_mem_primeFactors (Finsupp.mem_support_iff.mpr (by rw [hq_val1]; decide))
    have hu_dvd_r₀ : u ∣ sigma 1 (r₀ ^ N.factorization r₀) :=
      Nat.dvd_of_mem_primeFactors (Finsupp.mem_support_iff.mpr (by rw [hr₀_val1]; decide))
    exact ⟨heq_pair, hq_val1, hr₀_val1, Nat.dvd_gcd hu_dvd_q hu_dvd_r₀⟩

private theorem oddSigmaEdge_transGen_dichotomy {N q r₀ a b : ℕ}
    (hpart : N.primeFactors = insert q (insert r₀ (squareSources N)))
    (h : Relation.TransGen (oddSigmaEdge N) a b)
    (ha : a ∉ squareSources N) (hb : b ∉ squareSources N) :
    (∃ u ∈ squareSources N, (∃ x, oddSigmaEdge N x u) ∧ (∃ y, oddSigmaEdge N u y)) ∨
    (a ∈ ({q, r₀} : Finset ℕ) ∧ b ∈ ({q, r₀} : Finset ℕ) ∧
      (a = b → oddSigmaEdge N q r₀ ∧ oddSigmaEdge N r₀ q) ∧
      (a = q ∧ b = r₀ → oddSigmaEdge N q r₀) ∧
      (a = r₀ ∧ b = q → oddSigmaEdge N r₀ q)) := by
  have hmem_pair : ∀ {x : ℕ}, x ∈ N.primeFactors → x ∉ squareSources N → x ∈ ({q, r₀} : Finset ℕ) := by
    intro x hx hnot
    rw [hpart] at hx
    rcases Finset.mem_insert.mp hx with rfl | hx1
    · exact Finset.mem_insert_self _ _
    · rcases Finset.mem_insert.mp hx1 with rfl | hx2
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · exact absurd hx2 hnot
  induction h with
  | single hab =>
    right
    have hne := oddSigmaEdge_ne hab
    have ha_pair := hmem_pair hab.1 ha
    have hb_pair := hmem_pair hab.2.1 hb
    refine ⟨ha_pair, hb_pair, fun heq => absurd heq hne, ?_, ?_⟩
    · rintro ⟨rfl, rfl⟩; exact hab
    · rintro ⟨rfl, rfl⟩; exact hab
  | @tail c d hac hcd ih =>
    by_cases hc : c ∈ squareSources N
    · left
      have hin : ∃ x, oddSigmaEdge N x c := by
        cases hac with
        | single h1 => exact ⟨_, h1⟩
        | tail _ h2 => exact ⟨_, h2⟩
      exact ⟨c, hc, hin, ⟨d, hcd⟩⟩
    · rcases ih hc with hsq | ⟨ha_pair, hc_pair, h_eq, h_qr, h_rq⟩
      · exact Or.inl hsq
      · right
        have hne : c ≠ d := oddSigmaEdge_ne hcd
        have hd_pair := hmem_pair hcd.2.1 hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha_pair hc_pair hd_pair
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rcases ha_pair with rfl | rfl
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        · rcases hd_pair with rfl | rfl
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        · intro had
          subst had
          rcases ha_pair with rfl | rfl
          · rcases hc_pair with rfl | rfl
            · exact absurd rfl hne
            · exact ⟨h_qr ⟨rfl, rfl⟩, hcd⟩
          · rcases hc_pair with rfl | rfl
            · exact ⟨hcd, h_rq ⟨rfl, rfl⟩⟩
            · exact absurd rfl hne
        · rintro ⟨rfl, rfl⟩
          rcases hc_pair with rfl | rfl
          · exact (h_eq rfl).1
          · exact h_qr ⟨rfl, rfl⟩
        · rintro ⟨rfl, rfl⟩
          rcases hc_pair with rfl | rfl
          · exact h_rq ⟨rfl, rfl⟩
          · exact (h_eq rfl).2

/-- **Direct 2-Cycle or Square-Source Common-Divisor Witness on Three-Free Restrained Candidates**:
Either `oddSigmaEdge N q r₀ ∧ oddSigmaEdge N r₀ q` holds directly, or there exists
`u ∈ squareSources N` with `oddSigmaSources N u = {q, r₀}`,
`u ∣ Nat.gcd (sigma 1 (q ^ N.factorization q)) (sigma 1 (r₀ ^ N.factorization r₀))`, and
`oddSigmaEdge N u q ∨ oddSigmaEdge N u r₀`. -/
theorem restrained_three_free_cycle_two_or_gcd_witness {N q r₀ : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) (hr₀ : largeSources N q = {r₀}) :
    (oddSigmaEdge N q r₀ ∧ oddSigmaEdge N r₀ q) ∨
    (∃ u ∈ squareSources N,
      oddSigmaSources N u = {q, r₀} ∧
      u ∣ Nat.gcd (sigma 1 (q ^ N.factorization q)) (sigma 1 (r₀ ^ N.factorization r₀)) ∧
      (oddSigmaEdge N u q ∨ oddSigmaEdge N u r₀)) := by
  have hle : (largeSources N q).card ≤ 1 := by rw [hr₀, Finset.card_singleton]
  obtain ⟨_, _, _, _, _, _, _, _, hcyc_ex⟩ :=
    restrained_three_free_forces_oddSigma_cycle ho hN hq hq4 he hev h3 hle
  obtain ⟨p, _, hcyc⟩ := hcyc_ex
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hpart, _, _, _, hsq_ndvd⟩ :=
    restrained_three_free_invariants ho hN hq hq4 he hev h3 hr₀
  have hsq_step : ∀ u ∈ squareSources N, ∀ x y,
      oddSigmaEdge N x u → oddSigmaEdge N u y →
      ∃ w ∈ squareSources N,
        oddSigmaSources N w = {q, r₀} ∧
        w ∣ Nat.gcd (sigma 1 (q ^ N.factorization q)) (sigma 1 (r₀ ^ N.factorization r₀)) ∧
        (oddSigmaEdge N w q ∨ oddSigmaEdge N w r₀) := by
    intro u hu x y hxu huy
    have hpair := (restrained_three_free_square_source_oddSigma_pairing
      ho hN hq hq4 he hev h3 hr₀ u hu).2
    have hx_src : x ∈ oddSigmaSources N u := Finset.mem_filter.mpr ⟨hxu.1, hxu.2.2⟩
    rcases hpair with hempty | ⟨hsrc, _, _, hgcd⟩
    · rw [hempty] at hx_src
      exact absurd hx_src (Finset.notMem_empty x)
    · have hy_mem : y ∈ N.primeFactors := huy.2.1
      rw [hpart] at hy_mem
      have hy_qr : y = q ∨ y = r₀ := by
        rcases Finset.mem_insert.mp hy_mem with rfl | hy1
        · exact Or.inl rfl
        · rcases Finset.mem_insert.mp hy1 with rfl | hy2
          · exact Or.inr rfl
          · exfalso
            have hy_dvd : y ∣ sigma 1 (u ^ N.factorization u) :=
              Nat.dvd_of_mem_primeFactors (Finsupp.mem_support_iff.mpr huy.2.2.pos.ne')
            exact hsq_ndvd u hu y hy2 hy_dvd
      refine ⟨u, hu, hsrc, hgcd, ?_⟩
      rcases hy_qr with rfl | rfl
      · exact Or.inl huy
      · exact Or.inr huy
  by_cases hp : p ∈ squareSources N
  · have hin : ∃ x, oddSigmaEdge N x p := by
      cases hcyc with
      | single h1 => exact ⟨_, h1⟩
      | tail _ h2 => exact ⟨_, h2⟩
    have hout : ∃ y, oddSigmaEdge N p y := by
      cases hcyc using Relation.TransGen.head_induction_on with
      | single h1 => exact ⟨_, h1⟩
      | head h1 _ => exact ⟨_, h1⟩
    obtain ⟨x, hx⟩ := hin
    obtain ⟨y, hy⟩ := hout
    exact Or.inr (hsq_step p hp x y hx hy)
  · rcases oddSigmaEdge_transGen_dichotomy hpart hcyc hp hp with
      ⟨u, hu, ⟨x, hx⟩, ⟨y, hy⟩⟩ | ⟨_, _, heq_cyc, _, _⟩
    · exact Or.inr (hsq_step u hu x y hx hy)
    · exact Or.inl (heq_cyc rfl)

private theorem prod_mod_four_eq_one_of_primeFactors {m : ℕ} (hm0 : m ≠ 0)
    (hmod : ∀ w ∈ m.primeFactors, w % 4 = 1) : m % 4 = 1 := by
  rw [Nat.prod_primeFactors_pow_factorization hm0]
  refine Finset.prod_induction _ (fun x => x % 4 = 1) ?_ (by decide) ?_
  · intro a b ha hb
    rw [Nat.mul_mod, ha, hb]
  · intro p hp
    rw [Nat.pow_mod, hmod p hp]
    simp

/-- **Mod-12 Congruence on Square Sources when `r₀ % 4 = 1`**:
On a three-free restrained odd perfect number (`¬ 3 ∣ N`, `largeSources N q = {r₀}`),
if `r₀ % 4 = 1`, then every prime factor of `u ^ 2 + u + 1` (`u ∈ squareSources N`) is
`≡ 1 [MOD 4]`, forcing `(u ^ 2 + u + 1) % 4 = 1` and hence `u % 12 = 11`. -/
theorem restrained_three_free_mod_four_square_sources {N q r₀ : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) (hr₀ : largeSources N q = {r₀}) (hr₀4 : r₀ % 4 = 1) :
    ∀ u ∈ squareSources N, u % 12 = 11 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hpart, _, _, hS_prop, _⟩ :=
    restrained_three_free_invariants ho hN hq hq4 he hev h3 hr₀
  intro u hu
  obtain ⟨hu_prime, hu_odd, _, _, _, hu_exp2, hu_mod3, _, hsig_u⟩ := hS_prop u hu
  have hsum_ne0 : u ^ 2 + u + 1 ≠ 0 := by positivity
  have hsum_odd : Odd (u ^ 2 + u + 1) :=
    ((hu_odd.pow).add_odd hu_odd).add_odd (by decide : Odd 1)
  have hsum_mod4 : (u ^ 2 + u + 1) % 4 = 1 := by
    refine prod_mod_four_eq_one_of_primeFactors hsum_ne0 ?_
    intro w hw
    obtain ⟨hw_prime, hw_dvd, _⟩ := Nat.mem_primeFactors.mp hw
    have hw_odd : Odd w := hsum_odd.of_dvd_nat hw_dvd
    have hw_N : w ∣ N := by
      apply dvd_perfect_of_exact_prime_pow hN hu_prime (Nat.ordProj_dvd N u) _ hw_prime hw_odd
      · rw [← sigma_one_apply, hsig_u]
        exact hw_dvd
      · rw [hu_prime.pow_dvd_iff_le_factorization hN.2.ne']
        omega
    have hw_mem : w ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hw_prime, hw_N, hN.2.ne'⟩
    rw [hpart] at hw_mem
    rcases Finset.mem_insert.mp hw_mem with rfl | hw1
    · exact hq4
    · rcases Finset.mem_insert.mp hw1 with rfl | hwS
      · exact hr₀4
      · exfalso
        have hw_mod3 := (hS_prop w hwS).2.2.2.2.2.2.1
        have hdich := prime_dvd_sq_add_self_add_one hw_prime hw_dvd
        omega
  have hu_mod2 : u % 2 = 1 := Nat.odd_iff.mp hu_odd
  have hu_not1 : u % 4 ≠ 1 := by
    intro hu1
    have h3m : (u ^ 2 + u + 1) % 4 = 3 := by
      rw [Nat.add_mod, Nat.add_mod (u ^ 2), Nat.pow_mod, hu1]
    omega
  omega

end OddPerfect
