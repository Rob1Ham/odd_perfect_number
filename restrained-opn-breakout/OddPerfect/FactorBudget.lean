module

public import OddPerfect.Counts
public import OddPerfect.FewPrimes
import Mathlib.Algebra.Order.Ring.Abs

/-! Exact coprime components and residual budgets for factor-chain certificates. -/

public section

namespace OddPerfect.FactorBudget

open ArithmeticFunction

/-- Numeric data retained after assigning exact exponents to distinct primes. -/
structure Node where
  component : ℕ
  divisorSum : ℕ
  spent : ℕ
  closed : ℕ
  deriving Repr

@[expose] def root : Node := ⟨1, 1, 0, 0⟩

@[expose] def Node.extend (s : Node) (p e : ℕ) : Node :=
  ⟨s.component * p ^ e, s.divisorSum * SupportSieve.geomValue p (e + 1), s.spent + e, s.closed + 1⟩

/-- The true cofactor is retained symbolically through every branch. -/
structure Realizes (s : Node) (N m : ℕ) : Prop where
  value : N = s.component * m
  coprime : s.component.Coprime m
  sigma : sigma 1 s.component = s.divisorSum
  spent : cardFactors s.component = s.spent
  closed : cardDistinctFactors s.component = s.closed

/-- The known global bounds for a putative odd perfect number. -/
structure Conditions (N budget minDistinct : ℕ) : Prop where
  odd : Odd N
  perfect : N.Perfect
  count : cardFactors N ≤ budget
  distinct : minDistinct ≤ N.primeFactors.card

theorem root_realizes (N : ℕ) : Realizes root N N := by
  constructor <;> simp [root]

private theorem nonzero {s : Node} {N m : ℕ} (h : Realizes s N m) (hN : N ≠ 0) :
    s.component ≠ 0 ∧ m ≠ 0 := mul_ne_zero_iff.mp (h.value ▸ hN)

/-- The part of the assigned divisor sum not absorbed by twice the assigned
component must divide the remaining cofactor. -/
@[expose] def Node.forcedPart (s : Node) : ℕ := s.divisorSum / s.divisorSum.gcd (2*s.component)

private theorem balance {s : Node} {N m : ℕ} (h : Realizes s N m) (hN : N.Perfect) :
    s.divisorSum * sigma 1 m = 2*s.component*m := by
  rw [← h.sigma, ← isMultiplicative_sigma.map_mul_of_coprime h.coprime, ← h.value,
    sigma_one_apply, (Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN, h.value, Nat.mul_assoc]

theorem forcedPart_dvd {s : Node} {N m : ℕ} (h : Realizes s N m) (hN : N.Perfect) :
    s.forcedPart ∣ m := by
  have ha : 0 < s.divisorSum := h.sigma ▸ sigma_pos 1 _ (nonzero h hN.2.ne').1
  have hd : s.divisorSum ∣ (2*s.component)*m := (balance h hN) ▸ dvd_mul_right _ _
  have hcancel := Nat.dvd_gcd (Nat.dvd_mul_right s.divisorSum m) hd
  rw [Nat.gcd_mul_right] at hcancel
  apply (Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left s.divisorSum (2*s.component))
    (Nat.gcd_pos_of_pos_left _ ha)).2
  exact hcancel

/-- A forced prime is assigned its full valuation in the remaining cofactor. -/
theorem extend_realizes {s : Node} {N m p : ℕ} (hN : N ≠ 0) (h : Realizes s N m)
    (hp : p.Prime) (hd : p ∣ m) :
    Realizes (s.extend p (m.factorization p)) N (ordCompl[p] m) := by
  let e := m.factorization p
  have hm := (nonzero h hN).2
  have hD := (nonzero h hN).1
  have he : 0 < e := (hp.dvd_iff_one_le_factorization hm).mp hd
  have hsplit : p ^ e * ordCompl[p] m = m := Nat.ordProj_mul_ordCompl_eq_self m p
  have hDp := (h.coprime.coprime_dvd_right hd).pow_right e
  have hpM := (Nat.coprime_ordCompl hp hm).pow_left e
  have hgeom : SupportSieve.geomValue p (e+1) = sigma 1 (p^e) := by
    rw [sigma_one_apply_prime_pow hp, SupportSieve.geomValue, ← geom_sum_mul_of_one_le hp.one_le,
      Nat.mul_div_cancel _ (by have := hp.one_lt; omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change N = s.component * p^e * _
    rw [mul_assoc, hsplit, ← h.value]
  · exact (h.coprime.coprime_dvd_right (Nat.ordCompl_dvd m p)).mul_left hpM
  · change sigma 1 (s.component * p^e) = _ * _
    rw [isMultiplicative_sigma.map_mul_of_coprime hDp, h.sigma, hgeom]
  · change cardFactors (s.component * p^e) = _ + _
    rw [cardFactors_mul hD (pow_ne_zero _ hp.ne_zero), h.spent, cardFactors_apply_prime_pow hp]
  · change cardDistinctFactors (s.component * p^e) = _ + 1
    rw [cardDistinctFactors_mul hDp, h.closed, cardDistinctFactors_apply_prime_pow hp he.ne']

private theorem sum_counts {s : Node} {N m : ℕ} (h : Realizes s N m) (hN : N ≠ 0) :
    cardFactors N = s.spent + cardFactors m := by
  obtain ⟨hD, hm⟩ := nonzero h hN
  rw [h.value, cardFactors_mul hD hm, h.spent]

private theorem residual_euler {s : Node} {N m : ℕ} (h : Realizes s N m) (ho : Odd N)
    (hN : N.Perfect) : 2*m.primeFactors.card ≤ cardFactors m + 1 := by
  obtain ⟨sp, _, _, _, hev⟩ := euler_exponents ho hN
  obtain ⟨hD, hm⟩ := nonzero h ho.pos.ne'
  have two {p : ℕ} (hp : p ∈ m.primeFactors) (hps : p ≠ sp) : 2 ≤ m.factorization p := by
    have hpos : 0 < m.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    have hpD : p ∉ s.component.primeFactors := fun h' =>
      Finset.disjoint_left.mp h.coprime.disjoint_primeFactors h' hp
    obtain ⟨k, hk⟩ := hev p hps
    rw [h.value, Nat.factorization_mul hD hm, Finsupp.add_apply,
      Finsupp.notMem_support_iff.mp hpD, zero_add] at hk
    omega
  rw [cardFactors_eq_sum_factorization]
  change 2*m.primeFactors.card ≤ (∑ p ∈ m.primeFactors, m.factorization p) + 1
  by_cases hs : sp ∈ m.primeFactors
  · have hl := Finset.sum_le_sum (s := m.primeFactors.erase sp) (f := fun _ => 2)
      (g := fun p => m.factorization p) (fun _ hp => two (Finset.mem_of_mem_erase hp) (Finset.mem_erase.mp hp).1)
    simp only [Finset.sum_const, smul_eq_mul] at hl
    have hterm : 0 < m.factorization sp := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hs)
    have hc := Finset.card_erase_add_one hs
    have ht := Finset.add_sum_erase m.primeFactors (fun p => m.factorization p) hs
    omega
  · have hl := Finset.sum_le_sum (s := m.primeFactors) (f := fun _ => 2)
      (g := fun p => m.factorization p) (fun p hp => two hp (fun he => hs (he ▸ hp)))
    simp only [Finset.sum_const, smul_eq_mul] at hl
    omega

/-- Each remaining distinct prime costs two copies, except for a possible
Euler prime. The parity of the count already spent determines that exception. -/
theorem budget_bound {s : Node} {N m B w : ℕ} (H : Conditions N B w) (h : Realizes s N m)
    {k : ℕ} (hk : k ≤ m.primeFactors.card) :
    s.spent + 2 * max k (w-s.closed) + s.spent % 2 ≤ B+1 := by
  have hr := residual_euler h H.odd H.perfect
  have ht := sum_counts h H.odd.pos.ne'
  have oddCount := Nat.odd_iff.mp (odd_total_prime_factor_count H.odd H.perfect)
  rw [← cardFactors_apply, ht] at oddCount
  have hω : N.primeFactors.card = s.closed + m.primeFactors.card := by
    rw [← cardDistinctFactors_eq_card_primeFactors, h.value, cardDistinctFactors_mul h.coprime,
      h.closed, cardDistinctFactors_eq_card_primeFactors]
  have hl := H.distinct
  have hu := H.count
  have hle : max k (w-s.closed) ≤ m.primeFactors.card := max_le hk (by omega)
  omega

/-- Pairwise coprime positive factors greater than one each force a distinct
prime, even when their prime factorizations are unknown. -/
@[expose] def checkGroups : List ℕ → Bool
  | [] => true
  | a :: rest => decide (1 < a ∧ a.Coprime rest.prod) && checkGroups rest

private theorem group_count (gs : List ℕ) (h : checkGroups gs = true) :
    gs.length ≤ cardDistinctFactors gs.prod := by
  induction gs with
  | nil => simp
  | cons a gs ih =>
    simp only [checkGroups, Bool.and_eq_true, decide_eq_true_eq] at h
    have := ih h.2
    have := cardDistinctFactors_pos.mpr h.1.1
    rw [List.length_cons, List.prod_cons, cardDistinctFactors_mul h.1.2]
    omega

theorem groups_le_support {s : Node} {N m : ℕ} (hN : N.Perfect) (h : Realizes s N m)
    (gs : List ℕ) (hg : checkGroups gs = true) (hd : gs.prod ∣ s.forcedPart) :
    gs.length ≤ m.primeFactors.card := by
  have hc := group_count gs hg
  rw [cardDistinctFactors_eq_card_primeFactors] at hc
  exact hc.trans (Finset.card_le_card (Nat.primeFactors_mono (hd.trans (forcedPart_dvd h hN))
    (nonzero h hN.2.ne').2))

/-- Tests using only the assigned component, the global budget and the
minimum support size. When only one factor remains, its divisor sum is linear. -/
@[expose] def Node.automatic (s : Node) (budget minDistinct : ℕ) : Bool :=
  decide (4 ∣ s.divisorSum ∨ 2*s.component < s.divisorSum ∨
    ¬ s.component.Coprime s.forcedPart ∨
    (budget ≤ s.spent+1 ∧ s.divisorSum < 2*s.component ∧
      ¬ (2*s.component-s.divisorSum) ∣ s.divisorSum) ∨
    budget+1 < s.spent + 2*(minDistinct-s.closed) + s.spent%2)

theorem automatic_false {s : Node} {N m B w : ℕ} (H : Conditions N B w) (h : Realizes s N m)
    (test : s.automatic B w = true) : False := by
  have hm := (nonzero h H.odd.pos.ne').2
  have hb := balance h H.perfect
  have hc := sum_counts h H.odd.pos.ne'
  have hu := H.count
  rcases of_decide_eq_true test with h4 | hab | hcop | ⟨hsmall, hdef, hnod⟩ | hbudget
  · have hd : s.divisorSum ∣ 2*N := by
      rw [h.value, ← mul_assoc, ← hb]
      exact dvd_mul_right _ _
    have := h4.trans hd
    have := H.odd.not_two_dvd_nat
    omega
  · have hself : m ≤ sigma 1 m := by
      rw [sigma_one_apply]
      exact Finset.single_le_sum (f := fun i : ℕ => i) (fun _ _ => Nat.zero_le _)
        (Nat.mem_divisors_self m hm)
    have hle := Nat.mul_le_mul_left s.divisorSum hself
    rw [hb] at hle
    exact hab.not_ge ((mul_le_mul_iff_left₀ (Nat.pos_of_ne_zero hm)).mp hle)
  · exact hcop (h.coprime.coprime_dvd_right (forcedPart_dvd h H.perfect))
  · have hl : cardFactors m ≤ 1 := by omega
    rcases Nat.eq_zero_or_pos (cardFactors m) with hz | hp
    · have hm1 := (cardFactors_eq_zero_iff_eq_zero_or_one.mp hz).resolve_left hm
      simp [hm1] at hb
      omega
    · have hp' := cardFactors_eq_one_iff_prime.mp (show cardFactors m = 1 by omega)
      have hs : sigma 1 m = m+1 := by rw [sigma_one_apply, hp'.sum_divisors]
      rw [hs, Nat.mul_add, Nat.mul_one] at hb
      apply hnod
      refine ⟨m, ?_⟩
      rw [Nat.mul_sub_right_distrib, ← hb]
      omega
  · have hl := budget_bound H h (k := 0) (Nat.zero_le _)
    simp only [Nat.zero_max] at hl
    omega

/-- A branch must cover every possible exact exponent of its chosen prime. -/
theorem exponent_bounds {s : Node} {N m p B w : ℕ} (H : Conditions N B w) (h : Realizes s N m)
    (hp : p.Prime) (hd : p ∣ m) :
    1 ≤ m.factorization p ∧ m.factorization p ≤ B-s.spent := by
  have hm := (nonzero h H.odd.pos.ne').2
  have he := (hp.dvd_iff_one_le_factorization hm).mp hd
  have hc := sum_counts h H.odd.pos.ne'
  have hu := H.count
  have htotal : cardFactors m = ∑ r ∈ m.primeFactors, m.factorization r :=
    cardFactors_eq_sum_factorization (n := m)
  have hsum := Finset.single_le_sum (f := fun r => m.factorization r) (fun _ _ => Nat.zero_le _)
    (Nat.mem_primeFactors.mpr ⟨hp, hd, hm⟩)
  exact ⟨he, by omega⟩

end OddPerfect.FactorBudget
