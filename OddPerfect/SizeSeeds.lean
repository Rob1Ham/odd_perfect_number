module

public import OddPerfect.SizeChain
public import OddPerfect.HigherCountSeeds

/-! Absolute size bounds from the least allowed prime and counts with and without multiplicity. -/

public section

namespace OddPerfect

open ArithmeticFunction Finset

private theorem prime_interval_prod_le {a b : ℕ} (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ a ≤ p) (hc : s.card = ((Icc a b).filter Nat.Prime).card) :
    (∏ p ∈ (Icc a b).filter Nat.Prime, p) ≤ ∏ p ∈ s, p := by
  let t := (Icc a b).filter Nat.Prime
  have hd : (t \ s).card = (s \ t).card := by
    rw [card_sdiff, card_sdiff, inter_comm t s, hc]
  have hl : (∏ p ∈ t \ s, p) ≤ b^(t \ s).card := by
    calc
      _ ≤ ∏ _p ∈ t \ s, b := by
        apply prod_le_prod (fun p hp => (mem_Icc.mp (mem_filter.mp (mem_sdiff.mp hp).1).1).2)
      _ = _ := by simp
  have hr : b^(s \ t).card ≤ ∏ p ∈ s \ t, p := by
    calc
      _ = ∏ _p ∈ s \ t, b := by simp
      _ ≤ _ := by
        apply prod_le_prod
        intro p hp
        obtain ⟨hps, hpt⟩ := mem_sdiff.mp hp
        obtain ⟨hp', hpa⟩ := hs p hps
        by_contra! hn
        exact hpt (mem_filter.mpr ⟨mem_Icc.mpr ⟨hpa, hn.le⟩, hp'⟩)
  rw [hd] at hl
  calc
    _ = (∏ p ∈ t ∩ s, p) * (∏ p ∈ t \ s, p) := (prod_inter_mul_prod_sdiff t s _).symm
    _ ≤ (∏ p ∈ t ∩ s, p) * (∏ p ∈ s \ t, p) := Nat.mul_le_mul_left _ (hl.trans hr)
    _ = _ := by rw [inter_comm t s, prod_inter_mul_prod_sdiff s t _]

private theorem count_product_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    cardFactors (∏ p ∈ s, p) = s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hprime := hs p (mem_insert_self ..)
    have hrest := fun q (hq : q ∈ s) => hs q (mem_insert_of_mem hq)
    have hpos : (∏ q ∈ s, q) ≠ 0 := (prod_pos fun q hq => (hrest q hq).pos).ne'
    rw [prod_insert hp, cardFactors_mul hprime.ne_zero hpos, cardFactors_eq_one_iff_prime.mpr hprime,
      ih hrest, card_insert_of_notMem hp, Nat.add_comm]

/-- Assign two copies to each of the selected nonspecial primes. Each unassigned
factor is at least a. The first primes at least a minimize the selected product. -/
theorem size_of_prime_interval_counts {N a b total : ℕ} (ho : Odd N) (hN : N.Perfect) (ha : 0 < a)
    (hfloor : ∀ p ∈ N.primeFactors, a ≤ p) (hcount : total ≤ cardFactors N)
    (hcard : ((Icc a b).filter Nat.Prime).card < N.primeFactors.card) :
    let t := (Icc a b).filter Nat.Prime
    (∏ p ∈ t, p)^2 * a^(total-2*t.card) ≤ N := by
  let t := (Icc a b).filter Nat.Prime
  change (∏ p ∈ t, p)^2 * a^(total-2*t.card) ≤ N
  obtain ⟨q, hqN, _, _, hev⟩ := euler_exponents ho hN
  have ht : t.card ≤ (N.primeFactors.erase q).card := by
    have hc := card_erase_add_one hqN
    change t.card < _ at hcard
    omega
  obtain ⟨s, hs, hsc⟩ := exists_subset_card_eq ht
  have inN (p) (hp : p ∈ s) := mem_of_mem_erase (hs hp)
  have prime (p) (hp : p ∈ s) := Nat.prime_of_mem_primeFactors (inN p hp)
  let v := ∏ p ∈ s, p
  have hv0 : v ≠ 0 := (prod_pos fun p hp => (prime p hp).pos).ne'
  have hd : v^2 ∣ N := by
    rw [Nat.prod_primeFactors_pow_factorization hN.2.ne']
    apply dvd_trans _ (prod_dvd_prod_of_subset s N.primeFactors _ (fun p hp => inN p hp))
    dsimp only [v]
    rw [← prod_pow]
    apply prod_dvd_prod_of_dvd
    intro p hp
    obtain ⟨j, hj⟩ := hev p (mem_erase.mp (hs hp)).1
    have hpos : 0 < N.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (inN p hp))
    exact pow_dvd_pow p (by omega)
  obtain ⟨m, hm⟩ := hd
  have hm0 := (mul_ne_zero_iff.mp (hm ▸ hN.2.ne')).2
  have hmN : m ∣ N := hm ▸ Nat.dvd_mul_left _ _
  have hfac : cardFactors N = 2*t.card + cardFactors m := by
    rw [hm, cardFactors_mul (pow_ne_zero _ hv0) hm0, cardFactors_pow, count_product_primes s prime, hsc]
  have hfloorM : a^cardFactors m ≤ m := FactorBudget.pow_cardFactors_le hm0
    (fun p hp => hfloor p (Nat.primeFactors_mono hmN hN.2.ne' hp))
  have hprod : (∏ p ∈ t, p) ≤ v := prime_interval_prod_le s
    (fun p hp => ⟨prime p hp, hfloor p (inN p hp)⟩) hsc
  rw [hm]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left hprod 2)
    ((Nat.pow_le_pow_right ha (show total-2*t.card ≤ cardFactors m by omega)).trans hfloorM)

private theorem size_from_cut {N a b total w avoid exponent : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hav : avoid.Coprime N) (hf : FactorBudget.root.residualFloor avoid = a) (ha : 0 < a)
    (ht : total ≤ cardFactors N) (hw : w ≤ N.primeFactors.card)
    (hc : ((Icc a b).filter Nat.Prime).card < w)
    (hnum : let t := (Icc a b).filter Nat.Prime
      10^exponent < (∏ p ∈ t, p)^2 * a^(total-2*t.card)) : 10^exponent < N := by
  have hfloor := FactorBudget.residualFloor_le (FactorBudget.root_realizes N) ho hav
  rw [hf] at hfloor
  exact hnum.trans_le (size_of_prime_interval_counts ho hN ha hfloor ht (hc.trans_le hw))

/-- Without 3 or 5, fourteen nonspecial prime squares give over 47 decimal powers. -/
theorem size_of_three_five_free {N : ℕ} (ho : Odd N) (hN : N.Perfect) (h3 : ¬ 3 ∣ N)
    (h5 : ¬ 5 ∣ N) : 10^47 < N := by
  have hav : Nat.Coprime 15 N := ((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr h3).mul_left
    ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr h5)
  apply size_from_cut (a := 7) (b := 59) ho hN hav (by decide) (by decide)
    (total_count_of_three_five_free ho hN h3 h5) (fifteen_distinct_of_three_five_free ho hN h3 h5)
  all_goals decide +kernel

/-- The least prime exceeding 7 gives a three-seed complement past 10^106. -/
theorem size_of_three_five_seven_free {N : ℕ} (ho : Odd N) (hN : N.Perfect) (h3 : ¬ 3 ∣ N)
    (h5 : ¬ 5 ∣ N) (h7 : ¬ 7 ∣ N) : 10^106 < N := by
  have hav : Nat.Coprime 105 N := (((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr h3).mul_left
    ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr h5)).mul_left
    ((by decide : Nat.Prime 7).coprime_iff_not_dvd.mpr h7)
  obtain ⟨hw, ht⟩ := counts_of_three_five_seven_free ho hN h3 h5 h7
  apply size_from_cut (a := 11) (b := 113) ho hN hav (by decide) (by decide) ht hw
  all_goals decide +kernel

/-- The least prime exceeding 11 gives a four-seed complement past 10^180. -/
theorem size_of_three_five_seven_eleven_free {N : ℕ} (ho : Odd N) (hN : N.Perfect)
    (h3 : ¬ 3 ∣ N) (h5 : ¬ 5 ∣ N) (h7 : ¬ 7 ∣ N) (h11 : ¬ 11 ∣ N) : 10^180 < N := by
  have hav : Nat.Coprime 1155 N := ((((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr h3).mul_left
    ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr h5)).mul_left
    ((by decide : Nat.Prime 7).coprime_iff_not_dvd.mpr h7)).mul_left
    ((by decide : Nat.Prime 11).coprime_iff_not_dvd.mpr h11)
  obtain ⟨hw, ht⟩ := counts_of_three_five_seven_eleven_free ho hN h3 h5 h7 h11
  apply size_from_cut (a := 13) (b := 197) ho hN hav (by decide) (by decide) ht hw
  all_goals decide +kernel

end OddPerfect
