module

public import OddPerfect.ChainScript
import Mathlib.Data.Nat.Log

/-! Factor-chain certificates for absolute lower bounds on an odd perfect number. -/

public section

namespace OddPerfect.FactorBudget

open ArithmeticFunction

/-- Each prime counted with multiplicity contributes at least the supplied lower bound. -/
theorem pow_cardFactors_le {a m : ℕ} (hm : m ≠ 0) (hf : ∀ p ∈ m.primeFactors, a ≤ p) :
    a ^ cardFactors m ≤ m := by
  have list_bound (ps : List ℕ) (hh : ∀ p ∈ ps, a ≤ p) : a^ps.length ≤ ps.prod := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
      rw [List.length_cons, pow_succ', List.prod_cons]
      exact Nat.mul_le_mul (hh p List.mem_cons_self) (ih (fun q hq => hh q (List.mem_cons_of_mem _ hq)))
  simpa [cardFactors_apply, Nat.prod_primeFactorsList hm] using
    list_bound m.primeFactorsList (fun p hp => hf p (Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hp))

/-- The list of possible small residual primes can be capped at any fixed
endpoint. Absence below the endpoint gives that endpoint as a lower bound. -/
@[expose] def Node.residualFloor (s : Node) (avoid : ℕ) : ℕ :=
  max 2 ((s.belowPrimes avoid 43).foldr min 43)

private theorem fold_min_le (xs : List ℕ) (last : ℕ) :
    xs.foldr min last ≤ last ∧ ∀ q ∈ xs, xs.foldr min last ≤ q := by
  induction xs with
  | nil => simp
  | cons p ps ih =>
    refine ⟨(min_le_right _ _).trans ih.1, ?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih.2 q hq)

theorem residualFloor_le {N m avoid : ℕ} {s : Node} (h : Realizes s N m) (ho : Odd N)
    (hav : avoid.Coprime N) : ∀ q ∈ m.primeFactors, s.residualFloor avoid ≤ q := by
  intro q hq
  obtain ⟨hq', hd, _⟩ := Nat.mem_primeFactors.mp hq
  have hmN : m ∣ N := h.value ▸ Nat.dvd_mul_left _ _
  have hNdiv := hd.trans hmN
  have hle := fold_min_le (s.belowPrimes avoid 43) 43
  apply max_le hq'.two_le
  by_cases hlt : q < 43
  · apply hle.2
    refine List.mem_filter.mpr ⟨List.mem_range.mpr hlt, decide_eq_true ⟨hq', ?_, ?_, ?_⟩⟩
    · rintro rfl
      exact ho.not_two_dvd_nat hNdiv
    · exact fun hd' => hq'.not_dvd_one (h.coprime.gcd_eq_one ▸ Nat.dvd_gcd hd' hd)
    · exact fun hd' => hq'.not_dvd_one (hav.gcd_eq_one ▸ Nat.dvd_gcd hd' hNdiv)
  · exact hle.1.trans (by omega)

@[expose] def Node.sizeBudget (s : Node) (avoid X : ℕ) : ℕ :=
  s.spent + Nat.log (s.residualFloor avoid) (X/s.component)

private theorem residual_data {N m X avoid : ℕ} {s : Node} (h : Realizes s N m) (ho : Odd N)
    (hav : avoid.Coprime N) (hX : N ≤ X) :
    cardFactors N = s.spent + cardFactors m ∧ m ≤ X/s.component ∧
      s.residualFloor avoid ^ cardFactors m ≤ m := by
  obtain ⟨hD, hm⟩ := mul_ne_zero_iff.mp (h.value ▸ ho.pos.ne')
  refine ⟨?_, ?_, pow_cardFactors_le hm (residualFloor_le h ho hav)⟩
  · rw [h.value, cardFactors_mul hD hm, h.spent]
  · apply (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hD)).2
    simpa [h.value, Nat.mul_comm] using hX

theorem sizeBudget_valid {N m X avoid : ℕ} {s : Node} (h : Realizes s N m) (ho : Odd N)
    (hav : avoid.Coprime N) (hX : N ≤ X) : cardFactors N ≤ s.sizeBudget avoid X := by
  obtain ⟨he, hsize, hpow⟩ := residual_data h ho hav hX
  rw [Node.sizeBudget, he]
  exact Nat.add_le_add_left (Nat.le_log_of_pow_le (lt_of_lt_of_le (by decide : 1 < 2) (le_max_left ..))
    (hpow.trans hsize)) _

/-- The forced divisor and the unspent global count each provide a size obstruction. -/
@[expose] def Node.overSize (s : Node) (X avoid low : ℕ) : Bool :=
  decide (X < s.component*s.forcedPart ∨ X < s.component*s.residualFloor avoid ^ (low-s.spent))

theorem overSize_false {N m X avoid low : ℕ} {s : Node} (h : Realizes s N m) (ho : Odd N)
    (hN : N.Perfect) (hav : avoid.Coprime N) (hX : N ≤ X) (hlow : low ≤ cardFactors N)
    (test : s.overSize X avoid low = true) : False := by
  have hm := (mul_ne_zero_iff.mp (h.value ▸ ho.pos.ne')).2
  obtain ⟨he, _, hpow⟩ := residual_data h ho hav hX
  rcases of_decide_eq_true test with hK | hf
  · have ht := Nat.mul_le_mul_left s.component (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (forcedPart_dvd h hN))
    rw [← h.value] at ht
    omega
  · have hfpos : 0 < s.residualFloor avoid := lt_of_lt_of_le (by decide : 0 < 2) (le_max_left ..)
    have ht := Nat.mul_le_mul_left s.component ((Nat.pow_le_pow_right hfpos (show low-s.spent ≤ cardFactors m by omega)).trans hpow)
    rw [← h.value] at ht
    omega

/-- The ordinary exact-exponent search, with a node-dependent total-factor
budget and an exponent cap imposed by the absolute size limit. -/
@[expose] def replaySize (primes : List ℕ) (seed avoid X w c low stride : ℕ) :
    ℕ → Node → Script → Bool
  | 0, _, _ => false
  | fuel+1, s, tree =>
    if s.overSize X avoid low then true else
    let B := s.sizeBudget avoid X
    if s.automatic B w then true else
    match prepareTightChoices primes (fun _ => tree.hint?) seed avoid B w c s with
    | none => false
    | some ps => ps.all fun p => (List.range (min (B-s.spent) (Nat.log p (X/s.component)))).all fun i =>
        replaySize primes seed avoid X w c low stride fuel (s.extend p (i+1))
          (tree.child (ps.idxOf p * stride + (i+1)))

/-- Every real odd perfect number at most X follows a branch at each step. -/
theorem replaySize_correct {N seed avoid X w c low stride : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hw : w ≤ N.primeFactors.card) (hseed : seed ∣ N) (hav : avoid.Coprime N) (hX : N ≤ X)
    (hcount : 18*N.primeFactors.card ≤ 7*cardFactors N+c) (hlow : low ≤ cardFactors N)
    (primes : List ℕ) (hp : ∀ p ∈ primes, p.Prime) (fuel : ℕ) {s : Node} {m : ℕ}
    (h : Realizes s N m) (tree : Script)
    (test : replaySize primes seed avoid X w c low stride fuel s tree = true) : False := by
  induction fuel generalizing s m tree with
  | zero => simp [replaySize] at test
  | succ fuel ih =>
    let B := s.sizeBudget avoid X
    have H : Conditions N B w := ⟨ho, hN, sizeBudget_valid h ho hav hX, hw⟩
    by_cases hsz : s.overSize X avoid low = true
    · exact overSize_false h ho hN hav hX hlow hsz
    by_cases ha : s.automatic B w = true
    · exact automatic_false H h ha
    cases hsteps : prepareTightChoices primes (fun _ => tree.hint?) seed avoid B w c s with
    | none =>
      dsimp only [B] at ha hsteps
      simp [replaySize, hsz, ha, hsteps] at test
    | some ps =>
      dsimp only [B] at ha hsteps
      simp only [replaySize, hsz, Bool.false_eq_true, ↓reduceIte, ha,
        hsteps, List.all_eq_true, List.mem_range] at test
      have hc : 18*N.primeFactors.card ≤ 7*B+c := by have := H.count; omega
      obtain ⟨p, hpm, hprime, hd⟩ := prepareTightChoices_correct H hseed hav hc primes hp _ h hsteps
      obtain ⟨he, hu⟩ := exponent_bounds H h hprime hd
      have hm := (mul_ne_zero_iff.mp (h.value ▸ ho.pos.ne')).2
      have hpow := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.ordProj_dvd m p)
      have hsize := (residual_data h ho hav hX).2.1
      have hcap := Nat.le_log_of_pow_le hprime.one_lt (hpow.trans hsize)
      change m.factorization p ≤ Nat.log p (X/s.component) at hcap
      have hnext := test p hpm (m.factorization p-1) (by omega)
      rw [Nat.sub_add_cancel he] at hnext
      exact ih (extend_realizes ho.pos.ne' h hprime hd) _ hnext

end OddPerfect.FactorBudget
