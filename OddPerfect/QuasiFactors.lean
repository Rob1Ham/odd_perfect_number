module

public import OddPerfect.SpoofFactors
public import OddPerfect.Euler
public import OddPerfect.CandidateSets
import Mathlib.Algebra.Order.BigOperators.Ring.List

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- Replace a component by successive blocks of the given lengths.
The base for the next block is the current base raised to the current length. -/
@[expose] def refineComponent (x : ℕ) : List ℕ → List (ℕ × ℕ)
  | [] => []
  | q :: qs => (x, q-1) :: refineComponent (x^q) qs

/-- Product of the indicated powers, including multiplicities of indexed entries. -/
@[expose] def listValue (X : List (ℕ × ℕ)) : ℕ := (X.map (fun z => z.1 ^ z.2)).prod

/-- The formal geometric divisor sum for a list of quasi-prime factors. -/
@[expose] def listFormalSigma (X : List (ℕ × ℕ)) : ℕ :=
  (X.map (fun z => ∑ j ∈ range (z.2+1), z.1 ^ j)).prod

private theorem geom_blocks (x q m : ℕ) :
    (∑ j ∈ range (q*m), x^j) = (∑ j ∈ range q, x^j) * ∑ j ∈ range m, (x^q)^j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ, mul_add]
    simp_rw [pow_add, ← mul_sum, ← pow_mul]
    rw [mul_comm (x^(q*m))]

/-- Dittmer's geometric block decomposition preserves both integer products,
for any ordering of the prime divisors of the component length. -/
theorem refineComponent_products (x : ℕ) (qs : List ℕ) (hp : ∀ q ∈ qs, q.Prime) :
    listValue (refineComponent x qs) = x ^ (qs.prod-1) ∧
    listFormalSigma (refineComponent x qs) = ∑ j ∈ range qs.prod, x^j := by
  induction qs generalizing x with
  | nil => simp [refineComponent, listValue, listFormalSigma]
  | cons q qs ih =>
    have hq := hp q (.head _)
    have hps (p : ℕ) (hm : p ∈ qs) := hp p (.tail q hm)
    have hprod : 0 < qs.prod := CanonicallyOrderedAdd.list_prod_pos.mpr (fun p hm => (hps p hm).pos)
    obtain ⟨hv, hs⟩ := ih (x^q) hps
    change x^(q-1) * listValue (refineComponent (x^q) qs) = x^((q * qs.prod)-1) ∧
      (∑ j ∈ range (q-1+1), x^j) * listFormalSigma (refineComponent (x^q) qs) =
        ∑ j ∈ range (q * qs.prod), x^j
    rw [hv, hs, Nat.sub_add_cancel hq.pos, ← pow_mul, ← pow_add, geom_blocks x q qs.prod]
    constructor
    · congr 1
      have hA := Nat.sub_add_cancel (show 1 ≤ q from hq.pos)
      have hB := Nat.sub_add_cancel (show 1 ≤ qs.prod from hprod)
      have hC := Nat.sub_add_cancel (show 1 ≤ q*qs.prod from Nat.mul_pos hq.pos hprod)
      nlinarith [congrArg (fun z => q*z) hB]
    · rfl

theorem mem_refineComponent {x : ℕ} {qs : List ℕ} (hp : ∀ q ∈ qs, q.Prime)
    {z : ℕ × ℕ} (hz : z ∈ refineComponent x qs) :
    ∃ d : ℕ, 0 < d ∧ z.1 = x^d ∧ z.2+1 ∈ qs ∧ (z.2+1).Prime := by
  induction qs generalizing x with
  | nil => simp [refineComponent] at hz
  | cons q qs ih =>
    have hq := hp q (.head _)
    rcases List.mem_cons.mp hz with rfl | h
    · refine ⟨1, by decide, (pow_one _).symm, ?_, ?_⟩ <;> simp [Nat.sub_add_cancel hq.pos, hq]
    · obtain ⟨d, hd, hval, hm, hprime⟩ := ih (fun p hm => hp p (.tail _ hm)) h
      exact ⟨q*d, Nat.mul_pos hq.pos hd, hval.trans (pow_mul x q d).symm, .tail q hm, hprime⟩

/-- A quasi-prime factorization with prime component lengths obtained from
the true prime factorization. It may contain powers of the original primes. -/
noncomputable def quasiFactors (N : ℕ) : List (ℕ × ℕ) :=
  N.primeFactors.toList.flatMap (fun p => refineComponent p (N.factorization p+1).primeFactorsList)

private theorem listValue_flatMap {ι : Type*} (L : List ι) (f : ι → List (ℕ × ℕ)) :
    listValue (L.flatMap f) = (L.map (fun i => listValue (f i))).prod := by
  induction L with
  | nil => rfl
  | cons i l ih => simpa [listValue, List.prod_append] using congrArg (listValue (f i) * ·) ih

private theorem listFormalSigma_flatMap {ι : Type*} (L : List ι) (f : ι → List (ℕ × ℕ)) :
    listFormalSigma (L.flatMap f) = (L.map (fun i => listFormalSigma (f i))).prod := by
  induction L with
  | nil => rfl
  | cons i l ih => simpa [listFormalSigma, List.prod_append] using congrArg (listFormalSigma (f i) * ·) ih

/-- Dittmer's Corollary 7.3, with the divisor-sum numerator and represented
integer separately identified. -/
theorem quasiFactors_preserve {N : ℕ} (hn : N ≠ 0) :
    listValue (quasiFactors N) = N ∧ listFormalSigma (quasiFactors N) = sigma 1 N := by
  have h (p : ℕ) := refineComponent_products p (N.factorization p+1).primeFactorsList
    (fun _ hm => Nat.prime_of_mem_primeFactorsList hm)
  simp only [Nat.prod_primeFactorsList (Nat.succ_ne_zero _)] at h
  constructor
  · rw [quasiFactors, listValue_flatMap, Finset.prod_map_toList]
    exact (prod_congr rfl (fun p _ => (h p).1)).trans (Nat.prod_primeFactors_pow_factorization hn).symm
  · rw [quasiFactors, listFormalSigma_flatMap, Finset.prod_map_toList]
    apply Eq.trans _ (isMultiplicative_sigma.multiplicative_factorization _ hn).symm
    exact prod_congr rfl (fun p hp => (h p).2.trans (sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)).symm)

theorem mem_quasiFactors {N : ℕ} {z : ℕ × ℕ} (hz : z ∈ quasiFactors N) :
    ∃ p ∈ N.primeFactors, ∃ d : ℕ, 0 < d ∧ z.1 = p^d ∧ (z.2+1).Prime := by
  obtain ⟨p, hp, hm⟩ := List.mem_flatMap.mp hz
  obtain ⟨d, hd, hx, _, hq⟩ := mem_refineComponent (fun _ h => Nat.prime_of_mem_primeFactorsList h) hm
  exact ⟨p, mem_toList.mp hp, d, hd, hx, hq⟩

private theorem no_singles_of_odd_length (x n : ℕ) (ho : Odd n) :
    (refineComponent x n.primeFactorsList).filter (fun z => z.2 == 1) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro z hz
  simp only [beq_iff_eq]
  intro h
  obtain ⟨_, _, _, hm, _⟩ := mem_refineComponent (fun _ h => Nat.prime_of_mem_primeFactorsList h) hz
  rw [h] at hm
  exact ho.not_two_dvd_nat (Nat.dvd_of_mem_primeFactorsList hm)

private theorem flatMap_singleton_once (L : List ℕ) (q : ℕ) (hn : L.Nodup) :
    L.flatMap (fun p => if p = q then [(q,1)] else []) =
      if q ∈ L then [(q,(1 : ℕ))] else [] := by
  induction L with
  | nil => simp
  | cons p ps ih =>
    rcases List.nodup_cons.mp hn with ⟨hnot, htail⟩
    by_cases h : p = q
    · subst p
      simp [List.flatMap_cons, ih htail, hnot]
    · simp [List.flatMap_cons, ih htail, h, Ne.symm h]

/-- The single exponent-one entry in Dittmer's normalization of an odd
perfect number has a genuine prime base. All other lengths are odd primes. -/
theorem quasiFactors_single_euler {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    ∃ q ∈ N.primeFactors, q.Prime ∧ q % 4 = 1 ∧
      (quasiFactors N).filter (fun z => z.2 == 1) = [(q,1)] := by
  obtain ⟨q, hq, hq4, he4, hrest⟩ := euler_exponents ho hN
  have localEq (p : ℕ) :
      (refineComponent p (N.factorization p + 1).primeFactorsList).filter (fun z => z.2 == 1) =
        if p = q then [(q,1)] else [] := by
    by_cases h : p = q
    · subst p
      let t := N.factorization q - 1
      have he : N.factorization q + 1 = t+2 := by dsimp [t]; omega
      have ht : (t+2).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr (by omega)
      have hodd : Odd ((t+2)/2) := Nat.odd_iff.mpr (by omega)
      rw [he, Nat.primeFactorsList_add_two, ht, ite_eq_left (rfl : q = q)]
      change ((q,1) :: refineComponent (q^2) ((t+2)/2).primeFactorsList).filter _ = [(q,1)]
      change (q,1) :: (refineComponent (q^2) ((t+2)/2).primeFactorsList).filter _ = [(q,1)]
      rw [no_singles_of_odd_length (q^2) _ hodd]
    · simp only [h, ite_false]
      exact no_singles_of_odd_length _ _ (by obtain ⟨t, ht⟩ := hrest p h; exact ⟨t, by omega⟩)
  refine ⟨q, hq, Nat.prime_of_mem_primeFactors hq, hq4, ?_⟩
  rw [quasiFactors, List.filter_flatMap]
  simp_rw [localEq]
  rw [flatMap_singleton_once _ _ N.primeFactors.nodup_toList]
  simp [hq]

/-- The same natural number is represented by a formally perfect
factorization with prime lengths and a single genuine linear component. -/
theorem odd_perfect_has_normalized_spoof {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    ∃ X : List (ℕ × ℕ), listValue X = N ∧ listFormalSigma X = 2*N ∧
      (∀ z ∈ X, ∃ p ∈ N.primeFactors, ∃ d : ℕ, 0 < d ∧ z.1 = p^d ∧ (z.2+1).Prime) ∧
      ∃ q ∈ N.primeFactors, q.Prime ∧ q % 4 = 1 ∧ X.filter (fun z => z.2 == 1) = [(q,1)] := by
  obtain ⟨hv, hs⟩ := quasiFactors_preserve hN.2.ne'
  rw [sigma_one_apply, (Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN] at hs
  exact ⟨quasiFactors N, hv, hs, fun _ hz => mem_quasiFactors hz, quasiFactors_single_euler ho hN⟩

/-- For the refinement obtained from the true prime factorization, formal
balance characterizes perfection on positive inputs. -/
theorem canonical_balance_iff_perfect {N : ℕ} (hn : 0 < N) :
    listFormalSigma (quasiFactors N) = 2 * listValue (quasiFactors N) ↔ N.Perfect := by
  obtain ⟨hv, hs⟩ := quasiFactors_preserve hn.ne'
  rw [hv, hs, sigma_one_apply, Nat.perfect_iff_sum_divisors_eq_two_mul hn]

/-- Numbers represented by an odd formal factorization with prime lengths,
prime-power bases, and a single linear term whose base is a genuine Euler prime. -/
@[expose] def normalizedSpoofCandidates : Set ℕ := {N | Odd N ∧
  ∃ X : List (ℕ × ℕ), listValue X = N ∧ listFormalSigma X = 2*N ∧
    (∀ z ∈ X, ∃ p ∈ N.primeFactors, ∃ d : ℕ, 0 < d ∧ z.1 = p^d ∧ (z.2+1).Prime) ∧
    ∃ q ∈ N.primeFactors, q.Prime ∧ q % 4 = 1 ∧ X.filter (fun z => z.2 == 1) = [(q,1)]}

theorem oddPerfectNumbers_subset_normalizedSpoofCandidates :
    oddPerfectNumbers ⊆ normalizedSpoofCandidates :=
  fun _ hn => ⟨hn.1, odd_perfect_has_normalized_spoof hn.1 hn.2⟩

theorem descartes_canonical_formal_sigma :
    listFormalSigma (quasiFactors 198585576189) = 426027470778 :=
  (quasiFactors_preserve (by decide)).2.trans descartes_true_sigma

/-- Both refinements represent the same component. Only the one starting
with length two puts a genuine prime at the linear entry. -/
theorem order_matters_for_linear_entry :
    refineComponent 5 [3,2] = [(5,2),(125,1)] ∧
    refineComponent 5 [2,3] = [(5,1),(25,2)] := by decide

end OddPerfect
