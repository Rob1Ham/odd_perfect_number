module

public import OddPerfect.OchemNormalized
public import OddPerfect.Transfer
import OddPerfect.SteuerwaldFree
import Mathlib.Algebra.Order.Ring.Abs

/-! Count the prime factors, with multiplicity, supplied by the normalized
square-component sums in Ochem and Rao (2014), §3, inequality (8). -/

public section

namespace OddPerfect

open ArithmeticFunction

theorem ochem_rao_incidence {N p : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) (_hp4 : p % 4 = 1) (he : N.factorization p % 4 = 1)
    (hev : ∀ q : ℕ, q ≠ p → Even (N.factorization q)) :
    2 * (squareSources N).card ≤ 1 + N.factorization p +
      3 * (squareSourcesOne N).card + (largeSources N p).card +
      ∑ q ∈ largeSources N p, N.factorization q := by
  let T := insert p (squareSourcesOne N ∪ largeSources N p)
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
  have hdis : Disjoint (squareSourcesOne N) (largeSources N p) := by
    apply Finset.disjoint_left.mpr
    intro r hr hl
    have := (source (Finset.mem_filter.mp hr).1).2.2
    have := (Finset.mem_filter.mp hl).2.2.2
    omega
  have hnot : p ∉ squareSourcesOne N ∪ largeSources N p := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · have := (source (Finset.mem_filter.mp h).1).2.2
      omega
    · exact (Finset.mem_filter.mp h).2.2.1 rfl
  have htcard : T.card = (squareSourcesOne N).card + (largeSources N p).card + 1 := by
    dsimp only [T]
    rw [Finset.card_insert_of_notMem hnot, Finset.card_union_of_disjoint hdis]
  have hsum : ∑ r ∈ squareSourcesOne N, N.factorization r = (squareSourcesOne N).card * 2 := by
    calc
      _ = ∑ _r ∈ squareSourcesOne N, (2 : ℕ) := Finset.sum_congr rfl fun _ hr =>
        (source (Finset.mem_filter.mp hr).1).2.2
      _ = _ := by simp
  dsimp only [T] at upper
  rw [Finset.sum_insert hnot, Finset.sum_union hdis, hsum] at upper
  have lower := squareSources_count_le_normalized_count ho
  change 2 * S.card ≤ (∑ u ∈ S, cardFactors (normalizedSquareSum u)) + A.card at lower
  change 2 * S.card ≤ _
  omega

end OddPerfect
