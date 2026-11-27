module

public import OddPerfect.HarmonicRoots
import Mathlib.Data.Finset.Max

public section

namespace OddPerfect.HarmonicChain
open Finset

/-- To exclude large divisor-count primes it suffices to rule out each
possible largest prime below 37. The component bound handles the tail. -/
theorem divisor_count_prime_le_three_of_covers {n : ℕ} (ho : Odd n) (hh : OreHarmonic n)
    (hsize : n ≤ 10^24)
    (covers : ∀ r ∈ ([5,7,11,13,17,19,23,29,31] : List ℕ),
      Small n r → ¬ r ∣ n.divisors.card)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ n.divisors.card) : p ≤ 3 := by
  let s := n.divisors.card.primeFactors
  have hτ : n.divisors.card ≠ 0 := (card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr ho.pos.ne'⟩).ne'
  have hmem : p ∈ s := Nat.mem_primeFactors.mpr ⟨hp, hd, hτ⟩
  let r := s.max' ⟨p, hmem⟩
  have hrmem : r ∈ s := s.max'_mem _
  have hr := Nat.prime_of_mem_primeFactors hrmem
  have hdr := Nat.dvd_of_mem_primeFactors hrmem
  have hmax : Small n r := ⟨ho, hh, hsize, fun q hq hqd =>
    s.le_max' q (Nat.mem_primeFactors.mpr ⟨hq, hqd, hτ⟩)⟩
  have hupper : r < 37 := by
    by_contra! h
    exact hsize.not_gt (ten_pow_twenty_four_lt_of_large_harmonic_divisor_count_prime ho hh hr h hdr)
  by_contra! h
  have hpr : p ≤ r := s.le_max' p hmem
  have check : ∀ j : Fin 37, j.val.Prime → 3 < j.val →
      j.val ∈ ([5,7,11,13,17,19,23,29,31] : List ℕ) := by decide +kernel
  exact covers r (check ⟨r, hupper⟩ hr (h.trans_le hpr)) hmax hdr

end OddPerfect.HarmonicChain
