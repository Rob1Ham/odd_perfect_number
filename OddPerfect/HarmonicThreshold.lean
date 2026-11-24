module

public import OddPerfect.HarmonicQuartic
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect
open ArithmeticFunction Finset

/-- Cohen–Sorli Proposition 1, in integral form. The endpoint is
included because the component-to-size inequality is strict. -/
theorem ten_pow_twenty_four_lt_of_harmonic_component {n p a : ℕ}
    (ho : Odd n) (hh : OreHarmonic n) (hp : p.Prime) (ha : 0<a)
    (hd : p^a∣n) (hbig : 10^15≤p^a) : 10^24<n := by
  have h := harmonic_prime_power_eighth_lt_fifth ho hh hp ha hd
  by_contra! le
  have num : ((10:ℕ)^24)^5=(10^15)^8 := by norm_num
  exact h.not_ge ((Nat.pow_le_pow_left le 5).trans (num ▸ Nat.pow_le_pow_left hbig 8))

/-- The large-prime branch in Cohen–Sorli Proposition 2. A prime r
dividing the divisor count divides one of the component lengths. -/
theorem ten_pow_twenty_four_lt_of_large_harmonic_divisor_count_prime {n r : ℕ}
    (ho : Odd n) (hh : OreHarmonic n) (hr : r.Prime) (hlarge : 37≤r)
    (hd : r∣n.divisors.card) : 10^24<n := by
  rw [Nat.card_divisors ho.pos.ne'] at hd
  obtain ⟨p,hp,hdiv⟩ := (hr.prime.dvd_finsetProd_iff _).mp hd
  have he := Nat.le_of_dvd (Nat.succ_pos (n.factorization p)) hdiv
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hpo := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
  have h3 : 3≤p := by have := hpr.two_le; have := Nat.odd_iff.mp hpo; omega
  have h36 : 36≤n.factorization p := by omega
  apply ten_pow_twenty_four_lt_of_harmonic_component ho hh hpr (a:=36) (by decide)
    ((hpr.pow_dvd_iff_le_factorization ho.pos.ne').mpr h36)
  exact (by decide +kernel : (10:ℕ)^15≤3^36).trans (Nat.pow_le_pow_left h3 36)

end OddPerfect
