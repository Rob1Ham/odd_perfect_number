module

public import OddPerfect.HarmonicCount3.Part01
public import OddPerfect.HarmonicSize

public section

namespace OddPerfect

/-- Cohen and Sorli (2010), Lemma 1, for the full odd harmonic class. -/
theorem harmonic_divisor_count_cubed {n : ℕ} (ho : Odd n) (hh : OreHarmonic n) :
    n.divisors.card^3 ≤ n := HarmonicSearch.divisor_bound_of_closed HarmonicSearch.harmonic3_17 ho hh

/-- Cohen and Sorli (2010), Lemma 2, with denominators in the exponent
cleared: for each positive prime power P dividing n, P³<n². -/
theorem harmonic_prime_power_cubed_lt_square {n p a : ℕ} (ho : Odd n) (hh : OreHarmonic n)
    (hp : p.Prime) (ha : 0<a) (hd : p^a∣n) : (p^a)^3 < n^2 := by
  have h := harmonic_prime_power_of_divisor_bound hh hp ha hd (by decide : 0<3)
    (harmonic_divisor_count_cubed ho hh)
  by_contra! le
  exact h.not_ge (by simpa only [←pow_mul,Nat.mul_assoc] using Nat.pow_le_pow_left le 2)

end OddPerfect
