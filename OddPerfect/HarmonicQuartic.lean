module

public import OddPerfect.HarmonicCount4.Part26
public import OddPerfect.HarmonicCubic

public section

namespace OddPerfect

/-- Cohen and Sorli (2010), Theorem 4. -/
theorem harmonic_divisor_count_fourth {n : ℕ} (ho : Odd n) (hh : OreHarmonic n) :
    n.divisors.card^4 ≤ n := HarmonicSearch.divisor_bound_of_closed HarmonicSearch.harmonic4_504 ho hh

/-- Cohen and Sorli (2010), Theorem 5. The integer-power form applies
to every divided prime power, including a smaller exponent than the exact one. -/
theorem harmonic_prime_power_eighth_lt_fifth {n p a : ℕ} (ho : Odd n) (hh : OreHarmonic n)
    (hp : p.Prime) (ha : 0<a) (hd : p^a∣n) : (p^a)^8 < n^5 :=
  harmonic_prime_power_of_divisor_bound hh hp ha hd (by decide : 0<4)
    (harmonic_divisor_count_fourth ho hh)

end OddPerfect
