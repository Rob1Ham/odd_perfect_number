module

public import OddPerfect.HarmonicSmooth
public import OddPerfect.HarmonicTau5.Part063
public import OddPerfect.HarmonicTau7.Part008
public import OddPerfect.HarmonicTau11.Part001
public import OddPerfect.HarmonicTau13.Part001
public import OddPerfect.HarmonicTau17.Part001
public import OddPerfect.HarmonicTau19.Part001
public import OddPerfect.HarmonicTau23.Part001
public import OddPerfect.HarmonicTau29.Part001
public import OddPerfect.HarmonicTau31.Part001

public section

namespace OddPerfect
open HarmonicChain

/-- Cohen–Sorli (2010), Proposition 2. -/
theorem ten_pow_twenty_four_lt_of_harmonic_divisor_count_prime {n p : ℕ}
    (ho : Odd n) (hh : OreHarmonic n) (hp : p.Prime)
    (hlarge : 3 < p) (hd : p ∣ n.divisors.card) : 10^24 < n := by
  by_contra! hsize
  apply hlarge.not_ge (divisor_count_prime_le_three_of_covers ho hh hsize ?_ hp hd)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact no_max_tau_5 n
  · exact no_max_tau_7 n
  · exact no_max_tau_11 n
  · exact no_max_tau_13 n
  · exact no_max_tau_17 n
  · exact no_max_tau_19 n
  · exact no_max_tau_23 n
  · exact no_max_tau_29 n
  · exact no_max_tau_31 n

/-- In the residual bounded case, Garcia's odd divisor-count prime must be three. -/
theorem three_dvd_card_divisors_of_small_odd_harmonic {n : ℕ} (ho : Odd n)
    (hh : OreHarmonic n) (hsize : n ≤ 10^24) : 3 ∣ n.divisors.card := by
  obtain ⟨r, hr, hodd, hd⟩ := odd_prime_dvd_card_divisors_of_odd_harmonic ho hh
  have hrle : r ≤ 3 := by
    by_contra! h
    exact hsize.not_gt (ten_pow_twenty_four_lt_of_harmonic_divisor_count_prime ho hh hr h hd)
  have h := Nat.odd_iff.mp hodd
  have := hr.two_le
  rwa [show r = 3 by omega] at hd

end OddPerfect
