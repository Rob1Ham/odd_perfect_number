module

public import OddPerfect.SixthLeast3.Part008
public import OddPerfect.SixthLeast5.Part006
public import OddPerfect.SixthLeast7.Part001
public import OddPerfect.SixthLeast11.Part001
public import OddPerfect.SixthLeast13.Part001
public import OddPerfect.SixthLeast17.Part001
public import OddPerfect.SixthLeast19.Part001
public import OddPerfect.SixthLeast23.Part001
public import OddPerfect.SixthLeast29.Part001
public import OddPerfect.SixthLeast31.Part001
public import OddPerfect.SixthLeast37.Part001
public import OddPerfect.SixthLeast41.Part001
public import OddPerfect.SixthLeast43.Part001
public import OddPerfect.SixthLeast47.Part001

public section

namespace OddPerfect
open SixthPowerChain

/-- The least-prime branches through 47 all close for a sixth-power-free
odd perfect number. In particular this includes the 3 and 5 exclusions
proved by Fletcher, Nielsen and Ochem. -/
theorem prime_sixth_power_dvd_of_small_factor {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : 2 ≤ q) (hd : q ∣ N) (hsmall : q < 53) : ∃ p : ℕ, p.Prime ∧ p^6 ∣ N := by
  by_contra! hf
  have hn : N ≠ 1 := by
    rintro rfl
    have := Nat.le_of_dvd (by decide : 0 < 1) hd
    omega
  have H : Hyp N N.minFac := ⟨ho,hN,le_rfl,hf⟩
  have hdN := Nat.minFac_dvd N
  have hp := Nat.minFac_prime hn
  have oddp := Nat.odd_iff.mp (ho.of_dvd_nat hdN)
  have le := (Nat.minFac_le_of_dvd hq hd).trans_lt hsmall
  have cert : ∀ j : Fin 53, j.val.Prime → j.val%2=1 →
      j.val ∈ ([3,5,7,11,13,17,19,23,29,31,37,41,43,47] : List ℕ) := by decide +kernel
  have mem := cert ⟨N.minFac,le⟩ hp oddp
  change N.minFac ∈ _ at mem
  generalize N.minFac = p at mem H hdN
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact no_sixth_free_min_3 H hdN
  · exact no_sixth_free_min_5 H hdN
  · exact no_sixth_free_min_7 H hdN
  · exact no_sixth_free_min_11 H hdN
  · exact no_sixth_free_min_13 H hdN
  · exact no_sixth_free_min_17 H hdN
  · exact no_sixth_free_min_19 H hdN
  · exact no_sixth_free_min_23 H hdN
  · exact no_sixth_free_min_29 H hdN
  · exact no_sixth_free_min_31 H hdN
  · exact no_sixth_free_min_37 H hdN
  · exact no_sixth_free_min_41 H hdN
  · exact no_sixth_free_min_43 H hdN
  · exact no_sixth_free_min_47 H hdN

/-- Fletcher–Nielsen–Ochem's sixth-power-free exclusion of the prime 5. -/
theorem sixth_power_free_five_not_dvd {N : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hf : ∀ p : ℕ, p.Prime → ¬ p^6 ∣ N) : ¬ 5 ∣ N := by
  intro hd
  obtain ⟨p,hp,hpow⟩ := prime_sixth_power_dvd_of_small_factor ho hN (by decide : 2≤5) hd (by decide)
  exact hf p hp hpow

end OddPerfect
