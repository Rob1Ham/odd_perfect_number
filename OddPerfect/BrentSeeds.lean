module

public import OddPerfect.SizeSeeds

public section

namespace OddPerfect

open Finset ArithmeticFunction

private theorem brent_floor {N : ℕ} (ho : Odd N) (hav : Nat.Coprime 1123167045 N) :
    ∀ p ∈ N.primeFactors, 17 ≤ p := by
  have hav' := hav.coprime_dvd_left (by decide +kernel : 15015 ∣ 1123167045)
  have hf : FactorBudget.root.residualFloor 15015 = 17 := by decide +kernel
  simpa only [hf] using FactorBudget.residualFloor_le (FactorBudget.root_realizes N) ho hav'

/-- The odd primes possibly occurring below the cut after the eight exclusions. -/
private def brentSample : Finset ℕ :=
  ⟨([17, 23, 29, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 131, 137,
    139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197,
    199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269,
    271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347,
    349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419,
    421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487,
    491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571,
    577, 587, 593, 599] : List ℕ), by decide +kernel⟩

/-- The first 100 primes at least 17, used to minimize the size product. -/
private def plainSample : Finset ℕ :=
  ⟨([17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
    67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
    127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
    191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
    257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
    331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397,
    401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
    467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
    563, 569, 571, 577] : List ℕ), by decide +kernel⟩

private def covers (bound : ℕ) (omitted : List ℕ) (t : Finset ℕ) : Bool :=
  (List.range (bound+1)).all fun p => decide (p < 17) || omitted.contains p ||
    [2,3,5,7,11,13,17,19,23].any (fun q => decide (1 < q ∧ q < p ∧ p%q = 0)) || decide (p ∈ t)

private theorem mem_of_covers {b p : ℕ} {omitted : List ℕ} {t : Finset ℕ}
    (h : covers b omitted t = true) (hp : p.Prime) (hlo : 17 ≤ p) (hhi : p ≤ b)
    (hnot : p ∉ omitted) : p ∈ t := by
  have hh := List.all_eq_true.mp h p (List.mem_range.mpr (by omega))
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem, List.any_eq_true] at hh
  rcases hh with ((hs | ho) | ⟨q, _, hq, hqp, hm⟩) | ht
  · omega
  · exact (hnot ho).elim
  · rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero hm) with h | h <;> omega
  · exact ht

private theorem brent_cover : covers 599 [19,31,127] brentSample = true := by decide +kernel

private theorem brent_interval : brentSample.card = 100 ∧
    (∏ p ∈ brentSample, p) ≤ 2*∏ p ∈ brentSample, (p-1) := by decide +kernel

private theorem brent_range : ∀ p ∈ brentSample, 1 < p ∧ p ≤ 599 := by decide +kernel

private theorem plain_cover : covers 577 [] plainSample = true := by decide +kernel

private theorem plain_range : ∀ p ∈ plainSample, 17 ≤ p ∧ p ≤ 577 ∧ p.Prime := by decide +kernel

private theorem plain_eq : (Icc 17 577).filter Nat.Prime = plainSample := by
  ext p
  constructor
  · intro hp
    obtain ⟨hi, hprime⟩ := mem_filter.mp hp
    exact mem_of_covers plain_cover hprime (mem_Icc.mp hi).1 (mem_Icc.mp hi).2 (by simp)
  · intro hp
    obtain ⟨hl, hu, hprime⟩ := plain_range p hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hl, hu⟩, hprime⟩

private theorem plain_size : plainSample.card = 100 ∧
    10^536 < (∏ p ∈ plainSample, p)^2 * 17^(259-2*plainSample.card) := by decide +kernel

/-- Brent and Cohen's eight forbidden seeds are 127, 19, 7, 11, 31, 13, 3 and 5.
The first 100 permitted limiting abundancies have product below two. -/
theorem brent_seed_free_counts {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hav : Nat.Coprime 1123167045 N) :
    101 ≤ N.primeFactors.card ∧ 259 ≤ N.primeFactorsList.length := by
  let t := brentSample
  have hfloor := brent_floor ho hav
  obtain ⟨h100, hprod⟩ := brent_interval
  change t.card = 100 at h100
  change (∏ p ∈ t, p) ≤ 2 * ∏ p ∈ t, (p-1) at hprod
  have hnum : (∏ p ∈ t, primeAbundancyLimit p) ≤ 2 := by
    simp only [primeAbundancyLimit, prod_div_distrib, ← Nat.cast_prod]
    have hden : 0 < ∏ p ∈ t, (p-1) := prod_pos fun p hp =>
      Nat.sub_pos_of_lt (brent_range p hp).1
    rw [div_le_iff₀ (by exact_mod_cast hden)]
    simpa only [Nat.cast_prod, Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_le (α := ℚ)).mpr hprod
  have hw : 101 ≤ N.primeFactors.card := by
    by_contra! hsmall
    have bound := prod_primeAbundancyLimit_le_of_cut (by decide : 1<599) N.primeFactors t
      (by omega) (by
        intro p hp
        obtain ⟨hps,hpt⟩ := mem_sdiff.mp hp
        obtain ⟨hprime,hd,_⟩ := Nat.mem_primeFactors.mp hps
        by_contra! hlt
        have havoid (r : ℕ) (hr : r ∣ 1123167045) : p ≠ r := by
          rintro rfl
          exact hprime.not_dvd_one (hav.gcd_eq_one ▸ Nat.dvd_gcd hr hd)
        apply hpt (mem_of_covers brent_cover hprime (hfloor p hps) hlt.le ?_)
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        exact fun h => h.elim (havoid 19 (by decide +kernel)) (fun h =>
          h.elim (havoid 31 (by decide +kernel)) (havoid 127 (by decide +kernel))))
      (fun p hp => brent_range p (mem_sdiff.mp hp).1)
    exact (two_lt_prod_primeAbundancyLimit hN).not_ge (bound.trans hnum)
  have h3 : ¬ 3 ∣ N := fun hd => (by decide : Nat.Prime 3).not_dvd_one
    (hav.gcd_eq_one ▸ Nat.dvd_gcd (by decide +kernel : 3 ∣ 1123167045) hd)
  have hc := (ochem_rao_count_cases ho hN).2 h3
  have hpar := Nat.odd_iff.mp (odd_total_prime_factor_count ho hN)
  exact ⟨hw, by omega⟩

/-- The 3-free count bound improves the eight-seed complement beyond 10^536. -/
theorem brent_seed_free_size {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hav : Nat.Coprime 1123167045 N) :
    10^536 < N := by
  obtain ⟨hw, ht⟩ := brent_seed_free_counts ho hN hav
  have hcard : ((Icc 17 577).filter Nat.Prime).card < N.primeFactors.card := by
    rw [plain_eq, plain_size.1]
    omega
  have hs := size_of_prime_interval_counts (b := 577) ho hN (by decide : 0<17)
    (brent_floor ho hav) ht hcard
  dsimp only at hs
  rw [plain_eq] at hs
  exact plain_size.2.trans_le hs

end OddPerfect
