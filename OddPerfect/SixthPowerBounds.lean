module

public import OddPerfect.SixthPowerSieve
public import OddPerfect.SizeSeeds

public section

namespace OddPerfect
open ArithmeticFunction Finset

private abbrev primes53 : Finset ℕ := (Icc 53 3229).filter Nat.Prime

private def smallPrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53]

private def fastPrime53 (n : ℕ) : Bool :=
  smallPrimes.all fun q => decide (n ≤ q) || decide (n % q ≠ 0)

private theorem smallPrimes_ge_two : ∀ q ∈ smallPrimes, 2 ≤ q := by decide

private theorem smallPrimes_complete : ∀ m : Fin 59, m.val.Prime → m.val ∈ smallPrimes := by decide

private theorem fastPrime53_iff {n : ℕ} (hlo : 53 ≤ n) (hhi : n ≤ 3229) :
    fastPrime53 n = true ↔ n.Prime := by
  constructor
  · intro h
    by_contra hnp
    have hmp : n.minFac.Prime := Nat.minFac_prime (by omega)
    have hmd := Nat.minFac_dvd n
    have hmsq := Nat.minFac_sq_le_self (by omega) hnp
    have hmlt59 : n.minFac < 59 := by nlinarith
    have hmmem : n.minFac ∈ smallPrimes :=
      smallPrimes_complete ⟨n.minFac, hmlt59⟩ hmp
    have hmle : n.minFac < n := by
      have : n.minFac ≠ n := fun he => hnp (he ▸ hmp)
      have := Nat.le_of_dvd (by omega) hmd
      omega
    have hq := List.all_eq_true.mp h n.minFac hmmem
    simp only [Bool.or_eq_true, decide_eq_true_eq, ne_eq] at hq
    rcases hq with hle | hnz
    · omega
    · exact hnz (Nat.mod_eq_zero_of_dvd hmd)
  · intro hp
    rw [fastPrime53, List.all_eq_true]
    intro q hq
    simp only [Bool.or_eq_true, decide_eq_true_eq, ne_eq]
    by_cases hle : n ≤ q
    · exact Or.inl hle
    · right
      have hq2 := smallPrimes_ge_two q hq
      intro hmod
      have hd := Nat.dvd_of_mod_eq_zero hmod
      rcases (Nat.dvd_prime hp).mp hd with h1 | h2 <;> omega

private abbrev Stats := ℕ × ℕ × ℕ

private def primes53List : List ℕ :=
  (List.range' 53 (3230 - 53)).filter fastPrime53

private def listStats : Stats :=
  (primes53List.length, primes53List.prod, (primes53List.map (· - 1)).prod)

private def sufficientStats (s : Stats) : Prop :=
  s.1 = 442 ∧ s.2.1 ≤ 2*s.2.2 ∧ 10^3136 < s.2.1^2 * 53^(1137-2*s.1)

private instance (s : Stats) : Decidable (sufficientStats s) := by
  unfold sufficientStats
  infer_instance

private theorem primes53_bounds : primes53.card = 442 ∧
    (∏ p ∈ primes53, p) ≤ 2 * ∏ p ∈ primes53, (p-1) ∧
    10^3136 < (∏ p ∈ primes53, p)^2 * 53^(1137-2*primes53.card) := by
  have cert : sufficientStats listStats := by decide +kernel
  have hnodup : primes53List.Nodup := (List.nodup_range').filter _
  have hset : primes53List.toFinset = primes53 := by
    ext n
    simp only [List.mem_toFinset, primes53List, List.mem_filter, List.mem_range'_1, primes53,
      mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hf⟩
      have hle : n ≤ 3229 := by omega
      exact ⟨⟨h1, hle⟩, (fastPrime53_iff h1 hle).mp hf⟩
    · rintro ⟨⟨h1, h2⟩, hp⟩
      exact ⟨⟨h1, by omega⟩, (fastPrime53_iff h1 h2).mpr hp⟩
  have hcard : primes53.card = primes53List.length := by
    rw [← hset, List.toFinset_card_of_nodup hnodup]
  have hprod1 : (∏ p ∈ primes53, p) = primes53List.prod := by
    rw [← hset, List.prod_toFinset _ hnodup, List.map_id']
  have hprod2 : (∏ p ∈ primes53, (p - 1)) = (primes53List.map (· - 1)).prod := by
    rw [← hset, List.prod_toFinset (fun p => p - 1) hnodup]
  simpa only [sufficientStats, listStats, ← hcard, ← hprod1, ← hprod2] using cert

/-- Conditional bounds for the entire class with least prime at least 53.
Removing the Euler prime leaves 442 distinct square divisors contributing
to the size estimate. -/
theorem bounds_of_prime_factors_ge_fifty_three {N : ℕ} (ho : Odd N) (hN : N.Perfect)
    (floor : ∀ p ∈ N.primeFactors, 53≤p) :
    443 ≤ N.primeFactors.card ∧ 1137 ≤ N.primeFactorsList.length ∧ 10^3136 < N := by
  obtain ⟨hc,hm,hs⟩ := primes53_bounds
  have hden : 0 < ∏ p ∈ primes53, (p-1) := prod_pos fun p hp =>
    Nat.sub_pos_of_lt (mem_filter.mp hp).2.one_lt
  have hnum : (∏ p ∈ primes53, primeAbundancyLimit p) ≤ 2 := by
    simp only [primeAbundancyLimit, prod_div_distrib, ← Nat.cast_prod]
    rw [div_le_iff₀ (by exact_mod_cast hden)]
    simpa only [Nat.cast_prod, Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_le (α := ℚ)).mpr hm
  have many : primes53.card < N.primeFactors.card := by
    by_contra! hsmall
    have bound := prod_primeAbundancyLimit_le_interval (by decide : 1<3229) N.primeFactors
      (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp,floor p hp⟩) hsmall
    exact (two_lt_prod_primeAbundancyLimit hN).not_ge (bound.trans hnum)
  have h3 : ¬3∣N := fun hd => (by decide : ¬53≤3) (floor 3
    (Nat.mem_primeFactors.mpr ⟨by decide,hd,ho.pos.ne'⟩))
  have ratio := (ochem_rao_count_cases ho hN).2 h3
  have total : 1137 ≤ N.primeFactorsList.length := by omega
  have hsz := size_of_prime_interval_counts (a:=53) (b:=3229) (total:=1137) ho hN
    (by decide : 0<53) floor total many
  dsimp only at hsz
  have hpeq : (Icc 53 3229).filter Nat.Prime = primes53 := rfl
  rw [hpeq] at hsz
  exact ⟨by omega,total,Nat.lt_of_lt_of_le hs hsz⟩

/-- Fletcher–Nielsen–Ochem's sixth-power alternative with explicit
consequences for the complementary branch of the local sieve. -/
theorem sixth_power_or_large_support {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    (∃ p : ℕ, p.Prime ∧ p^6∣N) ∨
      (443 ≤ N.primeFactors.card ∧ 1137 ≤ N.primeFactorsList.length ∧ 10^3136 < N) := by
  by_cases branch : ∃ p : ℕ, p.Prime ∧ p^6∣N
  · exact Or.inl branch
  · right
    apply bounds_of_prime_factors_ge_fifty_three ho hN
    intro p hp
    by_contra! h
    exact branch (prime_sixth_power_dvd_of_small_factor ho hN (Nat.prime_of_mem_primeFactors hp).two_le
      (Nat.dvd_of_mem_primeFactors hp) h)

end OddPerfect
