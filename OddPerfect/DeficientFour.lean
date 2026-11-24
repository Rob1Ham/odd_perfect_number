module

public import OddPerfect.DeficientEuler
public import OddPerfect.ChainAbundancy
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect
open ArithmeticFunction Finset

/-- If every prime factor of n is at least b, the complementary divisor
n/d is at least b. This supplies the lower abundancy used by Yang–Togbé. -/
theorem DeficientPerfectWith.abundancy_lower {n d b : ℕ} (h : DeficientPerfectWith n d)
    (hb : 0<b) (hall : ∀ p ∈ n.primeFactors, b≤p) :
    ((2*(b:ℚ)-1)/b) ≤ (sigma 1 n:ℚ)/n := by
  obtain ⟨⟨t,ht⟩,hlt⟩ := Nat.mem_properDivisors.mp h.1
  have hd := Nat.pos_of_mem_properDivisors h.1
  have hn := hd.trans hlt
  have htwo : 1<t := by
    by_contra! he
    exact hlt.not_ge (ht ▸ (Nat.mul_le_mul_left d he).trans_eq (Nat.mul_one _))
  obtain ⟨r,hr,hrt⟩ := Nat.exists_prime_and_dvd htwo.ne'
  have hrn : r∣n := ht ▸ hrt.trans (dvd_mul_left t d)
  have hbt := (hall r (Nat.mem_primeFactors.mpr ⟨hr,hrn,hn.ne'⟩)).trans
    (Nat.le_of_dvd (zero_lt_one.trans htwo) hrt)
  have hbd : b*d≤n := by simpa only [ht,Nat.mul_comm d t] using Nat.mul_le_mul_right d hbt
  have hsum : (sigma 1 n:ℚ)+d=2*n := by exact_mod_cast h.2
  have hbdr : (b:ℚ)*d ≤ n := by exact_mod_cast hbd
  rw [div_le_div_iff₀ (by exact_mod_cast hb) (by exact_mod_cast hn)]
  nlinarith [congrArg (· * (b:ℚ)) hsum]

/-- The first-prime reduction in Yang–Togbé for at most four prime factors. -/
theorem three_dvd_of_deficientPerfect_four {n d : ℕ} (h : DeficientPerfectWith n d)
    (ho : Odd n) (hc : n.primeFactors.card≤4) : 3∣n := by
  by_contra h3
  have hall (p) (hp : p ∈ n.primeFactors) : 5≤p := by
    have hd := Nat.dvd_of_mem_primeFactors hp
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    have hop := Nat.odd_iff.mp (ho.of_dvd_nat hd)
    have hp3 : p≠3 := fun e => h3 (e ▸ hd)
    omega
  have lo := h.abundancy_lower (by decide : 0<5) hall
  have hbounds := prod_primeAbundancyLimit_le_interval (by decide : 1<13) n.primeFactors
    (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp,hall p hp⟩)
    (hc.trans (by decide : 4≤((Icc 5 13).filter Nat.Prime).card))
  have npos := Nat.pos_of_mem_properDivisors h.1
  have gt : 1<n := by have := (Nat.mem_properDivisors.mp h.1).2; omega
  have limit := (FactorBudget.abundancy_lt_prod_limits gt).trans_le hbounds
  exact ((lo.trans_lt limit).not_ge (by decide +kernel))

/-- Besides 3 there must be a prime divisor at most 23. Removing 3
leaves at most three bases. If all exceed 23, their three limiting
factors, together with 3/2, give abundancy below 5/3. -/
theorem second_prime_le_twenty_three_of_deficientPerfect_four {n d : ℕ}
    (h : DeficientPerfectWith n d) (ho : Odd n) (hc : n.primeFactors.card≤4) :
    ∃ p ∈ n.primeFactors, 3<p ∧ p≤23 := by
  have h3 := Nat.mem_primeFactors.mpr ⟨(by decide : Nat.Prime 3),three_dvd_of_deficientPerfect_four h ho hc,ho.pos.ne'⟩
  have hall (p) (hp : p∈n.primeFactors) : 3≤p := by
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    have hop := Nat.odd_iff.mp (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
    omega
  have lo := h.abundancy_lower (by decide : 0<3) hall
  by_contra! hnone
  let S := n.primeFactors.erase 3
  have far (p) (hp : p∈S) : 24≤p := by
    have hmem := (mem_erase.mp hp).2
    have hne := (mem_erase.mp hp).1
    exact hnone p hmem (lt_of_le_of_ne (hall p hmem) (Ne.symm hne))
  have hsize : S.card≤3 := by have := card_erase_add_one h3; dsimp [S]; omega
  have hr := prod_primeAbundancyLimit_le_interval (by decide : 1<37) S
    (fun p hp => ⟨Nat.prime_of_mem_primeFactors (mem_of_mem_erase hp),far p hp⟩)
    (hsize.trans (by decide : 3≤((Icc 24 37).filter Nat.Prime).card))
  have hi := mul_le_mul_of_nonneg_left hr (by decide +kernel : 0≤primeAbundancyLimit 3)
  rw [show primeAbundancyLimit 3*S.prod primeAbundancyLimit = n.primeFactors.prod primeAbundancyLimit
    from mul_prod_erase _ _ h3] at hi
  have hn : 1<n := by have := Nat.pos_of_mem_properDivisors h.1; have := (Nat.mem_properDivisors.mp h.1).2; omega
  exact ((lo.trans_lt ((FactorBudget.abundancy_lt_prod_limits hn).trans_le hi)).not_ge (by decide +kernel))

end OddPerfect
