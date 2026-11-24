module

public import OddPerfect.DeficientLargeSecond
public import OddPerfect.DeficientThirdSource

public section

namespace OddPerfect
open ArithmeticFunction Finset

private theorem complement_lt_of_abundancy {n d t b : ℕ} (h : DeficientPerfectWith n d)
    (ht : n=d*t) (hb : 0<b) (hu : (sigma 1 n:ℚ)/n < (2*(b:ℚ)-1)/b) : t<b := by
  have hd := Nat.pos_of_mem_properDivisors h.1
  have hn := hd.trans (Nat.mem_properDivisors.mp h.1).2
  have bound := (div_lt_div_iff₀ (by exact_mod_cast hn) (by exact_mod_cast hb)).mp hu
  have eqn : (sigma 1 n:ℚ)+d=2*n := by exact_mod_cast h.2
  by_contra! high
  have hbd : (d:ℚ)*b≤n := by exact_mod_cast (ht ▸ Nat.mul_le_mul_left d high : d*b≤n)
  nlinarith [congrArg (·*(b:ℚ)) eqn]

/-- In the four-prime branches with no prime factor 5 or 7, the omitted
divisor is n/3. The apparent endpoint n/d=9 would force a divisor-sum
source congruent to one modulo 17, despite every prime factor being ≤17. -/
theorem deficient_complement_eq_three_of_large_second {n d : ℕ}
    (h : DeficientPerfectWith n d) (ho : Odd n) (hc : n.primeFactors.card≤4)
    (floor : ∀ p ∈ n.primeFactors, p≠3 → 11≤p) : n/d=3 := by
  have h3 := Nat.mem_primeFactors.mpr ⟨(by decide : Nat.Prime 3),
    three_dvd_of_deficientPerfect_four h ho hc,ho.pos.ne'⟩
  let s := n.primeFactors.erase 3
  have far (p) (hp : p∈s) : 11≤p := floor p (mem_erase.mp hp).2 (mem_erase.mp hp).1
  have sc : s.card≤3 := by have := card_erase_add_one h3; dsimp [s]; omega
  have non (p : ℕ) : 0≤primeAbundancyLimit p := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hn : 1<n := by have := Nat.pos_of_mem_properDivisors h.1; have := (Nat.mem_properDivisors.mp h.1).2; omega
  have upper : (sigma 1 n:ℚ)/n < primeAbundancyLimit 3 * s.prod primeAbundancyLimit := by
    rw [show primeAbundancyLimit 3*s.prod primeAbundancyLimit = n.primeFactors.prod primeAbundancyLimit
      from mul_prod_erase _ _ h3]
    exact FactorBudget.abundancy_lt_prod_limits hn
  obtain ⟨⟨t,ht⟩,hlt⟩ := Nat.mem_properDivisors.mp h.1
  have hd := Nat.pos_of_mem_properDivisors h.1
  have hdiv : t∣n := ht ▸ dvd_mul_left t d
  have hodd := Nat.odd_iff.mp (ho.of_dvd_nat hdiv)
  have gt : 1<t := by
    by_contra! he
    exact hlt.not_ge (ht ▸ (Nat.mul_le_mul_left d he).trans_eq (Nat.mul_one _))
  have hs := prod_primeAbundancyLimit_le_interval (by decide : 1<17) s
    (fun p hp => ⟨Nat.prime_of_mem_primeFactors (mem_of_mem_erase hp),far p hp⟩)
    (sc.trans (by decide : 3≤((Icc 11 17).filter Nat.Prime).card))
  have small : t<11 := complement_lt_of_abundancy h ht (by decide)
    ((upper.trans_le (mul_le_mul_of_nonneg_left hs (non 3))).trans (by decide +kernel))
  have ne5 : t≠5 := fun he => (by decide : ¬11≤5) (floor 5
    (Nat.mem_primeFactors.mpr ⟨by decide,he ▸ hdiv,ho.pos.ne'⟩) (by decide))
  have ne7 : t≠7 := fun he => (by decide : ¬11≤7) (floor 7
    (Nat.mem_primeFactors.mpr ⟨by decide,he ▸ hdiv,ho.pos.ne'⟩) (by decide))
  have avoid : t≠9 := by
    intro eq9
    have h17 : 17∣sigma 1 n := by
      have sum := h.2
      have scale : 9*sigma 1 n=17*n := by rw [eq9] at ht; omega
      exact (by decide : Nat.Coprime 17 9).dvd_of_dvd_mul_left (scale ▸ dvd_mul_right 17 n)
    obtain ⟨x,hx,_,pair,_⟩ := h.tothPair ho
    have sq := (toth_odd_cofactor_square pair hx).1
    obtain ⟨R,hR,con,_⟩ := fermat_divisor_of_square_sigma_companion ho.pos.ne' sq
      (by decide : Nat.Prime 17) (by decide) (by decide : 17-1=2^4) h17
    have hpr := Nat.prime_of_mem_primeFactors hR
    have hbig : 19≤R := by
      have := hpr.two_le
      have oddR := Nat.odd_iff.mp (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hR))
      omega
    have hr : R∈s := mem_erase.mpr ⟨by omega,hR⟩
    have rc : (s.erase R).card≤2 := by have := card_erase_add_one hr; omega
    have rest := prod_primeAbundancyLimit_le_interval (by decide : 1<13) (s.erase R)
      (fun p hp => ⟨Nat.prime_of_mem_primeFactors (mem_of_mem_erase (mem_of_mem_erase hp)),
        far p (mem_of_mem_erase hp)⟩) (rc.trans (by decide : 2≤((Icc 11 13).filter Nat.Prime).card))
    have cap := mul_le_mul (primeAbundancyLimit_antitone (by decide : 1<19) hbig) rest
      (prod_nonneg fun p _ => non p) (non 19)
    rw [mul_prod_erase _ _ hr] at cap
    have low : t<9 := complement_lt_of_abundancy h ht (by decide)
      ((upper.trans_le (mul_le_mul_of_nonneg_left cap (non 3))).trans (by decide +kernel))
    omega
  rw [ht,Nat.mul_div_cancel_left _ hd]
  omega

end OddPerfect
