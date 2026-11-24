module

public import OddPerfect.DeficientFour
public import OddPerfect.SupportSieve
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect
open ArithmeticFunction Finset

/-- A proper deficient divisor gives an odd perfect number whenever
its complementary divisor gives a prime multiplier coprime to n. -/
theorem DeficientPerfectWith.perfect_of_prime_multiplier {n d p : ℕ}
    (h : DeficientPerfectWith n d) (ho : Odd n) (hp : p.Prime)
    (eqn : p+1=2*(n/d)) (cop : ¬p∣n) : (n*p).Perfect := by
  obtain ⟨x,_,hx,pair,he⟩ := h.tothPair ho
  have : x=p := by omega
  subst x
  exact (toth_coprime_perfect_iff_prime pair hx (hp.coprime_iff_not_dvd.mpr cop).symm).mpr hp

/-- Yang–Togbé §5.4. If an odd deficient-perfect number has at most
four distinct prime factors, some prime besides 3 is at most 17.
Turning the cofactor into an odd perfect number supplies the large
prime used to exclude the final two cases. -/
theorem second_prime_le_seventeen_of_deficientPerfect_four {n d : ℕ}
    (h : DeficientPerfectWith n d) (ho : Odd n) (hc : n.primeFactors.card≤4) :
    ∃ p ∈ n.primeFactors, 3<p ∧ p≤17 := by
  by_contra! hnone
  have h3 := Nat.mem_primeFactors.mpr ⟨(by decide : Nat.Prime 3),
    three_dvd_of_deficientPerfect_four h ho hc,ho.pos.ne'⟩
  let s := n.primeFactors.erase 3
  have far (p) (hp : p∈s) : 19≤p := by
    obtain ⟨hne,hm⟩ := mem_erase.mp hp
    have oddp := Nat.odd_iff.mp (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hm))
    have low := (Nat.prime_of_mem_primeFactors hm).two_le
    have := hnone p hm (by omega)
    omega
  have sc : s.card≤3 := by have := card_erase_add_one h3; dsimp [s]; omega
  have z3 : 0≤primeAbundancyLimit 3 := by decide +kernel
  have hn : 1<n := by
    have := Nat.pos_of_mem_properDivisors h.1
    have := (Nat.mem_properDivisors.mp h.1).2
    omega
  have upper : (sigma 1 n:ℚ)/n < primeAbundancyLimit 3 * s.prod primeAbundancyLimit := by
    rw [show primeAbundancyLimit 3*s.prod primeAbundancyLimit = n.primeFactors.prod primeAbundancyLimit
      from mul_prod_erase _ _ h3]
    exact FactorBudget.abundancy_lt_prod_limits hn
  have hs := prod_primeAbundancyLimit_le_interval (by decide : 1<29) s
    (fun p hp => ⟨Nat.prime_of_mem_primeFactors (mem_of_mem_erase hp),far p hp⟩)
    (sc.trans (by decide : 3≤((Icc 19 29).filter Nat.Prime).card))
  have u9 : (sigma 1 n:ℚ)/n < 9/5 :=
    (upper.trans_le (mul_le_mul_of_nonneg_left hs z3)).trans (by decide +kernel)
  obtain ⟨⟨t,ht⟩,hlt⟩ := Nat.mem_properDivisors.mp h.1
  have hd := Nat.pos_of_mem_properDivisors h.1
  have ot := Nat.odd_iff.mp (ho.of_dvd_nat (ht ▸ dvd_mul_left t d : t∣n))
  have gt : 1<t := by
    by_contra! he
    exact hlt.not_ge (ht ▸ (Nat.mul_le_mul_left d he).trans_eq (Nat.mul_one _))
  have bound := (div_lt_div_iff₀ (by exact_mod_cast ho.pos : (0:ℚ)<n) (by decide : (0:ℚ)<5)).mp u9
  have num : sigma 1 n * 5 < 9*n := by exact_mod_cast bound
  have sig := h.2
  have t3 : t=3 := by
    by_contra he
    have hi : 5≤t := by omega
    have : 5*d≤n := ht ▸ (Nat.mul_le_mul_right d hi).trans_eq (Nat.mul_comm t d)
    omega
  subst t
  have comp : n/d=3 := by rw [ht,Nat.mul_div_cancel_left _ hd]
  have n5 : ¬5∣n := fun hp => (by decide : ¬19≤5) (far 5 (mem_erase.mpr
    ⟨by decide,Nat.mem_primeFactors.mpr ⟨by decide,hp,ho.pos.ne'⟩⟩))
  have perf := h.perfect_of_prime_multiplier ho (by decide : Nat.Prime 5) (by rw [comp]) n5
  obtain ⟨R,hR,hbig⟩ := SupportSieve.exists_prime_gt_257 perf (ho.mul (by decide : Odd 5))
  have hpr := Nat.prime_of_mem_primeFactors hR
  have hdR : R∣n := (hpr.dvd_mul.mp (Nat.dvd_of_mem_primeFactors hR)).resolve_right
    (fun h5 => (by omega : ¬ R≤5) (Nat.le_of_dvd (by decide) h5))
  have hmR : R∈s := mem_erase.mpr ⟨by omega,Nat.mem_primeFactors.mpr ⟨hpr,hdR,ho.pos.ne'⟩⟩
  have rc : (s.erase R).card≤2 := by have := card_erase_add_one hmR; omega
  have rest := prod_primeAbundancyLimit_le_interval (by decide : 1<23) (s.erase R)
    (fun p hp => ⟨Nat.prime_of_mem_primeFactors (mem_of_mem_erase (mem_of_mem_erase hp)),
      far p (mem_of_mem_erase hp)⟩) (rc.trans (by decide : 2≤((Icc 19 23).filter Nat.Prime).card))
  have non (p : ℕ) : 0≤primeAbundancyLimit p :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have upperR := mul_le_mul (primeAbundancyLimit_antitone (by decide : 1<257) hbig.le) rest
    (prod_nonneg fun p _ => non p) (non 257)
  rw [mul_prod_erase _ _ hmR] at upperR
  have contradiction : (sigma 1 n:ℚ)/n < 5/3 :=
    (upper.trans_le (mul_le_mul_of_nonneg_left upperR z3)).trans (by decide +kernel)
  have bound := (div_lt_div_iff₀ (by exact_mod_cast ho.pos : (0:ℚ)<n) (by decide : (0:ℚ)<3)).mp contradiction
  have finish : sigma 1 n * 3 < 5*n := by exact_mod_cast bound
  omega

end OddPerfect
