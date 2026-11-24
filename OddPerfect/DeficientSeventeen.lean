module

public import OddPerfect.DeficientQuotient

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- The second distinct prime factor of an odd deficient-perfect number
with at most four distinct prime factors is at most thirteen. -/
theorem second_prime_le_thirteen_of_deficientPerfect_four {n d : ℕ}
    (h : DeficientPerfectWith n d) (ho : Odd n) (hc : n.primeFactors.card≤4) :
    ∃ p∈n.primeFactors, 3<p ∧ p≤13 := by
  by_contra! hnone
  have hn3 := Nat.mem_primeFactors.mpr ⟨(by decide : Nat.Prime 3),
    three_dvd_of_deficientPerfect_four h ho hc,ho.pos.ne'⟩
  have floor (p : ℕ) (hp : p∈n.primeFactors) (hne : p≠3) : 11≤p := by
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    have := Nat.odd_iff.mp (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
    have := hnone p hp (by omega)
    omega
  obtain ⟨p,hp,hp3,hp17⟩ := second_prime_le_seventeen_of_deficientPerfect_four h ho hc
  have hp13 := hnone p hp hp3
  have h17 : p=17 := (show ∀ b : Fin 18, 13<b.val → b.val.Prime → b.val=17 by decide)
    ⟨p,by omega⟩ hp13 (Nat.prime_of_mem_primeFactors hp)
  subst p
  have hquot := deficient_complement_eq_three_of_large_second h ho hc floor
  have hprod := Nat.div_mul_cancel (Nat.mem_properDivisors.mp h.1).1
  rw [hquot] at hprod
  have hbal : 3*sigma 1 n=5*n := by have := h.2; omega
  have hsig : 17∣sigma 1 n := (by decide : Nat.Coprime 17 3).dvd_of_dvd_mul_left
    (hbal ▸ dvd_mul_of_dvd_right (Nat.dvd_of_mem_primeFactors hp) _)
  obtain ⟨x,hx,_,pair,_⟩ := h.tothPair ho
  obtain ⟨r,hr,s,hs,hrs,hr1,hs1⟩ := two_fermat_residue_primes_of_deficient_thirds ho
    (toth_odd_cofactor_square pair hx).1 (by decide : Nat.Prime 17) (by decide)
    (by decide : 17-1=2^4) hsig hbal
  have big (b : ℕ) (hb : b∈n.primeFactors) (hmod : 17∣b-1) : 53≤b := by
    by_contra! hh
    exact (show ∀ z : Fin 53, z.val.Prime → ¬17∣z.val-1 by decide)
      ⟨b,hh⟩ (Nat.prime_of_mem_primeFactors hb) hmod
  have hR := big r hr hr1
  have hS := big s hs hs1
  have hr3 : (3:ℕ)≠r := by omega
  have hs3 : (3:ℕ)≠s := by omega
  have hr17 : (17:ℕ)≠r := by omega
  have hs17 : (17:ℕ)≠s := by omega
  have h317 : (3:ℕ)≠17 := by decide
  have hset : ({3,17,r,s}:Finset ℕ) = n.primeFactors := by
    apply eq_of_subset_of_card_le
    · intro b hb
      rcases (show b=3 ∨ b=17 ∨ b=r ∨ b=s by simpa using hb) with rfl|rfl|rfl|rfl
      · exact hn3
      · exact hp
      · exact hr
      · exact hs
    · simpa [h317,hr3,hs3,hr17,hs17,hrs] using hc
  have hn : 1<n := by have := Nat.pos_of_mem_properDivisors h.1; have := (Nat.mem_properDivisors.mp h.1).2; omega
  have lower := FactorBudget.abundancy_lt_prod_limits hn
  rw [←hset] at lower
  simp only [prod_insert,mem_insert,mem_singleton,h317,hr3,hs3,hr17,hs17,hrs,
    false_or,not_false_eq_true,prod_singleton] at lower
  have non (b : ℕ) : 0≤primeAbundancyLimit b := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have bound := mul_le_mul (primeAbundancyLimit_antitone (by decide : 1<53) hR)
    (primeAbundancyLimit_antitone (by decide : 1<53) hS) (non s) (non 53)
  have upper : (sigma 1 n:ℚ)/n<5/3 :=
    (lower.trans_le (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left bound (non 17)) (non 3))).trans (by decide +kernel)
  have cap := (div_lt_div_iff₀ (by exact_mod_cast ho.pos : (0:ℚ)<n) (by decide : (0:ℚ)<3)).mp upper
  have small : sigma 1 n*3<5*n := by exact_mod_cast cap
  omega

end OddPerfect
