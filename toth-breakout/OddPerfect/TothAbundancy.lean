module

public import OddPerfect.TothCandidates
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

public section

namespace OddPerfect.Toth

open Finset ArithmeticFunction

theorem sigma_ratio_product {m : ℕ} (hm : 0<m) :
    (sigma 1 m:ℚ)/m = ∏ p ∈ m.primeFactors, componentAbundancy p (m.factorization p) := by
  calc _ = ((∏ p ∈ m.primeFactors, sigma 1 (p^m.factorization p):ℕ):ℚ) /
             ((∏ p ∈ m.primeFactors, p^m.factorization p:ℕ):ℚ) := by
             congr 1
             · exact_mod_cast isMultiplicative_sigma.multiplicative_factorization (sigma 1) hm.ne'
             · exact_mod_cast Nat.prod_primeFactors_pow_factorization hm.ne'
       _ = _ := by
             simp only [Nat.cast_prod,← prod_div_distrib]
             apply prod_congr rfl
             intro p hp
             have hpr := Nat.prime_of_mem_primeFactors hp
             rw [sigma_one_apply_prime_pow hpr,componentAbundancy_eq hpr.pos,Nat.cast_pow]

/-- A size limit bounds the number of distinct primes in the unknown
square root and hence its multiplicative contribution to abundancy. -/
theorem suffix_strict_limit {m a k : ℕ} (hm : 1<m) (ha : 1<a) (hpr : ∀ p ∈ m.primeFactors, a≤p)
    (hk : m<a^(k+1)) : (sigma 1 (m^2):ℚ)/(m^2:ℕ) < (primeAbundancyLimit a)^k := by
  have hm' : 0<m := by omega
  have hprod : a^m.primeFactors.card ≤ m := by
    calc _ = ∏ _ ∈ m.primeFactors,a := by simp
         _ ≤ ∏ p ∈ m.primeFactors,p^m.factorization p := by
             apply prod_le_prod
             intro p hp
             have h := Nat.prime_of_mem_primeFactors hp
             have he := h.factorization_pos_of_dvd hm'.ne' (Nat.dvd_of_mem_primeFactors hp)
             exact (hpr p hp).trans (by simpa using Nat.pow_le_pow_right h.pos he)
         _ = m := (Nat.prod_primeFactors_pow_factorization hm'.ne').symm
  have hcard : m.primeFactors.card≤k := by
    by_contra! h
    exact hk.not_ge ((Nat.pow_le_pow_right (by omega : 0<a) h).trans hprod)
  have hlim : 1 ≤ primeAbundancyLimit a := by
    rw [primeAbundancyLimit,le_div_iff₀ (by exact_mod_cast Nat.sub_pos_of_lt ha),one_mul]
    exact_mod_cast Nat.sub_le a 1
  have hset := Nat.primeFactors_pow m (by decide : 2≠0)
  rw [sigma_ratio_product (pow_pos hm' 2),hset]
  apply lt_of_lt_of_le _ (pow_le_pow_right₀ hlim hcard)
  rw [←prod_const]
  apply prod_lt_prod_of_nonempty₀ (f:=fun p => componentAbundancy p ((m^2).factorization p))
    (g:=fun _ => primeAbundancyLimit a) (fun p _ => zero_lt_one.trans_le (one_le_componentAbundancy p _))
    _ (Nat.nonempty_primeFactors.mpr hm)
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hb : componentAbundancy p ((m^2).factorization p) < primeAbundancyLimit p := by
    simpa only [primeAbundancyLimit,Nat.cast_sub hprime.one_lt.le,Nat.cast_one] using
      componentAbundancy_lt_limit hprime.one_lt ((m^2).factorization p)
  exact hb.trans_le (primeAbundancyLimit_antitone ha (hpr p hp))

/-- Least multiplier above the prefix quotient and compatible with the
Euler residue and nontriviality. The suffix here is nonempty. -/
@[expose] def nextMultiplier (D S : ℕ) : ℕ :=
  let z := max 5 (S/(2*D^2-S)+1)
  z+(5-z%4)%4

private theorem prefix_strict {B D S a m x : ℕ} (h : Candidate B D S a m x) (hm : 1<m) :
    S*(x+1) < (2*D^2)*x := by
  have hv : 1<m^2 := Nat.one_lt_pow (by decide) hm
  have hs := self_lt_sigma_of_one_lt hv
  have le := Nat.mul_lt_mul_of_pos_left hs (Nat.mul_pos h.sumpos (Nat.succ_pos x))
  have eq : S*(x+1)*sigma 1 (m^2) = ((2*D^2)*x)*m^2 := by
    convert h.balance using 1 <;> ring
  rw [eq] at le
  exact Nat.lt_of_mul_lt_mul_right le

theorem nextMultiplier_le {B D S a m x : ℕ} (h : Candidate B D S a m x) (hm : 1<m) :
    nextMultiplier D S ≤ x := by
  have hlow := prefix_strict h hm
  have hlt : S<2*D^2 := by
    by_contra! hn
    have := Nat.mul_le_mul_right x hn
    nlinarith
  have hd := Nat.sub_pos_of_lt hlt
  have hv : S < (2*D^2-S)*x := by nlinarith [congrArg (· * x) (Nat.sub_add_cancel hlt.le)]
  have hx := (Nat.div_lt_iff_lt_mul hd).mpr (by simpa [mul_comm] using hv)
  have hmax : max 5 (S/(2*D^2-S)+1)≤x := max_le h.large hx
  dsimp only [nextMultiplier]
  have := h.residue
  omega

theorem closed_abundant {B D S a : ℕ} (cut : 2*D^2≤S) (empty : checkPoint D S) : Closed B D S a := by
  intro m x h
  by_cases hm : m=1
  · subst m; exact at_one h empty
  · have hl := prefix_strict h (by have := h.pos; omega)
    have := Nat.mul_le_mul_right x cut
    nlinarith

theorem closed_interval {B D S a k : ℕ} (ha : 1<a) (cap : B<D*a^(k+1))
    (empty : checkPoint D S)
    (cut : (S:ℚ)*(primeAbundancyLimit a)^k*((nextMultiplier D S:ℚ)+1) ≤
      2*(D:ℚ)^2*(nextMultiplier D S:ℚ)) : Closed B D S a := by
  intro m x h
  by_cases hm : m=1
  · subst m; exact at_one h empty
  · have hm' : 1<m := by have := h.pos; omega
    have hlim := suffix_strict_limit hm' ha h.least (show m<a^(k+1) by
      by_contra! ht
      exact cap.not_ge ((Nat.mul_le_mul_left D ht).trans h.bound))
    let t := nextMultiplier D S
    have htx : (t:ℚ)≤x := by exact_mod_cast nextMultiplier_le h hm'
    have ht0 : (0:ℚ)≤t := Nat.cast_nonneg _
    have hx0 : (0:ℚ)≤x := Nat.cast_nonneg _
    have hD : (0:ℚ)<D := by exact_mod_cast h.prefix_pos
    have hm0 : (0:ℚ)<m := by exact_mod_cast h.pos
    have hS : (0:ℚ)<S := by exact_mod_cast h.sumpos
    have hc : (S:ℚ)*(primeAbundancyLimit a)^k / (2*(D:ℚ)^2) ≤ (t:ℚ)/(t+1) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      simpa only [mul_right_comm,mul_comm,mul_left_comm,mul_assoc,t] using cut
    have hmono : (t:ℚ)/(t+1) ≤ (x:ℚ)/(x+1) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
    have hEq : (S:ℚ)*((sigma 1 (m^2):ℚ)/(m^2:ℕ))/(2*(D:ℚ)^2)=(x:ℚ)/(x+1) := by
      apply (div_eq_div_iff (by positivity) (by positivity)).mpr
      rw [mul_div_assoc',div_mul_eq_mul_div,div_eq_iff (by positivity)]
      have he : (S:ℚ)*(sigma 1 (m^2):ℚ)*((x:ℚ)+1)=2*((D:ℚ)*m)^2*x := by exact_mod_cast h.balance
      push_cast
      nlinarith
    have hstrict := div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hlim hS) (show (0:ℚ)<2*(D:ℚ)^2 by positivity)
    exact (hEq ▸ hstrict).not_ge (hc.trans hmono) |>.elim

end OddPerfect.Toth
