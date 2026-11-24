module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

public section

namespace OddPerfect.DivisorMoments

open Finset

/-- The contribution of a prime-power component to the divisor-count moment. -/
@[expose] def component (p k s e : ℕ) : ℚ := ((e+1 : ℕ) : ℚ)^k/(p:ℚ)^(s*e)

/-- Maximum of the component ratio over exponents zero through eight. -/
@[expose] def peak (p k s : ℕ) : ℚ :=
  (range 9).sup' (by decide) (component p k s)

/-- Primes in the half-open interval from the lower prime bound to the cutoff. -/
@[expose] def smallPrimes (a C : ℕ) : Finset ℕ := (Ico a C).filter Nat.Prime

/-- The product of the individual small-prime peaks. -/
@[expose] def envelope (a k s C : ℕ) : ℚ := ∏ p ∈ smallPrimes a C, peak p k s

private theorem step {p k s t e : ℕ} (hp : 0<p) (he : t≤e)
    (h : (t+2)^k ≤ p^s*(t+1)^k) : component p k s (e+1) ≤ component p k s e := by
  have hmul : (t+1)*(e+2) ≤ (t+2)*(e+1) := by nlinarith
  have hpow := Nat.pow_le_pow_left hmul k
  rw [mul_pow,mul_pow] at hpow
  have hcancel : (t+1)^k*(e+2)^k ≤ (t+1)^k*(p^s*(e+1)^k) := by
    calc _ ≤ (t+2)^k*(e+1)^k := hpow
         _ ≤ (p^s*(t+1)^k)*(e+1)^k := Nat.mul_le_mul_right _ h
         _ = _ := by ac_rfl
  have hnat := Nat.le_of_mul_le_mul_left hcancel (Nat.pow_pos (Nat.succ_pos _))
  have hrat : ((e+2:ℕ):ℚ)^k ≤ (p:ℚ)^s*((e+1:ℕ):ℚ)^k := by exact_mod_cast hnat
  have hpos : 0<(p:ℚ) := by exact_mod_cast hp
  unfold component
  apply (div_le_div_iff₀ (pow_pos hpos _) (pow_pos hpos _)).mpr
  rw [Nat.mul_succ,pow_add]
  calc _ ≤ ((p:ℚ)^s*((e+1:ℕ):ℚ)^k)*(p:ℚ)^(s*e) :=
         mul_le_mul_of_nonneg_right hrat (pow_nonneg hpos.le _)
       _ = _ := by ring

/-- Successive local ratios decrease past any certified threshold, for all
larger exponents. -/
theorem component_antitone_from {p k s t H e : ℕ} (hp : 0<p)
    (h : (t+2)^k ≤ p^s*(t+1)^k) (ht : t≤H) (he : H≤e) :
    component p k s e ≤ component p k s H := by
  induction e, he using Nat.le_induction with
  | base => rfl
  | succ e he ih => exact (step hp (ht.trans he) h).trans ih

/-- Exponents past any branch cutoff at least eight never exceed the value
at the cutoff when the step from eight to nine decreases. -/
theorem local_moment_tail {p k s H e : ℕ} (hp : 0<p) (h : 10^k ≤ p^s*9^k)
    (hH : 8≤H) (he : H≤e) : component p k s e ≤ component p k s H :=
  component_antitone_from (t:=8) hp h hH he

theorem component_le_peak {p k s e : ℕ} (hp : 0<p) (h : 10^k ≤ p^s*9^k) :
    component p k s e ≤ peak p k s := by
  by_cases he : e≤8
  · exact Finset.le_sup' _ (Finset.mem_range.mpr (by omega : e<9))
  · exact (local_moment_tail hp h (Nat.le_refl 8) (by omega)).trans
      (Finset.le_sup' _ (Finset.mem_range.mpr (by decide : 8<9)))

theorem one_le_peak (p k s : ℕ) : 1 ≤ peak p k s := by
  have h : component p k s 0 ≤ peak p k s := Finset.le_sup' _ (Finset.mem_range.mpr (by decide : 0<9))
  rwa [show component p k s 0=1 by simp [component]] at h

theorem component_le_one {p k s e : ℕ} (hp : 0<p) (h : 2^k≤p^s) : component p k s e ≤ 1 := by
  have h0 : (0+2)^k ≤ p^s*(0+1)^k := by simpa using h
  simpa [component] using component_antitone_from (e:=e) hp h0 (Nat.le_refl 0) (Nat.zero_le e)

theorem divisor_moment_factorization {m : ℕ} (hm : 0<m) (k s : ℕ) :
    (m.divisors.card:ℚ)^k/(m:ℚ)^s = ∏ p ∈ m.primeFactors, component p k s (m.factorization p) := by
  simp only [component,Finset.prod_div_distrib]
  congr 1
  · rw [Finset.prod_pow,←Nat.cast_prod,←Nat.card_divisors hm.ne']
  · calc (m:ℚ)^s = ((∏ p ∈ m.primeFactors,p^m.factorization p : ℕ):ℚ)^s := by
           exact congrArg (fun z : ℕ => (z:ℚ)^s) (Nat.prod_primeFactors_pow_factorization hm.ne')
         _ = ∏ p ∈ m.primeFactors, (p:ℚ)^(s*m.factorization p) := by
           simp only [Nat.cast_prod,Nat.cast_pow,←Finset.prod_pow,←pow_mul,Nat.mul_comm]

/-- A certified product of small-prime peaks bounds the divisor moment
for every positive integer with the prescribed lower prime bound. -/
theorem divisor_moment_le_envelope {m a k s C : ℕ} (hm : 0<m) (ha : 3≤a)
    (hpr : ∀ p ∈ m.primeFactors, a≤p) (hC : 2^k≤C^s)
    (hpeak : ∀ p ∈ smallPrimes a C, 10^k ≤ p^s*9^k) :
    (m.divisors.card:ℚ)^k/(m:ℚ)^s ≤ envelope a k s C := by
  rw [divisor_moment_factorization hm]
  calc _ ≤ ∏ p ∈ m.primeFactors, if p ∈ smallPrimes a C then peak p k s else 1 := by
         apply Finset.prod_le_prod₀
         · intro p _; unfold component; positivity
         · intro p hp
           have hpp := Nat.prime_of_mem_primeFactors hp
           have hpz : 0<p := by have := hpr p hp; omega
           split_ifs with h
           · exact component_le_peak hpz (hpeak p h)
           · have hCp : C≤p := by
               by_contra! hlt
               exact h (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hpr p hp,hlt⟩,hpp⟩)
             exact component_le_one hpz (hC.trans (Nat.pow_le_pow_left hCp s))
       _ = ∏ p ∈ m.primeFactors.filter (· ∈ smallPrimes a C), peak p k s := by rw [Finset.prod_filter]
       _ ≤ _ := Finset.prod_le_prod_of_subset_of_one_le₀ (fun _ hp => (Finset.mem_filter.mp hp).2)
         (fun p _ => (by decide : (0:ℚ)≤1).trans (one_le_peak p k s)) (fun p _ _ => one_le_peak p k s)

/-- If every admissible prime is already beyond the cutoff, nontriviality
allows one prime factor to retain the full first-exponent decrease. -/
theorem divisor_moment_le_first_prime {m a k s : ℕ} (hm : 1<m) (ha : 3≤a)
    (hpr : ∀ p ∈ m.primeFactors, a≤p) (hlarge : 2^k≤a^s) :
    (m.divisors.card:ℚ)^k/(m:ℚ)^s ≤ (2:ℚ)^k/(a:ℚ)^s := by
  let p := m.minFac
  have hp := Nat.minFac_prime hm.ne'
  have hmpos : 0<m := by omega
  have hpS : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp,Nat.minFac_dvd _,hmpos.ne'⟩
  have he := hp.factorization_pos_of_dvd hmpos.ne' (Nat.minFac_dvd m)
  have hpa := hpr p hpS
  have hstep : (0+2)^k ≤ p^s*(0+1)^k := by simpa using hlarge.trans (Nat.pow_le_pow_left hpa s)
  rw [divisor_moment_factorization hmpos]
  calc _ ≤ ∏ u ∈ ({p}:Finset ℕ), component u k s (m.factorization u) := by
         refine Finset.prod_le_prod_of_subset_of_le_one₀ (Finset.singleton_subset_iff.mpr hpS) ?_ ?_
         · intro u _; unfold component; positivity
         · intro u hu _; exact component_le_one (Nat.prime_of_mem_primeFactors hu).pos
             (hlarge.trans (Nat.pow_le_pow_left (hpr u hu) s))
       _ = component p k s (m.factorization p) := by simp
       _ ≤ component p k s 1 := component_antitone_from hp.pos hstep (by decide) he
       _ ≤ _ := by
         simp only [component,Nat.mul_one]
         exact div_le_div_of_nonneg_left (by positivity) (pow_pos (by exact_mod_cast (show 0<a by omega)) _)
           (by exact_mod_cast Nat.pow_le_pow_left hpa s)

end OddPerfect.DivisorMoments
