module

public import OddPerfect.EvenIndexRoots
public import OddPerfect.AbundancyLimit
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Tactic.Primality.Lucas
import Mathlib.Tactic.FieldSimp

public section
namespace OddPerfect
open ArithmeticFunction Finset
open Mathlib.Tactic.Primality

/-- A local cost β(r−1)≥K lets the multiplicity pay for the limiting
abundancy at r. -/
theorem prime_limit_le_cost_pow {r v K : ℕ} (hr : 1<r) (hk : 0<K) (hc : K≤v*(r-1)) :
    primeAbundancyLimit r ≤ (1+1/(K:ℚ))^v := by
  have hK : (0:ℚ)<K := by exact_mod_cast hk
  have hR : (0:ℚ)<(r-1:ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hr
  have H : (K:ℚ)≤(v:ℚ)*((r-1:ℕ):ℚ) := by exact_mod_cast hc
  have he : (r:ℚ)=((r-1:ℕ):ℚ)+1 := by exact_mod_cast (by omega : r=r-1+1)
  calc primeAbundancyLimit r ≤ 1+(v:ℚ)*(1/(K:ℚ)) := by
         rw [primeAbundancyLimit,div_le_iff₀ hR,he]
         field_simp [hK]
         nlinarith
       _ ≤ _ := one_add_mul_le_pow ((by decide : (-2:ℚ)≤0).trans (one_div_nonneg.mpr (Nat.cast_nonneg K))) v

/-- Limiting abundancies over exceptional sources can be multiplied
once each. All remaining sources are charged to their valuation budget. -/
theorem even_index_abundancy_envelope {p q s u K : ℕ} (hp : p.Prime) (hs : Odd s)
    (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2) (hσs : sigma 1 (s^2)=p^(2*u))
    (hk : 0<K) (E : Finset ℕ) (hE : ∀ r ∈ E, 1<r)
    (hcost : ∀ r ∈ s.primeFactors, r∉E → ∀ v, Odd v →
      sigma 1 (r^(2*s.factorization r))=p^v → v≤2*u → K≤v*(r-1)) :
    (∏ r ∈ s.primeFactors, primeAbundancyLimit r) ≤
      (∏ r ∈ E,primeAbundancyLimit r)*(1+1/(K:ℚ))^(2*u) := by
  let S := s.primeFactors
  let v (r : ℕ) := (sigma 1 (r^(2*s.factorization r))).factorization p
  let F := fun r => if r ∈ E then primeAbundancyLimit r else 1
  let L := 1+1/(K:ℚ)
  have hlay : 1≤L := le_add_of_nonneg_right (one_div_nonneg.mpr (Nat.cast_nonneg K))
  have non (r : ℕ) : 0≤primeAbundancyLimit r := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have one (r : ℕ) (hr : 1<r) : 1≤primeAbundancyLimit r := by
    rw [primeAbundancyLimit,le_div_iff₀ (by exact_mod_cast Nat.sub_pos_of_lt hr),one_mul]
    exact_mod_cast Nat.sub_le r 1
  obtain ⟨hsum,hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  change ∑ r ∈ S,v r=2*u at hsum
  have hloc (r : ℕ) (hr : r∈S) : primeAbundancyLimit r≤F r*L^(v r) := by
    by_cases he : r∈E
    · change _≤(if r∈E then _ else _)*_
      rw [ite_eq_left he]
      exact le_mul_of_one_le_right (non r) (one_le_pow₀ hlay)
    · change _≤(if r∈E then _ else _)*_
      rw [ite_eq_right he,one_mul]
      obtain ⟨ho,H⟩ := hparts r hr
      have hc : v r≤2*u := hsum ▸ Finset.single_le_sum (fun r _ => Nat.zero_le (v r)) hr
      exact prime_limit_le_cost_pow (Nat.prime_of_mem_primeFactors hr).one_lt hk (hcost _ hr he _ ho H hc)
  have hFE : S.prod F≤E.prod primeAbundancyLimit := by
    simp only [F,Finset.prod_ite,Finset.prod_const_one,mul_one]
    exact Finset.prod_le_prod_of_subset_of_one_le₀ (fun r hr => (Finset.mem_filter.mp hr).2)
      (fun r _ => non r) (fun r hr _ => one r (hE r hr))
  calc _ ≤ ∏ r ∈ S,F r*L^(v r) := Finset.prod_le_prod₀ (fun r _ => non r) hloc
       _ = S.prod F * L^(2*u) := by rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,hsum]
       _ ≤ E.prod primeAbundancyLimit * L^(2*u) := mul_le_mul_of_nonneg_right hFE (pow_nonneg (zero_le_one.trans hlay) _)

/-- The finite checker asks whether the two congruences admit a return
multiplicity that is too small at one of the primes below the cutoff. -/
@[expose] def SourceCostCheck (j K C : ℕ) (E : Finset ℕ) : Prop :=
  ∀ r : Fin C, r.val.Prime → 2<r.val → r.val∉E → ∀ x : Fin r.val,
    (x.val≠1 ∨ r.val ∣ j+2) → (powMod x.val (j+1) r.val+x.val)%r.val=2%r.val →
    ∀ v : Fin (j+1), Odd v.val → powMod x.val v.val r.val=1%r.val →
      K≤v.val*(r.val-1)

instance (j K C : ℕ) (E : Finset ℕ) : Decidable (SourceCostCheck j K C E) := by
  unfold SourceCostCheck
  infer_instance

theorem source_cost_of_check {p q s u r β K C : ℕ} (E : Finset ℕ)
    (check : SourceCostCheck (2*u) K C E)
    (hp : p.Prime) (hr : r.Prime) (hro : Odd r) (hrs : r ∣ s) (he : r∉E)
    (hcut : r<C) (hβ : Odd β) (hb : β≤2*u)
    (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2)
    (hout : sigma 1 (r^(2*s.factorization r))=p^β) : K≤β*(r-1) := by
  let : NeZero r := ⟨hr.ne_zero⟩
  let x : ZMod r := p
  obtain ⟨hpow,hret,hone⟩ := even_index_source_root_equations hp hr hrs hσq hplus hout
  change x^β=1 at hpow
  change x^(2*u+1)+x=2 at hret
  change x=1 → r ∣ 2*u+2 at hone
  have H (k : ℕ) : powMod x.val k r=(x^k).val := by
    rw [powMod_def,←ZMod.val_natCast,Nat.cast_pow,ZMod.natCast_zmod_val]
  have h1 : x.val≠1 ∨ r ∣ 2*u+2 := by
    by_cases hx : x.val=1
    · right
      apply hone
      rw [←ZMod.natCast_zmod_val x,hx,Nat.cast_one]
    · exact .inl hx
  have h2 : (powMod x.val (2*u+1) r+x.val)%r=2%r := by
    rw [H,←ZMod.val_add,hret]
    exact (ZMod.val_natCast r 2)
  have h3 : powMod x.val β r=1%r := by
    rw [H,hpow]
    simpa only [Nat.cast_one] using (ZMod.val_natCast r 1)
  have hgt : 2<r := by have := hr.two_le; have := Nat.odd_iff.mp hro; omega
  exact check ⟨r,hcut⟩ hr hgt he ⟨x.val,ZMod.val_lt x⟩ h1 h2 ⟨β,by omega⟩ hβ h3

end OddPerfect
