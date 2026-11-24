module

public import OddPerfect.EvenPrimePowerSources
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Order.Ring.Abs

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- Every cofactor source returns an odd power of the index prime. Their
exponents, counted separately for every source, add to the exponent of the index. -/
theorem even_index_source_valuation_budget {q p s u : ℕ} (hp : p.Prime) (hs : Odd s)
    (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2) (hσs : sigma 1 (s^2)=p^(2*u)) :
    let f (r : ℕ) := sigma 1 (r^(2*s.factorization r))
    let v (r : ℕ) := (f r).factorization p
    (∑ r ∈ s.primeFactors,v r)=2*u ∧
      ∀ r ∈ s.primeFactors, Odd (v r) ∧ f r=p^(v r) := by
  let f (r : ℕ) := sigma 1 (r^(2*s.factorization r))
  let v (r : ℕ) := (f r).factorization p
  have hprod : (∏ r ∈ s.primeFactors,f r)=p^(2*u) := by
    rw [←hσs,(isMultiplicative_sigma (k:=1)).multiplicative_factorization _ (pow_ne_zero _ hs.pos.ne')]
    change _ = ∏ r ∈ (s^2).primeFactors,sigma 1 (r^((s^2).factorization r))
    simp [f,Nat.primeFactors_pow s (by decide : 2≠0),Nat.factorization_pow]
  have hpos (r : ℕ) (hr : r ∈ s.primeFactors) : f r≠0 :=
    (sigma_pos _ _ (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hr).ne_zero)).ne'
  have hsum := congrArg (fun n:ℕ => n.factorization p) hprod
  change (∏ r ∈ s.primeFactors,f r).factorization p=(p^(2*u)).factorization p at hsum
  rw [Nat.factorization_prod_apply hpos,hp.factorization_pow,Finsupp.single_eq_same] at hsum
  change ∑ r ∈ s.primeFactors,v r=2*u at hsum
  refine ⟨hsum,?_⟩
  intro r hr
  obtain ⟨β,hβ,hEq⟩ := even_index_source_odd_power hp hs hσq hplus hσs hr
  change Odd (v r) ∧ f r=p^(v r)
  have hv : v r=β := by simp [v,f,hEq,hp.factorization_pow]
  exact ⟨hv ▸ hβ,hv ▸ hEq⟩

/-- The number of primes in the remaining cofactor is even and cannot
exceed the exponent of the prime-power index. -/
theorem even_index_cofactor_prime_count {q p s u : ℕ} (hp : p.Prime) (hs : Odd s)
    (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2) (hσs : sigma 1 (s^2)=p^(2*u)) :
    Even s.primeFactors.card ∧ s.primeFactors.card≤2*u := by
  let v (r : ℕ) := (sigma 1 (r^(2*s.factorization r))).factorization p
  obtain ⟨hsum,hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  change ∑ r ∈ s.primeFactors,v r=2*u at hsum
  have hodd (r : ℕ) (hr : r ∈ s.primeFactors) : Odd (v r) := (hparts r hr).1
  have hpar := Nat.ModEq.sum (s:=s.primeFactors) (g:=fun _ => 1)
    (fun r hr => (show v r ≡ 1 [MOD 2] from Nat.odd_iff.mp (hodd r hr)))
  rw [hsum] at hpar
  simp only [Finset.sum_const,smul_eq_mul,mul_one] at hpar
  change 2*u%2=s.primeFactors.card%2 at hpar
  have hle : ∑ _r ∈ s.primeFactors,1 ≤ ∑ r ∈ s.primeFactors,v r :=
    Finset.sum_le_sum (fun r hr => (hodd r hr).pos)
  simpa [hsum] using (show Even s.primeFactors.card ∧ (∑ _r ∈ s.primeFactors,1) ≤ ∑ r ∈ s.primeFactors,v r
    from ⟨Nat.even_iff.mpr (by omega),hle⟩)

/-- An odd square doubled and decreased by one is one modulo sixteen. -/
theorem one_mod_sixteen_of_twice_odd_square {q s : ℕ} (hs : Odd s) (hplus : q+1=2*s^2) : q%16=1 := by
  have hs2 := Nat.odd_iff.mp hs
  have hs8 : s%8=1 ∨ s%8=3 ∨ s%8=5 ∨ s%8=7 := by omega
  have hsq : s^2%8=1 := by
    rw [pow_two,Nat.mul_mod]
    rcases hs8 with h|h|h|h <;> simp [h]
  omega

/-- At a base one modulo four, the selected prime's residue forces a
multiple of sixteen as the exponent of the index prime. -/
theorem sixteen_dvd_even_index_exponent_of_one_mod_four {q p s u : ℕ}
    (hp : p.Prime) (hp4 : p%4=1) (hs : Odd s)
    (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2) : 16 ∣ 2*u := by
  let G := geometricBlock (p^2) u
  have hgeom : q=p*(p+1)*G+1 := by
    rw [←hσq,sigma_one_apply_prime_pow hp,Finset.sum_range_succ']
    simp only [pow_succ',←Finset.mul_sum,pow_zero]
    change p*geometricBlock p (2*u)+1=_
    rw [geometricBlock_mul,show geometricBlock p 2=p+1 by simp [geometricBlock,Finset.sum_range_succ,Nat.add_comm]]
    simp [G,Nat.mul_assoc]
  have hq16 := one_mod_sixteen_of_twice_odd_square hs hplus
  let h := (p+1)/2
  have hh : p+1=2*h := by dsimp [h]; omega
  have hho : Odd h := Nat.odd_iff.mpr (by dsimp [h]; omega)
  have hpo : Odd p := Nat.odd_iff.mpr (by omega)
  have hdiv : 16 ∣ p*(p+1)*G := by omega
  rw [hh,show p*(2*h)*G=2*((p*h)*G) by ring] at hdiv
  have hd8 : 8 ∣ (p*h)*G := Nat.dvd_of_mul_dvd_mul_left (by decide : 0<2) hdiv
  have hcop : Nat.Coprime 8 (p*h) := by
    exact (show Nat.Coprime (2^3) (p*h) from (Nat.coprime_two_left.mpr (hpo.mul hho)).pow_left 3)
  have hG : 8 ∣ G := hcop.dvd_of_dvd_mul_left hd8
  have hp8 : p%8=1 ∨ p%8=5 := by omega
  have hs8 : p^2 ≡ 1 [MOD 8] := by
    change p^2%8=1
    rw [pow_two,Nat.mul_mod]
    rcases hp8 with h|h <;> simp [h]
  have hmod : G ≡ u [MOD 8] := geom_modEq_of_one hs8 _
  have hud := (hmod.dvd_iff dvd_rfl).mp hG
  omega

/-- The number of prime divisors of the whole Euler form is exactly two
more than that of the remaining cofactor. -/
theorem prime_count_of_even_index_split {N q p m s u : ℕ} (hq : q.Prime) (hp : p.Prime)
    (hm : Odd m) (hs : Odd s) (hu : 0<u) (hqm : ¬q ∣ m) (hc : p.Coprime s)
    (hform : N=q*m^2) (hms : m=p^u*s) : N.primeFactors.card=s.primeFactors.card+2 := by
  have hqn : q ∉ m.primeFactors := fun h => hqm (Nat.dvd_of_mem_primeFactors h)
  have hpn : p ∉ s.primeFactors := fun h => (hp.coprime_iff_not_dvd.mp hc) (Nat.dvd_of_mem_primeFactors h)
  rw [hform,Nat.primeFactors_mul hq.ne_zero (pow_ne_zero 2 hm.pos.ne'),Nat.primeFactors_pow m (by decide : 2≠0),
    hq.primeFactors,Finset.singleton_union,Finset.card_insert_of_notMem hqn,hms,
    Nat.primeFactors_mul (pow_ne_zero _ hp.ne_zero) hs.pos.ne',Nat.primeFactors_pow p hu.ne',hp.primeFactors,
    Finset.singleton_union,Finset.card_insert_of_notMem hpn]

end OddPerfect
