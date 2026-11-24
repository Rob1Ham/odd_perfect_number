module

public import OddPerfect.OddGeometricSquares
public import OddPerfect.Hirakawa
public import OddPerfect.Valuations
public import OddPerfect.Cuts
public import OddPerfect.FewPrimes
import all OddPerfect.EulerSquareClass
import Mathlib.Order.Preorder.Finite

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- A divisor-sum edge whose target occurs to odd valuation in the source
component. Both endpoints are genuine prime divisors of N. -/
@[expose] def oddSigmaEdge (N p r : ℕ) : Prop :=
  p∈N.primeFactors ∧ r∈N.primeFactors ∧ Odd ((sigma 1 (p^N.factorization p)).factorization r)

@[expose] def oddSigmaSources (N r : ℕ) : Finset ℕ :=
  N.primeFactors.filter (fun p => Odd ((sigma 1 (p^N.factorization p)).factorization r))

theorem oddSigmaEdge_sigmaEdge {N p r : ℕ} (h : oddSigmaEdge N p r) : sigmaEdge N p r := by
  obtain ⟨hp,hr,ho⟩ := h
  exact ⟨hp,hr,(Nat.dvd_of_mem_primeFactors (Finsupp.mem_support_iff.mpr ho.pos.ne'))⟩

theorem oddSigmaEdge_ne {N p r : ℕ} (h : oddSigmaEdge N p r) : p≠r := by
  intro hh
  subst r
  have hdiv := (oddSigmaEdge_sigmaEdge h).2.2
  rw [Nat.dvd_iff_mod_eq_zero,sigma_prime_pow_mod_self (Nat.prime_of_mem_primeFactors h.1)] at hdiv
  omega

private theorem sum_mod_two_filter_odd {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → ℕ) :
    (∑ i∈S, f i) ≡ (S.filter (fun i => Odd (f i))).card [MOD 2] := by
  induction S using Finset.induction_on with
  | empty => exact Nat.ModEq.refl _
  | insert a S ha ih =>
    rw [sum_insert ha,filter_insert]
    by_cases hw : Odd (f a)
    · rw [ite_eq_left hw,card_insert_of_notMem (fun h => ha (mem_filter.mp h).1),add_comm _ 1]
      exact (show f a ≡ 1 [MOD 2] from Nat.odd_iff.mp hw).add ih
    · rw [ite_eq_right hw]
      have hf : f a ≡ 0 [MOD 2] := Nat.even_iff.mp ((Nat.even_or_odd _).resolve_right hw)
      simpa using hf.add ih

theorem even_oddSigmaSources_iff {N r : ℕ} (hN : N.Perfect) (hr : r.Prime) (hro : Odd r) :
    Even (oddSigmaSources N r).card ↔ Even (N.factorization r) := by
  rw [factorization_eq_sum_sigma_factorizations hN hro hr,Nat.even_iff,Nat.even_iff]
  have h := sum_mod_two_filter_odd N.primeFactors (fun p => (sigma 1 (p^N.factorization p)).factorization r)
  exact (congrArg (· = 0) h).symm.to_iff

private theorem parity_target_in_support {N p r : ℕ} (hN : N.Perfect) (hp : p∈N.primeFactors)
    (hr : r.Prime) (hro : Odd r) (hv : Odd ((sigma 1 (p^N.factorization p)).factorization r)) :
    r∈N.primeFactors := by
  have h := single_le_sum (f:=fun u => (sigma 1 (u^N.factorization u)).factorization r)
      (s:=N.primeFactors) (fun _ _ => Nat.zero_le _) hp
  rw [←factorization_eq_sum_sigma_factorizations hN hro hr] at h
  exact Finsupp.mem_support_iff.mpr ((hv.pos.trans_le h).ne')

private theorem nonspecial_odd_edge
    {N p : ℕ} (hN : N.Perfect) (hNo : Odd N) (hp : p∈N.primeFactors)
    (he : Even (N.factorization p)) (hex : ¬(p=3 ∧ N.factorization p=4)) :
    ∃ r, oddSigmaEdge N p r := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hepos := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (show p∈N.factorization.support from hp))
  have hpo := hNo.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
  have heo : Odd (N.factorization p+1) := Nat.odd_iff.mpr (by have := Nat.even_iff.mp he; omega)
  have hshape : sigma 1 (p^N.factorization p)=geometricBlock p (N.factorization p+1) := sigma_one_apply_prime_pow hpp
  have hn : ¬IsSquare (sigma 1 (p^N.factorization p)) := by
    rw [hshape,geometricBlock_isSquare_iff_of_odd_length hpp.one_lt (by omega) heo]
    omega
  obtain ⟨r,hr,hv⟩ := exists_odd_valuation_of_nonsquare hn
  have hd : r∣sigma 1 (p^N.factorization p) := Nat.dvd_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hv.pos.ne')
  have hs := sigma_modEq_of_one hpp (show p ≡ 1 [MOD 2] from Nat.odd_iff.mp hpo) (N.factorization p)
  have hso : Odd (sigma 1 (p^N.factorization p)) := Nat.odd_iff.mpr (hs.trans (show N.factorization p+1 ≡ 1 [MOD 2] from Nat.odd_iff.mp heo))
  exact ⟨r,hp,parity_target_in_support hN hp hr (hso.of_dvd_nat hd) hv,hv⟩

private theorem special_odd_edge_of_nonsquare_half {N q : ℕ} (hN : N.Perfect) (hq : q∈N.primeFactors)
    (hq4 : q%4=1) (ha4 : N.factorization q%4=1)
    (hn : ¬IsSquare ((sigma 1 (q^N.factorization q))/2)) : ∃ r, oddSigmaEdge N q r := by
  have hqp := Nat.prime_of_mem_primeFactors hq
  let S := sigma 1 (q^N.factorization q)
  have h4 := sigma_modEq_of_one hqp (show q ≡ 1 [MOD 4] from hq4) (N.factorization q)
  change S%4=(N.factorization q+1)%4 at h4
  have hs : S=2*(S/2) := by omega
  obtain ⟨r,hr,hv⟩ := exists_odd_valuation_of_nonsquare hn
  have hrd : r∣S/2 := Nat.dvd_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hv.pos.ne')
  have hro := (Nat.odd_iff.mpr (show (S/2)%2=1 by omega)).of_dvd_nat hrd
  have h2 : ¬r∣2 := fun h => hro.not_two_dvd_nat (((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h) ▸ dvd_refl _)
  have hval : Odd (S.factorization r) := by
    conv in S.factorization r => rw [hs,Nat.factorization_mul (by decide : (2:ℕ)≠0) (by omega),Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd h2,zero_add]
    exact hv
  exact ⟨r,hq,parity_target_in_support hN hq hr hro hval,hval⟩

private theorem special_half_nonsquare {N q : ℕ} (hq : q∈N.primeFactors) (hq4 : q%4=1)
    (ha4 : N.factorization q%4=1) (ha : 1<N.factorization q) :
    ¬IsSquare (sigma 1 (q^N.factorization q)/2) := by
  let S := sigma 1 (q^N.factorization q)
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hs := sigma_modEq_of_one hqp (show q ≡ 1 [MOD 4] from hq4) (N.factorization q)
  change S%4=(N.factorization q+1)%4 at hs
  rintro ⟨y,hy⟩
  change S/2=y*y at hy
  apply sigma_prime_pow_ne_twice_square hqp hq4 ha y
  change S=2*y^2
  rw [pow_two]
  omega

/-- Some nonspecial prime gets odd divisor-sum valuations from at least two
different components of every odd perfect number. -/
theorem exists_even_exponent_with_two_odd_sigma_sources
    {N : ℕ} (hN : N.Perfect) (hNo : Odd N) :
    ∃ r∈N.primeFactors, Even (N.factorization r) ∧ 2≤(oddSigmaSources N r).card := by
  obtain ⟨q,hq,hq4,ha4,hrest⟩ := euler_exponents hNo hN
  have hex : ∃ p r, oddSigmaEdge N p r ∧ r≠q := by
    by_cases ha : 1<N.factorization q
    · obtain ⟨r,hr⟩ := special_odd_edge_of_nonsquare_half hN hq hq4 ha4 (special_half_nonsquare hq hq4 ha4 ha)
      exact ⟨q,r,hr,(oddSigmaEdge_ne hr).symm⟩
    by_contra! h
    let S := (N.primeFactors.erase q).erase 3
    have hsub : S ⊆ N.primeFactors := fun _ h => mem_of_mem_erase (mem_of_mem_erase h)
    have hsources (p : ℕ) (hp : p∈S) : q∣sigma 1 (p^N.factorization p) := by
      have hp3 := (mem_erase.mp hp).1
      have hpq := (mem_erase.mp (mem_erase.mp hp).2).1
      obtain ⟨r,hr⟩ := nonspecial_odd_edge hN hNo (hsub hp) (hrest p hpq) (fun eq => hp3 eq.1)
      have hqeq := h p r hr
      exact hqeq ▸ (oddSigmaEdge_sigmaEdge hr).2.2
    have hc := card_le_factorization_of_sigma_sources hN (hNo.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq))
      (Nat.prime_of_mem_primeFactors hq) S hsub hsources
    have h5 := five_le_distinct_prime_factor_count hNo hN
    have h2 := card_erase_of_mem hq
    by_cases h3 : 3∈N.primeFactors.erase q
    · change ((N.primeFactors.erase q).erase 3).card ≤ _ at hc
      rw [card_erase_of_mem h3,h2] at hc
      omega
    · dsimp [S] at hc
      rw [erase_eq_of_notMem h3,h2] at hc
      omega
  obtain ⟨p,r,hpr,hne⟩ := hex
  have hr := hpr.2.1
  have he := hrest r hne
  have hrom := (even_oddSigmaSources_iff hN (Nat.prime_of_mem_primeFactors hr)
    (hNo.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr))).mpr he
  have hpos : 0<(oddSigmaSources N r).card := card_pos.mpr ⟨p,mem_filter.mpr ⟨hpr.1,hpr.2.2⟩⟩
  exact ⟨r,hr,he,by have := Nat.even_iff.mp hrom; omega⟩

private theorem transGen_cycle_of_finite_outgoing {S : Finset ℕ} {E : ℕ → ℕ → Prop} (hS : S.Nonempty)
    (hout : ∀ p∈S, ∃ r∈S, E p r) : ∃ p∈S, Relation.TransGen E p p := by
  classical
  let step (p : S) : S := ⟨(hout p p.property).choose,(hout p p.property).choose_spec.1⟩
  have hstep (p : S) : E p (step p) := (hout p p.property).choose_spec.2
  obtain ⟨p,hp⟩ := hS
  let f : ℕ → ↥S := Nat.rec (motive:=fun _ => ↥S) ⟨p,hp⟩ (fun _ prev => step prev)
  have hf (j : ℕ) : E (f j).val (f (j+1)).val := by
    change E (f j).val (step (f j)).val
    exact hstep (f j)
  obtain ⟨i,j,hij,heq⟩ := S.finite_toSet.exists_lt_map_eq_of_forall_mem (f:=fun n : ℕ => (f n).val)
    (fun n => (f n).property)
  have hpath (k : ℕ) : Relation.TransGen E (f i).val (f (i+k+1)).val := by
    induction k with
    | zero => exact .single (hf i)
    | succ k ih => exact .tail ih (hf (i+k+1))
  have h := hpath (j-i-1)
  rw [show i+(j-i-1)+1=j by omega,←heq] at h
  exact ⟨(f i).val,(f i).property,h⟩

private theorem dvd121_of_four {N : ℕ} (hN : N.Perfect) (he : N.factorization 3=4) : 121∣N := by
  have h := Nat.prime_three.pow_dvd_iff_le_factorization hN.2.ne' (k:=4)
  have h' := Nat.prime_three.pow_dvd_iff_le_factorization hN.2.ne' (k:=5)
  obtain ⟨b,hab,hcop⟩ := exists_coprime_cofactor_of_exact_prime_pow (p:=3) (k:=4)
    Nat.prime_three (h.mpr (by omega)) (fun H => by have := h'.mp H; omega)
  apply odd_dvd_perfect_of_dvd_sum_divisors hN hab hcop (by decide)
  rw [←sigma_one_apply,sigma_one_apply_prime_pow Nat.prime_three]
  decide

/-- The odd-valuation edges contain a directed cycle unless the exact
component 3^4 is present or the exponent-one Euler prime has square half-sum.
The former case forces 11² into the number. -/
theorem odd_sigma_cycle_or_exceptional_sink
    {N : ℕ} (hN : N.Perfect) (hNo : Odd N) :
    (∃ p∈N.primeFactors, Relation.TransGen (oddSigmaEdge N) p p) ∨
    (N.factorization 3=4 ∧ 121∣N) ∨
    ∃ q∈N.primeFactors, q%16=1 ∧ N.factorization q=1 ∧ IsSquare ((q+1)/2) := by
  obtain ⟨q,hq,hq4,ha4,hrest⟩ := euler_exponents hNo hN
  by_cases h3 : N.factorization 3=4
  · exact Or.inr (Or.inl ⟨h3,dvd121_of_four hN h3⟩)
  by_cases hy : IsSquare (sigma 1 (q^N.factorization q)/2)
  · have ha : N.factorization q=1 := by
      by_contra! hh
      exact special_half_nonsquare hq hq4 ha4 (by omega) hy
    have hqsum : sigma 1 (q^N.factorization q)=q+1 := by
      rw [ha,sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hq)]
      simp [sum_range_succ,add_comm]
    rw [hqsum] at hy
    obtain ⟨y,hy'⟩ := hy
    have hymod := (Nat.mod_modEq y 8).pow 2
    change (y%8)^2%8=y^2%8 at hymod
    have hy2 : (q+1)/2=y^2 := by simpa [pow_two] using hy'
    have hy8 : y%8<8 := Nat.mod_lt _ (by decide)
    have hq16 : q%16=1 := by interval_cases y%8 <;> norm_num at hymod <;> omega
    exact Or.inr (Or.inr ⟨q,hq,hq16,ha,y,hy'⟩)
  left
  apply transGen_cycle_of_finite_outgoing ⟨q,hq⟩
  intro p hp
  by_cases hpq : p=q
  · subst p
    obtain ⟨r,hr⟩ := special_odd_edge_of_nonsquare_half hN hq hq4 ha4 hy
    exact ⟨r,hr.2.1,hr⟩
  obtain ⟨r,hr⟩ := nonspecial_odd_edge hN hNo hp (hrest p hpq)
    (by rintro ⟨rfl,he⟩; exact h3 he)
  exact ⟨r,hr.2.1,hr⟩

/-- Odd-valuation local edges at even exponents admit a three-cycle among
primes three modulo four. -/
theorem odd_valuation_three_cycle :
    Odd ((sigma 1 (7^2)).factorization 19) ∧
    Odd ((sigma 1 (19^4)).factorization 151) ∧
    Odd ((sigma 1 (151^2)).factorization 7) := by
  rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 7),
    sigma_one_apply_prime_pow (by decide : Nat.Prime 19),
    sigma_one_apply_prime_pow (by decide : Nat.Prime 151)]
  decide +kernel

end OddPerfect
