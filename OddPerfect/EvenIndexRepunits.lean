module

public import OddPerfect.PrimePowerNagellLjunggren
import Mathlib.Data.Finset.Max

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- The same integer has prime-length repunit representations in two
distinct odd prime bases. -/
@[expose] def HasTwoOddPrimeRepunits (z : ℕ) : Prop :=
  ∃ r t l k : ℕ, r.Prime ∧ Odd r ∧ t.Prime ∧ Odd t ∧ r≠t ∧
    l.Prime ∧ 2<l ∧ k.Prime ∧ 2<k ∧ geometricBlock r l=z ∧ geometricBlock t k=z

/-- All the witnesses in a family of this kind share the same prime p
on the right. The witness is indexed by its base r. -/
@[expose] def IsOddRepunitPowerAt (r p : ℕ) : Prop :=
  r.Prime ∧ Odd r ∧ p.Prime ∧ ∃ n c l : ℕ, n.Prime ∧ 2<n ∧ 0<c ∧
    l.Prime ∧ Odd l ∧ geometricBlock r n=(p^c)^l

private theorem small_repunit_parameters {r n : ℕ} (hr : r.Prime) (hn : 2<n)
    (h : geometricBlock r n≤8191) : r<91 ∧ n<15 := by
  have term (t : ℕ) (ht : t<n) : r^t≤geometricBlock r n :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (r^j)) (Finset.mem_range.mpr ht)
  constructor
  · by_contra! hb
    have := (Nat.pow_le_pow_left hb 2).trans ((term 2 hn).trans h)
    norm_num at this
  · by_contra! hb
    have := (Nat.pow_le_pow_left hr.two_le 14).trans ((term 14 (by omega)).trans h)
    norm_num at this

/-- The two classical numerical values cannot have two odd prime-base
representations of the required lengths. -/
theorem classical_values_not_two_odd_prime_repunits :
    ¬HasTwoOddPrimeRepunits 31 ∧ ¬HasTwoOddPrimeRepunits 8191 := by
  have screen : ∀ r : Fin 91, ∀ n : Fin 15, r.val.Prime → Odd r.val →
      n.val.Prime → 2<n.val → (geometricBlock r.val n.val=31 → r.val=5) ∧
        geometricBlock r.val n.val≠8191 := by decide +kernel
  constructor
  · rintro ⟨r,t,l,k,hr,hro,ht,hto,hne,hl,hl2,hk,hk2,H,K⟩
    obtain ⟨h1,h2⟩ := small_repunit_parameters hr hl2 (by omega)
    obtain ⟨h3,h4⟩ := small_repunit_parameters ht hk2 (by omega)
    have hr5 := (screen ⟨r,h1⟩ ⟨l,h2⟩ hr hro hl hl2).1 H
    have ht5 := (screen ⟨t,h3⟩ ⟨k,h4⟩ ht hto hk hk2).1 K
    exact hne (hr5.trans ht5.symm)
  · rintro ⟨r,t,l,k,hr,hro,_,_,_,hl,hl2,_,_,H,_⟩
    obtain ⟨h1,h2⟩ := small_repunit_parameters hr hl2 H.le
    exact (screen ⟨r,h1⟩ ⟨l,h2⟩ hr hro hl hl2).2 H

private theorem source_length {s r p v : ℕ} (hs : Odd s) (hp : p.Prime)
    (hr : r ∈ s.primeFactors) (hout : sigma 1 (r^(2*s.factorization r))=p^v) :
    ∃ n : ℕ, n.Prime ∧ 2<n ∧ geometricBlock r n=p^v := by
  obtain ⟨hrp,hrs,_⟩ := Nat.mem_primeFactors.mp hr
  have he := (hrp.dvd_iff_one_le_factorization hs.pos.ne').mp hrs
  refine ⟨2*s.factorization r+1,prime_length_of_pure_even_component hrp (hs.of_dvd_nat hrs) hp
    (by omega) ⟨s.factorization r,by omega⟩ hout.dvd,by omega,?_⟩
  exact (sigma_one_apply_prime_pow hrp).symm.trans hout

private theorem nontrivial_source {s r p v : ℕ} (hs : Odd s) (hp : p.Prime)
    (hr : r ∈ s.primeFactors) (hvo : Odd v) (hv : v≠1)
    (hout : sigma 1 (r^(2*s.factorization r))=p^v) : IsOddRepunitPowerAt r p := by
  obtain ⟨l,hl,hld⟩ := Nat.exists_prime_and_dvd hv
  obtain ⟨n,hn,hn2,H⟩ := source_length hs hp hr hout
  have hlo := hvo.of_dvd_nat hld
  obtain ⟨c,hc⟩ := hld
  have hcp : 0<c := by
    by_contra! h
    rw [show c=0 by omega,mul_zero] at hc
    have := hvo.pos
    omega
  refine ⟨Nat.prime_of_mem_primeFactors hr,hs.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr),
    hp,n,c,l,hn,hn2,hcp,hl,hlo,?_⟩
  rwa [←pow_mul',←hc]

private theorem repeated_source {s p r t v : ℕ} (hs : Odd s) (hp : p.Prime)
    (hr : r ∈ s.primeFactors) (ht : t ∈ s.primeFactors) (hne : r≠t)
    (h1 : sigma 1 (r^(2*s.factorization r))=p^v)
    (h2 : sigma 1 (t^(2*s.factorization t))=p^v) : HasTwoOddPrimeRepunits (p^v) := by
  obtain ⟨n,hn,hn2,H⟩ := source_length hs hp hr h1
  obtain ⟨k,hk,hk2,K⟩ := source_length hs hp ht h2
  exact ⟨r,t,n,k,Nat.prime_of_mem_primeFactors hr,hs.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr),
    Nat.prime_of_mem_primeFactors ht,hs.of_dvd_nat (Nat.dvd_of_mem_primeFactors ht),hne,hn,hn2,hk,hk2,H,K⟩

/-- Either the index prime is a repunit in two odd prime bases, or all
but at most one cofactor prime give distinct-base Nagell–Ljunggren
witnesses having the same prime support on the right. -/
theorem even_index_multiple_repunit_witnesses {q p s u : ℕ} (hp : p.Prime) (hs : Odd s)
    (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2) (hσs : sigma 1 (s^2)=p^(2*u)) :
    HasTwoOddPrimeRepunits p ∨ ∃ T ⊆ s.primeFactors,
      s.primeFactors.card ≤ T.card+1 ∧ ∀ r ∈ T, IsOddRepunitPowerAt r p := by
  let v (r : ℕ) := (sigma 1 (r^(2*s.factorization r))).factorization p
  obtain ⟨_,hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  let S := s.primeFactors.filter (v · = 1)
  by_cases hsmall : S.card≤1
  · right
    let T := s.primeFactors.filter (fun r => ¬v r=1)
    refine ⟨T,Finset.filter_subset _ _,?_,?_⟩
    · have hc := Finset.card_filter_add_card_filter_not (s:=s.primeFactors) (fun r => v r=1)
      change S.card+T.card=s.primeFactors.card at hc
      omega
    · intro r hr
      obtain ⟨hr,hn⟩ := Finset.mem_filter.mp hr
      obtain ⟨hodd,hout⟩ := hparts r hr
      exact nontrivial_source hs hp hr hodd hn hout
  · left
    obtain ⟨r,hr,t,ht,hne⟩ := Finset.one_lt_card.mp (show 1<S.card by omega)
    obtain ⟨hr,h1⟩ := Finset.mem_filter.mp hr
    obtain ⟨ht,h2⟩ := Finset.mem_filter.mp ht
    have H := (hparts r hr).2
    have K := (hparts t ht).2
    change _=p^(v r) at H
    change _=p^(v t) at K
    rw [h1] at H
    rw [h2] at K
    simpa only [pow_one] using repeated_source hs hp hr ht hne H K

private theorem card_sq_le_sum_of_odd (S : Finset ℕ) (ho : ∀ t ∈ S, Odd t) :
    S.card^2≤∑ t ∈ S,t := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hmax ih =>
    have ha := Nat.odd_iff.mp (ho a (Finset.mem_insert_self ..))
    have hso (t : ℕ) (ht : t ∈ S) := ho t (Finset.mem_insert_of_mem ht)
    have hne : a ∉ S := fun h => (hmax a h).false
    have hinj : Set.InjOn (fun t : ℕ => t/2) S := by
      intro t ht z hz h
      change t/2=z/2 at h
      have := Nat.odd_iff.mp (hso t ht)
      have := Nat.odd_iff.mp (hso z hz)
      omega
    have hsub : S.image (fun t : ℕ => t/2) ⊆ range (a/2) := by
      intro t ht
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ht
      apply Finset.mem_range.mpr
      have := hmax z hz
      have := Nat.odd_iff.mp (hso z hz)
      omega
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj,Finset.card_range] at hc
    have hstep : 2*S.card+1≤a := by omega
    rw [Finset.card_insert_of_notMem hne,Finset.sum_insert hne]
    nlinarith [ih hso]

/-- A larger number of cofactor primes than the square root of the index
exponent forces a repeated odd-base repunit representation of a power of p. -/
theorem even_index_repeated_repunit_or_card_sq_le {q p s u : ℕ} (hp : p.Prime) (hs : Odd s)
    (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2) (hσs : sigma 1 (s^2)=p^(2*u)) :
    (∃ v : ℕ, Odd v ∧ HasTwoOddPrimeRepunits (p^v)) ∨ s.primeFactors.card^2≤2*u := by
  let v (r : ℕ) := (sigma 1 (r^(2*s.factorization r))).factorization p
  obtain ⟨hsum,hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  change ∑ r ∈ s.primeFactors,v r = 2*u at hsum
  by_cases hinj : Set.InjOn v s.primeFactors
  · right
    have H := card_sq_le_sum_of_odd (s.primeFactors.image v) (by
      intro z hz
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hz
      exact (hparts r hr).1)
    rw [Finset.card_image_of_injOn hinj,Finset.sum_image hinj,hsum] at H
    exact H
  · left
    unfold Set.InjOn at hinj
    push Not at hinj
    obtain ⟨r,hr,t,ht,hv,hne⟩ := hinj
    refine ⟨v r,(hparts r hr).1,repeated_source hs hp hr ht hne (hparts r hr).2 ?_⟩
    rw [hv]
    exact (hparts t ht).2

/-- An even prime-power index at any exact component forces either a
Goormaghtigh solution at the index prime or at least three odd-base
Nagell–Ljunggren solutions sharing that prime on the right. -/
theorem even_prime_power_component_repunit_alternatives {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0<a)
    (hform : N=q^a*b) (hqb : ¬q ∣ b) (hl : sigma 1 b=q^a*i)
    (hr : sigma 1 (q^a)*i=2*b) (hp : p.Prime) (hu : 0<u) (hi : i=p^(2*u)) :
    HasTwoOddPrimeRepunits p ∨ ∃ T : Finset ℕ, 3≤T.card ∧ ∀ r ∈ T, IsOddRepunitPowerAt r p := by
  obtain ⟨ha1,hσ⟩ := even_prime_power_index_eq_selected_sigma hN ho hq ha hform hqb hl hr hp hu hi
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b _)
  have hp2 : p≠2 := by
    rintro rfl
    have h4 : 4 ∣ 2*b := hr ▸ hi ▸ (pow_dvd_pow 2 (by omega : 2≤2*u)).trans (dvd_mul_left _ _)
    have := hbo.not_two_dvd_nat
    omega
  have hpo := hp.odd_of_ne_two hp2
  obtain ⟨m,_,_,hqm,rfl⟩ := euler_form_of_odd_component_index hN ho hq ha hform hqb hl hr (hi ▸ hpo.pow)
  have hmo := ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2≠0)) _)
  rw [ha1,pow_one] at hform hl hr
  rw [hi] at hl hr
  obtain ⟨s,hso,hcop,hms,_,hplus,hσs⟩ := even_prime_power_cofactor_split hq hp hmo hpo hu hl hr
  have hn := prime_count_of_even_index_split hq hp hmo hso hu hqm hcop hform hms
  have hmin := five_le_distinct_prime_factor_count ho hN
  have hpar := Nat.even_iff.mp (even_index_cofactor_prime_count hp hso hσ hplus hσs).1
  rcases even_index_multiple_repunit_witnesses hp hso hσ hplus hσs with h|⟨T,_,hc,hT⟩
  · exact Or.inl h
  · exact Or.inr ⟨T,by omega,hT⟩

end OddPerfect
