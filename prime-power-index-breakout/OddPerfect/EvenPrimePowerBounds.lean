module

public import OddPerfect.EvenIndexSingleCopy
public import OddPerfect.OddPrimePowerBound
public import OddPerfect.AbundancyLimit
import Mathlib.Algebra.Order.Ring.Abs

public section
namespace OddPerfect
open ArithmeticFunction Finset

private def firstOneModFour : Finset ℕ :=
  (Finset.range 318).filter (fun r => r.Prime ∧ r%4=1)

private theorem oneModFour_bound :
    firstOneModFour.card=31 ∧
      primeAbundancyLimit 19*(∏ r ∈ firstOneModFour,primeAbundancyLimit r)<2 := by
  decide +kernel

private def halfRepunit (p u : ℕ) : ℕ := ((p^(2*u+1)-1)/(p-1)+1)/2

/-- A fixed number of integer Newton steps produces a candidate adjacent
square certificate. The inequalities below verify the candidate exactly. -/
private def rootCandidate (n : ℕ) : ℕ :=
  (fun x : ℕ => min x ((x+n/x)/2))^[12] (2^(n.log2/2+1))

private theorem small_three_mod_four_screen :
    ∀ p : Fin 19, p.val.Prime → p.val%4=3 →
      ∀ u : Fin 32, 0<u.val → (2*u.val+1).Prime →
        let n := halfRepunit p.val u.val
        let x := rootCandidate n
        x^2 < n ∧ n < (x+1)^2 := by
  decide +kernel

/-- A prime-power Euler index at exponent one either has base one modulo
four and exponent divisible by sixteen, or has exponent at least 64. -/
theorem even_index_exponent_alternatives {N q p s u : ℕ}
    (hN : N.Perfect) (hq : q.Prime) (hp : p.Prime) (hpo : Odd p) (hso : Odd s) (hu : 0<u)
    (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2) (hσs : sigma 1 (s^2)=p^(2*u))
    (hform : N=q*(p^u*s)^2) : (p%4=1 ∧ 16 ∣ 2*u) ∨ 64≤2*u := by
  by_cases h1 : p%4=1
  · exact Or.inl ⟨h1,sixteen_dvd_even_index_exponent_of_one_mod_four hp h1 hso hσq hplus⟩
  right
  by_contra! hlim
  have hp3 : p%4=3 := by have := Nat.odd_iff.mp hpo; omega
  have hlen := prime_length_of_prime_sigma hp (by omega : 0<2*u) (hσq ▸ hq)
  have hu60 : 2*u≤60 := by
    have hx : 2*u+1≠63 := fun h => (by decide : ¬Nat.Prime 63) (h ▸ hlen)
    omega
  have hsbound := even_index_three_copy_bound hp hso hσq hplus hσs
  have hdist : (u+1).primeFactors.card≤11 := by
    have hsub : (u+1).primeFactors ⊆ (Finset.range 32).filter Nat.Prime := by
      intro r hr
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
        have := Nat.le_of_dvd (by omega : 0<u+1) (Nat.dvd_of_mem_primeFactors hr)
        omega),Nat.prime_of_mem_primeFactors hr⟩
    exact (Finset.card_le_card hsub).trans (by decide)
  have hbig : 19≤p := by
    by_contra! h
    have hcheck := small_three_mod_four_screen ⟨p,h⟩ hp hp3 ⟨u,by omega⟩ hu hlen
    have hrep : (p^(2*u+1)-1)/(p-1)=q := by
      rw [←hσq,sigma_one_apply_prime_pow hp]
      exact (Nat.eq_div_of_mul_eq_left (by have := hp.one_lt; omega)
        (geom_sum_mul_of_one_le hp.one_le (2*u+1))).symm
    have heq : halfRepunit p u=s^2 := by rw [halfRepunit,hrep,hplus,Nat.mul_div_cancel_left _ (by decide)]
    change (rootCandidate (halfRepunit p u))^2 < halfRepunit p u ∧
      halfRepunit p u < (rootCandidate (halfRepunit p u)+1)^2 at hcheck
    let x := rootCandidate (halfRepunit p u)
    change x^2 < halfRepunit p u ∧ halfRepunit p u < (x+1)^2 at hcheck
    rw [heq] at hcheck
    rcases le_or_gt s x with hle|hlt
    · exact hcheck.1.not_ge (Nat.pow_le_pow_left hle 2)
    · exact hcheck.2.not_ge (Nat.pow_le_pow_left hlt 2)
  have hmem : N.primeFactors={q} ∪ ({p} ∪ s.primeFactors) := by
    rw [hform,Nat.primeFactors_mul hq.ne_zero (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hp.ne_zero) hso.pos.ne')),
      Nat.primeFactors_pow _ (by decide : 2≠0),Nat.primeFactors_mul (pow_ne_zero _ hp.ne_zero) hso.pos.ne',
      Nat.primeFactors_pow p hu.ne',hq.primeFactors,hp.primeFactors]
  have hpN : p ∈ N.primeFactors := by simp [hmem]
  have H (r : ℕ) (hr : r ∈ N.primeFactors.erase p) : r ∈ insert q s.primeFactors := by
    obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hr
    simpa [hmem,hne] using hm
  have hcard : (N.primeFactors.erase p).card≤firstOneModFour.card := by
    have := Finset.card_le_card (show N.primeFactors.erase p ⊆ insert q s.primeFactors from fun r hr => H r hr)
    have := Finset.card_insert_le q s.primeFactors
    rw [oneModFour_bound.1]
    omega
  have hq16 := one_mod_sixteen_of_twice_odd_square hso hplus
  have hbound := prod_primeAbundancyLimit_le_of_cut (b:=317) (by decide) (N.primeFactors.erase p) firstOneModFour
    hcard (by
      intro r hr
      obtain ⟨hin,hout⟩ := Finset.mem_sdiff.mp hr
      have hprime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hin)
      have hres : r%4=1 := by
        rcases Finset.mem_insert.mp (H _ hin) with rfl|hsr
        · omega
        · exact even_index_sources_one_mod_four hp hp3 hso hσq hplus hσs hsr
      by_contra! ht
      exact hout (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hprime,hres⟩))
    (by
      intro r hr
      obtain ⟨hh,hprime,_⟩ := Finset.mem_filter.mp (Finset.mem_sdiff.mp hr).1
      exact ⟨hprime.one_lt,by have := Finset.mem_range.mp hh; omega⟩)
  have hple := primeAbundancyLimit_antitone (by decide : 1<19) hbig
  have hnonneg (r : ℕ) : 0≤primeAbundancyLimit r :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hfinal := mul_le_mul hple hbound (Finset.prod_nonneg (fun r _ => hnonneg r)) (hnonneg _)
  rw [Finset.mul_prod_erase _ _ hpN] at hfinal
  exact (two_lt_prod_primeAbundancyLimit hN).not_ge (hfinal.trans oneModFour_bound.2.le)

/-- For every exact component of an odd perfect number, a prime-power
index has exponent 16 or at least 66. The only unexcluded exponent below
66 is an even power with base one modulo four. -/
theorem component_prime_power_index_exponent {N q a b i p j : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0<a)
    (hform : N=q^a*b) (hqb : ¬q ∣ b) (hl : sigma 1 b=q^a*i)
    (hr : sigma 1 (q^a)*i=2*b) (hp : p.Prime) (hj : 0<j) (hi : i=p^j) :
    (j=16 ∧ p%4=1) ∨ 66≤j := by
  by_cases hb : 66≤j
  · exact Or.inr hb
  have he : Even j := (Nat.even_or_odd j).resolve_right (fun h =>
    component_index_ne_small_odd_prime_power hN ho hq ha hform hqb hl hr hp h (by omega) hi)
  obtain ⟨u,hu'⟩ := he
  have hj2 : j=2*u := by omega
  have hu : 0<u := by omega
  rw [hj2] at hi
  obtain ⟨ha1,hσq⟩ := even_prime_power_index_eq_selected_sigma hN ho hq ha hform hqb hl hr hp hu hi
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b (q^a))
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
  obtain ⟨s,hso,_,hms,_,hplus,hσs⟩ := even_prime_power_cofactor_split hq hp hmo hpo hu hl hr
  have hlen := prime_length_of_prime_sigma hp (by omega : 0<2*u) (hσq ▸ hq)
  have h16 : 16 ∣ j ∨ 64≤j := by
    rcases even_index_exponent_alternatives hN hq hp hpo hso hu hσq hplus hσs (hms ▸ hform) with h|h
    · exact Or.inl (hj2 ▸ h.2)
    · exact Or.inr (by omega)
  have hcut : ∀ v : Fin 66, 0<v.val → Even v.val → (v.val+1).Prime →
      (16 ∣ v.val ∨ 64≤v.val) → v.val=16 := by decide +kernel
  have heven : Even j := ⟨u,by omega⟩
  have hjprime : (j+1).Prime := hj2 ▸ hlen
  have hj16 := hcut ⟨j,by omega⟩ hj heven hjprime h16
  change j=16 at hj16
  have hselected := even_index_exponent_alternatives hN hq hp hpo hso hu hσq hplus hσs (hms ▸ hform)
  exact Or.inl ⟨hj16,(hselected.resolve_right (by omega)).1⟩

end OddPerfect
