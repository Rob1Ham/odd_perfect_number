module

public import OddPerfect.FermatIndexNonspecial
import Mathlib.Algebra.Order.Ring.Abs

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- Prime divisors whose predecessor has an odd prime divisor. -/
@[expose] def nonFermatIndexPrimes (i : ℕ) : Finset ℕ :=
  i.primeFactors.filter (fun p => ((p-1).primeFactors.erase 2).Nonempty)

private theorem odd_factor_of_twice_odd {d n : ℕ} (hd : Odd d) (hn : n ∣ 2*d)
    (hn1 : n≠1) (hn2 : n≠2) : ∃ l : ℕ, l.Prime ∧ Odd l ∧ l ∣ n := by
  rcases Nat.even_or_odd n with ⟨t,ht⟩|ho
  · have hn' : n=2*t := by omega
    have htd := Nat.dvd_of_mul_dvd_mul_left (by decide : 0<2) (show 2*t∣2*d from hn' ▸ hn)
    obtain ⟨l,hl,hlt⟩ := Nat.exists_prime_and_dvd (by omega : t≠1)
    exact ⟨l,hl,hd.of_dvd_nat (hlt.trans htd),hn' ▸ hlt.trans (dvd_mul_left _ _)⟩
  · obtain ⟨l,hl,hln⟩ := Nat.exists_prime_and_dvd hn1
    exact ⟨l,hl,ho.of_dvd_nat hln,hln⟩

private theorem order_with_odd_prime_target {r e q a i n l : ℕ} (hr : r.Prime) (hro : Odd r)
    (hq : q.Prime) (hi : i≠0) (hout : sigma 1 (r^e) ∣ q^a*i)
    (hn : n ∣ e+1) (hl : l.Prime) (hlo : Odd l) (hln : l ∣ n) :
    ∃ p ∈ insert q (nonFermatIndexPrimes i), orderOf (r:ZMod p)=n := by
  have hnpos : 0<n := Nat.pos_of_dvd_of_pos hn (by omega)
  have hn2 : 1<n := hl.one_lt.trans_le (Nat.le_of_dvd hnpos hln)
  have primitive : ∃ p : ℕ, p.Prime ∧ orderOf (r:ZMod p)=n ∧ n ∣ p-1 := by
    by_cases hpp : IsPrimePow n
    · obtain ⟨s,k,hsp,hsk⟩ := (isPrimePow_iff_pow_succ n).mp hpp
      have hs := Nat.prime_iff.mpr hsp
      have hls := (Nat.prime_dvd_prime_iff_eq hl hs).mp (hl.dvd_of_dvd_pow (hsk ▸ hln))
      subst s
      simpa [←hsk] using exists_prime_order_prime_pow hr.one_lt hl hlo k
    · exact exists_prime_order_mixed (by have := hr.two_le; have := Nat.odd_iff.mp hro; omega) hn2 hpp
  obtain ⟨p,hp,hord,hdiv⟩ := primitive
  have hne : (r:ZMod p)≠1 := by intro h; rw [h,orderOf_one] at hord; omega
  have hσ : p ∣ sigma 1 (r^e) := by
    rw [sigma_one_apply,dvd_sum_divisors_prime_pow_iff hr hp]
    simpa [hne,hord] using hn
  refine ⟨p,?_,hord⟩
  rcases hp.dvd_mul.mp (hσ.trans hout) with h|h
  · exact Finset.mem_insert.mpr (.inl ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h)))
  · apply Finset.mem_insert_of_mem
    refine Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp,h,hi⟩,l,Finset.mem_erase.mpr ⟨?_,?_⟩⟩
    · intro h
      exact hlo.not_two_dvd_nat (h ▸ dvd_rfl)
    · exact Nat.mem_primeFactors.mpr ⟨hl,hln.trans hdiv,by have := hp.one_lt; omega⟩

/-- All divisors of the Euler component's length other than one and two
have distinct non-Fermat order witnesses. At most one can be the selected
target q instead of a divisor of its index. -/
theorem euler_length_divisors_le_nonfermat_targets {r e q a i : ℕ} (hr : r.Prime) (hro : Odd r)
    (he : e%4=1) (hq : q.Prime) (hi : i≠0) (hout : sigma 1 (r^e) ∣ q^a*i) :
    2*((e+1)/2).divisors.card ≤ (nonFermatIndexPrimes i).card+3 := by
  let d := (e+1)/2
  let D := (e+1).divisors
  let S := (D.erase 1).erase 2
  let T := insert q (nonFermatIndexPrimes i)
  have hdo : Odd d := Nat.odd_iff.mpr (by dsimp [d]; omega)
  have hd2 : e+1=2*d := by dsimp [d]; omega
  have hsub : S ⊆ T.image (fun p => orderOf (r:ZMod p)) := by
    intro n hn
    obtain ⟨hn2,hn⟩ := Finset.mem_erase.mp hn
    obtain ⟨hn1,hn⟩ := Finset.mem_erase.mp hn
    have hd := Nat.dvd_of_mem_divisors hn
    obtain ⟨l,hl,hlo,hln⟩ := odd_factor_of_twice_odd hdo (hd2 ▸ hd) hn1 hn2
    obtain ⟨p,hp,hh⟩ := order_with_odd_prime_target hr hro hq hi hout hd hl hlo hln
    exact Finset.mem_image.mpr ⟨p,hp,hh⟩
  have hs := (Finset.card_le_card hsub).trans Finset.card_image_le
  have ht := Finset.card_insert_le q (nonFermatIndexPrimes i)
  have h1 : 1 ∈ D := Nat.one_mem_divisors.mpr (by omega)
  have h2 : 2 ∈ D.erase 1 := Finset.mem_erase.mpr ⟨by decide,Nat.mem_divisors.mpr
    ⟨hd2 ▸ dvd_mul_right _ _,by omega⟩⟩
  have hc := Finset.card_erase_add_one h1
  have hc' := Finset.card_erase_add_one h2
  have hD : D.card=2*d.divisors.card := by
    dsimp only [D]
    rw [hd2,Nat.Coprime.card_divisors_mul hdo.coprime_two_left,show (2:ℕ).divisors.card=2 by decide]
  change S.card≤(insert q (nonFermatIndexPrimes i)).card at hs
  change S.card+1=(D.erase 1).card at hc'
  change 2*d.divisors.card≤_
  omega

/-- At an exact component distinct from the Euler prime, the divisor
count of the Euler half-length bounds the number of non-Fermat index
primes. The bound holds independently of the selected exponent. -/
theorem nonspecial_index_nonfermat_prime_count {N q a b i r : ℕ}
    (ho : Odd N) (hq : q.Prime) (hform : N=q^a*b)
    (hl : sigma 1 b=q^a*i) (hrN : r ∈ N.primeFactors) (hrq : r≠q)
    (he : N.factorization r%4=1) :
    2*((N.factorization r+1)/2).divisors.card ≤ (nonFermatIndexPrimes i).card+3 := by
  obtain ⟨hr,hrd,_⟩ := Nat.mem_primeFactors.mp hrN
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b _)
  have hn : ¬r∣q^a := fun h => hrq ((Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow h))
  have hrd' := (hr.dvd_mul.mp (hform ▸ hrd)).resolve_left hn
  have hrb := Nat.mem_primeFactors.mpr ⟨hr,hrd',hbo.pos.ne'⟩
  have hv : N.factorization r=b.factorization r := by
    rw [hform,Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) hbo.pos.ne',Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hn,zero_add]
  have hout : sigma 1 (r^N.factorization r) ∣ q^a*i := by
    rw [hv,←hl,(isMultiplicative_sigma (k:=1)).multiplicative_factorization _ hbo.pos.ne']
    exact Finset.dvd_prod_of_mem _ hrb
  have hi : i≠0 := by
    rintro rfl
    simp only [mul_zero] at hl
    exact (sigma_pos 1 b hbo.pos.ne').ne' hl
  exact euler_length_divisors_le_nonfermat_targets hr (ho.of_dvd_nat hrd) he hq hi hout

/-- Above Euler exponent one, every exact component index, including
an even index at a nonspecial component, contains a non-Fermat prime. -/
theorem exists_nonfermat_index_prime_of_large_euler_exponent {N q a b i r : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0<a)
    (hform : N=q^a*b) (hqb : ¬q ∣ b) (hl : sigma 1 b=q^a*i)
    (hr : sigma 1 (q^a)*i=2*b) (hrN : r ∈ N.primeFactors)
    (he : N.factorization r%4=1) (hgt : 1<N.factorization r) :
    ∃ p ∈ i.primeFactors, ∀ k : ℕ, p-1≠2^k := by
  rcases eq_or_ne r q with heq|hrq
  · subst r
    have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b _)
    have hv : N.factorization q=a := by
      rw [hform,Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) hbo.pos.ne',Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hqb,hq.factorization_pow,Finsupp.single_eq_same,add_zero]
    have hio := ((component_index_parity_bound hN ho hq ha hform hqb hl hr).resolve_right (by
      rintro ⟨heven,_,_⟩
      have := Nat.even_iff.mp heven
      omega)).2.1
    exact exists_nonfermat_prime_of_odd_component_index hN ho hq ha hform hqb hl hr hio
  · let d := (N.factorization r+1)/2
    have hd : 1<d := by dsimp [d]; omega
    have hcard : 1<d.divisors.card := Finset.one_lt_card.mpr
      ⟨1,Nat.one_mem_divisors.mpr (by omega),d,Nat.mem_divisors.mpr ⟨dvd_rfl,by omega⟩,by omega⟩
    have hc := nonspecial_index_nonfermat_prime_count ho hq hform hl hrN hrq he
    change 2*d.divisors.card≤_ at hc
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0<(nonFermatIndexPrimes i).card)
    obtain ⟨hpI,l,hl⟩ := Finset.mem_filter.mp hp
    obtain ⟨hl2,hlp⟩ := Finset.mem_erase.mp hl
    refine ⟨p,hpI,?_⟩
    intro k hk
    have hdv := Nat.dvd_of_mem_primeFactors hlp
    rw [hk] at hdv
    exact hl2 ((Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hlp) Nat.prime_two).mp
      ((Nat.prime_of_mem_primeFactors hlp).dvd_of_dvd_pow hdv))

end OddPerfect
