module

public import OddPerfect.EvenIndexSmallBase
import Mathlib.Algebra.Order.Ring.Abs

public section
namespace OddPerfect
open ArithmeticFunction Finset

theorem even_index_prime_support {N q p s u : ℕ} (hq : q.Prime) (hp : p.Prime)
    (hs : Odd s) (hu : 0<u) (hform : N=q*(p^u*s)^2) :
    N.primeFactors={q} ∪ ({p} ∪ s.primeFactors) := by
  rw [hform,Nat.primeFactors_mul hq.ne_zero (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hp.ne_zero) hs.pos.ne')),
    Nat.primeFactors_pow _ (by decide : 2≠0),Nat.primeFactors_mul (pow_ne_zero _ hp.ne_zero) hs.pos.ne',
    Nat.primeFactors_pow p hu.ne',hq.primeFactors,hp.primeFactors]

private def oneModFourCandidates (t : ℕ) : Finset ℕ :=
  (Finset.range 1118).filter (fun r => r.Prime ∧ r%4=1 ∧ r≠t)

private def oneModFourSample : Finset ℕ :=
  ⟨([5, 13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101, 109, 113, 137, 149, 157,
    173, 181, 193, 197, 229, 233, 241, 257, 269, 277, 281, 293, 313, 317, 337,
    349, 353, 373, 389, 397, 401, 409, 421, 433, 449, 457, 461, 509, 521, 541,
    557, 569, 577, 593, 601, 613, 617, 641, 653, 661, 673, 677, 701, 709, 733,
    757, 761, 769, 773, 797, 809, 821, 829, 853, 857, 877, 881, 929, 937, 941,
    953, 977, 997, 1009, 1013, 1021, 1033, 1049, 1061, 1069, 1093, 1097, 1109,
    1117] : List ℕ), by decide +kernel⟩

private def oneModFourCovers : Bool :=
  (List.range 1118).all fun p => decide (p % 4 ≠ 1) || decide (p < 2) ||
    [2,3,5,7,11,13,17,19,23,29,31].any (fun q => decide (1 < q ∧ q < p ∧ p % q = 0)) ||
    decide (p ∈ oneModFourSample)

private theorem oneModFourCovers_ok : oneModFourCovers = true := by decide +kernel

private theorem oneModFourSample_spec :
    ∀ p ∈ oneModFourSample, p < 1118 ∧ p.Prime ∧ p % 4 = 1 := by decide +kernel

private theorem oneModFourCandidates_eq (t : ℕ) :
    oneModFourCandidates t = oneModFourSample.erase t := by
  ext p
  simp only [oneModFourCandidates, Finset.mem_filter, Finset.mem_range, Finset.mem_erase, ne_eq]
  constructor
  · rintro ⟨hlt, hp, hm, hne⟩
    refine ⟨hne, ?_⟩
    have hh := List.all_eq_true.mp oneModFourCovers_ok p (List.mem_range.mpr hlt)
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hh
    rcases hh with ((h1 | h2) | ⟨q, _, hq, hqp, hd⟩) | hs
    · exact (h1 hm).elim
    · have := hp.two_le; omega
    · rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero hd) with h | h <;> omega
    · exact hs
  · rintro ⟨hne, hs⟩
    obtain ⟨hlt, hp, hm⟩ := oneModFourSample_spec p hs
    exact ⟨hlt, hp, hm, hne⟩

private theorem oneModFour_nat_ok {t : ℕ} (h : t = 5 ∨ t = 13 ∨ t = 17) :
    (oneModFourSample.erase t).card = 90 ∧
      61 * (∏ r ∈ oneModFourSample.erase t, r) <
        2 * 60 * (∏ r ∈ oneModFourSample.erase t, (r - 1)) := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

private theorem oneModFour_values {t : ℕ} (h : t=5 ∨ t=13 ∨ t=17) :
    (oneModFourCandidates t).card=90 ∧
      primeAbundancyLimit 61*(∏ r ∈ oneModFourCandidates t,primeAbundancyLimit r)<2 := by
  rw [oneModFourCandidates_eq]
  obtain ⟨hcard, hnat⟩ := oneModFour_nat_ok h
  refine ⟨hcard, ?_⟩
  have hden : 0 < ∏ r ∈ oneModFourSample.erase t, (r - 1) :=
    Finset.prod_pos fun r hr => Nat.sub_pos_of_lt
      (oneModFourSample_spec r (Finset.mem_of_mem_erase hr)).2.1.one_lt
  simp only [primeAbundancyLimit, Finset.prod_div_distrib, ← Nat.cast_prod]
  rw [show ((61 : ℕ) : ℚ) / ((61 - 1 : ℕ) : ℚ) = (61 : ℚ) / (60 : ℚ) by norm_num, div_mul_div_comm]
  rw [div_lt_iff₀ (mul_pos (by norm_num : (0 : ℚ) < 60) (by exact_mod_cast hden))]
  simpa only [Nat.cast_prod, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using
    (Nat.cast_lt (α := ℚ)).mpr hnat

private theorem missing_short_order_source {q p s u : ℕ} (hp : p.Prime) (hs : Odd s)
    (hcut : 2*u<256) (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2)
    (hσs : sigma 1 (s^2)=p^(2*u)) : ∃ t, (t=5 ∨ t=13 ∨ t=17) ∧ t ∉ s.primeFactors := by
  have H (r : ℕ) (hr : r ∈ s.primeFactors) (h3 : r≠3) (h48 : r-1 ∣ 48) : r ∣ u+1 := by
    obtain ⟨hb,hout⟩ := (even_index_source_valuation_budget hp hs hσq hplus hσs).2 r hr
    have hd := Nat.dvd_of_mem_primeFactors hr
    exact low_order_source_dvd hp (Nat.prime_of_mem_primeFactors hr) (hs.of_dvd_nat hd) h3 h48 hd hb hσq hplus hout
  by_cases h5 : 5 ∈ s.primeFactors
  · by_cases h13 : 13 ∈ s.primeFactors
    · by_cases h17 : 17 ∈ s.primeFactors
      · have d5 := H 5 h5 (by decide) (by decide)
        have d13 := H 13 h13 (by decide) (by decide)
        have d17 := H 17 h17 (by decide) (by decide)
        have d65 := (by decide : Nat.Coprime 5 13).mul_dvd_of_dvd_of_dvd d5 d13
        have d1105 := (by decide : Nat.Coprime (5*13) 17).mul_dvd_of_dvd_of_dvd d65 d17
        have := Nat.le_of_dvd (by omega : 0<u+1) d1105
        omega
      · exact ⟨17,.inr (.inr rfl),h17⟩
    · exact ⟨13,.inr (.inl rfl),h13⟩
  · exact ⟨5,.inl rfl,h5⟩

/-- The limited number of available primes 1 modulo 4 makes the
support deficient below exponent 256 when the index prime is 3 modulo 4. -/
theorem even_index_exponent_ge_256_of_three_mod_four {N q p s u : ℕ}
    (hN : N.Perfect) (hq : q.Prime) (hp : p.Prime) (hpo : Odd p) (hp3 : p%4=3)
    (hs : Odd s) (hu : 0<u) (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2)
    (hσs : sigma 1 (s^2)=p^(2*u)) (hform : N=q*(p^u*s)^2) : 256≤2*u := by
  by_contra! hcut
  have hbig := sixty_one_le_small_even_index_base hp hpo hq hu hcut (.inl hp3) hσq hplus
  obtain ⟨t,ht,hts⟩ := missing_short_order_source hp hs hcut hσq hplus hσs
  have hqbig : p≤q := by
    have h := self_lt_sigma_of_one_lt (one_lt_pow₀ hp.one_lt (by omega : 2*u≠0))
    rw [hσq] at h
    exact (Nat.le_self_pow (by omega : 2*u≠0) p).trans h.le
  have hmem := even_index_prime_support hq hp hs hu hform
  have hpN : p ∈ N.primeFactors := by simp [hmem]
  have H (r : ℕ) (hr : r ∈ N.primeFactors.erase p) : r ∈ insert q s.primeFactors := by
    obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hr
    simpa [hmem,hne] using hm
  have hcard : (N.primeFactors.erase p).card≤(oneModFourCandidates t).card := by
    have := Finset.card_le_card (show N.primeFactors.erase p ⊆ insert q s.primeFactors from fun r hr => H r hr)
    have := Finset.card_insert_le q s.primeFactors
    have := even_index_three_copy_bound hp hs hσq hplus hσs
    have check : ∀ z : Fin 128, (z.val+1).primeFactors.card≤3 := by decide +kernel
    have hω : (u+1).primeFactors.card≤3 := check ⟨u,by omega⟩
    rw [(oneModFour_values ht).1]
    omega
  have hq16 := one_mod_sixteen_of_twice_odd_square hs hplus
  have hbound := prod_primeAbundancyLimit_le_of_cut (b:=1117) (by decide) (N.primeFactors.erase p) (oneModFourCandidates t)
    hcard (by
      intro r hr
      obtain ⟨hin,hout⟩ := Finset.mem_sdiff.mp hr
      have hprime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hin)
      have hdata : r%4=1 ∧ r≠t := by
        rcases Finset.mem_insert.mp (H _ hin) with heq|hsr
        · omega
        · exact ⟨even_index_sources_one_mod_four hp hp3 hs hσq hplus hσs hsr,fun h => hts (h ▸ hsr)⟩
      by_contra! small
      exact hout (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hprime,hdata⟩))
    (by
      intro r hr
      obtain ⟨hh,hprime,_⟩ := Finset.mem_filter.mp (Finset.mem_sdiff.mp hr).1
      exact ⟨hprime.one_lt,by have := Finset.mem_range.mp hh; omega⟩)
  have hple := primeAbundancyLimit_antitone (by decide : 1<61) hbig
  have hnonneg (r : ℕ) : 0≤primeAbundancyLimit r := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hfinal := mul_le_mul hple hbound (Finset.prod_nonneg (fun r _ => hnonneg r)) (hnonneg _)
  rw [Finset.mul_prod_erase _ _ hpN] at hfinal
  exact (two_lt_prod_primeAbundancyLimit hN).not_ge (hfinal.trans (oneModFour_values ht).2.le)

end OddPerfect
