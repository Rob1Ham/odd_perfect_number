module

public import OddPerfect.PerfectShapes
public import OddPerfect.CandidateSets
public import OddPerfect.SpoofCompletion

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- Ore's integral harmonic mean condition on the true positive divisors.
The trivial value one is excluded, as in Cohen and Sorli. -/
@[expose] def OreHarmonic (N : ℕ) : Prop :=
  1 < N ∧ sigma 1 N ∣ N * N.divisors.card

/-- Pairing a divisor with its complementary divisor calculates the sum of
the reciprocals without assuming that the integer is perfect. -/
theorem sum_reciprocal_divisors {N : ℕ} (hN : 0 < N) :
    (∑ d ∈ N.divisors, (1:ℚ)/d) = (sigma 1 N : ℚ)/N := by
  rw [sigma_one_apply, Nat.cast_sum, Finset.sum_div]
  calc (∑ d ∈ N.divisors, (1:ℚ)/d) = ∑ d ∈ N.divisors, ((N/d:ℕ):ℚ)/N := by
         apply sum_congr rfl
         intro d hd
         have hdpos := Nat.pos_of_mem_divisors hd
         rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) (by exact_mod_cast hdpos.ne' : (d:ℚ)≠0)]
         field_simp
       _ = _ := Nat.sum_div_divisors N (fun d => (d:ℚ)/N)

/-- A positive nonsquare has an even number of divisors. -/
theorem even_card_divisors_of_nonsquare {N : ℕ} (hN : 0 < N) (h : ¬ IsSquare N) :
    Even N.divisors.card := by
  rw [Nat.isSquare_iff_even_factorization] at h
  obtain ⟨p,hbad⟩ := Classical.not_forall.mp h
  have he : ¬Even (N.factorization p) := fun he => hbad (fun _ => he)
  have hemod := Nat.even_iff.not.mp he
  have hmem : p ∈ N.primeFactors := by
    by_contra hn
    have hz : N.factorization p = 0 := Finsupp.notMem_support_iff.mp hn
    simp [hz] at he
  rw [Nat.card_divisors hN.ne',even_iff_two_dvd]
  exact (show 2 ∣ N.factorization p + 1 by omega).trans
    (dvd_prod_of_mem (fun p => N.factorization p+1) hmem)

/-- Ore (1948), pp. 617–618. For any perfect number the harmonic mean
of its positive divisors is exactly half their number and is integral. -/
theorem perfect_oreHarmonic {N : ℕ} (h : N.Perfect) :
    OreHarmonic N ∧ N*N.divisors.card / sigma 1 N = N.divisors.card/2 := by
  have h1 : 1 < N := by
    by_contra! hn
    have he : N=1 := by have := h.2; omega
    subst N
    simp [Nat.Perfect] at h
  obtain ⟨k,hk⟩ := even_card_divisors_of_nonsquare h.2 (perfect_not_square h)
  have hσ := (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul h.2).mp h)
  have hmul : N*N.divisors.card = (2*N)*k := by rw [hk]; ring
  refine ⟨⟨h1,⟨k,by rw [hσ,hmul]⟩⟩,?_⟩
  rw [hmul,hσ,Nat.mul_div_cancel_left _ (Nat.mul_pos (by decide) h.2),hk]
  omega

/-- An odd perfect integer has exactly one factor two in its divisor
count. Its harmonic mean is consequently an odd integer. -/
theorem odd_perfect_divisor_count_mod_four {N : ℕ} (ho : Odd N) (h : N.Perfect) :
    N.divisors.card % 4 = 2 := by
  obtain ⟨q,hq,_,he,hrest⟩ := euler_exponents ho h
  let f := fun p => N.factorization p + 1
  have hrs : Odd (∏ p ∈ N.primeFactors.erase q, f p) := by
    apply prod_induction f Odd (fun _ _ => Odd.mul) odd_one
    intro p hp
    have hh := hrest p (mem_erase.mp hp).1
    dsimp [f]
    exact Nat.odd_iff.mpr (by obtain ⟨t,ht⟩ := hh; omega)
  rw [Nat.card_divisors ho.pos.ne', ← mul_prod_erase N.primeFactors f hq]
  change ((N.factorization q+1) * _) % 4 = 2
  rw [Nat.mul_mod]
  have hf : (N.factorization q+1)%4=2 := by omega
  rw [hf]
  have := Nat.odd_iff.mp hrs
  omega

theorem oddPerfectNumbers_subset_oddOreHarmonic :
    oddPerfectNumbers ⊆ {N : ℕ | Odd N ∧ OreHarmonic N} :=
  fun _ h => ⟨h.1, (perfect_oreHarmonic h.2).1⟩

/-- Ore's obstruction for a positive power of a single prime. -/
theorem prime_pow_not_oreHarmonic {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    ¬ OreHarmonic (p^e) := by
  rintro ⟨_,hd⟩
  rw [← sigma_zero_apply, sigma_zero_apply_prime_pow hp, sigma_one_apply_prime_pow hp] at hd
  have hs := (coprime_power_geometric_sum p e).symm.dvd_of_dvd_mul_left hd
  have hlt : e+1 < ∑ j ∈ range (e+1), p^j := by
    calc e+1 = ∑ _ ∈ range (e+1), 1 := by simp
         _ < _ := sum_lt_sum (fun j _ => Nat.one_le_pow _ _ hp.pos)
           ⟨1,mem_range.mpr (by omega),by simpa using hp.one_lt⟩
  exact hlt.not_ge (Nat.le_of_dvd (by omega) hs)

theorem descartes_not_oreHarmonic : ¬ OreHarmonic 198585576189 := by
  rintro ⟨_,h⟩
  rw [descartes_true_sigma, Nat.card_divisors (by decide : 198585576189 ≠ 0)] at h
  have hτ : (198585576189 : ℕ).primeFactors.prod (fun p => (198585576189 : ℕ).factorization p+1) = 486 := by
    decide +kernel
  rw [hτ] at h
  exact (by decide : ¬426027470778 ∣ 198585576189*486) h

end OddPerfect
