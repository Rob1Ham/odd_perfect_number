module

public import OddPerfect.Euler
public import OddPerfect.SixthPowerFreeEuler
public import OddPerfect.SixthPowerFreeQuarticCollisionPinch
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
public import Mathlib.Data.Nat.Factorization.Divisors
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Cyclotomic Irreducibility and Zeta Divisor Laws (`OddPerfect.CyclotomicIrreducibleAndZetaDivisorLaws`)

Formalizes:
1. `odd_perfect_zeta_divisor_and_lattice_laws`: Zeta-identity divisor sum `(ζ * id) N = 2 * N`,
   factorization-lattice description of `N.properDivisors`, exact cardinality relation
   `(Finset.Iio N.factorization).card = N.divisors.card - 1`, and `mod 4` congruence laws.
2. `sixth_power_free_divisor_count_mod_eight_iff`: Exact `mod 8` divisor-count dichotomy
   (`2` vs `6`) governed by the parity of `(squareSources N).card` in the sixth-power-free case.
3. `odd_perfect_component_cyclotomic_irreducible_and_coprime`: Irreducibility over `ℤ` and `ℚ`,
   and pairwise coprimality over `ℚ`, of cyclotomic factors of component lengths `e + 1`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma sixth_power_free_partition_invariants {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    N.factorization q = 1 ∧
    (∀ s ∈ squareSources N, N.factorization s = 2) ∧
    (∀ u ∈ largeSources N q, N.factorization u = 4) ∧
    N.primeFactors = insert q (squareSources N ∪ largeSources N q) ∧
    q ∉ squareSources N ∪ largeSources N q ∧
    Disjoint (squareSources N) (largeSources N q) := by
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have hq1 : N.factorization q = 1 := sixth_power_free_euler_exponent_one ho hN hq he hfree
  have hsq2 : ∀ s ∈ squareSources N, N.factorization s = 2 := fun s hs =>
    (Finset.mem_filter.mp hs).2.2
  have hlg4 : ∀ u ∈ largeSources N q, N.factorization u = 4 :=
    (three_free_sixthPowerFree_forces_147_largeSources ho hN hq hq4 he hev h3 hfree).1
  have hparts : N.primeFactors = insert q (squareSources N ∪ largeSources N q) := by
    ext r
    simp only [Finset.mem_insert, Finset.mem_union, squareSources, largeSources, Finset.mem_filter]
    constructor
    · intro hr
      by_cases hrq : r = q
      · exact Or.inl hrq
      · right
        have hr_prime := Nat.prime_of_mem_primeFactors hr
        have hr3 : r ≠ 3 := fun h => h3 (h ▸ Nat.dvd_of_mem_primeFactors hr)
        have hr_pos : 0 < N.factorization r := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
        have hr_lt6 : ¬ 6 ≤ N.factorization r := fun hge =>
          hfree r hr_prime ((hr_prime.pow_dvd_iff_le_factorization hN.2.ne').2 hge)
        obtain ⟨k, hk⟩ := hev r hrq
        by_cases htwo : N.factorization r = 2
        · exact Or.inl ⟨hr, hr3, htwo⟩
        · exact Or.inr ⟨hr, hr3, hrq, by omega⟩
    · rintro (rfl | ⟨hr, _, _⟩ | ⟨hr, _, _, _⟩) <;> assumption
  have hq_notin : q ∉ squareSources N ∪ largeSources N q := by
    intro hmem
    rcases Finset.mem_union.mp hmem with hsq | hlg
    · have := (Finset.mem_filter.mp hsq).2.2
      omega
    · exact (Finset.mem_filter.mp hlg).2.2.1 rfl
  have hdisj : Disjoint (squareSources N) (largeSources N q) := by
    apply Finset.disjoint_left.mpr
    intro r hs hl
    have htwo := (Finset.mem_filter.mp hs).2.2
    have hlarge := (Finset.mem_filter.mp hl).2.2.2
    omega
  exact ⟨hq1, hsq2, hlg4, hparts, hq_notin, hdisj⟩

private lemma prod_odd_of_forall_odd {α : Type*} (s : Finset α) (f : α → ℕ)
    (hf : ∀ x ∈ s, Odd (f x)) : Odd (∏ x ∈ s, f x) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul
      (ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)))

private lemma pow_five_mod_four (k : ℕ) : 5 ^ k % 4 = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod, ih]

private lemma pow_three_mod_four_of_even {c : ℕ} (hc : Even c) : 3 ^ c % 4 = 1 := by
  obtain ⟨k, rfl⟩ := hc
  rw [← two_mul, pow_mul]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    norm_num

private lemma pow_three_mod_four_of_odd {c : ℕ} (hc : Odd c) : 3 ^ c % 4 = 3 := by
  obtain ⟨k, rfl⟩ := hc
  rw [pow_succ, Nat.mul_mod, pow_three_mod_four_of_even (even_two_mul k)]

/-- **1. Odd Perfect Zeta, Divisor-Count, and Factorization-Lattice Laws**:
Establishes `(ζ * id) N = 2 * N`, the `Iio N.factorization` image representation of
`N.properDivisors`, `(Finset.Iio N.factorization).card = N.divisors.card - 1`, and
`mod 4` divisor-count congruences. -/
theorem odd_perfect_zeta_divisor_and_lattice_laws {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    (ArithmeticFunction.zeta * ArithmeticFunction.id) N = 2 * N ∧
    N.properDivisors = (Finset.Iio N.factorization).image (·.prod (· ^ ·)) ∧
    (Finset.Iio N.factorization).card = N.divisors.card - 1 ∧
    N.divisors.card % 4 = 2 ∧
    N.properDivisors.card % 4 = 1 ∧
    (Finset.Iio N.factorization).card % 4 = 1 := by
  have hzeta : (ArithmeticFunction.zeta * ArithmeticFunction.id) N = 2 * N := by
    rw [ArithmeticFunction.zeta_mul_apply]
    simp only [ArithmeticFunction.id_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN
  have himg : N.properDivisors = (Finset.Iio N.factorization).image (·.prod (· ^ ·)) :=
    Nat.properDivisors_eq_image_Iio_factorization_prod_pow
  have hcard_iio : (Finset.Iio N.factorization).card = N.properDivisors.card := by
    have hmap := congrArg Finset.card
      (Nat.properDivisors_eq_map_attach_Iio_factorization_prod_pow (n := N))
    rw [Finset.card_map, Finset.card_attach] at hmap
    exact hmap.symm
  have hcard_prop : N.properDivisors.card = N.divisors.card - 1 := by
    have hins := congrArg Finset.card (Nat.insert_self_properDivisors hN.2.ne')
    have hnotmem : N ∉ N.properDivisors := fun h =>
      Nat.lt_irrefl N (Nat.mem_properDivisors.mp h).2
    rw [Finset.card_insert_of_notMem hnotmem] at hins
    omega
  have hcard_eq : (Finset.Iio N.factorization).card = N.divisors.card - 1 :=
    hcard_iio.trans hcard_prop
  have hdiv4 : N.divisors.card % 4 = 2 := by
    obtain ⟨q, hq, _, he4, hev⟩ := euler_exponents ho hN
    rw [Nat.card_divisors hN.2.ne', ← Finset.mul_prod_erase N.primeFactors _ hq]
    have hodd : Odd (∏ p ∈ N.primeFactors.erase q, (N.factorization p + 1)) := by
      apply prod_odd_of_forall_odd
      intro p hp
      obtain ⟨k, hk⟩ := hev p (Finset.mem_erase.mp hp).1
      rw [hk, ← two_mul]
      exact ⟨k, rfl⟩
    obtain ⟨m, hm⟩ := hodd
    have hq_mod : (N.factorization q + 1) % 4 = 2 := by omega
    rw [hm, Nat.mul_mod, hq_mod]
    have : (2 * ((2 * m + 1) % 4)) % 4 = 2 := by omega
    exact this
  have hprop4 : N.properDivisors.card % 4 = 1 := by omega
  have hiio4 : (Finset.Iio N.factorization).card % 4 = 1 := by omega
  exact ⟨hzeta, himg, hcard_eq, hdiv4, hprop4, hiio4⟩

/-- **2. Sixth-Power-Free Divisor Count Modulo 8**:
In the sixth-power-free case, `N.divisors.card % 8` is either `2` (iff `(squareSources N).card`
is even) or `6` (iff `(squareSources N).card` is odd). -/
theorem sixth_power_free_divisor_count_mod_eight_iff {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    (N.divisors.card % 8 = 2 ∨ N.divisors.card % 8 = 6) ∧
    (N.divisors.card % 8 = 2 ↔ Even (squareSources N).card) ∧
    (N.divisors.card % 8 = 6 ↔ Odd (squareSources N).card) := by
  obtain ⟨hq1, hsq2, hlg4, hparts, hq_notin, hdisj⟩ :=
    sixth_power_free_partition_invariants ho hN hq hq4 he hev hfree
  have hcard : N.divisors.card =
      2 * (3 ^ (squareSources N).card * 5 ^ (largeSources N q).card) := by
    rw [Nat.card_divisors hN.2.ne', hparts, Finset.prod_insert hq_notin,
      Finset.prod_union hdisj, hq1]
    have hprod_sq : (∏ s ∈ squareSources N, (N.factorization s + 1)) =
        3 ^ (squareSources N).card := by
      calc
        ∏ s ∈ squareSources N, (N.factorization s + 1)
          = ∏ _s ∈ squareSources N, 3 :=
            Finset.prod_congr rfl (fun s hs => by rw [hsq2 s hs])
        _ = 3 ^ (squareSources N).card := Finset.prod_const 3
    have hprod_lg : (∏ u ∈ largeSources N q, (N.factorization u + 1)) =
        5 ^ (largeSources N q).card := by
      calc
        ∏ u ∈ largeSources N q, (N.factorization u + 1)
          = ∏ _u ∈ largeSources N q, 5 :=
            Finset.prod_congr rfl (fun u hu => by rw [hlg4 u hu])
        _ = 5 ^ (largeSources N q).card := Finset.prod_const 5
    rw [hprod_sq, hprod_lg]
  set c := (squareSources N).card
  set k := (largeSources N q).card
  have h5 : 5 ^ k % 4 = 1 := pow_five_mod_four k
  have hmod2 : Even c → N.divisors.card % 8 = 2 := by
    intro hc
    have h3 : 3 ^ c % 4 = 1 := pow_three_mod_four_of_even hc
    have hprod4 : (3 ^ c * 5 ^ k) % 4 = 1 := by
      rw [Nat.mul_mod, h3, h5]
    rw [hcard]
    omega
  have hmod6 : Odd c → N.divisors.card % 8 = 6 := by
    intro hc
    have h3 : 3 ^ c % 4 = 3 := pow_three_mod_four_of_odd hc
    have hprod4 : (3 ^ c * 5 ^ k) % 4 = 3 := by
      rw [Nat.mul_mod, h3, h5]
    rw [hcard]
    omega
  rcases Nat.even_or_odd c with hc | hc
  · have hm := hmod2 hc
    refine ⟨Or.inl hm, ⟨fun _ => hc, fun _ => hm⟩, ⟨fun h => by omega, fun ho' => ?_⟩⟩
    exact absurd (Nat.not_odd_iff_even.mpr hc) (fun _ => absurd ho' (Nat.not_odd_iff_even.mpr hc))
  · have hm := hmod6 hc
    refine ⟨Or.inr hm, ⟨fun h => by omega, fun he' => ?_⟩, ⟨fun _ => hc, fun _ => hm⟩⟩
    exact absurd he' (Nat.not_even_iff_odd.mpr hc)

/-- **3. Cyclotomic Irreducibility and Pairwise Coprimality for Component Lengths**:
Every divisor `d` of `N.factorization p + 1` gives irreducible cyclotomic polynomials `Φ_d`
over both `ℤ` and `ℚ`, and distinct divisors give coprime cyclotomic polynomials over `ℚ`. -/
theorem odd_perfect_component_cyclotomic_irreducible_and_coprime {N : ℕ}
    (_ho : Odd N) (_hN : N.Perfect) {p : ℕ} (_hp : p ∈ N.primeFactors) :
    (∀ d ∈ (N.factorization p + 1).divisors,
      Irreducible (Polynomial.cyclotomic d ℤ) ∧ Irreducible (Polynomial.cyclotomic d ℚ)) ∧
    (∀ d₁ ∈ (N.factorization p + 1).divisors, ∀ d₂ ∈ (N.factorization p + 1).divisors,
      d₁ ≠ d₂ → IsCoprime (Polynomial.cyclotomic d₁ ℚ) (Polynomial.cyclotomic d₂ ℚ)) := by
  refine ⟨fun d hd => ?_, fun d₁ _ d₂ _ hne => Polynomial.cyclotomic.isCoprime_rat hne⟩
  have hpos : 0 < d := Nat.pos_of_mem_divisors hd
  exact ⟨Polynomial.cyclotomic.irreducible hpos, Polynomial.cyclotomic.irreducible_rat hpos⟩

end OddPerfect
