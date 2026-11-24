module

public import OddPerfect.SmallEulerIndex
public import OddPerfect.IndexEstimate
public import OddPerfect.IndexReturn
public import OddPerfect.FewPrimes
import Mathlib.Algebra.Order.Ring.Abs

/-! Dris–Luca Theorem 1.1. The proof uses the checked four-prime lower bound,
the index-two exclusion and a separate estimate for prime Euler indices. -/

public section

namespace OddPerfect

open ArithmeticFunction

private theorem euler_index_ne_three_five {N q a m i : ℕ} (hN : Nat.Perfect N) (ho : Odd N)
    (hq : Nat.Prime q) (hq4 : q % 4 = 1) (ha4 : a % 4 = 1) (hNform : N = q^a * m^2)
    (hleft : sigma 1 (m^2) = q^a * i) (hright : sigma 1 (q^a) * i = 2 * m^2)
    (hismall : i = 3 ∨ i = 5) : False := by
  have hi : i.Prime := by rcases hismall with rfl | rfl <;> decide
  obtain ⟨k, hk⟩ : ∃ k : ℕ, i-1 = 2^k := by
    rcases hismall with rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  have hm : Odd m := ho.of_dvd_nat (hNform ▸
    (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left _ _))
  have hm2 : m^2 ≠ 0 := pow_ne_zero _ hm.pos.ne'
  have hiσ : i ∣ sigma 1 (m^2) := hleft ▸ dvd_mul_left _ _
  rw [isMultiplicative_sigma.multiplicative_factorization _ hm2] at hiσ
  obtain ⟨r, hrmem, hir⟩ := (hi.prime.dvd_finsetProd_iff _).mp hiσ
  obtain ⟨hr, hrm2, _⟩ := Nat.mem_primeFactors.mp hrmem
  let e := (m^2).factorization r
  change i ∣ sigma 1 (r^e) at hir
  have he : e = 2 * m.factorization r := by simp [e, Nat.factorization_pow]
  have hE : Even e := ⟨m.factorization r, by omega⟩
  have hepos : 0 < e := (hr.dvd_iff_one_le_factorization hm2).mp hrm2
  have hσr : sigma 1 (r^e) ∣ i*q^a := by
    rw [Nat.mul_comm, ← hleft, isMultiplicative_sigma.multiplicative_factorization _ hm2]
    exact Finset.dvd_prod_of_mem _ hrmem
  obtain ⟨_, _, hqcon⟩ := exceptional_small_index_component hr hE hepos hi hk hq hσr hir
  have hq7 : 7 ≤ q := by rcases hismall with rfl | rfl <;> have := hq.two_le <;> omega
  have hq1 : q ≡ 1 [MOD i] := ((Nat.modEq_iff_dvd' (show 1 ≤ q by omega)).mpr hqcon).symm
  have hi2 : ¬ i ∣ 2 := by rcases hismall with rfl | rfl <;> decide
  have him2 : i ∣ m^2 := (hi.coprime_iff_not_dvd.mpr hi2).dvd_of_dvd_mul_left
    (hright ▸ dvd_mul_left _ _)
  have him : i ∣ m := hi.dvd_of_dvd_pow him2
  have hiret : i ∣ sigma 1 (q^a) := by
    apply Nat.dvd_of_mul_dvd_mul_left hi.pos
    rw [Nat.mul_comm i (sigma 1 (q^a)), hright, ← pow_two]
    exact (pow_dvd_pow_of_dvd him 2).trans (dvd_mul_left _ _)
  have hilen := ((sigma_modEq_of_one hq hq1 a).dvd_iff dvd_rfl).mp hiret
  let v := m / r ^ m.factorization r
  have hvm : v ∣ m := Nat.ordCompl_dvd m r
  have hvo := hm.of_dvd_nat hvm
  have hrv : ¬ r ∣ v := Nat.not_dvd_ordCompl hr hm.pos.ne'
  have hshape : r^e * v^2 = m^2 := by
    have hd := Nat.ordProj_mul_ordCompl_eq_self (m^2) r
    rw [pow_two m, Nat.ordCompl_mul] at hd
    simpa only [pow_two, e, v] using hd
  obtain ⟨U, hUeq⟩ := hir
  have hUprod : U * sigma 1 (v^2) = q^a := by
    apply Nat.mul_left_cancel hi.pos
    calc
      _ = sigma 1 (r^e) * sigma 1 (v^2) := by rw [hUeq]; ac_rfl
      _ = sigma 1 (m^2) := by
        rw [← isMultiplicative_sigma.map_mul_of_coprime
          (((hr.coprime_iff_not_dvd.mpr hrv).pow_left e).pow_right 2), hshape]
      _ = _ := hleft.trans (Nat.mul_comm _ _)
  have hU : U ∣ q^a := hUprod ▸ dvd_mul_right _ _
  obtain ⟨β, _, hβ⟩ := (Nat.dvd_prime_pow hq).mp
    (show sigma 1 (v^2) ∣ q^a from hUprod ▸ dvd_mul_left _ _)
  have hvback : v^2 ∣ i * sigma 1 (q^a) := by
    rw [Nat.mul_comm, hright, ← hshape]
    exact (dvd_mul_left _ _).trans (dvd_mul_left _ _)
  have hvlen := root_dvd_length_of_prime_index_return hvo hi hq hilen hβ hvback
  have hv6 := small_index_root_le_six hq hq7 hr (by omega : 2 ≤ e) hi.pos
    (by omega : i ≤ 5) hvo.pos ha4 hvlen hU hUeq (hright.trans (congrArg (2*·) hshape.symm))
  have hirne : i ≠ r := by
    intro h
    have hd : i ∣ sigma 1 (r^e) := hUeq ▸ dvd_mul_right _ _
    rw [h, Nat.dvd_iff_mod_eq_zero, sigma_prime_pow_mod_self hr] at hd
    omega
  have hiv : i ∣ v := by
    rw [← hshape] at him2
    exact hi.dvd_of_dvd_pow ((hi.dvd_mul.mp him2).resolve_left
      (fun h => hirne ((Nat.prime_dvd_prime_iff_eq hi hr).mp (hi.dvd_of_dvd_pow h))))
  have hvi : v = i := by
    have := Nat.odd_iff.mp hvo
    have := hvo.pos
    rcases hismall with rfl | rfl <;> omega
  have hsub : N.primeFactors ⊆ {q, r, i} := by
    intro p hpN
    obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp hpN
    rw [hNform, ← hshape, hvi] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hp.dvd_mul.mp hd with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h))
    · rcases hp.dvd_mul.mp h with h | h
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow h)))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp hi).mp (hp.dvd_of_dvd_pow h)))
  have hcard := Finset.card_le_card hsub
  have h2 := Finset.card_insert_le r ({i} : Finset ℕ)
  have h3 := Finset.card_insert_le q ({r,i} : Finset ℕ)
  have h1 : ({i} : Finset ℕ).card = 1 := Finset.card_singleton _
  have hf := four_le_distinct_prime_factor_count ho hN
  omega

/-- Dris–Luca Theorem 1.1. Every exact component of an odd perfect number
has index greater than five. -/
theorem component_index_gt_five {N q a b i : ℕ} (hN : Nat.Perfect N) (ho : Odd N)
    (hq : Nat.Prime q) (ha : 0 < a) (hform : N = q^a*b) (hqb : ¬ q ∣ b)
    (hleft : sigma 1 b = q^a*i) (hright : sigma 1 (q^a)*i = 2*b) : 5 < i := by
  rcases component_index_parity_bound hN ho hq ha hform hqb hleft hright with
    ⟨hao, hio, hi3⟩ | ⟨_, _, hi6⟩
  · by_contra! hsmall
    have hcases : i = 3 ∨ i = 5 := by have := Nat.odd_iff.mp hio; omega
    have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b (q^a))
    have hval : N.factorization q = a := by
      rw [hform, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) hbo.pos.ne',
        Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hqb, hq.factorization_pow,
        Finsupp.single_eq_same, add_zero]
    obtain ⟨p, _, hp4, hpExp4, hother⟩ := euler_exponents ho hN
    have hqp : q = p := by
      by_contra! h
      have := Nat.even_iff.mp (hother q h)
      have := Nat.odd_iff.mp hao
      omega
    subst p
    have hsq : IsSquare b := by
      rw [← Nat.ordCompl_pow_mul_of_not_dvd a hq hqb, ← hform]
      apply Nat.isSquare_iff_even_factorization.mpr
      intro r _
      rw [Nat.factorization_ordCompl]
      rcases eq_or_ne r q with rfl | h
      · simp
      · rw [Finsupp.erase_ne h]
        exact hother r h
    obtain ⟨m, hm⟩ := hsq
    rw [← pow_two] at hm
    subst b
    exact euler_index_ne_three_five hN ho hq hp4 (hval ▸ hpExp4) hform hleft hright hcases
  · omega

/-- The quotient formulation of the universal component-index bound. -/
theorem five_lt_divisor_sum_component_index {N q a : ℕ} (hN : Nat.Perfect N) (ho : Odd N)
    (hq : Nat.Prime q) (ha : 0 < a) (hd : q^a ∣ N) (hex : ¬ q^(a+1) ∣ N) :
    5 < sigma 1 (N / q^a) / q^a := by
  obtain ⟨b, hb⟩ := hd
  have hqb : ¬ q ∣ b := by
    intro h
    apply hex
    rw [hb, pow_succ]
    exact Nat.mul_dvd_mul_left _ h
  obtain ⟨i, _, hleft, hright, _⟩ := exists_component_index hN hq hb hqb
  have hgt := component_index_gt_five hN ho hq ha hb hqb hleft hright
  rw [hb, Nat.mul_div_cancel_left b (Nat.pow_pos hq.pos), hleft,
    Nat.mul_div_cancel_left i (Nat.pow_pos hq.pos)]
  exact hgt

end OddPerfect
