module

public import OddPerfect.IndexWeight
public import OddPerfect.SmallEulerIndex
public import OddPerfect.Steuerwald
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- The base of a prime-square Euler index cannot also divide the component
length: the two occurrences would overlap in the support count. -/
theorem prime_square_index_not_dvd_length {N q a b p : ℕ} (hN : Nat.Perfect N)
    (ho : Odd N) (hq : Nat.Prime q) (ha : Odd a) (hform : N = q^a*b) (hqb : ¬ q ∣ b)
    (hp : Nat.Prime p) (hpo : Odd p) (hleft : sigma 1 b = q^a*p^2)
    (hright : sigma 1 (q^a)*p^2 = 2*b) : ¬ p ∣ a+1 := by
  intro hd
  let L := (a+1).primeFactors.erase 2
  have hpL : p ∈ L := Finset.mem_erase.mpr
    ⟨fun h => hpo.not_two_dvd_nat (h ▸ dvd_rfl), Nat.mem_primeFactors.mpr ⟨hp, hd, by omega⟩⟩
  have hunion : L ∪ (p^2).primeFactors = L := by
    rw [Nat.primeFactors_pow _ (by decide : 2 ≠ 0), hp.primeFactors]
    exact Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr hpL)
  have hcover := euler_prime_count_le_index_union hN ho hq ha hform hqb hleft hright
  change N.primeFactors.card ≤ (L ∪ (p^2).primeFactors).card + cardFactors (p^2) + 1 at hcover
  rw [hunion, cardFactors_apply_prime_pow hp] at hcover
  have h2 : 2 ∈ (a+1).primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_two, by have := Nat.odd_iff.mp ha; omega, by omega⟩
  have hL : L.card + 1 = (a+1).primeFactors.card := Finset.card_erase_add_one h2
  have := component_length_support_add_three_le hN ho hq ha.pos hform hqb
  omega

/-- A prime-square index with Fermat-prime base is impossible at every exact
component. This includes the Euler indices nine and twenty-five. -/
theorem component_index_ne_fermat_prime_square {N q a b i p k : ℕ} (hN : Nat.Perfect N)
    (ho : Odd N) (hq : Nat.Prime q) (ha : 0 < a) (hform : N = q^a*b) (hqb : ¬ q ∣ b)
    (hleft : sigma 1 b = q^a*i) (hright : sigma 1 (q^a)*i = 2*b)
    (hp : Nat.Prime p) (hk : p-1 = 2^k) : i ≠ p^2 := by
  rintro rfl
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b (q^a))
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hd : 4 ∣ 2*b := hright ▸ dvd_mul_left _ _
    have := hbo.not_two_dvd_nat
    omega
  have hpo := hp.odd_of_ne_two hp2
  have hao : Odd a := by
    rcases component_index_parity_bound hN ho hq ha hform hqb hleft hright with h | h
    · exact h.1
    · have := Nat.odd_iff.mp (hpo.pow (n := 2))
      have := h.2.1
      omega
  have hnlen := prime_square_index_not_dvd_length hN ho hq hao hform hqb hp hpo hleft hright
  have hval : N.factorization q = a := by
    rw [hform, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) hbo.pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hqb, hq.factorization_pow, Finsupp.single_eq_same, add_zero]
  obtain ⟨s, _, hs4, _, hoth⟩ := euler_exponents ho hN
  have hqs : q = s := by
    by_contra h
    have := Nat.even_iff.mp (hoth q h)
    have := Nat.odd_iff.mp hao
    omega
  subst s
  let f := fun r : ℕ => sigma 1 (r ^ b.factorization r)
  have hprod : sigma 1 b = ∏ r ∈ b.primeFactors, f r :=
    (isMultiplicative_sigma (k := 1)).multiplicative_factorization _ hbo.pos.ne'
  have hcofactor (r : ℕ) (hr : r.Prime) (hrq : r ≠ q) :
      N.factorization r = b.factorization r := by
    have hnd : ¬ r ∣ q^a := fun h => hrq ((Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow h))
    rw [hform, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) hbo.pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnd, zero_add]
  have htypes (r : ℕ) (hrB : r ∈ b.primeFactors) :
      Even (b.factorization r) ∧ 0 < b.factorization r ∧ f r ∣ p^2 * q^a := by
    obtain ⟨hr, hd, _⟩ := Nat.mem_primeFactors.mp hrB
    have hrq : r ≠ q := fun h => hqb (h ▸ hd)
    refine ⟨hcofactor r hr hrq ▸ hoth r hrq, (hr.dvd_iff_one_le_factorization hbo.pos.ne').mp hd, ?_⟩
    rw [Nat.mul_comm, ← hleft, hprod]
    exact Finset.dvd_prod_of_mem _ hrB
  have hpout : p ∣ sigma 1 b := hleft ▸ (dvd_pow_self p (by decide : 2 ≠ 0)).trans (dvd_mul_left _ _)
  rw [hprod] at hpout
  obtain ⟨r, hrB, hpr⟩ := (hp.prime.dvd_finsetProd_iff _).mp hpout
  obtain ⟨hrE, hrpos, hrσ⟩ := htypes r hrB
  have hcon := (exceptional_prime_power_index_component (Nat.prime_of_mem_primeFactors hrB)
    hrE hrpos hp hk hq hrσ hpr).2.2
  have hq1 : q ≡ 1 [MOD p] := ((Nat.modEq_iff_dvd' hq.one_lt.le).mpr hcon).symm
  have hnotS : ¬ p ∣ sigma 1 (q^a) := fun h => hnlen (((sigma_modEq_of_one hq hq1 a).dvd_iff dvd_rfl).mp h)
  have hpN : b.factorization p = 2 := by
    have hv := congrArg (fun n : ℕ => n.factorization p) hright
    change (sigma 1 (q^a)*p^2).factorization p = (2*b).factorization p at hv
    rw [Nat.factorization_mul (sigma_pos _ _ (pow_ne_zero _ hq.ne_zero)).ne' (pow_ne_zero _ hp.ne_zero),
      Nat.factorization_mul (by decide : 2 ≠ 0) hbo.pos.ne', Finsupp.add_apply, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnotS, hp.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))] at hv
    omega
  have hpB : p ∈ b.primeFactors := Finsupp.mem_support_iff.mpr (by omega : b.factorization p ≠ 0)
  have hsP := (htypes p hpB).2.2
  change sigma 1 (p ^ b.factorization p) ∣ p^2 * q^a at hsP
  rw [hpN] at hsP
  have hnotP : ¬ p ∣ sigma 1 (p^2) := by
    rw [Nat.dvd_iff_mod_eq_zero, sigma_prime_pow_mod_self hp]
    decide
  have hseed := ((hp.coprime_iff_not_dvd.mpr hnotP).symm.pow_right 2).dvd_of_dvd_mul_left hsP
  obtain ⟨β, _, hβ⟩ := (Nat.dvd_prime_pow hq).mp hseed
  have hp4 : p % 4 ≠ 1 := by
    intro h
    have hs := sigma_modEq_of_one hp (show p ≡ 1 [MOD 4] from h) 2
    have hqpow := (show q ≡ 1 [MOD 4] from hs4).pow β
    rw [hβ] at hs
    simp only [one_pow] at hqpow
    change q^β % 4 = 1 at hqpow
    change q^β % 4 = 3 at hs
    omega
  have hp3 : p = 3 := by
    have hpge := hp.two_le
    cases k with
    | zero => simp only [pow_zero] at hk; omega
    | succ k =>
      cases k with
      | zero => norm_num at hk; omega
      | succ k => rw [pow_succ, pow_succ] at hk; omega
  subst p
  have hs13 : sigma 1 ((3 : ℕ)^2) = 13 := by decide +kernel
  have hβ0 : β ≠ 0 := by rintro rfl; simp only [pow_zero] at hβ; omega
  have hq13 : q = 13 := (Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 13)).mp
    ((hs13.symm.trans hβ) ▸ dvd_pow_self q hβ0)
  subst q
  obtain ⟨_, _, _, _, t, htN, _, hte, ht4⟩ := steuerwald ho hN
  have htq : t ≠ 13 := by
    rintro rfl
    have := Nat.even_iff.mp hte
    have := Nat.odd_iff.mp hao
    omega
  obtain ⟨ht, htd, _⟩ := Nat.mem_primeFactors.mp htN
  have htn : ¬ t ∣ 13^a := fun h => htq ((Nat.prime_dvd_prime_iff_eq ht hq).mp (ht.dvd_of_dvd_pow h))
  have htb := (ht.dvd_mul.mp (hform ▸ htd)).resolve_left htn
  obtain ⟨htEven, htpos, htσ⟩ := htypes t (Nat.mem_primeFactors.mpr ⟨ht, htb, hbo.pos.ne'⟩)
  obtain ⟨hl, _, hd⟩ := prime_length_of_two_prime_support ht htEven htpos hp hk hq htσ
  change b.factorization t + 1 ∣ 3 * 2^2 at hd
  have hval' := hcofactor t ht htq
  rcases hl.dvd_mul.mp hd with h | h
  · have := Nat.le_of_dvd (by decide : 0 < 3) h
    omega
  · have := Nat.le_of_dvd (by decide : 0 < 2) (hl.dvd_of_dvd_pow h)
    omega

end OddPerfect
