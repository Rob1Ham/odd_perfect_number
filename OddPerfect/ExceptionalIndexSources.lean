module

public import OddPerfect.ExceptionalIndexResidue
public import OddPerfect.IndexPrimeReturn
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Algebra.Order.Ring.Abs

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- The geometric sum at a cofactor prime outside the index cannot be pure
when the Euler length is twice a prime one modulo four. -/
theorem no_pure_external_source_of_twice_prime_length {q a m i d r β : ℕ}
    (hq : q.Prime) (hq4 : q%4=1) (hd : d.Prime) (hd4 : d%4=1)
    (hlen : a+1=2*d) (hm : Odd m) (hi : 0 < i)
    (hr : r.Prime) (hrm : r ∣ m) (hri : ¬r ∣ i) (hret : sigma 1 (q^a)*i=2*m^2) :
    sigma 1 (r^(2*m.factorization r))≠q^β := by
  intro hpure
  let e := 2*m.factorization r
  have he1 := (hr.dvd_iff_one_le_factorization hm.pos.ne').mp hrm
  have he : 2≤e := by dsimp [e]; omega
  have hro := hm.of_dvd_nat hrm
  have hback := pure_component_index_return_length hr hro hq hm.pos hi (by dsimp [e] at he; omega) hpure hret
  rw [Nat.factorization_eq_zero_of_not_dvd hri,Nat.sub_zero,hlen] at hback
  change r^(e-1) ∣ 2*d at hback
  have hpart : r^(e-1) ∣ d := (Nat.coprime_two_right.mpr (hro.pow (n:=e-1))).dvd_of_dvd_mul_left hback
  have hrd := (Nat.prime_dvd_prime_iff_eq hr hd).mp ((dvd_pow_self r (by omega : e-1≠0)).trans hpart)
  rw [←hrd] at hpart
  have hle : e-1 ≤ 1 := (Nat.pow_dvd_pow_iff_le_right hr.one_lt).mp (by simpa only [pow_one] using hpart)
  have heq : e=2 := by omega
  have hp4 : r ≡ 1 [MOD 4] := hrd ▸ hd4
  have h3 := (sigma_modEq_of_one hr hp4 e).symm
  change sigma 1 (r^e)=q^β at hpure
  rw [hpure] at h3
  have hcon := h3.trans ((show q ≡ 1 [MOD 4] from hq4).pow β)
  simp [heq,Nat.ModEq] at hcon

/-- The product of all index parts spent by a chosen set of cofactor
components divides the index. The set can have any finite cardinality. -/
theorem index_parts_dvd {q a m i : ℕ} (hqi : q.Coprime i) (hm : 0<m)
    (hl : sigma 1 (m^2)=q^a*i) (S : Finset ℕ) (hS : S⊆m.primeFactors) :
    (∏ r ∈ S,(sigma 1 (r^(2*m.factorization r))).gcd i) ∣ i := by
  let f (r : ℕ) := sigma 1 (r^(2*m.factorization r))
  have hprod : (∏ r ∈ m.primeFactors,f r)=q^a*i := by
    rw [←hl,(isMultiplicative_sigma (k:=1)).multiplicative_factorization _ (pow_ne_zero _ hm.ne')]
    change (∏ r ∈ m.primeFactors,f r) = ∏ r ∈ (m^2).primeFactors,sigma 1 (r^((m^2).factorization r))
    simp [f,Nat.primeFactors_pow m (by decide : 2≠0),Nat.factorization_pow]
  have hdiv : (∏ r ∈ S,(f r).gcd i) ∣ q^a*i := by
    rw [←hprod]
    exact (Finset.prod_dvd_prod_of_dvd _ _ (fun r _ => Nat.gcd_dvd_left _ _)).trans
      (Finset.prod_dvd_prod_of_subset S m.primeFactors f hS)
  have hc : q.Coprime (∏ r ∈ S,(f r).gcd i) := Nat.Coprime.prod_right (fun r _ =>
    hqi.of_dvd_right (Nat.gcd_dvd_right _ _))
  exact (hc.pow_left a).symm.dvd_of_dvd_mul_left hdiv

private theorem card_le_factors_of_parts {S : Finset ℕ} (f : ℕ → ℕ)
    (hg : ∀ r ∈ S, 1<f r) {i : ℕ} (hi : 0 < i) (hdiv : (∏ r ∈ S,f r) ∣ i) : S.card≤cardFactors i := by
  have hsum (s : Finset ℕ) (hb : ∀ r ∈ s, 1<f r) : s.card ≤ cardFactors (∏ r ∈ s,f r) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert r s hr ih =>
      have hl := hb r (Finset.mem_insert_self ..)
      have ht (r : ℕ) (h : r ∈ s) := hb r (Finset.mem_insert_of_mem h)
      have hpos : 0 < ∏ r ∈ s,f r := Finset.prod_pos (fun r h => by have := ht r h; omega)
      rw [Finset.prod_insert hr,Finset.card_insert_of_notMem hr,cardFactors_mul (by omega) hpos.ne']
      have := cardFactors_pos_iff_one_lt.mpr hl
      have := ih ht
      omega
  obtain ⟨u,hu⟩ := hdiv
  have hpos := (mul_ne_zero_iff.mp (hu ▸ hi.ne'))
  rw [hu,cardFactors_mul hpos.1 hpos.2]
  exact (hsum S hg).trans (Nat.le_add_right _ _)

/-- With a prime-times-square Euler index at exponent greater than one,
every prime outside the index spends at least one prime factor of it.
This gives a support bound independent of the Euler length. -/
theorem prime_mul_square_index_external_source_bound {N q a m l t i : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1)
    (ha : 1<a) (hqm : ¬q ∣ m) (hform : N=q^a*m^2) (hl : l=1 ∨ l.Prime)
    (hiEq : sigma 1 (m^2)/q^a=i) (hs : i=l*t^2) :
    (m.primeFactors \ i.primeFactors).card ≤ cardFactors i ∧
      N.primeFactors.card ≤ i.primeFactors.card+cardFactors i+1 := by
  have hmo : Odd m := ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2≠0)) _)
  obtain ⟨u,hu,hleft,hright,_⟩ := exists_component_index hN hq hform (fun h => hqm (hq.dvd_of_dvd_pow h))
  have heq : u=i := by simpa only [hleft,Nat.mul_div_cancel_left _ (Nat.pow_pos hq.pos)] using hiEq
  subst u
  obtain ⟨hd,hd8,_,_⟩ := prime_mul_square_index_forces_exceptional_prime_length
    hN ho hq hq4 ha4 ha hqm hform hl (hiEq.trans hs)
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  have hqi : q.Coprime i := hq.coprime_iff_not_dvd.mpr (fun h => hqm (hq.dvd_of_dvd_pow
    ((Nat.coprime_two_right.mpr hqo).dvd_of_dvd_mul_left (hright ▸ h.trans (dvd_mul_left _ _)))))
  let S := m.primeFactors \ i.primeFactors
  let f (r : ℕ) := sigma 1 (r^(2*m.factorization r))
  have hsub : S ⊆ m.primeFactors := Finset.sdiff_subset
  have hspent (r : ℕ) (h : r ∈ S) : 1<(f r).gcd i := by
    obtain ⟨hrm,hri⟩ := Finset.mem_sdiff.mp h
    obtain ⟨hr,hrm',_⟩ := Nat.mem_primeFactors.mp hrm
    have hrni : ¬r ∣ i := fun hr' => hri (Nat.mem_primeFactors.mpr ⟨hr,hr',hu.ne'⟩)
    have he := (hr.dvd_iff_one_le_factorization hmo.pos.ne').mp hrm'
    have hdiv := cofactor_component_sum_dvd_index_product hmo.pos hr rfl (by omega) hleft
    by_contra! hlow
    have hzero := Nat.gcd_pos_of_pos_right (f r) hu
    have hcop : (f r).Coprime i := by change (f r).gcd i=1; omega
    obtain ⟨β,_,hβ⟩ := (Nat.dvd_prime_pow hq).mp (hcop.dvd_of_dvd_mul_right hdiv)
    exact no_pure_external_source_of_twice_prime_length hq hq4 hd (by omega)
      (by omega) hmo hu hr hrm' hrni hright hβ
  have hbound := card_le_factors_of_parts (fun r => (f r).gcd i) hspent hu (index_parts_dvd hqi hmo.pos hleft S hsub)
  refine ⟨hbound,?_⟩
  have hmcard := Finset.card_sdiff_add_card_inter m.primeFactors i.primeFactors
  have hinter := Finset.card_le_card (Finset.inter_subset_right (s₁:=m.primeFactors) (s₂:=i.primeFactors))
  have hncard : N.primeFactors.card ≤ m.primeFactors.card+1 := by
    rw [hform,Nat.primeFactors_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hmo.pos.ne'),
      Nat.primeFactors_pow q (by omega),Nat.primeFactors_pow m (by decide : 2≠0),hq.primeFactors]
    simpa only [Finset.card_singleton,Nat.add_comm] using Finset.card_union_le ({q}:Finset ℕ) m.primeFactors
  dsimp [S] at hbound
  omega

end OddPerfect
