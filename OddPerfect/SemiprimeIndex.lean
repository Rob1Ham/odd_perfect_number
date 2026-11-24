module

public import OddPerfect.SemiprimeLocal
public import OddPerfect.SemiprimeSources
public import OddPerfect.PrimeSquareIndex
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction Finset

private theorem two_pow_gt_plus_four {t : ℕ} (h : 3 ≤ t) : t+4 < 2^t := by
  induction t, h using Nat.le_induction with
  | base => decide
  | succ t _ ih => rw [pow_succ]; omega

/-- A candidate with Euler index the product of two distinct odd primes would
need two pure square sources with a shared budget of outgoing exponents. -/
theorem semiprime_index_source_constraints {N q a m p r : ℕ} (hN : Nat.Perfect N)
    (ho : Odd N) (hq : q.Prime) (ha4 : a%4=1) (hqm : ¬ q ∣ m) (hform : N=q^a*m^2)
    (hp : p.Prime) (hr : r.Prime) (hpo : Odd p) (hro : Odd r) (hpr : p ≠ r)
    (hleft : sigma 1 (m^2) = q^a*(p*r)) (hright : sigma 1 (q^a)*(p*r) = 2*m^2) :
    ∃ β γ : ℕ, 0 < β ∧ 0 < γ ∧ sigma 1 (p^2)=q^β ∧ sigma 1 (r^2)=q^γ ∧
      p ∣ sigma 1 (q^a) ∧ r ∣ sigma 1 (q^a) ∧ β+γ ≤ a ∧
      (a+1=2 ∨ ∃ l k : ℕ, l.Prime ∧ Odd l ∧ (k=1 ∨ k=2) ∧ a+1=2*l^k ∧
        (k=2 → q ≡ 1 [MOD l])) := by
  classical
  let b := m^2
  let f := fun z : ℕ => sigma 1 (z^b.factorization z)
  have hbo : Odd b := ho.of_dvd_nat (hform ▸ dvd_mul_left _ _)
  have hqb : ¬ q ∣ b := fun h => hqm (hq.dvd_of_dvd_pow h)
  have hao : Odd a := Nat.odd_iff.mpr (by omega)
  have hpB : p ∈ b.primeFactors := Nat.mem_primeFactors.mpr ⟨hp,
    (Nat.coprime_two_right.mpr hpo).dvd_of_dvd_mul_left
      (hright ▸ (dvd_mul_right p r).trans (dvd_mul_left _ _)), hbo.pos.ne'⟩
  have hrB : r ∈ b.primeFactors := Nat.mem_primeFactors.mpr ⟨hr,
    (Nat.coprime_two_right.mpr hro).dvd_of_dvd_mul_left
      (hright ▸ (dvd_mul_left r p).trans (dvd_mul_left _ _)), hbo.pos.ne'⟩
  have hpq : p ≠ q := fun h => hqb (h ▸ Nat.dvd_of_mem_primeFactors hpB)
  have hrq : r ≠ q := fun h => hqb (h ▸ Nat.dvd_of_mem_primeFactors hrB)
  have hqI : q.Coprime (p*r) :=
    (hq.coprime_iff_not_dvd.mpr (fun h => hpq.symm ((Nat.prime_dvd_prime_iff_eq hq hp).mp h))).mul_right
    (hq.coprime_iff_not_dvd.mpr (fun h => hrq.symm ((Nat.prime_dvd_prime_iff_eq hq hr).mp h)))
  have hweight := euler_prime_count_le_length_and_index_factors hN ho hq hao hform hqb hleft hright
  rw [Nat.primeFactors_mul hp.ne_zero hr.ne_zero, hp.primeFactors, hr.primeFactors,
    cardFactors_mul hp.ne_zero hr.ne_zero, cardFactors_apply_prime hp, cardFactors_apply_prime hr] at hweight
  have hpair : (({p} : Finset ℕ) ∪ {r}).card = 2 := by simp [hpr]
  rw [hpair] at hweight
  have hpow := two_pow_component_length_support_le_prime_count hN ho hq hao.pos hform hqb
  have ht2 : (a+1).primeFactors.card ≤ 2 := by
    by_contra! h
    have := two_pow_gt_plus_four h
    omega
  have hN6 : N.primeFactors.card ≤ 6 := by omega
  have h2L : 2 ∈ (a+1).primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_two, by omega, by omega⟩
  let L := (a+1).primeFactors.erase 2
  have hLcard : L.card ≤ 1 := by
    have h : L.card + 1 = (a+1).primeFactors.card := Finset.card_erase_add_one h2L
    omega
  have hqN := Nat.mem_primeFactors.mpr ⟨hq, hform ▸ (dvd_pow_self q hao.pos.ne').trans
    (dvd_mul_right _ _), hN.2.ne'⟩
  have hval : N.factorization q = a := by
    rw [hform, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) hbo.pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hqb, hq.factorization_pow, Finsupp.single_eq_same, add_zero]
  have hτ := component_length_divisor_count hN ho hqN
  rw [hval] at hτ
  obtain ⟨x, hx, y, hy, pure⟩ := exists_two_exceptional_sources hbo.pos hq hp hr hpr hpq hrq hleft
  let E : Finset ℕ := {x,y}
  let T := insert q (insert p (insert r E))
  have hE : E.card ≤ 2 := by
    have := Finset.card_insert_le x ({y} : Finset ℕ)
    simpa [E] using this
  have hTq := Finset.card_insert_le q (insert p (insert r E))
  have hTp := Finset.card_insert_le p (insert r E)
  have hTr := Finset.card_insert_le r E
  have hTmax : T.card ≤ 5 := by dsimp only [T]; omega
  have hsrc (t : ℕ) (htN : t ∈ N.primeFactors) (htT : t ∉ T) :
      ∃ β : ℕ, sigma 1 (t ^ b.factorization t)=q^β ∧ t^b.factorization t ∣ sigma 1 (q^a) ∧ t ∈ L := by
    have ht := Nat.prime_of_mem_primeFactors htN
    have htd := Nat.dvd_of_mem_primeFactors htN
    have hto := ho.of_dvd_nat htd
    simp only [T, E, Finset.mem_insert, Finset.mem_singleton, not_or] at htT
    have htb := (ht.dvd_mul.mp (hform ▸ htd)).resolve_left
      (fun h => htT.1 ((Nat.prime_dvd_prime_iff_eq ht hq).mp (ht.dvd_of_dvd_pow h)))
    have htmem := Nat.mem_primeFactors.mpr ⟨ht, htb, hbo.pos.ne'⟩
    obtain ⟨β, hβ⟩ := pure t htmem htT.2.2.2.1 htT.2.2.2.2
    have hcop := ht.coprime_iff_not_dvd.mpr (fun h => (ht.dvd_mul.mp h).elim
      (fun h => htT.2.1 ((Nat.prime_dvd_prime_iff_eq ht hp).mp h))
      (fun h => htT.2.2.1 ((Nat.prime_dvd_prime_iff_eq ht hr).mp h)))
    have hback : t^b.factorization t ∣ sigma 1 (q^a) := (hcop.pow_left _).dvd_of_dvd_mul_right
      (hright ▸ (Nat.ordProj_dvd b t).trans (dvd_mul_left _ _))
    have hepos := (ht.dvd_iff_one_le_factorization hbo.pos.ne').mp htb
    have he : b.factorization t = 2*m.factorization t := by simp [b, Nat.factorization_pow]
    have hlen := reciprocal_component_length ht hto hq hepos hβ hback
    refine ⟨β, hβ, hback, Finset.mem_erase.mpr ⟨fun h => hto.not_two_dvd_nat (h ▸ dvd_rfl), ?_⟩⟩
    exact Nat.mem_primeFactors.mpr
      ⟨ht, (dvd_pow_self t (by omega : b.factorization t-1 ≠ 0)).trans hlen, by omega⟩
  have outside (h : T.card < N.primeFactors.card) : ∃ t ∈ N.primeFactors, t ∉ T := by
    by_contra! hnone
    exact h.not_ge (Finset.card_le_card hnone)
  have hTmin : 5 ≤ T.card := by
    by_contra! h
    have hsub : N.primeFactors ⊆ T ∪ L := by
      intro t ht
      by_cases htT : t ∈ T
      · exact Finset.mem_union_left _ htT
      · obtain ⟨_, _, _, htL⟩ := hsrc t ht htT
        exact Finset.mem_union_right _ htL
    have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le T L)
    have h5 := five_le_distinct_prime_factor_count ho hN
    obtain ⟨t, ht, htT⟩ := outside (by omega)
    obtain ⟨β, hβ, hback, htL⟩ := hsrc t ht htT
    have htp := Nat.prime_of_mem_primeFactors ht
    have hto := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors ht)
    have htwo := length_eq_twice_prime_of_five ha4 htp hto
      (Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase htL)) (by omega)
    have he : b.factorization t = 2*m.factorization t := by simp [b, Nat.factorization_pow]
    have hpurepos : 0 < b.factorization t := by
      by_contra! hz
      have hzero : b.factorization t = 0 := by omega
      have hqne : t ≠ q := fun h => htT (h ▸ Finset.mem_insert_self ..)
      have hdiv := (htp.dvd_mul.mp (hform ▸ Nat.dvd_of_mem_primeFactors ht)).resolve_left
        (fun h => hqne ((Nat.prime_dvd_prime_iff_eq htp hq).mp (htp.dvd_of_dvd_pow h)))
      have := (htp.dvd_iff_one_le_factorization hbo.pos.ne').mp hdiv
      omega
    exact not_pure_return_at_twice_source_length htp hto hq ⟨m.factorization t, by omega⟩ hpurepos hβ hback htwo
  have hpE : p ∉ E := by
    intro h
    have hpi : p ∈ insert r E := Finset.mem_insert_of_mem h
    change 5 ≤ (insert q (insert p (insert r E))).card at hTmin
    rw [Finset.insert_eq_of_mem hpi] at hTmin hTq
    omega
  have hrE : r ∉ E := by
    intro h
    change 5 ≤ (insert q (insert p (insert r E))).card at hTmin
    rw [Finset.insert_eq_of_mem h] at hTmin hTq hTp
    omega
  have named (u : ℕ) (hu : u.Prime) (huo : Odd u) (huT : u ∈ T) : ¬ u^2 ∣ a+1 := by
    intro h2
    have hd := (dvd_pow_self u (by decide : 2 ≠ 0)).trans h2
    by_cases hn5 : N.primeFactors.card ≤ 5
    · have hh := length_eq_twice_prime_of_five ha4 hu huo hd (hτ.trans hn5)
      rw [hh, pow_two, Nat.mul_comm 2] at h2
      have hle := Nat.le_of_dvd (by decide : 0 < 2) (Nat.dvd_of_mul_dvd_mul_left hu.pos h2)
      have := Nat.odd_iff.mp huo
      have := hu.two_le
      omega
    · obtain ⟨t, htN, htT⟩ := outside (by omega)
      obtain ⟨_, _, _, htL⟩ := hsrc t htN htT
      have huL : u ∈ L := Finset.mem_erase.mpr ⟨fun h => huo.not_two_dvd_nat (h ▸ dvd_rfl),
        Nat.mem_primeFactors.mpr ⟨hu, hd, by omega⟩⟩
      exact htT (((Finset.card_le_one.mp hLcard) t htL u huL) ▸ huT)
  have index_data (u : ℕ) (hu : u.Prime) (huo : Odd u) (huB : u ∈ b.primeFactors)
      (huE : u ∉ E) (huT : u ∈ T) (hui : (p*r).factorization u = 1) :
      ∃ β : ℕ, 0 < β ∧ sigma 1 (u^2)=q^β ∧ u ∣ sigma 1 (q^a) ∧ f u = q^β := by
    simp only [E, Finset.mem_insert, Finset.mem_singleton, not_or] at huE
    obtain ⟨β,hβ⟩ := pure u huB huE.1 huE.2
    have he : b.factorization u = 2*m.factorization u := by simp [b, Nat.factorization_pow]
    have hepos := (hu.dvd_iff_one_le_factorization hbo.pos.ne').mp (Nat.dvd_of_mem_primeFactors huB)
    have hv := one_copy_index_return_valuation hq hu huo hbo.pos (Nat.mul_pos hp.pos hr.pos) hui hright
    change b.factorization u = (sigma 1 (q^a)).factorization u + 1 at hv
    have hσpos := (sigma_pos 1 _ (pow_ne_zero a hq.ne_zero)).ne'
    have hweak := (hu.pow_dvd_iff_le_factorization hσpos).mpr
      (by omega : b.factorization u - 1 ≤ (sigma 1 (q^a)).factorization u)
    have hlen := reciprocal_return_length hu huo hq hepos hβ hweak
    have he2 : b.factorization u = 2 := by
      by_contra h
      exact named u hu huo huT ((pow_dvd_pow u (by omega : 2 ≤ b.factorization u-1-1)).trans hlen)
    have hs : sigma 1 (u^2)=q^β := he2 ▸ hβ
    have hβ0 : 0 < β := by
      have hlarge : 1 < sigma 1 (u^2) := by
        rw [sigma_one_apply_prime_pow hu]
        simp [Finset.sum_range_succ]
        have := hu.one_lt
        omega
      by_contra! hz
      rw [show β=0 by omega, pow_zero] at hs
      omega
    exact ⟨β, hβ0, hs, (hu.dvd_iff_one_le_factorization hσpos).mpr (by omega), hβ⟩
  have hprnd : ¬ p ∣ r := fun h => hpr ((Nat.prime_dvd_prime_iff_eq hp hr).mp h)
  have hrpnd : ¬ r ∣ p := fun h => hpr.symm ((Nat.prime_dvd_prime_iff_eq hr hp).mp h)
  have hp1 : (p*r).factorization p = 1 := by simp [Nat.factorization_mul hp.ne_zero hr.ne_zero,
    hp.factorization_self, Nat.factorization_eq_zero_of_not_dvd hprnd]
  have hr1 : (p*r).factorization r = 1 := by simp [Nat.factorization_mul hp.ne_zero hr.ne_zero,
    hr.factorization_self, Nat.factorization_eq_zero_of_not_dvd hrpnd]
  obtain ⟨β,hβ,hSp,hpRet,hfp⟩ := index_data p hp hpo hpB hpE (by simp [T]) hp1
  obtain ⟨γ,hγ,hSr,hrRet,hfr⟩ := index_data r hr hro hrB hrE (by simp [T]) hr1
  have hprod : sigma 1 b = ∏ t ∈ b.primeFactors, f t :=
    (isMultiplicative_sigma (k := 1)).multiplicative_factorization _ hbo.pos.ne'
  have hdq : q^(β+γ) ∣ q^a*(p*r) := by
    rw [pow_add, ← hfp, ← hfr, ← hleft, hprod]
    exact two_sources_mul_dvd_prod hpB hrB hpr f
  have heSum := (hq.pow_dvd_iff_le_factorization (pow_ne_zero a hq.ne_zero)).mp
    ((hqI.pow_left (β+γ)).dvd_of_dvd_mul_right hdq)
  rw [hq.factorization_pow, Finsupp.single_eq_same] at heSum
  refine ⟨β,γ,hβ,hγ,hSp,hSr,hpRet,hrRet,heSum,?_⟩
  rcases euler_length_cases_of_divisor_count_le_six ha4 (hτ.trans hN6) with h | ⟨l,k,hl,hlo,hk,hL⟩
  · exact Or.inl h
  · refine Or.inr ⟨l,k,hl,hlo,hk,hL,?_⟩
    rintro rfl
    have hlL : l ∣ a+1 := hL ▸ (dvd_pow_self l (by decide : 2 ≠ 0)).trans (dvd_mul_left _ _)
    have hn6 : 5 < N.primeFactors.card := by
      by_contra! h
      have hh := length_eq_twice_prime_of_five ha4 hl hlo hlL (hτ.trans h)
      have := Nat.mul_lt_mul_of_pos_left hl.one_lt hl.pos
      rw [pow_two] at hL
      omega
    obtain ⟨t, ht, htT⟩ := outside (by omega)
    obtain ⟨δ,hδ,hback,htL⟩ := hsrc t ht htT
    have hlmem : l ∈ L := Finset.mem_erase.mpr ⟨fun h => hlo.not_two_dvd_nat (h ▸ dvd_rfl),
      Nat.mem_primeFactors.mpr ⟨hl, hlL, by omega⟩⟩
    have htl := (Finset.card_le_one.mp hLcard) t htL l hlmem
    subst t
    have he : b.factorization l = 2*m.factorization l := by simp [b, Nat.factorization_pow]
    have hlq : l ≠ q := fun h => htT (h ▸ Finset.mem_insert_self ..)
    have hlb := (hl.dvd_mul.mp (hform ▸ Nat.dvd_of_mem_primeFactors ht)).resolve_left
      (fun h => hlq ((Nat.prime_dvd_prime_iff_eq hl hq).mp (hl.dvd_of_dvd_pow h)))
    have hepos := (hl.dvd_iff_one_le_factorization hbo.pos.ne').mp hlb
    have hlen := reciprocal_component_length hl hlo hq hepos hδ hback
    have he2 : b.factorization l = 2 := by
      by_contra h
      have hd3 := (pow_dvd_pow l (by omega : 3 ≤ b.factorization l - 1)).trans hlen
      rw [hL, pow_succ l 2, Nat.mul_comm 2] at hd3
      have := Nat.le_of_dvd (by decide : 0 < 2) (Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos hl.pos) hd3)
      have := Nat.odd_iff.mp hlo
      have := hl.two_le
      omega
    rw [he2] at hδ hback
    exact selected_modEq_one_at_length_prime hl hq hδ ((dvd_pow_self l (by decide : 2 ≠ 0)).trans hback) hL

/-- The Euler index cannot be a product of two distinct odd primes. -/
theorem euler_component_index_ne_semiprime {N q a m p r i : ℕ} (hN : Nat.Perfect N)
    (ho : Odd N) (hq : q.Prime) (ha4 : a%4=1) (hqm : ¬ q ∣ m) (hform : N=q^a*m^2)
    (hp : p.Prime) (hr : r.Prime) (hpo : Odd p) (hro : Odd r) (hpr : p ≠ r)
    (hleft : sigma 1 (m^2)=q^a*i) (hright : sigma 1 (q^a)*i=2*m^2) : i ≠ p*r := by
  rintro rfl
  obtain ⟨β,γ,hβ,hγ,hpout,hrout,hpback,hrback,hbudget,h⟩ :=
    semiprime_index_source_constraints hN ho hq ha4 hqm hform hp hr hpo hro hpr hleft hright
  rcases h with h | ⟨l,k,hl,hlo,hk,hL,h2⟩
  · omega
  · by_cases hpl : p = l
    · subst p
      exact selected_not_modEq_one_of_other_pure_square hr hro hq hl hlo hpr.symm hrout hrback hL
        (selected_modEq_one_at_length_prime hl hq hpout hpback hL)
    by_cases hrl : r = l
    · subst r
      exact selected_not_modEq_one_of_other_pure_square hp hpo hq hl hlo hpr hpout hpback hL
        (selected_modEq_one_at_length_prime hl hq hrout hrback hL)
    rcases hk with h | h
    · have hpβ := (length_prime_dvd_exponent_and_pred hp hpo hq hl hpl hpout hpback hL).1
      have hrγ := (length_prime_dvd_exponent_and_pred hr hro hq hl hrl hrout hrback hL).1
      rw [h, pow_one] at hL
      have := Nat.le_of_dvd hβ hpβ
      have := Nat.le_of_dvd hγ hrγ
      omega
    · exact selected_not_modEq_one_of_other_pure_square hp hpo hq hl hlo hpl hpout hpback hL (h2 h)

end OddPerfect
