module

public import OddPerfect.IndexSieveLengths
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.FieldTheory.Finite.Basic

public section

namespace OddPerfect.IndexSieve

open ArithmeticFunction Finset

/-- Every proper divisor above one of a cofactor component length divides
`u−1` for some *index* prime `u`. The Euler prime can realize only one order. -/
theorem proper_length_dvd_index_predecessor {p q e a i d : ℕ} (hp : p.Prime) (hpo : Odd p)
    (hq : q.Prime) (he : Even e) (hepos : 0<e) (hi : i≠0) (hout : sigma 1 (p^e) ∣ q^a*i)
    (hd : 1<d) (hproper : d<e+1) (hdlen : d ∣ e+1) : ∃ u ∈ i.primeFactors, d ∣ u-1 := by
  obtain ⟨r,hr,_,hord,hpred⟩ := component_length_is_order_at_index_or_euler hp hpo hq he hepos hi hout
  rcases Finset.mem_insert.mp hr with hrq|hrI
  · subst r
    have hodd := (show Odd (e+1) from Nat.odd_iff.mpr (by have := Nat.even_iff.mp he; omega)).of_dvd_nat hdlen
    have hde : Even (d-1) := Nat.even_iff.mpr (by have := Nat.odd_iff.mp hodd; omega)
    have hsmall := (sigma_dvd_of_length_dvd hp (by omega) hdlen).trans hout
    obtain ⟨s,hs,_,hos,hps⟩ := component_length_is_order_at_index_or_euler hp hpo hq hde (by omega) hi hsmall
    rw [show d-1+1=d by omega] at hos hps
    rcases Finset.mem_insert.mp hs with hsq|hsI
    · subst s; omega
    · exact ⟨s,hsI,hps⟩
  · exact ⟨r,hrI,hdlen.trans hpred⟩

/-- Odd divisors of all index prime predecessors form the possible proper
length divisors supplied by the preceding theorem. -/
@[expose] def predecessorDivisors (i : ℕ) : Finset ℕ :=
  i.primeFactors.biUnion fun u => (u-1).divisors.filter Odd

/-- Full component lengths account for the return bound in the pure case,
and for the complementary divisor after a minimal feeding length in the
impure case. -/
@[expose] def fullLengths (i p H : ℕ) : Finset ℕ :=
  let C := (Finset.Icc (max 2 (i.factorization p)) (i.factorization p+H)).filter Even
  let V := predecessorDivisors i
  let D := i.primeFactors.biUnion (feedingLengths p)
  let F := D.biUnion fun d => (insert 1 V).image (d*·)
  C.image (·+1) ∪ F.filter (fun L : ℕ => max 2 (i.factorization p) ≤ L-1 ∧
    ∀ z : Fin L, 1<(z:ℕ) → (z:ℕ) ∣ L → (z:ℕ) ∈ V)

/-- The actual even-exponent component at any cofactor prime has a length
in the computed finite set. This includes cofactor primes outside the index. -/
theorem actual_length_mem {q a m i p H : ℕ} (hq : q.Prime) (ha : Odd a) (hm : 0<m)
    (hio : Odd i) (hp : p.Prime) (hpo : Odd p) (hpm : p ∣ m)
    (hH : (a+1).divisors.card/2 ≤ H) (hl : sigma 1 (m^2)=q^a*i)
    (hr : sigma 1 (q^a)*i=2*m^2) : 2*m.factorization p+1 ∈ fullLengths i p H := by
  let e := 2*m.factorization p
  have hv := index_prime_return_valuation hp hpo hq hm hio.pos hr
  have hem := (hp.dvd_iff_one_le_factorization hm.ne').mp hpm
  have he2 : 2 ≤ e := by dsimp [e]; omega
  have he : 0<e := by omega
  have hec : i.factorization p ≤ e := by dsimp [e]; omega
  have heven : Even e := ⟨m.factorization p,by simp [e,two_mul]⟩
  have hout := cofactor_component_sum_dvd_index_product hm hp (e:=e) rfl he hl
  change e+1 ∈ _
  by_cases hc : (sigma 1 (p^e)).Coprime i
  · obtain ⟨β,_,hβ⟩ := (Nat.dvd_prime_pow hq).mp (hc.dvd_of_dvd_mul_right hout)
    have hbound := twice_pure_exponent_excess_le_length_divisors hp hpo hq ha hm hio.pos he hβ hr
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨max_le he2 hec,by dsimp [e]; omega⟩,heven⟩,rfl⟩)
  · obtain ⟨r,hpr,hrσ,hri⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    obtain ⟨d,hd,hdpos,hdiv⟩ := exists_feeding_length hp hpr heven hrσ
    have hd2 : 1<d := by
      unfold feedingLengths at hd
      split_ifs at hd with h
      · have h' := Finset.mem_singleton.mp hd; exact h' ▸ hpr.one_lt
      · exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
    have hproper (x : ℕ) (hx : 1<x) (hlt : x<e+1) (hdx : x ∣ e+1) : x ∈ predecessorDivisors i := by
      obtain ⟨u,hu,hpred⟩ := proper_length_dvd_index_predecessor hp hpo hq heven he hio.pos.ne' hout hx hlt hdx
      have hxodd := (show Odd (e+1) from Nat.odd_iff.mpr (by have := Nat.even_iff.mp heven; omega)).of_dvd_nat hdx
      exact Finset.mem_biUnion.mpr ⟨u,hu,Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
        ⟨hpred,by have := (Nat.prime_of_mem_primeFactors hu).one_lt; omega⟩,hxodd⟩⟩
    obtain ⟨k,hk⟩ := hdiv
    have hkpos : 0<k := by
      by_contra! h
      have hz : k=0 := by omega
      simp [hz] at hk
    have hkV : k ∈ insert 1 (predecessorDivisors i) := by
      by_cases h1 : k=1
      · exact Finset.mem_insert.mpr (.inl h1)
      · have hklt : k<e+1 := by rw [hk]; simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hd2 hkpos
        exact Finset.mem_insert_of_mem (hproper k (by omega) hklt (hk ▸ dvd_mul_left _ _))
    refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨d,
      Finset.mem_biUnion.mpr ⟨r,Nat.mem_primeFactors.mpr ⟨hpr,hri,hio.pos.ne'⟩,hd⟩,
      Finset.mem_image.mpr ⟨k,hkV,hk.symm⟩⟩,?_,?_⟩)
    · simp only [Nat.add_sub_cancel]; exact max_le he2 hec
    · intro z hz hd; exact hproper z hz z.isLt hd

end OddPerfect.IndexSieve
