module

public import OddPerfect.IndexSieveDivisors
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.FieldTheory.Finite.Basic

public section

namespace OddPerfect.IndexSieve

open Finset

/-- The least odd period can be found among divisors of the prime
predecessor. Modular exponentiation avoids constructing the base powers. -/
@[expose] def fastFeeding (p r : ℕ) : Finset ℕ :=
  if p%r=0 then ∅ else if p%r=1 then {r} else
    let S := (fastDivisors (r-1)).filter fun d => Odd d ∧ 2≤d ∧ Nat.powMod p d r=1
    if h : S.Nonempty then {S.min' h} else ∅

theorem fastFeeding_eq {p r : ℕ} (hr : r.Prime) : fastFeeding p r=feedingLengths p r := by
  let : Fact r.Prime := ⟨hr⟩
  have hrpos : 0<r-1 := by have := hr.one_lt; omega
  by_cases hz : p%r=0
  · have hn : p%r≠1 := by omega
    rw [fastFeeding,if_pos hz,feedingLengths,if_neg hn]
    symm
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro d hd
    obtain ⟨hIcc,_,hpow,_⟩ := Finset.mem_filter.mp hd
    have hd2 := (Finset.mem_Icc.mp hIcc).1
    have hdiv := dvd_pow (Nat.dvd_of_mod_eq_zero hz) (by omega : d≠0)
    have hzpow := Nat.mod_eq_zero_of_dvd hdiv
    omega
  by_cases h1 : p%r=1
  · simp [fastFeeding,feedingLengths,h1]
  let o := orderOf (p : ZMod r)
  have hcast (n : ℕ) : (p:ZMod r)^n=1 ↔ p^n%r=1 := by
    simpa only [Nat.cast_pow,Nat.cast_one,Nat.mod_eq_of_lt hr.one_lt] using ZMod.natCast_eq_natCast_iff' (p^n) 1 r
  have hnz : (p:ZMod r)≠0 := by simpa [ZMod.natCast_eq_zero_iff,Nat.dvd_iff_mod_eq_zero] using hz
  have hdvd : o∣r-1 := ZMod.orderOf_dvd_card_sub_one hnz
  have hop := Nat.pos_of_dvd_of_pos hdvd hrpos
  have ho1 : o≠1 := by
    intro heq
    apply h1
    simpa using (hcast 1).mp (by simpa using orderOf_eq_one_iff.mp heq)
  have ho2 : 2≤o := by omega
  have hlt := Nat.le_of_dvd hrpos hdvd
  let S := (fastDivisors (r-1)).filter fun d => Odd d ∧ 2≤d ∧ Nat.powMod p d r=1
  have memS (k : ℕ) : k ∈ S ↔ k∣r-1 ∧ Odd k ∧ 2≤k ∧ (p:ZMod r)^k=1 := by
    simp [S,fastDivisors_eq,Nat.mem_divisors,hrpos.ne',Nat.powMod_def,hcast]
  have hold (k : ℕ) : k ∈ feedingLengths p r ↔ k=o ∧ Odd k := by
    simp only [feedingLengths,h1,ite_false,Finset.mem_filter,Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hk,_⟩,hko,hpow,hsmall⟩
      refine ⟨((orderOf_eq_iff (by omega : 0<k)).mpr ⟨(hcast k).mpr hpow,?_⟩).symm,hko⟩
      intro j hj hjp h
      exact hsmall ⟨j,hj⟩ hjp ((hcast j).mp h)
    · rintro ⟨rfl,hko⟩
      have hmin := (orderOf_eq_iff hop).mp (rfl : orderOf (p:ZMod r)=o)
      refine ⟨⟨ho2,by omega⟩,hko,(hcast o).mp hmin.1,?_⟩
      intro j hj h
      exact hmin.2 j j.isLt hj ((hcast j).mpr h)
  simp only [fastFeeding,hz,h1,ite_false]
  change (if h:S.Nonempty then {S.min' h} else ∅)=_
  split_ifs with hS
  · have hmem := (memS _).mp (S.min'_mem hS)
    have hord : o ∣ S.min' hS := orderOf_dvd_of_pow_eq_one hmem.2.2.2
    have hoo := hmem.2.1.of_dvd_nat hord
    have hom := (memS o).mpr ⟨hdvd,hoo,ho2,pow_orderOf_eq_one _⟩
    have he : S.min' hS = o := Nat.le_antisymm (Finset.min'_le _ _ hom)
      (Nat.le_of_dvd (by have := hmem.2.2.1; omega) hord)
    ext k
    rw [Finset.mem_singleton,he,hold]
    exact ⟨fun hk => ⟨hk,hk ▸ hoo⟩,And.left⟩
  · ext k
    simp only [Finset.notMem_empty,hold,false_iff]
    rintro ⟨rfl,hko⟩
    exact hS ⟨o,(memS o).mpr ⟨hdvd,hko,ho2,pow_orderOf_eq_one _⟩⟩

/-- Compute the same full-length set by enumerating only actual divisors. -/
@[expose] def fastFullLengths (i p H : ℕ) : Finset ℕ :=
  let C := (Finset.Icc (max 2 (i.factorization p)) (i.factorization p+H)).filter Even
  let V := i.primeFactors.biUnion fun u => (fastDivisors (u-1)).filter Odd
  let D := i.primeFactors.biUnion (fastFeeding p)
  let F := D.biUnion fun d => (insert 1 V).image (d*·)
  C.image (·+1) ∪ F.filter (fun L : ℕ => max 2 (i.factorization p) ≤ L-1 ∧
    ∀ z ∈ fastDivisors L, 1<z → z<L → z ∈ V)

theorem fastFullLengths_eq (i p H : ℕ) : fastFullLengths i p H=fullLengths i p H := by
  have hD : i.primeFactors.biUnion (fastFeeding p)=i.primeFactors.biUnion (feedingLengths p) :=
    Finset.biUnion_congr rfl (fun _ hu => fastFeeding_eq (Nat.prime_of_mem_primeFactors hu))
  simp only [fastFullLengths,fullLengths,predecessorDivisors,fastDivisors_eq,hD]
  congr 1
  apply Finset.filter_congr
  intro L _
  apply and_congr_right
  intro _
  constructor
  · intro h z h1 hd
    exact h z (Nat.mem_divisors.mpr ⟨hd,by have := z.isLt; omega⟩) h1 z.isLt
  · intro h z hz h1 hlt
    exact h ⟨z,hlt⟩ h1 (Nat.dvd_of_mem_divisors hz)

end OddPerfect.IndexSieve
