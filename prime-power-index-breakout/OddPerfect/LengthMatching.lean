module

public import OddPerfect.WeightedLength
import all OddPerfect.WeightedLength
import all OddPerfect.PairedLength
import all OddPerfect.GeometricSquareClass
import Mathlib.FieldTheory.Finite.Basic

public section
namespace OddPerfect
open Finset ArithmeticFunction

/-- The largest divisor of d supported on primes away from q²−1. -/
@[expose] def neutralLengthPart (q d : ℕ) : ℕ :=
  (d.primeFactorsList.filter (fun p => decide (¬p∣q^2-1))).prod

private theorem length_prime_dvd_sub_one {b s r : ℕ} (hs : s.Prime) (hr : r.Prime) (hne : r≠s)
    (hd : r∣geometricBlock b s) : s∣r-1 := by
  let : Fact r.Prime := ⟨hr⟩
  have hpow := pow_eq_one_of_dvd_block hd
  have hn : (b:ZMod r)≠1 := by
    intro he
    have hz := cast_geometricBlock_zero hd
    simp [he] at hz
    exact hne ((Nat.prime_dvd_prime_iff_eq hr hs).mp ((ZMod.natCast_eq_zero_iff _ r).mp hz))
  have horder := orderOf_dvd_iff_pow_eq_one.mpr hpow
  have hfull := ((Nat.dvd_prime hs).mp horder).resolve_left (fun h => hn (orderOf_eq_one_iff.mp h))
  have h0 : (b:ZMod r)≠0 := by intro he; simp [he,zero_pow hs.ne_zero] at hpow
  exact hfull ▸ ZMod.orderOf_dvd_card_sub_one h0

private theorem fresh_match {q d : ℕ} (hq : q.Prime) (hq4 : q%4=1) (hdo : Odd d) (h1 : d≠1) :
    let s := d.minFac
    let D := d/s
    ∃ W : Finset ℕ, (1+(if s∣q^2-1 then 0 else 1)≤W.card) ∧
      (∀ r∈W, s∣r-1) ∧ Disjoint W (largeOddPrimes q D) ∧
      W∪largeOddPrimes q D ⊆ largeOddPrimes q d := by
  let s := d.minFac
  let D := d/s
  have hs := Nat.minFac_prime h1
  have hsd : s∣d := Nat.minFac_dvd d
  have hDlt : D<d := Nat.div_lt_self hdo.pos hs.one_lt
  have hsplit : D*s=d := Nat.div_mul_cancel hsd
  have hD : 0<D := Nat.pos_of_ne_zero (fun h => by rw [h,zero_mul] at hsplit; exact hdo.pos.ne' hsplit.symm)
  have hDd : D∣d := hsplit ▸ dvd_mul_right D s
  have hso := hdo.of_dvd_nat hsd
  let U := geometricBlock q (2*D)
  let T := geometricBlock (q^(2*D)) s
  have hU : U ≠ 0 := (geometricBlock_pos (by omega : 0<2*D)).ne'
  have hT : T ≠ 0 := (geometricBlock_pos hs.pos).ne'
  have hm : geometricBlock q (2*d)=U*T := by
    rw [←hsplit,←mul_assoc,geometricBlock_mul]
  have hmin (p : ℕ) (hp : p.Prime) (hd : p∣D) : s≤p := Nat.minFac_le_of_dvd hp.two_le (hd.trans hDd)
  obtain ⟨W,hW,hWmem⟩ := fresh_set hq hq4 hD hs hso hmin
  have hWnew : W ⊆ largeOddPrimes q d := by
    intro r hrW
    obtain ⟨hr,hrv⟩ := hWmem r hrW
    have hrT : r∈T.primeFactors := Finsupp.mem_support_iff.mpr hrv.pos.ne'
    have hrp := Nat.prime_of_mem_primeFactors hrT
    have hrn : ¬r ∣ U := fun h => hr.ne' (common_block_prime hrp hs h (Nat.dvd_of_mem_primeFactors hrT))
    simp only [largeOddPrimes,ite_eq_right h1,mem_filter,mem_oddValuationPrimes,hm,Nat.factorization_mul hU hT,
      Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd hrn,zero_add]
    exact ⟨hrv,hr⟩
  have hdis : Disjoint W (largeOddPrimes q D) := by
    apply disjoint_left.mpr
    intro r hrW hm
    obtain ⟨hr,hrv⟩ := hWmem r hrW
    have hrT : r∈T.primeFactors := Finsupp.mem_support_iff.mpr hrv.pos.ne'
    have hrp := Nat.prime_of_mem_primeFactors hrT
    by_cases h : D=1
    · simp [largeOddPrimes,h] at hm
    · have hv := (mem_filter.mp (show r∈(oddValuationPrimes U).filter (fun t => D.minFac<t) by
        simpa [largeOddPrimes,h] using hm)).1
      exact hr.ne' (common_block_prime hrp hs (Nat.dvd_of_mem_primeFactors (mem_filter.mp hv).1) (Nat.dvd_of_mem_primeFactors hrT))
  have hsub : largeOddPrimes q D ⊆ largeOddPrimes q d := by
    by_cases h : D=1
    · simp [h,largeOddPrimes]
    · intro t ht
      have ⟨htU,htD⟩ := mem_filter.mp (show t∈(oddValuationPrimes U).filter (fun t => D.minFac<t) by
        simpa [largeOddPrimes,h] using ht)
      have hmin : s≤D.minFac := Nat.minFac_le_of_dvd (Nat.minFac_prime h).two_le ((Nat.minFac_dvd D).trans hDd)
      have htp := Nat.prime_of_mem_primeFactors (mem_filter.mp htU).1
      have htd := Nat.dvd_of_mem_primeFactors (mem_filter.mp htU).1
      have hnt : ¬t ∣ T := fun hh => (lt_of_le_of_lt hmin htD).ne' (common_block_prime htp hs htd hh)
      simp only [largeOddPrimes,ite_eq_right h1,mem_filter,mem_oddValuationPrimes,hm,Nat.factorization_mul hU hT,
        Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd hnt,add_zero]
      exact ⟨mem_oddValuationPrimes.mp htU,hmin.trans_lt htD⟩
  have hdv (r : ℕ) (hrW : r∈W) : s∣r-1 := by
    obtain ⟨hr,hrv⟩ := hWmem r hrW
    have hrT : r∈T.primeFactors := Finsupp.mem_support_iff.mpr hrv.pos.ne'
    exact length_prime_dvd_sub_one hs (Nat.prime_of_mem_primeFactors hrT) hr.ne' (Nat.dvd_of_mem_primeFactors hrT)
  exact ⟨W,hW,hdv,hdis,union_subset hWnew hsub⟩

private theorem weighted_paired_product {q : ℕ} (hq : q.Prime) (hq4 : q%4=1) (d : ℕ) (hdo : Odd d) :
    d*neutralLengthPart q d ∣ ∏ r∈largeOddPrimes q d, (r-1) := by
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    by_cases h1 : d=1
    · simp [h1,largeOddPrimes,neutralLengthPart]
    let s := d.minFac
    let D := d/s
    have hs := Nat.minFac_prime h1
    have hsd : s∣d := Nat.minFac_dvd d
    have hDlt : D<d := Nat.div_lt_self hdo.pos hs.one_lt
    have hsplit : D*s=d := Nat.div_mul_cancel hsd
    have hD : 0<D := Nat.pos_of_ne_zero (fun h => by rw [h,zero_mul] at hsplit; exact hdo.pos.ne' hsplit.symm)
    have hDd : D∣d := hsplit ▸ dvd_mul_right D s
    have hso := hdo.of_dvd_nat hsd
    have hsum := ih D hDlt (hdo.of_dvd_nat hDd)
    obtain ⟨W,hW,hdv,hdis,hUW⟩ := fresh_match hq hq4 hdo h1
    have hprodW : s^W.card ∣ ∏ r∈W, (r-1) := by
      simpa using prod_dvd_prod_of_dvd (s:=W) (fun _ => s) (fun r => r-1) hdv
    let extra := if s∣q^2-1 then 0 else 1
    have hpow : s^(1+extra) ∣ ∏ r∈W, (r-1) := (pow_dvd_pow s hW).trans hprodW
    have hpro := (Nat.mul_dvd_mul hpow hsum).trans
        ((prod_union hdis (f:=fun r : ℕ => r-1)) ▸ prod_dvd_prod_of_subset (W ∪ largeOddPrimes q D)
          (largeOddPrimes q d) (fun r : ℕ => r-1) hUW)
    have hneu : neutralLengthPart q d=neutralLengthPart q D*(if s∣q^2-1 then 1 else s) := by
      rw [←hsplit]
      have hp := (Nat.perm_primeFactorsList_mul hD.ne' hs.ne_zero).filter (fun r => decide (¬r∣q^2-1))
      unfold neutralLengthPart
      rw [hp.prod_eq,List.filter_append,List.prod_append,Nat.primeFactorsList_prime hs]
      by_cases hh : d.minFac∣q^2-1 <;> simp [s,hh]
    have hmul : d*neutralLengthPart q d=s^(1+extra)*(D*neutralLengthPart q D) := by
      calc
        _ = (D*s)*(neutralLengthPart q D*(if s∣q^2-1 then 1 else s)) :=
          congrArg₂ (·*·) hsplit.symm hneu
        _ = _ := by
          dsimp only [extra]
          by_cases h : s∣q^2-1
          · simp only [ite_eq_left h]
            ring
          · simp only [ite_eq_right h]
            ring
    exact hmul ▸ hpro

private theorem large_odd_index_subset
    {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N) (hq : q.Prime)
    (ha4 : a%4=1) (hqm : ¬q∣m) (hform : N=q^a*m^2) :
    let d := (a+1)/2
    largeOddPrimes q d ⊆ (oddValuationPrimes (sigma 1 (m^2)/q^a)).filter (fun r => d.minFac<r) := by
  let d := (a+1)/2
  have hdo : Odd d := Nat.odd_iff.mpr (by dsimp [d]; omega)
  by_cases h1 : d=1
  · change largeOddPrimes q d ⊆ _
    simp [h1,largeOddPrimes]
  obtain ⟨i,hi,hleft,hright,_⟩ := exists_component_index hN hq hform (fun h => hqm (hq.dvd_of_dvd_pow h))
  dsimp only
  rw [hleft,Nat.mul_div_cancel_left i (pow_pos hq.pos _)]
  change largeOddPrimes q d ⊆ (oddValuationPrimes i).filter (fun r => d.minFac<r)
  intro r hr
  obtain ⟨hrG,hhigh⟩ := mem_filter.mp (show r∈(oddValuationPrimes (geometricBlock q (2*d))).filter
      (fun t => d.minFac<t) by simpa [largeOddPrimes,h1] using hr)
  have hrp := Nat.prime_of_mem_primeFactors (mem_filter.mp hrG).1
  have hv := mem_oddValuationPrimes.mp hrG
  have h2 : ¬r∣2 := by
    intro h
    have he := (Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).mp h
    have := (Nat.minFac_prime h1).two_le
    omega
  have hs : sigma 1 (q^a)=geometricBlock q (2*d) := by
    rw [sigma_one_apply_prime_pow hq,show a+1=2*d by dsimp [d]; omega]; rfl
  have hG := (geometricBlock_pos (by have := hdo.pos; omega : 0<2*d) (b:=q)).ne'
  have hm := (ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _)).pos
  rw [hs] at hright
  have hf := congrArg (fun n : ℕ => n.factorization r) hright
  rw [Nat.factorization_mul hG hi.ne',Nat.factorization_mul (by decide : (2:ℕ)≠0) (pow_ne_zero _ hm.ne'),
    Finsupp.add_apply,Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd h2,Nat.factorization_pow,
    Finsupp.smul_apply,smul_eq_mul,zero_add] at hf
  exact mem_filter.mpr ⟨mem_oddValuationPrimes.mpr (Nat.odd_iff.mpr (by have := Nat.odd_iff.mp hv; omega)),hhigh⟩


/-- Prime-length factors, with an extra copy away from q²−1, divide the
product of r−1 over large odd-valuation primes of the Euler index. -/
theorem euler_half_length_dvd_large_index_predecessors
    {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1)
    (ha4 : a%4=1) (hqm : ¬q∣m) (hform : N=q^a*m^2) :
    let d := (a+1)/2
    d*neutralLengthPart q d ∣ ∏ r∈(oddValuationPrimes (sigma 1 (m^2)/q^a)).filter
        (fun r => d.minFac<r), (r-1) := by
  let d := (a+1)/2
  have hoD : Odd d := Nat.odd_iff.mpr (by dsimp [d]; omega)
  exact (weighted_paired_product hq hq4 d hoD).trans
    (prod_dvd_prod_of_subset _ _ (fun r : ℕ => r-1) (large_odd_index_subset hN ho hq ha4 hqm hform))

private theorem count_new_labels {U T : Finset ℕ} (hdis : Disjoint U T) (f : ℕ → ℕ) (s y : ℕ) :
    ((U∪T).filter (fun r => (if r∈U then s else f r)=y)).card =
      (if s=y then U.card else 0)+(T.filter (fun r => f r=y)).card := by
  let g := fun r => (if r∈U then s else f r)=y
  have hu : U.filter g=(if s=y then U else ∅) := by
    ext r
    by_cases h : s=y <;> by_cases hr : r∈U <;> simp [g,h,hr]
  have ht : T.filter g=T.filter (fun r => f r=y) := filter_congr (fun r hr => by
    have hnot : r∉U := fun h => disjoint_left.mp hdis h hr
    dsimp only [g]
    rw [ite_eq_right hnot])
  change ((U∪T).filter g).card = _
  rw [filter_union,card_union_of_disjoint (hdis.mono (filter_subset _ _) (filter_subset _ _)),hu,ht]
  split <;> simp

private theorem large_odd_matching {q : ℕ} (hq : q.Prime) (hq4 : q%4=1) (d : ℕ) (ho : Odd d) :
    ∃ T ⊆ largeOddPrimes q d, ∃ f : ℕ → ℕ, (∀ r∈T, f r∣r-1) ∧
      ∀ s, (T.filter (fun r => f r=s)).card=d.factorization s*(if s∣q^2-1 then 1 else 2) := by
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    by_cases h1 : d=1
    · exact ⟨∅,empty_subset _,fun _ => 1,by simp,by simp [h1]⟩
    let s := d.minFac
    let D := d/s
    have hs := Nat.minFac_prime h1
    have hsplit : D*s=d := Nat.div_mul_cancel (Nat.minFac_dvd d)
    have hDd : D∣d := hsplit ▸ dvd_mul_right D s
    have hD : 0<D := (ho.of_dvd_nat hDd).pos
    obtain ⟨T,hT,f,hf,hcnt⟩ := ih D (Nat.div_lt_self ho.pos hs.one_lt) (ho.of_dvd_nat hDd)
    obtain ⟨W,hW,hdv,hd,hUW⟩ := fresh_match hq hq4 ho h1
    let k := 1+(if s∣q^2-1 then 0 else 1)
    obtain ⟨U,hU,hUk⟩ := exists_subset_card_eq (show k≤W.card from hW)
    have hdis : Disjoint U T := hd.mono hU hT
    let g (r : ℕ) := if r∈U then s else f r
    refine ⟨U∪T,(union_subset_union hU hT).trans hUW,g,?_,?_⟩
    · intro r hr
      rcases mem_union.mp hr with h | h
      · simpa [g,h] using hdv r (hU h)
      · have hn : r∉U := fun hh => disjoint_left.mp hdis hh h
        simpa [g,hn] using hf r h
    intro y
    change ((U∪T).filter (fun r => (if r∈U then s else f r)=y)).card=_
    rw [count_new_labels hdis,hcnt,hUk]
    have hfac : d.factorization y=D.factorization y+(s.factorization y) :=
      (congrArg (fun z : ℕ => z.factorization y) hsplit.symm).trans
        (by rw [Nat.factorization_mul hD.ne' hs.ne_zero,Finsupp.add_apply])
    rw [hfac]
    by_cases hy : s=y
    · subst y
      rw [ite_eq_left rfl,hs.factorization_self]
      dsimp only [k]
      by_cases h : s∣q^2-1
      · simp only [ite_eq_left h]; omega
      · simp only [ite_eq_right h]; omega
    · have hz : s.factorization y=0 := by
        rw [hs.factorization, Finsupp.single_eq_of_ne (Ne.symm (show s≠y from hy))]
      rw [ite_eq_right hy,hz,add_zero,zero_add]

/-- The large odd-valuation primes can be assigned to the length primes
simultaneously. Every assignment is to a divisor of the target minus one,
and the fiber size counts the occurrences of the length prime, doubled
away from q²−1. -/
theorem exists_euler_half_length_matching
    {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1)
    (ha4 : a%4=1) (hqm : ¬q∣m) (hform : N=q^a*m^2) :
    let d := (a+1)/2
    ∃ T ⊆ (oddValuationPrimes (sigma 1 (m^2)/q^a)).filter (fun r => d.minFac<r),
      ∃ f : ℕ → ℕ, (∀ r∈T, f r∣r-1) ∧
        ∀ s, (T.filter (fun r => f r=s)).card=d.factorization s*(if s∣q^2-1 then 1 else 2) := by
  let d := (a+1)/2
  have hoD : Odd d := Nat.odd_iff.mpr (by dsimp [d]; omega)
  obtain ⟨T,hT,f,hf,hcnt⟩ := large_odd_matching hq hq4 d hoD
  exact ⟨T,hT.trans (large_odd_index_subset hN ho hq ha4 hqm hform),f,hf,hcnt⟩

end OddPerfect
