module

public import OddPerfect.PairedLength
import all OddPerfect.PairedLength
import all OddPerfect.GeometricSquareClass
import all OddPerfect.EulerSquareClass
import all OddPerfect.AlternatingBlock
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.List.Count

public section
namespace OddPerfect
open Finset ArithmeticFunction

/-- Occurrences of length primes away from both neighbors of q. -/
@[expose] def neutralLengthFactors (q d : ℕ) : ℕ :=
  d.primeFactorsList.countP (fun r => decide (¬r ∣ q^2-1))

private theorem neutral_prime_not_dvd_new {q D s : ℕ} (hq : q.Prime) (hs : s.Prime)
    (hD : 0<D) (hmin : ∀ r : ℕ, r.Prime → r∣D → s≤r) (hnot : ¬s∣q^2-1) :
    ¬s ∣ geometricBlock (q^(2*D)) s := by
  intro hd
  let : Fact s.Prime := ⟨hs⟩
  have hp := pow_eq_one_of_dvd_block hd
  rw [ZMod.pow_card] at hp
  have hb : ((q:ZMod s)^2)^D=1 := by simpa [pow_mul] using hp
  have hzero : (q:ZMod s)^2 ≠ 0 := by intro h; simp [h,zero_pow hD.ne'] at hb
  have hlen := orderOf_dvd_iff_pow_eq_one.mpr hb
  have hcard := ZMod.orderOf_dvd_card_sub_one hzero
  have horder : orderOf ((q:ZMod s)^2)=1 := by
    by_contra hn
    obtain ⟨r,hr,hrd⟩ := Nat.exists_prime_and_dvd hn
    have hle := hmin r hr (hrd.trans hlen)
    have hlt := Nat.le_of_dvd (by have := hs.one_lt; omega : 0<s-1) (hrd.trans hcard)
    have := hs.one_lt
    omega
  have hcast := orderOf_eq_one_iff.mp horder
  have hnat : 1 ≡ q^2 [MOD s] := (ZMod.natCast_eq_natCast_iff' ..).mp (by simpa using hcast.symm)
  exact hnot ((Nat.modEq_iff_dvd' (one_le_pow₀ hq.one_le)).mp hnat)

private theorem two_signed_witnesses {q D s : ℕ} (hq : q.Prime) (hq4 : q%4=1) (hD : 0<D)
    (hs : s.Prime) (hso : Odd s) (hn : ¬ s ∣ geometricBlock (q^(2*D)) s) :
    ∃ r t, r ≠ t ∧ s<r ∧ s<t ∧ Odd ((geometricBlock (q^(2*D)) s).factorization r) ∧
      Odd ((geometricBlock (q^(2*D)) s).factorization t) := by
  let x := q^D
  let A := geometricBlock x s
  let C := alternatingBlock x s
  have hx : 1<x := one_lt_pow' hq.one_lt hD.ne'
  have hxo : Odd x := (Nat.odd_iff.mpr (show q%2=1 by omega)).pow
  have hAn : ¬IsSquare A := geometricBlock_not_square_of_prime_pow_one_mod_four hq hD
    (by simpa [Nat.ModEq] using (show q ≡ 1 [MOD 4] from hq4).pow D) hs.one_lt
  have hCn : ¬IsSquare C := alternatingBlock_not_square hx hs.one_lt hso
  have hc := coprime_signed_blocks hx hxo hso
  have hA0 : A≠0 := (geometricBlock_pos hs.pos).ne'
  have hC0 : C≠0 := by intro h; exact hCn (h ▸ ⟨0,rfl⟩)
  have hmul : geometricBlock (q^(2*D)) s=A*C := by rw [mul_comm 2 D,pow_mul,geometricBlock_neg_factor hso]
  obtain ⟨r,hr,hrA⟩ := exists_odd_valuation_of_nonsquare hAn
  obtain ⟨t,ht,htC⟩ := exists_odd_valuation_of_nonsquare hCn
  have hrd := (hr.dvd_iff_one_le_factorization hA0).mpr hrA.pos
  have htd := (ht.dvd_iff_one_le_factorization hC0).mpr htC.pos
  have hnot := prime_not_dvd_other hr hc hrd
  have htno := prime_not_dvd_other ht hc.symm htd
  have hrT : r∣geometricBlock (q^(2*D)) s := hmul ▸ dvd_mul_of_dvd_left hrd _
  have htT : t∣geometricBlock (q^(2*D)) s := hmul ▸ dvd_mul_of_dvd_right htd _
  have hrs : r≠s := fun h => hn (h ▸ hrT)
  have hts : t≠s := fun h => hn (h ▸ htT)
  refine ⟨r,t,fun h => hnot ((congrArg (fun z => z∣C) h.symm).mp htd),
    large_odd_valuation_prime hs hr hrs hrT, large_odd_valuation_prime hs ht hts htT,?_,?_⟩
  · rwa [hmul,Nat.factorization_mul hA0 hC0,Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd hnot,add_zero]
  · rwa [hmul,Nat.factorization_mul hA0 hC0,Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd htno,zero_add]

private theorem fresh_set {q D s : ℕ} (hq : q.Prime) (hq4 : q%4=1) (hD : 0<D)
    (hs : s.Prime) (hso : Odd s) (hmin : ∀ r : ℕ, r.Prime → r∣D → s≤r) :
    ∃ W : Finset ℕ, 1+(if s∣q^2-1 then 0 else 1)≤W.card ∧
      ∀ r∈W, s<r ∧ Odd ((geometricBlock (q^(2*D)) s).factorization r) := by
  by_cases hnot : s∣q^2-1
  · obtain ⟨r,hr,hv⟩ := signed_block_witness hq hq4 hD hs hso
    exact ⟨{r},by simp [hnot],by simpa using And.intro hr hv⟩
  · obtain ⟨r,t,hrt,hr,ht,hvr,hvt⟩ := two_signed_witnesses hq hq4 hD hs hso (neutral_prime_not_dvd_new hq hs hD hmin hnot)
    refine ⟨{r,t},by simp [hnot,hrt],?_⟩
    intro z hz
    rcases (show z=r ∨ z=t by simpa using hz) with rfl | rfl
    · exact ⟨hr,hvr⟩
    · exact ⟨ht,hvt⟩

private theorem weighted_paired_count {q : ℕ} (hq : q.Prime) (hq4 : q%4=1) (d : ℕ) (hdo : Odd d) :
    cardFactors d + neutralLengthFactors q d ≤ (largeOddPrimes q d).card := by
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    by_cases h1 : d=1
    · simp [h1,largeOddPrimes,neutralLengthFactors]
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
    have hcard := card_le_card (union_subset hWnew hsub)
    rw [card_union_of_disjoint hdis] at hcard
    have hc : cardFactors d = cardFactors D+1 := by rw [←hsplit,cardFactors_mul hD.ne' hs.ne_zero,cardFactors_apply_prime hs]
    have ht : neutralLengthFactors q d = neutralLengthFactors q D+(if s∣q^2-1 then 0 else 1) := by
      rw [←hsplit]
      have hp := (Nat.perm_primeFactorsList_mul hD.ne' hs.ne_zero).countP_eq (fun p => decide (¬p∣q^2-1))
      unfold neutralLengthFactors
      rw [hp,List.countP_append,Nat.primeFactorsList_prime hs]
      by_cases h : d.minFac∣q^2-1 <;> simp [s,h]
    change 1+(if s∣q^2-1 then 0 else 1)≤W.card at hW
    omega

/-- Multiplicity in the Euler half-length requires distinct odd-valuation
primes of the component index. For d>1, every counted prime exceeds the
smallest prime factor of d. -/
theorem euler_half_length_weighted_odd_valuation_bound
    {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1)
    (ha4 : a%4=1) (hqm : ¬ q∣m) (hform : N=q^a*m^2) :
    let d := (a+1)/2
    cardFactors d + neutralLengthFactors q d ≤ ((oddValuationPrimes (sigma 1 (m^2)/q^a)).filter (fun r => d.minFac<r)).card := by
  let d := (a+1)/2
  have hdo : Odd d := Nat.odd_iff.mpr (by dsimp [d]; omega)
  by_cases h1 : d=1
  · change cardFactors d + neutralLengthFactors q d ≤ _
    rw [h1]
    simp [neutralLengthFactors]
  obtain ⟨i,hi,hleft,hright,_⟩ := exists_component_index hN hq hform (fun h => hqm (hq.dvd_of_dvd_pow h))
  dsimp only
  rw [hleft,Nat.mul_div_cancel_left i (pow_pos hq.pos _)]
  change cardFactors d + neutralLengthFactors q d ≤ ((oddValuationPrimes i).filter (fun r => d.minFac<r)).card
  apply (weighted_paired_count hq hq4 d hdo).trans
  apply card_le_card
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

end OddPerfect
