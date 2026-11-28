module

public import OddPerfect.HalfLengthSupport
public import OddPerfect.AlternatingPell
import all OddPerfect.AlternatingBlock
import all OddPerfect.GeometricSquareClass
import all OddPerfect.EulerSquareClass
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

public section
namespace OddPerfect
open Finset ArithmeticFunction

private theorem geometricBlock_neg_factor {x s : ℕ} (hs : Odd s) :
    geometricBlock (x^2) s=geometricBlock x s*alternatingBlock x s := by
  have h := geometricBlock_mul x 2 s
  have hh := geometricBlock_mul x s 2
  rw [mul_comm 2 s,hh] at h
  have h2 (b : ℕ) : geometricBlock b 2=b+1 := by simp [geometricBlock,sum_range_succ,Nat.add_comm]
  rw [h2,h2,←alternatingBlock_mul hs] at h
  exact Nat.mul_left_cancel (by omega : 0<x+1) (by nlinarith [h])

private theorem coprime_signed_blocks {x s : ℕ} (hx : 1<x) (hxo : Odd x) (hso : Odd s) :
    (geometricBlock x s).Coprime (alternatingBlock x s) := by
  by_contra hn
  obtain ⟨r,hr,hA,hB⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
  have hmin : r ∣ x^s-1 := by rw [←geom_sum_mul_of_one_le hx.le]; exact dvd_mul_of_dvd_left hA _
  have hplus : r ∣ x^s+1 := (alternatingBlock_mul hso ▸ dvd_mul_of_dvd_left hB _)
  have h2 := Nat.dvd_sub hplus hmin
  rw [show x^s+1-(x^s-1)=2 by have := pow_pos (by omega : 0<x) s; omega] at h2
  have hmod : geometricBlock x s%2=1 := by
    have h := Nat.ModEq.sum (s:=range s) (fun i _ => (show x ≡ 1 [MOD 2] from Nat.odd_iff.mp hxo).pow i)
    simpa [geometricBlock,Nat.ModEq,Nat.odd_iff.mp hso] using h
  exact (Nat.odd_iff.mpr hmod).not_two_dvd_nat (((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2) ▸ hA)

private theorem large_odd_valuation_prime {y s r : ℕ} (hs : s.Prime) (hr : r.Prime) (hne : r≠s)
    (hdiv : r ∣ geometricBlock y s) : s<r := by
  let : Fact r.Prime := ⟨hr⟩
  have hpow := pow_eq_one_of_dvd_block hdiv
  have hn : (y:ZMod r) ≠ 1 := by
    intro h
    have hz := cast_geometricBlock_zero hdiv
    simp [h] at hz
    exact hne ((Nat.prime_dvd_prime_iff_eq hr hs).mp ((ZMod.natCast_eq_zero_iff _ r).mp hz))
  have horder := orderOf_dvd_iff_pow_eq_one.mpr hpow
  have hfull := ((Nat.dvd_prime hs).mp horder).resolve_left (fun h => hn (orderOf_eq_one_iff.mp h))
  have h0 : (y:ZMod r) ≠ 0 := by intro h; simp [h,zero_pow hs.ne_zero] at hpow
  have hh := ZMod.orderOf_dvd_card_sub_one h0
  rw [hfull] at hh
  exact lt_of_le_of_lt (Nat.le_of_dvd (by have := hr.one_lt; omega) hh) (by have := hr.pos; omega)

private theorem signed_block_witness
    {q D s : ℕ} (hq : q.Prime) (hq4 : q%4=1) (hD : 0<D) (hs : s.Prime) (hso : Odd s) :
    ∃ r : ℕ, s<r ∧ Odd ((geometricBlock (q^(2*D)) s).factorization r) := by
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
  by_cases hrs : r=s
  · have hts : t≠s := fun h => hnot ((congrArg (fun z => z ∣ C) (h.trans hrs.symm)).mp htd)
    refine ⟨t,large_odd_valuation_prime hs ht hts (hmul ▸ dvd_mul_of_dvd_right htd _),?_⟩
    rwa [hmul,Nat.factorization_mul hA0 hC0,Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd htno,zero_add]
  · refine ⟨r,large_odd_valuation_prime hs hr hrs (hmul ▸ dvd_mul_of_dvd_left hrd _),?_⟩
    rwa [hmul,Nat.factorization_mul hA0 hC0,Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd hnot,add_zero]

private theorem common_block_prime {q D s r : ℕ} (hr : r.Prime) (hs : s.Prime)
    (hprev : r ∣ geometricBlock q (2*D)) (hnew : r ∣ geometricBlock (q^(2*D)) s) : r=s := by
  have hz := cast_geometricBlock_zero hnew
  have hbase := pow_eq_one_of_dvd_block hprev
  simp [hbase] at hz
  exact (Nat.prime_dvd_prime_iff_eq hr hs).mp ((ZMod.natCast_eq_zero_iff _ r).mp hz)

private noncomputable def largeOddPrimes (q d : ℕ) : Finset ℕ :=
  if d=1 then ∅ else (oddValuationPrimes (geometricBlock q (2*d))).filter (fun r => d.minFac<r)

private theorem paired_length_count
    {q : ℕ} (hq : q.Prime) (hq4 : q%4=1) (d : ℕ) (hdo : Odd d) :
    cardFactors d ≤ (largeOddPrimes q d).card := by
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    by_cases h1 : d=1
    · simp [h1,largeOddPrimes]
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
    obtain ⟨r,hr,hrv⟩ := signed_block_witness hq hq4 hD hs hso
    have hrT : r∈T.primeFactors := Finsupp.mem_support_iff.mpr hrv.pos.ne'
    have hrp := Nat.prime_of_mem_primeFactors hrT
    have hrn : ¬r ∣ U := fun h => hr.ne' (common_block_prime hrp hs h (Nat.dvd_of_mem_primeFactors hrT))
    have hrmem : r ∈ largeOddPrimes q d := by
      simp only [largeOddPrimes,ite_eq_right h1,mem_filter,mem_oddValuationPrimes,hm,Nat.factorization_mul hU hT,
        Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd hrn,zero_add]
      exact ⟨hrv,hr⟩
    have hrold : r ∉ largeOddPrimes q D := by
      by_cases h : D=1
      · simp [largeOddPrimes,h]
      · intro hm
        have hv := (mem_filter.mp (show r∈(oddValuationPrimes U).filter (fun t => D.minFac<t) by
          simpa [largeOddPrimes,h] using hm)).1
        exact hrn (Nat.dvd_of_mem_primeFactors (mem_filter.mp hv).1)
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
    have hcard := card_le_card (insert_subset hrmem hsub)
    rw [card_insert_of_notMem hrold] at hcard
    have hc : cardFactors d = cardFactors D+1 := by rw [←hsplit,cardFactors_mul hD.ne' hs.ne_zero,cardFactors_apply_prime hs]
    omega


/-- Multiplicity in the Euler half-length requires distinct odd-valuation
primes of the component index. For d>1, every counted prime exceeds the
smallest prime factor of d. -/
theorem euler_half_length_factors_le_large_index_odd_valuations
    {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1)
    (ha4 : a%4=1) (hqm : ¬ q∣m) (hform : N=q^a*m^2) :
    let d := (a+1)/2
    cardFactors d ≤ ((oddValuationPrimes (sigma 1 (m^2)/q^a)).filter (fun r => d.minFac<r)).card := by
  let d := (a+1)/2
  have hdo : Odd d := Nat.odd_iff.mpr (by dsimp [d]; omega)
  by_cases h1 : d=1
  · change cardFactors d ≤ _
    rw [h1]
    simp
  obtain ⟨i,hi,hleft,hright,_⟩ := exists_component_index hN hq hform (fun h => hqm (hq.dvd_of_dvd_pow h))
  dsimp only
  rw [hleft,Nat.mul_div_cancel_left i (pow_pos hq.pos _)]
  change cardFactors d ≤ ((oddValuationPrimes i).filter (fun r => d.minFac<r)).card
  apply (paired_length_count hq hq4 d hdo).trans
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
