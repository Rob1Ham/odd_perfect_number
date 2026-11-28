module

public import OddPerfect.OddGeometricSquares
public import OddPerfect.HalfLengthSupport
import all OddPerfect.HalfLengthSupport
import all OddPerfect.GeometricSquareClass
import Mathlib.FieldTheory.Finite.Basic

public section
namespace OddPerfect
open Finset ArithmeticFunction

/-- The weight of each prime in a geometric-sum length accounts for
possible overlap at primes also dividing the base minus one. -/
@[expose] def oddSourceWeight (b d : ℕ) : ℕ :=
  ∑ s∈d.primeFactors, if s∣b-1 then (d.factorization s+1)/2 else d.factorization s

private theorem prime_length_with_ramification
    {b s : ℕ} (hb : 1<b) (hs : s.Prime) (hso : Odd s) (hdiv : s∣b-1) (k : ℕ) :
    k ≤ 2*(oddValuationPrimes (geometricBlock b (s^k))).card := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases hk : k<2
    · rcases (by omega : k=0 ∨ k=1) with rfl | rfl
      · exact Nat.zero_le _
      · rw [pow_one]
        have hn : ¬IsSquare (geometricBlock b s) := by
          rw [geometricBlock_isSquare_iff_of_odd_length hb hs.one_lt hso]
          rintro ⟨rfl,rfl⟩
          exact (by decide : ¬5∣3-1) hdiv
        have := oddValuationPrimes_pos hn
        omega
    let j := k-2
    have hrel : k=j+2 := by dsimp [j]; omega
    let x := b^(s^j)
    let A := geometricBlock b (s^j)
    let C := geometricBlock x (s^2)
    have hsj := pow_pos hs.pos j
    have hx : 1<x := one_lt_pow' hb hsj.ne'
    have hn : ¬IsSquare C := by
      dsimp only [C]
      rw [geometricBlock_isSquare_iff_of_odd_length hx (one_lt_pow' hs.one_lt (by decide)) hso.pow]
      rintro ⟨_,h5⟩
      have hs3 : 3≤s := by have := hs.two_le; have := Nat.odd_iff.mp hso; omega
      nlinarith
    have hdis : Disjoint (oddValuationPrimes A) (oddValuationPrimes C) := by
      apply disjoint_left.mpr
      intro r hrA hrC
      have hr := Nat.prime_of_mem_primeFactors (mem_filter.mp hrA).1
      have hpow := pow_eq_one_of_dvd_block (Nat.dvd_of_mem_primeFactors (mem_filter.mp hrA).1)
      have hcast : (x:ZMod r)=1 := by simpa [x] using hpow
      have hz := cast_geometricBlock_zero (Nat.dvd_of_mem_primeFactors (mem_filter.mp hrC).1)
      simp [hcast] at hz
      have hrs2 : r ∣ s^2 := (ZMod.natCast_eq_zero_iff _ r).mp (by simpa using hz)
      have hrs := (Nat.prime_dvd_prime_iff_eq hr hs).mp (hr.dvd_of_dvd_pow hrs2)
      subst r
      exact (Nat.not_even_iff_odd.mpr (mem_oddValuationPrimes.mp hrC)) (even_valuation_square_length_block hx hs hso)
    have hmul : geometricBlock b (s^k)=A*C := by rw [hrel,pow_add,geometricBlock_mul]
    rw [hmul,oddValuationPrimes_card_mul_of_disjoint (geometricBlock_pos hsj).ne'
      (geometricBlock_pos (pow_pos hs.pos _)).ne' hdis]
    have hj : j≤2*(oddValuationPrimes A).card := ih j (by omega)
    have := oddValuationPrimes_pos hn
    change k≤2*((oddValuationPrimes A).card+(oddValuationPrimes C).card)
    omega

private theorem prime_length_unramified
    {b s : ℕ} (hb : 1<b) (hs : s.Prime) (hso : Odd s) (hn : ¬s∣b-1) (k : ℕ) :
    k ≤ (oddValuationPrimes (geometricBlock b (s^k))).card + (if b=3 ∧ s=5 then 1 else 0) := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    have hpos := pow_pos hs.pos j
    have hc := coprime_blocks_prime_power_length hb.le hs hn j
    by_cases he : b^(s^j)=3 ∧ s=5
    · have hb3 := ((Nat.dvd_prime Nat.prime_three).mp (he.1 ▸ dvd_pow_self b hpos.ne')).resolve_left (by omega)
      have h3 := he.1
      rw [hb3] at h3
      have hj1 : s^j=1 := (pow_right_injective₀ (by decide : 0<(3:ℕ)) (by decide : (3:ℕ)≠1)) (by simpa using h3)
      have hj0 : j=0 := by by_contra hh; exact (one_lt_pow' hs.one_lt hh).ne' hj1
      simp [hj0,hb3,he.2]
    have hnon : ¬IsSquare (geometricBlock (b^(s^j)) s) := by
      rw [geometricBlock_isSquare_iff_of_odd_length (one_lt_pow' hb hpos.ne') hs.one_lt hso]
      exact he
    have hnew := oddValuationPrimes_pos hnon
    rw [pow_succ,geometricBlock_mul,oddValuationPrimes_card_mul (geometricBlock_pos hpos).ne'
      (geometricBlock_pos hs.pos).ne' hc]
    omega

private theorem base_pow_not_one_mod {b s D : ℕ} (hb : 1<b) (hs : s.Prime) (hD : 0<D)
    (hmin : ∀ r, r.Prime → r∣D → s<r) (hn : ¬s∣b-1) : ¬s∣b^D-1 := by
  intro hd
  let : Fact s.Prime := ⟨hs⟩
  have hm := (Nat.modEq_iff_dvd' (one_le_pow₀ hb.le)).mpr hd
  have hz : (b:ZMod s)^D=1 := by
    have h := (ZMod.natCast_eq_natCast_iff' ..).mpr hm.symm
    simpa using h
  have hn0 : (b:ZMod s)≠0 := by intro H; simp [H,zero_pow hD.ne'] at hz
  have hlen := orderOf_dvd_iff_pow_eq_one.mpr hz
  have hcard := ZMod.orderOf_dvd_card_sub_one hn0
  have horder : orderOf (b:ZMod s)=1 := by
    by_contra hh
    obtain ⟨r,hr,hrd⟩ := Nat.exists_prime_and_dvd hh
    have hle := Nat.le_of_dvd (by have := hs.one_lt; omega : 0<s-1) (hrd.trans hcard)
    have := hmin r hr (hrd.trans hlen)
    omega
  have h := (ZMod.natCast_eq_natCast_iff b 1 s).mp (by simpa using orderOf_eq_one_iff.mp horder)
  exact hn ((Nat.modEq_iff_dvd' hb.le).mp h.symm)

private theorem oddSourceWeight_split {b D s k : ℕ} (hD : 0<D) (hs : s.Prime) (hk : 0<k) (hsD : ¬s∣D) :
    oddSourceWeight b (D*s^k) = oddSourceWeight b D+(if s∣b-1 then (k+1)/2 else k) := by
  have hsD' : s∉D.primeFactors := fun h => hsD (Nat.dvd_of_mem_primeFactors h)
  unfold oddSourceWeight
  rw [Nat.primeFactors_mul hD.ne' (pow_ne_zero _ hs.ne_zero),Nat.primeFactors_prime_pow hk.ne' hs,
    union_singleton,sum_insert hsD',add_comm]
  have hf (r : ℕ) : (D*s^k).factorization r=D.factorization r+(s^k).factorization r := by
    rw [Nat.factorization_mul hD.ne' (pow_ne_zero _ hs.ne_zero),Finsupp.add_apply]
  rw [hf s,Nat.factorization_eq_zero_of_not_dvd hsD,zero_add,hs.factorization_pow,Finsupp.single_eq_same]
  apply congrArg (·+_)
  apply sum_congr rfl
  intro r hr
  have hne : r≠s := by rintro rfl; exact hsD' hr
  rw [hf r,hs.factorization_pow,Finsupp.single_eq_of_ne hne,add_zero]

/-- Each off-ramification length prime contributes once per occurrence and a
ramified prime contributes once per pair, rounded upwards. The unique
positive odd-length square can cost one contribution at base three. -/
theorem oddSourceWeight_le_geometric_odd_valuations {b : ℕ} (hb : 1<b)
    (d : ℕ) (ho : Odd d) :
    oddSourceWeight b d ≤ (oddValuationPrimes (geometricBlock b d)).card+
      (if b=3 ∧ 5∣d then 1 else 0) := by
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    by_cases h1 : d=1
    · simp [h1,oddSourceWeight]
    let s := d.minFac
    let k := d.factorization s
    let D := ordCompl[s] d
    have hs := Nat.minFac_prime h1
    have hk : 0<k := (hs.dvd_iff_one_le_factorization ho.pos.ne').mp (Nat.minFac_dvd d)
    have hkp := one_lt_pow' hs.one_lt hk.ne'
    have hD : 0<D := Nat.ordCompl_pos s ho.pos.ne'
    have hDlt : D<d := Nat.div_lt_self ho.pos hkp
    have heq : D*s^k=d := (mul_comm _ _).trans (Nat.ordProj_mul_ordCompl_eq_self d s)
    have hDd : D∣d := Nat.ordCompl_dvd d s
    have hsD : ¬s∣D := Nat.not_dvd_ordCompl hs ho.pos.ne'
    have hmin (r : ℕ) (hr : r.Prime) (hd : r∣D) : s<r := by
      have hh := Nat.minFac_le_of_dvd hr.two_le (hd.trans hDd)
      exact lt_of_le_of_ne hh (fun h => hsD (h ▸ hd))
    have hc := coprime_geometricBlock_prime_pow (b:=b) hD hs k hmin
    have hor := ho.of_dvd_nat (Nat.minFac_dvd d)
    have hprev := ih D hDlt (ho.of_dvd_nat hDd)
    have hbD := one_lt_pow' hb hD.ne'
    have hlocal : (if s∣b-1 then (k+1)/2 else k) ≤ (oddValuationPrimes (geometricBlock (b^D) (s^k))).card+
        (if b=3 ∧ s=5 then 1 else 0) := by
      by_cases hsB : s∣b-1
      · have hmod := ((Nat.modEq_iff_dvd' hb.le).mpr hsB).pow D
        have hsX : s∣b^D-1 := (Nat.modEq_iff_dvd' hbD.le).mp (by simpa using hmod)
        have h := prime_length_with_ramification hbD hs hor hsX k
        change k≤2*(oddValuationPrimes (geometricBlock (b^D) (s^k))).card at h
        simp only [hsB,ite_true]
        omega
      have hnot := base_pow_not_one_mod hb hs hD hmin hsB
      have hh := prime_length_unramified hbD hs hor hnot k
      have himp (H : b^D=3 ∧ s=5) : b=3 ∧ s=5 :=
        ⟨((Nat.dvd_prime Nat.prime_three).mp (H.1 ▸ dvd_pow_self b hD.ne')).resolve_left (by omega),H.2⟩
      simp only [hsB,ite_false]
      split_ifs at hh ⊢ <;> grind
    have hcorr : (if b=3 ∧ 5∣D then 1 else 0)+(if b=3 ∧ s=5 then 1 else 0) ≤
        (if b=3 ∧ 5∣d then 1 else 0) := by
      have h5 (H : 5∣D) : 5∣d := H.trans hDd
      have h5s (H : s=5) : 5∣d := H ▸ Nat.minFac_dvd d
      split_ifs <;> grind
    have hweight : oddSourceWeight b d=oddSourceWeight b D+(if s∣b-1 then (k+1)/2 else k) :=
      (congrArg (oddSourceWeight b) heq.symm).trans (oddSourceWeight_split hD hs hk hsD)
    have hcard : (oddValuationPrimes (geometricBlock b d)).card=(oddValuationPrimes
        (geometricBlock b D)).card+(oddValuationPrimes (geometricBlock (b^D) (s^k))).card := by
      calc
        _ = (oddValuationPrimes (geometricBlock b (D*s^k))).card :=
          congrArg (fun z => (oddValuationPrimes (geometricBlock b z)).card) heq.symm
        _ = _ := by
          rw [geometricBlock_mul,oddValuationPrimes_card_mul (geometricBlock_pos hD).ne'
            (geometricBlock_pos (pow_pos hs.pos _)).ne' hc]
    rw [hweight,hcard]
    omega

end OddPerfect
