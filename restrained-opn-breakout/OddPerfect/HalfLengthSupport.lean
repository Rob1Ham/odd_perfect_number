module

public import OddPerfect.GeometricPrimePower
public import OddPerfect.Hirakawa
import all OddPerfect.GeometricSquareClass
import all OddPerfect.EulerSquareClass
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.ArithmeticFunction.Misc

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- The prime divisors of the squarefree part of a natural number. -/
@[expose] def oddValuationPrimes (n : ℕ) : Finset ℕ := n.primeFactors.filter (fun p => Odd (n.factorization p))

@[simp] theorem mem_oddValuationPrimes {n p : ℕ} :
    p ∈ oddValuationPrimes n ↔ Odd (n.factorization p) := by
  exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr h.pos.ne',h⟩⟩

private theorem oddValuationPrimes_pos {n : ℕ} (hn : ¬IsSquare n) : 0 < (oddValuationPrimes n).card := by
  obtain ⟨p,_,hv⟩ := exists_odd_valuation_of_nonsquare hn
  exact Finset.card_pos.mpr ⟨p,mem_oddValuationPrimes.mpr hv⟩

theorem oddValuationPrimes_card_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : a.Coprime b) :
    (oddValuationPrimes (a*b)).card = (oddValuationPrimes a).card+(oddValuationPrimes b).card := by
  have hn (p : ℕ) (hr : p ∈ a.primeFactors) := prime_not_dvd_other (Nat.prime_of_mem_primeFactors hr)
    hc (Nat.dvd_of_mem_primeFactors hr)
  have hdis : Disjoint (oddValuationPrimes a) (oddValuationPrimes b) := by
    apply disjoint_left.mpr
    intro p hp hp'
    exact hn p (mem_filter.mp hp).1 (Nat.dvd_of_mem_primeFactors (mem_filter.mp hp').1)
  rw [←card_union_of_disjoint hdis]
  congr 1
  ext p
  simp only [mem_union,mem_oddValuationPrimes,Nat.factorization_mul ha hb,Finsupp.add_apply]
  by_cases hp : p ∈ a.primeFactors
  · simp [Nat.factorization_eq_zero_of_not_dvd (hn p hp)]
  · have hzero : a.factorization p = 0 := Finsupp.notMem_support_iff.mp (show p ∉ a.factorization.support from hp)
    simp [hzero]

private theorem oddValuationPrimes_card_mul_of_disjoint {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hdis : Disjoint (oddValuationPrimes a) (oddValuationPrimes b)) :
    (oddValuationPrimes (a*b)).card = (oddValuationPrimes a).card+(oddValuationPrimes b).card := by
  rw [←card_union_of_disjoint hdis]
  congr 1
  ext r
  have hno : ¬(Odd (a.factorization r) ∧ Odd (b.factorization r)) :=
    fun h => disjoint_left.mp hdis (mem_oddValuationPrimes.mpr h.1) (mem_oddValuationPrimes.mpr h.2)
  simp only [mem_union,mem_oddValuationPrimes,Nat.factorization_mul ha hb,Finsupp.add_apply,Nat.odd_iff] at *
  omega

private theorem even_valuation_square_length_block {b s : ℕ} (hb : 1<b) (hs : s.Prime) (hso : Odd s) :
    Even ((geometricBlock b (s^2)).factorization s) := by
  let : Fact s.Prime := ⟨hs⟩
  by_cases hpred : s ∣ b-1
  · have hnb : ¬s ∣ b := by
      intro h
      have h1 := Nat.dvd_sub h hpred
      rw [show b-(b-1)=1 by omega] at h1
      exact hs.not_dvd_one h1
    have h := Nat.multiplicity_pow_sub_pow hso hb hpred hnb (n:=s^2) (pow_ne_zero _ hs.ne_zero)
    simp only [one_pow,Nat.multiplicity_eq_factorization hs,hs.factorization_pow,Finsupp.single_eq_same] at h
    have hgeo := geom_sum_mul_of_one_le hb.le (s^2)
    change geometricBlock b (s^2)*(b-1)=b^(s^2)-1 at hgeo
    rw [←hgeo,Nat.factorization_mul (geometricBlock_pos (pow_pos hs.pos _)).ne' (by omega),Finsupp.add_apply] at h
    exact ⟨1,by omega⟩
  · have hnd : ¬s ∣ geometricBlock b (s^2) := by
      intro h
      have hx := pow_eq_one_of_dvd_block h
      rw [ZMod.pow_card_pow] at hx
      have hm := (ZMod.natCast_eq_natCast_iff b 1 s).mp (by simpa using hx)
      exact hpred ((Nat.modEq_iff_dvd' hb.le).mp hm.symm)
    rw [Nat.factorization_eq_zero_of_not_dvd hnd]
    exact ⟨0,rfl⟩

/-- Two consecutive copies of an odd prime in the length force one new
odd-valuation divisor. The only possible shared prime has even valuation
in the new double-length block. -/
theorem prime_pow_length_le_twice_odd_valuations {p u s : ℕ} (hp : p.Prime) (hu : 0 < u)
    (hb : p^u%4=1) (hs : s.Prime) (hso : Odd s) (k : ℕ) :
    k ≤ 2*(oddValuationPrimes (geometricBlock (p^u) (s^k))).card := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases hk : k<2
    · rcases (by omega : k=0 ∨ k=1) with rfl | rfl
      · exact Nat.zero_le _
      · simp only [pow_one]
        have hn := oddValuationPrimes_pos (geometricBlock_not_square_of_prime_pow_one_mod_four hp hu hb hs.one_lt)
        omega
    let j := k-2
    have hrel : k=j+2 := by dsimp [j]; omega
    have hsj := pow_pos hs.pos j
    let X := (p^u)^(s^j)
    let A := geometricBlock (p^u) (s^j)
    let C := geometricBlock X (s^2)
    have hx : 1<X := one_lt_pow₀ (one_lt_pow₀ hp.one_lt hu.ne') hsj.ne'
    have hs2 : 1<s^2 := one_lt_pow₀ hs.one_lt (by decide)
    have hCn : ¬IsSquare C := by
      dsimp [C,X]
      rw [←pow_mul]
      exact geometricBlock_not_square_of_prime_pow_one_mod_four hp (mul_pos hu hsj)
        (by rw [pow_mul]; simpa [Nat.ModEq] using (show p^u ≡ 1 [MOD 4] from hb).pow (s^j)) hs2
    have hdis : Disjoint (oddValuationPrimes A) (oddValuationPrimes C) := by
      apply disjoint_left.mpr
      intro r hrA hrC
      have hr := Nat.prime_of_mem_primeFactors (mem_filter.mp hrA).1
      have hpow := pow_eq_one_of_dvd_block (Nat.dvd_of_mem_primeFactors (mem_filter.mp hrA).1)
      have hcast : (X:ZMod r)=1 := by simpa [X] using hpow
      have hz := cast_geometricBlock_zero (Nat.dvd_of_mem_primeFactors (mem_filter.mp hrC).1)
      simp [hcast] at hz
      have hrs2 : r ∣ s^2 := (ZMod.natCast_eq_zero_iff _ r).mp (by simpa using hz)
      have hrp := hr.dvd_of_dvd_pow hrs2
      obtain rfl := (Nat.prime_dvd_prime_iff_eq hr hs).mp hrp
      exact (Nat.not_even_iff_odd.mpr (mem_oddValuationPrimes.mp hrC)) (even_valuation_square_length_block hx hr hso)
    have hmul : geometricBlock (p^u) (s^k)=A*C := by rw [hrel,pow_add,geometricBlock_mul]
    rw [hmul,oddValuationPrimes_card_mul_of_disjoint (geometricBlock_pos hsj).ne'
      (geometricBlock_pos (pow_pos hs.pos _)).ne' hdis]
    have hj : j ≤ 2*(oddValuationPrimes A).card := ih j (by omega)
    have hc := oddValuationPrimes_pos hCn
    change k ≤ 2*((oddValuationPrimes A).card+(oddValuationPrimes C).card)
    omega

/-- Every distinct prime divisor of the length gives a separate odd valuation
in the geometric sum at any prime-power base one modulo four. -/
private theorem length_odd_valuation_counts {p u : ℕ} (hp : p.Prime) (hu : 0 < u)
    (hb : p^u%4=1) (d : ℕ) (hd : 0 < d) :
    d.primeFactors.card ≤ (oddValuationPrimes (geometricBlock (p^u) d)).card ∧
      (Odd d → cardFactors d ≤ 2*(oddValuationPrimes (geometricBlock (p^u) d)).card) := by
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    by_cases hone : d=1
    · simp [hone]
    let l := d.minFac
    let k := d.factorization l
    let D := ordCompl[l] d
    have hl : l.Prime := Nat.minFac_prime hone
    have hk : 0<k := (hl.dvd_iff_one_le_factorization hd.ne').mp (Nat.minFac_dvd d)
    have hkp : 1<l^k := one_lt_pow₀ hl.one_lt hk.ne'
    have hD : 0<D := Nat.ordCompl_pos l hd.ne'
    have hDlt : D<d := Nat.div_lt_self hd hkp
    have hsplit : D*l^k=d := (mul_comm _ _).trans (Nat.ordProj_mul_ordCompl_eq_self d l)
    have hmin (r : ℕ) (hr : r.Prime) (hrd : r ∣ D) : l<r := by
      have hle : l≤r := Nat.minFac_le_of_dvd hr.two_le (hrd.trans (Nat.ordCompl_dvd d l))
      have hne : l≠r := fun h => Nat.not_dvd_ordCompl hl hd.ne' ((congrArg (fun w => w ∣ D) h).mpr hrd)
      omega
    have hcop := coprime_geometricBlock_prime_pow (b:=p^u) hD hl k hmin
    have hn : ¬IsSquare (geometricBlock ((p^u)^D) (l^k)) := by
      rw [←pow_mul]
      exact geometricBlock_not_square_of_prime_pow_one_mod_four hp (mul_pos hu hD)
        (by rw [pow_mul]; simpa [Nat.ModEq] using (show p^u ≡ 1 [MOD 4] from hb).pow D) hkp
    have hnew := oddValuationPrimes_pos hn
    have hfirst := ih D hDlt hD
    have hnot : l ∉ D.primeFactors := fun hm => Nat.not_dvd_ordCompl hl hd.ne' (Nat.dvd_of_mem_primeFactors hm)
    rw [←hsplit,geometricBlock_mul,oddValuationPrimes_card_mul (geometricBlock_pos hD).ne'
      (geometricBlock_pos (pow_pos hl.pos _)).ne' hcop,Nat.primeFactors_mul hD.ne' (pow_ne_zero _ hl.ne_zero),
      Nat.primeFactors_prime_pow hk.ne' hl,union_singleton,card_insert_of_notMem hnot,
      cardFactors_mul hD.ne' (pow_ne_zero _ hl.ne_zero),cardFactors_apply_prime_pow hl]
    constructor
    · omega
    · intro hodd
      have hoddD := hodd.of_dvd_nat (dvd_mul_right D (l^k))
      have hoddl := hodd.of_dvd_nat ((dvd_pow_self l hk.ne').trans (dvd_mul_left _ D))
      have hprev := hfirst.2 hoddD
      have hmult : k ≤ 2*(oddValuationPrimes (geometricBlock ((p^u)^D) (l^k))).card := by
        rw [←pow_mul]
        exact prime_pow_length_le_twice_odd_valuations hp (mul_pos hu hD)
          (by rw [pow_mul]; simpa [Nat.ModEq] using (show p^u ≡ 1 [MOD 4] from hb).pow D) hl hoddl k
      omega

/-- Every distinct prime of the length contributes a distinct odd-valuation
prime to the geometric sum. -/
theorem distinct_primes_length_le_odd_valuations {p u : ℕ} (hp : p.Prime) (hu : 0 < u)
    (hb : p^u%4=1) (d : ℕ) (hd : 0 < d) :
    d.primeFactors.card ≤ (oddValuationPrimes (geometricBlock (p^u) d)).card :=
  (length_odd_valuation_counts hp hu hb d hd).1

/-- Counted with multiplicity, the odd length has at most twice as many prime
factors as the geometric sum has distinct primes of odd valuation. -/
theorem length_factor_count_le_twice_odd_valuations {p u d : ℕ} (hp : p.Prime) (hu : 0 < u)
    (hb : p^u%4=1) (hd : Odd d) :
    cardFactors d ≤ 2*(oddValuationPrimes (geometricBlock (p^u) d)).card :=
  (length_odd_valuation_counts hp hu hb d hd.pos).2 hd

private theorem coprime_blocks_prime_power_length {b l : ℕ} (hb : 0 < b) (hl : l.Prime)
    (hnot : ¬l ∣ b-1) (j : ℕ) :
    (geometricBlock b (l^j)).Coprime (geometricBlock (b^(l^j)) l) := by
  by_contra hc
  obtain ⟨r,hr,hrA,hrB⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  have hx := pow_eq_one_of_dvd_block hrA
  have hcast : ((b^(l^j):ℕ):ZMod r)=1 := by simpa using hx
  have hz := cast_geometricBlock_zero hrB
  simp [hcast] at hz
  have hrl := (ZMod.natCast_eq_zero_iff _ r).mp hz
  obtain rfl := (Nat.prime_dvd_prime_iff_eq hr hl).mp hrl
  let : Fact r.Prime := ⟨hr⟩
  rw [ZMod.pow_card_pow] at hx
  have hm := (ZMod.natCast_eq_natCast_iff b 1 r).mp (by simpa using hx)
  exact hnot ((Nat.modEq_iff_dvd' hb).mp hm.symm)

/-- If the prime length factor does not divide the base minus one, every copy
of it contributes its own distinct odd-valuation prime. -/
theorem prime_pow_length_le_odd_valuations {p u l : ℕ} (hp : p.Prime) (hu : 0 < u)
    (hb : p^u%4=1) (hl : l.Prime) (hnot : ¬l ∣ p^u-1) (k : ℕ) :
    k ≤ (oddValuationPrimes (geometricBlock (p^u) (l^k))).card := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    have hpos := pow_pos hl.pos j
    have hc := coprime_blocks_prime_power_length (pow_pos hp.pos u) hl hnot j
    have hn : ¬IsSquare (geometricBlock ((p^u)^(l^j)) l) := by
      rw [←pow_mul]
      exact geometricBlock_not_square_of_prime_pow_one_mod_four hp (mul_pos hu hpos)
        (by rw [pow_mul]; simpa [Nat.ModEq] using (show p^u ≡ 1 [MOD 4] from hb).pow (l^j)) hl.one_lt
    have hnew := oddValuationPrimes_pos hn
    rw [pow_succ,geometricBlock_mul,oddValuationPrimes_card_mul (geometricBlock_pos hpos).ne'
      (geometricBlock_pos hl.pos).ne' hc]
    omega

private theorem oddValuationPrimes_in_index {q a m i : ℕ} (hq : q.Prime) (hq4 : q%4=1)
    (ha4 : a%4=1) (hm : m ≠ 0) (hret : sigma 1 (q^a)*i=2*m^2) :
    let d := (a+1)/2
    (oddValuationPrimes i).card = (oddValuationPrimes (geometricBlock q d)).card +
      (oddValuationPrimes ((q^d+1)/2)).card := by
  let d := (a+1)/2
  let A := geometricBlock q d
  let B := (q^d+1)/2
  obtain ⟨hbal,hcop,_,_,_⟩ := euler_half_blocks hq hq4 ha4 hret
  have hne : A*B*i ≠ 0 := hbal ▸ pow_ne_zero 2 hm
  have hH := left_ne_zero_of_mul hne
  have heq : oddValuationPrimes i = oddValuationPrimes (A*B) := by
    ext r
    simp only [mem_oddValuationPrimes]
    have hh := congrArg (fun x : ℕ => x.factorization r) hbal
    rw [Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul,
      Nat.factorization_mul hH (right_ne_zero_of_mul hne),Finsupp.add_apply] at hh
    change Odd (i.factorization r) ↔ Odd ((A*B).factorization r)
    simp only [Nat.odd_iff]
    omega
  exact (congrArg card heq).trans (oddValuationPrimes_card_mul (left_ne_zero_of_mul hH) (right_ne_zero_of_mul hH) hcop)

/-- Every distinct prime of the Euler half-length demands an odd valuation in
the index, plus an additional one whenever the second half-block is nonsquare. -/
theorem euler_half_length_distinct_primes_bound {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (hqm : ¬q ∣ m) (hform : N=q^a*m^2) :
    let d := (a+1)/2
    d.primeFactors.card + (if IsSquare ((q^d+1)/2) then 0 else 1) ≤
      (oddValuationPrimes (sigma 1 (m^2)/q^a)).card := by
  dsimp only
  obtain ⟨i,_,hleft,hright,_⟩ := exists_component_index hN hq hform (fun h => hqm (hq.dvd_of_dvd_pow h))
  rw [hleft,Nat.mul_div_cancel_left i (pow_pos hq.pos _)]
  have hm := (ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _)).pos
  rw [oddValuationPrimes_in_index hq hq4 ha4 hm.ne' hright]
  apply Nat.add_le_add
  · simpa using distinct_primes_length_le_odd_valuations hq (by decide : 0<1) (by simpa using hq4)
      ((a+1)/2) (by omega)
  · split_ifs with h
    · omega
    · exact oddValuationPrimes_pos h

/-- Counting repeated prime factors of the Euler half-length still gives a
uniform lower bound for the number of odd-valuation primes of the index. -/
theorem euler_half_length_total_factors_bound {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (hqm : ¬q ∣ m) (hform : N=q^a*m^2) :
    cardFactors ((a+1)/2) ≤ 2*(oddValuationPrimes (sigma 1 (m^2)/q^a)).card := by
  obtain ⟨i,_,hleft,hright,_⟩ := exists_component_index hN hq hform (fun h => hqm (hq.dvd_of_dvd_pow h))
  rw [hleft,Nat.mul_div_cancel_left i (pow_pos hq.pos _)]
  have hm := (ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _)).pos
  rw [oddValuationPrimes_in_index hq hq4 ha4 hm.ne' hright]
  have h : cardFactors ((a+1)/2) ≤ 2*(oddValuationPrimes (geometricBlock q ((a+1)/2))).card := by
    simpa using length_factor_count_le_twice_odd_valuations hq (by decide : 0<1) (by simpa using hq4)
      (Nat.odd_iff.mpr (by omega) : Odd ((a+1)/2))
  omega

private theorem oddValuationPrimes_card_le_one {i l t : ℕ} (hi : 0 < i) (hs : i=l*t^2) (hl : l=1 ∨ l.Prime) :
    (oddValuationPrimes i).card ≤ 1 := by
  have hl0 : l ≠ 0 := by rintro rfl; simp [hs] at hi
  have ht0 : t ≠ 0 := by rintro rfl; simp [hs] at hi
  have hsub : oddValuationPrimes i ⊆ {l} := by
    intro r hr
    have hrp := Nat.prime_of_mem_primeFactors (mem_filter.mp hr).1
    have hv := mem_oddValuationPrimes.mp hr
    have hrl : r ∣ l := by
      by_contra hn
      rw [hs] at hv
      exact (Nat.not_even_iff_odd.mpr hv) (even_valuation_mul_square ht0 hl0 hn)
    rcases hl with rfl | h
    · exact (hrp.not_dvd_one hrl).elim
    · exact mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hrp h).mp hrl)
  simpa using Finset.card_le_card hsub

/-- An Euler component index equal to a square times one prime can only have
a prime or prime-square half-length. In the square case the prime must
divide the Euler prime minus one. -/
theorem prime_mul_square_index_forces_prime_power_half_length {N q a m l t : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (ha : 1<a) (hqm : ¬q ∣ m) (hform : N=q^a*m^2)
    (hl : l=1 ∨ l.Prime) (hs : sigma 1 (m^2)/q^a=l*t^2) :
    ∃ s k : ℕ, s.Prime ∧ 0<k ∧ k≤2 ∧ (a+1)/2=s^k ∧ (1<k → s ∣ q-1) := by
  let d := (a+1)/2
  have hd : 1<d := by dsimp [d]; omega
  obtain ⟨i,hi,hleft,hright,_⟩ := exists_component_index hN hq hform (fun h => hqm (hq.dvd_of_dvd_pow h))
  have hm := (ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _)).pos
  rw [hleft,Nat.mul_div_cancel_left i (pow_pos hq.pos _)] at hs
  have hcap := oddValuationPrimes_card_le_one hi hs hl
  have hcount := oddValuationPrimes_in_index hq hq4 ha4 hm.ne' hright
  have hA : (oddValuationPrimes (geometricBlock q d)).card ≤ 1 := by
    change (oddValuationPrimes i).card = (oddValuationPrimes (geometricBlock q d)).card+_ at hcount
    omega
  have hlen : d.primeFactors.card ≤ (oddValuationPrimes (geometricBlock q d)).card := by
    simpa using distinct_primes_length_le_odd_valuations hq (by decide : 0<1) (by simpa using hq4) d hd.le
  have hpos : 0 < d.primeFactors.card := card_pos.mpr ⟨d.minFac,Nat.mem_primeFactors.mpr
    ⟨Nat.minFac_prime (by omega),Nat.minFac_dvd d,(by omega)⟩⟩
  obtain ⟨s,k,hsp,hk,hpow⟩ := (isPrimePow_nat_iff d).mp (isPrimePow_iff_card_primeFactors_eq_one.mpr (by omega : d.primeFactors.card=1))
  have htotal : cardFactors d ≤ 2*(oddValuationPrimes (geometricBlock q d)).card := by
    simpa using length_factor_count_le_twice_odd_valuations hq (by decide : 0<1) (by simpa using hq4)
      (Nat.odd_iff.mpr (by dsimp [d]; omega) : Odd d)
  have heval : cardFactors d=k := by rw [←hpow,cardFactors_apply_prime_pow hsp]
  rw [heval] at htotal
  refine ⟨s,k,hsp,hk,by omega,hpow.symm,fun hk1 => ?_⟩
  by_contra hn
  have hbound : k ≤ (oddValuationPrimes (geometricBlock q (s^k))).card := by
    simpa using prime_pow_length_le_odd_valuations hq (by decide : 0<1) (by simpa using hq4) hsp (by simpa using hn) k
  rw [hpow] at hbound
  omega

/-- Any half-length with two distinct prime factors excludes the
square/prime-times-square index for every Euler prime. -/
theorem euler_index_ne_prime_mul_square_of_non_prime_power_length {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (ha : 1<a) (hqm : ¬q ∣ m) (hform : N=q^a*m^2)
    (hd : ¬IsPrimePow ((a+1)/2)) (l t : ℕ) (hl : l=1 ∨ l.Prime) :
    sigma 1 (m^2)/q^a ≠ l*t^2 := by
  intro hs
  obtain ⟨p,k,hp,hk,_,hpow,_⟩ := prime_mul_square_index_forces_prime_power_half_length hN ho hq hq4 ha4 ha hqm hform hl hs
  exact hd ((isPrimePow_nat_iff _).mpr ⟨p,k,hp,hk,hpow.symm⟩)

end OddPerfect
