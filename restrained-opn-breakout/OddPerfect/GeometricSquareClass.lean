module

public import OddPerfect.Order
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.FieldTheory.Finite.Basic

/-! # Odd valuations at primes three modulo four in geometric sums -/

public section
namespace OddPerfect
open Finset ArithmeticFunction

/-- A natural number `3 mod 4` contains a prime `3 mod 4` to odd valuation. -/
theorem exists_three_mod_four_odd_valuation {n : ℕ} (hn : n%4=3) :
    ∃ r ∈ n.primeFactors, r%4=3 ∧ Odd (n.factorization r) := by
  by_contra H
  have hn0 : n ≠ 0 := by omega
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have hu : n ≡ 1 [MOD 4] := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn0]
    apply Nat.ModEq.prod_one
    intro r hr
    have hro := Nat.odd_iff.mp (hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr))
    rcases (by omega : r%4=1 ∨ r%4=3) with hr1 | hr3
    · simpa using (show r ≡ 1 [MOD 4] from hr1).pow (n.factorization r)
    · have hno : ¬ Odd (n.factorization r) := fun he => H ⟨r,hr,hr3,he⟩
      have hpar : n.factorization r = 2*(n.factorization r/2) := by rw [Nat.odd_iff] at hno; omega
      have hs : r^2 ≡ 1 [MOD 4] := ((show r ≡ 3 [MOD 4] from hr3).pow 2).trans (by decide)
      rw [hpar, pow_mul]
      simpa using hs.pow (n.factorization r/2)
  exact (by omega : n%4 ≠ 1) hu

/-- The primes three modulo four appearing to odd order in a positive integer. -/
@[expose] def threeOddFactors (n : ℕ) : Finset ℕ :=
  n.primeFactors.filter (fun p => p%4=3 ∧ Odd (n.factorization p))

/-- The geometric sum with `n` terms beginning at the zeroth power. -/
@[expose] def geometricBlock (b n : ℕ) : ℕ := ∑ j ∈ range n, b^j

private theorem geometricBlock_pos {b n : ℕ} (hn : 0<n) : 0 < geometricBlock b n :=
  Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨0,Finset.mem_range.mpr hn,by simp⟩

theorem geometricBlock_mul (b m n : ℕ) : geometricBlock b (m*n) = geometricBlock b m * geometricBlock (b^m) n := by
  induction n with
  | zero => simp [geometricBlock]
  | succ n ih =>
    have hnew : geometricBlock (b^m) (n+1) = geometricBlock (b^m) n + (b^m)^n := sum_range_succ _ _
    rw [Nat.mul_succ, geometricBlock, sum_range_add, ← geometricBlock, ih]
    simp_rw [pow_add]
    rw [← mul_sum, ← geometricBlock, hnew, ← pow_mul]
    ring

private theorem cast_geometricBlock_zero {b s d : ℕ} (hd : s ∣ geometricBlock b d) :
    (∑ j ∈ range d, (b : ZMod s)^j) = 0 := by
  simpa [geometricBlock] using (ZMod.natCast_eq_zero_iff _ s).mpr hd

private theorem pow_eq_one_of_dvd_block {b s d : ℕ} (hd : s ∣ geometricBlock b d) :
    (b : ZMod s)^d = 1 := by
  apply sub_eq_zero.mp
  rw [← geom_sum_mul,cast_geometricBlock_zero hd,zero_mul]

/-- Sorting the prime factors of the length from largest to smallest makes the
successive geometric blocks coprime. -/
theorem coprime_geometricBlock_prime_pow {b D l : ℕ} (hD : 0<D) (hl : l.Prime) (k : ℕ)
    (hmin : ∀ p : ℕ, p.Prime → p ∣ D → l < p) :
    (geometricBlock b D).Coprime (geometricBlock (b^D) (l^k)) := by
  by_contra hh
  obtain ⟨r,hr,hrA,hrC⟩ := Nat.Prime.not_coprime_iff_dvd.mp hh
  have hpow := pow_eq_one_of_dvd_block hrA
  have hpow' : ((b^D : ℕ) : ZMod r) = 1 := by simpa using hpow
  have hz := cast_geometricBlock_zero hrC
  simp [hpow'] at hz
  have hrl : r ∣ l^k := (ZMod.natCast_eq_zero_iff _ r).mp (by simpa using hz)
  obtain rfl := (Nat.prime_dvd_prime_iff_eq hr hl).mp (hr.dvd_of_dvd_pow hrl)
  let : Fact r.Prime := ⟨hr⟩
  have hb0 : (b : ZMod r) ≠ 0 := fun h => by simp [h,zero_pow hD.ne'] at hpow
  have horder := orderOf_dvd_iff_pow_eq_one.mpr hpow
  have hcard := ZMod.orderOf_dvd_card_sub_one hb0
  have ho : orderOf (b : ZMod r) = 1 := by
    by_contra hn
    obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd hn
    have hlt := hmin p hp (hpd.trans horder)
    have hle := Nat.le_of_dvd (by have := hr.one_lt; omega : 0<r-1) (hpd.trans hcard)
    omega
  have hbase := orderOf_eq_one_iff.mp ho
  have hzD := cast_geometricBlock_zero hrA
  simp [hbase] at hzD
  exact (lt_irrefl r) (hmin r hr ((ZMod.natCast_eq_zero_iff _ r).mp hzD))

private theorem threeOddFactors_disjoint {A B : ℕ} (hc : A.Coprime B) :
    Disjoint (threeOddFactors A) (threeOddFactors B) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hpA := (Finset.mem_filter.mp hp).1
  have hpB := (Finset.mem_filter.mp hq).1
  exact (Nat.prime_of_mem_primeFactors hpA).not_dvd_one (hc.gcd_eq_one ▸
    Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hpA) (Nat.dvd_of_mem_primeFactors hpB))

private theorem threeOddFactors_mul {A B : ℕ} (hA : A ≠ 0) (hB : B ≠ 0) (hc : A.Coprime B) :
    threeOddFactors (A*B) = threeOddFactors A ∪ threeOddFactors B := by
  ext p
  simp only [threeOddFactors, Finset.mem_filter, Nat.primeFactors_mul hA hB, Finset.mem_union,
    Nat.factorization_mul hA hB, Finsupp.add_apply]
  by_cases hpA : p ∈ A.primeFactors
  · have hnd : ¬p ∣ B := fun h => (Nat.prime_of_mem_primeFactors hpA).not_dvd_one
      (hc.gcd_eq_one ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hpA) h)
    have hpB : p ∉ B.primeFactors := fun h => hnd (Nat.dvd_of_mem_primeFactors h)
    simp [hpA,hpB,Nat.factorization_eq_zero_of_not_dvd hnd]
  · have hzero : A.factorization p = 0 := Finsupp.notMem_support_iff.mp (show p ∉ A.factorization.support from hpA)
    simp [hpA,hzero]

theorem threeOddFactors_card_mul {A B : ℕ} (hA : A ≠ 0) (hB : B ≠ 0) (hc : A.Coprime B) :
    (threeOddFactors (A*B)).card = (threeOddFactors A).card + (threeOddFactors B).card := by
  rw [threeOddFactors_mul hA hB hc, Finset.card_union_of_disjoint (threeOddFactors_disjoint hc)]

private theorem geometricBlock_modEq_one {b n : ℕ} (hb : b ≡ 1 [MOD 4]) :
    geometricBlock b n ≡ n [MOD 4] := by
  induction n with
  | zero => simp [geometricBlock,Nat.ModEq]
  | succ n ih =>
    rw [geometricBlock,sum_range_succ,← geometricBlock]
    exact ih.add (by simpa using hb.pow n)

private theorem threeOddFactors_prime_pow_le {b l : ℕ} (hb : b%4=1) (hl : l.Prime) (k : ℕ) :
    (threeOddFactors (l^k)).card ≤ (threeOddFactors (geometricBlock b (l^k))).card := by
  by_cases he : (threeOddFactors (l^k)).Nonempty
  · obtain ⟨p,hp⟩ := he
    have hsub : threeOddFactors (l^k) ⊆ {l} := by
      intro r hr
      have hh := (Finset.mem_filter.mp hr).1
      exact Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hh) hl).mp
        (Nat.Prime.dvd_of_dvd_pow (Nat.prime_of_mem_primeFactors hh) (Nat.dvd_of_mem_primeFactors hh)))
    obtain rfl := Finset.mem_singleton.mp (hsub hp)
    obtain ⟨_,hp3,hodd⟩ := Finset.mem_filter.mp hp
    rw [hl.factorization_pow,Finsupp.single_eq_same] at hodd
    obtain ⟨j,hj⟩ := hodd
    have hs : p^2 ≡ 1 [MOD 4] := ((show p ≡ 3 [MOD 4] from hp3).pow 2).trans (by decide)
    have hpow : p^k ≡ 3 [MOD 4] := by
      simpa [show k=2*j+1 by omega, pow_succ,pow_mul] using (hs.pow j).mul (show p ≡ 3 [MOD 4] from hp3)
    have h3 : geometricBlock b (p^k) %4=3 := (geometricBlock_modEq_one (show b ≡ 1 [MOD 4] from hb)).trans hpow
    obtain ⟨r,hr,hr3,hrv⟩ := exists_three_mod_four_odd_valuation h3
    have hc := Finset.card_le_card hsub
    have hh : (threeOddFactors (geometricBlock b (p^k))).Nonempty := ⟨r,Finset.mem_filter.mpr ⟨hr,hr3,hrv⟩⟩
    simpa using hc.trans (by simpa using Finset.card_pos.mpr hh : ({p}:Finset ℕ).card ≤ _)
  · simp [Finset.not_nonempty_iff_eq_empty.mp he]

/-- A geometric sum at base `1 mod 4` has at least as many distinct primes
`3 mod 4` of odd valuation as its positive length does. -/
theorem threeOddFactors_card_geometricBlock {b : ℕ} (hb : b%4=1) (d : ℕ) (hd : 0<d) :
    (threeOddFactors d).card ≤ (threeOddFactors (geometricBlock b d)).card := by
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    by_cases hone : d = 1
    · simp [hone,threeOddFactors]
    let l := d.minFac
    let k := d.factorization l
    let D := ordCompl[l] d
    have hl : l.Prime := Nat.minFac_prime hone
    have hld : l ∣ d := Nat.minFac_dvd d
    have hk : 0<k := (hl.dvd_iff_one_le_factorization hd.ne').mp hld
    have hkp : 1<l^k := one_lt_pow₀ hl.one_lt hk.ne'
    have hD : 0<D := Nat.ordCompl_pos l hd.ne'
    have hDlt : D<d := Nat.div_lt_self hd hkp
    have hsplit : D*l^k=d := (mul_comm _ _).trans (Nat.ordProj_mul_ordCompl_eq_self d l)
    have hmin (p : ℕ) (hp : p.Prime) (hpd : p ∣ D) : l<p := by
      have hle : l≤p := Nat.minFac_le_of_dvd hp.two_le (hpd.trans (Nat.ordCompl_dvd d l))
      have hne : l ≠ p := fun h => Nat.not_dvd_ordCompl hl hd.ne' ((congrArg (fun x => x ∣ D) h).mpr hpd)
      omega
    have hc : D.Coprime (l^k) := ((Nat.coprime_ordCompl hl hd.ne').symm).pow_right k
    have hcop := coprime_geometricBlock_prime_pow (b:=b) hD hl k hmin
    have hstep := threeOddFactors_prime_pow_le (b:=b^D)
      (by simpa [Nat.ModEq] using (show b ≡ 1 [MOD 4] from hb).pow D) hl k
    have hfirst := ih D hDlt hD
    rw [← hsplit, geometricBlock_mul, threeOddFactors_card_mul hD.ne' (pow_ne_zero _ hl.ne_zero) hc,
      threeOddFactors_card_mul (geometricBlock_pos hD).ne' (geometricBlock_pos (pow_pos hl.pos _)).ne' hcop]
    omega

end OddPerfect
