module

public import OddPerfect.Order
import OddPerfect.Euler
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.NumberTheory.Multiplicity
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum

/-! # Primitive prime divisors at odd prime-power lengths -/

public section

namespace OddPerfect

open Finset

private theorem prime_lt_geom_sum {b l : ℕ} (hb : 1 < b) (hl : l.Prime) :
    l < ∑ i ∈ range l, b ^ i := by
  calc
    l = ∑ _i ∈ range l, 1 := by simp
    _ < _ := Finset.sum_lt_sum (fun i _ => Nat.one_le_pow i b (by omega))
      ⟨1, mem_range.mpr hl.one_lt, by simpa using hb⟩

private theorem cast_geom_sum_zero {b l r : ℕ} (hd : r ∣ ∑ i ∈ range l, b ^ i) :
    (∑ i ∈ range l, (b : ZMod r) ^ i) = 0 := by
  simpa only [Nat.cast_sum, Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ r).mpr hd

private theorem pow_eq_one_of_dvd_geom_sum {b l r : ℕ} (hd : r ∣ ∑ i ∈ range l, b ^ i) :
    (b : ZMod r) ^ l = 1 := by
  apply sub_eq_zero.mp
  rw [← geom_sum_mul, cast_geom_sum_zero hd, zero_mul]

/-- At odd prime length `l`, the exceptional prime `l` can divide the geometric
sum only once. This uses Fermat in `ZMod l` and geometric-sum lifting over `ℤ`. -/
theorem not_sq_dvd_geom_sum {b l : ℕ} (hl : l.Prime) (hodd : Odd l)
    (hd : l ∣ ∑ i ∈ range l, b ^ i) : ¬ l ^ 2 ∣ ∑ i ∈ range l, b ^ i := by
  let : Fact l.Prime := ⟨hl⟩
  have hb : (b : ZMod l) = 1 := (ZMod.pow_card (b : ZMod l)).symm.trans
    (pow_eq_one_of_dvd_geom_sum hd)
  have hsub : (l : ℤ) ∣ (b : ℤ) - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp [hb]
  have hnd : ¬ (l : ℤ) ∣ (b : ℤ) := by
    rw [Int.natCast_dvd_natCast, ← ZMod.natCast_eq_zero_iff, hb]; exact one_ne_zero
  have hval := emultiplicity_geom_sum₂_eq_one (Nat.prime_iff_prime_int.mp hl) hodd hsub hnd
  have hval' : emultiplicity (l : ℤ) (∑ i ∈ range l, (b : ℤ) ^ i) = (1 : ℕ) := by simpa using hval
  have hn := (emultiplicity_eq_coe.mp hval').2
  intro H
  apply hn
  exact_mod_cast H

private theorem exists_other_prime_dvd_geom_sum {b l : ℕ} (hb : 1 < b) (hl : l.Prime)
    (hodd : Odd l) : ∃ r : ℕ, r.Prime ∧ r ≠ l ∧ r ∣ ∑ i ∈ range l, b ^ i := by
  have hlt := prime_lt_geom_sum hb hl
  by_cases hdiv : l ∣ ∑ i ∈ range l, b ^ i
  · obtain ⟨u, hu⟩ := hdiv
    have hu1 : u ≠ 1 := by rintro rfl; simp [hu] at hlt
    obtain ⟨r, hr, hru⟩ := Nat.exists_prime_and_dvd hu1
    refine ⟨r, hr, ?_, hru.trans (hu ▸ dvd_mul_left _ _)⟩
    rintro rfl
    apply not_sq_dvd_geom_sum hl hodd (hu ▸ dvd_mul_right _ _)
    rw [hu, pow_two]; exact Nat.mul_dvd_mul_left _ hru
  · obtain ⟨r, hr, hrs⟩ := Nat.exists_prime_and_dvd (by have := hl.one_lt; omega : (∑ i ∈ range l, b ^ i) ≠ 1)
    exact ⟨r, hr, fun h => hdiv (h ▸ hrs), hrs⟩

/-- Odd prime-power case of Bang–Zsigmondy for any integral base above one.
There is a prime whose first return to one has exponent exactly `l^(k+1)`. -/
theorem exists_prime_order_prime_pow {b l : ℕ} (hb : 1 < b) (hl : l.Prime) (hodd : Odd l) (k : ℕ) :
    ∃ r : ℕ, r.Prime ∧ orderOf (b : ZMod r) = l ^ (k + 1) ∧ l ^ (k + 1) ∣ r - 1 := by
  let : Fact l.Prime := ⟨hl⟩
  let x := b ^ (l ^ k)
  have hx : 1 < x := one_lt_pow₀ hb (pow_ne_zero _ hl.ne_zero)
  obtain ⟨r, hr, hrl, hd⟩ := exists_other_prime_dvd_geom_sum hx hl hodd
  let : Fact r.Prime := ⟨hr⟩
  have hx1 : (x : ZMod r) ≠ 1 := by
    intro h
    have hs := cast_geom_sum_zero hd
    simp [h] at hs
    exact hrl ((Nat.prime_dvd_prime_iff_eq hr hl).mp ((ZMod.natCast_eq_zero_iff l r).mp hs))
  have hxpow := pow_eq_one_of_dvd_geom_sum hd
  have hnot : (b : ZMod r) ^ (l ^ k) ≠ 1 := by simpa [x] using hx1
  have hfin : (b : ZMod r) ^ l ^ (k + 1) = 1 := by simpa [x, pow_succ l k, pow_mul] using hxpow
  have horder := orderOf_eq_prime_pow hnot hfin
  refine ⟨r, hr, horder, horder ▸ ZMod.orderOf_dvd_card_sub_one ?_⟩
  intro hz
  rw [hz, zero_pow (pow_ne_zero _ hl.ne_zero)] at hfin
  exact zero_ne_one hfin

/-- A realized nontrivial order dividing an exact component length forces its modulus into `N`. -/
theorem forced_mem_erase_of_order {N p e r d : ℕ} (hN : N.Perfect) (hp : p.Prime)
    (he : N.factorization p = e) (hr : r.Prime) (hd : 1 < d) (hor : orderOf (p : ZMod r) = d)
    (hcon : d ∣ r-1) (hlen : d ∣ e+1) : r ∈ N.primeFactors.erase p := by
  let : Fact r.Prime := ⟨hr⟩
  have hr3 : 2 < r := by have := Nat.le_of_dvd (by have := hr.one_lt; omega) hcon; omega
  have hh : Odd r := hr.odd_of_ne_two (by omega)
  have hrp : r ≠ p := by
    rintro rfl
    rw [ZMod.natCast_self, orderOf_zero] at hor
    omega
  have how : (p : ZMod r) ≠ 1 := by rintro h; simp [h] at hor; omega
  have hdiv : r ∣ N := by
    apply dvd_perfect_of_order_test hN hp hr hh
      ((hp.pow_dvd_iff_le_factorization hN.2.ne').mpr he.ge)
      (fun h => by have := (hp.pow_dvd_iff_le_factorization hN.2.ne').mp h; omega)
    simpa [how, hor] using hlen
  exact mem_erase.mpr ⟨hrp, Nat.mem_primeFactors.mpr ⟨hr, hdiv, hN.2.ne'⟩⟩

/-- A divisor of the component length `e+1` which is a positive power of an
odd prime forces a distinct prime of `N` with precisely this multiplicative order. -/
theorem exists_forced_prime_order_prime_pow {N p e l : ℕ} (hN : N.Perfect) (hp : p.Prime)
    (he : N.factorization p = e) (hl : l.Prime) (hodd : Odd l) (k : ℕ) (hlen : l ^ (k+1) ∣ e+1) :
    ∃ r ∈ N.primeFactors, r ≠ p ∧ orderOf (p : ZMod r) = l ^ (k+1) ∧ l ^ (k+1) ∣ r-1 := by
  obtain ⟨r, hr, hor, hcon⟩ := exists_prime_order_prime_pow hp.one_lt hl hodd k
  have hd : 1 < l ^ (k+1) := one_lt_pow₀ hl.one_lt (by omega)
  obtain ⟨hrp, hrN⟩ := mem_erase.mp (forced_mem_erase_of_order hN hp he hr hd hor hcon hlen)
  exact ⟨r, hrN, hrp, hor, hcon⟩

/-- At an odd perfect number, Euler's mod-four condition handles the possible
length-two exception. Consequently every prime-power divisor of the length is realized. -/
theorem exists_forced_order_of_prime_pow_length {N p e l : ℕ} (hN : N.Perfect) (hNo : Odd N)
    (hp : p.Prime) (he : N.factorization p = e) (hl : l.Prime) (k : ℕ) (hlen : l ^ (k+1) ∣ e+1) :
    ∃ r ∈ N.primeFactors.erase p, orderOf (p : ZMod r) = l ^ (k+1) := by
  rcases eq_or_ne l 2 with rfl | hl2
  · have h2 : 2 ∣ e+1 := (dvd_pow_self 2 (by omega : k+1 ≠ 0)).trans hlen
    obtain ⟨s, _, hs4, hse, hother⟩ := euler_exponents hNo hN
    have hps : p = s := by
      by_contra h
      have := Nat.even_iff.mp (hother p h)
      omega
    subst s
    have hk : k = 0 := by
      by_contra h
      have h4 : 4 ∣ e+1 := (pow_dvd_pow 2 (by omega : 2 ≤ k+1)).trans hlen
      omega
    subst k
    simp only [zero_add, pow_one] at hlen ⊢
    have hp2 := hp.two_le
    let u := (p+1)/2
    have hu1 : 1 < u := by dsimp [u]; omega
    obtain ⟨r, hr, hru⟩ := Nat.exists_prime_and_dvd hu1.ne'
    have huodd : Odd u := Nat.odd_iff.mpr (by dsimp [u]; omega)
    have hro := huodd.of_dvd_nat hru
    have hr2 : r ≠ 2 := by rintro rfl; exact hro.not_two_dvd_nat dvd_rfl
    let : Fact r.Prime := ⟨hr⟩
    have hrp : r ∣ p+1 := hru.trans ⟨2, by dsimp [u]; omega⟩
    have hgeom : r ∣ ∑ i ∈ range 2, p ^ i := by simpa [sum_range_succ, add_comm] using hrp
    have hne : (p : ZMod r) ≠ 1 := by
      intro h
      have hs := cast_geom_sum_zero hgeom
      have hz : ((2 : ℕ) : ZMod r) = 0 := by simpa [h] using hs
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff _ _).mp hz))
    have hor : orderOf (p : ZMod r) = 2 := orderOf_eq_prime (pow_eq_one_of_dvd_geom_sum hgeom) hne
    have hcon : 2 ∣ r-1 := by have := Nat.odd_iff.mp hro; omega
    exact ⟨r, forced_mem_erase_of_order hN hp he hr (by decide) hor hcon hlen, hor⟩
  · obtain ⟨r, hr, hrp, hor, _⟩ := exists_forced_prime_order_prime_pow hN hp he hl (hl.odd_of_ne_two hl2) k hlen
    exact ⟨r, mem_erase.mpr ⟨hrp, hr⟩, hor⟩

private theorem count_orders {N p e : ℕ} (S : Finset ℕ) (hs : S ⊆ (e+1).primeFactors)
    (hforce : ∀ l ∈ S, ∀ k, l ^ (k+1) ∣ e+1 → ∃ r ∈ N.primeFactors.erase p,
      orderOf (p : ZMod r) = l ^ (k+1)) :
    ∑ l ∈ S, (e+1).factorization l ≤ (N.primeFactors.erase p).card := by
  classical
  let lengths := S.sigma (fun l => range ((e+1).factorization l))
  let orders := (N.primeFactors.erase p).image (fun r => orderOf (p : ZMod r))
  have hbound : lengths.card ≤ orders.card := by
    apply card_le_card_of_injOn (fun z : (Σ _ : ℕ, ℕ) => z.1 ^ (z.2 + 1))
    · rintro ⟨l, k⟩ hz
      obtain ⟨hl, hk⟩ := mem_sigma.mp hz
      have hlp := Nat.prime_of_mem_primeFactors (hs hl)
      have hd := (hlp.pow_dvd_iff_le_factorization (by omega : e+1 ≠ 0)).mpr
        (mem_range.mp hk : k+1 ≤ (e+1).factorization l)
      obtain ⟨r, hr, ho⟩ := hforce l hl k hd
      exact mem_image.mpr ⟨r, hr, ho⟩
    · rintro ⟨l,k⟩ hkl ⟨r,j⟩ hrj h
      have hprime {l k : ℕ} (hm : Sigma.mk (β := fun _ : ℕ => ℕ) l k ∈ lengths) : l.Prime :=
        Nat.prime_of_mem_primeFactors (hs (mem_sigma.mp hm).1)
      obtain ⟨rfl,rfl⟩ := (hprime hkl).pow_inj (hprime hrj) h
      rfl
  simpa [lengths, Finset.card_sigma] using hbound.trans (card_image_le (s := N.primeFactors.erase p))

/-- In any perfect number, each odd prime factor of the length counted with
multiplicity costs a distinct prime other than the base. -/
theorem odd_length_factor_count_bound {N p e : ℕ} (hN : N.Perfect) (hp : p.Prime)
    (he : N.factorization p = e) :
    ∑ l ∈ (e+1).primeFactors.erase 2, (e+1).factorization l ≤ (N.primeFactors.erase p).card := by
  apply count_orders _ (erase_subset _ _)
  intro l hl k hd
  obtain ⟨hl2, hmem⟩ := mem_erase.mp hl
  have hlp := Nat.prime_of_mem_primeFactors hmem
  obtain ⟨r, hr, hrp, hor, _⟩ := exists_forced_prime_order_prime_pow hN hp he hlp (hlp.odd_of_ne_two hl2) k hd
  exact ⟨r, mem_erase.mpr ⟨hrp, hr⟩, hor⟩

/-- For every prime-power component `p^e` of an odd perfect number, the total
number of prime factors of `e+1`, with repetitions, is bounded by the number of
other distinct primes dividing the perfect number. -/
theorem length_factor_count_bound {N p : ℕ} (hN : N.Perfect) (hNo : Odd N) (hp : p.Prime) :
    (N.factorization p + 1).primeFactorsList.length ≤ (N.primeFactors.erase p).card := by
  rw [← ArithmeticFunction.cardFactors_apply, ArithmeticFunction.cardFactors_eq_sum_factorization]
  apply count_orders _ (fun _ h => h)
  intro l hl k hd
  exact exists_forced_order_of_prime_pow_length hN hNo hp rfl (Nat.prime_of_mem_primeFactors hl) k hd

end OddPerfect
