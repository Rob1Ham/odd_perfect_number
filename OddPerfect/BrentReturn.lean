module

public import OddPerfect.RankBounds
import Mathlib.Data.Nat.ModEq

public section

namespace OddPerfect
open ArithmeticFunction

/-- A factor congruent to minus one modulo x leaves a cofactor congruent
to one. Once x² divides their successor, unequal quotients force cubic growth. -/
private theorem brent_cubic_product {x c b p r n : ℕ} (hx : 1 < x) (hc : 2 ≤ c) (hb : 0 < b)
    (hp : p+1=x*c) (hr : r=1+x*b) (hn : p*r+1=n) (hd : x^2 ∣ n)
    (hne : c ≠ b) : x^3 < n := by
  obtain ⟨t, ht⟩ := hd
  have he : x*(c+x*(c*b))=x*(b+x*t) := by
    nlinarith [congrArg (fun a => a*r) hp, congrArg (fun a => (x*c)*a) hr]
  have hf := Nat.eq_of_mul_eq_mul_left (by omega : 0<x) he
  have hm : c ≡ b [MOD x] := by
    change c%x=b%x
    simpa only [Nat.add_mul_mod_self_left] using congrArg (fun a => a%x) hf
  have hlarge : x ≤ c ∨ x ≤ b := by
    by_contra! h
    exact hne (hm.eq_of_lt_of_lt h.1 h.2)
  have hxp : x+1 ≤ p := by nlinarith [Nat.mul_le_mul_left x hc]
  have hxr : x+1 ≤ r := by nlinarith [Nat.mul_le_mul_left x hb]
  rcases hlarge with h | h
  · have hh : x^2 ≤ p+1 := by nlinarith [Nat.mul_le_mul_left x h]
    have hp0 : 0<p := by omega
    obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le hh
    nlinarith [Nat.mul_le_mul_left p hxr, congrArg (fun a => a*x) hv,
      Nat.le_mul_of_pos_right x (by omega : 0<x), Nat.zero_le (v*x)]
  · have hh : x^2 ≤ r := by nlinarith [Nat.mul_le_mul_left x h]
    nlinarith [Nat.mul_le_mul hxp hh, sq_pos_of_pos (by omega : 0<x)]

/-- Brent, Cohen and te Riele, Lemma 1. The source permits every positive
exponent, and the returning factor can be any odd divisor of its divisor sum. -/
theorem three_mul_le_of_sigma_dvd_return {p q k m : ℕ} (hq : q.Prime) (ho : Odd q)
    (hp : Odd p) (hd : p ∣ sigma 1 (q^k)) (hret : q^m ∣ p+1) : 3*m ≤ k := by
  by_cases hm : m=0
  · simp [hm]
  let x := q^m
  have hx : 1<x := one_lt_pow' hq.one_lt hm
  have hq3 : 3≤q := by have := hq.two_le; have := Nat.odd_iff.mp ho; omega
  obtain ⟨c, hc⟩ := hret
  change p+1=x*c at hc
  have hxc : Odd x := ho.pow
  have hcEven : Even c := by
    have he : Even (p+1) := by have := Nat.odd_iff.mp hp; exact Nat.even_iff.mpr (by omega)
    rw [hc, Nat.even_mul] at he
    exact he.resolve_left (Nat.not_even_iff_odd.mpr hxc)
  have hc2 : 2≤c := by
    have he := Nat.even_iff.mp hcEven
    have hc0 : c≠0 := by intro h; simp [h] at hc
    omega
  have hs := two_mul_sigma_prime_pow_lt_three_mul hq hq3 k
  have hpσ := Nat.le_of_dvd (sigma_pos _ _ (pow_ne_zero _ hq.ne_zero)) hd
  have hxq : x ≤ q^k := by nlinarith [Nat.mul_le_mul_left x hc2]
  have hmk := (Nat.pow_le_pow_iff_right hq.one_lt).mp hxq
  have hpow : x ∣ q^(k+1) := pow_dvd_pow q (by omega)
  obtain ⟨w, hw⟩ := hd
  let r := (q-1)*w
  have hrEven : Even r := by
    apply Even.mul_right
    exact Nat.even_iff.mpr (by have := Nat.odd_iff.mp ho; omega)
  have hw0 : 0<w := by
    have hσ := sigma_pos 1 (q^k) (pow_ne_zero _ hq.ne_zero)
    rw [hw] at hσ
    exact Nat.pos_of_mul_pos_left hσ
  have hr2 : 2≤r := by
    dsimp [r]
    exact (by omega : 2≤q-1) |>.trans (Nat.le_mul_of_pos_right _ hw0)
  have hsum := geom_sum_mul_add (q-1) (k+1)
  rw [Nat.sub_add_cancel hq.one_le, ← sigma_one_apply_prime_pow hq, hw] at hsum
  have hn : p*r+1=q^(k+1) := by dsimp [r]; nlinarith
  have hdiv1 : x ∣ p*r+1 := hn ▸ hpow
  have hdivr : x ∣ p*r+r := by
    rw [show p*r+r=(p+1)*r by ring, hc]
    exact dvd_mul_of_dvd_left (dvd_mul_right x c) r
  have hmod := (Nat.modEq_zero_iff_dvd.mpr hdiv1).trans (Nat.modEq_zero_iff_dvd.mpr hdivr).symm
  obtain ⟨b, hb⟩ := (Nat.modEq_iff_exists_eq_add (by omega : 1≤r)).mp (hmod.add_left_cancel' _)
  have hb0 : 0<b := by by_contra! hh; simp [show b=0 by omega] at hb; omega
  have hxp : x≤p := by nlinarith [Nat.mul_le_mul_left x hc2]
  have hxr : x<r := by nlinarith [Nat.mul_le_mul_left x hb0]
  have h2 : q^(2*m) < q^(k+1) := by
    rw [two_mul,pow_add,←hn]
    change x*x < p*r+1
    exact Nat.lt_succ_of_le (Nat.mul_le_mul hxp hxr.le)
  have hmk2 := (Nat.pow_lt_pow_iff_right hq.one_lt).mp h2
  have hd2 : x^2 ∣ q^(k+1) := by
    simp only [x,←pow_mul]
    apply pow_dvd_pow
    omega
  have hne : c≠b := by
    rintro rfl
    have := Nat.odd_iff.mp hp
    have := Nat.even_iff.mp hrEven
    omega
  have h3 := brent_cubic_product hx hc2 hb0 hc hb hn hd2 hne
  change (q^m)^3 < q^(k+1) at h3
  rw [←pow_mul,Nat.pow_lt_pow_iff_right hq.one_lt] at h3
  omega

end OddPerfect
