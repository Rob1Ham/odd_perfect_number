module

public import OddPerfect.AlternatingBlock
import all OddPerfect.AlternatingBlock
public import OddPerfect.PellCoordinates
import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Algebra.BigOperators.ModEq

public section

namespace OddPerfect
open Finset

private theorem small_valuation_odd_index {p j : ℕ} (hp : p.Prime) (hp5 : 5≤p) (hj : 0<j) :
    (2*j+1).factorization p < j := by
  have hg (t : ℕ) : 2*(t+1)+1 < p^(t+1) := by
    induction t with
    | zero => simp; omega
    | succ t ih =>
      rw [pow_succ]
      have h := Nat.mul_le_mul_right (p^(t+1)) hp5
      nlinarith [mul_comm p (p^(t+1))]
  by_contra! h
  have hd := (hp.pow_dvd_iff_le_factorization (by omega : 2*j+1 ≠ 0)).mpr h
  have hb := Nat.le_of_dvd (by omega : 0<2*j+1) hd
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  exact (hg t).not_ge hb

private theorem higher_choose_term_dvd {p m j D : ℕ} (hp : p.Prime) (hp5 : 5≤p) (hj : 0<j)
    (hi : 2*j+1 ≤ m) (hd : p ∣ D) :
    p^(m.factorization p+1) ∣ m.choose (2*j+1)*D^j := by
  by_cases hD : D=0
  · simp [hD,zero_pow hj.ne']
  have hI : 2*j+1 ≠ 0 := by omega
  have hc := (Nat.choose_pos hi).ne'
  have hm : m ≠ 0 := by omega
  have hmul : m ∣ m.choose (2*j+1)*(2*j+1) := by
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    exact ⟨n.choose (2*j),(Nat.add_one_mul_choose_eq n (2*j)).symm⟩
  have hv := (Nat.factorization_le_iff_dvd hm (mul_ne_zero hc hI)).mpr hmul p
  rw [Nat.factorization_mul hc hI,Finsupp.add_apply] at hv
  have hlow := small_valuation_odd_index hp hp5 hj
  have hD1 := (hp.dvd_iff_one_le_factorization hD).mp hd
  apply (hp.pow_dvd_iff_le_factorization (mul_ne_zero hc (pow_ne_zero _ hD))).mpr
  rw [Nat.factorization_mul hc (pow_ne_zero _ hD),Finsupp.add_apply,Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul]
  have hJ := Nat.mul_le_mul_left j hD1
  omega

private def quadraticIm (D : ℤ) : ℤ√D →+ ℤ where
  toFun := Zsqrtd.im
  map_zero' := rfl
  map_add' := by intros; rfl

private theorem quadratic_sqrtd_even (D : ℤ) (j : ℕ) :
    (Zsqrtd.sqrtd : ℤ√D)^(2*j)=((D^j:ℤ):ℤ√D) := by
  rw [pow_mul,pow_two,Zsqrtd.dmuld,Int.cast_pow]

private theorem quadratic_sqrtd_odd_im (D : ℤ) (j : ℕ) :
    ((Zsqrtd.sqrtd : ℤ√D)^(2*j+1)).im=D^j := by
  rw [pow_succ,quadratic_sqrtd_even,Zsqrtd.im_mul,Zsqrtd.re_intCast,Zsqrtd.im_intCast]
  simp

/-- Modulo one power of p beyond the valuation of m, the imaginary
coordinate of (A+√D)^m has just its linear binomial term when p≥5 divides D. -/
theorem quadratic_im_mod_prime_power {p A D m : ℕ} (hp : p.Prime) (hp5 : 5≤p) (hm : 0<m) (hd : p∣D) :
    (((⟨A,1⟩ : ℤ√(D:ℤ))^m).im) ≡ m*(A:ℤ)^(m-1) [ZMOD ((p:ℤ)^(m.factorization p+1))] := by
  let M := (p:ℤ)^(m.factorization p+1)
  let T (i : ℕ) := ((Zsqrtd.sqrtd : ℤ√(D:ℤ)) ^ i * (A:ℤ√(D:ℤ)) ^ (m-i) * (m.choose i:ℤ√(D:ℤ))).im
  have hexp : ((⟨(A:ℤ),1⟩ : ℤ√(D:ℤ))^m).im = ∑ i ∈ range (m+1), T i := by
    have hsplit : (⟨(A:ℤ),1⟩ : ℤ√(D:ℤ)) = Zsqrtd.sqrtd+(A:ℤ√(D:ℤ)) := by ext <;> simp
    change quadraticIm _ _ = _
    rw [hsplit,add_pow,map_sum]
    rfl
  have hterm (i : ℕ) (hi : i∈range (m+1)) : T i ≡ (if i=1 then (m:ℤ)*(A:ℤ)^(m-1) else 0) [ZMOD M] := by
    have ht : T i = ((Zsqrtd.sqrtd : ℤ√(D:ℤ))^i).im * (A:ℤ)^(m-i) * (m.choose i:ℤ) := by
      dsimp [T]
      have hA : (A:ℤ√(D:ℤ))^(m-i) = ((A^(m-i):ℕ):ℤ√(D:ℤ)) := (Nat.cast_pow ..).symm
      rw [hA]
      simp only [Zsqrtd.im_natCast,Zsqrtd.re_natCast,mul_zero,zero_add]
      push_cast
      ring
    rw [ht]
    by_cases hi1 : i=1
    · subst i
      simp [mul_comm]
    rw [ite_eq_right hi1,Int.modEq_zero_iff_dvd]
    rcases Nat.even_or_odd i with he | ho
    · obtain ⟨j,hj⟩ := he
      rw [show i=2*j by omega,quadratic_sqrtd_even,Zsqrtd.im_intCast]
      simp
    · obtain ⟨j,hj⟩ := ho
      have hj0 : 0<j := by omega
      have him : 2*j+1≤m := by have := mem_range.mp hi; omega
      rw [show i=2*j+1 by omega,quadratic_sqrtd_odd_im]
      have H := higher_choose_term_dvd hp hp5 hj0 him hd
      have H' : M ∣ (m.choose (2*j+1):ℤ)*(D:ℤ)^j := by dsimp [M]; exact_mod_cast H
      convert dvd_mul_of_dvd_left H' ((A:ℤ)^(m-(2*j+1))) using 1; ring
  have hs := Int.ModEq.sum (s:=range (m+1)) hterm
  rw [hexp]
  simpa [M,hm] using hs


private theorem power_coordinates {x : ℕ} (j : ℕ) :
    let w : ℤ√((x*(x+1):ℕ):ℤ) := ⟨x+1,1⟩
    (w^(2*j+1)).re=((x:ℤ)+1)^(j+1)*(alternatingPellCoordinates x j).1 ∧
    (w^(2*j+1)).im=((x:ℤ)+1)^j*(alternatingPellCoordinates x j).2 := by
  let w : ℤ√((x*(x+1):ℕ):ℤ) := ⟨x+1,1⟩
  have hr : (w^2).re = ((x:ℤ)+1)*(2*x+1) := by
    rw [pow_two,Zsqrtd.re_mul]; dsimp only [w]; push_cast; ring
  have hi : (w^2).im = 2*((x:ℤ)+1) := by
    rw [pow_two,Zsqrtd.im_mul]; dsimp only [w]; ring
  change (w^(2*j+1)).re=_ ∧ (w^(2*j+1)).im=_
  induction j with
  | zero => simp [w,alternatingPellCoordinates]
  | succ j ih =>
    rw [show 2*(j+1)+1=(2*j+1)+2 by omega,pow_add,Zsqrtd.re_mul,Zsqrtd.im_mul,hr,hi,ih.1,ih.2]
    simp only [alternatingPellCoordinates,pow_succ]
    push_cast
    constructor <;> ring

/-- At primes at least five dividing x, every prime power dividing the
second Pell coordinate divides the exponent 2j+1. -/
theorem alternatingPellCoordinates_pow_dvd_length {x p k : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    (hpx : p∣x) (j : ℕ) (hdiv : (p:ℤ)^k ∣ (alternatingPellCoordinates x j).2) :
    p^k ∣ 2*j+1 := by
  let m := 2*j+1
  have hm : 0<m := by dsimp [m]; omega
  let v := m.factorization p
  apply (hp.pow_dvd_iff_le_factorization hm.ne').mpr
  by_contra! hk
  have hv : v+1 ≤ k := by change m.factorization p+1 ≤ k; exact hk
  have hd : p ∣ x*(x+1) := dvd_mul_of_dvd_left hpx _
  have hc := quadratic_im_mod_prime_power (A:=x+1) hp hp5 hm hd
  have him := (power_coordinates (x:=x) j).2
  push_cast at hc
  change _ ≡ (m:ℤ)*((x:ℤ)+1)^(m-1) [ZMOD (p:ℤ)^(v+1)] at hc
  change _ = ((x:ℤ)+1)^j*(alternatingPellCoordinates x j).2 at him
  rw [him] at hc
  have ht := (pow_dvd_pow (p:ℤ) hv).trans hdiv
  have hzero := Int.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right ht (((x:ℤ)+1)^j))
  have hpow : (p:ℤ)^(v+1) ∣ (m:ℤ)*((x:ℤ)+1)^(m-1) := Int.modEq_zero_iff_dvd.mp (hc.symm.trans hzero)
  have hnat : p^(v+1) ∣ m*(x+1)^(m-1) := by exact_mod_cast hpow
  have hf := (hp.pow_dvd_iff_le_factorization (mul_ne_zero hm.ne' (pow_ne_zero _ (by omega)))).mp hnat
  have hn : ¬p ∣ x+1 := fun h => hp.not_dvd_one ((Nat.dvd_add_iff_right hpx).mpr h)
  rw [Nat.factorization_mul hm.ne' (pow_ne_zero _ (by omega)),Finsupp.add_apply,Nat.factorization_pow,
    Finsupp.smul_apply,Nat.factorization_eq_zero_of_not_dvd hn,smul_eq_mul,mul_zero,add_zero] at hf
  change m.factorization p+1≤_ at hf
  omega

private theorem alternatingPellCoordinates_odd_snd (x : ℤ) (j : ℕ) : Odd (alternatingPellCoordinates x j).2 := by
  induction j with
  | zero => exact odd_one
  | succ j ih =>
    obtain ⟨u,hu⟩ := ih
    refine ⟨(x+1)*(alternatingPellCoordinates x j).1+2*x*u+x+u,?_⟩
    simp only [alternatingPellCoordinates,hu]
    ring

private theorem three_dvd_length {x : ℕ} (hx : 3∣x) (j : ℕ) :
    (alternatingPellCoordinates x j).1 ≡ 1 [ZMOD 3] ∧
     (alternatingPellCoordinates x j).2 ≡ 2*j+1 [ZMOD 3] := by
  have hx0 : (x:ℤ) ≡ 0 [ZMOD 3] := Int.modEq_zero_iff_dvd.mpr (by exact_mod_cast hx)
  induction j with
  | zero => simp [alternatingPellCoordinates]
  | succ j ih =>
    simp only [alternatingPellCoordinates,Nat.cast_succ]
    have h2 := (Int.ModEq.refl 2).mul hx0
    have h3 := h2.add (Int.ModEq.refl 1)
    have h4 := (Int.ModEq.refl 2).mul (hx0.add (Int.ModEq.refl 1))
    constructor
    · simpa using (h3.mul ih.1).add (h2.mul ih.2)
    · convert (h4.mul ih.1).add (h3.mul ih.2) using 1; ring

private theorem pell_three_step (x : ℤ) (j : ℕ) :
    (alternatingPellCoordinates x (j+3)).2 ≡ (alternatingPellCoordinates x j).2 [ZMOD 4*x+3] := by
  apply Int.modEq_iff_dvd.mpr
  refine ⟨-((4*x+1)*2*(x+1)*(alternatingPellCoordinates x j).1
    +(8*x^2+6*x)*(alternatingPellCoordinates x j).2),?_⟩
  simp only [alternatingPellCoordinates]
  ring

private theorem three_index_forces_divisor (x : ℤ) (j : ℕ) :
    (4*x+3) ∣ (alternatingPellCoordinates x (3*j+1)).2 := by
  induction j with
  | zero => refine ⟨1,?_⟩; simp [alternatingPellCoordinates]; ring
  | succ j ih =>
    rw [show 3*(j+1)+1=(3*j+1)+3 by omega]
    exact Int.modEq_zero_iff_dvd.mp ((pell_three_step _ _).trans (Int.modEq_zero_iff_dvd.mpr ih))

private theorem exceptional_three {x h j : ℕ} (hx : Odd x) (hx3 : 3∣x) (hh : 0<h)
    (he : (alternatingPellCoordinates x j).2=(x:ℤ)^h) : False := by
  have hz : (3:ℤ) ∣ (alternatingPellCoordinates x j).2 := by
    rw [he]
    exact_mod_cast hx3.trans (dvd_pow_self x hh.ne')
  have hlen := Int.modEq_zero_iff_dvd.mp ((three_dvd_length hx3 j).2.symm.trans (Int.modEq_zero_iff_dvd.mpr hz))
  have hn : 3 ∣ 2*j+1 := by exact_mod_cast hlen
  have hj : j=3*(j/3)+1 := by omega
  have hcz := three_index_forces_divisor (x:ℤ) (j/3)
  rw [←hj,he] at hcz
  have hd : 4*x+3 ∣ x^h := by exact_mod_cast hcz
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (p:=3) (by omega : 4*x+3 ≠ 0) (fun {r} hr hrc => by
    have hrx := hr.dvd_of_dvd_pow (hrc.trans hd)
    have hr3 : r ∣ 3 := (Nat.dvd_add_iff_right (dvd_mul_of_dvd_right hrx 4)).mpr hrc
    exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp hr3)
  have hres (t : ℕ) : 3^t%8=1 ∨ 3^t%8=3 := by
    induction t with
    | zero => decide
    | succ t ih =>
      rw [pow_succ,Nat.mul_mod]
      rcases ih with hv | hv <;> rw [hv] <;> decide
  have hm := hres ((4*x+3).primeFactorsList.length)
  rw [←hpow] at hm
  have := Nat.odd_iff.mp hx
  omega

/-- At every natural base greater than one, an alternating geometric sum
of odd length greater than one is nonsquare (Ljunggren's negative-base case). -/
theorem alternatingBlock_not_square {x n : ℕ} (hx : 1<x) (hn : 1<n) (hno : Odd n) :
    ¬IsSquare (alternatingBlock x n) := by
  rintro ⟨y,hy⟩
  obtain ⟨h,hh⟩ := hno
  have hn' : n=2*h+1 := by omega
  have hh0 : 0<h := by omega
  have hprod := alternatingBlock_mul (x:=x) (show Odd n from ⟨h,hh⟩)
  rw [hy,hn',pow_succ,pow_mul',pow_two] at hprod
  have hzero : 0<y := by
    by_contra! h0
    rw [show y=0 by omega] at hprod
    simp at hprod
  have hP : ((x:ℤ)+1)*(y:ℤ)^2-(x:ℤ)*((x:ℤ)^h)^2=1 := by
    have h := congrArg (fun u : ℕ => (u:ℤ)) hprod
    push_cast at h
    nlinarith
  obtain ⟨j,hj⟩ := exists_alternatingPellCoordinates (x:=x) (by positivity) (by positivity) (by positivity) hP
  have he := congrArg Prod.snd hj
  change (alternatingPellCoordinates x j).2=(x:ℤ)^h at he
  have hgt : 1<x^h := one_lt_pow' hx hh0.ne'
  have hj0 : 0<j := by
    by_contra! hh
    rw [show j=0 by omega] at he
    change 1=(x:ℤ)^h at he
    exact (by exact_mod_cast hgt : (1:ℤ)<(x:ℤ)^h).ne he
  have hodd := alternatingPellCoordinates_odd_snd (x:ℤ) j
  rw [he] at hodd
  have hxo : Odd x := by
    by_contra hn
    have he := (Nat.even_or_odd x).resolve_right hn
    have hez : Even ((x:ℤ)^h) := by exact_mod_cast he.pow_of_ne_zero hh0.ne'
    exact (Int.not_even_iff_odd.mpr hodd) hez
  have hs := (alternatingPellCoordinates_gt_length (x:=(x:ℤ)) (by positivity) j).2 hj0
  rw [he] at hs
  by_cases h3 : 3∣x
  · exact exceptional_three hxo h3 hh0 he
  have hd : x^h ∣ 2*j+1 := by
    apply (Nat.dvd_iff_prime_pow_dvd_dvd ..).mpr
    intro p k hp hpk
    by_cases hk : k=0
    · simp [hk]
    have hpx := hp.dvd_of_dvd_pow ((dvd_pow_self p hk).trans hpk)
    have hp5 : 5≤p := by
      have hp2 := hp.two_le
      have hid : p≠4 := by intro h; subst p; exact (by decide : ¬Nat.Prime 4) hp
      have hin : p≠2 := fun he => hxo.not_two_dvd_nat (he ▸ hpx)
      have hip : p≠3 := fun he => h3 (he ▸ hpx)
      omega
    apply alternatingPellCoordinates_pow_dvd_length hp hp5 hpx j
    rw [he]
    exact_mod_cast hpk
  have hle := Nat.le_of_dvd (by omega : 0<2*j+1) hd
  exact hs.not_ge (by exact_mod_cast hle)

end OddPerfect
