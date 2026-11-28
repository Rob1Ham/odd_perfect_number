module

public import OddPerfect.AlternatingPell
import all OddPerfect.PellCoordinates
import Mathlib.Tactic.LinearCombination

public section
namespace OddPerfect

private theorem quadratic_im_pow_dvd_length {p A D k m : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    (hm : 0<m) (hd : p∣D) (hA : ¬p∣A)
    (hdiv : (p:ℤ)^k ∣ ((⟨(A:ℤ),1⟩ : ℤ√(D:ℤ))^m).im) : p^k ∣ m := by
  let v := m.factorization p
  apply (hp.pow_dvd_iff_le_factorization hm.ne').mpr
  by_contra! hk
  have hv : v+1 ≤ k := hk
  have hc := quadratic_im_mod_prime_power (A:=A) hp hp5 hm hd
  have ht := (pow_dvd_pow (p:ℤ) hv).trans hdiv
  have hpow := Int.modEq_zero_iff_dvd.mp (hc.symm.trans (Int.modEq_zero_iff_dvd.mpr ht))
  have hnat : p^(v+1) ∣ m*A^(m-1) := by dsimp only [v]; exact_mod_cast hpow
  have hA0 : A ≠ 0 := by rintro rfl; exact hA (dvd_zero _)
  have hf := (hp.pow_dvd_iff_le_factorization (mul_ne_zero hm.ne' (pow_ne_zero _ hA0))).mp hnat
  rw [Nat.factorization_mul hm.ne' (pow_ne_zero _ hA0),Finsupp.add_apply,Nat.factorization_pow,
    Finsupp.smul_apply,Nat.factorization_eq_zero_of_not_dvd hA,smul_eq_mul,mul_zero,add_zero] at hf
  change m.factorization p+1≤_ at hf
  omega

private theorem first_power_coordinates (x j : ℕ) :
    let w : ℤ√((x*(x+1):ℕ):ℤ) := ⟨x,1⟩
    (w^(2*j+1)).re=(x:ℤ)^(j+1)*(alternatingPellCoordinates x j).2 ∧
    (w^(2*j+1)).im=(x:ℤ)^j*(alternatingPellCoordinates x j).1 := by
  let w : ℤ√((x*(x+1):ℕ):ℤ) := ⟨x,1⟩
  have hr : (w^2).re = (x:ℤ)*(2*x+1) := by
    rw [pow_two,Zsqrtd.re_mul]; dsimp only [w]; push_cast; ring
  have hi : (w^2).im = 2*(x:ℤ) := by
    rw [pow_two,Zsqrtd.im_mul]; dsimp only [w]; ring
  change (w^(2*j+1)).re=_ ∧ (w^(2*j+1)).im=_
  induction j with
  | zero => simp [w,alternatingPellCoordinates]
  | succ j ih =>
    rw [show 2*(j+1)+1=(2*j+1)+2 by omega,pow_add,Zsqrtd.re_mul,Zsqrtd.im_mul,hr,hi,ih.1,ih.2]
    simp only [alternatingPellCoordinates,pow_succ]
    push_cast
    constructor <;> ring

private theorem first_coordinate_pow_dvd_length {x p k : ℕ} (hp : p.Prime) (hp5 : 5≤p) (hpx : p∣x+1)
    (j : ℕ) (hdiv : (p:ℤ)^k ∣ (alternatingPellCoordinates x j).1) : p^k∣2*j+1 := by
  have hx : ¬p∣x := fun h => hp.not_dvd_one ((Nat.dvd_add_iff_right h).mpr hpx)
  apply quadratic_im_pow_dvd_length (A:=x) (D:=x*(x+1)) hp hp5 (by omega) (dvd_mul_of_dvd_right hpx _) hx
  rw [(first_power_coordinates x j).2]
  exact dvd_mul_of_dvd_right hdiv _

private theorem first_coordinate_gt {x : ℤ} (hx : 0<x) (j : ℕ) :
    (2*j+1:ℤ) ≤ (alternatingPellCoordinates x j).1 ∧
      (0<j → (2*j+1:ℤ) < (alternatingPellCoordinates x j).1) := by
  induction j with
  | zero => simp [alternatingPellCoordinates]
  | succ j ih =>
    obtain ⟨hy,hz⟩ := alternatingPellCoordinates_pos hx j
    simp only [alternatingPellCoordinates,Nat.cast_succ]
    have h : 2*((j:ℤ)+1)+1 <
        (2*x+1)*(alternatingPellCoordinates x j).1+2*x*(alternatingPellCoordinates x j).2 := by
      nlinarith [mul_pos hx hy,mul_pos hx hz,ih.1]
    exact ⟨h.le,fun _ => h⟩

private theorem first_coordinate_odd (x : ℤ) (j : ℕ) : Odd (alternatingPellCoordinates x j).1 := by
  induction j with
  | zero => exact odd_one
  | succ j ih =>
    obtain ⟨u,hu⟩ := ih
    refine ⟨2*x*u+x+u+x*(alternatingPellCoordinates x j).2,?_⟩
    simp only [alternatingPellCoordinates,hu]
    ring

private theorem pell_norm (x : ℤ) (j : ℕ) :
    (x+1)*(alternatingPellCoordinates x j).1^2-x*(alternatingPellCoordinates x j).2^2=1 := by
  induction j with
  | zero => simp [alternatingPellCoordinates]
  | succ j ih => simp only [alternatingPellCoordinates]; linear_combination ih

private theorem triple_index_coords (x : ℤ) (j : ℕ) :
    let y := (alternatingPellCoordinates x j).1
    let z := (alternatingPellCoordinates x j).2
    (alternatingPellCoordinates x (3*j+1)).1=(x+1)*y^3+3*x*y*z^2 ∧
    (alternatingPellCoordinates x (3*j+1)).2=3*(x+1)*y^2*z+x*z^3 := by
  induction j with
  | zero => simp [alternatingPellCoordinates]; constructor <;> ring
  | succ j ih =>
    rw [show 3*(j+1)+1=(3*j+1)+3 by omega]
    generalize hJ : 3*j+1=J at ih ⊢
    dsimp only
    simp only [alternatingPellCoordinates,ih.1,ih.2]
    constructor <;> ring

private theorem triple_index_first (x : ℤ) (j : ℕ) :
    (alternatingPellCoordinates x (3*j+1)).1=(alternatingPellCoordinates x j).1*
      (4*(x+1)*(alternatingPellCoordinates x j).1^2-3) := by
  rw [(triple_index_coords x j).1]
  linear_combination (-3*(alternatingPellCoordinates x j).1)*(pell_norm x j)

private theorem first_index_mod_three {x : ℕ} (hx : 3∣x+1) (j : ℕ) :
    (alternatingPellCoordinates x j).1 ≡ (-1)^j*(2*j+1) [ZMOD 3] ∧
    (alternatingPellCoordinates x j).2 ≡ (-1)^j [ZMOD 3] := by
  have hx0 : (x:ℤ)+1 ≡ 0 [ZMOD 3] := Int.modEq_zero_iff_dvd.mpr (by exact_mod_cast hx)
  have hx' : (x:ℤ) ≡ -1 [ZMOD 3] := by simpa using hx0.sub_right 1
  induction j with
  | zero => simp [alternatingPellCoordinates]
  | succ j ih =>
    simp only [alternatingPellCoordinates,Nat.cast_succ,pow_succ]
    have h2 := (Int.ModEq.refl 2).mul hx'
    have h3 := h2.add (Int.ModEq.refl 1)
    have h4 := (Int.ModEq.refl 2).mul hx0
    constructor
    · convert (h3.mul ih.1).add (h2.mul ih.2) using 1; ring
    · convert (h4.mul ih.1).add (h3.mul ih.2) using 1; ring

private theorem smooth_first_coordinate {x j Y : ℕ} (hx : 0<x)
    (hY : (alternatingPellCoordinates x j).1=(Y:ℤ)) (hn : ¬3∣Y)
    (hd : ∀ p : ℕ, p.Prime → p∣Y → p∣x+1) : j=0 := by
  have hyo : Odd Y := by
    have ho := first_coordinate_odd (x:ℤ) j
    rw [hY] at ho
    exact_mod_cast ho
  have hdiv : Y ∣ 2*j+1 := by
    apply (Nat.dvd_iff_prime_pow_dvd_dvd ..).mpr
    intro p k hp hpk
    by_cases hk : k=0
    · simp [hk]
    have hpy := (dvd_pow_self p hk).trans hpk
    have hp5 : 5≤p := by
      have := hp.two_le
      have h2 : p≠2 := fun h => hyo.not_two_dvd_nat (h ▸ hpy)
      have h3 : p≠3 := fun h => hn (h ▸ hpy)
      have h4 : p≠4 := fun h => (by decide : ¬Nat.Prime 4) (h ▸ hp)
      omega
    apply first_coordinate_pow_dvd_length hp hp5 (hd p hp hpy) j
    rw [hY]
    exact_mod_cast hpk
  by_contra hn
  have hh := (first_coordinate_gt (x:=(x:ℤ)) (by positivity) j).2 (Nat.pos_of_ne_zero hn)
  rw [hY] at hh
  exact hh.not_ge (by exact_mod_cast Nat.le_of_dvd (by omega : 0<2*j+1) hdiv)


private theorem positive_first_power {x j h : ℕ} (hx : 0<x) (hh : 0<h)
    (he : (alternatingPellCoordinates x j).1=((x:ℤ)+1)^h) :
    x+1=3 ∧ h=2 := by
  let b := x+1
  have hb : 1<b := by dsimp [b]; omega
  have hY : (alternatingPellCoordinates x j).1=((b^h:ℕ):ℤ) := by simpa [b] using he
  have hbH : 1<b^h := one_lt_pow' hb hh.ne'
  have hsmooth (p : ℕ) (hp : p.Prime) (hpY : p∣b^h) : p∣x+1 := hp.dvd_of_dvd_pow hpY
  have h3 : 3∣b^h := by
    by_contra hn
    have hj := smooth_first_coordinate hx hY hn hsmooth
    rw [hj] at hY
    change 1=((b^h:ℕ):ℤ) at hY
    exact (by exact_mod_cast hbH : (1:ℤ)<(b^h:ℕ)).ne hY
  have hb3 := Nat.prime_three.dvd_of_dvd_pow h3
  have hm := (first_index_mod_three hb3 j).1
  rw [hY] at hm
  have hmod := hm.symm.trans (Int.modEq_zero_iff_dvd.mpr (by exact_mod_cast h3))
  have hlen : 3 ∣ 2*j+1 := by
    have h := Int.modEq_zero_iff_dvd.mp hmod
    have hu : IsUnit ((-1:ℤ)^j) := isUnit_neg_one.pow _
    exact_mod_cast (hu.dvd_mul_left.mp h)
  let k := j/3
  have hj : j=3*k+1 := by dsimp [k]; omega
  let Y := (alternatingPellCoordinates x k).1.toNat
  have hYpos := (alternatingPellCoordinates_pos (x:=(x:ℤ)) (by positivity) k).1
  have hy : (alternatingPellCoordinates x k).1=(Y:ℤ) := (Int.toNat_of_nonneg hYpos.le).symm
  have hy0 : 0<Y := by dsimp [Y]; omega
  let F := 4*b*Y^2-3
  have hnum : 8≤4*b*Y^2 := by
    have hy' : 1≤Y^2 := Nat.one_le_pow _ _ hy0
    have h := Nat.mul_le_mul (by omega : 8≤4*b) hy'
    simpa using h
  have hf0 : 5≤F := by dsimp [F]; omega
  have hf : (F:ℤ)=4*(x+1:ℤ)*(Y:ℤ)^2-3 := by
    change ((4*b*Y^2-3:ℕ):ℤ)=_
    rw [Nat.cast_sub (by omega : 3≤4*b*Y^2)]
    simp [b]
  have hprod : b^h=Y*F := by
    have h := triple_index_first (x:ℤ) k
    rw [←hj,hY,hy,←hf] at h
    exact_mod_cast h
  have hFd : F∣b^h := hprod ▸ dvd_mul_left _ _
  have hYd : Y∣b^h := hprod ▸ dvd_mul_right _ _
  have hFeq := Nat.eq_prime_pow_of_unique_prime_dvd (p:=3) (by omega : F≠0) (fun {r} hr hrF => by
    have hrb := hr.dvd_of_dvd_pow (hrF.trans hFd)
    have hA : r∣4*b*Y^2 := dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hrb _) _
    have hdiff : 4*b*Y^2-F=3 := by dsimp [F] at *; omega
    exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hdiff ▸ Nat.dvd_sub hA hrF))
  have h9 : 9∣F := by
    let e := F.primeFactorsList.length
    have he2 : 2≤e := by
      by_contra! hh
      have hh1 : e=0 ∨ e=1 := by omega
      change F=3^e at hFeq
      rcases hh1 with e | e <;> rw [e] at hFeq <;> simp_all
    rw [hFeq]
    exact pow_dvd_pow 3 he2
  have hY3 : ¬3∣Y := by
    intro hh
    have hy9 : 9∣Y^2 := pow_dvd_pow_of_dvd hh 2
    have hsub : 4*b*Y^2-F=3 := by dsimp [F] at *; omega
    have hbad := Nat.dvd_sub (dvd_mul_of_dvd_right hy9 (4*b)) h9
    rw [hsub] at hbad
    exact (by decide : ¬9∣3) hbad
  have hk := smooth_first_coordinate hx hy hY3 (fun p hp H => hsmooth p hp (H.trans hYd))
  have hj1 : j=1 := by omega
  rw [hj1] at he
  have hpower : b^h=4*b-3 := by
    dsimp [alternatingPellCoordinates] at he
    have hbsub : ((4*b-3:ℕ):ℤ)=4*((x:ℤ)+1)-3 := by
      dsimp [b]; push_cast [Nat.cast_sub (by omega : 3≤4*(x+1))]; ring
    exact_mod_cast (show ((b^h:ℕ):ℤ)=((4*b-3:ℕ):ℤ) by rw [hbsub]; dsimp [b]; nlinarith)
  have hbdiv := dvd_pow_self b hh.ne'
  rw [hpower] at hbdiv
  have hdiff : 4*b-(4*b-3)=3 := by omega
  have hbd : b∣3 := hdiff ▸ Nat.dvd_sub (dvd_mul_left b 4) hbdiv
  have hb3 := ((Nat.dvd_prime Nat.prime_three).mp hbd).resolve_left (by omega)
  have hh2 : 3^h=(3:ℕ)^2 := by simpa [hb3] using hpower
  exact ⟨hb3,(pow_right_injective₀ (by decide : 0<(3:ℕ)) (by decide : (3:ℕ) ≠ 1)) hh2⟩

/-- Ljunggren's complete square classification for positive bases and
odd lengths greater than one. -/
theorem geometricBlock_isSquare_iff_of_odd_length {b n : ℕ} (hb : 1<b) (hn : 1<n) (hno : Odd n) :
    IsSquare (geometricBlock b n) ↔ b=3 ∧ n=5 := by
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨h,hh⟩ := hno
    have hn' : n=2*h+1 := by omega
    have hh0 : 0<h := by omega
    let x := b-1
    have hxb : x+1=b := by dsimp [x]; omega
    have hx : 0<x := by omega
    have hgeom := geom_sum_mul_of_one_le hb.le n
    change geometricBlock b n*(b-1)=b^n-1 at hgeom
    have H : y*y*x+1=b*(b^h)^2 := by
      rw [hy,hn',pow_succ,pow_mul',pow_two] at hgeom
      have hpos : 0<b^h := pow_pos (by omega) _
      have hproduct : 0<(b^h*b^h)*b := by positivity
      dsimp [x]
      nlinarith [Nat.sub_add_cancel hproduct]
    have hy0 : 0<y := by
      have hi := one_lt_pow' hb hh0.ne'
      by_contra! hz
      rw [show y=0 by omega] at H
      simp at H
      nlinarith [Nat.mul_le_mul hb.le (show 1≤(b^h)^2 from one_le_pow₀ hi.le)]
    have heq : ((x:ℤ)+1)*((b:ℤ)^h)^2-(x:ℤ)*(y:ℤ)^2=1 := by
      have hi := congrArg (fun t : ℕ => (t:ℤ)) H
      push_cast at hi
      have hx' : (x:ℤ)+1=(b:ℤ) := by exact_mod_cast hxb
      rw [hx']
      nlinarith
    obtain ⟨j,hj⟩ := exists_alternatingPellCoordinates (x:=(x:ℤ)) (by positivity) (by positivity) (by positivity) heq
    have hY := congrArg Prod.fst hj
    have hb' : (b:ℤ)=(x:ℤ)+1 := by exact_mod_cast hxb.symm
    change (alternatingPellCoordinates x j).1=(b:ℤ)^h at hY
    rw [hb'] at hY
    obtain ⟨h3,h2⟩ := positive_first_power hx hh0 hY
    exact ⟨hxb ▸ h3,by omega⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨11,by decide⟩

/-- The only positive even-exponent prime-power component with a square
divisor sum is 3^4. -/
theorem sigma_prime_pow_isSquare_iff_of_even {p e : ℕ} (hp : p.Prime) (he : 0<e) (heo : Even e) :
    IsSquare (ArithmeticFunction.sigma 1 (p^e)) ↔ p=3 ∧ e=4 := by
  have ho : Odd (e+1) := Nat.odd_iff.mpr (by have := Nat.even_iff.mp heo; omega)
  have h := geometricBlock_isSquare_iff_of_odd_length (b:=p) (n:=e+1) hp.one_lt (by omega) ho
  change IsSquare (geometricBlock p (e+1)) ↔ _ at h
  rw [show ArithmeticFunction.sigma 1 (p^e)=geometricBlock p (e+1) from
    ArithmeticFunction.sigma_one_apply_prime_pow hp,h]
  omega

end OddPerfect
