module

public import OddPerfect.GeometricNonSquare
import all OddPerfect.GeometricNonSquare
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Data.Nat.Prime.Int
import Mathlib.NumberTheory.Zsqrtd.Basic

public section

namespace OddPerfect

private theorem generator_dvd_at_prime_power {p x D : ℤ} {k : ℕ} (hp : Prime p)
    (hx : x=p^k) (hD : D=1-x) (z : Zsqrtd D) (hn : x ∣ z.norm)
    (hnd : ¬p ∣ z.im+z.re) : quadraticGenerator D ∣ z := by
  apply (generator_dvd_iff hD _).mpr
  have hprod : x ∣ (z.im-z.re)*(-z.im-z.re) := by
    have he : (z.im-z.re)*(-z.im-z.re)=z.norm-x*(z.im*z.im) := by
      rw [Zsqrtd.norm_def]
      nlinarith [congrArg (fun v => v*z.im*z.im) hD]
    rw [he]
    exact dvd_sub hn (dvd_mul_right _ _)
  rw [hx] at hprod ⊢
  apply hp.pow_dvd_of_dvd_mul_right k _ hprod
  intro hd
  apply hnd
  rwa [show -z.im-z.re = -(z.im+z.re) by ring,dvd_neg] at hd

private theorem generator_pow_dvd_at_prime_power {p x D : ℤ} {k : ℕ} (hp : Prime p)
    (hx : x=p^k) (hk : 0<k) (hD : D=1-x) (d : ℕ) (z : Zsqrtd D) (hn : z.norm=x^d)
    (hnd : ¬p ∣ z.im+z.re) : (quadraticGenerator D)^d ∣ z := by
  induction d generalizing z with
  | zero => rw [pow_zero]; exact one_dvd _
  | succ d ih =>
    have hd : x ∣ z.norm := hn ▸ dvd_pow_self _ (Nat.succ_ne_zero d)
    obtain ⟨v,hv⟩ := generator_dvd_at_prime_power hp hx hD z hd hnd
    have hn' : v.norm=x^d := by
      rw [hv,Zsqrtd.norm_mul,generator_norm hD,pow_succ'] at hn
      exact mul_left_cancel₀ (hx ▸ pow_ne_zero k hp.ne_zero) hn
    have hnd' : ¬p ∣ v.im+v.re := by
      intro h
      apply hnd
      have he : z.im+z.re=2*(v.im+v.re)-x*v.im := by
        rw [hv,Zsqrtd.im_mul,Zsqrtd.re_mul]
        dsimp [quadraticGenerator]
        nlinarith [congrArg (·*v.im) hD]
      rw [he]
      exact dvd_sub (dvd_mul_of_dvd_right h 2)
        (dvd_mul_of_dvd_left (hx ▸ dvd_pow_self p hk.ne') _)
    obtain ⟨u,hu⟩ := ih v hn' hnd'
    exact ⟨u,by rw [hv,hu,pow_succ']; ac_rfl⟩

/-- A geometric sum with at least two terms at a prime-power base congruent
to one modulo four cannot be square. The prime underneath the base may be
three modulo four when its exponent is even. -/
theorem geometricBlock_not_square_of_prime_pow_one_mod_four {p k d : ℕ} (hp : p.Prime)
    (hk : 0 < k) (hx4 : p^k%4=1) (hd : 1 < d) : ¬IsSquare (geometricBlock (p^k) d) := by
  let x := p^k
  have hx : 1 < x := one_lt_pow₀ hp.one_lt hk.ne'
  have hx4' : x%4=1 := hx4
  have hx5 : 5 ≤ x := by omega
  have hkz : (x:ℤ)=(p:ℤ)^k := by simp [x]
  let c : ℤ := -((x/4:ℕ):ℤ)
  have hD : 4*c=1-(x:ℤ) := by dsimp [c]; omega
  have hc : c ≠ 0 := by dsimp [c]; omega
  rintro ⟨y,hy⟩
  let z : Zsqrtd (4*c) := ⟨1,(y:ℤ)⟩
  have hz : z.norm=(x:ℤ)^d := by
    have he := geom_sum_mul_of_one_le hx.le d
    change geometricBlock x d*(x-1)=x^d-1 at he
    rw [show geometricBlock x d=y*y from hy] at he
    have hpow := Nat.pow_pos (by omega : 0<x) (n:=d)
    have hn : y*y*(x-1)+1=x^d := by omega
    have hzint := congrArg (fun n : ℕ => (n:ℤ)) hn
    push_cast [Nat.cast_sub hx.le] at hzint
    change 1*1-4*c*(y:ℤ)*(y:ℤ)=(x:ℤ)^d
    rw [hD]
    nlinarith
  have hunit (u : Zsqrtd (4*c)) (hu : u.norm=(x:ℤ)^d) (hre : u.re=1)
      (hnd : ¬(p:ℤ) ∣ u.im+u.re) : False := by
    obtain ⟨v,hv⟩ := generator_pow_dvd_at_prime_power (Nat.prime_iff_prime_int.mp hp) hkz hk hD d u hu hnd
    have hn : v.norm=1 := by
      have hg : ((quadraticGenerator (4*c))^d).norm=(x:ℤ)^d := by
        change Zsqrtd.normMonoidHom ((quadraticGenerator (4*c))^d) = _
        rw [map_pow]
        exact congrArg (·^d) (generator_norm hD)
      rw [hv,Zsqrtd.norm_mul,hg] at hu
      exact (mul_left_cancel₀ (pow_ne_zero d (by exact_mod_cast (by omega : x ≠ 0)))) (hu.trans (mul_one _).symm)
    obtain ⟨hn1,hn2⟩ := generator_power_re_ne hc hd
    rcases real_unit_of_norm_one (by omega : 4*c ≤ -2) v hn with h | h
    · rw [hv,h,mul_one] at hre
      exact hn1 hre
    · rw [hv,h,mul_neg_one,Zsqrtd.re_neg] at hre
      exact hn2 (by omega)
  by_cases h : (p:ℤ) ∣ z.im+z.re
  · apply hunit (star z) (by rwa [Zsqrtd.norm_conj]) rfl
    intro h'
    have ht := dvd_add h h'
    change (p:ℤ) ∣ ((y:ℤ)+1)+(-(y:ℤ)+1) at ht
    have ht' : (p:ℤ) ∣ (2:ℤ) := by convert ht using 1; ring
    have hp2 : p=2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (by exact_mod_cast ht')
    have hpo := (Nat.odd_iff.mpr (show x%2=1 by omega)).of_dvd_nat (dvd_pow_self p hk.ne')
    exact hpo.not_two_dvd_nat (hp2 ▸ dvd_refl _)
  · exact hunit z hz rfl h

end OddPerfect
