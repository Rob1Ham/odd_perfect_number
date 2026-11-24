module

public import OddPerfect.GeometricSquareClass
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Data.Nat.Prime.Int

public section

namespace OddPerfect

open Finset ArithmeticFunction

private def quadraticGenerator (D : ℤ) : Zsqrtd D := ⟨1,1⟩

/-- The real coefficient is controlled modulo twice its indicated scale, while
the imaginary coefficient stays a multiple of twice R. -/
private def powerCoordinates (c R u : ℤ) (z : Zsqrtd (4*c)) : Prop :=
  ∃ a b : ℤ, z.re=1+4*c*R*(u+2*a) ∧ z.im=2*R*b

private theorem powerCoordinates_mul {c R u v : ℤ} {z w : Zsqrtd (4*c)}
    (hz : powerCoordinates c R u z) (hw : powerCoordinates c R v w) :
    powerCoordinates c R (u+v) (z*w) := by
  obtain ⟨a,b,hr,hi⟩ := hz
  obtain ⟨f,g,hs,hj⟩ := hw
  refine ⟨a+f+2*c*R*(u+2*a)*(v+2*f)+2*R*b*g,
    (1+4*c*R*(u+2*a))*g+(1+4*c*R*(v+2*f))*b,?_,?_⟩
  · rw [Zsqrtd.re_mul,hr,hi,hs,hj]; ring
  · rw [Zsqrtd.im_mul,hr,hi,hs,hj]; ring

private theorem powerCoordinates_pow {c R : ℤ} {z : Zsqrtd (4*c)}
    (hz : powerCoordinates c R 1 z) (n : ℕ) : powerCoordinates c R n (z^n) := by
  induction n with
  | zero => exact ⟨0,0,by simp,by simp⟩
  | succ n ih => simpa [pow_succ] using powerCoordinates_mul ih hz

private theorem powerCoordinates_square {c R : ℤ} {z : Zsqrtd (4*c)} (hz : powerCoordinates c R 1 z) :
    powerCoordinates c (2*R) 1 (z^2) := by
  obtain ⟨a,b,hr,hi⟩ := hz
  refine ⟨a+c*R*(1+2*a)^2+R*b^2,(1+4*c*R*(1+2*a))*b,?_,?_⟩
  · rw [pow_two,Zsqrtd.re_mul,hr,hi]; ring
  · rw [pow_two,Zsqrtd.im_mul,hr,hi]; ring

private theorem generator_even_power_coords (c : ℤ) (k : ℕ) (hk : 0 < k) :
    ∃ R : ℤ, 0 < R ∧ powerCoordinates c R 1 ((quadraticGenerator (4*c))^(2*k)) := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rcases Nat.even_or_odd k with he | ho
    · obtain ⟨j,hj⟩ := he
      obtain ⟨R,hR,hs⟩ := ih j (by omega) (by omega)
      refine ⟨2*R,by omega,?_⟩
      rw [show 2*k=(2*j)*2 by omega,pow_mul]
      exact powerCoordinates_square hs
    · have hbase : powerCoordinates c 1 1 ((quadraticGenerator (4*c))^2) := by
        refine ⟨0,1,?_,?_⟩ <;> simp [pow_two,quadraticGenerator]
      obtain ⟨a,b,hr,hi⟩ := powerCoordinates_pow hbase k
      obtain ⟨j,hj⟩ := ho
      refine ⟨1,by decide,(j:ℤ)+a,b,?_,?_⟩
      · rw [pow_mul,hr,hj]
        push_cast
        ring
      · rwa [pow_mul]

private theorem generator_power_re_ne {c : ℤ} (hc : c ≠ 0) {d : ℕ} (hd : 1<d) :
    ((quadraticGenerator (4*c))^d).re ≠ 1 ∧ ((quadraticGenerator (4*c))^d).re ≠ -1 := by
  let k := d/2
  obtain ⟨R,hR,a,b,hr,hi⟩ := generator_even_power_coords c k (by dsimp [k]; omega)
  have hshape : ∃ A : ℤ, ((quadraticGenerator (4*c))^d).re = 1+4*c*R*(1+2*A) := by
    rcases (by dsimp [k]; omega : d=2*k ∨ d=2*k+1) with h | h
    · exact ⟨a,h ▸ hr⟩
    · refine ⟨a+b,?_⟩
      rw [h,pow_succ,Zsqrtd.re_mul,hr,hi]
      dsimp [quadraticGenerator]
      ring
  obtain ⟨A,hA⟩ := hshape
  rw [hA]
  have hne : 4*c*R*(1+2*A) ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (by decide) hc) hR.ne') (by omega)
  constructor
  · omega
  · have h : 4*c*R*(1+2*A) = 4*(c*R*(1+2*A)) := by ring
    omega

private theorem generator_dvd_iff {q D : ℤ} (hD : D=1-q) (z : Zsqrtd D) :
    quadraticGenerator D ∣ z ↔ q ∣ z.im-z.re := by
  constructor
  · rintro ⟨w,rfl⟩
    refine ⟨w.im,?_⟩
    simp [quadraticGenerator,hD]
    ring
  · rintro ⟨v,hv⟩
    refine ⟨⟨z.im-v,v⟩,?_⟩
    apply Zsqrtd.ext
    · simp [quadraticGenerator,hD]
      linarith
    · simp [quadraticGenerator]

private theorem generator_norm {q D : ℤ} (hD : D=1-q) :
    (quadraticGenerator D).norm=q := by simp [Zsqrtd.norm,quadraticGenerator,hD]

private theorem divides_or_conj_of_norm {q D : ℤ} (hD : D=1-q) (hq : Prime q) (z : Zsqrtd D)
    (hd : q ∣ z.norm) : quadraticGenerator D ∣ z ∨ quadraticGenerator D ∣ star z := by
  have hprod : q ∣ (z.im-z.re)*(-z.im-z.re) := by
    have he : (z.im-z.re)*(-z.im-z.re)=z.norm-q*(z.im*z.im) := by
      rw [Zsqrtd.norm_def]
      nlinarith [congrArg (fun v => v*z.im*z.im) hD]
    rw [he]
    exact dvd_sub hd (dvd_mul_right _ _)
  rcases hq.dvd_or_dvd hprod with h | h
  · exact Or.inl ((generator_dvd_iff hD _).mpr h)
  · exact Or.inr ((generator_dvd_iff hD _).mpr (by simpa using h))

private theorem generator_pow_dvd_of_norm {q D : ℤ} (hD : D=1-q) (hq : Prime q) (d : ℕ)
    (z : Zsqrtd D) (hn : z.norm=q^d) (hconj : ¬quadraticGenerator D ∣ star z) :
    (quadraticGenerator D)^d ∣ z := by
  induction d generalizing z with
  | zero => rw [pow_zero]; exact one_dvd _
  | succ d ih =>
    have hd : q ∣ z.norm := hn ▸ dvd_pow_self _ (Nat.succ_ne_zero d)
    obtain ⟨w,hw⟩ := (divides_or_conj_of_norm hD hq z hd).resolve_right hconj
    have hnorm : w.norm=q^d := by
      rw [hw,Zsqrtd.norm_mul,generator_norm hD,pow_succ'] at hn
      exact mul_left_cancel₀ hq.ne_zero hn
    have hcw : ¬quadraticGenerator D ∣ star w := by
      intro h
      apply hconj
      rw [hw,star_mul]
      exact dvd_mul_of_dvd_left h _
    obtain ⟨v,hv⟩ := ih w hnorm hcw
    exact ⟨v,by rw [hw,hv,pow_succ']; ac_rfl⟩

private theorem real_unit_of_norm_one {D : ℤ} (hD : D ≤ -2) (z : Zsqrtd D) (hz : z.norm=1) :
    z = 1 ∨ z = -1 := by
  have hh := Zsqrtd.norm_def z
  have him : z.im=0 := by
    by_contra h
    have hsq : 0 < z.im*z.im := mul_self_pos.mpr h
    have hn := mul_le_mul_of_nonneg_right hD hsq.le
    nlinarith [mul_self_nonneg z.re]
  have hre : z.re=1 ∨ z.re= -1 := by
    rw [him,hz] at hh
    have hprod : (z.re-1)*(z.re+1)=0 := by nlinarith
    rcases mul_eq_zero.mp hprod with h | h <;> omega
  rcases hre with h | h
  · left; apply Zsqrtd.ext <;> simp [h,him]
  · right; apply Zsqrtd.ext <;> simp [h,him]

/-- Hirakawa's Theorem 2.3, in length form. The geometric sum of at least two
terms at a prime base one modulo four cannot be a square. -/
theorem geometricBlock_not_square_of_prime_one_mod_four {q d : ℕ} (hq : q.Prime) (hq4 : q%4=1)
    (hd : 1 < d) : ¬IsSquare (geometricBlock q d) := by
  rintro ⟨y,hy⟩
  let c : ℤ := -((q/4:ℕ):ℤ)
  have hq5 : 5 ≤ q := by have := hq.one_lt; omega
  have hD : 4*c=1-(q:ℤ) := by dsimp [c]; omega
  have hc : c ≠ 0 := by dsimp [c]; omega
  let z : Zsqrtd (4*c) := ⟨1,(y:ℤ)⟩
  have hz : z.norm=(q:ℤ)^d := by
    have he := geom_sum_mul_of_one_le hq.one_le d
    change geometricBlock q d * (q-1)=q^d-1 at he
    rw [hy] at he
    have hpow := Nat.pow_pos hq.pos (n:=d)
    have hn : y*y*(q-1)+1=q^d := by omega
    have hzint := congrArg (fun n : ℕ => (n:ℤ)) hn
    push_cast [Nat.cast_sub hq.one_le] at hzint
    change 1*1-4*c*(y:ℤ)*(y:ℤ)=(q:ℤ)^d
    rw [hD]
    nlinarith
  let w := quadraticGenerator (4*c)
  have hunit (u : Zsqrtd (4*c)) (hu : u.norm=(q:ℤ)^d) (hdiv : w^d ∣ u) (hre : u.re=1) : False := by
    obtain ⟨v,hv⟩ := hdiv
    have hn : v.norm=1 := by
      have hg : (w^d).norm=(q:ℤ)^d := by
        change Zsqrtd.normMonoidHom (w^d) = _
        rw [map_pow]
        exact congrArg (·^d) (generator_norm hD)
      rw [hv,Zsqrtd.norm_mul,hg] at hu
      exact (mul_left_cancel₀ (pow_ne_zero d (by positivity : (q:ℤ) ≠ 0))) (hu.trans (mul_one _).symm)
    obtain ⟨hn1,hn2⟩ := generator_power_re_ne hc hd
    rcases real_unit_of_norm_one (by omega : 4*c ≤ -2) v hn with h | h
    · rw [hv,h,mul_one] at hre
      exact hn1 hre
    · rw [hv,h,mul_neg_one,Zsqrtd.re_neg] at hre
      change -((quadraticGenerator (4*c))^d).re=1 at hre
      exact hn2 (by omega)
  by_cases h : w ∣ star z
  · have hnot : ¬w ∣ z := by
      intro h2
      have hplus := (generator_dvd_iff hD _).mp h
      have hminus := (generator_dvd_iff hD _).mp h2
      have hboth := dvd_add hplus hminus
      change (q:ℤ) ∣ (-(y:ℤ)-1)+((y:ℤ)-1) at hboth
      have ht : (q:ℤ) ∣ (-2:ℤ) := by convert hboth using 1; ring
      have hnat : q ∣ 2 := by exact_mod_cast (dvd_neg.mp ht)
      exact (by omega : ¬ q ≤ 2) (Nat.le_of_dvd (by decide) hnat)
    have hz' : (star z).norm=(q:ℤ)^d := by rwa [Zsqrtd.norm_conj]
    exact hunit (star z) hz' (generator_pow_dvd_of_norm hD (Nat.prime_iff_prime_int.mp hq) d _ hz'
      (by simpa using hnot)) rfl
  · exact hunit z hz (generator_pow_dvd_of_norm hD (Nat.prime_iff_prime_int.mp hq) d _ hz h) rfl

/-- Hirakawa, Theorem 2.3, in the published divisor-sum notation. -/
theorem sigma_prime_pow_not_square_of_one_mod_four {q e : ℕ} (hq : q.Prime) (hq4 : q%4=1)
    (he : 0 < e) : ¬IsSquare (sigma 1 (q^e)) := by
  rw [sigma_one_apply_prime_pow hq]
  exact geometricBlock_not_square_of_prime_one_mod_four hq hq4 (by omega)

end OddPerfect
