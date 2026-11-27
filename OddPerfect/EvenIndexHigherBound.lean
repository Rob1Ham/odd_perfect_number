module

public import OddPerfect.EvenIndexHigherCongruence
public import OddPerfect.EvenIndexCoefficients
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.FieldSimp

public section
namespace OddPerfect
open ArithmeticFunction Finset ReturnLift

/-- Bound each truncated polynomial by evaluating its positive
coefficient majorant at 1/64. -/
theorem even_index_truncatedSum_le {q p s u : ℕ} (hp : p.Prime) (hs : Odd s)
    (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2) (hσs : sigma 1 (s^2)=p^(2*u))
    (k shift : ℕ) : truncatedSum s.primeFactors (sourceMultiplicity s p) k shift p≤4*(u+1)*128^k*p^k := by
  let z : ℚ := 1/64
  let v := sourceMultiplicity s p
  let S := s.primeFactors
  let U := terms S k
  let A := ((64:ℚ)*p)^k
  have hnonA : 0≤A := by dsimp [A]; positivity
  have hnonz : 0≤z := by norm_num [z]
  have hlocal (t : Finset ℕ × ℕ) : (term v k shift p t:ℚ)≤A*((weight k t:ℚ)*z^(degree v t)) := by
    by_cases h : degree v t+shift≤k
    · have h1 := pow_le_pow_right₀ (by decide : (1:ℚ)≤64) (by omega : degree v t≤k)
      have hp1 : (1:ℚ)≤p := by exact_mod_cast hp.one_le
      have h2 := pow_le_pow_right₀ hp1 h
      have H := mul_le_mul h2 h1 (by positivity : (0:ℚ)≤64^(degree v t)) (by positivity : (0:ℚ)≤(p:ℚ)^k)
      have hdiv : (p:ℚ)^(degree v t+shift)≤A/64^(degree v t) := by
        rw [le_div_iff₀ (by positivity : (0:ℚ)<64^(degree v t))]
        simpa [A,mul_pow,mul_comm] using H
      simp only [term,ite_eq_left h,Nat.cast_mul,Nat.cast_pow]
      calc _ ≤ (weight k t:ℚ)*(A/64^(degree v t)) := mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg _)
           _ = _ := by simp only [z,one_div_pow]; ring
    · simp only [term,ite_eq_right h,Nat.cast_zero]
      exact mul_nonneg hnonA (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hnonz _))
  let H := ∑ a ∈ range (k+1),z^a*2^(k-a)
  have hH : H≤2*2^k := by
    have hg := geom_sum_mul_neg z (k+1)
    have hg' : (∑a ∈ range (k+1),z^a)≤2 := by
      have hz : z=1/64 := rfl
      have hpos := pow_nonneg hnonz (k+1)
      rw [hz] at hg
      dsimp [z] at hpos ⊢
      linarith
    have h := Finset.sum_le_sum (s:=range (k+1)) (fun a _ =>
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by decide : (1:ℚ)≤2) (Nat.sub_le k a)) (pow_nonneg hnonz a))
    rw [←Finset.sum_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right hg' (by positivity))
  let D := ∏r ∈ S,(1+((r-1:ℕ):ℚ)*z^(v r))
  have hD : D≤2*((u:ℚ)+1) := by
    simpa [D,z,v,S,one_div_pow,div_eq_mul_inv] using even_index_weighted_return_product hp hs hσq hplus hσs
  have heq := sum_weighted_powers z S v k
  change (∑t ∈ U,(weight k t:ℚ)*z^(degree v t))=D*H at heq
  have hsum := Finset.sum_le_sum (s:=U) (fun t _ => hlocal t)
  rw [←Nat.cast_sum,←Finset.mul_sum,heq] at hsum
  have hnonH : 0≤H := Finset.sum_nonneg (fun a _ => mul_nonneg (pow_nonneg hnonz _) (by positivity))
  have hfinal := hsum.trans (mul_le_mul_of_nonneg_left (mul_le_mul hD hH hnonH (by positivity)) hnonA)
  have ident : A*(2*((u:ℚ)+1)*(2*2^k))=4*((u:ℚ)+1)*128^k*p^k := by
    dsimp [A]
    rw [show (128:ℚ)=64*2 by norm_num,mul_pow,mul_pow]
    ring
  rw [ident] at hfinal
  exact_mod_cast hfinal

/-- The base is at most the explicit truncation threshold or its
(k+1)-st power is bounded in terms of the radical. -/
theorem even_index_base_higher_lift_bound {q p s u k : ℕ} (hp : p.Prime) (hpo : Odd p)
    (hs : Odd s) (hk : 0<k) (hkj : k≤2*u) (hσq : sigma 1 (p^(2*u))=q)
    (hplus : q+1=2*s^2) (hσs : sigma 1 (s^2)=p^(2*u)) :
    p≤8*(u+1)*128^k ∨ p^(k+1)≤2^(k+1)*s.primeFactors.prod id := by
  by_cases hsmall : p≤8*(u+1)*128^k
  · exact .inl hsmall
  right
  let P := s.primeFactors.prod id
  let v := sourceMultiplicity s p
  let C := truncatedSum s.primeFactors v k 0 p
  let B := truncatedSum s.primeFactors v k 1 p
  let L := 4*(u+1)*128^k*p^k
  have hC : C≤L := even_index_truncatedSum_le hp hs hσq hplus hσs k 0
  have hB : B≤L := even_index_truncatedSum_le hp hs hσq hplus hσs k 1
  have hL : 2*L<p^(k+1) := by
    have hh := Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_ge hsmall) (pow_pos hp.pos k)
    dsimp [L]
    rw [pow_succ']; nlinarith only [hh]
  have hh := even_index_radical_higher_congruence hp hpo hs hkj hσq hplus hσs
  change 2^k*P+B ≡ C [MOD p^(k+1)] at hh
  have hparts := (even_index_source_valuation_budget hp hs hσq hplus hσs).2
  obtain ⟨hodd,heven⟩ := truncatedSum_parity (k:=k) hpo (fun r hr => (hparts r hr).1.pos)
  change Odd C at hodd
  change Even B at heven
  have he : Even (2^k*P+B) := ((even_two.pow_of_ne_zero hk.ne').mul_right _).add heven
  have hge : p^(k+1)≤2^k*P+B := by
    by_contra! h
    have heq := hh.eq_of_lt_of_lt h (by omega)
    exact (Nat.not_even_iff_odd.mpr hodd) (heq ▸ he)
  change _≤2^(k+1)*P
  rw [pow_succ' 2 k, mul_assoc]
  omega

end OddPerfect
