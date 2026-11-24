module

public import OddPerfect.EvenIndexDeterminant
public import OddPerfect.EvenIndexBaseBound
public import OddPerfect.ExponentOneSize
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Abs

public section
namespace OddPerfect
open ArithmeticFunction Finset Matrix

/-- Dropping permutation signs and then allowing all functions in place
of permutations bounds the absolute determinant by the product of the
row sums of absolute values. -/
theorem abs_int_det_le_prod_row_sums {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℤ) : |M.det| ≤ ∏ i,∑ j,|M i j| := by
  classical
  let f (g : α→α) := ∏ i,|M i (g i)|
  let co (g : Equiv.Perm α) : α→α := g
  have hinj : Set.InjOn co (↑(univ : Finset (Equiv.Perm α)) : Set _) :=
    fun _ _ _ _ h => Equiv.ext (congrFun h)
  have hprod (g : Equiv.Perm α) :
      |(Equiv.Perm.sign g : ℤˣ) • (∏ i,M i (g i))| = f (co g) := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h|h <;> simp [h,f,co,Finset.abs_prod]
  have H : ∑ g : Equiv.Perm α, f (co g) ≤ ∑ g : α→α, f g := by
    rw [←Finset.sum_image hinj]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ =>
      Finset.prod_nonneg (fun _ _ => abs_nonneg _))
  calc |M.det| = |Mᵀ.det| := by rw [Matrix.det_transpose]
       _ ≤ ∑ g : Equiv.Perm α, |(Equiv.Perm.sign g : ℤˣ) • (∏ i,M i (g i))| := by
          rw [Matrix.det_apply]
          exact Finset.abs_sum_le_sum_abs _ _
       _ = ∑ g : Equiv.Perm α, f (co g) := Finset.sum_congr rfl (fun g _ => hprod g)
       _ ≤ ∑ g : α→α, f g := H
       _ = ∏ i,∑ j,|M i j| := (Fintype.prod_sum (fun i j => |M i j|)).symm

/-- The anchored row has absolute weight one. Every other row has
absolute weight at most four, including when cyclic neighbors coincide. -/
theorem returnDeterminant_le_four_pow_pred (β n : ℕ) : returnDeterminant β n≤4^(β-1) := by
  cases β with
  | zero => simp [returnDeterminant]
  | succ b =>
    let M := returnMatrix ℤ b n
    have row (i : ZMod (b+1)) : ∑ j,|M i j| ≤ (if i=0 then 1 else 4) := by
      by_cases hi : i=0
      · simp [M,returnMatrix,hi,apply_ite abs]
      rw [ite_eq_right hi]
      let w (j : ZMod (b+1)) : ℤ := (if j=i then 2 else 0)+(if j=i+1 then 1 else 0)+
        (if j=i+n then 1 else 0)
      have hw (j : ZMod (b+1)) : |M i j| ≤ w j := by
        simp only [M,returnMatrix,w,ite_eq_right hi]
        split_ifs <;> decide
      have hsum : ∑ j,w j≤4 := by simp [w,Finset.sum_add_distrib]
      exact (Finset.sum_le_sum (fun j _ => hw j)).trans hsum
    have H := (abs_int_det_le_prod_row_sums M).trans (Finset.prod_le_prod₀ (s:=univ) (g:=fun i => if i=0 then (1:ℤ) else 4)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (fun i _ => row i))
    change M.det.natAbs≤4^b
    rw [← Nat.cast_le (α:=ℤ),Int.natCast_natAbs,Nat.cast_pow,Nat.cast_ofNat]
    simpa [Finset.prod_ite,Finset.filter_ne',Finset.card_erase_of_mem] using H

/-- For fixed exponent 2u the cofactor radical has an explicit
singly exponential upper bound independent of the index prime. -/
theorem even_index_cofactor_radical_le {q p s u : ℕ}
    (hp : p.Prime) (hs : Odd s) (hσq : sigma 1 (p^(2*u))=q)
    (hplus : q+1=2*s^2) (hσs : sigma 1 (s^2)=p^(2*u)) :
    s.primeFactors.prod id≤(u+1)*4^(2*u-s.primeFactors.card) := by
  let S := s.primeFactors
  let v (r : ℕ) := (sigma 1 (r^(2*s.factorization r))).factorization p
  let F := (u+1).primeFactors
  let U := S.filter (· ∈ F)
  let V := S.filter (fun r => ¬ r∈F)
  obtain ⟨hsum,hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  change ∑ r ∈ S,v r=2*u at hsum
  have hU : U.prod id≤u+1 := by
    apply Nat.le_of_dvd (by omega)
    exact (Finset.prod_dvd_prod_of_subset U F id (fun r hr => (Finset.mem_filter.mp hr).2)).trans
      (Nat.prod_primeFactors_dvd _)
  have hlocal (r : ℕ) (hV : r∈V) : r≤4^(v r-1) := by
    obtain ⟨hr,hnot⟩ := Finset.mem_filter.mp hV
    obtain ⟨hβ,hout⟩ := hparts r hr
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hrs := Nat.dvd_of_mem_primeFactors hr
    have hro := hs.of_dvd_nat hrs
    obtain ⟨hpow,hrel,hone⟩ := even_index_source_root_equations hp hrp hrs hσq hplus hout
    have hx : (p:ZMod r)≠1 := by
      intro h
      have hd : r ∣ u+1 := (Nat.coprime_two_right.mpr hro).dvd_of_dvd_mul_left
        (show r ∣ 2*(u+1) by simpa only [Nat.mul_add,Nat.mul_one] using hone h)
      exact hnot (Nat.mem_primeFactors.mpr ⟨hrp,hd,by omega⟩)
    have hD := prime_dvd_returnDeterminant hrp hβ.pos hx hpow hrel
    exact (Nat.le_of_dvd (returnDeterminant_pos _ _) hD).trans (returnDeterminant_le_four_pow_pred _ _)
  have hmass : (∑ r ∈ S,(v r-1)) + S.card=2*u := by
    have hh : ∑ r ∈ S,((v r-1)+1) = 2*u := by
      rw [←hsum]
      exact Finset.sum_congr rfl (fun r hr => Nat.sub_add_cancel (hparts r hr).1.pos)
    simpa only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,mul_one] using hh
  have hV : V.prod id≤4^(2*u-S.card) := by
    have hval := Finset.sum_le_sum_of_subset_of_nonneg (show V ⊆ S from Finset.filter_subset _ _)
      (fun r _ _ => Nat.zero_le (v r-1))
    calc V.prod id ≤ ∏ r ∈ V,4^(v r-1) := Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) hlocal
         _ = 4^(∑ r ∈ V,(v r-1)) := Finset.prod_pow_eq_pow_sum ..
         _ ≤ 4^(2*u-S.card) := Nat.pow_le_pow_right (by decide) (by omega)
  exact (S.prod_filter_mul_prod_filter_not (fun r => r∈F) id) ▸ Nat.mul_le_mul hU hV

/-- A fully explicit exponent-only bound for the prime base. -/
theorem even_prime_power_index_base_le {q p s u : ℕ} (hp : p.Prime) (hs : Odd s) (hu : 0<u)
    (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2) (hσs : sigma 1 (s^2)=p^(2*u)) :
    p ≤ 2*(2*u+3)*((u+1)*4^(2*u)) := by
  have H := even_index_base_le_cofactor_radical hp hs hu hσq hplus hσs
  have hw := (even_index_cofactor_prime_count hp hs hσq hplus hσs).2
  exact H.trans (Nat.mul_le_mul (by omega) ((even_index_cofactor_radical_le hp hs hσq hplus hσs).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)))))

/-- A prime-power index with even exponent 2u at any exact component
bounds both its prime base and the entire odd perfect number explicitly. -/
theorem even_prime_power_component_explicit_bounds {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0<a)
    (hform : N=q^a*b) (hqb : ¬q ∣ b) (hl : sigma 1 b=q^a*i)
    (hr : sigma 1 (q^a)*i=2*b) (hp : p.Prime) (hu : 0<u) (hi : i=p^(2*u)) :
    let B := 14*(u+1)*4^(2*u-4)
    p≤B ∧ N<2*B^(6*u) := by
  obtain ⟨ha1,hσ⟩ := even_prime_power_index_eq_selected_sigma hN ho hq ha hform hqb hl hr hp hu hi
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b _)
  have hp2 : p≠2 := by
    rintro rfl
    have h4 : 4 ∣ 2*b := hr ▸ hi ▸ (pow_dvd_pow 2 (by omega : 2≤2*u)).trans (dvd_mul_left _ _)
    have := hbo.not_two_dvd_nat
    omega
  have hpo := hp.odd_of_ne_two hp2
  obtain ⟨m,_,_,hqm,rfl⟩ := euler_form_of_odd_component_index hN ho hq ha hform hqb hl hr (hi ▸ hpo.pow)
  have hmo := ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2≠0)) _)
  rw [ha1,pow_one] at hform hl hr
  rw [hi] at hl hr
  obtain ⟨s,hso,hcop,hms,_,hplus,hσs⟩ := even_prime_power_cofactor_split hq hp hmo hpo hu hl hr
  let w := s.primeFactors.card
  have hn := prime_count_of_even_index_split hq hp hmo hso hu hqm hcop hform hms
  have hmin := five_le_distinct_prime_factor_count ho hN
  obtain ⟨hpar,hw⟩ := even_index_cofactor_prime_count hp hso hσ hplus hσs
  change w≤2*u at hw
  have hw4 : 4≤w := by dsimp [w]; have := Nat.even_iff.mp hpar; omega
  have growth (t : ℕ) : t+7≤7*4^t := by
    induction t with
    | zero => decide
    | succ t ih => rw [pow_succ]; omega
  have hwg : w+3≤7*4^(w-4) := by have := growth (w-4); omega
  let B := 14*(u+1)*4^(2*u-4)
  have hbound : p≤B := by
    calc p ≤ 2*(w+3)*s.primeFactors.prod id := even_index_base_le_cofactor_radical hp hso hu hσ hplus hσs
         _ ≤ 2*(7*4^(w-4))*((u+1)*4^(2*u-w)) :=
           Nat.mul_le_mul (Nat.mul_le_mul_left _ hwg) (even_index_cofactor_radical_le hp hso hσ hplus hσs)
         _ = B := by dsimp [B]; rw [show 2*u-4=(w-4)+(2*u-w) by omega,pow_add]; ring
  have H := (exponent_one_size_lt_twice_index_cube hN ho hq hqm hform).2.2
  rw [hl,Nat.mul_div_cancel_left _ hq.pos,←pow_mul,show 2*u*3=6*u by omega] at H
  exact ⟨hbound,H.trans_le (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbound _))⟩

end OddPerfect
