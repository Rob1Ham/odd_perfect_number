module

public import OddPerfect.OddValuationGraph
public import OddPerfect.OddValuationCycleObstruction
public import OddPerfect.Reciprocity
public import OddPerfect.ComponentIndexMatrix
public import OddPerfect.GlobalObstruction
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Valuation Matrix Linear Algebra over `𝔽₂` (`OddPerfect.ValuationMatrixLinearAlgebra`)

Formalizes the `𝔽₂`-linear algebra of the odd-valuation incidence matrix `oddSigmaMatrix N`
and off-diagonal component-index factorization sums:

1. `oddSigmaMatrix`: the `↥N.primeFactors × ↥N.primeFactors` matrix over `ZMod 2` recording
   `v_r(σ(p^{v_p(N)})) mod 2`, with entrywise characterization and zero diagonal.
2. `vecMul_ones_oddSigmaMatrix_eq_single`, `oddSigmaMatrix_mulVec_ones_apply`, and
   `sum_oddSigmaTargets_card_odd`: exact column-sum cokernel (`1 ᵥ* oddSigmaMatrix N = e_q`)
   and global target-count parity (`Odd (∑ p ∈ N.primeFactors, (oddSigmaTargets N p).card)`).
3. `oddSigmaMatrix_right_kernel_avoids_euler` and
   `oddSigmaMatrix_even_hit_subset_avoids_euler_and_det_zero`: right-kernel orthogonality to the
   Euler prime `q` and determinant obstruction from any nonempty evenly hit target subset.
4. `oddSigmaMatrix_left_kernel_jacobi_and_det_zero`: left-kernel determinant vanishing,
   square-product obstruction, and Jacobi reciprocity laws from any nonempty evenly hit
   non-Euler source subset.
5. `sum_offDiag_componentIndex_factorization`: exact global off-diagonal component-index
   factorization sum `(ω(N) - 2) * Ω(N)`.
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset
open scoped Matrix NumberTheorySymbols

/-! ## 1. `𝔽₂` Odd-Valuation Operator -/

/-- The `𝔽₂` odd-valuation matrix on `N.primeFactors`: entry `(p, r)` is
`v_r(σ(p^{v_p(N)})) mod 2`. -/
@[expose] noncomputable def oddSigmaMatrix (N : ℕ) :
    Matrix ↥N.primeFactors ↥N.primeFactors (ZMod 2) :=
  Matrix.of fun p r =>
    (((sigma 1 (p.1 ^ N.factorization p.1)).factorization r.1 : ℕ) : ZMod 2)

theorem oddSigmaMatrix_apply_eq_one_iff {N : ℕ} (p r : ↥N.primeFactors) :
    oddSigmaMatrix N p r = 1 ↔ oddSigmaEdge N p.1 r.1 := by
  simp only [oddSigmaMatrix, Matrix.of_apply, ZMod.natCast_eq_one_iff_odd, oddSigmaEdge]
  exact ⟨fun h => ⟨p.2, r.2, h⟩, fun h => h.2.2⟩

theorem oddSigmaMatrix_apply_eq_zero_iff {N : ℕ} (p r : ↥N.primeFactors) :
    oddSigmaMatrix N p r = 0 ↔ ¬ oddSigmaEdge N p.1 r.1 := by
  simp only [oddSigmaMatrix, Matrix.of_apply, ZMod.natCast_eq_zero_iff_even, oddSigmaEdge,
    ← Nat.not_odd_iff_even]
  exact ⟨fun h hE => h hE.2.2, fun h hO => h ⟨p.2, r.2, hO⟩⟩

theorem oddSigmaMatrix_diag_eq_zero {N : ℕ} (p : ↥N.primeFactors) :
    oddSigmaMatrix N p p = 0 :=
  (oddSigmaMatrix_apply_eq_zero_iff p p).mpr fun h => oddSigmaEdge_ne h rfl

/-! ## 2. Exact Column-Sum Cokernel & Global Target-Count Parity -/

private theorem sum_coe_sort_eq_sum {α : Type*} (s : Finset ℕ) (f : ℕ → α) [AddCommMonoid α] :
    (∑ x : ↥s, f x.1) = ∑ x ∈ s, f x := by
  simpa using Finset.sum_attach s f

theorem vecMul_ones_oddSigmaMatrix_eq_single {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (_hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    (fun _ : ↥N.primeFactors => (1 : ZMod 2)) ᵥ* oddSigmaMatrix N =
      Pi.single ⟨q, hq⟩ (1 : ZMod 2) := by
  ext r
  have hr_prime : r.1.Prime := Nat.prime_of_mem_primeFactors r.2
  have hr_odd : Odd r.1 := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors r.2)
  have hsum :
      ((fun _ : ↥N.primeFactors => (1 : ZMod 2)) ᵥ* oddSigmaMatrix N) r =
        ((N.factorization r.1 : ℕ) : ZMod 2) := by
    simp only [Matrix.vecMul, dotProduct, one_mul, oddSigmaMatrix, Matrix.of_apply]
    rw [← Nat.cast_sum, sum_coe_sort_eq_sum N.primeFactors
      (fun p => (sigma 1 (p ^ N.factorization p)).factorization r.1),
      ← factorization_eq_sum_sigma_factorizations hN hr_odd hr_prime]
  rw [hsum]
  by_cases hrq : r = ⟨q, hq⟩
  · subst hrq
    rw [Pi.single_eq_same, ZMod.natCast_eq_one_iff_odd]
    exact Nat.odd_iff.mpr (by dsimp; omega)
  · have hr_ne : r.1 ≠ q := fun h => hrq (Subtype.ext h)
    rw [Pi.single_eq_of_ne hrq, ZMod.natCast_eq_zero_iff_even]
    exact hev r.1 hr_ne

theorem oddSigmaMatrix_mulVec_ones_apply {N : ℕ} (p : ↥N.primeFactors) :
    (oddSigmaMatrix N *ᵥ (fun _ : ↥N.primeFactors => (1 : ZMod 2))) p =
      ((oddSigmaTargets N p.1).card : ZMod 2) := by
  simp only [Matrix.mulVec, dotProduct, mul_one]
  have hterm : ∀ r : ↥N.primeFactors,
      oddSigmaMatrix N p r = if r.1 ∈ oddSigmaTargets N p.1 then (1 : ZMod 2) else 0 := by
    intro r
    by_cases hr : r.1 ∈ oddSigmaTargets N p.1
    · rw [ite_eq_left hr]
      exact (oddSigmaMatrix_apply_eq_one_iff p r).mpr
        ⟨p.2, r.2, (Finset.mem_filter.mp hr).2⟩
    · rw [ite_eq_right hr]
      exact (oddSigmaMatrix_apply_eq_zero_iff p r).mpr
        fun h => hr (Finset.mem_filter.mpr ⟨r.2, h.2.2⟩)
  simp_rw [hterm]
  rw [sum_coe_sort_eq_sum N.primeFactors (fun r => if r ∈ oddSigmaTargets N p.1 then (1 : ZMod 2) else 0)]
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter]
  have hinter : N.primeFactors ∩ oddSigmaTargets N p.1 = oddSigmaTargets N p.1 :=
    Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
  rw [hinter]

theorem sum_oddSigmaTargets_card_odd {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    Odd (∑ p ∈ N.primeFactors, (oddSigmaTargets N p).card) ∧
      ∃ p ∈ N.primeFactors, Odd (oddSigmaTargets N p).card := by
  let ones : ↥N.primeFactors → ZMod 2 := fun _ => 1
  have hcast :
      ((∑ p ∈ N.primeFactors, (oddSigmaTargets N p).card : ℕ) : ZMod 2) = 1 := by
    rw [Nat.cast_sum, ← sum_coe_sort_eq_sum N.primeFactors (fun p => ((oddSigmaTargets N p).card : ZMod 2))]
    have hmul :
        (∑ p : ↥N.primeFactors, ((oddSigmaTargets N p.1).card : ZMod 2)) =
          ones ⬝ᵥ (oddSigmaMatrix N *ᵥ ones) := by
      simp only [dotProduct, ones, one_mul, oddSigmaMatrix_mulVec_ones_apply]
    rw [hmul, Matrix.dotProduct_mulVec,
      vecMul_ones_oddSigmaMatrix_eq_single ho hN hq hq4 he hev]
    simp [dotProduct, ones]
  have hsum_odd : Odd (∑ p ∈ N.primeFactors, (oddSigmaTargets N p).card) :=
    ZMod.natCast_eq_one_iff_odd.mp hcast
  refine ⟨hsum_odd, ?_⟩
  by_contra hnone
  push Not at hnone
  have heven : Even (∑ p ∈ N.primeFactors, (oddSigmaTargets N p).card) := by
    rw [Finset.even_sum_iff_even_card_odd,
      Finset.filter_eq_empty_iff.mpr (fun p hp => Nat.not_odd_iff_even.mpr (hnone p hp)),
      Finset.card_empty]
    exact Even.zero
  exact (Nat.not_odd_iff_even.mpr heven) hsum_odd

/-! ## 3. Right-Kernel Orthogonality & Determinant Obstruction -/

theorem oddSigmaMatrix_right_kernel_avoids_euler {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    {w : ↥N.primeFactors → ZMod 2} (hw : oddSigmaMatrix N *ᵥ w = 0) :
    w ⟨q, hq⟩ = 0 := by
  have hdot : (fun _ : ↥N.primeFactors => (1 : ZMod 2)) ⬝ᵥ (oddSigmaMatrix N *ᵥ w) = 0 := by
    rw [hw, dotProduct_zero]
  rw [Matrix.dotProduct_mulVec, vecMul_ones_oddSigmaMatrix_eq_single ho hN hq hq4 he hev] at hdot
  simpa [dotProduct, Pi.single_apply] using hdot

theorem oddSigmaMatrix_even_hit_subset_avoids_euler_and_det_zero {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    {T : Finset ℕ} (hT_ne : T.Nonempty) (hT_sub : T ⊆ N.primeFactors)
    (hT_even : ∀ p ∈ N.primeFactors, Even ((oddSigmaTargets N p ∩ T).card)) :
    q ∉ T ∧ (oddSigmaMatrix N).det = 0 := by
  let w : ↥N.primeFactors → ZMod 2 := fun r => if r.1 ∈ T then 1 else 0
  have hw_ne : w ≠ 0 := by
    obtain ⟨t, ht⟩ := hT_ne
    intro h0
    have hval := congrFun h0 ⟨t, hT_sub ht⟩
    dsimp [w] at hval
    rw [ite_eq_left ht] at hval
    exact one_ne_zero hval
  have hw_ker : oddSigmaMatrix N *ᵥ w = 0 := by
    ext p
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    have hterm : ∀ r : ↥N.primeFactors,
        oddSigmaMatrix N p r * w r =
          if r.1 ∈ oddSigmaTargets N p.1 ∩ T then (1 : ZMod 2) else 0 := by
      intro r
      dsimp [w]
      by_cases hrT : r.1 ∈ T
      · rw [ite_eq_left hrT, mul_one]
        by_cases hrt : r.1 ∈ oddSigmaTargets N p.1
        · rw [ite_eq_left (Finset.mem_inter.mpr ⟨hrt, hrT⟩)]
          exact (oddSigmaMatrix_apply_eq_one_iff p r).mpr
            ⟨p.2, r.2, (Finset.mem_filter.mp hrt).2⟩
        · rw [ite_eq_right (fun h => hrt (Finset.mem_inter.mp h).1)]
          exact (oddSigmaMatrix_apply_eq_zero_iff p r).mpr
            fun h => hrt (Finset.mem_filter.mpr ⟨r.2, h.2.2⟩)
      · rw [ite_eq_right hrT, mul_zero, ite_eq_right (fun h => hrT (Finset.mem_inter.mp h).2)]
    simp_rw [hterm]
    rw [sum_coe_sort_eq_sum N.primeFactors
      (fun r => if r ∈ oddSigmaTargets N p.1 ∩ T then (1 : ZMod 2) else 0)]
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter]
    have hinter : N.primeFactors ∩ (oddSigmaTargets N p.1 ∩ T) = oddSigmaTargets N p.1 ∩ T :=
      Finset.inter_eq_right.mpr ((Finset.inter_subset_left).trans (Finset.filter_subset _ _))
    rw [hinter, ZMod.natCast_eq_zero_iff_even]
    exact hT_even p.1 p.2
  have hwq : w ⟨q, hq⟩ = 0 :=
    oddSigmaMatrix_right_kernel_avoids_euler ho hN hq hq4 he hev hw_ker
  refine ⟨fun hqT => ?_, Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hw_ne, hw_ker⟩⟩
  dsimp [w] at hwq
  rw [ite_eq_left hqT] at hwq
  exact one_ne_zero hwq

/-! ## 4. Left-Kernel Square-Product & Jacobi Reciprocity Law -/

theorem oddSigmaMatrix_left_kernel_jacobi_and_det_zero {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    {U : Finset ℕ} (hU_ne : U.Nonempty) (hU_sub : U ⊆ N.primeFactors.erase q)
    (hU_even : ∀ r ∈ N.primeFactors, Even ((oddSigmaSources N r ∩ U).card)) :
    (oddSigmaMatrix N).det = 0 ∧
      IsSquare (∏ u ∈ U, sigma 1 (u ^ N.factorization u)) ∧
      ∀ u ∈ U, (∏ r ∈ oddSigmaTargets N u, J((r : ℤ) | u)) = 1 := by
  have hU_mem : U ⊆ N.primeFactors := hU_sub.trans (Finset.erase_subset q N.primeFactors)
  let v : ↥N.primeFactors → ZMod 2 := fun p => if p.1 ∈ U then 1 else 0
  have hv_ne : v ≠ 0 := by
    obtain ⟨u, hu⟩ := hU_ne
    intro h0
    have hval := congrFun h0 ⟨u, hU_mem hu⟩
    dsimp [v] at hval
    rw [ite_eq_left hu] at hval
    exact one_ne_zero hval
  have hv_ker : v ᵥ* oddSigmaMatrix N = 0 := by
    ext r
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    have hterm : ∀ p : ↥N.primeFactors,
        v p * oddSigmaMatrix N p r =
          if p.1 ∈ oddSigmaSources N r.1 ∩ U then (1 : ZMod 2) else 0 := by
      intro p
      dsimp [v]
      by_cases hpU : p.1 ∈ U
      · rw [ite_eq_left hpU, one_mul]
        by_cases hps : p.1 ∈ oddSigmaSources N r.1
        · rw [ite_eq_left (Finset.mem_inter.mpr ⟨hps, hpU⟩)]
          exact (oddSigmaMatrix_apply_eq_one_iff p r).mpr
            ⟨p.2, r.2, (Finset.mem_filter.mp hps).2⟩
        · rw [ite_eq_right (fun h => hps (Finset.mem_inter.mp h).1)]
          exact (oddSigmaMatrix_apply_eq_zero_iff p r).mpr
            fun h => hps (Finset.mem_filter.mpr ⟨p.2, h.2.2⟩)
      · rw [ite_eq_right hpU, zero_mul, ite_eq_right (fun h => hpU (Finset.mem_inter.mp h).2)]
    simp_rw [hterm]
    rw [sum_coe_sort_eq_sum N.primeFactors
      (fun p => if p ∈ oddSigmaSources N r.1 ∩ U then (1 : ZMod 2) else 0)]
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter]
    have hinter : N.primeFactors ∩ (oddSigmaSources N r.1 ∩ U) = oddSigmaSources N r.1 ∩ U :=
      Finset.inter_eq_right.mpr ((Finset.inter_subset_left).trans (Finset.filter_subset _ _))
    rw [hinter, ZMod.natCast_eq_zero_iff_even]
    exact hU_even r.1 r.2
  have hdet : (oddSigmaMatrix N).det = 0 :=
    Matrix.exists_vecMul_eq_zero_iff.mp ⟨v, hv_ne, hv_ker⟩
  have hS_ne0 : ∀ u ∈ U, sigma 1 (u ^ N.factorization u) ≠ 0 := by
    intro u hu
    have hu_prime := Nat.prime_of_mem_primeFactors (hU_mem hu)
    exact (sigma_pos 1 _ (pow_ne_zero _ hu_prime.ne_zero)).ne'
  have hS_odd : ∀ u ∈ U, Odd (sigma 1 (u ^ N.factorization u)) := by
    intro u hu
    have hu_mem := hU_mem hu
    have hu_neq : u ≠ q := (Finset.mem_erase.mp (hU_sub hu)).1
    have hu_prime := Nat.prime_of_mem_primeFactors hu_mem
    have hu_odd := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hu_mem)
    have hpow_odd : Odd (u ^ N.factorization u) := hu_odd.pow
    obtain ⟨k, hk⟩ := hev u hu_neq
    have hpow_sq : IsSquare (u ^ N.factorization u) := ⟨u ^ k, by rw [hk, pow_add]⟩
    exact (odd_sigma_iff_square_of_odd hpow_odd).mpr hpow_sq
  have hsig_prod : (∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p)) = 2 * N := by
    trans sigma 1 N
    · exact (isMultiplicative_sigma.multiplicative_factorization _ hN.2.ne').symm
    · rw [sigma_one_apply]
      exact (Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN
  have hsq : IsSquare (∏ u ∈ U, sigma 1 (u ^ N.factorization u)) := by
    rw [Nat.isSquare_iff_even_factorization]
    intro r hr_prime
    rw [Nat.factorization_prod_apply hS_ne0]
    by_cases hr2 : r = 2
    · subst hr2
      have hzero : ∀ u ∈ U, (sigma 1 (u ^ N.factorization u)).factorization 2 = 0 := by
        intro u hu
        exact Nat.factorization_eq_zero_of_not_dvd (hS_odd u hu).not_two_dvd_nat
      simp [Finset.sum_congr rfl hzero]
    · by_cases hrN : r ∈ N.primeFactors
      · rw [Finset.even_sum_iff_even_card_odd]
        have hfilter :
            U.filter (fun u => Odd ((sigma 1 (u ^ N.factorization u)).factorization r)) =
              oddSigmaSources N r ∩ U := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_inter, oddSigmaSources]
          constructor
          · rintro ⟨huU, hodd⟩
            exact ⟨⟨hU_mem huU, hodd⟩, huU⟩
          · rintro ⟨⟨_, hodd⟩, huU⟩
            exact ⟨huU, hodd⟩
        rw [hfilter]
        exact hU_even r hrN
      · have hzero : ∀ u ∈ U, (sigma 1 (u ^ N.factorization u)).factorization r = 0 := by
          intro u hu
          refine Nat.factorization_eq_zero_of_not_dvd fun hdvd => hrN ?_
          have hdvd_prod : sigma 1 (u ^ N.factorization u) ∣ 2 * N := by
            rw [← hsig_prod]
            exact Finset.dvd_prod_of_mem _ (hU_mem hu)
          have hr_dvd_2N : r ∣ 2 * N := hdvd.trans hdvd_prod
          have hr_ndvd2 : ¬ r ∣ 2 := fun h =>
            hr2 (((Nat.dvd_prime Nat.prime_two).mp h).resolve_left hr_prime.ne_one)
          have hr_dvd_N : r ∣ N := (hr_prime.coprime_iff_not_dvd.mpr hr_ndvd2).dvd_of_dvd_mul_left hr_dvd_2N
          exact Nat.mem_primeFactors.mpr ⟨hr_prime, hr_dvd_N, hN.2.ne'⟩
        simp [Finset.sum_congr rfl hzero]
  refine ⟨hdet, hsq, fun u hu => ?_⟩
  exact jacobi_prod_oddSigmaTargets_of_even hN ho (hU_mem hu)
    (hev u (Finset.mem_erase.mp (hU_sub hu)).1)

/-! ## 5. Off-Diagonal Component-Index Factorization Sum -/

theorem sum_offDiag_componentIndex_factorization {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    (∑ p ∈ N.primeFactors, ∑ r ∈ N.primeFactors.erase p, (componentIndex N p).factorization r) =
      (N.primeFactors.card - 2) * cardFactors N := by
  have hdiag : ∀ p ∈ N.primeFactors,
      (∑ r ∈ N.primeFactors.erase p, (componentIndex N p).factorization r) =
        ∑ r ∈ N.primeFactors, (componentIndex N p).factorization r := by
    intro p hp
    have h := Finset.add_sum_erase N.primeFactors (fun r => (componentIndex N p).factorization r) hp
    rw [componentIndex_factorization_self_eq_zero ho hN hp, zero_add] at h
    exact h
  calc
    (∑ p ∈ N.primeFactors, ∑ r ∈ N.primeFactors.erase p, (componentIndex N p).factorization r)
        = ∑ p ∈ N.primeFactors, ∑ r ∈ N.primeFactors, (componentIndex N p).factorization r :=
          Finset.sum_congr rfl hdiag
    _ = ∑ r ∈ N.primeFactors, ∑ p ∈ N.primeFactors, (componentIndex N p).factorization r :=
          Finset.sum_comm
    _ = ∑ r ∈ N.primeFactors, (N.primeFactors.card - 2) * N.factorization r := by
          refine Finset.sum_congr rfl fun r hr => ?_
          exact (sum_componentIndex_factorization_conservation ho hN).1 r hr
    _ = (N.primeFactors.card - 2) * ∑ r ∈ N.primeFactors, N.factorization r := by
          rw [Finset.mul_sum]
    _ = (N.primeFactors.card - 2) * cardFactors N := by
          rw [cardFactors_eq_sum_factorization]
          congr 1

end OddPerfect
