module

public import OddPerfect.IndexSieveTrials
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect.IndexSieve

open ArithmeticFunction Finset

structure TrialRow extends Row where
  trials : List ℕ

/-- The witnesses are independently checked prime. Every positive divisor
of a listed residual with one of those values identifies the Euler prime. -/
@[expose] def TrialRow.valid (w : TrialRow) : Prop :=
  w.firstPrime ∈ w.index.primeFactors ∧ w.secondPrime ∈ w.index.primeFactors ∧
   (∀ c ∈ w.trials, c.Prime) ∧ 4+(w.index.primeFactors.card+cardFactors w.index)<2^4 ∧
   ¬TrialCompatible w.index w.firstPrime w.secondPrime (supportBound w.index/2) (residueModulus w.index) w.trials

instance (w : TrialRow) : Decidable w.valid :=
  inferInstanceAs (Decidable (w.firstPrime ∈ w.index.primeFactors ∧ w.secondPrime ∈ w.index.primeFactors ∧
   (∀ c ∈ w.trials, c.Prime) ∧ 4+(w.index.primeFactors.card+cardFactors w.index)<2^4 ∧
   ¬TrialCompatible w.index w.firstPrime w.secondPrime (supportBound w.index/2) (residueModulus w.index) w.trials))

theorem excludes_of_valid_trial_row {N q a m i : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (ha : 1<a) (hqm : ¬q ∣ m) (hform : N=q^a*m^2)
    (hl : sigma 1 (m^2)=q^a*i) (hr : sigma 1 (q^a)*i=2*m^2) (hio : Odd i)
    (w : TrialRow) (hw : w.valid) : i ≠ w.index := by
  intro heq
  obtain ⟨hpI,hrI,htr,hweight,hbad⟩ := hw
  rw [←heq] at hpI hrI hweight hbad
  have hao : Odd a := Nat.odd_iff.mpr (by omega)
  have hmo := ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2≠0)).trans (dvd_mul_left _ _))
  have hqo := ho.of_dvd_nat (hform ▸ (dvd_pow_self q hao.pos.ne').trans (dvd_mul_right _ _))
  have hqi : q.Coprime i := hq.coprime_iff_not_dvd.mpr (fun h => hqm (hq.dvd_of_dvd_pow
    ((Nat.coprime_two_right.mpr hqo).dvd_of_dvd_mul_left (hr ▸ h.trans (dvd_mul_left _ _)))))
  have hbound : (a+1).divisors.card ≤ supportBound i := by
    unfold supportBound
    dsimp only
    split_ifs with h
    · have h3 : 3+(i.primeFactors.card+cardFactors i)<2^3 := by omega
      have := euler_index_weight_bounds hN ho hq hao hqm hform hl hr (Nat.le_refl _) h3
      omega
    · have := euler_index_weight_bounds hN ho hq hao hqm hform hl hr (Nat.le_refl _) hweight
      omega
  have cofactor (p : ℕ) (hp : p ∈ i.primeFactors) : p ∈ m.primeFactors := by
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hd := Nat.dvd_of_mem_primeFactors hp
    have hdm : p ∣ m := hpr.dvd_of_dvd_pow ((Nat.coprime_two_right.mpr (hio.of_dvd_nat hd)).dvd_of_dvd_mul_left
      (hr ▸ hd.trans (dvd_mul_left _ _)))
    exact Nat.mem_primeFactors.mpr ⟨hpr,hdm,hmo.pos.ne'⟩
  obtain ⟨hM,hqM⟩ := euler_modulus hN ho hq hq4 ha4 ha hqm hform hl
  exact hbad (trial_compatible_of_euler_index hq hao hmo.pos hmo hio hqi hM hqM (cofactor _ hpI)
    (cofactor _ hrI) (by omega) hl hr w.trials htr)

end OddPerfect.IndexSieve
