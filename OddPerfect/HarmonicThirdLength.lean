module

public import OddPerfect.HarmonicRoots
public import OddPerfect.DivisorCountValuation
import Mathlib.Tactic.Ring

public section

namespace OddPerfect.HarmonicChain
open ArithmeticFunction Finset

/-- The third cyclotomic value at an odd p has no factor 2 and contains
at most one copy of 3. -/
private theorem phi_three_cofactor {p : ℕ} (hp : Odd p) :
    ∃ c : ℕ, c.Coprime 6 ∧ c ∣ p^2+p+1 ∧ p^2+p+1 ≤ 3*c := by
  let S := p^2+p+1
  have resid : S%18 = ((p%18)^2+p%18+1)%18 := by
    simp [S, Nat.add_mod, Nat.pow_mod]
  have po := Nat.odd_iff.mp hp
  have check : ∀ a : Fin 18, a.val%2=1 →
      ((a.val^2+a.val+1)%18) ∈ ([1,3,7,13] : List ℕ) := by decide +kernel
  have hmem := check ⟨p%18,Nat.mod_lt _ (by decide)⟩ (by simpa using po)
  rw [← resid] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  have mod6 (x : ℕ) (h : x%6=1 ∨ x%6=5) : x.Coprime 6 := by
    change x.gcd 6=1
    rw [Nat.gcd_comm, Nat.gcd_rec]
    rcases h with h | h <;> rw [h] <;> decide
  rcases hmem with h|h|h|h
  · exact ⟨S,mod6 _ (by omega), dvd_rfl, by omega⟩
  · exact ⟨S/3,mod6 _ (by omega), ⟨3, by omega⟩, by omega⟩
  · exact ⟨S,mod6 _ (by omega), dvd_rfl, by omega⟩
  · exact ⟨S,mod6 _ (by omega), dvd_rfl, by omega⟩

/-- Cohen–Sorli's quadratic-component cutoff applies to every component
whose length is divisible by three. -/
theorem Small.base_lt_of_three_dvd_length {n p : ℕ} (H : Small n 3)
    (hp : p ∈ n.primeFactors) (hlen : 3∣n.factorization p+1) : p < 1316099 := by
  have pr := Nat.prime_of_mem_primeFactors hp
  have pd := Nat.dvd_of_mem_primeFactors hp
  obtain ⟨c,hc,hcs,hle⟩ := phi_three_cofactor (H.odd.of_dvd_nat pd)
  have hcτ : c.Coprime n.divisors.card := H.coprime_divisor_count hc
  have hg : p^2+p+1 ∣ sigma 1 (p^n.factorization p) := by
    obtain ⟨j,hj⟩ := hlen
    rw [show sigma 1 (p^n.factorization p) = geometricBlock p (n.factorization p+1)
        from sigma_one_apply_prime_pow pr]
    rw [hj,geometricBlock_mul]
    have eq : geometricBlock p 3 = p^2+p+1 := by
      simp [geometricBlock, sum_range_succ]; omega
    rw [eq]
    exact dvd_mul_right _ _
  have hs : sigma 1 (p^n.factorization p) ∣ sigma 1 n := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ H.odd.pos.ne']
    exact dvd_prod_of_mem _ hp
  have hcn := hcτ.dvd_of_dvd_mul_right (hcs.trans (hg.trans (hs.trans H.harmonic.2)))
  have hn := Nat.le_of_dvd (Nat.succ_pos _) hlen
  have pp := (pr.pow_dvd_iff_le_factorization H.odd.pos.ne').mpr (by omega : 2≤n.factorization p)
  have cop : p.Coprime c := pr.coprime_iff_not_dvd.mpr (by
    intro h
    have h1 := h.trans hcs
    have hbase : p∣p^2+p := dvd_add (dvd_pow_self p (by decide : 2≠0)) dvd_rfl
    exact pr.not_dvd_one ((Nat.dvd_add_iff_right hbase).mpr h1))
  have hprod := Nat.le_of_dvd H.odd.pos ((cop.pow_left 2).mul_dvd_of_dvd_of_dvd pp hcn)
  by_contra! hb
  have min := Nat.pow_le_pow_left hb 4
  have threshold : 3*(10:ℕ)^24 < 1316099^4 := by decide +kernel
  have hscaled := Nat.mul_le_mul_left (p^2) hle
  nlinarith [H.size]

end OddPerfect.HarmonicChain
