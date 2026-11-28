module

public import OddPerfect.IndexSieveExactLengths
public import OddPerfect.EulerIndexSieve
import OddPerfect.SemiprimeSources
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect.IndexSieve

open ArithmeticFunction Finset

/-- Geometric sums in a form that needs only one exponentiation for each length. -/
@[expose] def repunit (p d : ℕ) : ℕ := (p^d-1)/(p-1)

theorem repunit_eq_sigma {p e : ℕ} (hp : p.Prime) : repunit p (e+1)=sigma 1 (p^e) := by
  rw [sigma_one_apply_prime_pow hp]
  exact (Nat.eq_div_of_mul_eq_left (by have := hp.one_lt; omega)
    (geom_sum_mul_of_one_le (by have := hp.one_lt; omega : 1≤p) (e+1))).symm

/-- Each exact source spends the gcd of its sum with the index; separate
sources must fit inside the index with multiplicity. -/
theorem spent_mul_dvd_index {q a i m p r : ℕ} (hq : q.Coprime i) (hm : 0<m)
    (hp : p ∈ m.primeFactors) (hr : r ∈ m.primeFactors) (hne : p≠r)
    (hl : sigma 1 (m^2)=q^a*i) :
    (sigma 1 (p^(2*m.factorization p))).gcd i *
      (sigma 1 (r^(2*m.factorization r))).gcd i ∣ i := by
  let f (s : ℕ) := sigma 1 (s^((m^2).factorization s))
  have hpm : p ∈ (m^2).primeFactors := by rwa [Nat.primeFactors_pow m (by decide : 2≠0)]
  have hrm : r ∈ (m^2).primeFactors := by rwa [Nat.primeFactors_pow m (by decide : 2≠0)]
  have hd : f p*f r ∣ q^a*i := by
    rw [← hl,(isMultiplicative_sigma (k:=1)).multiplicative_factorization _ (pow_ne_zero _ hm.ne')]
    exact two_sources_mul_dvd_prod hpm hrm hne f
  have hg : (f p).gcd i*(f r).gcd i ∣ q^a*i :=
    (Nat.mul_dvd_mul (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)).trans hd
  have hc (u : ℕ) : q.Coprime ((f u).gcd i) := hq.of_dvd_right (Nat.gcd_dvd_right _ _)
  simpa [f,Nat.factorization_pow] using (((hc p).mul_right (hc r)).pow_left a).symm.dvd_of_dvd_mul_left hg

/-- Candidate pairs encode the part spent from the index and the remaining
Euler-prime power. Small residuals admit a complete prime support test. -/
@[expose] def sourceOptions (i p H M : ℕ) : Finset (ℕ × ℕ) :=
  ((fullLengths i p H).image fun d =>
    let b := repunit p d
    (b.gcd i,residual b i)).filter fun z =>
      z.2.Coprime i ∧ z.2%M=1 ∧ (z.2 ≤ 100000 → z.2.primeFactors.card ≤ 1) ∧
      ∀ u : Fin 14, (u:ℕ).Prime → (u:ℕ) ∣ z.2 → (u:ℕ)%M=1

/-- The actual source realizes one option, and its residual is a power of
the Euler prime. -/
theorem actual_source_option {q a m i p H M : ℕ} (hq : q.Prime) (ha : Odd a) (hm : 0<m)
    (hio : Odd i) (hqi : q.Coprime i) (hM : 1<M) (hqM : q%M=1)
    (hp : p.Prime) (hpo : Odd p) (hpm : p ∣ m) (hH : (a+1).divisors.card/2 ≤ H)
    (hl : sigma 1 (m^2)=q^a*i) (hr : sigma 1 (q^a)*i=2*m^2) :
    ∃ j : ℕ, ((sigma 1 (p^(2*m.factorization p))).gcd i,q^j) ∈ sourceOptions i p H M := by
  let e := 2*m.factorization p
  have hem := (hp.dvd_iff_one_le_factorization hm.ne').mp hpm
  have hd := cofactor_component_sum_dvd_index_product hm hp (e:=e) rfl (by dsimp [e]; omega) hl
  obtain ⟨j,hj⟩ := residual_eq_prime_pow hq hio.pos hd
  refine ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨e+1,
    actual_length_mem hq ha hm hio hp hpo hpm hH hl hr,by simp only [repunit_eq_sigma hp,hj]; rfl⟩,
    hqi.pow_left _,?_,?_,?_⟩⟩
  · have hcon : q ≡ 1 [MOD M] := by simpa [Nat.ModEq,Nat.mod_eq_of_lt hM] using hqM
    simpa [Nat.ModEq,Nat.mod_eq_of_lt hM] using hcon.pow j
  · intro _
    by_cases hz : j=0
    · simp [hz]
    · simp [Nat.primeFactors_pow q hz,hq.primeFactors]
  · intro z hz hdq
    exact ((Nat.prime_dvd_prime_iff_eq hz hq).mp (hz.dvd_of_dvd_pow hdq)) ▸ hqM

/-- Both residuals must be powers of a common prime and distinct sources
must be able to spend their two gcds simultaneously. -/
@[expose] def BudgetCompatible (i p r H M : ℕ) : Prop :=
  ∃ x ∈ sourceOptions i p H M, ∃ y ∈ sourceOptions i r H M,
    (p=r ∨ x.1*y.1 ∣ i) ∧ (x.2=1 ∨ y.2=1 ∨ x.2.gcd y.2 ≠ 1)

instance (i p r H M : ℕ) : Decidable (BudgetCompatible i p r H M) :=
  inferInstanceAs (Decidable (∃ x ∈ sourceOptions i p H M, ∃ y ∈ sourceOptions i r H M,
    (p=r ∨ x.1*y.1 ∣ i) ∧ (x.2=1 ∨ y.2=1 ∨ x.2.gcd y.2 ≠ 1)))

/-- The necessary two-source test applies to any two actual cofactor
bases, including small bases forced into the cofactor by a support bound. -/
theorem budget_compatible_of_euler_index {q a m i p r H M : ℕ} (hq : q.Prime) (ha : Odd a)
    (hm : 0<m) (hmo : Odd m) (hio : Odd i) (hqi : q.Coprime i) (hM : 1<M) (hqM : q%M=1)
    (hp : p ∈ m.primeFactors) (hrp : r ∈ m.primeFactors) (hH : (a+1).divisors.card/2 ≤ H)
    (hl : sigma 1 (m^2)=q^a*i) (hr : sigma 1 (q^a)*i=2*m^2) : BudgetCompatible i p r H M := by
  have one (u : ℕ) (hu : u ∈ m.primeFactors) := actual_source_option hq ha hm hio hqi hM hqM
    (Nat.prime_of_mem_primeFactors hu) (hmo.of_dvd_nat (Nat.dvd_of_mem_primeFactors hu))
    (Nat.dvd_of_mem_primeFactors hu) hH hl hr
  obtain ⟨j,hj⟩ := one p hp
  obtain ⟨k,hk⟩ := one r hrp
  refine ⟨_,hj,_,hk,?_,?_⟩
  · exact or_iff_not_imp_left.mpr (fun hn => spent_mul_dvd_index hqi hm hp hrp hn hl)
  · by_cases hz : j=0
    · exact .inl (by simp [hz])
    by_cases hz' : k=0
    · exact .inr (.inl (by simp [hz']))
    exact .inr (.inr (fun h => hq.not_dvd_one (h ▸ Nat.dvd_gcd (dvd_pow_self q hz) (dvd_pow_self q hz'))))

end OddPerfect.IndexSieve
