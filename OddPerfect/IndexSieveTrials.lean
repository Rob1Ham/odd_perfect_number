module

public import OddPerfect.IndexSieveReturns
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect.IndexSieve

open ArithmeticFunction Finset

/-- Congruence and small factor checks on a residual, allowing exponent zero. -/
@[expose] def ResidueFits (i M x : ℕ) : Prop :=
  x.Coprime i ∧ x%M=1 ∧ (x≤100000 → x.primeFactors.card≤1) ∧
    ∀ u : Fin 14, (u:ℕ).Prime → (u:ℕ) ∣ x → (u:ℕ)%M=1

instance (i M x : ℕ) : Decidable (ResidueFits i M x) :=
  inferInstanceAs (Decidable (x.Coprime i ∧ x%M=1 ∧ (x≤100000 → x.primeFactors.card≤1) ∧
    ∀ u : Fin 14, (u:ℕ).Prime → (u:ℕ) ∣ x → (u:ℕ)%M=1))

private theorem fits_pow {q i M : ℕ} (hq : q.Prime) (hqi : q.Coprime i)
    (hM : 1<M) (hqM : q%M=1) (t : ℕ) : ResidueFits i M (q^t) := by
  refine ⟨hqi.pow_left _,?_,?_,?_⟩
  · have hcon : q ≡ 1 [MOD M] := by simpa [Nat.ModEq,Nat.mod_eq_of_lt hM] using hqM
    simpa [Nat.ModEq,Nat.mod_eq_of_lt hM] using hcon.pow t
  · intro _
    by_cases hz : t=0
    · simp [hz]
    · simp [Nat.primeFactors_pow q hz,hq.primeFactors]
  · intro z hz hd
    exact ((Nat.prime_dvd_prime_iff_eq hz hq).mp (hz.dvd_of_dvd_pow hd)) ▸ hqM

/-- The test for a specified pair of exact lengths, using a bank of possible
Euler-prime witnesses and the successor and predecessor restrictions. -/
@[expose] def TrialPair (i p r d e H M : ℕ) (trials : List ℕ) : Prop :=
  let u := repunit p d
  let v := repunit r e
  let x := residual u i
  let y := residual v i
  ResidueFits i M x ∧ ResidueFits i M y ∧
    (p=r ∨ u.gcd i * v.gcd i ∣ i) ∧ (x=1 ∨ y=1 ∨ x.gcd y ≠ 1) ∧
    ∀ c ∈ trials, (c ∣ x ∨ c ∣ y) → c%M=1 ∧ acceptsEuler i p d c H ∧ acceptsEuler i r e c H

instance (i p r d e H M : ℕ) (trials : List ℕ) : Decidable (TrialPair i p r d e H M trials) :=
  inferInstanceAs (Decidable (let u := repunit p d; let v := repunit r e
    let x := residual u i; let y := residual v i
    ResidueFits i M x ∧ ResidueFits i M y ∧ (p=r ∨ u.gcd i * v.gcd i ∣ i) ∧
      (x=1 ∨ y=1 ∨ x.gcd y ≠ 1) ∧
      ∀ c ∈ trials, (c ∣ x ∨ c ∣ y) → c%M=1 ∧ acceptsEuler i p d c H ∧ acceptsEuler i r e c H))

@[expose] def TrialCompatible (i p r H M : ℕ) (trials : List ℕ) : Prop :=
  ∃ d ∈ fullLengths i p H, ∃ e ∈ fullLengths i r H, TrialPair i p r d e H M trials

instance (i p r H M : ℕ) (trials : List ℕ) : Decidable (TrialCompatible i p r H M trials) :=
  inferInstanceAs (Decidable (∃ d ∈ fullLengths i p H, ∃ e ∈ fullLengths i r H, TrialPair i p r d e H M trials))

theorem trial_compatible_of_euler_index {q a m i p r H M : ℕ} (hq : q.Prime) (ha : Odd a)
    (hm : 0<m) (hmo : Odd m) (hio : Odd i) (hqi : q.Coprime i) (hM : 1<M) (hqM : q%M=1)
    (hp : p ∈ m.primeFactors) (hrp : r ∈ m.primeFactors) (hH : (a+1).divisors.card/2 ≤ H)
    (hl : sigma 1 (m^2)=q^a*i) (hr : sigma 1 (q^a)*i=2*m^2)
    (trials : List ℕ) (hcert : ∀ c ∈ trials, c.Prime) : TrialCompatible i p r H M trials := by
  let D u := 2*m.factorization u+1
  let U u := repunit u (D u)
  have one (u : ℕ) (hu : u ∈ m.primeFactors) : D u ∈ fullLengths i u H ∧
      (∃ t : ℕ, residual (U u) i=q^t) ∧ acceptsEuler i u (D u) q H := by
    have hup := Nat.prime_of_mem_primeFactors hu
    have hum := Nat.dvd_of_mem_primeFactors hu
    have huo := hmo.of_dvd_nat hum
    have he := (hup.dvd_iff_one_le_factorization hm.ne').mp hum
    refine ⟨actual_length_mem hq ha hm hio hup huo hum hH hl hr,?_,
      actual_component_accepts_euler hq ha hup huo hm hio.pos hum hH hl hr⟩
    apply residual_eq_prime_pow hq hio.pos
    rw [show U u=sigma 1 (u^(2*m.factorization u)) from repunit_eq_sigma hup]
    exact cofactor_component_sum_dvd_index_product hm hup rfl (by omega) hl
  obtain ⟨hpL,⟨j,hj⟩,hpq⟩ := one p hp
  obtain ⟨hrL,⟨k,hk⟩,hrq⟩ := one r hrp
  refine ⟨_,hpL,_,hrL,?_⟩
  change ResidueFits i M (residual (U p) i) ∧ ResidueFits i M (residual (U r) i) ∧
    (p=r ∨ (U p).gcd i*(U r).gcd i ∣ i) ∧
    (residual (U p) i=1 ∨ residual (U r) i=1 ∨ (residual (U p) i).gcd (residual (U r) i)≠1) ∧ _
  rw [hj,hk]
  refine ⟨fits_pow hq hqi hM hqM _,fits_pow hq hqi hM hqM _,?_,?_,?_⟩
  · apply or_iff_not_imp_left.mpr
    intro hne
    simpa [U,D,repunit_eq_sigma (Nat.prime_of_mem_primeFactors hp),repunit_eq_sigma (Nat.prime_of_mem_primeFactors hrp)]
      using spent_mul_dvd_index hqi hm hp hrp hne hl
  · by_cases h0 : j=0
    · exact .inl (by simp [h0])
    by_cases h0' : k=0
    · exact .inr (.inl (by simp [h0']))
    exact .inr (.inr (fun h => hq.not_dvd_one (h ▸ Nat.dvd_gcd (dvd_pow_self q h0) (dvd_pow_self q h0'))))
  · intro c hc hd
    have hcp := hcert c hc
    have heq : c=q := by
      rcases hd with h|h
      · exact (Nat.prime_dvd_prime_iff_eq hcp hq).mp (hcp.dvd_of_dvd_pow h)
      · exact (Nat.prime_dvd_prime_iff_eq hcp hq).mp (hcp.dvd_of_dvd_pow h)
    subst c
    exact ⟨hqM,hpq,hrq⟩

end OddPerfect.IndexSieve
