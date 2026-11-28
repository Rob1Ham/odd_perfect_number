import OddPerfect.SixthPowerFreePrimeCompositeSplit
import OddPerfect.OddValuationCycleObstruction
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Positivity

/-! Standalone companion to the November 27 assessment. Run from the project root with
`lake env lean research/QuarticChainCheck.lean`. -/
namespace OddPerfect.QuarticChainCheck

open ArithmeticFunction

private def firstFactor (w : ℕ) := w ^ 2 - w + 1
private def secondFactor (w : ℕ) :=
  w ^ 6 + 3 * w ^ 5 + 5 * w ^ 4 + 6 * w ^ 3 + 7 * w ^ 2 + 6 * w + 3
private def quartic (w : ℕ) := w ^ 4 + w ^ 3 + w ^ 2 + w + 1

private theorem factor_product (w : ℕ) :
    quartic w ^ 2 + quartic w + 1 = firstFactor w * secondFactor w :=
  phi3_comp_phi5_factorization w

private theorem factors_coprime {w : ℕ}
    (h31 : ¬ 31 ∣ firstFactor w * secondFactor w) :
    (firstFactor w).Coprime (secondFactor w) := by
  let Q := w ^ 4 + 4 * w ^ 3 + 8 * w ^ 2 + 10 * w + 9
  have hBezout : (25 + Q * (5 * w + 1)) * firstFactor w =
      (5 * w + 1) * secondFactor w + 31 := by
    dsimp [Q, firstFactor, secondFactor]
    zify [Nat.le_self_pow (by decide : 2 ≠ 0) w]
    ring
  apply Nat.coprime_of_dvd
  intro p hp hA hB
  have hD := hA.mul_left (25 + Q * (5 * w + 1))
  rw [hBezout] at hD
  have hp31 : p ∣ 31 := (Nat.dvd_add_right (hB.mul_left (5 * w + 1))).mp hD
  have heq := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 31)).mp hp31
  exact h31 (heq ▸ hA.trans (dvd_mul_right _ _))

private theorem first_nonsquare {w : ℕ} (hw : 19 ≤ w) : ¬ IsSquare (firstFactor w) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = 19 + k := Nat.exists_eq_add_of_le hw
  have hA : firstFactor (19 + k) = k ^ 2 + 37 * k + 343 := by
    unfold firstFactor
    rw [show (19 + k) ^ 2 = (19 + k) + (k ^ 2 + 37 * k + 342) by ring]
    omega
  rw [hA]
  rintro ⟨y, hy⟩
  exact Nat.not_exists_sq' (m := 18 + k) (n := k ^ 2 + 37 * k + 343) (by nlinarith) (by nlinarith)
    ⟨y, by simpa [pow_two] using hy.symm⟩

private theorem second_nonsquare {w : ℕ} (hw : 19 ≤ w) : ¬ IsSquare (secondFactor w) := by
  let P := 16 * w ^ 3 + 24 * w ^ 2 + 22 * w + 15
  have hlo : P ^ 2 < 256 * secondFactor w := by
    dsimp [P, secondFactor]
    ring_nf
    omega
  have hhi : 256 * secondFactor w < (P + 1) ^ 2 := by
    obtain ⟨k, hk⟩ : ∃ k, w = 19 + k := Nat.exists_eq_add_of_le hw
    dsimp [P, secondFactor]
    rw [hk]
    ring_nf
    omega
  rintro ⟨y, hy⟩
  exact Nat.not_exists_sq' hlo hhi ⟨16 * y, by rw [hy]; ring⟩

private theorem odd_factor_of_nonsquare {a : ℕ} (ha : ¬ IsSquare a) :
    ∃ p, p.Prime ∧ Odd (a.factorization p) := by
  by_contra! h
  exact ha (Nat.isSquare_iff_even_factorization.mpr h)

/-- A prime-valued quartic followed by a quadratic divisor sum uses two distinct
odd-valuation targets as soon as 31 is excluded. The arithmetic also holds without
primality of either base. -/
theorem two_odd_valuations {w s : ℕ} (hw : 19 ≤ w)
    (hs : s = w ^ 4 + w ^ 3 + w ^ 2 + w + 1) (h31 : ¬ 31 ∣ s ^ 2 + s + 1) :
    ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p ≠ r ∧
      Odd ((s ^ 2 + s + 1).factorization p) ∧ Odd ((s ^ 2 + s + 1).factorization r) := by
  have hprod : s ^ 2 + s + 1 = firstFactor w * secondFactor w := hs ▸ factor_product w
  rw [hprod] at h31 ⊢
  have hcop := factors_coprime h31
  obtain ⟨p, hp, hpA⟩ := odd_factor_of_nonsquare (first_nonsquare hw)
  obtain ⟨r, hr, hrB⟩ := odd_factor_of_nonsquare (second_nonsquare hw)
  have hpd := Nat.dvd_of_mem_primeFactors (p := p) (n := firstFactor w)
    (Finsupp.mem_support_iff.mpr hpA.pos.ne')
  have hrd := Nat.dvd_of_mem_primeFactors (p := r) (n := secondFactor w)
    (Finsupp.mem_support_iff.mpr hrB.pos.ne')
  have hpB : ¬ p ∣ secondFactor w := fun hd =>
    hp.not_dvd_one (hcop ▸ Nat.dvd_gcd hpd hd)
  have hrA : ¬ r ∣ firstFactor w := fun hd =>
    hr.not_dvd_one (hcop ▸ Nat.dvd_gcd hd hrd)
  have hA0 : firstFactor w ≠ 0 := by unfold firstFactor; omega
  have hB0 : secondFactor w ≠ 0 := by unfold secondFactor; positivity
  simp only [Nat.factorization_mul hA0 hB0, Finsupp.add_apply]
  exact ⟨p, r, hp, hr, fun e => hpB (e ▸ hrd),
    by simpa [Nat.factorization_eq_zero_of_not_dvd hpB] using hpA,
    by simpa [Nat.factorization_eq_zero_of_not_dvd hrA] using hrB⟩

/-- In a sixth-power-free candidate, a prime-valued quartic sum which is an exact
square component has two different outgoing odd-valuation edges. -/
theorem two_edges_in_candidate {N w s : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hw : w ∈ N.primeFactors) (hs : s ∈ N.primeFactors) (he : N.factorization s = 2)
    (hchain : s = w ^ 4 + w ^ 3 + w ^ 2 + w + 1) :
    ∃ p r : ℕ, p ≠ r ∧ oddSigmaEdge N s p ∧ oddSigmaEdge N s r := by
  have hws := sixth_power_free_min_prime_ge_53 ho hN hfree hw
  have hsPrime := Nat.prime_of_mem_primeFactors hs
  have hsOdd := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hs)
  have hpoly : sigma 1 (s ^ 2) = s ^ 2 + s + 1 := by
    rw [sigma_one_apply_prime_pow hsPrime]
    simp [Finset.sum_range_succ]
    ring
  obtain ⟨b, hNb, hcop⟩ := exists_coprime_cofactor_of_exact_prime_pow hsPrime
    (he ▸ Nat.ordProj_dvd N s)
    ((hsPrime.pow_dvd_iff_le_factorization hN.2.ne').not.mpr (by omega : ¬ 2 + 1 ≤ N.factorization s))
  have hdiv : s ^ 2 + s + 1 ∣ N := by
    apply odd_dvd_perfect_of_dvd_sum_divisors hN hNb hcop ((hsOdd.pow.add_odd hsOdd).add_one)
    rw [← sigma_one_apply, hpoly]
  have h31 : ¬ 31 ∣ s ^ 2 + s + 1 := by
    intro hd
    have hx : 31 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, hd.trans hdiv, hN.2.ne'⟩
    have := sixth_power_free_min_prime_ge_53 ho hN hfree hx
    omega
  obtain ⟨p, r, hp, hr, hpr, hvp, hvr⟩ := two_odd_valuations (by omega : 19 ≤ w) hchain h31
  have edge (v : ℕ) (hv : Odd ((s ^ 2 + s + 1).factorization v)) : oddSigmaEdge N s v := by
    have hmem : v ∈ (s ^ 2 + s + 1).primeFactors := Finsupp.mem_support_iff.mpr hv.pos.ne'
    exact ⟨hs, Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hmem,
      (Nat.dvd_of_mem_primeFactors hmem).trans hdiv, hN.2.ne'⟩, by simpa [he, hpoly] using hv⟩
  exact ⟨p, r, hpr, edge p hvp, edge r hvr⟩

#print axioms two_odd_valuations
#print axioms two_edges_in_candidate
end OddPerfect.QuarticChainCheck
