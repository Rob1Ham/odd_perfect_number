module

public import OddPerfect.DeficientFourClassification
import Mathlib.Tactic.Ring

/-! Structural reductions for cube-free Descartes factorizations. -/

public section

namespace DescartesSubmission
open ArithmeticFunction OddPerfect

private theorem tothPair_of_spoof {m w : ℕ} (h : SingleCompositeSpoof m w) :
    TothPair m w :=
  ⟨h.odd_left, h.odd_right.pos, h.balance⟩

/-- In a cube-free nonclassical example on fewer than seven primes, the composite
factor is a prime square, and every ordinary component has exponent two. -/
theorem support_shape {m w : ℕ} (h : SingleCompositeSpoof m w)
    (hcf : ∀ p : ℕ, p.Prime → ¬ p^3 ∣ m*w) (hc : (m*w).primeFactors.card < 7)
    (hne : m*w ≠ 198585576189) :
    ∃ r, r.Prime ∧ w = r^2 ∧ ∀ p ∈ m.primeFactors, m.factorization p = 2 := by
  have hm := h.odd_left.pos.ne'
  have hw := h.odd_right.pos.ne'
  have hpair := tothPair_of_spoof h
  have hlarge : 5 ≤ m.primeFactors.card := by
    by_contra! hsmall
    obtain ⟨hm', hw'⟩ := (toth_odd_pair_four_iff (by omega) h.odd_right h.one_lt).mp hpair
    exact hne (by rw [hm', hw'])
  rw [h.coprime.primeFactors_mul, Finset.card_union_of_disjoint h.coprime.disjoint_primeFactors] at hc
  have hpos := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr h.one_lt)
  obtain ⟨r, hs⟩ := Finset.card_eq_one.mp (show w.primeFactors.card = 1 by omega)
  have hrmem : r ∈ w.primeFactors := by simp [hs]
  have hr := Nat.prime_of_mem_primeFactors hrmem
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (p := r) hw
    (fun {q} hq hqw => by
      have hmem := Nat.mem_primeFactors.mpr ⟨hq, hqw, hw⟩
      simpa [hs] using hmem)
  have hk : w.primeFactorsList.length = 2 := by
    have hlt : w.primeFactorsList.length < 3 := by
      by_contra! hge
      apply hcf r hr
      apply dvd_mul_of_dvd_right _ m
      calc r^3 ∣ r^w.primeFactorsList.length := pow_dvd_pow _ hge
           _ = w := hpow.symm
    have hzero : w.primeFactorsList.length ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hpow
      have := h.one_lt
      omega
    have hone : w.primeFactorsList.length ≠ 1 := by
      intro h1
      rw [h1, pow_one] at hpow
      exact h.not_prime (hpow ▸ hr)
    omega
  refine ⟨r, hr, hk ▸ hpow, ?_⟩
  intro p hp
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hp0 := hpr.factorization_pos_of_dvd hm (Nat.dvd_of_mem_primeFactors hp)
  have heven := Nat.isSquare_iff_even_factorization.mp (toth_odd_cofactor_square hpair h.odd_right).1 p hpr
  have hlt : m.factorization p < 3 := by
    by_contra! hge
    exact hcf p hpr (dvd_mul_of_dvd_left ((hpr.pow_dvd_iff_le_factorization hm).2 hge) w)
  obtain ⟨k, hk'⟩ := heven
  omega

private theorem odd_prime_mem_of_dvd_balance {m w q : ℕ}
    (h : SingleCompositeSpoof m w) (hq : q.Prime) (hodd : q ≠ 2)
    (hd : q ∣ 2*(m*w)) : q ∈ (m*w).primeFactors := by
  have hn2 : ¬ q ∣ 2 := by
    intro hq2
    rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hq2 with h1 | h2
    · exact hq.ne_one h1
    · exact hodd h2
  exact Nat.mem_primeFactors.mpr ⟨hq, (hq.dvd_mul.mp hd).resolve_left hn2,
    Nat.mul_ne_zero h.odd_left.pos.ne' h.odd_right.pos.ne'⟩

/-- An ordinary prime square contributes every odd prime divisor of its
geometric sum back to the support of the whole number. -/
theorem ordinary_edge {m w r : ℕ} (h : SingleCompositeSpoof m w) (hw : w = r^2)
    (hr : r.Prime) (he : ∀ p ∈ m.primeFactors, m.factorization p = 2)
    {p q : ℕ} (hp : p ∈ (m*w).primeFactors) (hpne : p ≠ r)
    (hq : q.Prime) (hodd : q ≠ 2) (hd : q ∣ p^2+p+1) :
    q ∈ (m*w).primeFactors := by
  have hunion := h.coprime.primeFactors_mul
  have hp' : p ∈ m.primeFactors := by
    rw [hunion, Finset.mem_union] at hp
    rcases hp with hpm | hpw
    · exact hpm
    · rw [hw, Nat.primeFactors_prime_pow (by decide) hr] at hpw
      exact (hpne (Finset.mem_singleton.mp hpw)).elim
  have hpr := Nat.prime_of_mem_primeFactors hp'
  have hblock : sigma 1 (p ^ m.factorization p) ∣ sigma 1 m := by
    rw [(isMultiplicative_sigma (k := 1)).multiplicative_factorization _ h.odd_left.pos.ne']
    exact Finset.dvd_prod_of_mem _ hp'
  rw [he p hp', sigma_one_apply_prime_pow hpr] at hblock
  have hval : (∑ i ∈ Finset.range (2+1), p^i) = p^2+p+1 := by
    simp [Finset.sum_range_succ]
    ring
  rw [hval] at hblock
  apply odd_prime_mem_of_dvd_balance h hq hodd
  rw [← h.balance]
  exact dvd_mul_of_dvd_left (hd.trans hblock) _

/-- The composite factor contributes its own endpoint sum. -/
theorem exceptional_edge {m w r : ℕ} (h : SingleCompositeSpoof m w) (hw : w = r^2)
    {q : ℕ} (hq : q.Prime) (hodd : q ≠ 2) (hd : q ∣ (r^2+1)/2) :
    q ∈ (m*w).primeFactors := by
  have hwo := Nat.odd_iff.mp h.odd_right
  have htwo : 2 ∣ w+1 := by omega
  have hsum : q ∣ w+1 := by
    rw [← hw] at hd
    have heq := Nat.mul_div_cancel' htwo
    exact heq ▸ dvd_mul_of_dvd_right hd 2
  apply odd_prime_mem_of_dvd_balance h hq hodd
  rw [← h.balance]
  exact dvd_mul_of_dvd_right hsum _

end DescartesSubmission
