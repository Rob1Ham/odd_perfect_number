module

public import OddPerfect.Euler
public import OddPerfect.Valuations
import Mathlib.Tactic.NormNum.Prime

/-! The additional exact-fourth-power branch on p. 72 of Steuerwald (1937). -/

public section

namespace OddPerfect

open ArithmeticFunction

/-- If 3 has exponent four in an odd perfect number, a second prime of even
exponent at least four belongs to this explicit six-element set. -/
theorem steuerwald_four_at_three {N : ℕ} (ho : Odd N) (hN : N.Perfect)
    (h3 : N.factorization 3 = 4) :
    ∃ q ∈ ({7, 11, 19, 31, 127, 5419} : Finset ℕ), q.Prime ∧
      Even (N.factorization q) ∧ 4 ≤ N.factorization q := by
  let candidates : Finset ℕ := {7, 11, 19, 31, 127, 5419}
  change ∃ q ∈ candidates, _
  by_contra h
  obtain ⟨p, _, hp4, _, he⟩ := euler_exponents ho hN
  have primes : ∀ q ∈ candidates, q.Prime ∧ q % 4 = 3 := by
    intro q hq
    simp only [candidates, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have square {q : ℕ} (hq : q ∈ candidates) (hd : q ∣ N) : N.factorization q = 2 := by
    obtain ⟨hprime, hq4⟩ := primes q hq
    have hpar := he q (by omega)
    have hmin := (hprime.dvd_iff_one_le_factorization ho.pos.ne').1 hd
    have hsmall : ¬ 4 ≤ N.factorization q := fun h4 => h ⟨q, hq, hprime, hpar, h4⟩
    obtain ⟨k, hk⟩ := hpar
    omega
  have force {q r e : ℕ} (hq : q.Prime) (hr : r.Prime) (hodd : Odd r)
      (hexp : N.factorization q = e) (hd : r ∣ ∑ i ∈ Finset.range (e + 1), q ^ i) :
      r ∣ N := by
    refine dvd_perfect_of_exact_prime_pow hN hq (k := e) ?_ ?_ hr hodd ?_
    · rw [hq.pow_dvd_iff_le_factorization hN.2.ne', hexp]
    · simp [hq.pow_dvd_iff_le_factorization hN.2.ne', hexp]
    · rwa [Nat.sum_divisors_prime_pow (f := fun x => x) hq]
  have step {q r : ℕ} (hq : q ∈ candidates) (hr : r.Prime) (hodd : Odd r)
      (hqN : q ∣ N) (hd : r ∣ 1 + q + q ^ 2) : r ∣ N :=
    force (primes q hq).1 hr hodd (square hq hqN) (by simpa [Finset.sum_range_succ] using hd)
  have h11 : 11 ∣ N := force (by decide : Nat.Prime 3) (by decide) (by decide) h3 (by decide)
  have h7 : 7 ∣ N := step (q := 11) (by decide) (by decide) (by decide) h11 (by decide)
  have h19 : 19 ∣ N := step (q := 11) (by decide) (by decide) (by decide) h11 (by decide)
  have h127 : 127 ∣ N := step (q := 19) (by decide) (by decide) (by decide) h19 (by decide)
  have h5419 : 5419 ∣ N := step (q := 127) (by decide) (by norm_num) (by decide) h127 (by decide)
  have h31 : 31 ∣ N := step (q := 5419) (by decide) (by decide) (by decide) h5419 (by norm_num)
  let sources : Finset ℕ := {7, 19, 31, 127, 5419}
  have cert : ∀ s ∈ sources, s ∈ candidates ∧ 3 ∣ 1 + s + s ^ 2 := by
    intro s hs
    simp only [sources, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> norm_num [candidates]
  have member : ∀ s ∈ sources, s ∣ N := by
    intro s hs
    simp only [sources, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> assumption
  have bound := card_le_factorization_of_sigma_sources hN (by decide : Odd 3) (by decide)
    sources (fun s hs => Nat.mem_primeFactors.mpr ⟨(primes s (cert s hs).1).1,
      member s hs, ho.pos.ne'⟩) (by
        intro s hs
        obtain ⟨hc, hd⟩ := cert s hs
        rw [square hc (member s hs), sigma_one_apply_prime_pow (primes s hc).1]
        simpa [Finset.sum_range_succ] using hd)
  have card : sources.card = 5 := by decide
  rw [card, h3] at bound
  exact (by decide : ¬ (5 : ℕ) ≤ 4) bound

end OddPerfect
