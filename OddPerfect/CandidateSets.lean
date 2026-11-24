module

public import OddPerfect.Abundance
public import OddPerfect.Euler
public import OddPerfect.Touchard
public import OddPerfect.Steuerwald
public import OddPerfect.Spoof

public section

namespace OddPerfect

/-- The set whose nonemptiness is the odd perfect number question. -/
@[expose] def oddPerfectNumbers : Set ℕ := {n | Odd n ∧ n.Perfect}

/-- Three necessary tests, retaining the actual primality and coprimality
conditions in Euler's form. -/
def classicalCandidates : Set ℕ :=
  {n | Odd n ∧ (∃ q a m : ℕ, q.Prime ∧ q % 4 = 1 ∧ a % 4 = 1 ∧
    ¬ q ∣ m ∧ n = q ^ a * m ^ 2) ∧ (n % 12 = 1 ∨ n % 36 = 9) ∧ ¬ 105 ∣ n}

/-- Retain a candidate only if some genuine prime fourth power divides it. -/
def fourthPowerCandidates : Set ℕ :=
  {n ∈ classicalCandidates | ∃ q : ℕ, q.Prime ∧ q ^ 4 ∣ n}

theorem oddPerfectNumbers_subset_fourthPowerCandidates : oddPerfectNumbers ⊆ fourthPowerCandidates := by
  intro n hn
  obtain ⟨ho, hp⟩ := hn
  obtain ⟨_, _, _, _, q, hq, _, _, he⟩ := steuerwald ho hp
  have hqp := Nat.prime_of_mem_primeFactors hq
  exact ⟨⟨ho, euler_form ho hp, touchard_congruence ho hp, not_dvd_105_of_odd_perfect hp ho⟩,
    q, hqp, (hqp.pow_dvd_iff_le_factorization hp.2.ne').2 he⟩

/-- The historical spoof passes the three tests with Euler prime 61, even
when the tests use its genuine prime factorization. -/
theorem descartes_mem_classicalCandidates : 198585576189 ∈ classicalCandidates :=
  ⟨by decide, ⟨61, 1, 57057, by decide, rfl, rfl, by decide, rfl⟩, Or.inr rfl, by decide⟩

theorem descartes_not_mem_fourthPowerCandidates : 198585576189 ∉ fourthPowerCandidates := by
  rintro ⟨_, q, hq, hd⟩
  have hdiv := (dvd_pow_self q (by decide : 4 ≠ 0)).trans hd
  change q ∣ (3 * 7 * 11 * 13 * 19) ^ 2 * 61 at hdiv
  have hcases : q = 3 ∨ q = 7 ∨ q = 11 ∨ q = 13 ∨ q = 19 ∨ q = 61 := by
    rcases hq.dvd_mul.mp hdiv with h | h
    · have h' := hq.dvd_of_dvd_pow h
      simp only [hq.dvd_mul, Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 3),
        Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 7),
        Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 11),
        Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 13),
        Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 19)] at h'
      tauto
    · have := (Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 61)).mp h
      tauto
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at hd

/-- The fourth-power test strictly shrinks the classical search set. -/
theorem fourthPowerCandidates_ssubset : fourthPowerCandidates ⊂ classicalCandidates := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨fun n hn => hn.1, ?_⟩
  intro heq
  exact descartes_not_mem_fourthPowerCandidates (heq ▸ descartes_mem_classicalCandidates)

end OddPerfect
