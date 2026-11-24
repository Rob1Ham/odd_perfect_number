module

public import OddPerfect.FewPrimes
public import OddPerfect.SpoofBoxState
import Mathlib.Data.Finset.Sort

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- The true prime-power slots, sorted by strictly increasing base. Their
length counts distinct prime divisors, regardless of the exponents. -/
noncomputable def primeSlots (N : ℕ) {k : ℕ} (hk : N.primeFactors.card=k) (i : Fin k) : ℕ × ℕ :=
  let p := N.primeFactors.orderEmbOfFin hk i
  (p,N.factorization p)

/-- Information available to a sieve specialized to genuine prime-power
factorizations. These conditions are verified simultaneously on the true tuple. -/
structure GenuineSlots {k : ℕ} (x : Fin k → ℕ × ℕ) : Prop where
  prime : ∀ i, (x i).1.Prime
  strict : StrictMono (fun i => (x i).1)
  large : ∃ i, 257 < (x i).1
  three : k < 8 → ∃ i, (x i).1=3
  no105 : ¬ ((∃ i, (x i).1=3) ∧ (∃ i, (x i).1=5) ∧ (∃ i, (x i).1=7))

theorem primeSlots_of_odd_perfect {N k : ℕ} (ho : Odd N) (hN : N.Perfect) (hk : N.primeFactors.card=k) :
    let x := primeSlots N hk
    GenuineSlots x ∧ (∀ i, 1 < (x i).1 ∧ Odd (x i).1 ∧ 0 < (x i).2) ∧
    (∏ i, (x i).1^(x i).2) = N ∧
    formalSigma univ (fun i => (x i).1) (fun i => (x i).2) = 2*∏ i, (x i).1^(x i).2 := by
  let P := N.primeFactors.orderEmbOfFin hk
  let x := primeSlots N hk
  have hmem (i : Fin k) : P i ∈ N.primeFactors := N.primeFactors.orderEmbOfFin_mem hk _
  have hp (i : Fin k) := Nat.prime_of_mem_primeFactors (hmem i)
  have embprod (f : ℕ → ℕ) : (∏ i : Fin k, f (P i)) = ∏ p ∈ N.primeFactors, f p := by
    rw [← N.primeFactors.map_orderEmbOfFin_univ hk, prod_map]
    rfl
  have hNprod : (∏ i, (P i)^N.factorization (P i)) = N :=
    (embprod (fun p => p^N.factorization p)).trans (Nat.prod_primeFactors_pow_factorization ho.pos.ne').symm
  have hsurj (p : ℕ) (hp : p ∈ N.primeFactors) : ∃ i, P i=p :=
    by
      change p ∈ Set.range (N.primeFactors.orderEmbOfFin hk)
      rwa [N.primeFactors.range_orderEmbOfFin hk]
  refine ⟨⟨hp,P.strictMono,?_,?_,?_⟩,?_,hNprod,?_⟩
  · obtain ⟨r,hr,hgt⟩ := SupportSieve.exists_prime_gt_257 hN ho
    obtain ⟨i,hi⟩ := hsurj r hr
    exact ⟨i,show 257 < P i by omega⟩
  · intro h
    have h3 : 3 ∣ N := by
      by_contra hh
      have := eight_le_distinct_prime_factor_count_of_three_free ho hN hh
      omega
    exact hsurj 3 (Nat.mem_primeFactors.mpr ⟨by decide,h3,ho.pos.ne'⟩)
  · rintro ⟨⟨i,hi⟩,⟨j,hj⟩,⟨l,hl⟩⟩
    change P i=3 at hi
    change P j=5 at hj
    change P l=7 at hl
    apply not_dvd_105_of_odd_perfect hN ho
    have h3 := Nat.dvd_of_mem_primeFactors (hmem i)
    have h5 := Nat.dvd_of_mem_primeFactors (hmem j)
    have h7 := Nat.dvd_of_mem_primeFactors (hmem l)
    rw [hi] at h3
    rw [hj] at h5
    rw [hl] at h7
    exact (show Nat.Coprime 15 7 by decide).mul_dvd_of_dvd_of_dvd
      ((show Nat.Coprime 3 5 by decide).mul_dvd_of_dvd_of_dvd h3 h5) h7
  · intro i
    have hd := Nat.dvd_of_mem_primeFactors (hmem i)
    exact ⟨(hp i).one_lt,ho.of_dvd_nat hd,(hp i).factorization_pos_of_dvd ho.pos.ne' hd⟩
  · unfold formalSigma
    change (∏ i, ∑ j ∈ range (N.factorization (P i)+1), P i ^ j) = 2*∏ i, P i^N.factorization (P i)
    rw [embprod (fun p => ∑ j ∈ range (N.factorization p+1), p^j),hNprod,
      ← (Nat.perfect_iff_sum_divisors_eq_two_mul ho.pos).mp hN, ← sigma_one_apply,
      isMultiplicative_sigma.multiplicative_factorization _ ho.pos.ne']
    exact prod_congr rfl (fun p hp => (sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)).symm)

/-- An odd prime factor of any slot sum must occur as a base somewhere
in a formally balanced prime tuple. A composite-base spoof can evade this step. -/
theorem prime_slot_forcing {k r : ℕ} {x : Fin k → ℕ × ℕ} (hr : r.Prime) (ho : Odd r)
    (hp : ∀ i, (x i).1.Prime) (i : Fin k)
    (hs : r ∣ ∑ j ∈ range ((x i).2+1), (x i).1^j)
    (hb : formalSigma univ (fun i => (x i).1) (fun i => (x i).2) = 2*∏ i, (x i).1^(x i).2) :
    ∃ j, (x j).1 = r := by
  have hd : r ∣ formalSigma univ (fun i => (x i).1) (fun i => (x i).2) :=
    hs.trans (dvd_prod_of_mem _ (mem_univ i))
  rw [hb] at hd
  obtain ⟨j,_,hj⟩ := (hr.prime.dvd_finsetProd_iff _).mp (ho.coprime_two_right.dvd_of_dvd_mul_left hd)
  exact ⟨j,((Nat.prime_dvd_prime_iff_eq hr (hp j)).mp (hr.dvd_of_dvd_pow hj)).symm⟩

end OddPerfect
