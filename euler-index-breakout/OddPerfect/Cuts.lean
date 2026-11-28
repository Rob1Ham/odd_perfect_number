module

public import OddPerfect.Forcing
public import Mathlib.Logic.Relation
import Mathlib.Algebra.BigOperators.Associated

public section

namespace OddPerfect

open ArithmeticFunction

/-- A number greater than one has both one and itself among its divisors. -/
theorem self_lt_sigma_of_one_lt {a : ℕ} (ha : 1 < a) : a < sigma 1 a := by
  have h : 1 ≤ ∑ i ∈ a.properDivisors, i :=
    Finset.single_le_sum (f := fun i : ℕ => i) (fun i _ => Nat.zero_le i)
      (Nat.one_mem_properDivisors_iff_one_lt.mpr ha)
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  omega

/-- Across a nontrivial coprime split of a perfect number, the divisor sum
on one side must have a prime in common with the other side. -/
theorem exists_prime_across_coprime_split {N a b : ℕ} (hn : N.Perfect)
    (hprod : N = a * b) (hc : a.Coprime b) (ha : 1 < a) (hb : 1 < b) :
    ∃ r : ℕ, r.Prime ∧ r ∣ sigma 1 a ∧ r ∣ b := by
  apply Nat.Prime.not_coprime_iff_dvd.mp
  intro hcop
  have hfull : sigma 1 a * sigma 1 b = (2 * a) * b := by
    rw [← isMultiplicative_sigma.map_mul_of_coprime hc, ← hprod, sigma_one_apply,
      (Nat.perfect_iff_sum_divisors_eq_two_mul hn.2).mp hn, hprod, Nat.mul_assoc]
  have ha' := self_lt_sigma_of_one_lt ha
  have hb' := self_lt_sigma_of_one_lt hb
  have hl : sigma 1 a < 2 * a := by
    apply (Nat.mul_lt_mul_right (by omega : 0 < b)).mp
    rw [← hfull]
    exact Nat.mul_lt_mul_of_pos_left hb' (by omega)
  have hd : sigma 1 a ∣ (2 * a) * b := hfull ▸ dvd_mul_right _ _
  obtain ⟨k, hk⟩ := hcop.dvd_of_dvd_mul_right hd
  have hk2 : 2 ≤ k := by
    by_contra! h
    obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    · simp at hk
      omega
    · simp at hk
      omega
  have := Nat.mul_le_mul_left (sigma 1 a) hk2
  omega

/-- A directed edge records a prime divisor of the exact component sum.
Both endpoints belong to the true prime support. -/
@[expose] def sigmaEdge (N u v : ℕ) : Prop :=
  u ∈ N.primeFactors ∧ v ∈ N.primeFactors ∧ v ∣ sigma 1 (u ^ N.factorization u)

/-- Every nonempty proper subset of the prime support sends an edge outside
itself. Applying the same theorem to its complement gives the reverse cut. -/
theorem exists_sigmaEdge_leaving {N : ℕ} (hn : N.Perfect) (s : Finset ℕ)
    (hs : s ⊂ N.primeFactors) (hne : s.Nonempty) :
    ∃ u ∈ s, ∃ v ∈ N.primeFactors \ s, sigmaEdge N u v := by
  let t := N.primeFactors \ s
  let f := fun p : ℕ => p ^ N.factorization p
  have hsub := hs.subset
  have ht : t ⊆ N.primeFactors := Finset.sdiff_subset
  have prime {p : ℕ} (hp : p ∈ N.primeFactors) := Nat.prime_of_mem_primeFactors hp
  have hgt (p : ℕ) (hp : p ∈ N.primeFactors) : 1 < f p :=
    one_lt_pow₀ (prime hp).one_lt (Finsupp.mem_support_iff.mp hp)
  have gt (a : Finset ℕ) (ha : a ⊆ N.primeFactors) (hne' : a.Nonempty) : 1 < a.prod f := by
    obtain ⟨p, hp⟩ := hne'
    exact (hgt p (ha hp)).trans_le (Nat.le_of_dvd
      (Finset.prod_pos fun i hi => (hgt i (ha hi)).le) (Finset.dvd_prod_of_mem f hp))
  have hprod : N = s.prod f * t.prod f := by
    rw [mul_comm, Finset.prod_sdiff hsub]
    exact (Nat.prod_factorization_pow_eq_self hn.2.ne').symm
  have hc : (s.prod f).Coprime (t.prod f) := by
    apply Nat.Coprime.prod_left
    intro p hp
    apply Nat.Coprime.prod_right
    intro q hq
    exact ((Nat.coprime_primes (prime (hsub hp)) (prime (ht hq))).mpr
      (fun h => (Finset.mem_sdiff.mp hq).2 (h ▸ hp))).pow _ _
  obtain ⟨r, hr, hrs, hrt⟩ := exists_prime_across_coprime_split hn hprod hc (gt s hsub hne)
    (gt t ht (Finset.sdiff_nonempty.mpr hs.not_superset))
  obtain ⟨q, hq, hrq⟩ := (hr.prime.dvd_finsetProd_iff f).mp hrt
  have hr_eq := (Nat.prime_dvd_prime_iff_eq hr (prime (ht hq))).mp (hr.dvd_of_dvd_pow hrq)
  subst r
  rw [ArithmeticFunction.IsMultiplicative.map_prod f isMultiplicative_sigma s
    (fun i hi j hj hij => ((Nat.coprime_primes (prime (hsub hi)) (prime (hsub hj))).mpr hij).pow _ _)] at hrs
  obtain ⟨u, hu, hdiv⟩ := (hr.prime.dvd_finsetProd_iff _).mp hrs
  exact ⟨u, hu, q, hq, hsub hu, ht hq, hdiv⟩

/-- Every proper nonempty group of components also receives an edge from
its complement. -/
theorem exists_sigmaEdge_entering {N : ℕ} (hn : N.Perfect) (s : Finset ℕ)
    (hs : s ⊂ N.primeFactors) (hne : s.Nonempty) :
    ∃ u ∈ N.primeFactors \ s, ∃ v ∈ s, sigmaEdge N u v := by
  let c := N.primeFactors \ s
  have hc : c ⊂ N.primeFactors := by
    apply (Finset.ssubset_iff_of_subset Finset.sdiff_subset).mpr
    obtain ⟨p, hp⟩ := hne
    exact ⟨p, hs.subset hp, fun h => (Finset.mem_sdiff.mp h).2 hp⟩
  obtain ⟨u, hu, v, hv, h⟩ := exists_sigmaEdge_leaving hn c hc (Finset.sdiff_nonempty.mpr hs.not_superset)
  refine ⟨u, hu, v, ?_, h⟩
  by_contra hvs
  exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hv).1, hvs⟩)

/-- Every two prime components of a perfect number are connected in the
indicated direction by a path of exact divisor-sum forcing steps. -/
theorem sigmaEdge_reachable {N u v : ℕ} (hn : N.Perfect) (hu : u ∈ N.primeFactors)
    (hv : v ∈ N.primeFactors) : Relation.ReflTransGen (sigmaEdge N) u v := by
  classical
  let s := N.primeFactors.filter (Relation.ReflTransGen (sigmaEdge N) u)
  have hu' : u ∈ s := Finset.mem_filter.mpr ⟨hu, .refl⟩
  by_contra h
  have hv' : v ∉ s := fun H => h (Finset.mem_filter.mp H).2
  have hproper : s ⊂ N.primeFactors :=
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, fun eq => hv' (eq ▸ hv)⟩
  obtain ⟨x, hx, y, hy, hedge⟩ := exists_sigmaEdge_leaving hn s hproper ⟨u, hu'⟩
  have hpath := (Finset.mem_filter.mp hx).2
  exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_filter.mpr ⟨hedge.2.1, hpath.tail hedge⟩)

end OddPerfect
