module

public import OddPerfect.OddValuationGraph
public import OddPerfect.OddSourceWeight
public import OddPerfect.WeightedLength
import all OddPerfect.OddValuationGraph

public section
namespace OddPerfect
open Finset ArithmeticFunction

/-- Distinct odd-valuation targets of a fixed source component. -/
@[expose] def oddSigmaTargets (N p : ℕ) : Finset ℕ :=
  N.primeFactors.filter (fun r => Odd ((sigma 1 (p^N.factorization p)).factorization r))

theorem oddSigmaTargets_eq_of_even {N p : ℕ} (hN : N.Perfect) (ho : Odd N) (hp : p∈N.primeFactors)
    (he : Even (N.factorization p)) :
    oddSigmaTargets N p=oddValuationPrimes (sigma 1 (p^N.factorization p)) := by
  have hpo := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
  have hs := sigma_modEq_of_one (Nat.prime_of_mem_primeFactors hp) (show p ≡ 1 [MOD 2] from Nat.odd_iff.mp hpo) (N.factorization p)
  have hodd : Odd (sigma 1 (p^N.factorization p)) := Nat.odd_iff.mpr (by
    change sigma 1 (p^N.factorization p)%2=(N.factorization p+1)%2 at hs
    have := Nat.even_iff.mp he
    omega)
  ext r
  simp only [oddSigmaTargets,mem_filter,mem_oddValuationPrimes]
  constructor
  · exact And.right
  · intro hv
    have hr : r∈(sigma 1 (p^N.factorization p)).primeFactors := Finsupp.mem_support_iff.mpr hv.pos.ne'
    exact ⟨parity_target_in_support hN hp (Nat.prime_of_mem_primeFactors hr)
      (hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr)) hv,hv⟩

/-- Weighted prime occurrences in the ordinary component length are bounded
by its outdegree, with one possible loss at the base three. -/
theorem component_length_weight_le_odd_sigma_outdegree {N p : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hp : p∈N.primeFactors) (he : Even (N.factorization p)) :
    oddSourceWeight p (N.factorization p+1) ≤ (oddSigmaTargets N p).card+
      (if p=3 ∧ 5∣N.factorization p+1 then 1 else 0) := by
  have hodd : Odd (N.factorization p+1) := Nat.odd_iff.mpr (by have := Nat.even_iff.mp he; omega)
  rw [oddSigmaTargets_eq_of_even hN ho hp he,sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)]
  exact oddSourceWeight_le_geometric_odd_valuations (Nat.prime_of_mem_primeFactors hp).one_lt _ hodd

/-- The Euler index has precisely the same odd-valuation primes as the
Euler component's odd-valuation targets. -/
theorem euler_oddSigmaTargets_eq_index {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N) (hq : q.Prime)
    (hq4 : q%4=1) (ha4 : a%4=1) (hqm : ¬q∣m) (hform : N=q^a*m^2) :
    oddSigmaTargets N q = oddValuationPrimes (sigma 1 (m^2)/q^a) := by
  have hm := (ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _))
  have ha : 0<a := by omega
  have hqN : q∈N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq,hform ▸ dvd_mul_of_dvd_left (dvd_pow_self q ha.ne') _,hN.2.ne'⟩
  have hval : N.factorization q=a := by
    rw [hform,Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hm.pos.ne'),
      Finsupp.add_apply,hq.factorization_pow,Finsupp.single_eq_same,Nat.factorization_pow,
      Finsupp.smul_apply,Nat.factorization_eq_zero_of_not_dvd hqm,smul_eq_mul,mul_zero,add_zero]
  obtain ⟨i,hi,hleft,hright,_⟩ := exists_component_index hN hq hform (fun h => hqm (hq.dvd_of_dvd_pow h))
  rw [hleft,Nat.mul_div_cancel_left i (pow_pos hq.pos _)]
  let A := sigma 1 (q^a)
  have hA0 : A≠0 := (sigma_pos _ _ (pow_ne_zero _ hq.ne_zero)).ne'
  have hA4 := sigma_modEq_of_one hq (show q ≡ 1 [MOD 4] from hq4) a
  change A%4=(a+1)%4 at hA4
  have hio : Odd i := by
    have hA : A=2*(A/2) := by omega
    have hm2 := hm.pow (n:=2)
    change A*i=2*m^2 at hright
    have hh : A/2*i=m^2 := by rw [show A*i=2*(A/2*i) by rw [←mul_assoc,←hA]] at hright; omega
    exact hm2.of_dvd_nat (hh ▸ dvd_mul_left _ _)
  have heq (r : ℕ) (hr : r.Prime) (hro : Odd r) : Odd (A.factorization r) ↔ Odd (i.factorization r) := by
    have hn2 : ¬r∣2 := fun h => hro.not_two_dvd_nat (((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h) ▸ dvd_rfl)
    have h := congrArg (fun z : ℕ => z.factorization r) hright
    change (A*i).factorization r=(2*m^2).factorization r at h
    rw [Nat.factorization_mul hA0 hi.ne',Nat.factorization_mul (by decide : (2:ℕ)≠0) (pow_ne_zero _ hm.pos.ne'),
      Finsupp.add_apply,Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd hn2,zero_add,
      Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul] at h
    rw [Nat.odd_iff,Nat.odd_iff]
    omega
  ext r
  simp only [oddSigmaTargets,hval,mem_filter,mem_oddValuationPrimes]
  constructor
  · rintro ⟨hr,hv⟩
    exact (heq r (Nat.prime_of_mem_primeFactors hr) (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr))).mp hv
  · intro hv
    have hr : r∈i.primeFactors := Finsupp.mem_support_iff.mpr hv.pos.ne'
    have hro := hio.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr)
    have hA := (heq r (Nat.prime_of_mem_primeFactors hr) hro).mpr hv
    refine ⟨parity_target_in_support hN hqN (Nat.prime_of_mem_primeFactors hr) hro ?_,hA⟩
    simpa [hval] using hA

/-- The Euler source has a large distinct target for every prime of its
half-length, counting multiplicity and counting neutral occurrences twice. -/
theorem euler_length_weight_le_odd_sigma_outdegree {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (hqm : ¬q∣m) (hform : N=q^a*m^2) :
    let d := (a+1)/2
    cardFactors d+neutralLengthFactors q d ≤ ((oddSigmaTargets N q).filter (fun r => d.minFac<r)).card := by
  rw [euler_oddSigmaTargets_eq_index hN ho hq hq4 ha4 hqm hform]
  exact euler_half_length_weighted_odd_valuation_bound hN ho hq hq4 ha4 hqm hform

end OddPerfect
