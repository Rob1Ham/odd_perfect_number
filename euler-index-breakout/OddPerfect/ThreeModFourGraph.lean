module

public import OddPerfect.OddValuationGraph
public import OddPerfect.Reciprocity
public import OddPerfect.ChenLuo
import all OddPerfect.ChenLuo
import all OddPerfect.Reciprocity
import all OddPerfect.OddValuationGraph
import Mathlib.Algebra.BigOperators.ModEq

public section
namespace OddPerfect
open Finset ArithmeticFunction

/-- The number of negative factors modulo four, counting only odd
valuations, gives the residue of any odd natural number. -/
theorem mod_four_three_odd_factors {n : ℕ} (ho : Odd n) :
    n ≡ 3^(threeOddFactors n).card [MOD 4] := by
  let good (p : ℕ) := p%4=3 ∧ Odd (n.factorization p)
  calc
    n = ∏ p∈n.primeFactors, p^n.factorization p := Nat.prod_primeFactors_pow_factorization ho.pos.ne'
    _ ≡ ∏ p∈n.primeFactors, (if good p then 3 else 1) [MOD 4] := by
      apply Nat.ModEq.prod
      intro p hp
      have hpo := Nat.odd_iff.mp (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
      by_cases hp3 : p%4=3
      · have h := (show p ≡ 3 [MOD 4] from hp3).pow (n.factorization p)
        dsimp only [good]
        by_cases hv : Odd (n.factorization p)
        · simp only [hp3,hv,and_self,ite_true]
          exact h.trans (show 3^(n.factorization p) ≡ 3 [MOD 4] from (three_pow_mod_four_iff_odd _).mpr hv)
        · simp only [hp3,hv,and_false,ite_false]
          obtain ⟨j,hj⟩ := (Nat.even_or_odd _).resolve_right hv
          rw [show n.factorization p=2*j by omega,pow_mul]
          simpa using (((show p ≡ 3 [MOD 4] from hp3).pow 2).trans (by decide : (3:ℕ)^2 ≡ 1 [MOD 4])).pow j
      · simpa [good,hp3] using (show p ≡ 1 [MOD 4] from (by change p%4=1; omega)).pow (n.factorization p)
    _ = _ := by rw [←Finset.prod_filter]; simp [threeOddFactors,good]

/-- Targets among the prime divisors of N that are 3 modulo 4 and receive
an odd valuation from p. -/
@[expose] def threeOddTargets (N p : ℕ) : Finset ℕ :=
  N.primeFactors.filter (fun r => r%4=3 ∧ Odd ((sigma 1 (p^N.factorization p)).factorization r))

private theorem threeOddTargets_eq_factors {N p : ℕ} (hN : N.Perfect) (hp : p∈N.primeFactors) :
    threeOddTargets N p=threeOddFactors (sigma 1 (p^N.factorization p)) := by
  ext r
  simp only [threeOddTargets,threeOddFactors,mem_filter]
  constructor
  · rintro ⟨_,hr3,hv⟩
    exact ⟨Finsupp.mem_support_iff.mpr hv.pos.ne',hr3,hv⟩
  · rintro ⟨hrS,hr3,hv⟩
    have hro : Odd r := Nat.odd_iff.mpr (by omega)
    exact ⟨parity_target_in_support hN hp (Nat.prime_of_mem_primeFactors hrS) hro hv,hr3,hv⟩

theorem even_threeOddTargets_of_three_mod_four {N p : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hp : p∈N.primeFactors) (hp3 : p%4=3) : Even (threeOddTargets N p).card := by
  obtain ⟨j,hj⟩ := even_exponent_of_three_mod_four hN ho hp3
  have hs := sigma_three_mod_four_even (Nat.prime_of_mem_primeFactors hp) hp3 j
  rw [show 2*j=N.factorization p by omega] at hs
  let S := sigma 1 (p^N.factorization p)
  have hs1 : S%4=1 := hs
  have hm := mod_four_three_odd_factors (n:=S) (Nat.odd_iff.mpr (by omega))
  change S%4=3^(threeOddFactors S).card%4 at hm
  rw [threeOddTargets_eq_factors hN hp]
  change Even (threeOddFactors S).card
  apply (Nat.even_or_odd _).resolve_right
  intro hv
  have hh := (three_pow_mod_four_iff_odd _).mpr hv
  omega

private theorem threeOddFactors_two_mul {H : ℕ} (hH : 0<H) :
    threeOddFactors (2*H)=threeOddFactors H := by
  ext r
  simp only [threeOddFactors,mem_filter]
  by_cases h3 : r%4=3
  · have hnot : ¬r∣2 := by intro h; have := Nat.le_of_dvd (by decide : 0<(2:ℕ)) h; omega
    have hv : (2*H).factorization r=H.factorization r := by
      rw [Nat.factorization_mul (by decide : (2:ℕ)≠0) hH.ne',Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hnot,zero_add]
    constructor
    · rintro ⟨_,_,ho⟩
      rw [hv] at ho
      exact ⟨Finsupp.mem_support_iff.mpr ho.pos.ne',h3,ho⟩
    · rintro ⟨_,_,ho⟩
      have hp : Odd ((2*H).factorization r) := hv ▸ ho
      exact ⟨Finsupp.mem_support_iff.mpr hp.pos.ne',h3,hp⟩
  · simp [h3]

/-- The Euler component emits an odd number of edges into the class
three modulo four exactly when its prime and exponent differ modulo eight. -/
theorem odd_threeOddTargets_euler_iff {N q : ℕ} (hN : N.Perfect) (hq : q∈N.primeFactors)
    (hq4 : q%4=1) (ha4 : N.factorization q%4=1) :
    Odd (threeOddTargets N q).card ↔ q%8≠N.factorization q%8 := by
  let a := N.factorization q
  let S := sigma 1 (q^a)
  let H := S/2
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hS4 := sigma_modEq_of_one hqp (show q ≡ 1 [MOD 4] from hq4) a
  change S%4=(a+1)%4 at hS4
  change a%4=1 at ha4
  have hS : S=2*H := by dsimp only [H]; omega
  have hHo : Odd H := Nat.odd_iff.mpr (by dsimp only [H]; omega)
  have hres := (half_sigma_prime_pow_mod_eight hqp (Nat.odd_iff.mpr (by omega : q%2=1))
    (Nat.odd_iff.mpr (by omega : a%2=1))).of_dvd (by decide : 4∣8)
  change H%4=(((q+1)/2)*((a+1)/2))%4 at hres
  have hsign := mod_four_three_odd_factors hHo
  change H%4=3^(threeOddFactors H).card%4 at hsign
  rw [threeOddTargets_eq_factors hN hq]
  change Odd (threeOddFactors S).card ↔ q%8≠a%8
  rw [hS,threeOddFactors_two_mul hHo.pos,←three_pow_mod_four_iff_odd,←hsign,hres,Nat.mul_mod]
  have cases (x : ℕ) (hx : x%4=1) :
      (x%8=1 ∧ ((x+1)/2)%4=1) ∨ (x%8=5 ∧ ((x+1)/2)%4=3) := by omega
  rcases cases q hq4 with hq | hq <;> rcases cases a ha4 with ha | ha <;> rw [hq.2,ha.2] <;> omega

/-- Every odd-valuation edge inside the residue class 3 mod 4 has a
second target in that class. Neither target returns a divisor-sum edge. -/
theorem odd_sigma_three_mod_four_fork {N p r : ℕ} (hN : N.Perfect) (ho : Odd N)
    (he : oddSigmaEdge N p r) (hp3 : p%4=3) (hr3 : r%4=3) :
    ∃ t, t≠r ∧ t%4=3 ∧ oddSigmaEdge N p t ∧ ¬sigmaEdge N t p ∧ ¬sigmaEdge N r p := by
  have hr : r∈threeOddTargets N p := mem_filter.mpr ⟨he.2.1,hr3,he.2.2⟩
  have hpos := card_pos.mpr (show (threeOddTargets N p).Nonempty from ⟨r,hr⟩)
  have hpar := Nat.even_iff.mp (even_threeOddTargets_of_three_mod_four hN ho he.1 hp3)
  obtain ⟨t,ht,hne⟩ := exists_mem_ne (show 1<(threeOddTargets N p).card by omega) r
  obtain ⟨htN,ht3,hv⟩ := mem_filter.mp ht
  have het : oddSigmaEdge N p t := ⟨he.1,htN,hv⟩
  exact ⟨t,hne,ht3,het,not_sigmaEdge_reverse_of_three_mod_four hN ho (oddSigmaEdge_sigmaEdge het)
    (oddSigmaEdge_ne het) hp3 ht3,not_sigmaEdge_reverse_of_three_mod_four hN ho (oddSigmaEdge_sigmaEdge he)
    (oddSigmaEdge_ne he) hp3 hr3⟩

/-- Even a two-step path inside the odd-valuation graph on primes 3 mod 4
forces a fourth prime in that class. -/
theorem four_three_mod_four_of_odd_sigma_path {N p r s : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hpr : oddSigmaEdge N p r) (hrs : oddSigmaEdge N r s)
    (hp3 : p%4=3) (hr3 : r%4=3) (hs3 : s%4=3) :
    4≤(N.primeFactors.filter (fun q => q%4=3)).card := by
  obtain ⟨t,hts,ht3,hrt,_,_⟩ := odd_sigma_three_mod_four_fork hN ho hrs hr3 hs3
  have hno := not_sigmaEdge_reverse_of_three_mod_four hN ho (oddSigmaEdge_sigmaEdge hpr) (oddSigmaEdge_ne hpr) hp3 hr3
  have hps : p≠s := by rintro rfl; exact hno (oddSigmaEdge_sigmaEdge hrs)
  have hpt : p≠t := by rintro rfl; exact hno (oddSigmaEdge_sigmaEdge hrt)
  have hd : ({p,r,s,t}:Finset ℕ)⊆N.primeFactors.filter (fun q => q%4=3) := by
    intro x hx
    rcases (show x=p ∨ x=r ∨ x=s ∨ x=t by simpa using hx) with rfl | rfl | rfl | rfl
    · exact mem_filter.mpr ⟨hpr.1,hp3⟩
    · exact mem_filter.mpr ⟨hpr.2.1,hr3⟩
    · exact mem_filter.mpr ⟨hrs.2.1,hs3⟩
    · exact mem_filter.mpr ⟨hrt.2.1,ht3⟩
  have hcard : ({p,r,s,t}:Finset ℕ).card=4 := by
    simp [oddSigmaEdge_ne hpr,oddSigmaEdge_ne hrs,oddSigmaEdge_ne hrt,hps,hpt,hts.symm]
  calc
    4 = ({p,r,s,t}:Finset ℕ).card := hcard.symm
    _ ≤ _ := card_le_card hd

end OddPerfect
