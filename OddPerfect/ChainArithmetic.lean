module

public import OddPerfect.ChainCheckpoint

/-! Divisibility and coprimality checks using short modular inverse witnesses. -/

public section

namespace OddPerfect.FactorBudget
open ArithmeticFunction

@[expose] def Node.admissible (s : Node) (p e B w : ℕ) : Bool :=
  decide ((e%2=0 ∨ (s.divisorSum%2=1 ∧ p%4=1 ∧ e%4=1)) ∧
    s.spent+e + 2*(w-(s.closed+1)) + (s.spent+e)%2 ≤ B+1)

theorem admissible_of_realizes {N m B w p : ℕ} {s : Node} (H : Conditions N B w)
    (h : Realizes s N m) (hp : p.Prime) (hd : p∣m) : s.admissible p (m.factorization p) B w = true := by
  let e := m.factorization p
  have hv := extend_realizes H.odd.pos.ne' h hp hd
  have hb := budget_bound H hv (k := 0) (Nat.zero_le _)
  simp only [Nat.zero_max,Node.extend] at hb
  apply decide_eq_true
  refine ⟨?_,hb⟩
  by_cases he : e%2=0
  · exact Or.inl he
  right
  have hn := H.odd.pos.ne'
  have hdm := mul_ne_zero_iff.mp (h.value ▸ hn)
  have hpn : ¬p∣s.component := hp.coprime_iff_not_dvd.mp (h.coprime.coprime_dvd_right hd).symm
  have hfac : N.factorization p = e := by
    rw [h.value,Nat.factorization_mul hdm.1 hdm.2,Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpn,zero_add]
  obtain ⟨q,_,hq,heq,hother⟩ := euler_exponents H.odd H.perfect
  have hqeq : p=q := by
    by_contra hne
    have := Nat.even_iff.mp (hother p hne)
    rw [hfac] at this
    omega
  subst q
  rw [hfac] at heq
  refine ⟨?_,hq,heq⟩
  by_contra hnot
  have hdiv : 2∣s.divisorSum := Nat.dvd_of_mod_eq_zero (by omega)
  have hpodd : Odd p := H.odd.of_dvd_nat (hd.trans (h.value ▸ Nat.dvd_mul_left _ _))
  have hgeom : SupportSieve.geomValue p (e+1) = sigma 1 (p^e) := by
    rw [sigma_one_apply_prime_pow hp, SupportSieve.geomValue, ← geom_sum_mul_of_one_le hp.one_le,
      Nat.mul_div_cancel _ (by have := hp.one_lt; omega)]
  have hm2 := sigma_modEq_of_one hp (Nat.odd_iff.mp hpodd) e
  change sigma 1 (p^e)%2 = (e+1)%2 at hm2
  have hgeo : 2∣SupportSieve.geomValue p (e+1) := by
    rw [hgeom]
    exact Nat.dvd_of_mod_eq_zero (by omega)
  have h4 := Nat.mul_dvd_mul hdiv hgeo
  apply automatic_false H hv
  apply decide_eq_true
  exact Or.inl h4

@[expose] def Node.closesGroups (s : Node) (B w c : ℕ) (gs : List ℕ) : Bool :=
  checkGroups gs && decide (gs.prod∣s.forcedPart ∧
    (B+1 < s.spent + 2*max gs.length (w-s.closed) + s.spent%2 ∨
     7*B+c < 18*(s.closed+gs.length) ∨
     2*s.component*gs.prod < s.divisorSum*(gs.map (· + 1)).prod))

theorem closesGroups_false {N m B w c : ℕ} {s : Node} (H : Conditions N B w)
    (h : Realizes s N m) (hc : 18*N.primeFactors.card ≤ 7*B+c) (gs : List ℕ)
    (test : s.closesGroups B w c gs = true) : False := by
  simp only [Node.closesGroups,Bool.and_eq_true,decide_eq_true_eq] at test
  obtain ⟨hg,hd,hb | hx⟩ := test
  · exact hb.not_ge (budget_bound H h (groups_le_support H.perfect h gs hg hd))
  · apply extraGroupCheck_false H h hc gs
    simpa only [Node.extraGroupCheck,Bool.and_eq_true,decide_eq_true_eq] using And.intro hg (And.intro hd hx)


/-- A divisor of the selected divisor sum coprime to twice the selected component
survives in the forced residual. The inverse is supplied by the certificate. -/
@[expose] def Node.partWitness (s : Node) (g inv : ℕ) : Bool :=
  decide (g ∣ s.divisorSum ∧ (2*s.component)*inv % g = 1 % g)

theorem Node.partWitness_dvd {s : Node} {g inv : ℕ}
    (test : s.partWitness g inv = true) : g ∣ s.forcedPart := by
  obtain ⟨hd, hi⟩ := of_decide_eq_true test
  have hcop := (Nat.coprime_of_mul_modEq_one inv hi).symm
  have hc := hcop.coprime_dvd_right (Nat.gcd_dvd_right s.divisorSum (2*s.component))
  apply hc.dvd_of_dvd_mul_left
  simpa only [Node.forcedPart, Nat.mul_div_cancel' (Nat.gcd_dvd_left s.divisorSum (2*s.component))] using hd

@[expose] def Node.groupWitness (s : Node) (B w c inv : ℕ) (gs : List ℕ) : Bool :=
  checkGroups gs && s.partWitness gs.prod inv && decide (
    B+1 < s.spent + 2*max gs.length (w-s.closed) + s.spent%2 ∨
    7*B+c < 18*(s.closed+gs.length) ∨
    2*s.component*gs.prod < s.divisorSum*(gs.map (· + 1)).prod)

theorem Node.groupWitness_closes {s : Node} {B w c inv : ℕ} {gs : List ℕ}
    (test : s.groupWitness B w c inv gs = true) : s.closesGroups B w c gs = true := by
  simp only [Node.groupWitness,Node.closesGroups,Bool.and_eq_true,decide_eq_true_eq] at test ⊢
  exact ⟨test.1.1,Node.partWitness_dvd test.1.2,test.2⟩

/-- Both divisibility of the residual factor and its lack of small prime divisors
may be checked by modular multiplication. -/
@[expose] def Node.cutWitness (s : Node) (B a L g inv roughInv : ℕ) : Bool :=
  let k := s.residualCap B - 1
  decide (1<a ∧ 1<L ∧ s.divisorSum < 2*s.component ∧
    (L≤a ∨ (1<g ∧ s.partWitness g inv = true ∧
      (L-1).factorial * roughInv % g = 1 % g)) ∧
    s.divisorSum * L * a^k ≤ 2*s.component*(L-1)*(a-1)^k)

theorem Node.cutWitness_valid {s : Node} {B a L g inv roughInv : ℕ}
    (test : s.cutWitness B a L g inv roughInv = true) : s.validAbundancyCut B a L g = true := by
  obtain ⟨ha,hL,hs,hg,hnum⟩ := of_decide_eq_true test
  apply decide_eq_true
  refine ⟨ha,hL,hs,?_,hnum⟩
  rcases hg with hle | ⟨hgt,hpart,hinv⟩
  · exact Or.inl hle
  · exact Or.inr ⟨hgt,Node.partWitness_dvd hpart,(Nat.coprime_of_mul_modEq_one roughInv hinv).symm⟩

end OddPerfect.FactorBudget
