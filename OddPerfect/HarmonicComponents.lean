module

public import OddPerfect.Harmonic
public import OddPerfect.GeometricSquareClass

public section

namespace OddPerfect

open Finset ArithmeticFunction

private theorem geom_pos (b : ℕ) {n : ℕ} (hn : 0<n) : 0 < geometricBlock b n :=
  sum_pos' (by intros; omega) ⟨0,mem_range.mpr hn,by simp⟩

private theorem block_two (b : ℕ) : geometricBlock b 2 = b+1 := by
  simp [geometricBlock,sum_range_succ,add_comm]

/-- For an odd base, its geometric sum contains at least as many factors
two as its length. Repeatedly halving an even length splits off b+1. -/
theorem two_valuation_length_le_geometric (n : ℕ) (hn : 0<n) (b : ℕ) (hb : Odd b) :
    n.factorization 2 ≤ (geometricBlock b n).factorization 2 := by
  induction n using Nat.strong_induction_on generalizing b with
  | ind n ih =>
    rcases Nat.even_or_odd n with h | h
    · obtain ⟨d,hd⟩ := h
      have hdpos : 0<d := by omega
      have hlt : d<n := by omega
      have hlen : n=2*d := by omega
      have hrec := ih d hlt hdpos (b^2) (hb.pow)
      have hdiv : 2 ∣ b+1 := by have := Nat.odd_iff.mp hb; omega
      have hone := (Nat.prime_two.dvd_iff_one_le_factorization (by omega : b+1≠0)).mp hdiv
      rw [hlen,geometricBlock_mul,block_two,Nat.factorization_mul (by decide) hdpos.ne',
        Nat.factorization_mul (by omega) (geom_pos _ hdpos).ne',Finsupp.add_apply,Finsupp.add_apply,
        Nat.prime_two.factorization_self]
      omega
    · rw [Nat.factorization_eq_zero_of_not_dvd h.not_two_dvd_nat]
      exact Nat.zero_le _

private theorem strict_two_valuation {b n : ℕ} (hb : b % 4 = 3) (hn : 0<n) (he : Even n) :
    n.factorization 2 < (geometricBlock b n).factorization 2 := by
  obtain ⟨d,hd⟩ := he
  have hdpos : 0<d := by omega
  have hlen : n=2*d := by omega
  have hbo : Odd b := Nat.odd_iff.mpr (by omega)
  have hrec := two_valuation_length_le_geometric d hdpos (b^2) hbo.pow
  have hdiv : 2^2 ∣ b+1 := by change 4 ∣ b+1; omega
  have htwo := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by omega : b+1≠0)).mp hdiv
  rw [hlen,geometricBlock_mul,block_two,Nat.factorization_mul (by decide) hdpos.ne',
    Nat.factorization_mul (by omega) (geom_pos _ hdpos).ne',Finsupp.add_apply,Finsupp.add_apply,
    Nat.prime_two.factorization_self]
  omega

private theorem harmonic_two_valuation_comparison {N : ℕ} (ho : Odd N) (hh : OreHarmonic N) :
    (∑ p ∈ N.primeFactors, (geometricBlock p (N.factorization p + 1)).factorization 2) ≤
    ∑ p ∈ N.primeFactors, (N.factorization p+1).factorization 2 := by
  have hs : sigma 1 N = ∏ p ∈ N.primeFactors, geometricBlock p (N.factorization p+1) := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ ho.pos.ne']
    apply prod_congr rfl
    intro p hp
    exact sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)
  have ht : 0 < N.divisors.card := card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr ho.pos.ne'⟩
  have hle := (Nat.factorization_le_iff_dvd (sigma_pos_iff.mpr ho.pos).ne'
    (Nat.mul_pos ho.pos ht).ne').mpr hh.2 2
  rw [hs,Nat.factorization_mul ho.pos.ne' ht.ne',Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd ho.not_two_dvd_nat,zero_add,
    Nat.card_divisors ho.pos.ne'] at hle
  simpa only [Nat.factorization_prod_apply (fun p _ => (geom_pos p (Nat.succ_pos _)).ne'),
    Nat.factorization_prod_apply (fun p _ => Nat.succ_ne_zero (N.factorization p))] using hle

/-- Garcia's Theorem 2. Every exact component of an odd harmonic integer
is one modulo four. The equality of the two-adic bounds forces each local
inequality to be an equality. -/
theorem odd_harmonic_component_one_mod_four {N p : ℕ} (ho : Odd N) (hh : OreHarmonic N)
    (hp : p ∈ N.primeFactors) : p ^ N.factorization p % 4 = 1 := by
  have hpo (r : ℕ) (hr : r ∈ N.primeFactors) : Odd r :=
    ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr)
  have hle := harmonic_two_valuation_comparison ho hh
  have he : p%4=3 → Even (N.factorization p) := by
    intro hp3
    by_contra he
    have hodd := Nat.even_iff.not.mp he
    have hlen : Even (N.factorization p+1) := Nat.even_iff.mpr (by omega)
    have hstrict := strict_two_valuation hp3 (Nat.succ_pos _) hlen
    apply hle.not_gt
    exact sum_lt_sum (fun r hr => two_valuation_length_le_geometric _ (Nat.succ_pos _) r (hpo r hr))
      ⟨p,hp,hstrict⟩
  have hodd := Nat.odd_iff.mp (hpo p hp)
  rcases (show p%4=1 ∨ p%4=3 by omega) with h | h
  · change p ^ N.factorization p ≡ 1 [MOD 4]
    simpa only [one_pow] using (show p ≡ 1 [MOD 4] from h).pow (N.factorization p)
  · obtain ⟨a,ha⟩ := he h
    have hs : p^2 ≡ 1 [MOD 4] := ((show p ≡ 3 [MOD 4] from h).pow 2).trans (by decide)
    rw [show N.factorization p=2*a by omega,pow_mul]
    change (p^2)^a ≡ 1 [MOD 4]
    simpa only [one_pow] using hs.pow a

/-- Garcia's Theorem 3. The divisor count of any odd harmonic integer
has an odd prime divisor. The least prime divisor of N supplies the component used in the proof. -/
theorem odd_prime_dvd_card_divisors_of_odd_harmonic {N : ℕ} (ho : Odd N) (hh : OreHarmonic N) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ r ∣ N.divisors.card := by
  let p := N.minFac
  have hp : p.Prime := Nat.minFac_prime hh.1.ne'
  have hpN : p ∣ N := Nat.minFac_dvd _
  have hpS : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp,hpN,ho.pos.ne'⟩
  let e := N.factorization p
  have he : 0 < e := hp.factorization_pos_of_dvd ho.pos.ne' hpN
  have hpo := ho.of_dvd_nat hpN
  rcases Nat.even_or_odd e with hev | hod
  · have hodd : Odd (e+1) := Nat.odd_iff.mpr (by obtain ⟨t,ht⟩ := hev; omega)
    let r := (e+1).minFac
    have hd : r ∣ e+1 := Nat.minFac_dvd _
    have hdcard : e+1 ∣ N.divisors.card := by
      rw [Nat.card_divisors ho.pos.ne']
      exact dvd_prod_of_mem (fun q => N.factorization q+1) hpS
    exact ⟨r,Nat.minFac_prime (by omega),hodd.of_dvd_nat hd,hd.trans hdcard⟩
  · have hp4 : p%4=1 := by
      have hc := odd_harmonic_component_one_mod_four ho hh hpS
      have h2 := Nat.odd_iff.mp hpo
      by_contra h
      have hm : p ≡ 3 [MOD 4] := by change p%4=3; omega
      obtain ⟨t,ht⟩ := hod
      change p^e%4=1 at hc
      rw [ht,pow_succ,pow_mul] at hc
      have hs : p^2 ≡ 1 [MOD 4] := (hm.pow 2).trans (by decide)
      have ht3 : (p^2)^t*p ≡ 3 [MOD 4] := by simpa only [one_pow,one_mul] using (hs.pow t).mul hm
      change _ % 4 = 3 at ht3
      omega
    let d := (p+1)/2
    have hd1 : 1<d := by have := hp.two_le; dsimp [d]; omega
    have hdo : Odd d := Nat.odd_iff.mpr (by dsimp [d]; omega)
    let r := d.minFac
    have hr := Nat.minFac_prime hd1.ne'
    have hrd : r ∣ d := Nat.minFac_dvd _
    have hrp : r < p := (Nat.minFac_le hd1.le).trans_lt (by dsimp [d]; have := hp.two_le; omega)
    have hσ : sigma 1 (p^e) ∣ sigma 1 N := by
      rw [isMultiplicative_sigma.multiplicative_factorization _ ho.pos.ne']
      exact dvd_prod_of_mem _ hpS
    have hdsum : d ∣ p+1 := ⟨2,by dsimp [d]; omega⟩
    have hdtotal := hrd.trans (hdsum.trans ((succ_dvd_sigma_prime_pow hp hod).trans (hσ.trans hh.2)))
    refine ⟨r,hr,hdo.of_dvd_nat hrd,(hr.dvd_mul.mp hdtotal).resolve_left ?_⟩
    exact fun hd => hrp.not_ge (Nat.minFac_le_of_dvd hr.two_le hd)

/-- The odd squarefree exclusion in Ore's 1948 paper follows by computing
the divisor count as a power of two. -/
theorem odd_oreHarmonic_not_squarefree {N : ℕ} (ho : Odd N) (hh : OreHarmonic N) : ¬Squarefree N := by
  intro h
  obtain ⟨r,hr,hro,hd⟩ := odd_prime_dvd_card_divisors_of_odd_harmonic ho hh
  have hτ : N.divisors.card = 2^N.primeFactors.card := by
    rw [Nat.card_divisors ho.pos.ne']
    calc _ = ∏ _ ∈ N.primeFactors, (2:ℕ) := by
           apply prod_congr rfl
           intro p hp
           rw [Nat.factorization_eq_one_of_squarefree h (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)]
         _ = _ := by simp
  rw [hτ] at hd
  obtain rfl := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hd)
  exact hro.not_two_dvd_nat dvd_rfl

end OddPerfect
