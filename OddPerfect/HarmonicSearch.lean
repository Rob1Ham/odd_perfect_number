module

public import OddPerfect.DivisorCountBounds
public import OddPerfect.HarmonicComponents

public section

namespace OddPerfect.HarmonicSearch

open Finset ArithmeticFunction DivisorCountSearch
open DivisorMoments

/-- After removing exact prime powers, D,T,S are respectively the value,
divisor count and divisor sum of the prefix. The residual stores precisely
the divisibility and component conditions inherited from an odd harmonic
number. This allows a finite certificate to exclude an entire suffix. -/
structure Candidate (d D T S a m : ℕ) extends DivisorCountSearch.Candidate d 1 D T a m where
  harmonic : S * sigma 1 m ∣ (D*m)*(T*m.divisors.card)
  components : ∀ p, p^m.factorization p % 4 = 1

@[expose] def Closed (d D T S a : ℕ) : Prop := ∀ m, ¬ Candidate d D T S a m

theorem closed_of_plain {d D T S a : ℕ} (h : DivisorCountSearch.Closed d 1 D T a) :
    Closed d D T S a := fun m u => h m u.toCandidate

private theorem counterexample_moment {d D T S a m : ℕ} (h : Candidate d D T S a m) :
    1 < moment D T d 1 * moment m m.divisors.card d 1 := by
  rw [←moment_mul,moment,pow_one,lt_div_iff₀,one_mul]
  · exact_mod_cast h.bad
  · exact_mod_cast Nat.mul_pos h.prefix_pos h.pos

theorem closed_by_moment {d D T S a : ℕ} {W : ℚ} (hW : ResidualBound a d 1 W)
    (cut : moment D T d 1 * W ≤ 1) : Closed d D T S a := by
  intro m h
  exact (counterexample_moment h).not_ge ((mul_le_mul_of_nonneg_left (hW m h.pos h.lower)
    (moment_nonneg ..)).trans cut)

theorem closed_nonempty {d D T S a : ℕ} (ha : 3≤a) (hc : 2^d≤a)
    (he : T^d≤D ∨ ¬ S ∣ D*T)
    (cut : moment D T d 1 * ((2:ℚ)^d/a) ≤ 1) : Closed d D T S a := by
  intro m h
  by_cases hm : m=1
  · subst m
    have hb : D<T^d := by simpa using h.bad
    have hd : S ∣ D*T := by simpa using h.harmonic
    exact he.elim hb.not_ge (fun hn => hn hd)
  · have hw := divisor_moment_le_first_prime (show 1<m by have := h.pos; omega) ha h.lower
      (by simpa using hc : 2^d≤a^1)
    have hw' : moment m m.divisors.card d 1 ≤ (2:ℚ)^d/a := by simpa only [moment,pow_one] using hw
    exact (counterexample_moment h).not_ge ((mul_le_mul_of_nonneg_left hw' (moment_nonneg ..)).trans cut)

/-- Retain one particular component while bounding all others by one. -/
private theorem moment_le_component {d a m p b v : ℕ} (hm : 0<m) (hpr : ∀ w ∈ m.primeFactors, a≤w)
    (hc : 2^d ≤ a) (hp : p ∈ m.primeFactors) (hb : 0<b) (hle : b≤p)
    (hv : v≤m.factorization p) : moment m m.divisors.card d 1 ≤ component b d 1 v := by
  have hpos := (Nat.prime_of_mem_primeFactors hp).pos
  have hstep : (0+2)^d ≤ p^1*(0+1)^d := by simpa using hc.trans (hpr p hp)
  rw [moment, divisor_moment_factorization hm]
  calc _ ≤ ∏ u ∈ ({p}:Finset ℕ), component u d 1 (m.factorization u) := by
         refine prod_le_prod_of_subset_of_le_one₀ (singleton_subset_iff.mpr hp) ?_ ?_
         · intro u _; unfold component; positivity
         · intro u hu _
           exact component_le_one (Nat.prime_of_mem_primeFactors hu).pos (by simpa using hc.trans (hpr u hu))
       _ = component p d 1 (m.factorization p) := by simp
       _ ≤ component p d 1 v := component_antitone_from hpos hstep (Nat.zero_le _) hv
       _ ≤ _ := by
         simp only [component,one_mul]
         exact div_le_div_of_nonneg_left (by positivity) (pow_pos (by exact_mod_cast hb) _)
           (by exact_mod_cast Nat.pow_le_pow_left hle v)

/-- A prime still owed by the divisor sum either divides the residual
integer or divides one of its exponent lengths. The two alternatives
give independent upper bounds on the remaining divisor-count moment. -/
theorem closed_owed_prime {d D T S a r v : ℕ} (ha : 3≤a) (hc : 2^d≤a) (hr : r.Prime)
    (hS : r ∣ S) (hDT : ¬ r ∣ D*T) (hv : v<r)
    (lengthCut : moment D T d 1 * component a d 1 v ≤ 1)
    (baseCut : r<a ∨ moment D T d 1 * component r d 1 (if r%4=3 then 2 else 1) ≤ 1) :
    Closed d D T S a := by
  intro m h
  have hd := hS.trans ((dvd_mul_right S (sigma 1 m)).trans h.harmonic)
  rw [show (D*m)*(T*m.divisors.card) = (D*T)*(m*m.divisors.card) by ac_rfl] at hd
  obtain hm|ht := hr.dvd_mul.mp ((hr.dvd_mul.mp hd).resolve_left hDT)
  · have hp := Nat.mem_primeFactors.mpr ⟨hr,hm,h.pos.ne'⟩
    have he := hr.factorization_pos_of_dvd h.pos.ne' hm
    have hv' : (if r%4=3 then 2 else 1) ≤ m.factorization r := by
      split
      · rename_i hb
        have e1 : m.factorization r≠1 := by
          intro heq
          have hu := h.components r
          rw [heq,pow_one,hb] at hu
          contradiction
        omega
      · omega
    have cut := baseCut.resolve_left (not_lt.mpr (h.lower r hp))
    have w := moment_le_component h.pos h.lower hc hp hr.pos (Nat.le_refl r) hv'
    exact (counterexample_moment h).not_ge ((mul_le_mul_of_nonneg_left w (moment_nonneg ..)).trans cut)
  · rw [Nat.card_divisors h.pos.ne'] at ht
    obtain ⟨p,hp,hd⟩ := (hr.prime.dvd_finsetProd_iff _).mp ht
    have he := Nat.le_of_dvd (Nat.succ_pos _) hd
    have w := moment_le_component h.pos h.lower hc hp (by omega : 0<a) (h.lower p hp)
      (by omega : v ≤ m.factorization p)
    exact (counterexample_moment h).not_ge ((mul_le_mul_of_nonneg_left w (moment_nonneg ..)).trans lengthCut)

@[expose] def localSum (p e : ℕ) : ℕ := ∑ j ∈ range (e+1), p^j

theorem closed_split {d D T S p a : ℕ} (hp : p.Prime) (gap : ∀ j ∈ Ioo p a, ¬j.Prime)
    (branches : ∀ e, p^e%4=1 → Closed d (D*p^e) (T*(e+1)) (S*localSum p e) a) :
    Closed d D T S p := by
  intro m h
  obtain ⟨e,r,hr,hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd h.pos.ne' p hp.ne_one
  have hpp := pow_pos hp.pos e
  have hrpos : 0<r := by by_contra! he; have := h.pos; simp [hm,Nat.eq_zero_of_le_zero he] at this
  have hc : (p^e).Coprime r := (hp.coprime_pow_of_not_dvd hr).symm
  have ht : m.divisors.card = (e+1)*r.divisors.card := by
    rw [hm,hc.card_divisors_mul,←sigma_zero_apply,sigma_zero_apply_prime_pow hp]
  have hs : sigma 1 m = localSum p e * sigma 1 r := by
    rw [hm,isMultiplicative_sigma.map_mul_of_coprime hc,sigma_one_apply_prime_pow hp,localSum]
  have hx : D*m=(D*p^e)*r := by rw [hm,mul_assoc]
  have ht' : T*m.divisors.card=(T*(e+1))*r.divisors.card := by rw [ht,mul_assoc]
  have hfac (u : ℕ) : m.factorization u = (p^e).factorization u + r.factorization u := by
    rw [hm,Nat.factorization_mul hpp.ne' hrpos.ne',Finsupp.add_apply]
  have hpe : m.factorization p=e := by
    rw [hfac,Nat.factorization_pow_self hp,Nat.factorization_eq_zero_of_not_dvd hr,Nat.add_zero]
  apply branches e (hpe ▸ h.components p) r
  refine ⟨⟨hrpos,Nat.mul_pos h.prefix_pos hpp,?_,hx ▸ h.size,?_⟩,?_,?_⟩
  · intro q hq
    have hqr := Nat.dvd_of_mem_primeFactors hq
    have hqm : q ∣ m := hm ▸ hqr.trans (dvd_mul_left _ _)
    have hprime := Nat.prime_of_mem_primeFactors hq
    have hleast := h.lower q (Nat.mem_primeFactors.mpr ⟨hprime,hqm,h.pos.ne'⟩)
    by_contra! hlt
    exact gap q (mem_Ioo.mpr ⟨lt_of_le_of_ne hleast (fun he => hr (he ▸ hqr)),hlt⟩) hprime
  · simpa only [←hx,←ht'] using h.bad
  · simpa only [hs,hx,ht',mul_assoc] using h.harmonic
  · intro q
    by_cases eq : p=q
    · subst q; simp [Nat.factorization_eq_zero_of_not_dvd hr]
    · have hz : (p^e).factorization q = 0 := by
        simp [hp.factorization_pow,Ne.symm eq]
      simpa only [hfac q,hz,zero_add] using h.components q

theorem divisor_bound_of_closed {d : ℕ} (hc : Closed d 1 1 1 3) {N : ℕ}
    (ho : Odd N) (hh : OreHarmonic N) : N.divisors.card^d ≤ N := by
  by_contra! hb
  apply hc N
  refine ⟨⟨ho.pos,by decide,?_,by simpa using (show 1≤N from ho.pos),by simpa using hb⟩,by simpa using hh.2,?_⟩
  · intro p hp
    have := Nat.odd_iff.mp (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  · intro p
    by_cases hp : p ∈ N.primeFactors
    · exact odd_harmonic_component_one_mod_four ho hh hp
    · have hz : N.factorization p=0 := (N.factorization.notMem_support_iff).mp hp
      simp [hz]

end OddPerfect.HarmonicSearch
