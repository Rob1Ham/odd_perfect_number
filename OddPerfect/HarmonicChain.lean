module

public import OddPerfect.HarmonicThreshold
public import OddPerfect.FactorBudget
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Factorial.Basic

public section

namespace OddPerfect.HarmonicChain
open FactorBudget ArithmeticFunction Finset

/-- The largest possible prime divisor of the divisor count is retained as
a hypothesis. This permits a descending exclusion or a single maximum-prime argument. -/
structure Small (n r : ℕ) : Prop where
  odd : Odd n
  harmonic : OreHarmonic n
  size : n≤10^24
  smooth : ∀ p, p.Prime → p∣n.divisors.card → p≤r

@[expose] def Closed (r : ℕ) (s : Node) : Prop := ∀ n m, Small n r → Realizes s n m → False

theorem Small.component_lt {n r p a : ℕ} (H : Small n r) (hp : p.Prime) (ha : 0<a)
    (hd : p^a∣n) : p^a < 10^15 := by
  by_contra! h
  exact H.size.not_gt (ten_pow_twenty_four_lt_of_harmonic_component H.odd H.harmonic hp ha hd h)

theorem Small.coprime_divisor_count {n r c : ℕ} (H : Small n r) (hc : c.Coprime r.factorial) :
    c.Coprime n.divisors.card := by
  by_contra hn
  obtain ⟨p,hp,hd,ht⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
  exact hp.not_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd hd (Nat.dvd_factorial hp.pos (H.smooth p hp ht)))

theorem forced_dvd {n r m c : ℕ} {s : Node} (H : Small n r) (h : Realizes s n m)
    (hs : c∣s.divisorSum) (hc : c.Coprime r.factorial) : s.component.lcm c ∣ n := by
  have hsum : s.divisorSum ∣ sigma 1 n := by
    rw [h.value,isMultiplicative_sigma.map_mul_of_coprime h.coprime,h.sigma]
    exact dvd_mul_right _ _
  have hd := (hs.trans hsum).trans H.harmonic.2
  exact Nat.lcm_dvd (h.value ▸ dvd_mul_right _ _) ((H.coprime_divisor_count hc).dvd_of_dvd_mul_right hd)

private theorem raised_power {n r p e : ℕ} (H : Small n r) (hp : p.Prime) (h3 : p%4=3)
    (he : e%2=1) (hd : p^e∣n) : p^(e+1)∣n := by
  have le := (hp.pow_dvd_iff_le_factorization H.odd.pos.ne').mp hd
  apply (hp.pow_dvd_iff_le_factorization H.odd.pos.ne').mpr
  by_contra! bad
  have eq : n.factorization p=e := by omega
  have hpos : 0<e := by omega
  have hpN := Nat.mem_primeFactors.mpr ⟨hp,(dvd_pow_self p hpos.ne').trans hd,H.odd.pos.ne'⟩
  have hg := odd_harmonic_component_one_mod_four H.odd H.harmonic hpN
  rw [eq,Nat.pow_mod] at hg
  have hpow : ∀ j : ℕ, (3:ℕ)^(2*j+1)%4=3 := by
    intro j
    rw [pow_succ,pow_mul,Nat.mul_mod,Nat.pow_mod]
    simp
  have eodd : e=2*(e/2)+1 := by omega
  rw [h3,eodd,hpow] at hg
  contradiction

/-- Extra even valuations forced by Garcia are certified one at a time.
A proposed pair that does not pass its tests leaves the divisor unchanged. -/
@[expose] def raised (u : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => u
  | (p,e)::l =>
    if p%4=3 ∧ e%2=1 ∧ p^e∣u then raised (u.lcm (p^(e+1))) l else raised u l

theorem raised_dvd {n r : ℕ} (H : Small n r) (l : List (ℕ × ℕ))
    (hp : ∀ z ∈ l, Nat.Prime z.1) {u : ℕ} (hd : u∣n) : raised u l∣n := by
  induction l generalizing u with
  | nil => exact hd
  | cons z l ih =>
    have rest (z) (hz : z∈l) := hp z (List.mem_cons_of_mem _ hz)
    obtain ⟨p,e⟩ := z
    rw [raised]
    split
    · rename_i h
      exact ih rest (Nat.lcm_dvd hd (raised_power H (hp _ (.head _)) h.1 h.2.1 (h.2.2.trans hd)))
    · exact ih rest hd

theorem closed_size {r c : ℕ} {s : Node} (l : List (ℕ × ℕ)) (hs : c∣s.divisorSum)
    (hc : c.Coprime r.factorial) (hp : ∀ z ∈ l, Nat.Prime z.1)
    (cut : 10^24 < raised (s.component.lcm c) l) : Closed r s := by
  intro n m H h
  exact cut.not_ge ((Nat.le_of_dvd H.odd.pos (raised_dvd H l hp (forced_dvd H h hs hc))).trans H.size)

theorem closed_component {r c p e : ℕ} {s : Node} (l : List (ℕ × ℕ)) (hs : c∣s.divisorSum)
    (hc : c.Coprime r.factorial) (hpr : ∀ z ∈ l, Nat.Prime z.1)
    (hp : p.Prime) (he : 0<e) (hd : p^e ∣ raised (s.component.lcm c) l)
    (big : 10^15≤p^e) : Closed r s := by
  intro n m H h
  exact big.not_gt (H.component_lt hp he (hd.trans (raised_dvd H l hpr (forced_dvd H h hs hc))))

theorem closed_exact {r c p e : ℕ} {s : Node} (hs : c∣s.divisorSum) (hc : c.Coprime r.factorial)
    (hp : p.Prime) (hD : p∣s.component) (hsmall : ¬p^e∣s.component) (hforce : p^e∣c) : Closed r s := by
  intro n m H h
  have hpm := h.coprime.coprime_dvd_left hD
  have hdn := hforce.trans ((Nat.dvd_lcm_right _ _).trans (forced_dvd H h hs hc))
  rw [h.value] at hdn
  exact hsmall ((hpm.pow_left e).dvd_of_dvd_mul_right hdn)

@[expose] def Allowed (p e : ℕ) : Prop := 0<e ∧ p^e<10^15 ∧ p^e%4=1

/-- Split at the true valuation at a prime, with an explicit proof that
the chosen prime divides the remaining cofactor. -/
theorem split_at {n m r p : ℕ} {s : Node} (H : Small n r) (h : Realizes s n m)
    (hp : p.Prime) (hm : p∣m) : Allowed p (m.factorization p) ∧
    ∃ v, Realizes (s.extend p (m.factorization p)) n v := by
  have nz := H.odd.pos.ne'
  have hz := mul_ne_zero_iff.mp (h.value ▸ nz)
  have hnot : ¬p∣s.component := fun hpd =>
    hp.not_dvd_one (h.coprime.gcd_eq_one ▸ Nat.dvd_gcd hpd hm)
  have add : n.factorization p=m.factorization p := by
    rw [h.value,Nat.factorization_mul hz.1 hz.2,Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnot,zero_add]
  have he := hp.factorization_pos_of_dvd hz.2 hm
  have hd := hp.pow_dvd_iff_le_factorization nz |>.mpr add.ge
  have hg := odd_harmonic_component_one_mod_four H.odd H.harmonic
    (Nat.mem_primeFactors.mpr ⟨hp,hm.trans (h.value ▸ dvd_mul_left _ _),nz⟩)
  exact ⟨⟨he,H.component_lt hp he hd,add ▸ hg⟩,_,extend_realizes nz h hp hm⟩

theorem closed_split {r c p : ℕ} {s : Node} (hs : c∣s.divisorSum) (hc : c.Coprime r.factorial)
    (hp : p.Prime) (hn : ¬p∣s.component) (hpc : p∣c)
    (branches : ∀ e, Allowed p e → Closed r (s.extend p e)) : Closed r s := by
  intro n m H h
  have hd := hpc.trans ((Nat.dvd_lcm_right _ _).trans (forced_dvd H h hs hc))
  rw [h.value] at hd
  obtain ⟨he,v,hv⟩ := split_at H h hp ((hp.dvd_mul.mp hd).resolve_left hn)
  exact branches _ he n v H hv

end OddPerfect.HarmonicChain
