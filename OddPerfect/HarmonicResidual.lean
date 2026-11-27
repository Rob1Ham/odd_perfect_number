module

public import OddPerfect.DivisorCountValuation
import Mathlib.Tactic.Ring

public section

namespace OddPerfect.HarmonicChain
open FactorBudget ArithmeticFunction Finset

/-- The divisor-count factor T and an optional exclusion of 3 from the
remaining cofactor are the two extra data needed at stalled factor chains. -/
@[expose] def Refined (s : Node) (T : ℕ) (ban : Bool) : Prop :=
  ∀ n m, Small n 3 → Realizes s n m → n.divisors.card = T*m.divisors.card →
    (ban = true → ¬ 3 ∣ m) → False

theorem refine_closed {s : Node} {T : ℕ} {ban : Bool} (h : Closed 3 s) : Refined s T ban :=
  fun n m H hm _ _ => h n m H hm

@[expose] def goodLengths : List ℕ := [1,2,3,5,7,8,11,15,17,23,26,31]

theorem refined_exponent_list {p r e : ℕ} (xs : List ℕ)
    (table : ∀ j : Fin goodLengths.length, p^goodLengths[j] < 10^15 →
      p^goodLengths[j]%4=1 → r∣goodLengths[j]+1 → goodLengths[j]∈xs)
    (ha : Allowed p e) (hg : e∈goodLengths) (hd : r∣e+1) : e∈xs := by
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hg
  exact table j ha.2.1 ha.2.2 hd

theorem refined_children {n m p T : ℕ} {s : Node} {ban : Bool} (H : Small n 3)
    (h : Realizes s n m) (hτ : n.divisors.card = T*m.divisors.card)
    (hb : ban=true → ¬3∣m) (hp : p.Prime) (hd : p∣m)
    (extra : ℕ → Prop) (hext : extra (m.factorization p))
    (children : ∀ e, Allowed p e → e ∈ goodLengths → extra e →
      Refined (s.extend p e) (T*(e+1)) ban) : False := by
  let e := m.factorization p
  have hm := (mul_ne_zero_iff.mp (h.value ▸ H.odd.pos.ne')).2
  obtain ⟨ha,_,_⟩ := split_at H h hp hd
  have he := extend_realizes H.odd.pos.ne' h hp hd
  have hpodd := H.odd.of_dvd_nat (hd.trans (h.value ▸ dvd_mul_left m _))
  have hp3 : 3 ≤ p := by have := hp.two_le; have := Nat.odd_iff.mp hpodd; omega
  have bound : e < 32 := by
    by_contra! le
    have := (Nat.pow_le_pow_left hp3 32).trans (Nat.pow_le_pow_right hp.pos le)
    exact ha.2.1.not_ge ((by decide +kernel : (10:ℕ)^15 ≤ 3^32).trans this)
  have hsplit : p^e * ordCompl[p] m = m := Nat.ordProj_mul_ordCompl_eq_self m p
  have hc := (Nat.coprime_ordCompl hp hm).pow_left e
  have ht : m.divisors.card = (e+1)*(ordCompl[p] m).divisors.card := by
    calc m.divisors.card = (p^e * ordCompl[p] m).divisors.card := congrArg (fun a : ℕ => a.divisors.card) hsplit.symm
      _ = _ := by rw [hc.card_divisors_mul,←sigma_zero_apply,sigma_zero_apply_prime_pow hp]
  have hlen : e+1∣n.divisors.card := hτ ▸ (ht ▸ dvd_mul_right _ _).trans (dvd_mul_left _ T)
  have table : ∀ j : Fin 32, 0<j.val →
      (∀ r : Fin 33, r.val.Prime → r.val∣j.val+1 → r.val≤3) →
      j.val∈goodLengths := by decide +kernel
  have hgood := table ⟨e,bound⟩ ha.1 (fun r hr hd => H.smooth _ hr (hd.trans hlen))
  apply children e ha hgood hext n _ H he
  · rw [hτ,ht,mul_assoc]
  · exact fun hban h3 => hb hban (h3.trans (Nat.ordCompl_dvd m p))

theorem refined_forced {s : Node} {T p c : ℕ} {ban : Bool} (hp : p.Prime)
    (hs : c ∣ s.divisorSum) (hc : c.Coprime 6) (hd : p ∣ c) (hnew : ¬p∣s.component)
    (children : ∀ e, Allowed p e → e ∈ goodLengths → Refined (s.extend p e) (T*(e+1)) ban) :
    Refined s T ban := by
  intro n m H h hτ hb
  have hn := hd.trans ((Nat.dvd_lcm_right _ _).trans (forced_dvd H h hs hc))
  rw [h.value] at hn
  exact refined_children H h hτ hb hp ((hp.dvd_mul.mp hn).resolve_left hnew) (fun _ => True)
    trivial (fun e ha hg _ => children e ha hg)

@[expose] def RootThree (p : ℕ) : Prop := ∀ n, Small n 3 → p.Prime → p∣n →
  3∣n.factorization p+1 → False

theorem root_three {p : ℕ} (children : ∀ e, Allowed p e → e∈goodLengths → 3∣e+1 →
    Refined (root.extend p e) (1*(e+1)) false) : RootThree p := by
  intro n H hp hd hlen
  exact refined_children H (root_realizes n) (T:=1) (by simp) (ban:=false) (by simp) hp hd
    (fun e => 3∣e+1) hlen children

theorem refined_three_cases {s : Node} {T : ℕ}
    (absent : Refined s T true)
    (children : ∀ e, Allowed 3 e → e ∈ goodLengths → Refined (s.extend 3 e) (T*(e+1)) false) :
    Refined s T false := by
  intro n m H h hτ hb
  by_cases hd : 3∣m
  · exact refined_children H h hτ hb (by decide : Nat.Prime 3) hd (fun _ => True) trivial
      (fun e ha hg _ => children e ha hg)
  · exact absent n m H h hτ (fun _ => hd)

/-- The factor of the assigned divisor sum left after cancellation must
divide the product of the residual cofactor and its divisor count. -/
theorem residual_requirement {n m T : ℕ} {s : Node} (H : Small n 3)
    (h : Realizes s n m) (hτ : n.divisors.card = T*m.divisors.card) :
    s.divisorSum / s.divisorSum.gcd (s.component*T) ∣ m*m.divisors.card := by
  have pos : 0<s.divisorSum := h.sigma ▸ sigma_pos 1 _ (mul_ne_zero_iff.mp (h.value ▸ H.odd.pos.ne')).1
  have hd : s.divisorSum ∣ (s.component*T)*(m*m.divisors.card) := by
    have hsig : s.divisorSum ∣ sigma 1 n := by
      rw [h.value,isMultiplicative_sigma.map_mul_of_coprime h.coprime,h.sigma]
      exact dvd_mul_right _ _
    have hdiv := hsig.trans H.harmonic.2
    rw [hτ,h.value] at hdiv
    convert hdiv using 1
    ring
  have g := Nat.dvd_gcd (Nat.dvd_mul_right s.divisorSum (m*m.divisors.card)) hd
  rw [Nat.gcd_mul_right] at g
  exact (Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left _ _) (Nat.gcd_pos_of_pos_left _ pos)).2 g

theorem refined_owed {s : Node} {T r b L : ℕ} {ban : Bool} (hr : r.Prime)
    (hd : r^b ∣ s.divisorSum / s.divisorSum.gcd (s.component*T))
    (absent : r=2 ∨ r∣s.component ∨ (r=3 ∧ ban=true))
    (hL : 0<L) (cut : 10^24 < s.component * L^((r-1)*b))
    (children : ∀ p, p.Prime → 3≤p → p<L → ¬p∣s.component → (ban=true → p≠3) →
      ∀ e, Allowed p e → e∈goodLengths → r∣e+1 → Refined (s.extend p e) (T*(e+1)) ban) :
    Refined s T ban := by
  intro n m H h hτ hb
  have hm := (mul_ne_zero_iff.mp (h.value ▸ H.odd.pos.ne')).2
  have hmd : m∣n := h.value ▸ dvd_mul_left _ _
  have hnot : ¬r∣m := by
    rcases absent with rfl | hD | ⟨rfl,hb'⟩
    · exact (H.odd.of_dvd_nat hmd).not_two_dvd_nat
    · exact fun hmr => hr.not_dvd_one (h.coprime.gcd_eq_one ▸ Nat.dvd_gcd hD hmr)
    · exact hb hb'
  have hrd := ((hr.coprime_iff_not_dvd.mpr hnot).pow_left b).dvd_of_dvd_mul_left
    (hd.trans (residual_requirement H h hτ))
  have hsize : m < L^((r-1)*b) := by
    by_contra! he
    exact cut.not_ge ((Nat.mul_le_mul_left s.component he).trans (h.value ▸ H.size))
  obtain ⟨p,pm,plt,plen⟩ := small_base_of_dvd_divisor_count (Nat.pos_of_ne_zero hm) hr hL hrd hsize
  have hp := Nat.prime_of_mem_primeFactors pm
  have pd := Nat.dvd_of_mem_primeFactors pm
  have oddp := H.odd.of_dvd_nat (pd.trans hmd)
  have p3 : 3≤p := by have := hp.two_le; have := Nat.odd_iff.mp oddp; omega
  have hD : ¬p∣s.component := fun ha => hp.not_dvd_one (h.coprime.gcd_eq_one ▸ Nat.dvd_gcd ha pd)
  exact refined_children H h hτ hb hp pd (fun e => r∣e+1) plen
    (children p hp p3 plt hD (fun f he => hb f (he ▸ pd)))

end OddPerfect.HarmonicChain
