module

public import OddPerfect.IndexSieveCore
public import OddPerfect.Hirakawa
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- A prime repunit at a prime base has prime length. -/
theorem prime_length_of_prime_sigma {p e : ℕ} (hp : p.Prime) (he : 0<e)
    (hprime : (sigma 1 (p^e)).Prime) : (e+1).Prime := by
  obtain ⟨l,hl,hd⟩ := Nat.exists_prime_and_dvd (by omega : e+1 ≠ 1)
  suffices e+1=l by simpa [this] using hl
  have hdiv := sigma_dvd_of_length_dvd hp hl.pos hd
  have mono : StrictMono (fun n : ℕ => ∑ j ∈ Finset.range n, p^j) := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [Finset.sum_range_succ]
    have := Nat.pow_pos (n:=n) hp.pos
    omega
  have hlarge := mono hl.one_lt
  rw [sigma_one_apply_prime_pow hp,show l-1+1=l by have := hl.pos; omega] at hdiv
  rcases (Nat.dvd_prime hprime).mp hdiv with h|h
  · simp only [Finset.sum_range_one,pow_zero] at hlarge
    omega
  · rw [sigma_one_apply_prime_pow hp] at h
    exact (mono.injective h).symm

/-- An odd residue for the exact component index identifies the Euler
component and its square cofactor. -/
theorem euler_form_of_odd_component_index {N q a b i : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (ha : 0<a) (hform : N=q^a*b) (hqb : ¬q ∣ b)
    (hl : sigma 1 b=q^a*i) (hr : sigma 1 (q^a)*i=2*b) (hi : Odd i) :
    ∃ m : ℕ, q%4=1 ∧ a%4=1 ∧ ¬q ∣ m ∧ b=m^2 := by
  have hao : Odd a := by
    rcases component_index_parity_bound hN ho hq ha hform hqb hl hr with h|h
    · exact h.1
    · have := Nat.odd_iff.mp hi; have := h.2.1; omega
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left _ _)
  have hval : N.factorization q=a := by
    rw [hform,Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) hbo.pos.ne',Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hqb,hq.factorization_pow,Finsupp.single_eq_same,add_zero]
  obtain ⟨s,_,hs4,hA4,hother⟩ := euler_exponents ho hN
  have hqs : q=s := by
    by_contra h
    have := Nat.even_iff.mp (hother q h); have := Nat.odd_iff.mp hao; omega
  subst s
  have hsquare : IsSquare b := by
    rw [← Nat.ordCompl_pow_mul_of_not_dvd a hq hqb,← hform]
    apply Nat.isSquare_iff_even_factorization.mpr
    intro r _
    rw [Nat.factorization_ordCompl]
    rcases eq_or_ne r q with rfl|h
    · simp
    · rw [Finsupp.erase_ne h]; exact hother r h
  obtain ⟨m,hm⟩ := hsquare
  rw [← pow_two] at hm
  exact ⟨m,hs4,hval ▸ hA4,fun hd => hqb (hm ▸ dvd_pow hd (by decide : 2≠0)),hm⟩

/-- An even prime-power index forces Euler exponent one and identifies its
Euler prime with the divisor sum of that index. -/
theorem even_prime_power_index_eq_selected_sigma {N q a b i p u : ℕ} (hN : N.Perfect)
    (ho : Odd N) (hq : q.Prime) (ha : 0<a) (hform : N=q^a*b) (hqb : ¬q ∣ b)
    (hl : sigma 1 b=q^a*i) (hr : sigma 1 (q^a)*i=2*b)
    (hp : p.Prime) (hu : 0<u) (hi : i=p^(2*u)) : a=1 ∧ sigma 1 (p^(2*u))=q := by
  subst i
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left _ _)
  have hp2 : p≠2 := by
    rintro rfl
    have h4 : 4 ∣ 2*b := hr ▸ (pow_dvd_pow 2 (by omega : 2 ≤ 2*u)).trans (dvd_mul_left _ _)
    have := hbo.not_two_dvd_nat; omega
  have hpo := hp.odd_of_ne_two hp2
  obtain ⟨m,hq4,ha4,hqm,rfl⟩ := euler_form_of_odd_component_index hN ho hq ha hform hqb hl hr hpo.pow
  have ha1 : a=1 := by
    by_contra h
    apply euler_index_not_square_of_exponent_gt_one hN ho hq hq4 ha4 (by omega) hqm hform
    refine ⟨p^u,?_⟩
    rw [hl,Nat.mul_div_cancel_left _ (Nat.pow_pos hq.pos),show 2*u=u+u by omega,pow_add]
  subst a
  simp only [pow_one] at hl hr
  have hm : 0<m := by by_contra! h; simp [show m=0 by omega] at hbo
  exact ⟨rfl,(prime_power_index_data_at_one hq hm hp hpo (by omega : 0<2*u) hl hr).2⟩

/-- Chen–Chen 2014, Theorem 1.1 in quotient form: if an index is a positive
even power of a prime, its divisor sum and its exponent plus one are prime. -/
theorem chen_chen_even_prime_power_index {N q a p u : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (ha : 0<a) (hd : q^a ∣ N) (hex : ¬q^(a+1) ∣ N)
    (hp : p.Prime) (hu : 0<u) (hi : sigma 1 (N/q^a)/q^a=p^(2*u)) :
    (sigma 1 (p^(2*u))).Prime ∧ (2*u+1).Prime := by
  obtain ⟨b,hb⟩ := hd
  have hqb : ¬q ∣ b := by intro h; apply hex; rw [hb,pow_succ]; exact Nat.mul_dvd_mul_left (q^a) h
  obtain ⟨i,_,hl,hr,_⟩ := exists_component_index hN hq hb hqb
  rw [hb,Nat.mul_div_cancel_left _ (Nat.pow_pos hq.pos),hl,Nat.mul_div_cancel_left _ (Nat.pow_pos hq.pos)] at hi
  have hval := (even_prime_power_index_eq_selected_sigma hN ho hq ha hb hqb hl hr hp hu hi).2
  have hprime : (sigma 1 (p^(2*u))).Prime := hval ▸ hq
  exact ⟨hprime,prime_length_of_prime_sigma hp (by omega) hprime⟩

end OddPerfect
