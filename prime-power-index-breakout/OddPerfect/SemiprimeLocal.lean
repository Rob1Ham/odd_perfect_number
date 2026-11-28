module

public import OddPerfect.IndexWeight
public import OddPerfect.ReciprocalValuation
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- An Euler length with at most six divisors has odd part one, an odd prime,
or the square of an odd prime. -/
theorem euler_length_cases_of_divisor_count_le_six {a : ℕ} (ha4 : a%4=1)
    (hdiv : (a+1).divisors.card ≤ 6) : a+1 = 2 ∨ ∃ l k : ℕ, l.Prime ∧ Odd l ∧
      (k=1 ∨ k=2) ∧ a+1 = 2*l^k := by
  obtain ⟨u, hu⟩ : 2 ∣ a+1 := by omega
  have huo : Odd u := Nat.odd_iff.mpr (by omega)
  rcases eq_or_ne u 1 with rfl | hu1
  · exact Or.inl (by omega)
  have hmul := Nat.Coprime.card_divisors_mul (Nat.coprime_two_right.mpr huo).symm
  rw [← hu, show (2:ℕ).divisors.card = 2 by decide] at hmul
  have hpow := two_pow_prime_count_le_divisor_count huo.pos.ne'
  have hcard : u.primeFactors.card ≤ 1 := by
    by_contra! h
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ u.primeFactors.card)
    norm_num at this
    omega
  obtain ⟨l, hl, hd⟩ := Nat.exists_prime_and_dvd hu1
  have hmem := Nat.mem_primeFactors.mpr ⟨hl, hd, huo.pos.ne'⟩
  have hsing : u.primeFactors = {l} := by
    apply Finset.Subset.antisymm
    · intro p hp
      exact Finset.mem_singleton.mpr ((Finset.card_le_one.mp hcard) _ hp _ hmem)
    · exact Finset.singleton_subset_iff.mpr hmem
  have hprod := Nat.prod_primeFactors_pow_factorization huo.pos.ne'
  rw [hsing, Finset.prod_singleton] at hprod
  have hnum := Nat.card_divisors huo.pos.ne'
  rw [hsing, Finset.prod_singleton] at hnum
  have hpos := (hl.dvd_iff_one_le_factorization huo.pos.ne').mp hd
  exact Or.inr ⟨l, u.factorization l, hl, huo.of_dvd_nat hd, by omega, hu.trans (congrArg (2*·) hprod)⟩

private theorem pure_square_order_data {p q a β : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hout : sigma 1 (p^2)=q^β) (hback : p ∣ sigma 1 (q^a)) :
    Odd β ∧ orderOf (q : ZMod p) ∣ β ∧ orderOf (q : ZMod p) ∣ a+1 ∧ orderOf (q : ZMod p) ∣ p-1 := by
  have hs : sigma 1 (p^2) = p^2+p+1 := by
    rw [sigma_one_apply_prime_pow hp]
    simp [Finset.sum_range_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hβo : Odd β := by
    rcases Nat.even_or_odd β with ⟨j,hj⟩ | h
    · have heq : p^2+p+1 = (q^j)^2 := by rw [← hs, hout, hj, pow_add, pow_two]
      by_cases hle : q^j ≤ p
      · have hh := Nat.pow_le_pow_left hle 2
        nlinarith
      · have hh := Nat.pow_le_pow_left (by omega : p+1 ≤ q^j) 2
        have := hp.one_lt
        nlinarith
    · exact h
  let : Fact p.Prime := ⟨hp⟩
  have hpow : (q : ZMod p)^β = 1 := by rw [← Nat.cast_pow, ← hout, hs]; simp
  have hne : (q : ZMod p) ≠ 0 := by
    intro h; rw [h, zero_pow hβo.pos.ne'] at hpow; exact zero_ne_one hpow
  refine ⟨hβo, orderOf_dvd_of_pow_eq_one hpow, ?_, ZMod.orderOf_dvd_card_sub_one hne⟩
  by_cases h : (q : ZMod p) = 1
  · simp [h]
  · rw [sigma_one_apply, dvd_sum_divisors_prime_pow_iff hq hp] at hback
    simpa [h] using hback

/-- If the only odd prime in the Euler length is the pure square source
itself, the selected base must be one modulo that source. -/
theorem selected_modEq_one_at_length_prime {l q a k β : ℕ} (hl : l.Prime)
    (hq : q.Prime) (hout : sigma 1 (l^2)=q^β) (hback : l ∣ sigma 1 (q^a))
    (hlen : a+1=2*l^k) : q ≡ 1 [MOD l] := by
  obtain ⟨hβo, hβ, hL, hc⟩ := pure_square_order_data hl hq hout hback
  let o := orderOf (q : ZMod l)
  have hoc : o.Coprime l := (hl.coprime_iff_not_dvd.mpr (fun h => by
    have := Nat.le_of_dvd (by have := hl.one_lt; omega : 0 < l-1) (h.trans hc)
    have := hl.one_lt
    omega)).symm
  rw [hlen] at hL
  have ho2 := (hoc.pow_right k).dvd_of_dvd_mul_right hL
  have h1 : o = 1 := by
    have := Nat.le_of_dvd (by decide : 0 < 2) ho2
    have := Nat.odd_iff.mp (hβo.of_dvd_nat hβ)
    change o % 2 = 1 at this
    omega
  exact (ZMod.natCast_eq_natCast_iff q 1 l).mp (by simpa using orderOf_eq_one_iff.mp h1)

/-- A different pure square source with one or more returning factors forces
the odd length prime into both its outgoing exponent and its predecessor. -/
theorem length_prime_dvd_exponent_and_pred {p q a l k β : ℕ} (hp : p.Prime) (hpo : Odd p)
    (hq : q.Prime) (hl : l.Prime) (hpl : p ≠ l) (hout : sigma 1 (p^2)=q^β)
    (hback : p ∣ sigma 1 (q^a)) (hlen : a+1=2*l^k) : l ∣ β ∧ l ∣ p-1 := by
  obtain ⟨hβo, hβ, hL, hpred⟩ := pure_square_order_data hp hq hout hback
  let o := orderOf (q : ZMod p)
  have ho : Odd o := hβo.of_dvd_nat hβ
  have hon : o ≠ 1 := by
    intro h
    have hqone : q ≡ 1 [MOD p] :=
      (ZMod.natCast_eq_natCast_iff q 1 p).mp (by simpa using orderOf_eq_one_iff.mp h)
    have hpL := ((sigma_modEq_of_one hq hqone a).dvd_iff dvd_rfl).mp hback
    rw [hlen] at hpL
    exact hpl ((Nat.prime_dvd_prime_iff_eq hp hl).mp (hp.dvd_of_dvd_pow
      ((Nat.coprime_two_right.mpr hpo).dvd_of_dvd_mul_left hpL)))
  rw [hlen] at hL
  have hopow := (Nat.coprime_two_right.mpr ho).dvd_of_dvd_mul_left hL
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hl).mp hopow
  have hj0 : j ≠ 0 := by rintro rfl; simp at hj; omega
  have hld : l ∣ o := hj ▸ dvd_pow_self _ hj0
  exact ⟨hld.trans hβ, hld.trans hpred⟩

/-- When a pure square source away from the odd length prime returns, that
length prime excludes a selected base which is one modulo itself. -/
theorem selected_not_modEq_one_of_other_pure_square {p q a l k β : ℕ} (hp : p.Prime) (hpo : Odd p)
    (hq : q.Prime) (hl : l.Prime) (hlo : Odd l) (hpl : p ≠ l) (hout : sigma 1 (p^2)=q^β)
    (hback : p ∣ sigma 1 (q^a)) (hlen : a+1=2*l^k) : ¬ q ≡ 1 [MOD l] := by
  have hc := (length_prime_dvd_exponent_and_pred hp hpo hq hl hpl hout hback hlen).2
  intro hq1
  have hp1 := ((Nat.modEq_iff_dvd' hp.one_lt.le).mpr hc).symm
  have hs := sigma_modEq_of_one hp hp1 2
  rw [hout] at hs
  have h3 := hs.symm.trans (by simpa using hq1.pow β : q^β ≡ 1 [MOD l])
  have hd : l ∣ 3-1 := (Nat.modEq_iff_dvd' (by decide : 1 ≤ 3)).mp h3.symm
  have := Nat.le_of_dvd (by decide : 0 < 3-1) hd
  have := hl.two_le
  have := Nat.odd_iff.mp hlo
  omega

end OddPerfect
