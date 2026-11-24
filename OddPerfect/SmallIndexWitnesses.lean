module

public import OddPerfect.IndexResidueCertificates
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect

open ArithmeticFunction Finset

private structure FactorRow where
  p : ℕ
  r : ℕ
  k : ℕ
  u : ℕ
  v : ℕ

private def rows : List FactorRow := [⟨3,5,1,31,11⟩, ⟨5,3,2,13,11⟩, ⟨3,11,1,7,5⟩,
  ⟨3,13,1,61,30941⟩, ⟨3,17,1,307,88741⟩, ⟨3,19,1,127,151⟩, ⟨3,29,1,13,732541⟩,
  ⟨5,11,2,7,3221⟩, ⟨3,31,1,331,5⟩]

private def FactorRow.valid (x : FactorRow) : Prop :=
  x.p.Prime ∧ x.r.Prime ∧ Odd x.r ∧ x.p ≠ x.r ∧ x.p-1=2^x.k ∧
  (x.p=3 ∨ x.p=5) ∧ x.p^2*x.r<22971 ∧ x.u.Prime ∧ ¬x.u ∣ x.p ∧
  x.u ∣ (∑ j ∈ Finset.range 3, x.r^j) ∧ x.u%16 ≠ 1 ∧ x.v.Prime ∧ ¬x.v ∣ x.p ∧
  x.v ∣ (∑ j ∈ Finset.range 5, x.r^j) ∧ x.v%16 ≠ 1

private instance (x : FactorRow) : Decidable x.valid := by unfold FactorRow.valid; infer_instance

private theorem validate_rows : ∀ z : Fin rows.length, (rows.get z).valid := by
  intro z
  change Fin 9 at z
  fin_cases z
  · change (FactorRow.mk 3 5 1 31 11).valid
    norm_num [FactorRow.valid, Finset.sum_range_succ, Nat.odd_iff]
  · change (FactorRow.mk 5 3 2 13 11).valid
    norm_num [FactorRow.valid, Finset.sum_range_succ, Nat.odd_iff]
  · change (FactorRow.mk 3 11 1 7 5).valid
    norm_num [FactorRow.valid, Finset.sum_range_succ, Nat.odd_iff]
  · change (FactorRow.mk 3 13 1 61 30941).valid
    norm_num [FactorRow.valid, Finset.sum_range_succ, Nat.odd_iff]
  · change (FactorRow.mk 3 17 1 307 88741).valid
    norm_num [FactorRow.valid, Finset.sum_range_succ, Nat.odd_iff]
  · change (FactorRow.mk 3 19 1 127 151).valid
    norm_num [FactorRow.valid, Finset.sum_range_succ, Nat.odd_iff]
  · change (FactorRow.mk 3 29 1 13 732541).valid
    norm_num [FactorRow.valid, Finset.sum_range_succ, Nat.odd_iff]
  · change (FactorRow.mk 5 11 2 7 3221).valid
    norm_num [FactorRow.valid, Finset.sum_range_succ, Nat.odd_iff]
  · change (FactorRow.mk 3 31 1 331 5).valid
    norm_num [FactorRow.valid, Finset.sum_range_succ, Nat.odd_iff]

/-- Checked component factors at exponents two and four exclude the nine
listed Euler indices, including 99 and 117. -/
theorem euler_index_avoids_two_component_witnesses {N q a m i : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1)
    (hqm : ¬q ∣ m) (hform : N=q^a*m^2) (hl : sigma 1 (m^2)=q^a*i)
    (hr : sigma 1 (q^a)*i=2*m^2) : i ∉ ({45,75,99,117,153,171,261,275,279}:Finset ℕ) := by
  intro hi
  have bound : i<280 := by simp only [Finset.mem_insert, Finset.mem_singleton] at hi; omega
  have check : ∀ n : Fin 280, (n:ℕ) ∈ ({45,75,99,117,153,171,261,275,279}:Finset ℕ) →
      ∃ z : Fin rows.length, (n:ℕ) = (rows.get z).p^2*(rows.get z).r := by decide +kernel
  obtain ⟨z,hz⟩ := check ⟨i,bound⟩ hi
  let x := rows.get z
  change i=x.p^2*x.r at hz
  rw [hz] at hl hr
  obtain ⟨hp,hpr,hro,hne,hk,h35,hb,hu,hup,hud,hu16,hv,hvp,hvd,hv16⟩ := validate_rows z
  apply small_square_times_prime_excluded_of_component_factors hN ho hq hq4 ha4 hqm hform hp hpr hro hne hk hb hl hr
  intro e he
  have hcase : e=2 ∨ e=4 := by change e=2 ∨ e=4 ∨ e+1=x.p at he; change x.p=3 ∨ x.p=5 at h35; omega
  rcases hcase with rfl|rfl
  · exact ⟨x.u,hu,hup,by rwa [sigma_one_apply_prime_pow hpr],hu16⟩
  · exact ⟨x.v,hv,hvp,by rwa [sigma_one_apply_prime_pow hpr],hv16⟩

private theorem order_six_at_seven {p : ℕ} (hp : p=3 ∨ p=5) : Even (orderOf (p : ZMod 7)) := by
  have h6 : orderOf (p : ZMod 7) = 6 := by
    apply (orderOf_eq_iff (by decide : 0<6)).mpr
    constructor
    · rcases hp with rfl|rfl <;> decide +kernel
    · intro u hu hu0
      have check : ∀ v : Fin 6, 0<(v:ℕ) → (3 : ZMod 7)^(v:ℕ)≠1 ∧ (5 : ZMod 7)^(v:ℕ)≠1 := by decide +kernel
      rcases hp with rfl|rfl
      · exact (check ⟨u,hu⟩ hu0).1
      · exact (check ⟨u,hu⟩ hu0).2
  exact h6 ▸ (by decide : Even 6)

/-- A pure source at three or five rules out the four mixed indices with
seven listed here, including 63. -/
theorem euler_index_avoids_pure_sources_mod_seven {N q a m i : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1)
    (hqm : ¬q ∣ m) (hform : N=q^a*m^2) (hl : sigma 1 (m^2)=q^a*i)
    (hr : sigma 1 (q^a)*i=2*m^2) : i ∉ ({63,147,175,245}:Finset ℕ) := by
  intro hi
  have hdata : ∃ p j k l t : ℕ, (p=3 ∨ p=5) ∧ i=p^j*7^k ∧ l.Prime ∧ i=l*t^2 ∧
      (i.factorization p=1 ∨ i.factorization p=2) ∧ i<22971 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl
    · exact ⟨3,2,1,7,3,by decide +kernel⟩
    · exact ⟨3,1,2,3,7,by decide +kernel⟩
    · exact ⟨5,2,1,7,5,by decide +kernel⟩
    · exact ⟨5,1,2,5,7,by decide +kernel⟩
  obtain ⟨p,j,k,l,t,hp,hiF,hlp,hiS,hv,hb⟩ := hdata
  have hpp : p.Prime := by rcases hp with rfl|rfl <;> decide
  have hpo : Odd p := by rcases hp with rfl|rfl <;> decide
  have hm := (ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left _ _))).pos
  have hipos : 0 < i := by rw [hiF]; exact Nat.mul_pos (Nat.pow_pos hpp.pos) (Nat.pow_pos (by decide))
  have he := index_prime_return_valuation hpp hpo hq hm hipos hr
  have hut : 0 < 2*m.factorization p := by rcases hv with h|h <;> omega
  have hpure := pure_component_at_index_prime_of_even_order hpp (by decide : Nat.Prime 7) hq hm hiF hut (order_six_at_seven hp) hl
  exact small_prime_times_square_index_not_pure hN ho hq hq4 ha4 hqm hform hlp hiS hp hb hv hl hr hpure

end OddPerfect
