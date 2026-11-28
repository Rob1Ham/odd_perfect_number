module

public import OddPerfect.IndexSieveExactRows
public import OddPerfect.IndexBound343
import OddPerfect.Abundance
import OddPerfect.Cuts
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect.IndexSieve

open ArithmeticFunction Finset

/-- A finite table or either of the uniform obstructions accounts for
every remaining candidate in a half-open interval. -/
def Covers (lo hi : ℕ) : Prop := ∀ i, lo≤ i → i < hi → Odd i → 3≤cardFactors i →
  105 ∣ i ∨ i.sqrt^2=i ∨ ∃ w : Row, w.exactValid ∧ w.index=i

theorem covers_append {lo mid hi : ℕ} (hleft : Covers lo mid) (hright : Covers mid hi) : Covers lo hi := by
  intro i h₁ h₂
  by_cases h : i<mid
  · exact hleft i h₁ h
  · exact hright i (by omega) h₂

/-- The kernel checks row validity and coverage separately. The existential
in the resulting theorem has no computational role. -/
theorem covers_of_table {lo hi : ℕ} (rows : List Row)
    (hrows : ∀ z : Fin rows.length, (rows.get z).exactValid)
    (hcoverage : ∀ j : Fin (hi-lo), let i := lo+(j:ℕ)
      Odd i → 3≤cardFactors i → 105 ∣ i ∨ i.sqrt^2=i ∨ ∃ z : Fin rows.length, (rows.get z).index=i) :
    Covers lo hi := by
  intro i hlo hhi ho hweight
  have hz : lo+(i-lo)=i := by omega
  have hc := hcoverage ⟨i-lo,by omega⟩
  simp only [hz] at hc
  rcases hc ho hweight with h|h|⟨z,h⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨_,hrows z,h⟩)

/-- Any covered interval beyond an established lower bound advances the
bound, up to the separate exponent-one threshold. -/
theorem euler_component_index_ge_of_cover {N q a m lo hi : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (hqm : ¬q ∣ m) (hform : N=q^a*m^2)
    (hlo : lo≤sigma 1 (m^2)/q^a) (hhi : hi≤22971) (hipos : 0<hi) (hcover : Covers lo hi) :
    hi*q^a < 2*m^2 ∧ hi≤sigma 1 (m^2)/q^a := by
  have hao : Odd a := Nat.odd_iff.mpr (by omega)
  have hqb : ¬q ∣ m^2 := fun h => hqm (hq.dvd_of_dvd_pow h)
  obtain ⟨i,_,hl,hr,_⟩ := exists_component_index hN hq hform hqb
  have hquot : sigma 1 (m^2)/q^a=i := by rw [hl,Nat.mul_div_cancel_left i (Nat.pow_pos hq.pos)]
  have hio : Odd i := by
    rcases component_index_parity_bound hN ho hq hao.pos hform hqb hl hr with h|h
    · exact h.2.1
    · have := Nat.even_iff.mp h.1; omega
  have hω := three_le_euler_index_total_prime_count hN ho hq ha4 hqm hform
  rw [hquot] at hlo hω ⊢
  have hbound : hi≤ i := by
    by_contra! hlt
    have ha : 1<a := by
      by_contra! h
      have h1 : a=1 := by omega
      have := euler_exponent_one_index_ge_22971 hN ho hq hqm (by simpa [h1] using hform)
      simp only [h1,pow_one] at hquot
      omega
    rcases hcover i hlo hlt hio hω with hd|heq|⟨w,hw,hwi⟩
    · have hid : i ∣ m^2 := (Nat.coprime_two_right.mpr hio).dvd_of_dvd_mul_left (hr ▸ dvd_mul_left _ _)
      exact not_dvd_105_of_odd_perfect hN ho (hd.trans (hid.trans (hform ▸ dvd_mul_left _ _)))
    · exact euler_index_not_square_of_exponent_gt_one hN ho hq hq4 ha4 ha hqm hform
        ⟨i.sqrt,hquot.trans (by simpa [pow_two] using heq.symm)⟩
    · exact excludes_of_exact_valid_row hN ho hq hq4 ha4 ha hqm hform hl hr hio w hw hwi.symm
  refine ⟨?_,hbound⟩
  calc hi*q^a < hi*sigma 1 (q^a) := Nat.mul_lt_mul_of_pos_left (self_lt_sigma_of_one_lt
          (one_lt_pow₀ hq.one_lt hao.pos.ne')) hipos
       _ ≤ sigma 1 (q^a)*i := by rw [Nat.mul_comm hi]; exact Nat.mul_le_mul_left _ hbound
       _ = _ := hr

end OddPerfect.IndexSieve
