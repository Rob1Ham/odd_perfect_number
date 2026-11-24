module

public import OddPerfect.QuasiFactors
public import Mathlib.Data.Nat.Log

public section

namespace OddPerfect

open Finset

/-- A geometric sum is one modulo its base. Thus the contribution of a
single component to formal abundancy is already in lowest terms. -/
theorem coprime_power_geometric_sum (b e : ℕ) :
    (b ^ e).Coprime (∑ j ∈ range (e+1), b^j) := by
  apply Nat.Coprime.pow_left
  rw [sum_range_succ']
  simp_rw [pow_succ, ← sum_mul]
  simp

/-- If a prefix with formal sum U and twice its value V can be completed
with a single component, that component's value and its geometric sum are forced. -/
theorem last_component_reduced {U V b e : ℕ} (hU : 0 < U) (hb : 1 < b)
    (h : U * (∑ j ∈ range (e+1), b^j) = V * b^e) :
    U / U.gcd V = b^e ∧ V / U.gcd V = ∑ j ∈ range (e+1), b^j := by
  let S := ∑ j ∈ range (e+1), b^j
  let P := b^e
  have hc : P.Coprime S := coprime_power_geometric_sum b e
  have hpos : 0 < P := pow_pos hb.le _
  have hdiv : P ∣ U := hc.dvd_of_dvd_mul_right (h.symm ▸ dvd_mul_left P V)
  obtain ⟨g, hg⟩ := hdiv
  have hu : U = g*P := hg.trans (Nat.mul_comm _ _)
  have hgpos : 0 < g := by by_contra! hh; simp [Nat.eq_zero_of_le_zero hh] at hu; omega
  have hv : V = g*S := by
    apply (Nat.mul_right_cancel hpos)
    calc V * P = U * S := h.symm
      _ = (g * S) * P := by rw [hu]; ring
  have hred : U.gcd V = g := by rw [hu,hv,Nat.gcd_mul_left,hc.gcd_eq_one,mul_one]
  rw [hred, hu, hv, Nat.mul_div_cancel_left _ hgpos, Nat.mul_div_cancel_left _ hgpos]
  exact ⟨rfl,rfl⟩

/-- The base and exponent of the last slot are determined by the reduced
numerator and denominator. Exponents and bases can be recovered without factoring. -/
@[expose] def lastSpoofComponent (U V : ℕ) : ℕ × ℕ :=
  let P := U / U.gcd V
  let S := V / U.gcd V
  let b := (P-1)/(S-P) + 1
  (b, Nat.log b P)

theorem lastSpoofComponent_eq {U V b e : ℕ} (hU : 0 < U) (hb : 1 < b) (he : 0 < e)
    (h : U * (∑ j ∈ range (e+1), b^j) = V * b^e) :
    lastSpoofComponent U V = (b,e) := by
  obtain ⟨hP, hS⟩ := last_component_reduced hU hb h
  have ht : 0 < ∑ j ∈ range e, b^j := sum_pos' (by intros; omega)
    ⟨0, mem_range.mpr he, by simp⟩
  have hgeom := geom_sum_mul_add (b-1) e
  rw [Nat.sub_add_cancel hb.le] at hgeom
  have hbase : (b^e-1)/((∑ j ∈ range (e+1), b^j)-b^e)+1 = b := by
    rw [sum_range_succ, Nat.add_sub_cancel, ← hgeom, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ ht,
      Nat.sub_add_cancel hb.le]
  simp only [lastSpoofComponent, hP, hS, hbase, Nat.log_pow hb]

/-- No two different positive components can be joined to the same exact prefix. -/
theorem last_spoof_component_unique {U V b e c a : ℕ} (hU : 0 < U)
    (hb : 1 < b) (hc : 1 < c) (he : 0 < e) (ha : 0 < a)
    (h : U * (∑ j ∈ range (e+1), b^j) = V * b^e)
    (h' : U * (∑ j ∈ range (a+1), c^j) = V * c^a) :
    (b,e) = (c,a) :=
  (lastSpoofComponent_eq hU hb he h).symm.trans (lastSpoofComponent_eq hU hc ha h')

/-- The four ordinary squared components of Descartes's example determine
the remaining component uniquely. -/
theorem descartes_last_component : lastSpoofComponent 18035199 (2*9018009) = (22021,1) := by
  decide +kernel

end OddPerfect
