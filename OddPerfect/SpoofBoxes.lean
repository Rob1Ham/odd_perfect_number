module

public import OddPerfect.SpoofAbundancy
public import OddPerfect.AbundancyLimit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

public section

namespace OddPerfect.SpoofBox

open Finset

/-- Numerator/denominator pairs for comparisons without rational normalization. -/
structure Ratio where
  num : ℕ
  den : ℕ
deriving DecidableEq, Repr

@[expose] def Ratio.value (r : Ratio) : ℚ := (r.num:ℚ) / r.den

@[expose] def Ratio.geometric (b e : ℕ) : Ratio :=
  ⟨b^(e+1)-1, (b-1)*b^e⟩

@[expose] def Ratio.limit (b : ℕ) : Ratio := ⟨b,b-1⟩

theorem geometric_value {b : ℕ} (hb : 1 < b) (e : ℕ) :
    (Ratio.geometric b e).value = componentAbundancy b e := by
  have h := geom_sum_mul_add (b-1) (e+1)
  rw [Nat.sub_add_cancel hb.le] at h
  rw [componentAbundancy_eq (by omega : 0<b)]
  change ((b^(e+1)-1:ℕ):ℚ) / (((b-1)*b^e:ℕ):ℚ) = _
  rw [← h,Nat.add_sub_cancel]
  push_cast
  have hrat : (1:ℚ) < b := by exact_mod_cast hb
  have hpos : (0:ℚ) < b := zero_lt_one.trans hrat
  have hpred : (((b-1:ℕ):ℚ)) ≠ 0 := by exact_mod_cast (Nat.sub_pos_of_lt hb).ne'
  field_simp [hpred]

/-- Each zero upper endpoint indicates an unbounded coordinate. The special
slot has base and exponent one modulo four; ordinary slots have odd base
and positive even exponent. -/
structure Slot where
  special : Bool
  baseLo : ℕ
  baseHi : ℕ
  expLo : ℕ
  expHi : ℕ
deriving DecidableEq, Repr

@[expose] def Slot.stride (s : Slot) : ℕ := if s.special then 4 else 2
@[expose] def Slot.expResidue (s : Slot) : ℕ := if s.special then 1 else 0

structure Slot.Fits (s : Slot) (z : ℕ × ℕ) : Prop where
  base : 1 < z.1
  exp : 0 < z.2
  baseLo : s.baseLo ≤ z.1
  baseHi : s.baseHi = 0 ∨ z.1 ≤ s.baseHi
  expLo : s.expLo ≤ z.2
  expHi : s.expHi = 0 ∨ z.2 ≤ s.expHi
  baseResidue : z.1 % s.stride = 1
  expResidue : z.2 % s.stride = s.expResidue

@[expose] def Slot.lower (s : Slot) : Ratio :=
  if s.baseHi=0 then ⟨1,1⟩ else Ratio.geometric (max 2 s.baseHi) s.expLo

@[expose] def Slot.upper (s : Slot) : Ratio :=
  if s.expHi=0 then Ratio.limit (max 2 s.baseLo) else Ratio.geometric (max 2 s.baseLo) s.expHi

theorem Slot.lower_den_pos (s : Slot) : 0 < s.lower.den := by
  unfold lower
  split
  · decide
  · change 0 < (max 2 s.baseHi - 1) * (max 2 s.baseHi)^s.expLo
    exact Nat.mul_pos (by omega) (pow_pos (by omega) _)

theorem Slot.upper_den_pos (s : Slot) : 0 < s.upper.den := by
  unfold upper
  split
  · change 0 < max 2 s.baseLo-1
    omega
  · change 0 < (max 2 s.baseLo - 1) * (max 2 s.baseLo)^s.expHi
    exact Nat.mul_pos (by omega) (pow_pos (by omega) _)

theorem Slot.lower_le {s : Slot} {z : ℕ × ℕ} (h : s.Fits z) :
    s.lower.value ≤ componentAbundancy z.1 z.2 := by
  unfold lower
  split
  · simpa [Ratio.value] using one_le_componentAbundancy z.1 z.2
  · rename_i hn
    rw [geometric_value (by omega : 1 < max 2 s.baseHi)]
    exact (componentAbundancy_antitone h.base.le ((h.baseHi.resolve_left hn).trans (le_max_right ..)) _).trans
      ((componentAbundancy_strictMono h.base.le).monotone h.expLo)

theorem Slot.lower_lt {s : Slot} {z : ℕ × ℕ} (h : s.Fits z) (hu : s.baseHi=0) :
    s.lower.value < componentAbundancy z.1 z.2 := by
  simpa [lower,hu,Ratio.value,componentAbundancy] using
    (componentAbundancy_strictMono h.base.le h.exp)

theorem Slot.le_upper {s : Slot} {z : ℕ × ℕ} (h : s.Fits z) :
    componentAbundancy z.1 z.2 ≤ s.upper.value := by
  let b := max 2 s.baseLo
  have hb : 1 < b := by dsimp [b]; omega
  have hle : b ≤ z.1 := max_le h.base h.baseLo
  have ha := componentAbundancy_antitone hb.le hle z.2
  unfold upper
  split
  · change _ ≤ primeAbundancyLimit b
    have hlim := componentAbundancy_lt_limit hb z.2
    have hbcast : ((b-1:ℕ):ℚ) = (b:ℚ)-1 := by simp [Nat.cast_sub hb.le]
    exact ha.trans (by simpa [primeAbundancyLimit,hbcast] using hlim.le)
  · rename_i hn
    rw [geometric_value hb]
    exact ha.trans ((componentAbundancy_strictMono hb.le).monotone (h.expHi.resolve_left hn))

theorem Slot.lt_upper {s : Slot} {z : ℕ × ℕ} (h : s.Fits z) (hu : s.expHi=0) :
    componentAbundancy z.1 z.2 < s.upper.value := by
  let b := max 2 s.baseLo
  have hb : 1 < b := by dsimp [b]; omega
  have ha := componentAbundancy_antitone hb.le (show b ≤ z.1 from max_le h.base h.baseLo) z.2
  have hbcast : ((b-1:ℕ):ℚ) = (b:ℚ)-1 := by simp [Nat.cast_sub hb.le]
  rw [upper,ite_eq_left hu]
  change _ < (b:ℚ)/((b-1:ℕ):ℚ)
  rw [hbcast]
  exact ha.trans_lt (componentAbundancy_lt_limit hb z.2)

theorem Slot.lower_pos (s : Slot) : 0 < s.lower.value := by
  unfold lower
  split
  · norm_num [Ratio.value]
  · rw [geometric_value (by omega : 1 < max 2 s.baseHi)]
    exact zero_lt_one.trans_le (one_le_componentAbundancy ..)

@[expose] def productRatio {k : ℕ} (r : Fin k → Ratio) : Ratio :=
  ⟨∏ i, (r i).num, ∏ i, (r i).den⟩

theorem productRatio_value {k : ℕ} (r : Fin k → Ratio) :
    (productRatio r).value = ∏ i, (r i).value := by
  simp only [productRatio,Ratio.value,prod_div_distrib,Nat.cast_prod]

/-- A rectangle cannot balance if the target is outside its product of
intervals. Equality at a strict endpoint excludes the rectangle as well. -/
@[expose] def rejects {k : ℕ} (s : Fin k → Slot) : Bool :=
  let lo := productRatio (fun i => (s i).lower)
  let hi := productRatio (fun i => (s i).upper)
  decide (2*lo.den < lo.num ∨ hi.num < 2*hi.den ∨
    (lo.num = 2*lo.den ∧ ∃ i, (s i).baseHi=0) ∨
    (hi.num = 2*hi.den ∧ ∃ i, (s i).expHi=0))

theorem rejects_sound {k : ℕ} (s : Fin k → Slot) (x : Fin k → ℕ × ℕ)
    (hx : ∀ i, (s i).Fits (x i))
    (hb : formalSigma univ (fun i => (x i).1) (fun i => (x i).2) =
      2 * ∏ i, (x i).1^(x i).2) : rejects s = false := by
  let lo := productRatio (fun i => (s i).lower)
  let hi := productRatio (fun i => (s i).upper)
  let a := fun i => componentAbundancy (x i).1 (x i).2
  have htwo : ∏ i, a i = 2 := prod_componentAbundancy_eq_two univ _ _ (fun i _ => (hx i).base.le) hb
  have hlpos : (0:ℚ) < lo.den := by exact_mod_cast (prod_pos (s := univ) (fun i _ => (s i).lower_den_pos))
  have hupos : (0:ℚ) < hi.den := by exact_mod_cast (prod_pos (s := univ) (fun i _ => (s i).upper_den_pos))
  have hapos (i : Fin k) : 0 < a i := zero_lt_one.trans_le (one_le_componentAbundancy ..)
  have hLo : lo.value ≤ 2 := by
    rw [show lo.value = _ from productRatio_value _, ← htwo]
    exact prod_le_prod₀ (fun i _ => (s i).lower_pos.le) (fun i _ => Slot.lower_le (hx i))
  have hHi : 2 ≤ hi.value := by
    rw [show hi.value = _ from productRatio_value _, ← htwo]
    exact prod_le_prod₀ (fun i _ => (hapos i).le) (fun i _ => Slot.le_upper (hx i))
  have hl : lo.num ≤ 2*lo.den := by exact_mod_cast (div_le_iff₀ hlpos).mp hLo
  have hh : 2*hi.den ≤ hi.num := by exact_mod_cast (le_div_iff₀ hupos).mp hHi
  apply decide_eq_false
  rintro (hlt|hlt|⟨heq,i,hi0⟩|⟨heq,i,hi0⟩)
  · exact hl.not_gt hlt
  · exact hh.not_gt hlt
  · have hstrict : lo.value < 2 := by
      rw [show lo.value = _ from productRatio_value _, ← htwo]
      exact prod_lt_prod₀ (fun j _ => (s j).lower_pos) (fun j _ => Slot.lower_le (hx j))
        ⟨i,mem_univ _,Slot.lower_lt (hx i) hi0⟩
    have hlt : lo.num < 2*lo.den := by exact_mod_cast (div_lt_iff₀ hlpos).mp hstrict
    exact hlt.ne heq
  · have hstrict : 2 < hi.value := by
      rw [show hi.value = _ from productRatio_value _, ← htwo]
      exact prod_lt_prod₀ (fun j _ => hapos j) (fun j _ => Slot.le_upper (hx j))
        ⟨i,mem_univ _,Slot.lt_upper (hx i) hi0⟩
    have hlt : 2*hi.den < hi.num := by exact_mod_cast (lt_div_iff₀ hupos).mp hstrict
    exact hlt.ne' heq

end OddPerfect.SpoofBox
