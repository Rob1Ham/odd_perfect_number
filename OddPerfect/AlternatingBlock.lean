module

public import OddPerfect.Hirakawa
import Mathlib.Algebra.BigOperators.ModEq

public section

namespace OddPerfect
open Finset

/-- At odd prime length this is the value of the cyclotomic polynomial
of index twice that prime. -/
@[expose] def alternatingBlock (x s : ℕ) : ℕ := (x^s+1)/(x+1)

private theorem alternatingBlock_mul {x s : ℕ} (hs : Odd s) :
    alternatingBlock x s * (x+1) = x^s+1 := by
  apply Nat.div_mul_cancel
  simpa using hs.nat_add_dvd_pow_add_pow (x:=x) (y:=1)

theorem alternatingBlock_cast {x s : ℕ} (hs : Odd s) :
    (alternatingBlock x s : ℤ) = ∑ j ∈ range s, (-(x:ℤ))^j := by
  have h := congrArg (fun n : ℕ => (n:ℤ)) (alternatingBlock_mul (x:=x) hs)
  push_cast at h
  have hg := geom_sum_mul (-(x:ℤ)) s
  rw [hs.neg_pow] at hg
  apply mul_right_cancel₀ (by positivity : (x:ℤ)+1 ≠ 0)
  rw [h]
  nlinarith

private theorem alternatingBlock_one_mod_eight {x s : ℕ} (hx : x%8=1) (hs : Odd s) :
    alternatingBlock x s%8=1 := by
  have h8 : (x:ℤ) ≡ 1 [ZMOD 8] := by exact_mod_cast (show x ≡ 1 [MOD 8] from hx)
  have hsum := Int.ModEq.sum (s:=range s) (fun j _ => (h8.neg).pow j)
  rw [← alternatingBlock_cast hs,neg_one_geom_sum,ite_eq_right ((Nat.not_even_iff_odd.mpr hs))] at hsum
  exact_mod_cast hsum

private theorem common_prime_alternatingBlock {x s r : ℕ} (hs : Odd s) (hplus : r ∣ x+1)
    (hblock : r ∣ alternatingBlock x s) : r ∣ s := by
  have hzero : (x:ℤ)+1 ≡ 0 [ZMOD r] := by
    apply Int.modEq_zero_iff_dvd.mpr
    exact_mod_cast hplus
  have hx : -(x:ℤ) ≡ 1 [ZMOD r] := by
    have h := hzero.sub (Int.ModEq.refl (x:ℤ))
    simpa using h.symm
  have hsum := Int.ModEq.sum (s:=range s) (fun j _ => hx.pow j)
  rw [←alternatingBlock_cast hs] at hsum
  have hc0 : (alternatingBlock x s:ℤ) ≡ 0 [ZMOD r] := by
    apply Int.modEq_zero_iff_dvd.mpr
    exact_mod_cast hblock
  have hsd : (s:ℤ) ≡ 0 [ZMOD r] := by simpa using hsum.symm.trans hc0
  exact_mod_cast Int.modEq_zero_iff_dvd.mp hsd

/-- A nonsquare alternating geometric block gives a nonsquare half-sum as
soon as its only possible common prime can be excluded by size or residue. -/
theorem half_sum_not_square_of_alternatingBlock {x s : ℕ} (hx : x%8=1) (hs : s.Prime)
    (hso : Odd s) (hc : ¬IsSquare (alternatingBlock x s)) (hsep : s%8 ≠ 1 ∨ ¬s ∣ x+1) :
    ¬IsSquare ((x^s+1)/2) := by
  let C := alternatingBlock x s
  let H := (x+1)/2
  have hC8 : C%8=1 := alternatingBlock_one_mod_eight hx hso
  have hC0 : C ≠ 0 := by omega
  have hH0 : H ≠ 0 := by dsimp [H]; omega
  have hH : x+1=2*H := by dsimp [H]; omega
  have hprod : H*C=(x^s+1)/2 := by
    rw [←alternatingBlock_mul hso,hH,show alternatingBlock x s*(2*H)=2*(H*C) by dsimp [C]; ring,
      Nat.mul_div_cancel_left _ (by decide)]
  have hprime : ∃ p : ℕ, p.Prime ∧ Odd (C.factorization p) ∧ ¬p ∣ H := by
    rcases hsep with h8 | hnot
    · have hbad (w : ℕ) : C ≠ s*w^2 := by
        intro h
        have hodd := Nat.odd_iff.mp hso
        have hm := Nat.mod_lt w (by decide : 0<8)
        have hr : s%8=3 ∨ s%8=5 ∨ s%8=7 := by omega
        rw [h,pow_two,Nat.mul_mod s _ 8,Nat.mul_mod w w 8] at hC8
        rcases hr with hr | hr | hr <;> interval_cases (w%8) <;> simp_all
      obtain ⟨p,hp,hne,hv⟩ := exists_odd_valuation_away_of_nonsquare hc hbad
      refine ⟨p,hp,hv,fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hs).mp ?_)⟩
      apply common_prime_alternatingBlock hso (h.trans (hH ▸ dvd_mul_left H 2))
      exact (hp.dvd_iff_one_le_factorization hC0).mpr hv.pos
    · have hex : ∃ p : ℕ, p.Prime ∧ Odd (C.factorization p) := by
        by_contra h
        apply hc
        apply Nat.isSquare_iff_even_factorization.mpr
        intro p hp
        exact (Nat.even_or_odd _).resolve_right (fun hv => h ⟨p,hp,hv⟩)
      obtain ⟨p,hp,hv⟩ := hex
      refine ⟨p,hp,hv,fun h => ?_⟩
      have hd := h.trans (hH ▸ dvd_mul_left H 2)
      have hps := common_prime_alternatingBlock hso hd ((hp.dvd_iff_one_le_factorization hC0).mpr hv.pos)
      exact hnot (((Nat.prime_dvd_prime_iff_eq hp hs).mp hps) ▸ hd)
  obtain ⟨p,hp,hv,hn⟩ := hprime
  intro hsq
  rw [←hprod] at hsq
  have he := Nat.isSquare_iff_even_factorization.mp hsq p hp
  rw [Nat.factorization_mul hH0 hC0,Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd hn,zero_add] at he
  exact (Nat.not_even_iff_odd.mpr hv) he

/-- A scaled square root strictly within one unit of an odd integer cannot
itself be an even integer. The strict interval is checked using only squares. -/
theorem not_square_of_scaled_interval {n : ℕ} {P D : ℤ} (hP : 0<P) (hD : 0<D) (hPo : Odd P) (hDe : Even D)
    (hlo : (P-1)^2 < D^2*(n:ℤ)) (hhi : D^2*(n:ℤ) < (P+1)^2) : ¬IsSquare n := by
  rintro ⟨w,hw⟩
  have he : D^2*(n:ℤ)=(D*(w:ℤ))^2 := by rw [hw]; push_cast; ring
  rw [he] at hlo hhi
  have hzero : 0 ≤ D*(w:ℤ) := by positivity
  have hnot : D*(w:ℤ) ≠ P := by
    intro h
    exact (Int.not_even_iff_odd.mpr hPo) (h ▸ hDe.mul_right (w:ℤ))
  rcases lt_or_gt_of_ne hnot with h | h
  · apply hlo.not_ge
    exact pow_le_pow_left₀ hzero (by omega) 2
  · apply hhi.not_ge
    exact pow_le_pow_left₀ (by omega) (by omega) 2

end OddPerfect
