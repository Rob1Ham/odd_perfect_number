module

public import OddPerfect.PadicPadeExactSqrtTwoRatio
public import OddPerfect.PellMatiyasevicAndFirstBlockReciprocity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Symbolic All-Order Pell–Padé Contraction (`OddPerfect.PellSymbolicAllOrderPadeContraction`)

Collapses the infinite tower of Pell–Padé convergent orders symbolically (`∀ m ≤ u`) by linking
the leading-coefficient sequence `(padeLeadA u, padeLeadB u)` to odd powers of `silverUnit` in
`ℤ√2` and proving the unconditional `m ≤ u` ratio monotonicity and contraction bounds:

1. `padeLeadPair_eq_silverUnit_odd_pow_and_pell_norm`:
   Proves `StrictMono padeLeadA`, `StrictMono padeLeadB`, `1 ≤ padeLeadA u`, `1 ≤ padeLeadB u`,
   the Pell norm identity `2 * padeLeadA u ^ 2 - padeLeadB u ^ 2 = 1`, the exact `ℤ√2`
   identification `(silverUnit ^ (2 * u + 1)).re = padeLeadB u` and `.im = padeLeadA u`, and the
   symbolic all-order ratio bounds `padeLeadB m * padeLeadB (k + 1) ≤ padeLeadB (m + 1) * padeLeadB k`
   and `(padeLeadB m) ^ (k - m) * padeLeadB k ≤ padeLeadB m * (padeLeadB (m + 1)) ^ (k - m)`
   for all `m ≤ k`.
2. `padeSeq_symbolic_all_order_contraction`:
   For `3 ≤ p` and `1 ≤ u`, proves `padeSeqA u p < padeLeadA u * (p : ℤ) ^ u`,
   `padeSeqB u p < padeLeadB u * (p : ℤ) ^ u`, and the symbolic all-order contraction
   `(padeLeadB m) ^ (u - m) * padeSeqB u p < padeLeadB m * (padeLeadB (m + 1)) ^ (u - m) * (p : ℤ) ^ u`
   for all `m ≤ u`.
3. `even_prime_power_symbolic_all_order_and_exact_lead_profile`:
   Unconditional global odd-perfect-number wrapper on `componentIndex N r₀ = p ^ j` (`Even j`)
   establishing `(p : ℤ) * k_pade < padeLeadB u`, `140 * ((p : ℤ) - 1) * k_pade < 99 * padeLeadB u`,
   `p * k_pade.natAbs < (padeLeadB u).natAbs`, and the symbolic all-order tower bound
   `(padeLeadB m).natAbs ^ (u - m) * (p * k_pade.natAbs) < (padeLeadB m).natAbs * (padeLeadB (m + 1)).natAbs ^ (u - m)`
   for every `m ≤ u`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma odd_prime_ge_three_symbolic {p : ℕ} (hp : p.Prime) (hpo : Odd p) : 3 ≤ p := by
  have h2 : 2 ≤ p := hp.two_le
  rcases eq_or_lt_of_le h2 with rfl | hlt
  · exact absurd hpo (by decide)
  · exact hlt

private lemma padeSeq_le_padeLead_mul_pow_aux {p : ℕ} (hp3 : 3 ≤ p) (u : ℕ) :
    padeSeqA u p ≤ padeLeadA u * (p : ℤ) ^ u ∧
    padeSeqB u p ≤ padeLeadB u * (p : ℤ) ^ u := by
  induction u with
  | zero =>
      simp
  | succ u ih =>
      rcases ih with ⟨iha, ihb⟩
      obtain ⟨_, _⟩ := padeSeq_one_le hp3 u
      have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
      have hpow_nn : (0 : ℤ) ≤ (p : ℤ) ^ u := by positivity
      have ha_step : padeSeqA (u + 1) p ≤ padeLeadA (u + 1) * (p : ℤ) ^ (u + 1) := by
        calc
          padeSeqA (u + 1) p
              = (3 * (p : ℤ) - 4) * padeSeqA u p + 2 * ((p : ℤ) - 2) * padeSeqB u p :=
                  padeSeqA_succ u p
          _ ≤ 3 * (p : ℤ) * padeSeqA u p + 2 * (p : ℤ) * padeSeqB u p := by nlinarith
          _ ≤ 3 * (p : ℤ) * (padeLeadA u * (p : ℤ) ^ u) +
                2 * (p : ℤ) * (padeLeadB u * (p : ℤ) ^ u) := by
              have h1 := mul_le_mul_of_nonneg_left iha (by linarith : 0 ≤ 3 * (p : ℤ))
              have h2 := mul_le_mul_of_nonneg_left ihb (by linarith : 0 ≤ 2 * (p : ℤ))
              linarith
          _ = (3 * padeLeadA u + 2 * padeLeadB u) * ((p : ℤ) ^ u * (p : ℤ)) := by ring
          _ = padeLeadA (u + 1) * (p : ℤ) ^ (u + 1) := by rw [← pow_succ, padeLeadA_succ]
      have hb_step : padeSeqB (u + 1) p ≤ padeLeadB (u + 1) * (p : ℤ) ^ (u + 1) := by
        calc
          padeSeqB (u + 1) p
              = 4 * ((p : ℤ) - 1) * padeSeqA u p + (3 * (p : ℤ) - 4) * padeSeqB u p :=
                  padeSeqB_succ u p
          _ ≤ 4 * (p : ℤ) * padeSeqA u p + 3 * (p : ℤ) * padeSeqB u p := by nlinarith
          _ ≤ 4 * (p : ℤ) * (padeLeadA u * (p : ℤ) ^ u) +
                3 * (p : ℤ) * (padeLeadB u * (p : ℤ) ^ u) := by
              have h1 := mul_le_mul_of_nonneg_left iha (by linarith : 0 ≤ 4 * (p : ℤ))
              have h2 := mul_le_mul_of_nonneg_left ihb (by linarith : 0 ≤ 3 * (p : ℤ))
              linarith
          _ = (4 * padeLeadA u + 3 * padeLeadB u) * ((p : ℤ) ^ u * (p : ℤ)) := by ring
          _ = padeLeadB (u + 1) * (p : ℤ) ^ (u + 1) := by rw [← pow_succ, padeLeadB_succ]
      exact ⟨ha_step, hb_step⟩

/-- Links `(padeLeadA u, padeLeadB u)` to odd powers of `silverUnit = 1 + √2` in `ℤ√2`,
establishes `2 * padeLeadA u ^ 2 - padeLeadB u ^ 2 = 1` and strict monotonicity, and proves the
symbolic all-order ratio bounds for all `m ≤ k`. -/
theorem padeLeadPair_eq_silverUnit_odd_pow_and_pell_norm :
    StrictMono padeLeadA ∧
    StrictMono padeLeadB ∧
    (∀ u : ℕ,
      1 ≤ padeLeadA u ∧
      1 ≤ padeLeadB u ∧
      2 * padeLeadA u ^ 2 - padeLeadB u ^ 2 = 1 ∧
      ((silverUnit ^ (2 * u + 1) : (ℤ√2)ˣ) : ℤ√2).re = padeLeadB u ∧
      ((silverUnit ^ (2 * u + 1) : (ℤ√2)ˣ) : ℤ√2).im = padeLeadA u) ∧
    (∀ m k : ℕ, m ≤ k →
      padeLeadB m * padeLeadB (k + 1) ≤ padeLeadB (m + 1) * padeLeadB k ∧
      (padeLeadB m) ^ (k - m) * padeLeadB k ≤ padeLeadB m * (padeLeadB (m + 1)) ^ (k - m)) := by
  have hge : ∀ u : ℕ, 1 ≤ padeLeadA u ∧ 1 ≤ padeLeadB u := by
    intro u
    induction u with
    | zero =>
        simp
    | succ u ih =>
        rcases ih with ⟨ha, hb⟩
        rw [padeLeadA_succ, padeLeadB_succ]
        omega
  have hmonoA : StrictMono padeLeadA :=
    strictMono_nat_of_lt_succ fun u => by
      have ⟨ha, hb⟩ := hge u
      rw [padeLeadA_succ]
      omega
  have hmonoB : StrictMono padeLeadB :=
    strictMono_nat_of_lt_succ fun u => by
      have ⟨ha, hb⟩ := hge u
      rw [padeLeadB_succ]
      omega
  have hpell : ∀ u : ℕ, 2 * padeLeadA u ^ 2 - padeLeadB u ^ 2 = 1 := by
    intro u
    induction u with
    | zero =>
        norm_num
    | succ u ih =>
        rw [padeLeadA_succ, padeLeadB_succ]
        have hid :
            2 * (3 * padeLeadA u + 2 * padeLeadB u) ^ 2 -
              (4 * padeLeadA u + 3 * padeLeadB u) ^ 2 =
                2 * padeLeadA u ^ 2 - padeLeadB u ^ 2 := by
          ring
        linarith
  have hsilver :
      ∀ u : ℕ,
        ((silverUnit ^ (2 * u + 1) : (ℤ√2)ˣ) : ℤ√2).re = padeLeadB u ∧
        ((silverUnit ^ (2 * u + 1) : (ℤ√2)ˣ) : ℤ√2).im = padeLeadA u := by
    intro u
    induction u with
    | zero =>
        simp [silverUnit_val]
    | succ u ih =>
        rcases ih with ⟨ih_re, ih_im⟩
        have hsq : ((silverUnit ^ 2 : (ℤ√2)ˣ) : ℤ√2) = ⟨3, 2⟩ := by
          ext <;> simp [silverUnit_val, pow_two]
        have hmul :
            ((silverUnit ^ (2 * (u + 1) + 1) : (ℤ√2)ˣ) : ℤ√2) =
              ((silverUnit ^ (2 * u + 1) : (ℤ√2)ˣ) : ℤ√2) * ⟨3, 2⟩ := by
          calc
            ((silverUnit ^ (2 * (u + 1) + 1) : (ℤ√2)ˣ) : ℤ√2)
                = ((silverUnit ^ ((2 * u + 1) + 2) : (ℤ√2)ˣ) : ℤ√2) := by ring_nf
            _ = (((silverUnit ^ (2 * u + 1) * silverUnit ^ 2 : (ℤ√2)ˣ) : ℤ√2)) := by
                rw [pow_add]
            _ = ((silverUnit ^ (2 * u + 1) : (ℤ√2)ˣ) : ℤ√2) *
                  ((silverUnit ^ 2 : (ℤ√2)ˣ) : ℤ√2) := by
                simp
            _ = ((silverUnit ^ (2 * u + 1) : (ℤ√2)ˣ) : ℤ√2) * ⟨3, 2⟩ := by rw [hsq]
        constructor
        · rw [hmul]
          change ((silverUnit ^ (2 * u + 1) : (ℤ√2)ˣ) : ℤ√2).re * 3 +
              2 * ((silverUnit ^ (2 * u + 1) : (ℤ√2)ˣ) : ℤ√2).im * 2 = padeLeadB (u + 1)
          rw [ih_re, ih_im, padeLeadB_succ]
          ring
        · rw [hmul]
          change ((silverUnit ^ (2 * u + 1) : (ℤ√2)ˣ) : ℤ√2).re * 2 +
              ((silverUnit ^ (2 * u + 1) : (ℤ√2)ˣ) : ℤ√2).im * 3 = padeLeadA (u + 1)
          rw [ih_re, ih_im, padeLeadA_succ]
          ring
  have hratio_step :
      ∀ m k : ℕ, m ≤ k →
        padeLeadB m * padeLeadB (k + 1) ≤ padeLeadB (m + 1) * padeLeadB k := by
    intro m k hmk
    have hBm_le_Bk : padeLeadB m ≤ padeLeadB k := hmonoB.monotone hmk
    have ⟨hmA, hmB⟩ := hge m
    have ⟨hkA, hkB⟩ := hge k
    have hpellm := hpell m
    have hpellk := hpell k
    have hsq_le : padeLeadB m ^ 2 ≤ padeLeadB k ^ 2 :=
      pow_le_pow_left₀ (by linarith) hBm_le_Bk 2
    have hdiff :
        2 * ((padeLeadA m * padeLeadB k) ^ 2 - (padeLeadB m * padeLeadA k) ^ 2) =
          padeLeadB k ^ 2 - padeLeadB m ^ 2 := by
      have h2m : 2 * padeLeadA m ^ 2 = padeLeadB m ^ 2 + 1 := by linarith
      have h2k : 2 * padeLeadA k ^ 2 = padeLeadB k ^ 2 + 1 := by linarith
      calc
        2 * ((padeLeadA m * padeLeadB k) ^ 2 - (padeLeadB m * padeLeadA k) ^ 2)
            = (2 * padeLeadA m ^ 2) * padeLeadB k ^ 2 -
                padeLeadB m ^ 2 * (2 * padeLeadA k ^ 2) := by ring
        _ = (padeLeadB m ^ 2 + 1) * padeLeadB k ^ 2 -
              padeLeadB m ^ 2 * (padeLeadB k ^ 2 + 1) := by rw [h2m, h2k]
        _ = padeLeadB k ^ 2 - padeLeadB m ^ 2 := by ring
    have hcross : padeLeadB m * padeLeadA k ≤ padeLeadA m * padeLeadB k := by
      by_contra! hlt
      have hAmBk_pos : 0 < padeLeadA m * padeLeadB k := mul_pos (by linarith) (by linarith)
      have hsq_lt : (padeLeadA m * padeLeadB k) ^ 2 < (padeLeadB m * padeLeadA k) ^ 2 :=
        pow_lt_pow_left₀ hlt hAmBk_pos.le (by decide)
      linarith
    rw [padeLeadB_succ, padeLeadB_succ]
    linarith
  have hratio_pow :
      ∀ m k : ℕ, m ≤ k →
        (padeLeadB m) ^ (k - m) * padeLeadB k ≤ padeLeadB m * (padeLeadB (m + 1)) ^ (k - m) := by
    intro m k hmk
    obtain ⟨d, rfl⟩ : ∃ d : ℕ, k = m + d := ⟨k - m, by omega⟩
    clear hmk
    rw [Nat.add_sub_cancel_left]
    induction d with
    | zero =>
        simp
    | succ d ih =>
        have hstep := hratio_step m (m + d) (by omega)
        have hBm_pos : 0 < padeLeadB m := by linarith [(hge m).2]
        have hBm1_pos : 0 < padeLeadB (m + 1) := by linarith [(hge (m + 1)).2]
        calc
          (padeLeadB m) ^ (d + 1) * padeLeadB (m + (d + 1))
              = (padeLeadB m) ^ d * (padeLeadB m * padeLeadB (m + d + 1)) := by
                  rw [pow_succ']
                  ring_nf
          _ ≤ (padeLeadB m) ^ d * (padeLeadB (m + 1) * padeLeadB (m + d)) :=
              mul_le_mul_of_nonneg_left hstep (by positivity)
          _ = padeLeadB (m + 1) * ((padeLeadB m) ^ d * padeLeadB (m + d)) := by ring
          _ ≤ padeLeadB (m + 1) * (padeLeadB m * (padeLeadB (m + 1)) ^ d) :=
              mul_le_mul_of_nonneg_left ih (by positivity)
          _ = padeLeadB m * (padeLeadB (m + 1)) ^ (d + 1) := by
              rw [pow_succ']
              ring
  refine ⟨hmonoA, hmonoB, fun u => ?_, fun m k hmk => ⟨hratio_step m k hmk, hratio_pow m k hmk⟩⟩
  exact ⟨(hge u).1, (hge u).2, hpell u, (hsilver u).1, (hsilver u).2⟩

/-- Symbolic all-order Pell–Padé contraction for all `3 ≤ p`, `1 ≤ u`, and `m ≤ u`:
`padeSeqA u p < padeLeadA u * p ^ u`, `padeSeqB u p < padeLeadB u * p ^ u`, and
`(padeLeadB m) ^ (u - m) * padeSeqB u p < padeLeadB m * (padeLeadB (m + 1)) ^ (u - m) * p ^ u`. -/
theorem padeSeq_symbolic_all_order_contraction {p : ℕ} (hp3 : 3 ≤ p) :
    (∀ u : ℕ, 1 ≤ u →
      padeSeqA u p < padeLeadA u * (p : ℤ) ^ u ∧
      padeSeqB u p < padeLeadB u * (p : ℤ) ^ u) ∧
    (∀ m u : ℕ, m ≤ u → 1 ≤ u →
      (padeLeadB m) ^ (u - m) * padeSeqB u p <
        padeLeadB m * (padeLeadB (m + 1)) ^ (u - m) * (p : ℤ) ^ u) := by
  have hstrict :
      ∀ u : ℕ, 1 ≤ u →
        padeSeqA u p < padeLeadA u * (p : ℤ) ^ u ∧
        padeSeqB u p < padeLeadB u * (p : ℤ) ^ u := by
    intro u hu
    cases u with
    | zero => omega
    | succ k =>
        obtain ⟨iha, ihb⟩ := padeSeq_le_padeLead_mul_pow_aux hp3 k
        obtain ⟨ha_pos, hb_pos⟩ := padeSeq_one_le hp3 k
        have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
        have ha_lt : padeSeqA (k + 1) p < padeLeadA (k + 1) * (p : ℤ) ^ (k + 1) := by
          calc
            padeSeqA (k + 1) p
                = (3 * (p : ℤ) - 4) * padeSeqA k p + 2 * ((p : ℤ) - 2) * padeSeqB k p :=
                    padeSeqA_succ k p
            _ < 3 * (p : ℤ) * padeSeqA k p + 2 * (p : ℤ) * padeSeqB k p := by nlinarith
            _ ≤ 3 * (p : ℤ) * (padeLeadA k * (p : ℤ) ^ k) +
                  2 * (p : ℤ) * (padeLeadB k * (p : ℤ) ^ k) := by
                have h1 := mul_le_mul_of_nonneg_left iha (by linarith : 0 ≤ 3 * (p : ℤ))
                have h2 := mul_le_mul_of_nonneg_left ihb (by linarith : 0 ≤ 2 * (p : ℤ))
                linarith
            _ = (3 * padeLeadA k + 2 * padeLeadB k) * ((p : ℤ) ^ k * (p : ℤ)) := by ring
            _ = padeLeadA (k + 1) * (p : ℤ) ^ (k + 1) := by rw [← pow_succ, padeLeadA_succ]
        have hb_lt : padeSeqB (k + 1) p < padeLeadB (k + 1) * (p : ℤ) ^ (k + 1) := by
          calc
            padeSeqB (k + 1) p
                = 4 * ((p : ℤ) - 1) * padeSeqA k p + (3 * (p : ℤ) - 4) * padeSeqB k p :=
                    padeSeqB_succ k p
            _ < 4 * (p : ℤ) * padeSeqA k p + 3 * (p : ℤ) * padeSeqB k p := by nlinarith
            _ ≤ 4 * (p : ℤ) * (padeLeadA k * (p : ℤ) ^ k) +
                  3 * (p : ℤ) * (padeLeadB k * (p : ℤ) ^ k) := by
                have h1 := mul_le_mul_of_nonneg_left iha (by linarith : 0 ≤ 4 * (p : ℤ))
                have h2 := mul_le_mul_of_nonneg_left ihb (by linarith : 0 ≤ 3 * (p : ℤ))
                linarith
            _ = (4 * padeLeadA k + 3 * padeLeadB k) * ((p : ℤ) ^ k * (p : ℤ)) := by ring
            _ = padeLeadB (k + 1) * (p : ℤ) ^ (k + 1) := by rw [← pow_succ, padeLeadB_succ]
        exact ⟨ha_lt, hb_lt⟩
  refine ⟨hstrict, fun m u hmu hu => ?_⟩
  have hB_lt := (hstrict u hu).2
  have hlead_le := (padeLeadPair_eq_silverUnit_odd_pow_and_pell_norm.2.2.2 m u hmu).2
  have hBm_pos : 0 < padeLeadB m := by
    linarith [(padeLeadPair_eq_silverUnit_odd_pow_and_pell_norm.2.2.1 m).2.1]
  have hpow_pos : (0 : ℤ) < (padeLeadB m) ^ (u - m) := by positivity
  have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  have hpu_pos : (0 : ℤ) < (p : ℤ) ^ u := by positivity
  calc
    (padeLeadB m) ^ (u - m) * padeSeqB u p
        < (padeLeadB m) ^ (u - m) * (padeLeadB u * (p : ℤ) ^ u) :=
          mul_lt_mul_of_pos_left hB_lt hpow_pos
    _ = ((padeLeadB m) ^ (u - m) * padeLeadB u) * (p : ℤ) ^ u := by ring
    _ ≤ (padeLeadB m * (padeLeadB (m + 1)) ^ (u - m)) * (p : ℤ) ^ u :=
        mul_le_mul_of_nonneg_right hlead_le hpu_pos.le
    _ = padeLeadB m * (padeLeadB (m + 1)) ^ (u - m) * (p : ℤ) ^ u := by ring

/-- Global `componentIndex N r₀ = p ^ j` (`Even j`) wrapper combining the tridecuple exponent
floor `6541380665835014 ≤ u` with the exact infinite-order Pell–Padé contraction
`p * k_pade < padeLeadB u` and symbolic all-order tower bounds `∀ m ≤ u`. -/
theorem even_prime_power_symbolic_all_order_and_exact_lead_profile
    {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    ∀ r₀ ∈ N.primeFactors, ∀ p j : ℕ, p.Prime → 0 < j → Even j → componentIndex N r₀ = p ^ j →
    ∃ q s u : ℕ,
      let k_pade : ℤ := ((s : ℤ) * padeSeqB u p - padeSeqA u p) / (p : ℤ) ^ (2 * u + 1)
      r₀ = q ∧ q.Prime ∧ q % 4 = 1 ∧ N.factorization q = 1 ∧ Odd s ∧ j = 2 * u ∧
      6541380665835014 ≤ u ∧
      sigma 1 (p ^ (2 * u)) = q ∧ q + 1 = 2 * s ^ 2 ∧ sigma 1 (s ^ 2) = p ^ (2 * u) ∧
      1 ≤ k_pade ∧
      (p : ℤ) * k_pade < padeLeadB u ∧
      140 * ((p : ℤ) - 1) * k_pade < 99 * padeLeadB u ∧
      p * k_pade.natAbs < (padeLeadB u).natAbs ∧
      (∀ m : ℕ, m ≤ u →
        (padeLeadB m).natAbs ^ (u - m) * (p * k_pade.natAbs) <
          (padeLeadB m).natAbs * (padeLeadB (m + 1)).natAbs ^ (u - m)) := by
  intro r₀ hr₀ p j hp hj_pos hj_even hidx
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀
  have ha : 0 < N.factorization r₀ :=
    Nat.Prime.factorization_pos_of_dvd hr₀_prime hN.2.ne' (Nat.dvd_of_mem_primeFactors hr₀)
  have hNb : N = r₀ ^ N.factorization r₀ * ordCompl[r₀] N :=
    (Nat.ordProj_mul_ordCompl_eq_self N r₀).symm
  have hr₀b : ¬ r₀ ∣ ordCompl[r₀] N := Nat.not_dvd_ordCompl hr₀_prime hN.2.ne'
  obtain ⟨i, _, hl, hr, _⟩ := exists_component_index hN hr₀_prime hNb hr₀b
  have hci : componentIndex N r₀ = i := by
    rw [componentIndex, hl]
    exact Nat.mul_div_cancel_left i (pow_pos hr₀_prime.pos _)
  obtain ⟨u, hu_eq⟩ := hj_even
  have hj_eq : j = 2 * u := by omega
  have hu : 0 < u := by omega
  have hi : i = p ^ (2 * u) := by rw [← hci, hidx, hj_eq]
  obtain ⟨ha1, hσq⟩ :=
    even_prime_power_index_eq_selected_sigma hN ho hr₀_prime ha hNb hr₀b hl hr hp hu hi
  have hbo := ho.of_dvd_nat (hNb ▸ dvd_mul_left _ _)
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h4 : 4 ∣ 2 * ordCompl[r₀] N :=
      hr ▸ hi ▸ (pow_dvd_pow 2 (by omega : 2 ≤ 2 * u)).trans (dvd_mul_left _ _)
    have := hbo.not_two_dvd_nat
    omega
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := odd_prime_ge_three_symbolic hp hpo
  obtain ⟨m, hr₀4, _, _, hm_sq⟩ :=
    euler_form_of_odd_component_index hN ho hr₀_prime ha hNb hr₀b hl hr (hi ▸ hpo.pow)
  have hm_dvd_N : m ∣ N := by
    rw [hNb, hm_sq]
    exact dvd_mul_of_dvd_right (dvd_pow_self m (by decide : 2 ≠ 0)) _
  have hmo : Odd m := ho.of_dvd_nat hm_dvd_N
  have hl' := hl
  have hr' := hr
  rw [hm_sq, ha1, pow_one, hi] at hl' hr'
  obtain ⟨s, hs, _, _, _, hplus, hσs⟩ :=
    even_prime_power_cofactor_split hr₀_prime hp hmo hpo hu hl' hr'
  obtain ⟨hu_ge, _, _, _, _⟩ :=
    even_prime_power_tridecuple_sublinear_repunit_profile
      hN ho hr₀_prime ha hNb hr₀b hl hr hp hu hi
  obtain ⟨_, hk1, _, _, _⟩ :=
    even_index_pade_quotient_pos_and_quadratic_identity hp hpo hs hu hσq hplus hσs
  obtain ⟨_, hpu1_k, h140_k, _⟩ :=
    even_index_pade_quotient_weighted_contraction hp hpo hs hu hσq hplus hσs
  set k_pade : ℤ := ((s : ℤ) * padeSeqB u p - padeSeqA u p) / (p : ℤ) ^ (2 * u + 1)
  change 1 ≤ k_pade at hk1
  change (p : ℤ) ^ (u + 1) * k_pade < padeSeqB u p at hpu1_k
  change 140 * ((p : ℤ) - 1) * k_pade * (p : ℤ) ^ u < 99 * padeSeqB u p at h140_k
  have hu1 : 1 ≤ u := by omega
  obtain ⟨hseq_strict, htower_B⟩ := padeSeq_symbolic_all_order_contraction hp3
  have hBu_lt : padeSeqB u p < padeLeadB u * (p : ℤ) ^ u := (hseq_strict u hu1).2
  have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  have hpu_pos : (0 : ℤ) < (p : ℤ) ^ u := by positivity
  have hpk_lt_leadB : (p : ℤ) * k_pade < padeLeadB u := by
    have hmul : ((p : ℤ) * k_pade) * (p : ℤ) ^ u < padeLeadB u * (p : ℤ) ^ u := by
      calc
        ((p : ℤ) * k_pade) * (p : ℤ) ^ u
            = (p : ℤ) ^ (u + 1) * k_pade := by rw [pow_succ']; ring
        _ < padeSeqB u p := hpu1_k
        _ < padeLeadB u * (p : ℤ) ^ u := hBu_lt
    exact lt_of_mul_lt_mul_right hmul hpu_pos.le
  have h140_lt_leadB : 140 * ((p : ℤ) - 1) * k_pade < 99 * padeLeadB u := by
    have hmul : (140 * ((p : ℤ) - 1) * k_pade) * (p : ℤ) ^ u < (99 * padeLeadB u) * (p : ℤ) ^ u := by
      calc
        (140 * ((p : ℤ) - 1) * k_pade) * (p : ℤ) ^ u
            = 140 * ((p : ℤ) - 1) * k_pade * (p : ℤ) ^ u := by ring
        _ < 99 * padeSeqB u p := h140_k
        _ < 99 * (padeLeadB u * (p : ℤ) ^ u) := mul_lt_mul_of_pos_left hBu_lt (by norm_num)
        _ = (99 * padeLeadB u) * (p : ℤ) ^ u := by ring
    exact lt_of_mul_lt_mul_right hmul hpu_pos.le
  have hk_natAbs : (k_pade.natAbs : ℤ) = k_pade := Int.natAbs_of_nonneg (by omega)
  have hBu_natAbs : ((padeLeadB u).natAbs : ℤ) = padeLeadB u :=
    Int.natAbs_of_nonneg (by linarith [(padeLeadPair_eq_silverUnit_odd_pow_and_pell_norm.2.2.1 u).2.1])
  have hpk_nat_lt : p * k_pade.natAbs < (padeLeadB u).natAbs := by
    rw [← hk_natAbs, ← hBu_natAbs] at hpk_lt_leadB
    exact_mod_cast hpk_lt_leadB
  have htower_nat :
      ∀ m : ℕ, m ≤ u →
        (padeLeadB m).natAbs ^ (u - m) * (p * k_pade.natAbs) <
          (padeLeadB m).natAbs * (padeLeadB (m + 1)).natAbs ^ (u - m) := by
    intro m hmu
    have hBm_natAbs : ((padeLeadB m).natAbs : ℤ) = padeLeadB m :=
      Int.natAbs_of_nonneg (by linarith [(padeLeadPair_eq_silverUnit_odd_pow_and_pell_norm.2.2.1 m).2.1])
    have hBm1_natAbs : ((padeLeadB (m + 1)).natAbs : ℤ) = padeLeadB (m + 1) :=
      Int.natAbs_of_nonneg
        (by linarith [(padeLeadPair_eq_silverUnit_odd_pow_and_pell_norm.2.2.1 (m + 1)).2.1])
    have htowerZ := htower_B m u hmu hu1
    have hBm_pos : 0 < padeLeadB m := by
      linarith [(padeLeadPair_eq_silverUnit_odd_pow_and_pell_norm.2.2.1 m).2.1]
    have hpow_Bm_pos : (0 : ℤ) < (padeLeadB m) ^ (u - m) := by positivity
    have hmul :
        ((padeLeadB m) ^ (u - m) * ((p : ℤ) * k_pade)) * (p : ℤ) ^ u <
          (padeLeadB m * (padeLeadB (m + 1)) ^ (u - m)) * (p : ℤ) ^ u := by
      calc
        ((padeLeadB m) ^ (u - m) * ((p : ℤ) * k_pade)) * (p : ℤ) ^ u
            = (padeLeadB m) ^ (u - m) * ((p : ℤ) ^ (u + 1) * k_pade) := by
                rw [pow_succ']; ring
        _ < (padeLeadB m) ^ (u - m) * padeSeqB u p :=
            mul_lt_mul_of_pos_left hpu1_k hpow_Bm_pos
        _ < padeLeadB m * (padeLeadB (m + 1)) ^ (u - m) * (p : ℤ) ^ u := htowerZ
    have hltZ :
        (padeLeadB m) ^ (u - m) * ((p : ℤ) * k_pade) <
          padeLeadB m * (padeLeadB (m + 1)) ^ (u - m) :=
      lt_of_mul_lt_mul_right hmul hpu_pos.le
    rw [← hBm_natAbs, ← hBm1_natAbs, ← hk_natAbs] at hltZ
    exact_mod_cast hltZ
  exact ⟨r₀, s, u, rfl, hr₀_prime, hr₀4, ha1, hs, hj_eq, hu_ge, hσq, hplus, hσs, hk1,
    hpk_lt_leadB, h140_lt_leadB, hpk_nat_lt, htower_nat⟩

end OddPerfect
