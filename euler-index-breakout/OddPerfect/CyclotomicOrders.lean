module

public import OddPerfect.Primitive
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring

/-! # A distinct prime of an odd perfect number for every divisor of the component length -/

public section

namespace OddPerfect

open Polynomial Finset

private noncomputable abbrev cycloValue (b d : ℕ) : ℕ := ((cyclotomic d ℤ).eval (b : ℤ)).natAbs

/-- Reduction to characteristic `r` removes precisely the `r`-part of the cyclotomic index. -/
private theorem order_of_dvd_cycloValue {b d r : ℕ} (hd : d ≠ 0) (hr : r.Prime)
    (hdiv : r ∣ cycloValue b d) : orderOf (b : ZMod r) = ordCompl[r] d := by
  let : Fact r.Prime := ⟨hr⟩
  have hroot : (cyclotomic d (ZMod r)).IsRoot (b : ZMod r) := by
    rw [IsRoot.def, ← map_cyclotomic_int, eval_map, ← Int.cast_natCast]
    change eval₂ (Int.castRingHom (ZMod r)) ((Int.castRingHom (ZMod r)) (b : ℤ)) _ = 0
    rw [eval₂_hom, Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.dvd_natAbs.mp (by exact_mod_cast hdiv)
  let : NeZero ((ordCompl[r] d : ℕ) : ZMod r) := NeZero.of_not_dvd _ (Nat.not_dvd_ordCompl hr hd)
  have hidx := Nat.ordProj_mul_ordCompl_eq_self d r
  rw [← hidx] at hroot
  exact (isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp hroot).eq_orderOf.symm

/-- Each prime dividing both the value and the index is larger than every
other prime in the index. -/
private theorem lt_bad_prime {b d r s : ℕ} (hd : d ≠ 0) (hr : r.Prime) (hs : s.Prime)
    (hrd : r ∣ cycloValue b d) (hsd : s ∣ d) (hsr : s ≠ r) : s < r := by
  let : Fact r.Prime := ⟨hr⟩
  have hor := order_of_dvd_cycloValue hd hr hrd
  have hb0 : (b : ZMod r) ≠ 0 := by
    intro h; rw [h, orderOf_zero] at hor
    exact (Nat.ordCompl_pos r hd).ne' hor.symm
  have hco := ZMod.orderOf_dvd_card_sub_one hb0
  rw [hor] at hco
  have hnd : ¬ r ∣ s := fun h => hsr ((Nat.prime_dvd_prime_iff_eq hr hs).mp h).symm
  have hsco := Nat.dvd_ordCompl_of_dvd_not_dvd hsd hnd
  have := Nat.le_of_dvd (by have := hr.one_lt; omega) (hsco.trans hco)
  omega

private theorem cycloValue_dvd_geom_sum {b d t r : ℕ} (hb : 1 < b) (ht : 0 < t)
    (hr : 1 < r) (hd : d = t * r) : cycloValue b d ∣ ∑ i ∈ range r, (b ^ t) ^ i := by
  have hproper : t ∈ d.properDivisors := Nat.mem_properDivisors.mpr
    ⟨hd ▸ dvd_mul_right _ _, hd ▸ lt_mul_of_one_lt_right ht hr⟩
  obtain ⟨u, hu⟩ := X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ hproper
  have hval := congrArg (Polynomial.eval (b : ℤ)) hu
  simp only [eval_sub, eval_pow, eval_X, eval_one, eval_mul] at hval
  have hpos : (1 : ℤ) < (b : ℤ) ^ t := one_lt_pow₀ (by exact_mod_cast hb) ht.ne'
  have hsum : (∑ i ∈ range r, ((b : ℤ) ^ t) ^ i) = (cyclotomic d ℤ).eval (b : ℤ) * u.eval (b : ℤ) := by
    apply mul_right_cancel₀ (sub_ne_zero.mpr hpos.ne')
    rw [geom_sum_mul, ← pow_mul, ← hd, hval]
    ring
  have hcast : ((∑ i ∈ range r, (b ^ t) ^ i : ℕ) : ℤ) = (cyclotomic d ℤ).eval (b : ℤ) * u.eval (b : ℤ) := by
    simpa only [Nat.cast_sum, Nat.cast_pow] using hsum
  exact ⟨(u.eval (b : ℤ)).natAbs, by simpa only [Int.natAbs_natCast, Int.natAbs_mul, cycloValue] using congrArg Int.natAbs hcast⟩

/-- Mixed-length Bang–Zsigmondy for bases at least three. The index has at least
two distinct prime divisors. -/
theorem exists_prime_order_mixed {b d : ℕ} (hb : 3 ≤ b) (hd : 1 < d) (hmix : ¬ IsPrimePow d) :
    ∃ r : ℕ, r.Prime ∧ orderOf (b : ZMod r) = d ∧ d ∣ r-1 := by
  have hv := sub_one_pow_totient_lt_natAbs_cyclotomic_eval hd (by omega : b ≠ 1)
  change (b-1)^d.totient < cycloValue b d at hv
  have hdpos : 0 < d := by omega
  have hV : 1 < cycloValue b d := lt_of_le_of_lt (Nat.one_le_pow _ _ (by omega)) hv
  suffices h : ∃ r, r.Prime ∧ r ∣ cycloValue b d ∧ ¬ r ∣ d by
    obtain ⟨r, hr, hrv, hrd⟩ := h
    let : Fact r.Prime := ⟨hr⟩
    have hor := order_of_dvd_cycloValue hdpos.ne' hr hrv
    rw [(Nat.ordCompl_eq_self_iff_zero_or_not_dvd d hr).mpr (Or.inr hrd)] at hor
    refine ⟨r, hr, hor, hor ▸ ZMod.orderOf_dvd_card_sub_one ?_⟩
    intro h; rw [h, orderOf_zero] at hor; omega
  by_contra! hnone
  obtain ⟨r, hr, hrv⟩ := Nat.exists_prime_and_dvd hV.ne'
  have hrd := hnone r hr hrv
  have hro : Odd r := by
    apply hr.odd_of_ne_two
    rintro rfl
    apply hmix
    apply isPrimePow_iff_unique_prime_dvd.mpr
    refine ⟨2, ⟨hr, hrd⟩, ?_⟩
    rintro s ⟨hs, hsd⟩
    by_contra h
    exact (hs.two_le.not_gt (lt_bad_prime hdpos.ne' hr hs hrv hsd h))
  have hrlt : r < cycloValue b d := by
    have hφ := Nat.le_of_dvd (Nat.totient_pos.mpr hdpos) (Nat.totient_dvd_of_dvd hrd)
    rw [Nat.totient_prime hr] at hφ
    have hstep : r ≤ 2 ^ (r - 1) := by have := Nat.lt_two_pow_self (n := r-1); have := hr.one_lt; omega
    exact lt_of_le_of_lt (hstep.trans ((Nat.pow_le_pow_right (by decide : 0 < 2) hφ).trans
      (Nat.pow_le_pow_left (by omega : 2 ≤ b-1) _))) hv
  obtain ⟨u, hu⟩ := hrv
  have hu1 : u ≠ 1 := by rintro rfl; simp [hu] at hrlt
  obtain ⟨s, hs, hsu⟩ := Nat.exists_prime_and_dvd hu1
  have hsv : s ∣ cycloValue b d := hu ▸ hsu.trans (dvd_mul_left _ _)
  have hrv' : r ∣ cycloValue b d := hu ▸ dvd_mul_right _ _
  have hsr : s = r := by
    by_contra h
    have h1 := lt_bad_prime hdpos.ne' hr hs hrv' (hnone s hs hsv) h
    have h2 := lt_bad_prime hdpos.ne' hs hr hsv hrd (Ne.symm h)
    omega
  subst s
  obtain ⟨t, hdt⟩ := hrd
  have ht : 0 < t := by
    by_contra! h
    have ht0 : t = 0 := by omega
    rw [ht0, mul_zero] at hdt
    omega
  have hval := cycloValue_dvd_geom_sum (by omega : 1 < b) ht hr.one_lt (hdt.trans (mul_comm _ _))
  have hrsq : r ^ 2 ∣ cycloValue b d := by rw [hu, pow_two]; exact Nat.mul_dvd_mul_left _ hsu
  exact not_sq_dvd_geom_sum hr hro (hrv'.trans hval) (hrsq.trans hval)

/-- Every nontrivial divisor of the length `e+1` at a prime-power component
of an odd perfect number is realized as the precise order at another prime. -/
theorem exists_forced_order_of_length {N p e d : ℕ} (hN : N.Perfect) (hNo : Odd N)
    (hp : p.Prime) (he : N.factorization p = e) (hd : 1 < d) (hlen : d ∣ e+1) :
    ∃ r ∈ N.primeFactors.erase p, orderOf (p : ZMod r) = d ∧ d ∣ r-1 := by
  by_cases hpow : IsPrimePow d
  · obtain ⟨l, k, hl, rfl⟩ := (isPrimePow_iff_pow_succ d).mp hpow
    obtain ⟨r, hr, hor⟩ := exists_forced_order_of_prime_pow_length hN hNo hp he
      (Nat.prime_iff.mpr hl) k hlen
    let : Fact r.Prime := ⟨Nat.prime_of_mem_primeFactors (mem_of_mem_erase hr)⟩
    refine ⟨r, hr, hor, hor ▸ ZMod.orderOf_dvd_card_sub_one ?_⟩
    intro h; rw [h, orderOf_zero] at hor; omega
  · have hepos : 0 < e := by have := Nat.le_of_dvd (by omega : 0 < e+1) hlen; omega
    have hpd := (hp.dvd_iff_one_le_factorization hN.2.ne').mpr (by omega)
    have hp3 : 3 ≤ p := by
      have hp2 := hp.two_le
      rcases eq_or_ne p 2 with rfl | h
      · exact (hNo.not_two_dvd_nat hpd).elim
      · omega
    obtain ⟨r, hr, hor, hcon⟩ := exists_prime_order_mixed hp3 hd hpow
    exact ⟨r, forced_mem_erase_of_order hN hp he hr hd hor hcon hlen, hor, hcon⟩

/-- The divisor count of `e+1` cannot exceed the support size of the odd
perfect number. The empty collection of nontrivial divisors is allowed at length one. -/
theorem component_length_divisor_count {N p : ℕ} (hN : N.Perfect) (hNo : Odd N)
    (hp : p ∈ N.primeFactors) : (N.factorization p + 1).divisors.card ≤ N.primeFactors.card := by
  classical
  let e := N.factorization p
  let S := (e+1).divisors.erase 1
  let T := N.primeFactors.erase p
  have hsub : S ⊆ T.image (fun r => orderOf (p : ZMod r)) := by
    intro d hd
    obtain ⟨hd1, hmem⟩ := mem_erase.mp hd
    have hpos := Nat.pos_of_mem_divisors hmem
    have hlen := Nat.dvd_of_mem_divisors hmem
    obtain ⟨r, hr, hor, _⟩ := exists_forced_order_of_length hN hNo (Nat.prime_of_mem_primeFactors hp)
      (show N.factorization p = e from rfl) (by omega : 1 < d) hlen
    exact mem_image.mpr ⟨r, hr, hor⟩
  have hle : S.card ≤ T.card := (card_le_card hsub).trans card_image_le
  have hs : S.card + 1 = (e+1).divisors.card := card_erase_add_one (Nat.one_mem_divisors.mpr (by omega))
  have ht : T.card + 1 = N.primeFactors.card := card_erase_add_one hp
  change (e+1).divisors.card ≤ _
  omega

end OddPerfect
