module

public import Mathlib.Tactic.Primality.Lucas
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace OddPerfect

@[expose] def knownOrder (factors : List (ℕ × ℕ)) : ℕ :=
  (factors.map fun pe => pe.1 ^ pe.2).prod

open Mathlib.Tactic.Primality in
@[expose] def orderTests (n b : ℕ) (factors : List (ℕ × ℕ)) : Bool :=
  let F := knownOrder factors
  powMod b F n == 1 && factors.all fun pe => (powMod b (F/pe.1) n + (n-1)).gcd n == 1

open Mathlib.Tactic.Primality in
/-- Every prime divisor sees the full certified order. -/
theorem knownOrder_dvd_prime_pred {n b r : ℕ} {factors : List (ℕ × ℕ)}
    (hn : 1 < n) (hF : 0 < knownOrder factors) (hp : ∀ f ∈ factors, f.1.Prime)
    (h : orderTests n b factors = true) (hr : r.Prime) (hd : r ∣ n) : knownOrder factors ∣ r-1 := by
  let F := knownOrder factors
  change 0 < F at hF
  change F ∣ r-1
  simp only [orderTests, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hb,hc⟩ := h
  change powMod b F n = 1 at hb
  let : Fact r.Prime := ⟨hr⟩
  have hcast (k) : (powMod b k n : ZMod r) = (b : ZMod r)^k := by
    rw [powMod_def, ← Nat.cast_pow, ZMod.natCast_eq_natCast_iff]
    exact Nat.ModEq.of_dvd hd (Nat.mod_modEq _ _)
  have hbn : (b : ZMod r)^F = 1 := by rw [←hcast, hb, Nat.cast_one]
  have hnzero : (b : ZMod r) ≠ 0 := by
    rintro hz
    simp [hz, zero_pow (Nat.ne_of_gt hF)] at hbn
  have hord : orderOf (b : ZMod r) = F := by
    apply orderOf_eq_of_pow_and_pow_div_prime hbn
    intro q hq hqF heq
    obtain ⟨_, hx, hdiv⟩ := hq.prime.dvd_prod_iff.mp hqF
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (hp f hf)).mp (hq.dvd_of_dvd_pow hdiv)
    have hzero : ((powMod b (F/f.1) n + (n-1) : ℕ) : ZMod r) = 0 := by
      rw [Nat.cast_add, hcast, heq, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one,
        (ZMod.natCast_eq_zero_iff n r).mpr hd]
      simp
    have hbad := Nat.dvd_gcd ((ZMod.natCast_eq_zero_iff _ _).mp hzero) hd
    have hg := hc _ hf
    exact hr.not_dvd_one (hg ▸ hbad)
  exact hord ▸ ZMod.orderOf_dvd_card_sub_one hnzero

/-- A Pocklington certificate with a large known order F. Reduction modulo
the least prime divisor preserves this order, so that divisor exceeds F. -/
@[expose] def largeOrderCheck (n b : ℕ) (factors : List (ℕ × ℕ)) : Bool :=
  let F := knownOrder factors
  decide (1 < n ∧ 0 < F ∧ n < (F+1)^2) && orderTests n b factors

theorem prime_of_largeOrderCheck {n b : ℕ} {factors : List (ℕ × ℕ)}
    (hp : ∀ f ∈ factors, f.1.Prime) (h : largeOrderCheck n b factors = true) : n.Prime := by
  simp only [largeOrderCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hn, hF, hs⟩, hc⟩ := h
  have hr : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hd := knownOrder_dvd_prime_pred hn hF hp hc hr (Nat.minFac_dvd n)
  have hle := Nat.le_of_dvd (by have := hr.one_lt; omega : 0<n.minFac-1) hd
  by_contra hn'
  have hlow := Nat.minFac_sq_le_self (by omega) hn'
  have hh := Nat.pow_le_pow_left (by omega : knownOrder factors+1 ≤ n.minFac) 2
  exact hs.not_ge (hh.trans hlow)

end OddPerfect
