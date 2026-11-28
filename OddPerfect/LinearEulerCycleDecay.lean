module

public import OddPerfect.LinearEulerIteratedPeeling
public import OddPerfect.OddGeometricSquares
public import OddPerfect.OddValuationCycleObstruction
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Linear Euler Cycle Decay and Global Collapse of the Peeling-Cycle Branch

Formalizes exponential decay along full-power `σ`-peeling steps, exact two-step elimination of
`(3, 2) → (11, 1)`, impossibility of closed full-power prime-square cycles, and unconditional
collapse of the directed-cycle branch in `linear_euler_peeling_collision_or_cycle`:

1. `full_power_step_decay_of_ne_three_two`:
   Every full-power odd prime-square step `b ^ (2 * e_b) ∣ σ(a ^ (2 * e_a))` with `(a, e_a) ≠ (3, 2)`
   has odd cofactor `k ≥ 3`, yielding `3 * (a - 1) * b ^ (2 * e_b) < a * a ^ (2 * e_a)`,
   `2 * b ^ (2 * e_b) < a ^ (2 * e_a)`, and sharpened bounds for `5 ≤ a` (`12 / 5`) and
   `53 ≤ a` (`156 / 53`).
2. `three_four_to_eleven_two_two_step_decay`:
   `b ^ (2 * e_b) ∣ σ(3 ^ 4)` forces `b = 11 ∧ e_b = 1`, and `σ(11 ^ 2) = 133` admits no odd
   prime-square divisor `c ^ (2 * e_c)`.
3. `no_closed_all_full_power_square_cycle`:
   No non-empty cyclic list in `m.primeFactors` (for odd `m`) can absorb full prime-square powers
   at every cyclic step.
4. `peeling_chain_exponential_decay` and `sixth_power_free_peeling_chain_exponential_decay`:
   Exponential telescope decay along open full-power peeling chains (`2^(k-1)`, `(12/5)^(k-1)`,
   and `(156/53)^(k-1)` in the sixth-power-free regime).
5. `linear_euler_peeling_cycle_telescope_decay` and `linear_euler_collision_or_half_succ_hit`:
   On any linear Euler odd perfect number `N = q * m ^ 2`, the closing edge of any peeling cycle
   cannot absorb the full power, collapsing the third branch of
   `linear_euler_peeling_collision_or_cycle` unconditionally into either a prime collision or a
   half-successor hit `p ∣ (q + 1) / 2`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- **1. Full-Power Step Decay (`(a, e_a) ≠ (3, 2)`)**:
Whenever odd primes `a, b` and positive exponents `e_a, e_b` satisfy
`b ^ (2 * e_b) ∣ sigma 1 (a ^ (2 * e_a))` with `(a, e_a) ≠ (3, 2)`, the cofactor
`sigma 1 (a ^ (2 * e_a)) / b ^ (2 * e_b)` is at least `3`, giving
`3 * (a - 1) * b ^ (2 * e_b) < a * a ^ (2 * e_a)` as well as the linear decay bounds
`2 * b ^ (2 * e_b) < a ^ (2 * e_a)`, `5 ≤ a → 12 * b ^ (2 * e_b) < 5 * a ^ (2 * e_a)`,
and `53 ≤ a → 156 * b ^ (2 * e_b) < 53 * a ^ (2 * e_a)`. -/
theorem full_power_step_decay_of_ne_three_two {a b e_a e_b : ℕ}
    (ha : a.Prime) (ha_odd : Odd a) (hb : b.Prime) (hb_odd : Odd b)
    (hea : 0 < e_a) (heb : 0 < e_b) (hne : ¬ (a = 3 ∧ e_a = 2))
    (hdvd : b ^ (2 * e_b) ∣ sigma 1 (a ^ (2 * e_a))) :
    3 ≤ sigma 1 (a ^ (2 * e_a)) / b ^ (2 * e_b) ∧
    3 * (a - 1) * b ^ (2 * e_b) < a * a ^ (2 * e_a) ∧
    2 * b ^ (2 * e_b) < a ^ (2 * e_a) ∧
    (5 ≤ a → 12 * b ^ (2 * e_b) < 5 * a ^ (2 * e_a)) ∧
    (53 ≤ a → 156 * b ^ (2 * e_b) < 53 * a ^ (2 * e_a)) := by
  have _ := hb
  have _ := hb_odd
  have _ := heb
  let k := sigma 1 (a ^ (2 * e_a)) / b ^ (2 * e_b)
  have hmul : b ^ (2 * e_b) * k = sigma 1 (a ^ (2 * e_a)) := Nat.mul_div_cancel' hdvd
  have ha_sq_odd : Odd (a ^ (2 * e_a)) := ha_odd.pow
  have ha_sq_isSq : IsSquare (a ^ (2 * e_a)) := ⟨a ^ e_a, by ring⟩
  have hsig_odd : Odd (sigma 1 (a ^ (2 * e_a))) :=
    (odd_sigma_iff_square_of_odd ha_sq_odd).mpr ha_sq_isSq
  have hk_odd : Odd k := hsig_odd.of_dvd_nat ⟨b ^ (2 * e_b), by rw [← hmul, mul_comm]⟩
  have hk_ne1 : k ≠ 1 := by
    intro hk1
    have hsig_eq : sigma 1 (a ^ (2 * e_a)) = b ^ (2 * e_b) := by
      rw [← hmul, hk1, mul_one]
    have hsig_sq : IsSquare (sigma 1 (a ^ (2 * e_a))) := by
      rw [hsig_eq]
      exact ⟨b ^ e_b, by ring⟩
    have h34 : a = 3 ∧ 2 * e_a = 4 :=
      (sigma_prime_pow_isSquare_iff_of_even ha (by omega) ⟨e_a, by ring⟩).mp hsig_sq
    exact hne ⟨h34.1, by omega⟩
  have hk_ge3 : 3 ≤ k := by
    obtain ⟨t, ht⟩ := hk_odd
    omega
  have hgeom : sigma 1 (a ^ (2 * e_a)) * (a - 1) = a ^ (2 * e_a + 1) - 1 := by
    rw [sigma_one_apply_prime_pow ha]
    exact geom_sum_mul_of_one_le ha.one_lt.le (2 * e_a + 1)
  have ha_pow_pos : 1 ≤ a ^ (2 * e_a + 1) := Nat.one_le_pow _ _ ha.pos
  have hsig_lt : (a - 1) * sigma 1 (a ^ (2 * e_a)) < a * a ^ (2 * e_a) := by
    calc
      (a - 1) * sigma 1 (a ^ (2 * e_a))
          = sigma 1 (a ^ (2 * e_a)) * (a - 1) := Nat.mul_comm _ _
      _ = a ^ (2 * e_a + 1) - 1 := hgeom
      _ < a ^ (2 * e_a + 1) := Nat.sub_lt ha_pow_pos Nat.one_pos
      _ = a * a ^ (2 * e_a) := by rw [pow_succ']
  have h3b_le : 3 * b ^ (2 * e_b) ≤ sigma 1 (a ^ (2 * e_a)) := by
    calc
      3 * b ^ (2 * e_b) ≤ k * b ^ (2 * e_b) := Nat.mul_le_mul_right _ hk_ge3
      _ = sigma 1 (a ^ (2 * e_a)) := by rw [← hmul, mul_comm]
  have hmain : 3 * (a - 1) * b ^ (2 * e_b) < a * a ^ (2 * e_a) := by
    calc
      3 * (a - 1) * b ^ (2 * e_b)
          = (a - 1) * (3 * b ^ (2 * e_b)) := by ring
      _ ≤ (a - 1) * sigma 1 (a ^ (2 * e_a)) := Nat.mul_le_mul_left _ h3b_le
      _ < a * a ^ (2 * e_a) := hsig_lt
  have ha_ge3 : 3 ≤ a := by
    have := ha.two_le
    obtain ⟨t, ht⟩ := ha_odd
    omega
  have h2 : 2 * b ^ (2 * e_b) < a ^ (2 * e_a) := by
    have hcoeff : 2 * a ≤ 3 * (a - 1) := by omega
    have hmul_lt : a * (2 * b ^ (2 * e_b)) < a * a ^ (2 * e_a) := by
      calc
        a * (2 * b ^ (2 * e_b))
            = (2 * a) * b ^ (2 * e_b) := by ring
        _ ≤ (3 * (a - 1)) * b ^ (2 * e_b) := Nat.mul_le_mul_right _ hcoeff
        _ < a * a ^ (2 * e_a) := hmain
    exact Nat.lt_of_mul_lt_mul_left hmul_lt
  have h5 : 5 ≤ a → 12 * b ^ (2 * e_b) < 5 * a ^ (2 * e_a) := by
    intro ha5
    have hcoeff : 12 * a ≤ 15 * (a - 1) := by omega
    have hmul_lt : a * (12 * b ^ (2 * e_b)) < a * (5 * a ^ (2 * e_a)) := by
      calc
        a * (12 * b ^ (2 * e_b))
            = (12 * a) * b ^ (2 * e_b) := by ring
        _ ≤ (15 * (a - 1)) * b ^ (2 * e_b) := Nat.mul_le_mul_right _ hcoeff
        _ = 5 * (3 * (a - 1) * b ^ (2 * e_b)) := by ring
        _ < 5 * (a * a ^ (2 * e_a)) := Nat.mul_lt_mul_of_pos_left hmain (by decide)
        _ = a * (5 * a ^ (2 * e_a)) := by ring
    exact Nat.lt_of_mul_lt_mul_left hmul_lt
  have h53 : 53 ≤ a → 156 * b ^ (2 * e_b) < 53 * a ^ (2 * e_a) := by
    intro ha53
    have hcoeff : 156 * a ≤ 159 * (a - 1) := by omega
    have hmul_lt : a * (156 * b ^ (2 * e_b)) < a * (53 * a ^ (2 * e_a)) := by
      calc
        a * (156 * b ^ (2 * e_b))
            = (156 * a) * b ^ (2 * e_b) := by ring
        _ ≤ (159 * (a - 1)) * b ^ (2 * e_b) := Nat.mul_le_mul_right _ hcoeff
        _ = 53 * (3 * (a - 1) * b ^ (2 * e_b)) := by ring
        _ < 53 * (a * a ^ (2 * e_a)) := Nat.mul_lt_mul_of_pos_left hmain (by decide)
        _ = a * (53 * a ^ (2 * e_a)) := by ring
    exact Nat.lt_of_mul_lt_mul_left hmul_lt
  exact ⟨hk_ge3, hmain, h2, h5, h53⟩

/-- **2. Exact Two-Step Obstruction from `(3, 2)`**:
`sigma 1 (3 ^ 4) = 121 = 11 ^ 2`, so any prime-square divisor `b ^ (2 * e_b) ∣ sigma 1 (3 ^ 4)`
with `b.Prime`, `Odd b`, `0 < e_b` forces `b = 11 ∧ e_b = 1`; moreover `sigma 1 (11 ^ 2) = 133 = 7 * 19`
is squarefree, so it has no prime-square divisor `c ^ (2 * e_c)` at all. -/
theorem three_four_to_eleven_two_two_step_decay :
    (∀ b e_b : ℕ, b.Prime → Odd b → 0 < e_b → b ^ (2 * e_b) ∣ sigma 1 (3 ^ 4) →
      b = 11 ∧ e_b = 1) ∧
    (¬ ∃ c e_c : ℕ, c.Prime ∧ Odd c ∧ 0 < e_c ∧ c ^ (2 * e_c) ∣ sigma 1 (11 ^ 2)) := by
  have hsig3 : sigma 1 (3 ^ 4) = 11 ^ 2 := by
    rw [sigma_one_apply_prime_pow Nat.prime_three]
    norm_num [Finset.sum_range_succ]
  have hsig11 : sigma 1 (11 ^ 2) = 133 := by
    rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 11)]
    norm_num [Finset.sum_range_succ]
  constructor
  · intro b e_b hb _ heb hdvd
    rw [hsig3] at hdvd
    have hb_dvd_11 : b ∣ 11 :=
      hb.dvd_of_dvd_pow
        ((dvd_pow_self b (by omega : 2 * e_b ≠ 0)).trans hdvd)
    have hb11 : b = 11 := ((Nat.dvd_prime (by decide : Nat.Prime 11)).mp hb_dvd_11).resolve_left hb.ne_one
    subst hb11
    have hle : 2 * e_b ≤ 2 :=
      (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 11)).mp hdvd
    exact ⟨rfl, by omega⟩
  · rintro ⟨c, e_c, hc, _, hec, hdvd⟩
    rw [hsig11] at hdvd
    have hc2_dvd : c ^ 2 ∣ 133 :=
      (pow_dvd_pow c (by omega : 2 ≤ 2 * e_c)).trans hdvd
    have hc2_le : c ^ 2 ≤ 133 := Nat.le_of_dvd (by decide) hc2_dvd
    have hc_le11 : c ≤ 11 := by nlinarith
    have hc_ge2 : 2 ≤ c := hc.two_le
    interval_cases c <;> norm_num at hc2_dvd

private lemma ordProj_sq_eq_prime_pow {m p : ℕ} (hm0 : m ≠ 0) :
    ordProj[p] (m ^ 2) = p ^ (2 * m.factorization p) := by
  rw [pow_two, Nat.factorization_mul hm0 hm0, Finsupp.add_apply, ← two_mul]

private lemma chain_exponential_decay_of_step {m : ℕ} (A B : ℕ) (hB : 0 < B)
    (P : ℕ → ℕ) (S : ℕ → Prop)
    (hstep : ∀ a b : ℕ, S a → S b →
      b ^ (2 * m.factorization b) ∣ sigma 1 (ordProj[a] (m ^ 2)) →
      A * P b < B * P a) :
    ∀ L : List ℕ, ∀ (hL : L ≠ []),
      (∀ p ∈ L, S p) →
      (∀ i : ℕ, ∀ (hi : i + 1 < L.length),
        L[i + 1] ^ (2 * m.factorization L[i + 1]) ∣ sigma 1 (ordProj[L[i]] (m ^ 2))) →
      A ^ (L.length - 1) * P (L.getLast hL) ≤ B ^ (L.length - 1) * P (L.head hL) ∧
      (2 ≤ L.length → A ^ (L.length - 1) * P (L.getLast hL) < B ^ (L.length - 1) * P (L.head hL))
  | [], hL, _, _ => (hL rfl).elim
  | [a], _, _, _ => by
    constructor
    · simp
    · intro hlen
      simp at hlen
  | a :: b :: rest, _, hS_list, hsteps => by
    have hrest_ne : b :: rest ≠ [] := List.cons_ne_nil b rest
    have hS_rest : ∀ p ∈ b :: rest, S p := fun p hp =>
      hS_list p (List.mem_cons_of_mem a hp)
    have hsteps_rest : ∀ i : ℕ, ∀ (hi : i + 1 < (b :: rest).length),
        (b :: rest)[i + 1] ^ (2 * m.factorization (b :: rest)[i + 1]) ∣
          sigma 1 (ordProj[(b :: rest)[i]] (m ^ 2)) := fun i hi =>
      hsteps (i + 1) (by simpa using hi)
    obtain ⟨ih_le, _⟩ := chain_exponential_decay_of_step A B hB P S hstep (b :: rest) hrest_ne hS_rest hsteps_rest
    have ha_S : S a := hS_list a List.mem_cons_self
    have hb_S : S b := hS_list b (List.mem_cons_of_mem a List.mem_cons_self)
    have hab_dvd : b ^ (2 * m.factorization b) ∣ sigma 1 (ordProj[a] (m ^ 2)) :=
      hsteps 0 (by simp)
    have hab_lt : A * P b < B * P a := hstep a b ha_S hb_S hab_dvd
    have hhead_b : (b :: rest).head hrest_ne = b := rfl
    have hhead_a : (a :: b :: rest).head (List.cons_ne_nil a _) = a := rfl
    have hlast_eq : (a :: b :: rest).getLast (List.cons_ne_nil a _) = (b :: rest).getLast hrest_ne :=
      List.getLast_cons hrest_ne
    have hlen_eq : (a :: b :: rest).length - 1 = ((b :: rest).length - 1) + 1 := by simp
    set k := (b :: rest).length - 1
    have hBk_pos : 0 < B ^ k := pow_pos hB k
    have hstrict :
        A ^ (k + 1) * P ((a :: b :: rest).getLast (List.cons_ne_nil a _)) <
          B ^ (k + 1) * P ((a :: b :: rest).head (List.cons_ne_nil a _)) := by
      rw [hlast_eq, hhead_a]
      rw [hhead_b] at ih_le
      calc
        A ^ (k + 1) * P ((b :: rest).getLast hrest_ne)
            = A * (A ^ k * P ((b :: rest).getLast hrest_ne)) := by ring
        _ ≤ A * (B ^ k * P b) := Nat.mul_le_mul_left A ih_le
        _ = B ^ k * (A * P b) := by ring
        _ < B ^ k * (B * P a) := Nat.mul_lt_mul_of_pos_left hab_lt hBk_pos
        _ = B ^ (k + 1) * P a := by ring
    rw [hlen_eq]
    exact ⟨hstrict.le, fun _ => hstrict⟩

/-- **3. No Closed Full-Power Prime-Square Cycle**:
For any odd `m : ℕ` and any non-empty list `L : List ℕ` of primes dividing `m`, it is impossible
for every cyclic step in `L` (including the closing step `L.getLast → L.head`) to absorb the
full prime-square power `next ^ (2 * m.factorization next)`. -/
theorem no_closed_all_full_power_square_cycle {m : ℕ} (hm_odd : Odd m) (L : List ℕ)
    (hlen : 1 ≤ L.length) (hm_list : ∀ p ∈ L, p ∈ m.primeFactors) :
    ¬ ((∀ i : ℕ, ∀ (hi : i + 1 < L.length),
          L[i + 1] ^ (2 * m.factorization L[i + 1]) ∣ sigma 1 (ordProj[L[i]] (m ^ 2))) ∧
       (∀ hL : L ≠ [],
          (L.head hL) ^ (2 * m.factorization (L.head hL)) ∣
            sigma 1 (ordProj[L.getLast hL] (m ^ 2)))) := by
  rintro ⟨hsteps, hclose⟩
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have hL_ne : L ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hcyclic_step : ∀ i : ℕ, ∀ (hi : i < L.length),
      let j := (i + 1) % L.length
      have hj : j < L.length := Nat.mod_lt _ (by omega)
      L[j] ^ (2 * m.factorization L[j]) ∣ sigma 1 (ordProj[L[i]] (m ^ 2)) := by
    intro i hi
    dsimp only
    by_cases hi1 : i + 1 < L.length
    · have hidx : L[(i + 1) % L.length]'(Nat.mod_lt _ (by omega)) = L[i + 1] := by
        congr 1
        exact Nat.mod_eq_of_lt hi1
      rw [hidx]
      exact hsteps i hi1
    · have hi_eq : i = L.length - 1 := by omega
      have hidx1 : L[(i + 1) % L.length]'(Nat.mod_lt _ (by omega)) = L[0]'(by omega) := by
        congr 1
        rw [show i + 1 = L.length by omega, Nat.mod_self]
      have hidx2 : L[i] = L[L.length - 1]'(by omega) := by
        congr 1
      have hhead : L.head hL_ne = L[0]'(by omega) := List.head_eq_getElem_zero hL_ne
      have hlast : L.getLast hL_ne = L[L.length - 1]'(by omega) := List.getLast_eq_getElem hL_ne
      have h0 := hclose hL_ne
      rw [hhead, hlast] at h0
      rw [hidx1, hidx2]
      exact h0
  have hmem_prop : ∀ p ∈ m.primeFactors,
      p.Prime ∧ Odd p ∧ 0 < m.factorization p ∧
      ordProj[p] (m ^ 2) = p ^ (2 * m.factorization p) := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hp_dvd := Nat.dvd_of_mem_primeFactors hp
    have hp_odd := hm_odd.of_dvd_nat hp_dvd
    have hp_pos : 0 < m.factorization p := (hp_prime.dvd_iff_one_le_factorization hm0).mp hp_dvd
    exact ⟨hp_prime, hp_odd, hp_pos, ordProj_sq_eq_prime_pow hm0⟩
  by_cases h32 : ∃ p ∈ L, p = 3 ∧ m.factorization p = 2
  · obtain ⟨p, hpL, rfl, hp_exp⟩ := h32
    obtain ⟨i, hi, hi_eq⟩ := List.mem_iff_getElem.mp hpL
    let j := (i + 1) % L.length
    have hj : j < L.length := Nat.mod_lt _ (by omega)
    have hstep_ij : L[j] ^ (2 * m.factorization L[j]) ∣ sigma 1 (3 ^ 4) := by
      have h1 := hcyclic_step i hi
      have hord : ordProj[L[i]] (m ^ 2) = 3 ^ 4 := by
        rw [hi_eq, ordProj_sq_eq_prime_pow hm0, hp_exp]
      rwa [hord] at h1
    have hj_mem : L[j] ∈ m.primeFactors := hm_list _ (List.getElem_mem hj)
    obtain ⟨hj_prime, hj_odd, hj_pos, _⟩ := hmem_prop _ hj_mem
    obtain ⟨hj_eq11, hj_exp1⟩ :=
      three_four_to_eleven_two_two_step_decay.1 _ _ hj_prime hj_odd hj_pos hstep_ij
    let k := (j + 1) % L.length
    have hk : k < L.length := Nat.mod_lt _ (by omega)
    have hstep_jk : L[k] ^ (2 * m.factorization L[k]) ∣ sigma 1 (11 ^ 2) := by
      have h1 := hcyclic_step j hj
      have hord : ordProj[L[j]] (m ^ 2) = 11 ^ 2 := by
        rw [ordProj_sq_eq_prime_pow hm0, hj_exp1, hj_eq11]
      rwa [hord] at h1
    have hk_mem : L[k] ∈ m.primeFactors := hm_list _ (List.getElem_mem hk)
    obtain ⟨hk_prime, hk_odd, hk_pos, _⟩ := hmem_prop _ hk_mem
    exact three_four_to_eleven_two_two_step_decay.2
      ⟨L[k], m.factorization L[k], hk_prime, hk_odd, hk_pos, hstep_jk⟩
  · push Not at h32
    let g : ℕ → ℕ := fun t =>
      let idx := t % L.length
      let x := L[idx]'(Nat.mod_lt t (by omega))
      x ^ (2 * m.factorization x)
    have hg_step : ∀ t : ℕ, g (t + 1) < g t := by
      intro t
      let i := t % L.length
      have hi : i < L.length := Nat.mod_lt t (by omega)
      have hj_mod : (t + 1) % L.length = (i + 1) % L.length := by
        simp [i]
      let j := (i + 1) % L.length
      have hj : j < L.length := Nat.mod_lt _ (by omega)
      have hi_mem : L[i] ∈ m.primeFactors := hm_list _ (List.getElem_mem hi)
      have hj_mem : L[j] ∈ m.primeFactors := hm_list _ (List.getElem_mem hj)
      obtain ⟨hi_prime, hi_odd, hi_pos, hi_ord⟩ := hmem_prop _ hi_mem
      obtain ⟨hj_prime, hj_odd, hj_pos, _⟩ := hmem_prop _ hj_mem
      have hne_32 : ¬ (L[i] = 3 ∧ m.factorization L[i] = 2) := fun h =>
        h32 L[i] (List.getElem_mem hi) h.1 h.2
      have hdvd_ij : L[j] ^ (2 * m.factorization L[j]) ∣ sigma 1 (L[i] ^ (2 * m.factorization L[i])) := by
        have h1 := hcyclic_step i hi
        rwa [hi_ord] at h1
      have hdec := (full_power_step_decay_of_ne_three_two hi_prime hi_odd hj_prime hj_odd
        hi_pos hj_pos hne_32 hdvd_ij).2.2.1
      have hlt_ij : L[j] ^ (2 * m.factorization L[j]) < L[i] ^ (2 * m.factorization L[i]) := by
        omega
      change L[(t + 1) % L.length] ^ (2 * m.factorization L[(t + 1) % L.length]) <
        L[i] ^ (2 * m.factorization L[i])
      simpa [j, hj_mod] using hlt_ij
    have hg_lt : ∀ n : ℕ, 1 ≤ n → g n < g 0 := by
      intro n hn
      induction n with
      | zero => omega
      | succ k ih =>
        by_cases hk0 : k = 0
        · subst hk0
          exact hg_step 0
        · exact (hg_step k).trans (ih (by omega))
    have hcontra : g L.length < g 0 := hg_lt L.length hlen
    have hg_per : g L.length = g 0 := by
      simp [g]
    omega

/-- **4a. Exponential Telescope Decay Along Open Full-Power Peeling Chains**:
Along any non-empty peeling chain `L` in `m.primeFactors` (for odd `m`) avoiding `(3, 2)`:
- `2 ^ (L.length - 1) * last_pow ≤ head_pow` (strict `<` when `2 ≤ L.length`),
- if every `p ∈ L` satisfies `5 ≤ p`, then `12 ^ (L.length - 1) * last_pow ≤ 5 ^ (L.length - 1) * head_pow`
  (strict `<` when `2 ≤ L.length`),
- if every `p ∈ L` satisfies `53 ≤ p`, then `156 ^ (L.length - 1) * last_pow ≤ 53 ^ (L.length - 1) * head_pow`
  (strict `<` when `2 ≤ L.length`). -/
theorem peeling_chain_exponential_decay {m : ℕ} (hm_odd : Odd m) (L : List ℕ) (hL : L ≠ [])
    (hm_list : ∀ p ∈ L, p ∈ m.primeFactors)
    (hsteps : ∀ i : ℕ, ∀ (hi : i + 1 < L.length),
      L[i + 1] ^ (2 * m.factorization L[i + 1]) ∣ sigma 1 (ordProj[L[i]] (m ^ 2)))
    (hne32 : ∀ p ∈ L, ¬ (p = 3 ∧ m.factorization p = 2)) :
    let P := fun x : ℕ => x ^ (2 * m.factorization x)
    2 ^ (L.length - 1) * P (L.getLast hL) ≤ P (L.head hL) ∧
    (2 ≤ L.length → 2 ^ (L.length - 1) * P (L.getLast hL) < P (L.head hL)) ∧
    ((∀ p ∈ L, 5 ≤ p) →
      12 ^ (L.length - 1) * P (L.getLast hL) ≤ 5 ^ (L.length - 1) * P (L.head hL) ∧
      (2 ≤ L.length → 12 ^ (L.length - 1) * P (L.getLast hL) < 5 ^ (L.length - 1) * P (L.head hL))) ∧
    ((∀ p ∈ L, 53 ≤ p) →
      156 ^ (L.length - 1) * P (L.getLast hL) ≤ 53 ^ (L.length - 1) * P (L.head hL) ∧
      (2 ≤ L.length → 156 ^ (L.length - 1) * P (L.getLast hL) < 53 ^ (L.length - 1) * P (L.head hL))) := by
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  let P : ℕ → ℕ := fun x => x ^ (2 * m.factorization x)
  have hmem_prop : ∀ x ∈ m.primeFactors,
      x.Prime ∧ Odd x ∧ 0 < m.factorization x ∧
      ordProj[x] (m ^ 2) = x ^ (2 * m.factorization x) := by
    intro x hx
    have hx_prime := Nat.prime_of_mem_primeFactors hx
    have hx_dvd := Nat.dvd_of_mem_primeFactors hx
    exact ⟨hx_prime, hm_odd.of_dvd_nat hx_dvd,
      (hx_prime.dvd_iff_one_le_factorization hm0).mp hx_dvd, ordProj_sq_eq_prime_pow hm0⟩
  have h2 := chain_exponential_decay_of_step (m := m) 2 1 (by decide) P
    (fun x => x ∈ L) (fun a b haL hbL hdvd => by
      obtain ⟨ha_p, ha_o, hea, ha_ord⟩ := hmem_prop a (hm_list a haL)
      obtain ⟨hb_p, hb_o, heb, _⟩ := hmem_prop b (hm_list b hbL)
      rw [ha_ord] at hdvd
      have hlt := (full_power_step_decay_of_ne_three_two ha_p ha_o hb_p hb_o hea heb
        (hne32 a haL) hdvd).2.2.1
      simpa [P] using hlt) L hL (fun _ hx => hx) hsteps
  refine ⟨by simpa using h2.1, fun hlen2 => by simpa using h2.2 hlen2, ?_, ?_⟩
  · intro hge5
    exact chain_exponential_decay_of_step (m := m) 12 5 (by decide) P
      (fun x => x ∈ L) (fun a b haL hbL hdvd => by
        obtain ⟨ha_p, ha_o, hea, ha_ord⟩ := hmem_prop a (hm_list a haL)
        obtain ⟨hb_p, hb_o, heb, _⟩ := hmem_prop b (hm_list b hbL)
        rw [ha_ord] at hdvd
        exact (full_power_step_decay_of_ne_three_two ha_p ha_o hb_p hb_o hea heb
          (hne32 a haL) hdvd).2.2.2.1 (hge5 a haL)) L hL (fun _ hx => hx) hsteps
  · intro hge53
    exact chain_exponential_decay_of_step (m := m) 156 53 (by decide) P
      (fun x => x ∈ L) (fun a b haL hbL hdvd => by
        obtain ⟨ha_p, ha_o, hea, ha_ord⟩ := hmem_prop a (hm_list a haL)
        obtain ⟨hb_p, hb_o, heb, _⟩ := hmem_prop b (hm_list b hbL)
        rw [ha_ord] at hdvd
        exact (full_power_step_decay_of_ne_three_two ha_p ha_o hb_p hb_o hea heb
          (hne32 a haL) hdvd).2.2.2.2 (hge53 a haL)) L hL (fun _ hx => hx) hsteps

/-- **4b. Sixth-Power-Free Exponential Telescope Bound**:
On any sixth-power-free odd perfect number `N = q * m ^ 2`, every prime factor of `m` is `≥ 53`,
so any full-power peeling chain `L` of length `≥ 2` in `m.primeFactors` satisfies
`156 ^ (L.length - 1) * (L.getLast hL) ^ (2 * m.factorization (L.getLast hL)) <
  53 ^ (L.length - 1) * (L.head hL) ^ (2 * m.factorization (L.head hL))`. -/
theorem sixth_power_free_peeling_chain_exponential_decay {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (_hq : q.Prime) (_hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (L : List ℕ) (hlen : 2 ≤ L.length) (hm_list : ∀ p ∈ L, p ∈ m.primeFactors)
    (hsteps : ∀ i : ℕ, ∀ (hi : i + 1 < L.length),
      L[i + 1] ^ (2 * m.factorization L[i + 1]) ∣ sigma 1 (ordProj[L[i]] (m ^ 2))) :
    ∀ hL : L ≠ [],
      156 ^ (L.length - 1) * (L.getLast hL) ^ (2 * m.factorization (L.getLast hL)) <
        53 ^ (L.length - 1) * (L.head hL) ^ (2 * m.factorization (L.head hL)) := by
  intro hL
  have hmodd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have h53 : ∀ p ∈ L, 53 ≤ p := by
    intro p hpL
    have hp_m : p ∈ m.primeFactors := hm_list p hpL
    have hp_N : p ∈ N.primeFactors := by
      refine Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp_m, ?_, hN.2.ne'⟩
      rw [hform]
      exact (Nat.dvd_of_mem_primeFactors hp_m).trans
        ((dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
    exact sixth_power_free_min_prime_ge_53 ho hN hfree hp_N
  have hne32 : ∀ p ∈ L, ¬ (p = 3 ∧ m.factorization p = 2) := by
    intro p hpL h
    have := h53 p hpL
    omega
  exact ((peeling_chain_exponential_decay hmodd L hL hm_list hsteps hne32).2.2.2 h53).2 hlen

/-- **5a. Peeling-Cycle Closing Obstruction and Telescope Decay**:
For any linear Euler odd perfect number `N = q * m ^ 2` and any peeling cycle `L` of length `≥ 2`
in `m.primeFactors`:
1. The closing edge cannot absorb the full prime-square power of `L.head`:
   `¬ ((L.head hL) ^ (2 * m.factorization (L.head hL)) ∣ sigma 1 (ordProj[L.getLast hL] (m ^ 2)))`.
2. Therefore `L.head` must either divide `(q + 1) / 2` or divide `sigma 1 (ordProj[p'] (m ^ 2))`
   for a second prime `p' ∈ m.primeFactors` distinct from `L.getLast`.
3. Whenever `(3, 2)` is absent from `L`, `L` satisfies the strict exponential decay
   `2 ^ (L.length - 1) * (L.getLast hL) ^ (2 * m.factorization (L.getLast hL)) < (L.head hL) ^ (2 * m.factorization (L.head hL))`. -/
theorem linear_euler_peeling_cycle_telescope_decay {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (L : List ℕ) (hlen : 2 ≤ L.length) (hm_list : ∀ p ∈ L, p ∈ m.primeFactors)
    (hsteps : ∀ i : ℕ, ∀ (hi : i + 1 < L.length),
      L[i + 1] ^ (2 * m.factorization L[i + 1]) ∣ sigma 1 (ordProj[L[i]] (m ^ 2)))
    (hclose : ∀ hL : L ≠ [], L.head hL ∣ sigma 1 (ordProj[L.getLast hL] (m ^ 2))) :
    ∀ hL : L ≠ [],
      ¬ ((L.head hL) ^ (2 * m.factorization (L.head hL)) ∣
          sigma 1 (ordProj[L.getLast hL] (m ^ 2))) ∧
      (L.head hL ∣ (q + 1) / 2 ∨
        ∃ p' ∈ m.primeFactors, p' ≠ L.getLast hL ∧
          L.head hL ∣ sigma 1 (ordProj[p'] (m ^ 2))) ∧
      ((∀ p ∈ L, ¬ (p = 3 ∧ m.factorization p = 2)) →
        2 ^ (L.length - 1) * (L.getLast hL) ^ (2 * m.factorization (L.getLast hL)) <
          (L.head hL) ^ (2 * m.factorization (L.head hL))) := by
  intro hL
  have _ := hclose
  have hq_odd : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2))
  have hm_odd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have h_not_full : ¬ ((L.head hL) ^ (2 * m.factorization (L.head hL)) ∣
      sigma 1 (ordProj[L.getLast hL] (m ^ 2))) := by
    intro hfull
    exact no_closed_all_full_power_square_cycle hm_odd L (by omega) hm_list
      ⟨hsteps, fun hL' => by
        have h_eq : hL' = hL := Subsingleton.elim _ _
        simpa [h_eq] using hfull⟩
  refine ⟨h_not_full, ?_, fun hne32 => ?_⟩
  · set p₀ := L.head hL
    set pLast := L.getLast hL
    have hp₀_m : p₀ ∈ m.primeFactors := hm_list p₀ (List.head_mem hL)
    have hp₀_prime : p₀.Prime := Nat.prime_of_mem_primeFactors hp₀_m
    have hp₀_odd : Odd p₀ := hm_odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp₀_m)
    have hp₀_ne2 : p₀ ≠ 2 := fun h => by
      rw [h] at hp₀_odd
      exact (by decide : ¬ Odd 2) hp₀_odd
    by_cases h_half : p₀ ∣ (q + 1) / 2
    · exact Or.inl h_half
    · right
      have hq1_even : q + 1 = 2 * ((q + 1) / 2) := by
        have := Nat.odd_iff.mp hq_odd
        omega
      have hp₀_ndvd_q1 : ¬ p₀ ∣ q + 1 := by
        rw [hq1_even]
        intro h
        rcases hp₀_prime.dvd_mul.mp h with h2 | hh
        · exact hp₀_ne2 ((Nat.dvd_prime Nat.prime_two).mp h2 |>.resolve_left hp₀_prime.ne_one)
        · exact h_half hh
      have hsigN : sigma 1 N = 2 * N :=
        (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN)
      have hcop_qm2 : q.Coprime (m ^ 2) := (hq.coprime_iff_not_dvd.mpr hqm).pow_right 2
      have hsigN_split : sigma 1 N = (q + 1) * sigma 1 (m ^ 2) := by
        rw [hform, isMultiplicative_sigma.map_mul_of_coprime hcop_qm2]
        have hsig_q : sigma 1 q = q + 1 := by
          rw [← pow_one q, sigma_one_apply_prime_pow hq]
          simp [Finset.sum_range_succ]
          ring
        rw [hsig_q]
      have hp₀_pow_dvd_m2 : p₀ ^ (2 * m.factorization p₀) ∣ m ^ 2 := by
        rw [← ordProj_sq_eq_prime_pow hm0]
        exact Nat.ordProj_dvd (m ^ 2) p₀
      have hp₀_pow_dvd_sigN : p₀ ^ (2 * m.factorization p₀) ∣ (q + 1) * sigma 1 (m ^ 2) := by
        rw [← hsigN_split, hsigN, hform]
        exact hp₀_pow_dvd_m2.trans (dvd_mul_left (m ^ 2) (2 * q) |> fun h => by
          simpa [mul_assoc] using h)
      have hcop_pow_q1 : (p₀ ^ (2 * m.factorization p₀)).Coprime (q + 1) :=
        (hp₀_prime.coprime_iff_not_dvd.mpr hp₀_ndvd_q1).pow_left _
      have hp₀_pow_dvd_sigm2 : p₀ ^ (2 * m.factorization p₀) ∣ sigma 1 (m ^ 2) :=
        hcop_pow_q1.dvd_of_dvd_mul_left hp₀_pow_dvd_sigN
      have hpLast_m : pLast ∈ m.primeFactors := hm_list pLast (List.getLast_mem hL)
      have hpLast_prime : pLast.Prime := Nat.prime_of_mem_primeFactors hpLast_m
      let B_last := ordCompl[pLast] (m ^ 2)
      have hm2_split : m ^ 2 = ordProj[pLast] (m ^ 2) * B_last :=
        (Nat.ordProj_mul_ordCompl_eq_self (m ^ 2) pLast).symm
      have hm2_cop : (ordProj[pLast] (m ^ 2)).Coprime B_last :=
        (Nat.coprime_ordCompl hpLast_prime hm20).pow_left _
      have hsigm2_split : sigma 1 (m ^ 2) = sigma 1 (ordProj[pLast] (m ^ 2)) * sigma 1 B_last := by
        conv_lhs => rw [hm2_split, isMultiplicative_sigma.map_mul_of_coprime hm2_cop]
      have hp₀_dvd_B_last : p₀ ∣ sigma 1 B_last := by
        by_contra hndvd
        have hcop_pow_Blast : (p₀ ^ (2 * m.factorization p₀)).Coprime (sigma 1 B_last) :=
          (hp₀_prime.coprime_iff_not_dvd.mpr hndvd).pow_left _
        rw [hsigm2_split] at hp₀_pow_dvd_sigm2
        exact h_not_full (hcop_pow_Blast.dvd_of_dvd_mul_right hp₀_pow_dvd_sigm2)
      have hB_last_odd : Odd B_last := hm_odd.pow.of_dvd_nat (Nat.ordCompl_dvd (m ^ 2) pLast)
      have hB_last0 : B_last ≠ 0 := hB_last_odd.pos.ne'
      have hsig_Blast_prod : sigma 1 B_last = ∏ p' ∈ B_last.primeFactors, sigma 1 (ordProj[p'] B_last) := by
        rw [isMultiplicative_sigma.multiplicative_factorization (sigma 1) hB_last0]
        exact Finset.prod_congr B_last.support_factorization fun _ _ => rfl
      obtain ⟨p', hp'B, hp₀_dvd_p'⟩ := by
        rw [hsig_Blast_prod] at hp₀_dvd_B_last
        exact (hp₀_prime.prime.dvd_finsetProd_iff _).mp hp₀_dvd_B_last
      have hp'_prime : p'.Prime := Nat.prime_of_mem_primeFactors hp'B
      have hp'_dvd_m2 : p' ∣ m ^ 2 :=
        (Nat.dvd_of_mem_primeFactors hp'B).trans (Nat.ordCompl_dvd (m ^ 2) pLast)
      have hp'_m : p' ∈ m.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp'_prime, hp'_prime.dvd_of_dvd_pow hp'_dvd_m2, hm0⟩
      have hp'_ne : p' ≠ pLast := by
        intro heq
        subst heq
        exact (Nat.not_dvd_ordCompl hpLast_prime hm20) (Nat.dvd_of_mem_primeFactors hp'B)
      have h_ord_eq : ordProj[p'] (m ^ 2) = ordProj[p'] B_last := by
        have hfact : (m ^ 2).factorization p' = B_last.factorization p' := by
          have h1 : (m ^ 2).factorization p' =
              (ordProj[pLast] (m ^ 2)).factorization p' + B_last.factorization p' := by
            conv_lhs => rw [hm2_split]
            rw [Nat.factorization_mul (pow_ne_zero _ hpLast_prime.ne_zero) hB_last0, Finsupp.add_apply]
          have h2 : (ordProj[pLast] (m ^ 2)).factorization p' = 0 := by
            rw [hpLast_prime.factorization_pow, Finsupp.single_eq_of_ne hp'_ne]
          omega
        rw [hfact]
      refine ⟨p', hp'_m, hp'_ne, ?_⟩
      rwa [h_ord_eq]
  · exact (peeling_chain_exponential_decay hm_odd L hL hm_list hsteps hne32).2.1 hlen

/-- **5b. Unconditional Global Collapse of the Peeling-Cycle Branch**:
On EVERY linear Euler odd perfect number `N = q * m ^ 2`, the third branch (`σ`-cycle without
collision or half-successor hit) of `linear_euler_peeling_collision_or_cycle` is unconditionally
impossible: every such `N` admits either a prime collision between two distinct prime components
of `m` or a prime `p ∈ m.primeFactors` dividing `(q + 1) / 2`. -/
theorem linear_euler_collision_or_half_succ_hit {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    (∃ r' : ℕ, r'.Prime ∧
      ∃ p₁ ∈ m.primeFactors, ∃ p₂ ∈ m.primeFactors,
        p₁ ≠ p₂ ∧
        r' ∣ sigma 1 (ordProj[p₁] (m ^ 2)) ∧
        r' ∣ sigma 1 (ordProj[p₂] (m ^ 2))) ∨
    (∃ p ∈ m.primeFactors, p ∣ (q + 1) / 2) := by
  rcases linear_euler_peeling_collision_or_cycle ho hN hq hqm hform with hcoll | hhalf | hcyc
  · exact Or.inl hcoll
  · exact Or.inr hhalf
  · obtain ⟨L, hlen, _, hm_list, hsteps, hclose⟩ := hcyc
    have hL : L ≠ [] := List.ne_nil_of_length_pos (by omega)
    obtain ⟨_, hbranch, _⟩ :=
      linear_euler_peeling_cycle_telescope_decay ho hN hq hqm hform L hlen hm_list hsteps hclose hL
    rcases hbranch with h_head_half | ⟨p', hp'_m, hp'_ne, hp₀_dvd_p'⟩
    · exact Or.inr ⟨L.head hL, hm_list _ (List.head_mem hL), h_head_half⟩
    · left
      have hp₀_m : L.head hL ∈ m.primeFactors := hm_list _ (List.head_mem hL)
      have hp₀_prime : (L.head hL).Prime := Nat.prime_of_mem_primeFactors hp₀_m
      have hpLast_m : L.getLast hL ∈ m.primeFactors := hm_list _ (List.getLast_mem hL)
      exact ⟨L.head hL, hp₀_prime, p', hp'_m, L.getLast hL, hpLast_m, hp'_ne, hp₀_dvd_p', hclose hL⟩

end OddPerfect
