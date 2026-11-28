module

public import OddPerfect.TripleRepunitObstruction
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- The same integer has prime-length repunit representations in four
distinct odd prime bases. -/
@[expose] def HasFourOddPrimeRepunits (z : ℕ) : Prop :=
  ∃ r₁ r₂ r₃ r₄ l₁ l₂ l₃ l₄ : ℕ,
    r₁.Prime ∧ Odd r₁ ∧ r₂.Prime ∧ Odd r₂ ∧ r₃.Prime ∧ Odd r₃ ∧ r₄.Prime ∧ Odd r₄ ∧
    r₁ ≠ r₂ ∧ r₁ ≠ r₃ ∧ r₁ ≠ r₄ ∧ r₂ ≠ r₃ ∧ r₂ ≠ r₄ ∧ r₃ ≠ r₄ ∧
    l₁.Prime ∧ 2 < l₁ ∧ l₂.Prime ∧ 2 < l₂ ∧ l₃.Prime ∧ 2 < l₃ ∧ l₄.Prime ∧ 2 < l₄ ∧
    geometricBlock r₁ l₁ = z ∧ geometricBlock r₂ l₂ = z ∧
    geometricBlock r₃ l₃ = z ∧ geometricBlock r₄ l₄ = z

private lemma two_mul_add_one_lt_three_pow {e : ℕ} (he : 1 ≤ e) :
    2 * e + 1 < 3 ^ (2 * e) := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    calc 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
      _ < 3 ^ (2 * k) + 2 := by omega
      _ < 9 * 3 ^ (2 * k) := by
        have hpos : 1 ≤ 3 ^ (2 * k) := Nat.one_le_pow _ _ (by decide)
        omega
      _ = 3 ^ (2 * (k + 1)) := by ring

private lemma add_pow_of_sq_eq_zero {R : Type*} [CommRing R] (a b : R) (hb : b ^ 2 = 0) :
    ∀ m : ℕ, 1 ≤ m → (a + b) ^ m = a ^ m + (m : R) * a ^ (m - 1) * b := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    rcases eq_or_ne m 0 with rfl | hm0
    · simp
    · have ih' := ih (by omega)
      rw [pow_succ, ih']
      simp only [Nat.add_sub_cancel]
      have hsucc : m - 1 + 1 = m := by omega
      have hpow : a * a ^ (m - 1) = a ^ m := by rw [← pow_succ', hsucc]
      push_cast
      calc (a ^ m + (m : R) * a ^ (m - 1) * b) * (a + b)
          = a ^ m * a + (a ^ m + (m : R) * (a * a ^ (m - 1))) * b + (m : R) * a ^ (m - 1) * b ^ 2 := by
            ring
        _ = a ^ (m + 1) + ((m : R) + 1) * a ^ m * b := by
            rw [hpow, hb, mul_zero, add_zero, ← pow_succ]; ring

private lemma add_pow_of_cube_eq_zero {R : Type*} [CommRing R] (a b : R) (hb : b ^ 3 = 0) :
    ∀ m : ℕ, 2 ≤ m →
      (a + b) ^ m = a ^ m + (m : R) * a ^ (m - 1) * b + (Nat.choose m 2 : R) * a ^ (m - 2) * b ^ 2 := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    norm_num [Nat.choose_self]
    ring
  | succ k hk ih =>
    have h1 : k - 1 + 1 = k := by omega
    have h2 : k - 2 + 1 = k - 1 := by omega
    have hpow1 : a ^ (k - 1) * a = a ^ k := by rw [← pow_succ, h1]
    have hpow2 : a ^ (k - 2) * a = a ^ (k - 1) := by rw [← pow_succ, h2]
    have hch : Nat.choose (k + 1) 2 = Nat.choose k 2 + k := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      ring
    rw [pow_succ, ih, show k + 1 - 1 = k by omega, show k + 1 - 2 = k - 1 by omega, hch]
    push_cast
    calc (a ^ k + (k : R) * a ^ (k - 1) * b + (Nat.choose k 2 : R) * a ^ (k - 2) * b ^ 2) * (a + b)
        = a ^ k * a + (a ^ k + (k : R) * (a ^ (k - 1) * a)) * b +
            ((k : R) * a ^ (k - 1) + (Nat.choose k 2 : R) * (a ^ (k - 2) * a)) * b ^ 2 +
            (Nat.choose k 2 : R) * a ^ (k - 2) * b ^ 3 := by ring
      _ = a ^ (k + 1) + ((k : R) + 1) * a ^ k * b +
            ((Nat.choose k 2 : R) + (k : R)) * a ^ (k - 1) * b ^ 2 := by
          rw [hpow1, hpow2, hb, mul_zero, add_zero, ← pow_succ]
          ring

private lemma prod_one_add_mul_sq_eq_zero {R : Type*} [CommRing R] (b : R) (hb : b ^ 2 = 0)
    (A : Finset ℕ) (c : ℕ → R) :
    ∏ r ∈ A, (1 + c r * b) = 1 + (∑ r ∈ A, c r) * b := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
    calc (1 + c a * b) * (1 + (∑ r ∈ s, c r) * b)
        = 1 + (c a + ∑ r ∈ s, c r) * b + c a * (∑ r ∈ s, c r) * b ^ 2 := by ring
      _ = 1 + (c a + ∑ r ∈ s, c r) * b := by rw [hb, mul_zero, add_zero]

private lemma linear_lt_even_pow {r e : ℕ} (hr : 3 ≤ r) (he : 2 ≤ e) :
    4 * e * r ≤ r ^ (2 * e) := by
  induction e, he using Nat.le_induction with
  | base =>
    have h1 : 8 ≤ r ^ 3 := by
      rw [show r ^ 3 = r * r * r by ring]
      nlinarith
    calc 4 * 2 * r = 8 * r := by ring
      _ ≤ r ^ 3 * r := Nat.mul_le_mul_right r h1
      _ = r ^ (2 * 2) := by ring
  | succ k hk ih =>
    have h2 : 2 * (k + 1) ≤ 4 * k := by omega
    have h9 : 9 ≤ r ^ 2 := by rw [pow_two]; nlinarith
    calc 4 * (k + 1) * r ≤ 2 * (4 * k * r) := by nlinarith
      _ ≤ 2 * r ^ (2 * k) := Nat.mul_le_mul_left 2 ih
      _ ≤ r ^ 2 * r ^ (2 * k) := Nat.mul_le_mul_right _ (by omega)
      _ = r ^ (2 * (k + 1)) := by ring

private lemma sixteen_mul_odd_pow4_le_three_pow {e : ℕ} (he : 6 ≤ e) :
    16 * (2 * e + 1) ^ 4 ≤ 3 ^ (2 * e) := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hsq : (2 * (k + 1) + 1) ^ 2 ≤ 3 * (2 * k + 1) ^ 2 := by nlinarith
    have hpow4 : (2 * (k + 1) + 1) ^ 4 ≤ 9 * (2 * k + 1) ^ 4 := by
      calc (2 * (k + 1) + 1) ^ 4 = ((2 * (k + 1) + 1) ^ 2) ^ 2 := by ring
        _ ≤ (3 * (2 * k + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left hsq 2
        _ = 9 * (2 * k + 1) ^ 4 := by ring
    calc 16 * (2 * (k + 1) + 1) ^ 4
        ≤ 9 * (16 * (2 * k + 1) ^ 4) := by nlinarith
      _ ≤ 9 * 3 ^ (2 * k) := Nat.mul_le_mul_left 9 ih
      _ = 3 ^ (2 * (k + 1)) := by ring

private lemma thirty_six_mul_odd_pow6_le_three_pow {e : ℕ} (he : 10 ≤ e) :
    36 * (2 * e + 1) ^ 6 ≤ 3 ^ (2 * e) := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hsq : (2 * (k + 1) + 1) ^ 2 ≤ 2 * (2 * k + 1) ^ 2 := by nlinarith
    have hpow6 : (2 * (k + 1) + 1) ^ 6 ≤ 9 * (2 * k + 1) ^ 6 := by
      calc (2 * (k + 1) + 1) ^ 6 = ((2 * (k + 1) + 1) ^ 2) ^ 3 := by ring
        _ ≤ (2 * (2 * k + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left hsq 3
        _ = 8 * (2 * k + 1) ^ 6 := by ring
        _ ≤ 9 * (2 * k + 1) ^ 6 := Nat.mul_le_mul_right _ (by decide : 8 ≤ 9)
    calc 36 * (2 * (k + 1) + 1) ^ 6
        ≤ 9 * (36 * (2 * k + 1) ^ 6) := by nlinarith
      _ ≤ 9 * 3 ^ (2 * k) := Nat.mul_le_mul_left 9 ih
      _ = 3 ^ (2 * (k + 1)) := by ring

private lemma sigma_prime_pow_strictMono_exp {r a b : ℕ} (hr : r.Prime) (hab : a < b) :
    sigma 1 (r ^ a) < sigma 1 (r ^ b) := by
  rw [sigma_one_apply_prime_pow hr, sigma_one_apply_prime_pow hr]
  have hsub : range (a + 1) ⊆ range b := Finset.range_mono (by omega : a + 1 ≤ b)
  have hle : ∑ j ∈ range (a + 1), r ^ j ≤ ∑ j ∈ range b, r ^ j :=
    Finset.sum_le_sum_of_subset hsub
  have hlt : ∑ j ∈ range b, r ^ j < ∑ j ∈ range (b + 1), r ^ j := by
    rw [Finset.sum_range_succ]
    have hpos : 0 < r ^ b := pow_pos hr.pos b
    omega
  exact Nat.lt_of_le_of_lt hle hlt

private lemma sigma_prime_pow_lt_of_base_lt {a b e : ℕ} (ha : a.Prime) (hb : b.Prime)
    (hab : a < b) (he : 0 < e) : sigma 1 (a ^ e) < sigma 1 (b ^ e) := by
  rw [sigma_one_apply_prime_pow ha, sigma_one_apply_prime_pow hb]
  exact Finset.sum_lt_sum (fun j _ => Nat.pow_le_pow_left hab.le j)
    ⟨1, Finset.mem_range.mpr (by omega), by simpa using hab⟩

/-- Every single-copy cofactor prime `r ∈ S₁` has repunit length `l_r = 2 * v_r(s) + 1`
satisfying `2 * l_r ∣ p - 1`, and the product of all such prime lengths divides `(p - 1) / 2`. -/
theorem even_index_repunit_lengths_dvd_pred {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    let S₁ := s.primeFactors.filter (v · = 1)
    (∀ r ∈ S₁, 2 * (2 * s.factorization r + 1) ∣ p - 1) ∧
      (∏ r ∈ S₁, (2 * s.factorization r + 1)) ∣ (p - 1) / 2 := by
  intro v S₁
  have hp_pred : 2 * ((p - 1) / 2) = p - 1 := by
    have := Nat.odd_iff.mp hpo
    omega
  have hdvd_half : ∀ r ∈ S₁, 2 * s.factorization r + 1 ∣ (p - 1) / 2 := by
    intro r hrS
    obtain ⟨hr, _⟩ := Finset.mem_filter.mp hrS
    exact (even_index_cofactor_component_order_dvd_pred hp hpo hs hσq hplus hσs hr).2.2.2
  refine ⟨fun r hrS => ?_, ?_⟩
  · rw [← hp_pred]
    exact Nat.mul_dvd_mul_left 2 (hdvd_half r hrS)
  · obtain ⟨_, hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
    have hcop_pair : ∀ r₁ ∈ S₁, ∀ r₂ ∈ S₁, r₁ ≠ r₂ →
        Nat.Coprime (2 * s.factorization r₁ + 1) (2 * s.factorization r₂ + 1) := by
      intro r₁ hr₁S r₂ hr₂S hne
      obtain ⟨hr₁, hv₁⟩ := Finset.mem_filter.mp hr₁S
      obtain ⟨hr₂, hv₂⟩ := Finset.mem_filter.mp hr₂S
      have hr₁p := Nat.prime_of_mem_primeFactors hr₁
      have hr₂p := Nat.prime_of_mem_primeFactors hr₂
      have hr₁s := Nat.dvd_of_mem_primeFactors hr₁
      have hr₁e : 1 ≤ s.factorization r₁ := (hr₁p.dvd_iff_one_le_factorization hs.pos.ne').mp hr₁s
      have hσ₁ : sigma 1 (r₁ ^ (2 * s.factorization r₁)) = p := by
        have H := (hparts r₁ hr₁).2
        dsimp only at H
        change sigma 1 (r₁ ^ (2 * s.factorization r₁)) = p ^ v r₁ at H
        rwa [hv₁, pow_one] at H
      have hσ₂ : sigma 1 (r₂ ^ (2 * s.factorization r₂)) = p := by
        have H := (hparts r₂ hr₂).2
        dsimp only at H
        change sigma 1 (r₂ ^ (2 * s.factorization r₂)) = p ^ v r₂ at H
        rwa [hv₂, pow_one] at H
      have he_ne : s.factorization r₁ ≠ s.factorization r₂ := by
        intro heq
        rw [← heq] at hσ₂
        rcases Nat.lt_trichotomy r₁ r₂ with hlt | rfl | hgt
        · have := sigma_prime_pow_lt_of_base_lt hr₁p hr₂p hlt (by omega : 0 < 2 * s.factorization r₁)
          omega
        · exact hne rfl
        · have := sigma_prime_pow_lt_of_base_lt hr₂p hr₁p hgt (by omega : 0 < 2 * s.factorization r₁)
          omega
      have hl₁p := (even_index_cofactor_component_order_dvd_pred hp hpo hs hσq hplus hσs hr₁).1
      have hl₂p := (even_index_cofactor_component_order_dvd_pred hp hpo hs hσq hplus hσs hr₂).1
      exact (Nat.coprime_primes hl₁p hl₂p).mpr (by omega)
    suffices h : ∀ T ⊆ S₁, (∏ r ∈ T, (2 * s.factorization r + 1)) ∣ (p - 1) / 2 from
      h S₁ Subset.rfl
    intro T hT
    induction T using Finset.induction_on with
    | empty => simp
    | @insert a U ha ih =>
      have haS : a ∈ S₁ := hT (Finset.mem_insert_self a U)
      have hUS : U ⊆ S₁ := fun x hx => hT (Finset.mem_insert_of_mem hx)
      rw [Finset.prod_insert ha]
      have hcopU : Nat.Coprime (2 * s.factorization a + 1) (∏ r ∈ U, (2 * s.factorization r + 1)) := by
        apply Nat.coprime_prod_right_iff.mpr
        intro r hrU
        exact hcop_pair a haS r (hUS hrU) (fun heq => ha (heq ▸ hrU))
      exact hcopU.mul_dvd_of_dvd_of_dvd (hdvd_half a haS) (ih hUS)

/-- Second-order `ZMod (p ^ 3)` divisor-power congruence on the single-copy primes `S₁`.
Every `r ∉ S₁` has `v_p(σ(r^(2 e_r))) ≥ 3`, so its local factor collapses to `1` modulo `p ^ 3`. -/
theorem even_index_mod_p_cube_congruence {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    let S₁ := s.primeFactors.filter (v · = 1)
    let T := (s ^ 2).divisors.card
    let m (r : ℕ) := 2 * s.factorization r * (∏ t ∈ s.primeFactors.erase r, (2 * s.factorization t + 1))
    (2 : ZMod (p ^ 3)) ^ T *
      (∏ r ∈ S₁, (1 + ((m r * (r - 1) : ℕ) : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) +
        ((Nat.choose (m r) 2 * (r - 1) ^ 2 : ℕ) : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) ^ 2)) =
      (2 : ZMod (p ^ 3)) ^ T + (T : ZMod (p ^ 3)) * (2 : ZMod (p ^ 3)) ^ (T - 1) *
        ((p : ZMod (p ^ 3)) + (p : ZMod (p ^ 3)) ^ 2) +
      (Nat.choose T 2 : ZMod (p ^ 3)) * (2 : ZMod (p ^ 3)) ^ (T - 2) * (p : ZMod (p ^ 3)) ^ 2 := by
  intro v S₁ T m
  let R := ZMod (p ^ 3)
  obtain ⟨_, hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  have hp3_zero : (p : R) ^ 3 = 0 := by
    change (p : ZMod (p ^ 3)) ^ 3 = 0
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hT_prod : T = ∏ r ∈ s.primeFactors, (2 * s.factorization r + 1) := by
    dsimp [T]
    rw [Nat.card_divisors (pow_ne_zero 2 hs.pos.ne'), Nat.primeFactors_pow s (by decide : 2 ≠ 0)]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hq_ge13 : 13 ≤ q := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le; have := Nat.odd_iff.mp hpo; omega
    have hrange : range 3 ⊆ range (2 * u + 1) := Finset.range_mono (by omega : 3 ≤ 2 * u + 1)
    have hsum : 1 + p + p ^ 2 ≤ q := by
      rw [← hσq, sigma_one_apply_prime_pow hp]
      calc 1 + p + p ^ 2 = ∑ j ∈ range 3, p ^ j := by
            simp [Finset.sum_range_succ, Nat.add_assoc]
        _ ≤ ∑ j ∈ range (2 * u + 1), p ^ j := Finset.sum_le_sum_of_subset hrange
    nlinarith
  have hs_gt1 : 1 < s := by
    by_contra! hs1
    have hs_eq1 : s = 1 := by have := hs.pos; omega
    rw [hs_eq1] at hplus
    omega
  have hT_ge2 : 2 ≤ T := by
    obtain ⟨r₀, hr₀⟩ := Nat.exists_prime_and_dvd hs_gt1.ne'
    have hr₀_mem : r₀ ∈ s.primeFactors := Nat.mem_primeFactors.mpr ⟨hr₀.1, hr₀.2, hs.pos.ne'⟩
    have hfac : 1 ≤ s.factorization r₀ := (hr₀.1.dvd_iff_one_le_factorization hs.pos.ne').mp hr₀.2
    have hT_ge : 2 * s.factorization r₀ + 1 ≤ T := by
      rw [hT_prod, ← Finset.mul_prod_erase s.primeFactors _ hr₀_mem]
      have hprod_pos : 1 ≤ ∏ t ∈ s.primeFactors.erase r₀, (2 * s.factorization t + 1) :=
        Finset.one_le_prod fun _ _ => by omega
      nlinarith
    omega
  have hq_cast : (q : R) = 1 + (p : R) + (p : R) ^ 2 := by
    have hq_expand : q = 1 + p + p ^ 2 + p ^ 3 * ∑ j ∈ range (2 * u - 2), p ^ j := by
      rw [← hσq, sigma_one_apply_prime_pow hp, show 2 * u + 1 = (2 * u - 2) + 3 by omega,
        Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [pow_zero, pow_succ', ← Finset.mul_sum]
      ring
    have hcast := congrArg (fun n : ℕ => (n : R)) hq_expand
    push_cast at hcast
    rw [hp3_zero, zero_mul, add_zero] at hcast
    exact hcast
  have h2s2_cast : (2 : R) * (s ^ 2 : R) = 2 + ((p : R) + (p : R) ^ 2) := by
    have hcast := congrArg (fun n : ℕ => (n : R)) hplus
    push_cast at hcast
    rw [hq_cast] at hcast
    linear_combination -hcast
  have hb_sq : ((p : R) + (p : R) ^ 2) ^ 2 = (p : R) ^ 2 := by
    calc ((p : R) + (p : R) ^ 2) ^ 2
        = (p : R) ^ 2 + 2 * (p : R) ^ 3 + (p : R) ^ 3 * (p : R) := by ring
      _ = (p : R) ^ 2 := by rw [hp3_zero, mul_zero, zero_mul, add_zero, add_zero]
  have hb_cube : ((p : R) + (p : R) ^ 2) ^ 3 = 0 := by
    calc ((p : R) + (p : R) ^ 2) ^ 3
        = (p : R) ^ 3 * (1 + 3 * (p : R) + 3 * (p : R) ^ 2 + (p : R) ^ 3) := by ring
      _ = 0 := by rw [hp3_zero, zero_mul]
  have hpow_T : (2 : R) ^ T * ((s ^ 2 : ℕ) : R) ^ T =
      (2 : R) ^ T + (T : R) * (2 : R) ^ (T - 1) * ((p : R) + (p : R) ^ 2) +
        (Nat.choose T 2 : R) * (2 : R) ^ (T - 2) * (p : R) ^ 2 := by
    calc (2 : R) ^ T * ((s ^ 2 : ℕ) : R) ^ T
        = ((2 : R) * (s ^ 2 : R)) ^ T := by push_cast; ring
      _ = (2 + ((p : R) + (p : R) ^ 2)) ^ T := by rw [h2s2_cast]
      _ = (2 : R) ^ T + (T : R) * (2 : R) ^ (T - 1) * ((p : R) + (p : R) ^ 2) +
            (Nat.choose T 2 : R) * (2 : R) ^ (T - 2) * ((p : R) + (p : R) ^ 2) ^ 2 :=
          add_pow_of_cube_eq_zero 2 ((p : R) + (p : R) ^ 2) hb_cube T hT_ge2
      _ = (2 : R) ^ T + (T : R) * (2 : R) ^ (T - 1) * ((p : R) + (p : R) ^ 2) +
            (Nat.choose T 2 : R) * (2 : R) ^ (T - 2) * (p : R) ^ 2 := by rw [hb_sq]
  have hs2_prod : s ^ 2 = ∏ r ∈ s.primeFactors, r ^ (2 * s.factorization r) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization (pow_ne_zero 2 hs.pos.ne')]
    rw [Nat.primeFactors_pow s (by decide : 2 ≠ 0)]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hs2_pow_T : ((s ^ 2 : ℕ) : R) ^ T =
      ∏ r ∈ s.primeFactors, ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T := by
    conv_lhs => rw [hs2_prod]
    push_cast
    rw [Finset.prod_pow]
  have hlocal_not : ∀ r ∈ s.primeFactors, v r ≠ 1 →
      ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T = 1 := by
    intro r hr hvne
    obtain ⟨hvo, hσr⟩ := hparts r hr
    dsimp only at hvo hσr
    change Odd (v r) at hvo
    change sigma 1 (r ^ (2 * s.factorization r)) = p ^ v r at hσr
    have hv3 : 3 ≤ v r := by
      have := Nat.odd_iff.mp hvo
      omega
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hrel : r ^ (2 * s.factorization r + 1) = 1 + (r - 1) * p ^ (v r) := by
      rw [← hσr, sigma_one_apply_prime_pow hrp]
      zify [hrp.one_le]
      have hg := geom_sum_mul (r : ℤ) (2 * s.factorization r + 1)
      linarith
    have hrcast : ((r ^ (2 * s.factorization r + 1) : ℕ) : R) = 1 := by
      rw [hrel]
      push_cast
      have hpv : (p : R) ^ v r = 0 := by
        rw [show v r = 3 + (v r - 3) by omega, pow_add, hp3_zero, zero_mul]
      rw [hpv, mul_zero, add_zero]
    obtain ⟨Q, hTQ⟩ := (Finset.dvd_prod_of_mem (fun t => 2 * s.factorization t + 1) hr).trans
      hT_prod.symm.dvd
    calc ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T
        = ((r ^ (2 * s.factorization r) : ℕ) : R) ^ ((2 * s.factorization r + 1) * Q) := by rw [hTQ]
      _ = ((r ^ (2 * s.factorization r + 1) : ℕ) : R) ^ (2 * s.factorization r * Q) := by
        push_cast; ring
      _ = 1 ^ (2 * s.factorization r * Q) := by rw [hrcast]
      _ = 1 := one_pow _
  have hlocal_mem : ∀ r ∈ S₁,
      ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T =
        1 + ((m r * (r - 1) : ℕ) : R) * (p : R) +
          ((Nat.choose (m r) 2 * (r - 1) ^ 2 : ℕ) : R) * (p : R) ^ 2 := by
    intro r hrS
    obtain ⟨hr, hv1⟩ := Finset.mem_filter.mp hrS
    obtain ⟨_, hσr⟩ := hparts r hr
    dsimp only at hσr
    change sigma 1 (r ^ (2 * s.factorization r)) = p ^ v r at hσr
    rw [hv1, pow_one] at hσr
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hrs := Nat.dvd_of_mem_primeFactors hr
    have hepos : 1 ≤ s.factorization r := (hrp.dvd_iff_one_le_factorization hs.pos.ne').mp hrs
    have hrel : r ^ (2 * s.factorization r + 1) = 1 + (r - 1) * p := by
      rw [← hσr, sigma_one_apply_prime_pow hrp]
      zify [hrp.one_le]
      have hg := geom_sum_mul (r : ℤ) (2 * s.factorization r + 1)
      linarith
    have hrcast : ((r ^ (2 * s.factorization r + 1) : ℕ) : R) = 1 + ((r - 1 : ℕ) : R) * (p : R) := by
      rw [hrel]
      push_cast
      rfl
    set Q := ∏ t ∈ s.primeFactors.erase r, (2 * s.factorization t + 1)
    have hTQ : T = (2 * s.factorization r + 1) * Q := by
      rw [hT_prod]
      exact (Finset.mul_prod_erase s.primeFactors (fun t => 2 * s.factorization t + 1) hr).symm
    have hm_eq : m r = 2 * s.factorization r * Q := rfl
    have hQpos : 1 ≤ Q := Finset.one_le_prod fun _ _ => by omega
    have hm_ge2 : 2 ≤ m r := by rw [hm_eq]; nlinarith
    have hb3 : (((r - 1 : ℕ) : R) * (p : R)) ^ 3 = 0 := by
      calc (((r - 1 : ℕ) : R) * (p : R)) ^ 3 = ((r - 1 : ℕ) : R) ^ 3 * (p : R) ^ 3 := by ring
        _ = 0 := by rw [hp3_zero, mul_zero]
    calc ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T
        = ((r ^ (2 * s.factorization r) : ℕ) : R) ^ ((2 * s.factorization r + 1) * Q) := by rw [hTQ]
      _ = ((r ^ (2 * s.factorization r + 1) : ℕ) : R) ^ (m r) := by
        rw [hm_eq]; push_cast; ring
      _ = (1 + ((r - 1 : ℕ) : R) * (p : R)) ^ (m r) := by rw [hrcast]
      _ = 1 ^ (m r) + (m r : R) * 1 ^ (m r - 1) * (((r - 1 : ℕ) : R) * (p : R)) +
            (Nat.choose (m r) 2 : R) * 1 ^ (m r - 2) * (((r - 1 : ℕ) : R) * (p : R)) ^ 2 :=
          add_pow_of_cube_eq_zero 1 (((r - 1 : ℕ) : R) * (p : R)) hb3 (m r) hm_ge2
      _ = 1 + ((m r * (r - 1) : ℕ) : R) * (p : R) +
            ((Nat.choose (m r) 2 * (r - 1) ^ 2 : ℕ) : R) * (p : R) ^ 2 := by
          simp only [one_pow, mul_one, Nat.cast_mul, Nat.cast_pow]; ring
  have hs2_S1 : ((s ^ 2 : ℕ) : R) ^ T =
      ∏ r ∈ S₁, (1 + ((m r * (r - 1) : ℕ) : R) * (p : R) +
        ((Nat.choose (m r) 2 * (r - 1) ^ 2 : ℕ) : R) * (p : R) ^ 2) := by
    rw [hs2_pow_T, ← Finset.prod_filter_mul_prod_filter_not s.primeFactors (fun r => v r = 1)]
    have hnot : (∏ r ∈ s.primeFactors.filter (fun r => ¬ v r = 1),
        ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T) = 1 := by
      refine Finset.prod_eq_one fun r hr => ?_
      obtain ⟨hr_pf, hnv⟩ := Finset.mem_filter.mp hr
      exact hlocal_not r hr_pf hnv
    rw [hnot, mul_one]
    exact Finset.prod_congr rfl fun r hr => hlocal_mem r hr
  rw [hs2_S1] at hpow_T
  exact hpow_T

private lemma even_index_S1_nonempty_and_p_le_L {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    let S₁ := s.primeFactors.filter (v · = 1)
    let L := (∑ r ∈ S₁, 4 * s.factorization r * (r - 1) *
      ∏ t ∈ S₁.erase r, (2 * s.factorization t + 1)) - ∏ t ∈ S₁, (2 * s.factorization t + 1)
    S₁.Nonempty ∧ 0 < L ∧ p ≤ L := by
  intro v S₁ L
  let R := ZMod (p ^ 2)
  let T := (s ^ 2).divisors.card
  let l (t : ℕ) := 2 * s.factorization t + 1
  obtain ⟨_, hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  have hT_prod : T = ∏ r ∈ s.primeFactors, l r := by
    dsimp [T, l]
    rw [Nat.card_divisors (pow_ne_zero 2 hs.pos.ne'), Nat.primeFactors_pow s (by decide : 2 ≠ 0)]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hT_pos : 1 ≤ T := by
    dsimp [T]
    exact Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (pow_ne_zero 2 hs.pos.ne')⟩
  have hT_cop : p.Coprime T := by
    rw [hT_prod]
    apply Nat.coprime_prod_right_iff.mpr
    intro r hr
    exact hp.coprime_iff_not_dvd.mpr
      (even_index_cofactor_component_order_dvd_pred hp hpo hs hσq hplus hσs hr).2.1
  have hp2_zero : (p : R) ^ 2 = 0 := by
    change (p : ZMod (p ^ 2)) ^ 2 = 0
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hq_cast : (q : R) = 1 + (p : R) := by
    have hq_expand : q = 1 + p + p ^ 2 * ∑ j ∈ range (2 * u - 1), p ^ j := by
      rw [← hσq, sigma_one_apply_prime_pow hp, show 2 * u + 1 = (2 * u - 1) + 2 by omega,
        Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [pow_zero, pow_succ', ← Finset.mul_sum]
      ring
    have hcast := congrArg (fun n : ℕ => (n : R)) hq_expand
    push_cast at hcast
    rw [hp2_zero, zero_mul, add_zero] at hcast
    exact hcast
  have h2s2_cast : (2 : R) * (s ^ 2 : R) = 2 + (p : R) := by
    have hcast := congrArg (fun n : ℕ => (n : R)) hplus
    push_cast at hcast
    rw [hq_cast] at hcast
    linear_combination -hcast
  have hpow_T : (2 : R) ^ T * ((s ^ 2 : ℕ) : R) ^ T =
      (2 : R) ^ T + (T : R) * (2 : R) ^ (T - 1) * (p : R) := by
    calc (2 : R) ^ T * ((s ^ 2 : ℕ) : R) ^ T
        = ((2 : R) * (s ^ 2 : R)) ^ T := by push_cast; ring
      _ = (2 + (p : R)) ^ T := by rw [h2s2_cast]
      _ = (2 : R) ^ T + (T : R) * (2 : R) ^ (T - 1) * (p : R) :=
        add_pow_of_sq_eq_zero 2 (p : R) hp2_zero T hT_pos
  have hs2_prod : s ^ 2 = ∏ r ∈ s.primeFactors, r ^ (2 * s.factorization r) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization (pow_ne_zero 2 hs.pos.ne')]
    rw [Nat.primeFactors_pow s (by decide : 2 ≠ 0)]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hs2_pow_T : ((s ^ 2 : ℕ) : R) ^ T =
      ∏ r ∈ s.primeFactors, ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T := by
    conv_lhs => rw [hs2_prod]
    push_cast
    rw [Finset.prod_pow]
  have hlocal_not : ∀ r ∈ s.primeFactors, v r ≠ 1 →
      ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T = 1 := by
    intro r hr hvne
    obtain ⟨hvo, hσr⟩ := hparts r hr
    dsimp only at hvo hσr
    change Odd (v r) at hvo
    change sigma 1 (r ^ (2 * s.factorization r)) = p ^ v r at hσr
    have hv2 : 2 ≤ v r := by have := hvo.pos; omega
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hrel : r ^ (2 * s.factorization r + 1) = 1 + (r - 1) * p ^ (v r) := by
      rw [← hσr, sigma_one_apply_prime_pow hrp]
      zify [hrp.one_le]
      have hg := geom_sum_mul (r : ℤ) (2 * s.factorization r + 1)
      linarith
    have hrcast : ((r ^ (2 * s.factorization r + 1) : ℕ) : R) = 1 := by
      rw [hrel]
      push_cast
      have hpv : (p : R) ^ v r = 0 := by
        rw [show v r = 2 + (v r - 2) by omega, pow_add, hp2_zero, zero_mul]
      rw [hpv, mul_zero, add_zero]
    obtain ⟨Q, hTQ⟩ := (Finset.dvd_prod_of_mem l hr).trans hT_prod.symm.dvd
    calc ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T
        = ((r ^ (2 * s.factorization r) : ℕ) : R) ^ (l r * Q) := by rw [hTQ]
      _ = ((r ^ (2 * s.factorization r + 1) : ℕ) : R) ^ (2 * s.factorization r * Q) := by
        dsimp [l]; push_cast; ring
      _ = 1 ^ (2 * s.factorization r * Q) := by rw [hrcast]
      _ = 1 := one_pow _
  have hlocal_mem : ∀ r ∈ S₁,
      let Q := ∏ t ∈ s.primeFactors.erase r, l t
      ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T =
        1 + ((2 * s.factorization r * Q * (r - 1) : ℕ) : R) * (p : R) := by
    intro r hrS Q
    obtain ⟨hr, hv1⟩ := Finset.mem_filter.mp hrS
    obtain ⟨_, hσr⟩ := hparts r hr
    dsimp only at hσr
    change sigma 1 (r ^ (2 * s.factorization r)) = p ^ v r at hσr
    rw [hv1, pow_one] at hσr
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hrs := Nat.dvd_of_mem_primeFactors hr
    have hepos : 1 ≤ s.factorization r := (hrp.dvd_iff_one_le_factorization hs.pos.ne').mp hrs
    have hrel : r ^ (2 * s.factorization r + 1) = 1 + (r - 1) * p := by
      rw [← hσr, sigma_one_apply_prime_pow hrp]
      zify [hrp.one_le]
      have hg := geom_sum_mul (r : ℤ) (2 * s.factorization r + 1)
      linarith
    have hrcast : ((r ^ (2 * s.factorization r + 1) : ℕ) : R) = 1 + ((r - 1 : ℕ) : R) * (p : R) := by
      rw [hrel]
      push_cast
      rfl
    have hTQ : T = l r * Q := by
      rw [hT_prod]
      exact (Finset.mul_prod_erase s.primeFactors l hr).symm
    have hQpos : 1 ≤ Q := Finset.one_le_prod fun _ _ => by dsimp [l]; omega
    have hexp : 1 ≤ 2 * s.factorization r * Q := by nlinarith
    have hb2 : (((r - 1 : ℕ) : R) * (p : R)) ^ 2 = 0 := by
      calc (((r - 1 : ℕ) : R) * (p : R)) ^ 2 = ((r - 1 : ℕ) : R) ^ 2 * (p : R) ^ 2 := by ring
        _ = 0 := by rw [hp2_zero, mul_zero]
    calc ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T
        = ((r ^ (2 * s.factorization r) : ℕ) : R) ^ (l r * Q) := by rw [hTQ]
      _ = ((r ^ (2 * s.factorization r + 1) : ℕ) : R) ^ (2 * s.factorization r * Q) := by
        dsimp [l]; push_cast; ring
      _ = (1 + ((r - 1 : ℕ) : R) * (p : R)) ^ (2 * s.factorization r * Q) := by rw [hrcast]
      _ = 1 ^ (2 * s.factorization r * Q) +
          ((2 * s.factorization r * Q : ℕ) : R) * 1 ^ (2 * s.factorization r * Q - 1) *
            (((r - 1 : ℕ) : R) * (p : R)) :=
        add_pow_of_sq_eq_zero 1 (((r - 1 : ℕ) : R) * (p : R)) hb2 (2 * s.factorization r * Q) hexp
      _ = 1 + ((2 * s.factorization r * Q * (r - 1) : ℕ) : R) * (p : R) := by
        simp only [one_pow, mul_one, Nat.cast_mul]; ring
  have hS1_ne : S₁.Nonempty := by
    by_contra! h_empty
    have hs2_one : ((s ^ 2 : ℕ) : R) ^ T = 1 := by
      rw [hs2_pow_T]
      refine Finset.prod_eq_one fun r hr => hlocal_not r hr ?_
      intro hv1
      have : r ∈ S₁ := Finset.mem_filter.mpr ⟨hr, hv1⟩
      rw [h_empty] at this
      simp at this
    rw [hs2_one, mul_one] at hpow_T
    have hzero : ((T * 2 ^ (T - 1) * p : ℕ) : R) = 0 := by
      push_cast
      linear_combination -hpow_T
    have hdvd : p ^ 2 ∣ T * 2 ^ (T - 1) * p := (ZMod.natCast_eq_zero_iff _ _).mp hzero
    rw [pow_two] at hdvd
    have hdvd1 : p ∣ T * 2 ^ (T - 1) := Nat.dvd_of_mul_dvd_mul_right hp.pos hdvd
    have hdvd2 : p ∣ 2 ^ (T - 1) := hT_cop.dvd_of_dvd_mul_left hdvd1
    have hd2 : p ∣ 2 := hp.dvd_of_dvd_pow hdvd2
    exact hpo.not_two_dvd_nat ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd2 ▸ dvd_rfl)
  let Q_out := ∏ t ∈ s.primeFactors \ S₁, l t
  have hQ_eq : ∀ r ∈ S₁,
      (∏ t ∈ s.primeFactors.erase r, l t) = (∏ t ∈ S₁.erase r, l t) * Q_out := by
    intro r hrS
    have hr_pf : r ∈ s.primeFactors := (Finset.mem_filter.mp hrS).1
    have hsplit : s.primeFactors.erase r = S₁.erase r ∪ (s.primeFactors \ S₁) := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro ⟨hxr, hxs⟩
        by_cases hxS : x ∈ S₁
        · exact Or.inl ⟨hxr, hxS⟩
        · exact Or.inr ⟨hxs, hxS⟩
      · rintro (⟨hxr, hxS⟩ | ⟨hxs, hxS⟩)
        · exact ⟨hxr, (Finset.mem_filter.mp hxS).1⟩
        · exact ⟨fun h => hxS (h ▸ hrS), hxs⟩
    have hdisj : Disjoint (S₁.erase r) (s.primeFactors \ S₁) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_sdiff.mp hx2).2 (Finset.mem_of_mem_erase hx1)
    rw [hsplit, Finset.prod_union hdisj]
  have hT_split : T = (∏ t ∈ S₁, l t) * Q_out := by
    rw [hT_prod, ← Finset.prod_sdiff (Finset.filter_subset (v · = 1) s.primeFactors), mul_comm]
  have hQ_out_cop : p.Coprime Q_out :=
    hT_cop.coprime_dvd_right ⟨∏ t ∈ S₁, l t, by rw [hT_split, mul_comm]⟩
  have hs2_S1 : ((s ^ 2 : ℕ) : R) ^ T =
      1 + (∑ r ∈ S₁, ((2 * s.factorization r * (∏ t ∈ S₁.erase r, l t) * Q_out * (r - 1) : ℕ) : R)) *
        (p : R) := by
    rw [hs2_pow_T, ← Finset.prod_filter_mul_prod_filter_not s.primeFactors (fun r => v r = 1)]
    have hnot : (∏ r ∈ s.primeFactors.filter (fun r => ¬ v r = 1),
        ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T) = 1 := by
      refine Finset.prod_eq_one fun r hr => ?_
      obtain ⟨hr_pf, hnv⟩ := Finset.mem_filter.mp hr
      exact hlocal_not r hr_pf hnv
    rw [hnot, mul_one]
    have hprod_eq : ∏ r ∈ S₁, ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T =
        ∏ r ∈ S₁, (1 + ((2 * s.factorization r * (∏ t ∈ S₁.erase r, l t) * Q_out * (r - 1) : ℕ) : R) *
          (p : R)) := by
      refine Finset.prod_congr rfl fun r hrS => ?_
      have hm := hlocal_mem r hrS
      dsimp only at hm
      rw [hm, hQ_eq r hrS]
      push_cast
      ring
    rw [hprod_eq, prod_one_add_mul_sq_eq_zero (p : R) hp2_zero]
  rw [hs2_S1] at hpow_T
  let SumCoef := ∑ r ∈ S₁, 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t
  let ProdL := ∏ t ∈ S₁, l t
  have h2T : (2 : R) ^ T = (2 : R) * (2 : R) ^ (T - 1) := by
    rw [← pow_succ', show T - 1 + 1 = T by omega]
  have hcongr : ((SumCoef * Q_out * 2 ^ (T - 1) * p : ℕ) : R) =
      ((ProdL * Q_out * 2 ^ (T - 1) * p : ℕ) : R) := by
    have hA : (2 : R) ^ T * (1 + (∑ r ∈ S₁,
          ((2 * s.factorization r * (∏ t ∈ S₁.erase r, l t) * Q_out * (r - 1) : ℕ) : R)) * (p : R)) =
        (2 : R) ^ T + ((SumCoef * Q_out * 2 ^ (T - 1) * p : ℕ) : R) := by
      have hsum_cast : (∑ r ∈ S₁,
            ((2 * s.factorization r * (∏ t ∈ S₁.erase r, l t) * Q_out * (r - 1) : ℕ) : R)) * 2 =
          (SumCoef * Q_out : ℕ) := by
        dsimp [SumCoef]
        push_cast
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun r _ => ?_
        ring
      calc (2 : R) ^ T * (1 + (∑ r ∈ S₁,
              ((2 * s.factorization r * (∏ t ∈ S₁.erase r, l t) * Q_out * (r - 1) : ℕ) : R)) * (p : R))
          = (2 : R) ^ T + ((∑ r ∈ S₁,
              ((2 * s.factorization r * (∏ t ∈ S₁.erase r, l t) * Q_out * (r - 1) : ℕ) : R)) * 2) *
              (2 : R) ^ (T - 1) * (p : R) := by
            conv_lhs => rw [mul_add, mul_one]
            rw [h2T]; ring
        _ = (2 : R) ^ T + ((SumCoef * Q_out * 2 ^ (T - 1) * p : ℕ) : R) := by
            rw [hsum_cast]; push_cast; ring
    have hB : (2 : R) ^ T + (T : R) * (2 : R) ^ (T - 1) * (p : R) =
        (2 : R) ^ T + ((ProdL * Q_out * 2 ^ (T - 1) * p : ℕ) : R) := by
      dsimp [ProdL]
      rw [hT_split]
      push_cast
      ring
    rw [hA, hB] at hpow_T
    exact add_left_cancel hpow_T
  have hlt_L : ProdL < SumCoef := by
    obtain ⟨r₀, hr₀S⟩ := hS1_ne
    obtain ⟨hr₀, _⟩ := Finset.mem_filter.mp hr₀S
    have hr₀p := Nat.prime_of_mem_primeFactors hr₀
    have hr₀s := Nat.dvd_of_mem_primeFactors hr₀
    have hr₀o : Odd r₀ := hs.of_dvd_nat hr₀s
    have hr₀_sub : 2 ≤ r₀ - 1 := by
      have := hr₀p.two_le
      have := Nat.odd_iff.mp hr₀o
      omega
    have he₀ : 1 ≤ s.factorization r₀ := (hr₀p.dvd_iff_one_le_factorization hs.pos.ne').mp hr₀s
    have hlt_term : l r₀ < 4 * s.factorization r₀ * (r₀ - 1) := by
      dsimp [l]
      have : 8 * s.factorization r₀ ≤ 4 * s.factorization r₀ * (r₀ - 1) := by
        calc 8 * s.factorization r₀ = 4 * s.factorization r₀ * 2 := by ring
          _ ≤ 4 * s.factorization r₀ * (r₀ - 1) := Nat.mul_le_mul_left _ hr₀_sub
      omega
    have hpos_prod : 0 < ∏ t ∈ S₁.erase r₀, l t :=
      Finset.prod_pos fun _ _ => by dsimp [l]; omega
    have hsingle : ProdL < 4 * s.factorization r₀ * (r₀ - 1) * ∏ t ∈ S₁.erase r₀, l t := by
      dsimp [ProdL]
      rw [← Finset.mul_prod_erase S₁ l hr₀S]
      exact Nat.mul_lt_mul_of_pos_right hlt_term hpos_prod
    have hterm_le : 4 * s.factorization r₀ * (r₀ - 1) * ∏ t ∈ S₁.erase r₀, l t ≤ SumCoef :=
      Finset.single_le_sum
        (f := fun r => 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t)
        (fun _ _ => Nat.zero_le _) hr₀S
    omega
  have hL_pos : 0 < L := by change 0 < SumCoef - ProdL; omega
  have hL_eq : SumCoef = ProdL + L := by change SumCoef = ProdL + (SumCoef - ProdL); omega
  have hzero : ((L * Q_out * 2 ^ (T - 1) * p : ℕ) : R) = 0 := by
    have hcast := congrArg (fun n : ℕ => (n : R)) (by
      calc L * Q_out * 2 ^ (T - 1) * p + ProdL * Q_out * 2 ^ (T - 1) * p
          = (ProdL + L) * Q_out * 2 ^ (T - 1) * p := by ring
        _ = SumCoef * Q_out * 2 ^ (T - 1) * p := by rw [← hL_eq])
    push_cast at hcast hcongr ⊢
    linear_combination hcast + hcongr
  have hdvd_prod : p ^ 2 ∣ L * Q_out * 2 ^ (T - 1) * p := (ZMod.natCast_eq_zero_iff _ _).mp hzero
  rw [pow_two] at hdvd_prod
  have hdvd1 : p ∣ L * Q_out * 2 ^ (T - 1) := Nat.dvd_of_mul_dvd_mul_right hp.pos hdvd_prod
  have hdvd2 : p ∣ L * Q_out :=
    ((Nat.coprime_two_right.mpr hpo).pow_right (T - 1)).dvd_of_dvd_mul_right hdvd1
  have hp_dvd_L : p ∣ L := hQ_out_cop.dvd_of_dvd_mul_right hdvd2
  exact ⟨hS1_ne, hL_pos, Nat.le_of_dvd hL_pos hp_dvd_L⟩

private lemma refute_card_one_arith {p r e : ℕ}
    (hrp : r.Prime) (hro : Odd r) (he : 1 ≤ e) (hσr : sigma 1 (r ^ (2 * e)) = p)
    (hle_p : p ≤ 4 * e * (r - 1) - (2 * e + 1)) : False := by
  have hr_ge3 : 3 ≤ r := by
    have := hrp.two_le; have := Nat.odd_iff.mp hro; omega
  rcases eq_or_ne e 1 with rfl | hene1
  · have hp_val : p = 1 + r + r ^ 2 := by
      rw [← hσr, mul_one, sigma_one_apply_prime_pow hrp]
      simp [Finset.sum_range_succ]
    rw [hp_val] at hle_p
    zify [hrp.one_le] at hle_p
    have hle_int : (1 + r + r ^ 2 : ℤ) ≤ 4 * (r - 1) - 3 := by omega
    nlinarith
  · have he2 : 2 ≤ e := by omega
    have hlin := linear_lt_even_pow hr_ge3 he2
    have hσ_gt : r ^ (2 * e) < p := by
      rw [← hσr]
      exact self_lt_sigma_of_one_lt (one_lt_pow₀ hrp.one_lt (by omega))
    have hL_lt : 4 * e * (r - 1) - (2 * e + 1) < 4 * e * r := by
      have : 4 * e * (r - 1) ≤ 4 * e * r := Nat.mul_le_mul_left _ (by omega)
      omega
    omega

private lemma refute_card_two_arith {p r₁ r₂ e₁ e₂ : ℕ}
    (hp : p.Prime) (hr₁p : r₁.Prime) (hr₁o : Odd r₁) (hr₂p : r₂.Prime)
    (he₂ : 1 ≤ e₂) (he_lt : e₂ < e₁) (hr₁_lt_r₂ : r₁ < r₂)
    (hl₁p : (2 * e₁ + 1).Prime) (hl₂p : (2 * e₂ + 1).Prime)
    (hσr₁ : sigma 1 (r₁ ^ (2 * e₁)) = p) (hσr₂ : sigma 1 (r₂ ^ (2 * e₂)) = p)
    (hle_p : p ≤ 4 * e₁ * (r₁ - 1) * (2 * e₂ + 1) + 4 * e₂ * (r₂ - 1) * (2 * e₁ + 1) -
      (2 * e₁ + 1) * (2 * e₂ + 1)) : False := by
  have he₁ : 2 ≤ e₁ := by omega
  have hr₁_mod : r₁ % 2 = 1 := Nat.odd_iff.mp hr₁o
  have hr₁_ge3 : 3 ≤ r₁ := by have := hr₁p.two_le; omega
  let l₁ := 2 * e₁ + 1
  let l₂ := 2 * e₂ + 1
  let L := 4 * e₁ * (r₁ - 1) * l₂ + 4 * e₂ * (r₂ - 1) * l₁ - l₁ * l₂
  have hle_p' : p ≤ L := hle_p
  have hL_lt_prod : L < 4 * l₁ * l₂ * r₂ := by
    have h1 : 4 * e₁ * (r₁ - 1) * l₂ ≤ 4 * e₁ * r₁ * l₂ :=
      Nat.mul_le_mul_right l₂ (Nat.mul_le_mul_left (4 * e₁) (by omega))
    have h2 : 4 * e₂ * (r₂ - 1) * l₁ ≤ 4 * e₂ * r₂ * l₁ :=
      Nat.mul_le_mul_right l₁ (Nat.mul_le_mul_left (4 * e₂) (by omega))
    have h3 : 4 * e₁ * r₁ * l₂ < 2 * l₁ * l₂ * r₂ := by
      have h3a : 4 * e₁ * r₁ < 2 * l₁ * r₂ := by
        calc 4 * e₁ * r₁ < 2 * l₁ * r₁ := Nat.mul_lt_mul_of_pos_right (by dsimp [l₁]; omega) hr₁p.pos
          _ < 2 * l₁ * r₂ := Nat.mul_lt_mul_of_pos_left hr₁_lt_r₂ (by positivity)
      calc 4 * e₁ * r₁ * l₂ < 2 * l₁ * r₂ * l₂ :=
            Nat.mul_lt_mul_of_pos_right h3a (by dsimp [l₂]; omega)
        _ = 2 * l₁ * l₂ * r₂ := by ring
    have h4 : 4 * e₂ * r₂ * l₁ < 2 * l₁ * l₂ * r₂ := by
      have h4a : 4 * e₂ * r₂ < 2 * l₂ * r₂ :=
        Nat.mul_lt_mul_of_pos_right (by dsimp [l₂]; omega) hr₂p.pos
      calc 4 * e₂ * r₂ * l₁ < 2 * l₂ * r₂ * l₁ :=
            Nat.mul_lt_mul_of_pos_right h4a (by dsimp [l₁]; omega)
        _ = 2 * l₁ * l₂ * r₂ := by ring
    calc L ≤ 4 * e₁ * (r₁ - 1) * l₂ + 4 * e₂ * (r₂ - 1) * l₁ := Nat.sub_le _ _
      _ ≤ 4 * e₁ * r₁ * l₂ + 4 * e₂ * r₂ * l₁ := Nat.add_le_add h1 h2
      _ < 2 * l₁ * l₂ * r₂ + 2 * l₁ * l₂ * r₂ := Nat.add_lt_add h3 h4
      _ = 4 * l₁ * l₂ * r₂ := by ring
  have hr₂_sq_lt_p : r₂ ^ 2 < p := by
    have hrange : range 3 ⊆ range (2 * e₂ + 1) := Finset.range_mono (by omega : 3 ≤ 2 * e₂ + 1)
    have hsum3 : 1 + r₂ + r₂ ^ 2 ≤ sigma 1 (r₂ ^ (2 * e₂)) := by
      rw [sigma_one_apply_prime_pow hr₂p]
      calc 1 + r₂ + r₂ ^ 2 = ∑ j ∈ range 3, r₂ ^ j := by
            simp [Finset.sum_range_succ, Nat.add_assoc]
        _ ≤ ∑ j ∈ range (2 * e₂ + 1), r₂ ^ j := Finset.sum_le_sum_of_subset hrange
    rw [hσr₂] at hsum3
    omega
  have hr₁_pow_lt_p : r₁ ^ (2 * e₁) < p := by
    rw [← hσr₁]
    exact self_lt_sigma_of_one_lt (one_lt_pow₀ hr₁p.one_lt (by omega))
  by_cases hr₂_big : 4 * l₁ * l₂ ≤ r₂
  · have : L < r₂ ^ 2 := by
      calc L < 4 * l₁ * l₂ * r₂ := hL_lt_prod
        _ ≤ r₂ * r₂ := Nat.mul_le_mul_right r₂ hr₂_big
        _ = r₂ ^ 2 := by ring
    omega
  · have hr₂_lt : r₂ < 4 * l₁ * l₂ := by omega
    have hL_lt_sq : L < (4 * l₁ * l₂) ^ 2 := by
      have : 4 * l₁ * l₂ * r₂ < 4 * l₁ * l₂ * (4 * l₁ * l₂) :=
        Nat.mul_lt_mul_of_pos_left hr₂_lt (by positivity)
      calc L < 4 * l₁ * l₂ * r₂ := hL_lt_prod
        _ < 4 * l₁ * l₂ * (4 * l₁ * l₂) := this
        _ = (4 * l₁ * l₂) ^ 2 := by ring
    by_cases he₁_big : 6 ≤ e₁
    · have hl₂_lt_l₁ : l₂ < l₁ := by dsimp [l₁, l₂]; omega
      have hL_lt_16 : L < 16 * l₁ ^ 4 := by
        have hl₂_sq : l₂ ^ 2 < l₁ ^ 2 := Nat.pow_lt_pow_left hl₂_lt_l₁ (by decide : 2 ≠ 0)
        have hpow : (4 * l₁ * l₂) ^ 2 < 16 * l₁ ^ 4 := by
          calc (4 * l₁ * l₂) ^ 2 = 16 * l₁ ^ 2 * l₂ ^ 2 := by ring
            _ < 16 * l₁ ^ 2 * l₁ ^ 2 := Nat.mul_lt_mul_of_pos_left hl₂_sq (by positivity)
            _ = 16 * l₁ ^ 4 := by ring
        omega
      have h16 := sixteen_mul_odd_pow4_le_three_pow he₁_big
      have h3_le : 3 ^ (2 * e₁) ≤ r₁ ^ (2 * e₁) := Nat.pow_le_pow_left hr₁_ge3 (2 * e₁)
      change L < 16 * (2 * e₁ + 1) ^ 4 at hL_lt_16
      omega
    · rcases (by omega : e₁ = 2 ∨ e₁ = 3 ∨ e₁ = 4 ∨ e₁ = 5) with rfl | rfl | rfl | rfl
      · have he₂_eq : e₂ = 1 := by omega
        subst he₂_eq
        change L < (4 * (2 * 2 + 1) * (2 * 1 + 1)) ^ 2 at hL_lt_sq
        norm_num at hL_lt_sq
        by_cases hr₁_ge11 : 11 ≤ r₁
        · have h11 : (11 : ℕ) ^ (2 * 2) = 14641 := by norm_num
          have : 14641 ≤ r₁ ^ (2 * 2) := h11 ▸ Nat.pow_le_pow_left hr₁_ge11 (2 * 2)
          omega
        · rcases (by omega : r₁ = 3 ∨ r₁ = 5 ∨ r₁ = 7 ∨ r₁ = 9) with rfl | rfl | rfl | rfl
          · rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
            norm_num [Finset.sum_range_succ] at hσr₁
            rw [← hσr₁] at hp
            have hdiv : 11 ∣ 121 := by norm_num
            have := hp.eq_one_or_self_of_dvd 11 hdiv
            omega
          · rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
            norm_num [Finset.sum_range_succ] at hσr₁
            rw [← hσr₁] at hp
            have hdiv : 11 ∣ 781 := by norm_num
            have := hp.eq_one_or_self_of_dvd 11 hdiv
            omega
          · rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
            norm_num [Finset.sum_range_succ] at hσr₁
            have hσr₂_val : 1 + r₂ + r₂ ^ 2 = 2801 := by
              rw [hσr₁, ← hσr₂, mul_one, sigma_one_apply_prime_pow hr₂p]
              simp [Finset.sum_range_succ, Nat.add_assoc]
            by_cases hr₂_le : r₂ ≤ 52 <;> nlinarith
          · exact absurd hr₁p (by decide)
      · have hL_bound : L < 19600 := by
          have hl₁_val : l₁ = 7 := rfl
          have hl₂_le : l₂ ≤ 5 := by dsimp [l₂]; omega
          have hmul : 4 * l₁ * l₂ ≤ 140 := by
            calc 4 * l₁ * l₂ = 4 * 7 * l₂ := by rw [hl₁_val]
              _ ≤ 140 := by omega
          have hsq : (4 * l₁ * l₂) ^ 2 ≤ 19600 :=
            (Nat.pow_le_pow_left hmul 2).trans (by norm_num)
          omega
        by_cases hr₁_ge7 : 7 ≤ r₁
        · have h7 : (7 : ℕ) ^ (2 * 3) = 117649 := by norm_num
          have : 117649 ≤ r₁ ^ (2 * 3) := h7 ▸ Nat.pow_le_pow_left hr₁_ge7 (2 * 3)
          omega
        · rcases (by omega : r₁ = 3 ∨ r₁ = 5) with rfl | rfl
          · rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
            norm_num [Finset.sum_range_succ] at hσr₁
            rcases (by omega : e₂ = 1 ∨ e₂ = 2) with rfl | rfl
            · have hσr₂_val : 1 + r₂ + r₂ ^ 2 = 1093 := by
                rw [hσr₁, ← hσr₂, mul_one, sigma_one_apply_prime_pow hr₂p]
                simp [Finset.sum_range_succ, Nat.add_assoc]
              by_cases hr₂_le : r₂ ≤ 32 <;> nlinarith
            · have hσr₂_val : 1 + r₂ + r₂ ^ 2 + r₂ ^ 3 + r₂ ^ 4 = 1093 := by
                rw [hσr₁, ← hσr₂, sigma_one_apply_prime_pow hr₂p]
                simp [Finset.sum_range_succ, Nat.add_assoc]
              by_cases hr₂_le5 : r₂ ≤ 5
              · have hle5 : 1 + r₂ + r₂ ^ 2 + r₂ ^ 3 + r₂ ^ 4 ≤ 1 + 5 + 5 ^ 2 + 5 ^ 3 + 5 ^ 4 := by
                  gcongr
                omega
              · have hge6 : 6 ≤ r₂ := by omega
                have : 6 ^ 4 ≤ r₂ ^ 4 := Nat.pow_le_pow_left hge6 4
                norm_num at this
                omega
          · rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
            norm_num [Finset.sum_range_succ] at hσr₁
            rcases (by omega : e₂ = 1 ∨ e₂ = 2) with rfl | rfl
            · have hσr₂_val : 1 + r₂ + r₂ ^ 2 = 19531 := by
                rw [hσr₁, ← hσr₂, mul_one, sigma_one_apply_prime_pow hr₂p]
                simp [Finset.sum_range_succ, Nat.add_assoc]
              by_cases hr₂_le : r₂ ≤ 139 <;> nlinarith
            · have hσr₂_val : 1 + r₂ + r₂ ^ 2 + r₂ ^ 3 + r₂ ^ 4 = 19531 := by
                rw [hσr₁, ← hσr₂, sigma_one_apply_prime_pow hr₂p]
                simp [Finset.sum_range_succ, Nat.add_assoc]
              by_cases hr₂_le11 : r₂ ≤ 11
              · have hle11 : 1 + r₂ + r₂ ^ 2 + r₂ ^ 3 + r₂ ^ 4 ≤
                    1 + 11 + 11 ^ 2 + 11 ^ 3 + 11 ^ 4 := by
                  gcongr
                omega
              · have hge12 : 12 ≤ r₂ := by omega
                have : 12 ^ 4 ≤ r₂ ^ 4 := Nat.pow_le_pow_left hge12 4
                norm_num at this
                omega
      · exact absurd hl₁p (by decide)
      · have he₂_le : e₂ ≤ 3 := by
          by_contra! hge4
          have he₂_eq4 : e₂ = 4 := by omega
          rw [he₂_eq4] at hl₂p
          exact absurd hl₂p (by decide)
        have hL_bound : L < 94864 := by
          have hl₁_val : l₁ = 11 := rfl
          have hl₂_le : l₂ ≤ 7 := by dsimp [l₂]; omega
          have hmul : 4 * l₁ * l₂ ≤ 308 := by
            calc 4 * l₁ * l₂ = 4 * 11 * l₂ := by rw [hl₁_val]
              _ ≤ 308 := by omega
          have hsq : (4 * l₁ * l₂) ^ 2 ≤ 94864 :=
            (Nat.pow_le_pow_left hmul 2).trans (by norm_num)
          omega
        by_cases hr₁_ge5 : 5 ≤ r₁
        · have h5 : (5 : ℕ) ^ (2 * 5) = 9765625 := by norm_num
          have : 9765625 ≤ r₁ ^ (2 * 5) := h5 ▸ Nat.pow_le_pow_left hr₁_ge5 (2 * 5)
          omega
        · have hr₁_eq3 : r₁ = 3 := by omega
          subst hr₁_eq3
          rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
          norm_num [Finset.sum_range_succ] at hσr₁
          rw [← hσr₁] at hp
          have hdiv : 23 ∣ 88573 := by norm_num
          have := hp.eq_one_or_self_of_dvd 23 hdiv
          omega

private lemma refute_card_three_arith {p r₁ r₂ r₃ e₁ e₂ e₃ : ℕ}
    (hp : p.Prime) (hr₁p : r₁.Prime) (hr₁o : Odd r₁) (hr₂p : r₂.Prime) (hr₃p : r₃.Prime)
    (he₃ : 1 ≤ e₃) (he₂₃ : e₃ < e₂) (he₁₂ : e₂ < e₁)
    (hr₁_lt_r₂ : r₁ < r₂) (hr₂_lt_r₃ : r₂ < r₃)
    (hl₁p : (2 * e₁ + 1).Prime) (hl₂p : (2 * e₂ + 1).Prime) (hl₃p : (2 * e₃ + 1).Prime)
    (hl₂_dvd : 2 * (2 * e₂ + 1) ∣ p - 1)
    (hσr₁ : sigma 1 (r₁ ^ (2 * e₁)) = p)
    (hσr₂ : sigma 1 (r₂ ^ (2 * e₂)) = p)
    (hσr₃ : sigma 1 (r₃ ^ (2 * e₃)) = p)
    (hle_p : p ≤ 4 * e₁ * (r₁ - 1) * (2 * e₂ + 1) * (2 * e₃ + 1) +
      4 * e₂ * (r₂ - 1) * (2 * e₁ + 1) * (2 * e₃ + 1) +
      4 * e₃ * (r₃ - 1) * (2 * e₁ + 1) * (2 * e₂ + 1) -
      (2 * e₁ + 1) * (2 * e₂ + 1) * (2 * e₃ + 1)) : False := by
  have he₂ : 2 ≤ e₂ := by omega
  have he₁ : 3 ≤ e₁ := by omega
  have hr₁_mod : r₁ % 2 = 1 := Nat.odd_iff.mp hr₁o
  have hr₁_ge3 : 3 ≤ r₁ := by have := hr₁p.two_le; omega
  let l₁ := 2 * e₁ + 1
  let l₂ := 2 * e₂ + 1
  let l₃ := 2 * e₃ + 1
  let L := 4 * e₁ * (r₁ - 1) * l₂ * l₃ + 4 * e₂ * (r₂ - 1) * l₁ * l₃ +
    4 * e₃ * (r₃ - 1) * l₁ * l₂ - l₁ * l₂ * l₃
  have hle_p' : p ≤ L := hle_p
  have hr₁_lt_r₃ : r₁ < r₃ := lt_trans hr₁_lt_r₂ hr₂_lt_r₃
  have hL_lt_prod : L < 6 * l₁ * l₂ * l₃ * r₃ := by
    have h1 : 4 * e₁ * (r₁ - 1) * l₂ * l₃ ≤ 4 * e₁ * r₁ * l₂ * l₃ :=
      Nat.mul_le_mul_right l₃ (Nat.mul_le_mul_right l₂ (Nat.mul_le_mul_left (4 * e₁) (by omega)))
    have h2 : 4 * e₂ * (r₂ - 1) * l₁ * l₃ ≤ 4 * e₂ * r₂ * l₁ * l₃ :=
      Nat.mul_le_mul_right l₃ (Nat.mul_le_mul_right l₁ (Nat.mul_le_mul_left (4 * e₂) (by omega)))
    have h3 : 4 * e₃ * (r₃ - 1) * l₁ * l₂ ≤ 4 * e₃ * r₃ * l₁ * l₂ :=
      Nat.mul_le_mul_right l₂ (Nat.mul_le_mul_right l₁ (Nat.mul_le_mul_left (4 * e₃) (by omega)))
    have ht1 : 4 * e₁ * r₁ * l₂ * l₃ < 2 * l₁ * l₂ * l₃ * r₃ := by
      have ha : 4 * e₁ * r₁ < 2 * l₁ * r₃ := by
        calc 4 * e₁ * r₁ < 2 * l₁ * r₁ := Nat.mul_lt_mul_of_pos_right (by dsimp [l₁]; omega) hr₁p.pos
          _ < 2 * l₁ * r₃ := Nat.mul_lt_mul_of_pos_left hr₁_lt_r₃ (by positivity)
      calc 4 * e₁ * r₁ * l₂ * l₃ < 2 * l₁ * r₃ * l₂ * l₃ :=
            Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right ha (by dsimp [l₂]; omega))
              (by dsimp [l₃]; omega)
        _ = 2 * l₁ * l₂ * l₃ * r₃ := by ring
    have ht2 : 4 * e₂ * r₂ * l₁ * l₃ < 2 * l₁ * l₂ * l₃ * r₃ := by
      have ha : 4 * e₂ * r₂ < 2 * l₂ * r₃ := by
        calc 4 * e₂ * r₂ < 2 * l₂ * r₂ := Nat.mul_lt_mul_of_pos_right (by dsimp [l₂]; omega) hr₂p.pos
          _ < 2 * l₂ * r₃ := Nat.mul_lt_mul_of_pos_left hr₂_lt_r₃ (by positivity)
      calc 4 * e₂ * r₂ * l₁ * l₃ < 2 * l₂ * r₃ * l₁ * l₃ :=
            Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right ha (by dsimp [l₁]; omega))
              (by dsimp [l₃]; omega)
        _ = 2 * l₁ * l₂ * l₃ * r₃ := by ring
    have ht3 : 4 * e₃ * r₃ * l₁ * l₂ < 2 * l₁ * l₂ * l₃ * r₃ := by
      have ha : 4 * e₃ * r₃ < 2 * l₃ * r₃ :=
        Nat.mul_lt_mul_of_pos_right (by dsimp [l₃]; omega) hr₃p.pos
      calc 4 * e₃ * r₃ * l₁ * l₂ < 2 * l₃ * r₃ * l₁ * l₂ :=
            Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right ha (by dsimp [l₁]; omega))
              (by dsimp [l₂]; omega)
        _ = 2 * l₁ * l₂ * l₃ * r₃ := by ring
    calc L ≤ 4 * e₁ * (r₁ - 1) * l₂ * l₃ + 4 * e₂ * (r₂ - 1) * l₁ * l₃ +
          4 * e₃ * (r₃ - 1) * l₁ * l₂ := Nat.sub_le _ _
      _ ≤ 4 * e₁ * r₁ * l₂ * l₃ + 4 * e₂ * r₂ * l₁ * l₃ + 4 * e₃ * r₃ * l₁ * l₂ :=
        Nat.add_le_add (Nat.add_le_add h1 h2) h3
      _ < 2 * l₁ * l₂ * l₃ * r₃ + 2 * l₁ * l₂ * l₃ * r₃ + 2 * l₁ * l₂ * l₃ * r₃ :=
        Nat.add_lt_add (Nat.add_lt_add ht1 ht2) ht3
      _ = 6 * l₁ * l₂ * l₃ * r₃ := by ring
  have hr₃_sq_lt_p : r₃ ^ 2 < p := by
    have hrange : range 3 ⊆ range (2 * e₃ + 1) := Finset.range_mono (by omega : 3 ≤ 2 * e₃ + 1)
    have hsum3 : 1 + r₃ + r₃ ^ 2 ≤ sigma 1 (r₃ ^ (2 * e₃)) := by
      rw [sigma_one_apply_prime_pow hr₃p]
      calc 1 + r₃ + r₃ ^ 2 = ∑ j ∈ range 3, r₃ ^ j := by
            simp [Finset.sum_range_succ, Nat.add_assoc]
        _ ≤ ∑ j ∈ range (2 * e₃ + 1), r₃ ^ j := Finset.sum_le_sum_of_subset hrange
    rw [hσr₃] at hsum3
    omega
  have hr₁_pow_lt_p : r₁ ^ (2 * e₁) < p := by
    rw [← hσr₁]
    exact self_lt_sigma_of_one_lt (one_lt_pow₀ hr₁p.one_lt (by omega))
  by_cases hr₃_big : 6 * l₁ * l₂ * l₃ ≤ r₃
  · have : L < r₃ ^ 2 := by
      calc L < 6 * l₁ * l₂ * l₃ * r₃ := hL_lt_prod
        _ ≤ r₃ * r₃ := Nat.mul_le_mul_right r₃ hr₃_big
        _ = r₃ ^ 2 := by ring
    omega
  · have hr₃_lt : r₃ < 6 * l₁ * l₂ * l₃ := by omega
    have hL_lt_sq : L < (6 * l₁ * l₂ * l₃) ^ 2 := by
      have : 6 * l₁ * l₂ * l₃ * r₃ < 6 * l₁ * l₂ * l₃ * (6 * l₁ * l₂ * l₃) :=
        Nat.mul_lt_mul_of_pos_left hr₃_lt (by positivity)
      calc L < 6 * l₁ * l₂ * l₃ * r₃ := hL_lt_prod
        _ < 6 * l₁ * l₂ * l₃ * (6 * l₁ * l₂ * l₃) := this
        _ = (6 * l₁ * l₂ * l₃) ^ 2 := by ring
    by_cases he₁_big : 10 ≤ e₁
    · have hl₂_lt : l₂ < l₁ := by dsimp [l₁, l₂]; omega
      have hl₃_lt : l₃ < l₁ := by dsimp [l₁, l₃]; omega
      have hL_lt_36 : L < 36 * l₁ ^ 6 := by
        have hl₂_sq : l₂ ^ 2 < l₁ ^ 2 := Nat.pow_lt_pow_left hl₂_lt (by decide : 2 ≠ 0)
        have hl₃_sq : l₃ ^ 2 < l₁ ^ 2 := Nat.pow_lt_pow_left hl₃_lt (by decide : 2 ≠ 0)
        have hpow : (6 * l₁ * l₂ * l₃) ^ 2 < 36 * l₁ ^ 6 := by
          calc (6 * l₁ * l₂ * l₃) ^ 2 = 36 * l₁ ^ 2 * l₂ ^ 2 * l₃ ^ 2 := by ring
            _ < 36 * l₁ ^ 2 * l₁ ^ 2 * l₁ ^ 2 := by
              have h1 : 36 * l₁ ^ 2 * l₂ ^ 2 < 36 * l₁ ^ 2 * l₁ ^ 2 :=
                Nat.mul_lt_mul_of_pos_left hl₂_sq (by positivity)
              calc 36 * l₁ ^ 2 * l₂ ^ 2 * l₃ ^ 2
                  < 36 * l₁ ^ 2 * l₁ ^ 2 * l₃ ^ 2 :=
                    Nat.mul_lt_mul_of_pos_right h1 (pow_pos (by dsimp [l₃]; omega) 2)
                _ < 36 * l₁ ^ 2 * l₁ ^ 2 * l₁ ^ 2 :=
                    Nat.mul_lt_mul_of_pos_left hl₃_sq (by positivity)
            _ = 36 * l₁ ^ 6 := by ring
        omega
      have h36 := thirty_six_mul_odd_pow6_le_three_pow he₁_big
      have h3_le : 3 ^ (2 * e₁) ≤ r₁ ^ (2 * e₁) := Nat.pow_le_pow_left hr₁_ge3 (2 * e₁)
      change L < 36 * (2 * e₁ + 1) ^ 6 at hL_lt_36
      omega
    · rcases (by omega : e₁ = 3 ∨ e₁ = 4 ∨ e₁ = 5 ∨ e₁ = 6 ∨ e₁ = 7 ∨ e₁ = 8 ∨ e₁ = 9) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · -- e₁ = 3, l₁ = 7
        have he₂_eq : e₂ = 2 := by omega
        have he₃_eq : e₃ = 1 := by omega
        subst he₂_eq he₃_eq
        change L < (6 * (2 * 3 + 1) * (2 * 2 + 1) * (2 * 1 + 1)) ^ 2 at hL_lt_sq
        norm_num at hL_lt_sq
        by_cases hr₁_ge11 : 11 ≤ r₁
        · have h11 : (11 : ℕ) ^ (2 * 3) = 1771561 := by norm_num
          have : 1771561 ≤ r₁ ^ (2 * 3) := h11 ▸ Nat.pow_le_pow_left hr₁_ge11 (2 * 3)
          omega
        · rcases (by omega : r₁ = 3 ∨ r₁ = 5 ∨ r₁ = 7 ∨ r₁ = 9) with rfl | rfl | rfl | rfl
          · rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
            norm_num [Finset.sum_range_succ] at hσr₁
            rw [← hσr₁] at hl₂_dvd
            norm_num at hl₂_dvd
          · rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
            norm_num [Finset.sum_range_succ] at hσr₁
            have hσr₃_val : 1 + r₃ + r₃ ^ 2 = 19531 := by
              rw [hσr₁, ← hσr₃, mul_one, sigma_one_apply_prime_pow hr₃p]
              simp [Finset.sum_range_succ, Nat.add_assoc]
            by_cases hr₃_le : r₃ ≤ 139 <;> nlinarith
          · rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
            norm_num [Finset.sum_range_succ] at hσr₁
            rw [← hσr₁] at hl₂_dvd
            norm_num at hl₂_dvd
          · exact absurd hr₁p (by decide)
      · -- e₁ = 4, l₁ = 9 (not prime)
        exact absurd hl₁p (by decide)
      · -- e₁ = 5, l₁ = 11
        have he₂_le : e₂ ≤ 3 := by
          by_contra! hge4
          have he₂_eq4 : e₂ = 4 := by omega
          rw [he₂_eq4] at hl₂p
          exact absurd hl₂p (by decide)
        have hL_bound : L < 5336100 := by
          have hl₁_val : l₁ = 11 := rfl
          have hl₂_le : l₂ ≤ 7 := by dsimp [l₂]; omega
          have hl₃_le : l₃ ≤ 5 := by dsimp [l₃]; omega
          have hmul : 6 * l₁ * l₂ * l₃ ≤ 2310 := by
            have h1 : 6 * l₁ * l₂ ≤ 462 := by
              calc 6 * l₁ * l₂ = 6 * 11 * l₂ := by rw [hl₁_val]
                _ ≤ 462 := by omega
            calc 6 * l₁ * l₂ * l₃ ≤ 462 * l₃ := Nat.mul_le_mul_right l₃ h1
              _ ≤ 2310 := by omega
          have hsq : (6 * l₁ * l₂ * l₃) ^ 2 ≤ 5336100 :=
            (Nat.pow_le_pow_left hmul 2).trans (by norm_num)
          omega
        by_cases hr₁_ge5 : 5 ≤ r₁
        · have h5 : (5 : ℕ) ^ (2 * 5) = 9765625 := by norm_num
          have : 9765625 ≤ r₁ ^ (2 * 5) := h5 ▸ Nat.pow_le_pow_left hr₁_ge5 (2 * 5)
          omega
        · have hr₁_eq3 : r₁ = 3 := by omega
          subst hr₁_eq3
          rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
          norm_num [Finset.sum_range_succ] at hσr₁
          rw [← hσr₁] at hp
          have hdiv : 23 ∣ 88573 := by norm_num
          have := hp.eq_one_or_self_of_dvd 23 hdiv
          omega
      · -- e₁ = 6, l₁ = 13
        have hL_bound : L < 59629284 := by
          have hl₁_val : l₁ = 13 := rfl
          have hl₂_le : l₂ ≤ 11 := by dsimp [l₂]; omega
          have hl₃_le : l₃ ≤ 9 := by dsimp [l₃]; omega
          have hmul : 6 * l₁ * l₂ * l₃ ≤ 7722 := by
            have h1 : 6 * l₁ * l₂ ≤ 858 := by
              calc 6 * l₁ * l₂ = 6 * 13 * l₂ := by rw [hl₁_val]
                _ ≤ 858 := by omega
            calc 6 * l₁ * l₂ * l₃ ≤ 858 * l₃ := Nat.mul_le_mul_right l₃ h1
              _ ≤ 7722 := by omega
          have hsq : (6 * l₁ * l₂ * l₃) ^ 2 ≤ 59629284 :=
            (Nat.pow_le_pow_left hmul 2).trans (by norm_num)
          omega
        by_cases hr₁_ge5 : 5 ≤ r₁
        · have h5 : (5 : ℕ) ^ (2 * 6) = 244140625 := by norm_num
          have : 244140625 ≤ r₁ ^ (2 * 6) := h5 ▸ Nat.pow_le_pow_left hr₁_ge5 (2 * 6)
          omega
        · have hr₁_eq3 : r₁ = 3 := by omega
          subst hr₁_eq3
          rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
          norm_num [Finset.sum_range_succ] at hσr₁
          have he₂_ne4 : e₂ ≠ 4 := by
            intro h4; rw [h4] at hl₂p; exact absurd hl₂p (by decide)
          have he₂_ne5 : e₂ ≠ 5 := by
            intro h5
            rw [h5, ← hσr₁] at hl₂_dvd
            norm_num at hl₂_dvd
          have he₃_range : e₃ = 1 ∨ e₃ = 2 := by omega
          rcases he₃_range with rfl | rfl
          · have hσr₃_val : 1 + r₃ + r₃ ^ 2 = 797161 := by
              rw [hσr₁, ← hσr₃, mul_one, sigma_one_apply_prime_pow hr₃p]
              simp [Finset.sum_range_succ, Nat.add_assoc]
            by_cases hr₃_le : r₃ ≤ 892 <;> nlinarith
          · have hσr₃_val : 1 + r₃ + r₃ ^ 2 + r₃ ^ 3 + r₃ ^ 4 = 797161 := by
              rw [hσr₁, ← hσr₃, sigma_one_apply_prime_pow hr₃p]
              simp [Finset.sum_range_succ, Nat.add_assoc]
            by_cases hr₃_le29 : r₃ ≤ 29
            · have hle29 : 1 + r₃ + r₃ ^ 2 + r₃ ^ 3 + r₃ ^ 4 ≤
                  1 + 29 + 29 ^ 2 + 29 ^ 3 + 29 ^ 4 := by
                gcongr
              omega
            · have hge30 : 30 ≤ r₃ := by omega
              have : 30 ^ 4 ≤ r₃ ^ 4 := Nat.pow_le_pow_left hge30 4
              norm_num at this
              omega
      · -- e₁ = 7, l₁ = 15 (not prime)
        exact absurd hl₁p (by decide)
      · -- e₁ = 8, l₁ = 17
        have hL_bound : L < 450000000 := by
          have hl₁_val : l₁ = 17 := rfl
          have hl₂_le : l₂ ≤ 15 := by dsimp [l₂]; omega
          have hl₃_le : l₃ ≤ 13 := by dsimp [l₃]; omega
          have hmul : 6 * l₁ * l₂ * l₃ ≤ 19890 := by
            have h1 : 6 * l₁ * l₂ ≤ 1530 := by
              calc 6 * l₁ * l₂ = 6 * 17 * l₂ := by rw [hl₁_val]
                _ ≤ 1530 := by omega
            calc 6 * l₁ * l₂ * l₃ ≤ 1530 * l₃ := Nat.mul_le_mul_right l₃ h1
              _ ≤ 19890 := by omega
          have hsq : (6 * l₁ * l₂ * l₃) ^ 2 ≤ 395612100 :=
            (Nat.pow_le_pow_left hmul 2).trans (by norm_num)
          omega
        by_cases hr₁_ge5 : 5 ≤ r₁
        · have h5 : (5 : ℕ) ^ (2 * 8) = 152587890625 := by norm_num
          have : 152587890625 ≤ r₁ ^ (2 * 8) := h5 ▸ Nat.pow_le_pow_left hr₁_ge5 (2 * 8)
          omega
        · have hr₁_eq3 : r₁ = 3 := by omega
          subst hr₁_eq3
          rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
          norm_num [Finset.sum_range_succ] at hσr₁
          rw [← hσr₁] at hp
          have hdiv : 1871 ∣ 64570081 := by norm_num
          have := hp.eq_one_or_self_of_dvd 1871 hdiv
          omega
      · -- e₁ = 9, l₁ = 19
        have hL_bound : L < 1000000000 := by
          have hl₁_val : l₁ = 19 := rfl
          have hl₂_le : l₂ ≤ 17 := by dsimp [l₂]; omega
          have hl₃_le : l₃ ≤ 15 := by dsimp [l₃]; omega
          have hmul : 6 * l₁ * l₂ * l₃ ≤ 29070 := by
            have h1 : 6 * l₁ * l₂ ≤ 1938 := by
              calc 6 * l₁ * l₂ = 6 * 19 * l₂ := by rw [hl₁_val]
                _ ≤ 1938 := by omega
            calc 6 * l₁ * l₂ * l₃ ≤ 1938 * l₃ := Nat.mul_le_mul_right l₃ h1
              _ ≤ 29070 := by omega
          have hsq : (6 * l₁ * l₂ * l₃) ^ 2 ≤ 845064900 :=
            (Nat.pow_le_pow_left hmul 2).trans (by norm_num)
          omega
        by_cases hr₁_ge5 : 5 ≤ r₁
        · have h5 : (5 : ℕ) ^ (2 * 9) = 3814697265625 := by norm_num
          have : 3814697265625 ≤ r₁ ^ (2 * 9) := h5 ▸ Nat.pow_le_pow_left hr₁_ge5 (2 * 9)
          omega
        · have hr₁_eq3 : r₁ = 3 := by omega
          subst hr₁_eq3
          rw [sigma_one_apply_prime_pow hr₁p] at hσr₁
          norm_num [Finset.sum_range_succ] at hσr₁
          rw [← hσr₁] at hp
          have hdiv : 1597 ∣ 581130733 := by norm_num
          have := hp.eq_one_or_self_of_dvd 1597 hdiv
          omega

/-- Unconditionally, at any even prime-power component index `p ^ (2 * u)`,
at least four distinct cofactor primes return `p` with valuation `1`. -/
theorem even_index_four_le_S1_card {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    4 ≤ (s.primeFactors.filter (v · = 1)).card := by
  let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
  let S₁ := s.primeFactors.filter (v · = 1)
  let l (t : ℕ) := 2 * s.factorization t + 1
  obtain ⟨hS1_ne, _, hle_p⟩ := even_index_S1_nonempty_and_p_le_L hp hpo hs hu hσq hplus hσs
  obtain ⟨_, hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  obtain ⟨hdvd_pred, _⟩ := even_index_repunit_lengths_dvd_pred hp hpo hs hσq hplus hσs
  have hS1_ne0 : S₁.card ≠ 0 := Finset.card_ne_zero.mpr hS1_ne
  have hS1_ne1 : S₁.card ≠ 1 := by
    intro h1
    obtain ⟨r₀, hS1_eq⟩ := Finset.card_eq_one.mp h1
    have hr₀S : r₀ ∈ S₁ := by rw [hS1_eq]; exact Finset.mem_singleton_self r₀
    obtain ⟨hr₀, hv₀⟩ := Finset.mem_filter.mp hr₀S
    have hr₀p := Nat.prime_of_mem_primeFactors hr₀
    have hr₀s := Nat.dvd_of_mem_primeFactors hr₀
    have hr₀o : Odd r₀ := hs.of_dvd_nat hr₀s
    have he₀ : 1 ≤ s.factorization r₀ := (hr₀p.dvd_iff_one_le_factorization hs.pos.ne').mp hr₀s
    have hσr₀ : sigma 1 (r₀ ^ (2 * s.factorization r₀)) = p := by
      have H := (hparts r₀ hr₀).2
      dsimp only at H
      change sigma 1 (r₀ ^ (2 * s.factorization r₀)) = p ^ v r₀ at H
      rwa [hv₀, pow_one] at H
    have hL_eq : (∑ r ∈ S₁, 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t) -
        ∏ t ∈ S₁, l t = 4 * s.factorization r₀ * (r₀ - 1) - (2 * s.factorization r₀ + 1) := by
      rw [hS1_eq]
      simp [l]
    rw [hL_eq] at hle_p
    exact refute_card_one_arith hr₀p hr₀o he₀ hσr₀ hle_p
  have hS1_ne2 : S₁.card ≠ 2 := by
    have refute_ordered2 : ∀ r₁ r₂ : ℕ, r₁ ≠ r₂ → S₁ = {r₁, r₂} →
        s.factorization r₂ < s.factorization r₁ → False := by
      intro r₁ r₂ hne hS1_eq he_lt
      have hr₁S : r₁ ∈ S₁ := by rw [hS1_eq]; simp
      have hr₂S : r₂ ∈ S₁ := by rw [hS1_eq]; simp
      obtain ⟨hr₁, hv₁⟩ := Finset.mem_filter.mp hr₁S
      obtain ⟨hr₂, hv₂⟩ := Finset.mem_filter.mp hr₂S
      have hr₁p := Nat.prime_of_mem_primeFactors hr₁
      have hr₂p := Nat.prime_of_mem_primeFactors hr₂
      have hr₁o : Odd r₁ := hs.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr₁)
      have he₂ : 1 ≤ s.factorization r₂ :=
        (hr₂p.dvd_iff_one_le_factorization hs.pos.ne').mp (Nat.dvd_of_mem_primeFactors hr₂)
      have hl₁p := (even_index_cofactor_component_order_dvd_pred hp hpo hs hσq hplus hσs hr₁).1
      have hl₂p := (even_index_cofactor_component_order_dvd_pred hp hpo hs hσq hplus hσs hr₂).1
      have hσr₁ : sigma 1 (r₁ ^ (2 * s.factorization r₁)) = p := by
        have H := (hparts r₁ hr₁).2
        dsimp only at H
        change sigma 1 (r₁ ^ (2 * s.factorization r₁)) = p ^ v r₁ at H
        rwa [hv₁, pow_one] at H
      have hσr₂ : sigma 1 (r₂ ^ (2 * s.factorization r₂)) = p := by
        have H := (hparts r₂ hr₂).2
        dsimp only at H
        change sigma 1 (r₂ ^ (2 * s.factorization r₂)) = p ^ v r₂ at H
        rwa [hv₂, pow_one] at H
      have hr₁_lt_r₂ : r₁ < r₂ := by
        by_contra! hle
        have hle_base : sigma 1 (r₂ ^ (2 * s.factorization r₂)) ≤
            sigma 1 (r₁ ^ (2 * s.factorization r₂)) := by
          rw [sigma_one_apply_prime_pow hr₂p, sigma_one_apply_prime_pow hr₁p]
          exact Finset.sum_le_sum fun j _ => Nat.pow_le_pow_left hle j
        have hlt_exp : sigma 1 (r₁ ^ (2 * s.factorization r₂)) <
            sigma 1 (r₁ ^ (2 * s.factorization r₁)) :=
          sigma_prime_pow_strictMono_exp hr₁p (by omega)
        omega
      have hL_eq : (∑ r ∈ S₁, 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t) -
          ∏ t ∈ S₁, l t =
          4 * s.factorization r₁ * (r₁ - 1) * (2 * s.factorization r₂ + 1) +
            4 * s.factorization r₂ * (r₂ - 1) * (2 * s.factorization r₁ + 1) -
            (2 * s.factorization r₁ + 1) * (2 * s.factorization r₂ + 1) := by
        rw [hS1_eq, Finset.sum_pair hne, Finset.prod_pair hne]
        have he1 : ({r₁, r₂} : Finset ℕ).erase r₁ = {r₂} :=
          Finset.erase_insert (by simp [hne])
        have he2 : ({r₁, r₂} : Finset ℕ).erase r₂ = {r₁} := by
          rw [Finset.pair_comm]
          exact Finset.erase_insert (by simp [hne.symm])
        rw [he1, he2, Finset.prod_singleton, Finset.prod_singleton]
      rw [hL_eq] at hle_p
      exact refute_card_two_arith hp hr₁p hr₁o hr₂p he₂ he_lt hr₁_lt_r₂ hl₁p hl₂p hσr₁ hσr₂ hle_p
    intro h2
    obtain ⟨a, b, hab, hS1_eq⟩ := Finset.card_eq_two.mp h2
    have haS : a ∈ S₁ := by rw [hS1_eq]; simp
    have hbS : b ∈ S₁ := by rw [hS1_eq]; simp
    obtain ⟨ha_pf, hva⟩ := Finset.mem_filter.mp haS
    obtain ⟨hb_pf, hvb⟩ := Finset.mem_filter.mp hbS
    have hap := Nat.prime_of_mem_primeFactors ha_pf
    have hbp := Nat.prime_of_mem_primeFactors hb_pf
    have hae : 1 ≤ s.factorization a :=
      (hap.dvd_iff_one_le_factorization hs.pos.ne').mp (Nat.dvd_of_mem_primeFactors ha_pf)
    have hσa : sigma 1 (a ^ (2 * s.factorization a)) = p := by
      have H := (hparts a ha_pf).2
      dsimp only at H
      change sigma 1 (a ^ (2 * s.factorization a)) = p ^ v a at H
      rwa [hva, pow_one] at H
    have hσb : sigma 1 (b ^ (2 * s.factorization b)) = p := by
      have H := (hparts b hb_pf).2
      dsimp only at H
      change sigma 1 (b ^ (2 * s.factorization b)) = p ^ v b at H
      rwa [hvb, pow_one] at H
    have he_ne : s.factorization a ≠ s.factorization b := by
      intro heq
      rw [← heq] at hσb
      rcases Nat.lt_trichotomy a b with hlt | rfl | hgt
      · have := sigma_prime_pow_lt_of_base_lt hap hbp hlt (by omega : 0 < 2 * s.factorization a)
        omega
      · exact hab rfl
      · have := sigma_prime_pow_lt_of_base_lt hbp hap hgt (by omega : 0 < 2 * s.factorization a)
        omega
    rcases Nat.lt_or_gt_of_ne he_ne with hlt | hgt
    · exact refute_ordered2 b a hab.symm (by rw [hS1_eq, Finset.pair_comm]) hlt
    · exact refute_ordered2 a b hab hS1_eq hgt
  have hS1_ne3 : S₁.card ≠ 3 := by
    have refute_ordered3 : ∀ r₁ r₂ r₃ : ℕ, r₁ ≠ r₂ → r₁ ≠ r₃ → r₂ ≠ r₃ →
        S₁ = {r₁, r₂, r₃} →
        s.factorization r₃ < s.factorization r₂ →
        s.factorization r₂ < s.factorization r₁ → False := by
      intro r₁ r₂ r₃ h12 h13 h23 hS1_eq he₂₃ he₁₂
      have hr₁S : r₁ ∈ S₁ := by rw [hS1_eq]; simp
      have hr₂S : r₂ ∈ S₁ := by rw [hS1_eq]; simp
      have hr₃S : r₃ ∈ S₁ := by rw [hS1_eq]; simp
      obtain ⟨hr₁, hv₁⟩ := Finset.mem_filter.mp hr₁S
      obtain ⟨hr₂, hv₂⟩ := Finset.mem_filter.mp hr₂S
      obtain ⟨hr₃, hv₃⟩ := Finset.mem_filter.mp hr₃S
      have hr₁p := Nat.prime_of_mem_primeFactors hr₁
      have hr₂p := Nat.prime_of_mem_primeFactors hr₂
      have hr₃p := Nat.prime_of_mem_primeFactors hr₃
      have hr₁o : Odd r₁ := hs.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr₁)
      have he₃ : 1 ≤ s.factorization r₃ :=
        (hr₃p.dvd_iff_one_le_factorization hs.pos.ne').mp (Nat.dvd_of_mem_primeFactors hr₃)
      have hl₁p := (even_index_cofactor_component_order_dvd_pred hp hpo hs hσq hplus hσs hr₁).1
      have hl₂p := (even_index_cofactor_component_order_dvd_pred hp hpo hs hσq hplus hσs hr₂).1
      have hl₃p := (even_index_cofactor_component_order_dvd_pred hp hpo hs hσq hplus hσs hr₃).1
      have hl₂_dvd := hdvd_pred r₂ hr₂S
      have hσr₁ : sigma 1 (r₁ ^ (2 * s.factorization r₁)) = p := by
        have H := (hparts r₁ hr₁).2
        dsimp only at H
        change sigma 1 (r₁ ^ (2 * s.factorization r₁)) = p ^ v r₁ at H
        rwa [hv₁, pow_one] at H
      have hσr₂ : sigma 1 (r₂ ^ (2 * s.factorization r₂)) = p := by
        have H := (hparts r₂ hr₂).2
        dsimp only at H
        change sigma 1 (r₂ ^ (2 * s.factorization r₂)) = p ^ v r₂ at H
        rwa [hv₂, pow_one] at H
      have hσr₃ : sigma 1 (r₃ ^ (2 * s.factorization r₃)) = p := by
        have H := (hparts r₃ hr₃).2
        dsimp only at H
        change sigma 1 (r₃ ^ (2 * s.factorization r₃)) = p ^ v r₃ at H
        rwa [hv₃, pow_one] at H
      have hr₁_lt_r₂ : r₁ < r₂ := by
        by_contra! hle
        have hle_base : sigma 1 (r₂ ^ (2 * s.factorization r₂)) ≤
            sigma 1 (r₁ ^ (2 * s.factorization r₂)) := by
          rw [sigma_one_apply_prime_pow hr₂p, sigma_one_apply_prime_pow hr₁p]
          exact Finset.sum_le_sum fun j _ => Nat.pow_le_pow_left hle j
        have hlt_exp : sigma 1 (r₁ ^ (2 * s.factorization r₂)) <
            sigma 1 (r₁ ^ (2 * s.factorization r₁)) :=
          sigma_prime_pow_strictMono_exp hr₁p (by omega)
        omega
      have hr₂_lt_r₃ : r₂ < r₃ := by
        by_contra! hle
        have hle_base : sigma 1 (r₃ ^ (2 * s.factorization r₃)) ≤
            sigma 1 (r₂ ^ (2 * s.factorization r₃)) := by
          rw [sigma_one_apply_prime_pow hr₃p, sigma_one_apply_prime_pow hr₂p]
          exact Finset.sum_le_sum fun j _ => Nat.pow_le_pow_left hle j
        have hlt_exp : sigma 1 (r₂ ^ (2 * s.factorization r₃)) <
            sigma 1 (r₂ ^ (2 * s.factorization r₂)) :=
          sigma_prime_pow_strictMono_exp hr₂p (by omega)
        omega
      have hL_eq : (∑ r ∈ S₁, 4 * s.factorization r * (r - 1) * ∏ t ∈ S₁.erase r, l t) -
          ∏ t ∈ S₁, l t =
          4 * s.factorization r₁ * (r₁ - 1) * (2 * s.factorization r₂ + 1) *
            (2 * s.factorization r₃ + 1) +
          4 * s.factorization r₂ * (r₂ - 1) * (2 * s.factorization r₁ + 1) *
            (2 * s.factorization r₃ + 1) +
          4 * s.factorization r₃ * (r₃ - 1) * (2 * s.factorization r₁ + 1) *
            (2 * s.factorization r₂ + 1) -
          (2 * s.factorization r₁ + 1) * (2 * s.factorization r₂ + 1) *
            (2 * s.factorization r₃ + 1) := by
        rw [hS1_eq]
        have hr₁_not : r₁ ∉ ({r₂, r₃} : Finset ℕ) := by simp [h12, h13]
        have hr₂_not : r₂ ∉ ({r₁, r₃} : Finset ℕ) := by simp [h12.symm, h23]
        have hr₃_not : r₃ ∉ ({r₁, r₂} : Finset ℕ) := by simp [h13.symm, h23.symm]
        have he1 : ({r₁, r₂, r₃} : Finset ℕ).erase r₁ = {r₂, r₃} := Finset.erase_insert hr₁_not
        have he2 : ({r₁, r₂, r₃} : Finset ℕ).erase r₂ = {r₁, r₃} := by
          rw [Finset.insert_comm]
          exact Finset.erase_insert hr₂_not
        have he3 : ({r₁, r₂, r₃} : Finset ℕ).erase r₃ = {r₁, r₂} := by
          rw [Finset.insert_comm, Finset.pair_comm r₁ r₃, ← Finset.insert_comm,
            Finset.pair_comm r₂ r₁, Finset.erase_insert hr₃_not]
        have hsum_eq : (∑ r ∈ ({r₁, r₂, r₃} : Finset ℕ),
              4 * s.factorization r * (r - 1) * ∏ t ∈ ({r₁, r₂, r₃} : Finset ℕ).erase r, l t) =
            4 * s.factorization r₁ * (r₁ - 1) * l r₂ * l r₃ +
            4 * s.factorization r₂ * (r₂ - 1) * l r₁ * l r₃ +
            4 * s.factorization r₃ * (r₃ - 1) * l r₁ * l r₂ := by
          rw [Finset.sum_insert hr₁_not, Finset.sum_pair h23,
            he1, he2, he3, Finset.prod_pair h23, Finset.prod_pair h13, Finset.prod_pair h12]
          simp only [mul_assoc, add_assoc]
        have hprod_eq : (∏ t ∈ ({r₁, r₂, r₃} : Finset ℕ), l t) = l r₁ * l r₂ * l r₃ := by
          rw [Finset.prod_insert hr₁_not, Finset.prod_pair h23, mul_assoc]
        rw [hsum_eq, hprod_eq]
      rw [hL_eq] at hle_p
      exact refute_card_three_arith hp hr₁p hr₁o hr₂p hr₃p he₃ he₂₃ he₁₂ hr₁_lt_r₂ hr₂_lt_r₃
        hl₁p hl₂p hl₃p hl₂_dvd hσr₁ hσr₂ hσr₃ hle_p
    intro h3
    obtain ⟨a, b, c, hab, hac, hbc, hS1_eq⟩ := Finset.card_eq_three.mp h3
    have hfac_ne : ∀ x y : ℕ, x ∈ S₁ → y ∈ S₁ → x ≠ y →
        s.factorization x ≠ s.factorization y := by
      intro x y hxS hyS hxy heq
      obtain ⟨hx, hvx⟩ := Finset.mem_filter.mp hxS
      obtain ⟨hy, hvy⟩ := Finset.mem_filter.mp hyS
      have hxp := Nat.prime_of_mem_primeFactors hx
      have hyp := Nat.prime_of_mem_primeFactors hy
      have hxe : 1 ≤ s.factorization x :=
        (hxp.dvd_iff_one_le_factorization hs.pos.ne').mp (Nat.dvd_of_mem_primeFactors hx)
      have hσx : sigma 1 (x ^ (2 * s.factorization x)) = p := by
        have H := (hparts x hx).2
        dsimp only at H
        change sigma 1 (x ^ (2 * s.factorization x)) = p ^ v x at H
        rwa [hvx, pow_one] at H
      have hσy : sigma 1 (y ^ (2 * s.factorization y)) = p := by
        have H := (hparts y hy).2
        dsimp only at H
        change sigma 1 (y ^ (2 * s.factorization y)) = p ^ v y at H
        rwa [hvy, pow_one] at H
      rw [← heq] at hσy
      rcases Nat.lt_trichotomy x y with hlt | rfl | hgt
      · have := sigma_prime_pow_lt_of_base_lt hxp hyp hlt (by omega : 0 < 2 * s.factorization x)
        omega
      · exact hxy rfl
      · have := sigma_prime_pow_lt_of_base_lt hyp hxp hgt (by omega : 0 < 2 * s.factorization x)
        omega
    have haS : a ∈ S₁ := by rw [hS1_eq]; simp
    have hbS : b ∈ S₁ := by rw [hS1_eq]; simp
    have hcS : c ∈ S₁ := by rw [hS1_eq]; simp
    have hfab := hfac_ne a b haS hbS hab
    have hfac := hfac_ne a c haS hcS hac
    have hfbc := hfac_ne b c hbS hcS hbc
    rcases Nat.lt_or_gt_of_ne hfab with hab_lt | hba_lt
    · rcases Nat.lt_or_gt_of_ne hfac with hac_lt | hca_lt
      · rcases Nat.lt_or_gt_of_ne hfbc with hbc_lt | hcb_lt
        · exact refute_ordered3 c b a hbc.symm hac.symm hab.symm
            (by rw [hS1_eq]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
            hab_lt hbc_lt
        · exact refute_ordered3 b c a hbc hab.symm hac.symm
            (by rw [hS1_eq]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
            hac_lt hcb_lt
      · exact refute_ordered3 b a c hab.symm hbc hac
          (by rw [hS1_eq]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
          hca_lt hab_lt
    · rcases Nat.lt_or_gt_of_ne hfbc with hbc_lt | hcb_lt
      · rcases Nat.lt_or_gt_of_ne hfac with hac_lt | hca_lt
        · exact refute_ordered3 c a b hac.symm hbc.symm hab
            (by rw [hS1_eq]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
            hba_lt hac_lt
        · exact refute_ordered3 a c b hac hab hbc.symm
            (by rw [hS1_eq]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
            hbc_lt hca_lt
      · exact refute_ordered3 a b c hab hac hbc hS1_eq hcb_lt hba_lt
  change 4 ≤ S₁.card
  omega

/-- Every even prime-power component index `p ^ (2 * u)` forces at least four
simultaneous odd-prime-base repunit representations of `p`. -/
theorem even_index_forces_four_repunits {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    HasFourOddPrimeRepunits p := by
  let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
  let S₁ := s.primeFactors.filter (v · = 1)
  have hS1_ge4 : 4 ≤ S₁.card := even_index_four_le_S1_card hp hpo hs hu hσq hplus hσs
  obtain ⟨r₁, hr₁S⟩ := Finset.card_pos.mp (by omega : 0 < S₁.card)
  have hS1_er₁ : 3 ≤ (S₁.erase r₁).card := by rw [Finset.card_erase_of_mem hr₁S]; omega
  obtain ⟨r₂, hr₂S'⟩ := Finset.card_pos.mp (by omega : 0 < (S₁.erase r₁).card)
  have hS1_er₂ : 2 ≤ ((S₁.erase r₁).erase r₂).card := by
    rw [Finset.card_erase_of_mem hr₂S']; omega
  obtain ⟨r₃, hr₃S'⟩ := Finset.card_pos.mp (by omega : 0 < ((S₁.erase r₁).erase r₂).card)
  have hS1_er₃ : 1 ≤ (((S₁.erase r₁).erase r₂).erase r₃).card := by
    rw [Finset.card_erase_of_mem hr₃S']; omega
  obtain ⟨r₄, hr₄S'⟩ := Finset.card_pos.mp
    (by omega : 0 < (((S₁.erase r₁).erase r₂).erase r₃).card)
  obtain ⟨h34, hr₄S'''⟩ := Finset.mem_erase.mp hr₄S'
  obtain ⟨h24, hr₄S''⟩ := Finset.mem_erase.mp hr₄S'''
  obtain ⟨h14, hr₄S⟩ := Finset.mem_erase.mp hr₄S''
  obtain ⟨h23, hr₃S''⟩ := Finset.mem_erase.mp hr₃S'
  obtain ⟨h13, hr₃S⟩ := Finset.mem_erase.mp hr₃S''
  obtain ⟨h12, hr₂S⟩ := Finset.mem_erase.mp hr₂S'
  obtain ⟨_, hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  have extract : ∀ r ∈ S₁, r.Prime ∧ Odd r ∧ (2 * s.factorization r + 1).Prime ∧
      2 < 2 * s.factorization r + 1 ∧ geometricBlock r (2 * s.factorization r + 1) = p := by
    intro r hrS
    obtain ⟨hr, hvr⟩ := Finset.mem_filter.mp hrS
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hrs := Nat.dvd_of_mem_primeFactors hr
    have hro : Odd r := hs.of_dvd_nat hrs
    have hfac : 1 ≤ s.factorization r := (hrp.dvd_iff_one_le_factorization hs.pos.ne').mp hrs
    have hlp := (even_index_cofactor_component_order_dvd_pred hp hpo hs hσq hplus hσs hr).1
    have hgb : geometricBlock r (2 * s.factorization r + 1) = p := by
      dsimp only [geometricBlock]
      rw [← sigma_one_apply_prime_pow hrp]
      have H := (hparts r hr).2
      dsimp only at H
      change sigma 1 (r ^ (2 * s.factorization r)) = p ^ v r at H
      rwa [hvr, pow_one] at H
    exact ⟨hrp, hro, hlp, by omega, hgb⟩
  obtain ⟨hr₁p, hr₁o, hl₁p, hl₁_gt2, hgr₁⟩ := extract r₁ hr₁S
  obtain ⟨hr₂p, hr₂o, hl₂p, hl₂_gt2, hgr₂⟩ := extract r₂ hr₂S
  obtain ⟨hr₃p, hr₃o, hl₃p, hl₃_gt2, hgr₃⟩ := extract r₃ hr₃S
  obtain ⟨hr₄p, hr₄o, hl₄p, hl₄_gt2, hgr₄⟩ := extract r₄ hr₄S
  exact ⟨r₁, r₂, r₃, r₄, 2 * s.factorization r₁ + 1, 2 * s.factorization r₂ + 1,
    2 * s.factorization r₃ + 1, 2 * s.factorization r₄ + 1,
    hr₁p, hr₁o, hr₂p, hr₂o, hr₃p, hr₃o, hr₄p, hr₄o,
    h12.symm, h13.symm, h14.symm, h23.symm, h24.symm, h34.symm,
    hl₁p, hl₁_gt2, hl₂p, hl₂_gt2, hl₃p, hl₃_gt2, hl₄p, hl₄_gt2,
    hgr₁, hgr₂, hgr₃, hgr₄⟩

/-- Unconditional strengthening at any even prime-power component index `i = p ^ (2 * u)`:
`p` has at least four simultaneous odd-prime-base repunit representations and `N` has
at least 7 distinct prime factors (in fact at least 8). -/
theorem even_prime_power_component_forces_four_repunits_and_seven_primes {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    HasFourOddPrimeRepunits p ∧ 7 ≤ N.primeFactors.card := by
  obtain ⟨ha1, hσ⟩ := even_prime_power_index_eq_selected_sigma hN ho hq ha hform hqb hl hr hp hu hi
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b _)
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h4 : 4 ∣ 2 * b := hr ▸ hi ▸ (pow_dvd_pow 2 (by omega : 2 ≤ 2 * u)).trans (dvd_mul_left _ _)
    have := hbo.not_two_dvd_nat
    omega
  have hpo := hp.odd_of_ne_two hp2
  obtain ⟨m, _, _, hqm, rfl⟩ :=
    euler_form_of_odd_component_index hN ho hq ha hform hqb hl hr (hi ▸ hpo.pow)
  have hmo := ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _)
  rw [ha1, pow_one] at hform hl hr
  rw [hi] at hl hr
  obtain ⟨s, hso, hcop, hms, _, hplus, hσs⟩ := even_prime_power_cofactor_split hq hp hmo hpo hu hl hr
  have hfour := even_index_forces_four_repunits hp hpo hso hu hσ hplus hσs
  have hS1_ge4 := even_index_four_le_S1_card hp hpo hso hu hσ hplus hσs
  let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
  let S₁ := s.primeFactors.filter (v · = 1)
  change 4 ≤ S₁.card at hS1_ge4
  have hS1_ne_full : S₁ ≠ s.primeFactors := by
    intro h_eq
    obtain ⟨hsum, hparts⟩ := even_index_source_valuation_budget hp hso hσ hplus hσs
    change ∑ r ∈ s.primeFactors, v r = 2 * u at hsum
    have h2u_eq : 2 * u = S₁.card := by
      rw [← hsum, ← h_eq]
      calc ∑ r ∈ S₁, v r = ∑ _r ∈ S₁, 1 := by
            refine Finset.sum_congr rfl fun r hr => ?_
            exact (Finset.mem_filter.mp hr).2
        _ = S₁.card := by simp
    have hsub_u1 : S₁ ⊆ (u + 1).primeFactors := by
      intro r hrS
      obtain ⟨hr, hvr⟩ := Finset.mem_filter.mp hrS
      have hrp := Nat.prime_of_mem_primeFactors hr
      have hrs := Nat.dvd_of_mem_primeFactors hr
      have hro : Odd r := hso.of_dvd_nat hrs
      have hσr : sigma 1 (r ^ (2 * s.factorization r)) = p := by
        have H := (hparts r hr).2
        dsimp only at H
        change sigma 1 (r ^ (2 * s.factorization r)) = p ^ v r at H
        rwa [hvr, pow_one] at H
      have hpmodr : p ≡ 1 [MOD r] := by
        rw [← hσr]
        simpa [Nat.ModEq, Nat.mod_eq_of_lt hrp.one_lt] using
          sigma_prime_pow_mod_self hrp (2 * s.factorization r)
      have hqmodr := sigma_modEq_of_one hp hpmodr (2 * u)
      rw [hσ] at hqmodr
      have hr_dvd_qp1 : r ∣ q + 1 :=
        hplus ▸ dvd_mul_of_dvd_right (dvd_pow hrs (by decide : 2 ≠ 0)) _
      have hr_dvd_2u1 : r ∣ 2 * (u + 1) :=
        (by omega : 2 * u + 1 + 1 = 2 * (u + 1)) ▸
          ((hqmodr.add_right 1).dvd_iff dvd_rfl).mp hr_dvd_qp1
      have hr_dvd_u1 : r ∣ u + 1 := (Nat.coprime_two_right.mpr hro).dvd_of_dvd_mul_left hr_dvd_2u1
      exact Nat.mem_primeFactors.mpr ⟨hrp, hr_dvd_u1, by omega⟩
    have hprod_le_u1 : ∏ r ∈ S₁, r ≤ u + 1 := by
      have hdvd_prod : (∏ r ∈ S₁, r) ∣ ∏ r ∈ (u + 1).primeFactors, r :=
        Finset.prod_dvd_prod_of_subset S₁ (u + 1).primeFactors id hsub_u1
      have hdvd_u1 : (∏ r ∈ S₁, r) ∣ u + 1 := hdvd_prod.trans (Nat.prod_primeFactors_dvd (u + 1))
      exact Nat.le_of_dvd (by omega) hdvd_u1
    have hpow3_le : 3 ^ S₁.card ≤ ∏ r ∈ S₁, r := by
      calc 3 ^ S₁.card = ∏ _r ∈ S₁, 3 := by simp
        _ ≤ ∏ r ∈ S₁, r := by
          refine Finset.prod_le_prod fun r hrS => ?_
          have hr := (Finset.mem_filter.mp hrS).1
          have hrp := Nat.prime_of_mem_primeFactors hr
          have hro : Odd r := hso.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr)
          have := hrp.two_le
          have := Nat.odd_iff.mp hro
          omega
    have hlt := two_mul_add_one_lt_three_pow hu
    rw [h2u_eq] at hlt
    omega
  have hS1_ssub : S₁ ⊂ s.primeFactors :=
    lt_of_le_of_ne (Finset.filter_subset _ _) hS1_ne_full
  have hs_ge5 : 5 ≤ s.primeFactors.card := by
    have := Finset.card_lt_card hS1_ssub
    omega
  have hpar := Nat.even_iff.mp (even_index_cofactor_prime_count hp hso hσ hplus hσs).1
  have hs_ge6 : 6 ≤ s.primeFactors.card := by omega
  have hn := prime_count_of_even_index_split hq hp hmo hso hu hqm hcop hform hms
  exact ⟨hfour, by omega⟩

end OddPerfect
