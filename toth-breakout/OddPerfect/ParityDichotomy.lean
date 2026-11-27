module

public import OddPerfect.DeficientFiniteness
public import OddPerfect.NearPerfectFinite
public import Archive.Wiedijk100Theorems.PerfectNumbers
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-!
## 1. Infinite and Conditional Even Families
-/

/-- Every power of two `2 ^ a` (`a ≥ 1`) is deficient-perfect with deficient divisor `1`. -/
theorem pow_two_deficientPerfect {a : ℕ} (ha : 1 ≤ a) :
    DeficientPerfectWith (2 ^ a) 1 := by
  refine ⟨Nat.one_mem_properDivisors_iff_one_lt.mpr (Nat.one_lt_two_pow (by omega)), ?_⟩
  rw [Theorems100.Nat.sigma_two_pow_eq_mersenne_succ, mersenne]
  have hpow : 1 ≤ 2 ^ (a + 1) := Nat.one_le_pow _ _ (by decide)
  rw [pow_succ'] at hpow ⊢
  omega

/-- Thabit primes yield even deficient-perfect numbers `2 ^ a * (3 * 2 ^ a - 1)` with
deficient divisor `2 ^ a`. -/
theorem thabit_deficientPerfect {a : ℕ} (ha : 1 ≤ a) (hq : (3 * 2 ^ a - 1).Prime) :
    DeficientPerfectWith (2 ^ a * (3 * 2 ^ a - 1)) (2 ^ a) := by
  set q := 3 * 2 ^ a - 1
  have h2a : 2 ≤ 2 ^ a := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
         _ ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) ha
  have hq_odd : Odd q := by
    have heven : Even (3 * 2 ^ a) := by
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0) with ⟨b, rfl⟩
      exact ⟨3 * 2 ^ b, by rw [pow_succ']; ring⟩
    obtain ⟨m, hm⟩ := heven
    refine Nat.odd_iff.mpr ?_
    dsimp [q]
    omega
  refine ⟨Nat.mem_properDivisors.mpr ⟨dvd_mul_right _ _,
    lt_mul_of_one_lt_right (by positivity) hq.one_lt⟩, ?_⟩
  have hcop : Nat.Coprime (2 ^ a) q := hq_odd.coprime_two_right.symm.pow_left a
  have hσq : sigma 1 q = q + 1 := by
    rw [← pow_one q, sigma_one_apply_prime_pow hq, Finset.sum_range_succ, Finset.sum_range_one,
      pow_zero, pow_one, add_comm]
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop,
    Theorems100.Nat.sigma_two_pow_eq_mersenne_succ, mersenne, hσq]
  have h1 : 1 ≤ 2 ^ (a + 1) := Nat.one_le_pow _ _ (by decide)
  have h2 : 1 ≤ 3 * 2 ^ a := by omega
  have hq_eq : q + 1 = 3 * 2 ^ a := Nat.sub_add_cancel h2
  rw [hq_eq]
  dsimp [q]
  zify [h1, h2]
  rw [pow_succ']
  ring

private lemma nearPerfectWith_iff {n d : ℕ} :
    NearPerfectWith n d ↔ d ∈ n.properDivisors ∧ sigma 1 n = 2 * n + d := by
  rw [nearPerfectWith_iff_erase]
  refine and_congr_right fun hd => ?_
  have hsum := Finset.add_sum_erase n.properDivisors (fun i => i) hd
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  omega

/-- Mersenne primes yield even near-perfect numbers `2 ^ (k + 1) * mersenne (k + 1)`
with redundant divisor `2 ^ (k + 1)`. -/
theorem mersenne_nearPerfect_two_pow_mul {k : ℕ} (hk : 1 ≤ k) (hq : (mersenne (k + 1)).Prime) :
    NearPerfectWith (2 ^ (k + 1) * mersenne (k + 1)) (2 ^ (k + 1)) := by
  have _ := hk
  set q := mersenne (k + 1)
  have hq_odd : Odd q := mersenne_odd.mpr (by omega)
  refine nearPerfectWith_iff.mpr ⟨Nat.mem_properDivisors.mpr ⟨dvd_mul_right _ _,
    lt_mul_of_one_lt_right (by positivity) hq.one_lt⟩, ?_⟩
  have hcop : Nat.Coprime (2 ^ (k + 1)) q := hq_odd.coprime_two_right.symm.pow_left (k + 1)
  have hσq : sigma 1 q = q + 1 := by
    rw [← pow_one q, sigma_one_apply_prime_pow hq, Finset.sum_range_succ, Finset.sum_range_one,
      pow_zero, pow_one, add_comm]
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop,
    Theorems100.Nat.sigma_two_pow_eq_mersenne_succ, hσq]
  have h1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by decide)
  have h2 : 1 ≤ 2 ^ (k + 2) := Nat.one_le_pow _ _ (by decide)
  have hq_def : q = 2 ^ (k + 1) - 1 := rfl
  have hq1 : q + 1 = 2 ^ (k + 1) := by omega
  rw [hq1, mersenne]
  zify [h1, h2]
  rw [hq_def]
  zify [h1]
  rw [show k + 1 + 1 = (k + 1) + 1 by rfl, pow_succ']
  ring

/-- Mersenne primes also yield even near-perfect numbers `2 ^ k * mersenne (k + 1) ^ 2`
with redundant divisor `mersenne (k + 1)`. -/
theorem mersenne_nearPerfect_mul_sq {k : ℕ} (hq : (mersenne (k + 1)).Prime) :
    NearPerfectWith (2 ^ k * mersenne (k + 1) ^ 2) (mersenne (k + 1)) := by
  set q := mersenne (k + 1)
  have hk_ne : k ≠ 0 := Theorems100.Nat.ne_zero_of_prime_mersenne k hq
  have h2k : 1 < 2 ^ k := Nat.one_lt_two_pow hk_ne
  have hq_odd : Odd q := mersenne_odd.mpr (by omega)
  have hdvd : q ∣ 2 ^ k * q ^ 2 := ⟨2 ^ k * q, by ring⟩
  have hlt : q < 2 ^ k * q ^ 2 := by
    calc q = 1 * q := (one_mul q).symm
         _ < (2 ^ k * q) * q := Nat.mul_lt_mul_of_pos_right
           (Nat.one_lt_mul_iff.mpr ⟨by positivity, hq.pos, Or.inl h2k⟩) hq.pos
         _ = 2 ^ k * q ^ 2 := by ring
  refine nearPerfectWith_iff.mpr ⟨Nat.mem_properDivisors.mpr ⟨hdvd, hlt⟩, ?_⟩
  have hcop : Nat.Coprime (2 ^ k) (q ^ 2) := (hq_odd.coprime_two_right.symm.pow_left k).pow_right 2
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop,
    Theorems100.Nat.sigma_two_pow_eq_mersenne_succ,
    sigma_one_apply_prime_pow hq]
  have hsum : ∑ i ∈ Finset.range (2 + 1), q ^ i = 1 + q + q ^ 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    ring
  rw [hsum]
  change q * (1 + q + q ^ 2) = 2 * (2 ^ k * q ^ 2) + q
  have hq1 : q + 1 = 2 ^ (k + 1) := by
    have hpow : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by decide)
    change 2 ^ (k + 1) - 1 + 1 = 2 ^ (k + 1)
    omega
  have h2pow : 2 * 2 ^ k = q + 1 := by rw [← pow_succ', ← hq1]
  rw [show 2 * (2 ^ k * q ^ 2) = (2 * 2 ^ k) * q ^ 2 by ring, h2pow]
  ring

/-- No multiple of a perfect number can be deficient-perfect. -/
theorem not_deficientPerfectWith_of_perfect_dvd {P n d : ℕ} (hP : P.Perfect) (hdvd : P ∣ n) :
    ¬ DeficientPerfectWith n d := by
  intro ⟨hd, hsum⟩
  have hn_pos : 0 < n := Nat.pos_of_ne_zero fun h0 => by
    subst h0
    simp at hd
  have hd_pos : 0 < d := Nat.pos_of_mem_properDivisors hd
  have hle := Nat.abundancyIndex_le_of_dvd hn_pos.ne' hdvd
  have hP_idx : P.abundancyIndex = 2 := by
    rw [Nat.abundancyIndex, (Nat.perfect_iff_sum_divisors_eq_two_mul hP.2).mp hP]
    have hP_pos : (0 : ℚ) < P := by exact_mod_cast hP.2
    push_cast
    exact mul_div_cancel_right₀ 2 hP_pos.ne'
  rw [hP_idx, Nat.abundancyIndex, ← sigma_one_apply, le_div_iff₀ (by positivity)] at hle
  have h2n : 2 * n ≤ sigma 1 n := by exact_mod_cast hle
  omega

/-!
## 2. Weighted Product-Gap Engine
-/

/-- Elementary recurrence bounding every label in a weighted balanced product
after at most `n` gap-closing rounds with weight multiplier `M`. -/
def weightedLabelBound (k M : ℕ) : ℕ → ℕ → ℕ
  | 0, t => t
  | n + 1, t => weightedLabelBound k M n (max t (k * M * t ^ k))

private lemma weightedLabelBound_mono_right (k M : ℕ) :
    ∀ n {t₁ t₂ : ℕ}, t₁ ≤ t₂ → weightedLabelBound k M n t₁ ≤ weightedLabelBound k M n t₂
  | 0, _, _, h => h
  | n + 1, t₁, t₂, h => by
    apply weightedLabelBound_mono_right k M n
    exact max_le_max h (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h k))

private lemma weightedLabelBound_mono_M (k : ℕ) :
    ∀ n {M₁ M₂ t : ℕ}, M₁ ≤ M₂ → weightedLabelBound k M₁ n t ≤ weightedLabelBound k M₂ n t
  | 0, _, _, _, _ => le_rfl
  | n + 1, M₁, M₂, t, hM => by
    calc weightedLabelBound k M₁ n (max t (k * M₁ * t ^ k))
        ≤ weightedLabelBound k M₁ n (max t (k * M₂ * t ^ k)) :=
          weightedLabelBound_mono_right k M₁ n
            (max_le_max_left t (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left k hM)))
      _ ≤ weightedLabelBound k M₂ n (max t (k * M₂ * t ^ k)) :=
          weightedLabelBound_mono_M k n hM

/-- In a weighted balanced product `U * ∏ a = V * ∏ b` with no balanced proper
numerical prefix, every label is bounded in terms of `k` and `max U V`. -/
theorem labels_bounded_of_weighted_no_balanced_prefix {ι : Type*}
    (s : Finset ι) (label a b : ι → ℕ) {U V k : ℕ} (hk : s.card ≤ k)
    (hfull : U * s.prod a = V * s.prod b)
    (hpair : ∀ i ∈ s, 1 < label i ∧
      (a i = label i ∧ b i = label i - 1 ∨ a i = label i - 1 ∧ b i = label i))
    (hgap : ∀ T : ℕ, (∃ i ∈ s, T < label i) →
      U * (s.filter (fun i => label i ≤ T)).prod a ≠
        V * (s.filter (fun i => label i ≤ T)).prod b) :
    ∀ i ∈ s, label i ≤ weightedLabelBound k (max U V) k 1 := by
  let M := max U V
  let left (t : ℕ) := s.filter (fun i => label i ≤ t)
  let rest (t : ℕ) := s.filter (fun i => t < label i)
  have split (t : ℕ) (f : ι → ℕ) : (left t).prod f * (rest t).prod f = s.prod f := by
    simpa only [left, rest, not_le] using s.prod_filter_mul_prod_filter_not (fun i => label i ≤ t) f
  have main (n t : ℕ) (ht : 1 ≤ t) (hn : (rest t).card ≤ n) :
      ∀ i ∈ s, label i ≤ weightedLabelBound k M n t := by
    induction n generalizing t with
    | zero =>
      have hem : rest t = ∅ := card_eq_zero.mp (by omega)
      intro i hi
      by_contra! h
      have hm : i ∈ rest t := mem_filter.mpr ⟨hi, h⟩
      simp [hem] at hm
    | succ n ih =>
      let t' := max t (k * M * t ^ k)
      have htt : t ≤ t' := le_max_left _ _
      apply ih t' (ht.trans htt)
      by_cases hem : (rest t).Nonempty
      · obtain ⟨j, hj⟩ := hem
        have hne := hgap t ⟨j, (mem_filter.mp hj).1, (mem_filter.mp hj).2⟩
        have heq : (U * (left t).prod a) * (rest t).prod a =
            (V * (left t).prod b) * (rest t).prod b := by
          rw [mul_assoc, mul_assoc, split, split, hfull]
        obtain ⟨i, hi, hl⟩ := exists_small_label_of_balance (rest t) label a b hne heq
          (fun i hi => hpair i (mem_filter.mp hi).1)
        have hpbound (f : ι → ℕ) (hf : ∀ i ∈ s, f i ≤ label i) : (left t).prod f ≤ t ^ k := by
          have hprod := Finset.prod_le_prod₀ (s := left t) (f := f) (g := fun _ => t)
            (fun j _ => Nat.zero_le (f j))
            (fun j hj => (hf j (mem_filter.mp hj).1).trans (mem_filter.mp hj).2)
          rw [prod_const] at hprod
          exact hprod.trans (Nat.pow_le_pow_right ht ((card_le_card (filter_subset _ _)).trans hk))
        have ha := hpbound a (fun j hj => by rcases hpair j hj with ⟨_, h | h⟩ <;> omega)
        have hb := hpbound b (fun j hj => by rcases hpair j hj with ⟨_, h | h⟩ <;> omega)
        have hcard : (rest t).card ≤ k := (card_le_card (filter_subset _ _)).trans hk
        have hU : U * (left t).prod a ≤ M * t ^ k :=
          Nat.mul_le_mul (le_max_left U V) ha
        have hV : V * (left t).prod b ≤ M * t ^ k :=
          Nat.mul_le_mul (le_max_right U V) hb
        have hmax : max (U * (left t).prod a) (V * (left t).prod b) ≤ M * t ^ k := max_le hU hV
        have hle : label i ≤ t' := hl.trans ((Nat.mul_le_mul hcard hmax).trans (by
          dsimp [t']
          rw [← mul_assoc]
          exact le_max_right _ _))
        have hsub : rest t' ⊆ rest t := by
          intro x hx
          exact mem_filter.mpr ⟨(mem_filter.mp hx).1, htt.trans_lt (mem_filter.mp hx).2⟩
        have hlt := card_lt_card ((ssubset_iff_of_subset hsub).mpr
          ⟨i, hi, fun hx => hle.not_gt (mem_filter.mp hx).2⟩)
        omega
      · have hsub : rest t' = ∅ := eq_empty_iff_forall_notMem.mpr (fun i hi => hem
          ⟨i, mem_filter.mpr ⟨(mem_filter.mp hi).1, htt.trans_lt (mem_filter.mp hi).2⟩⟩)
        simp [hsub]
  exact main k 1 le_rfl ((card_le_card (filter_subset _ _)).trans hk)

/-!
## 3. Fixed-`(k, A)` Unrestricted-Parity Finiteness
-/

private lemma self_lt_sigma_one {a : ℕ} (ha : 1 < a) : a < sigma 1 a := by
  rw [sigma_one_apply]
  have hsub : ({1, a} : Finset ℕ) ⊆ a.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Nat.one_mem_divisors.mpr (by omega)
    · exact Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩
  have hsum := Finset.sum_le_sum_of_subset (f := fun x : ℕ => x) hsub
  rw [Finset.sum_pair ha.ne] at hsum
  omega

private theorem odd_part_component_bound {m a k t x labelNone : ℕ}
    (hm : Odd m) (hk : m.primeFactors.card ≤ k)
    (hbal : (2 ^ (a + 1) - 1) * (sigma 1 m * (2 * t)) = 2 ^ (a + 1) * (m * x))
    (hx_odd : Odd x)
    (hnone : 1 < labelNone ∧
      (2 * t = labelNone ∧ x = labelNone - 1 ∨ 2 * t = labelNone - 1 ∧ x = labelNone)) :
    ∀ p ∈ m.primeFactors,
      p ^ (m.factorization p + 1) ≤ weightedLabelBound (2 * k + 1) (2 ^ (a + 1)) (2 * k + 1) 1 := by
  let P := m.primeFactors
  let e := fun p => m.factorization p
  let L := fun p => p ^ (e p + 1)
  let f := fun p => p ^ e p
  let g := fun p => sigma 1 (f p)
  let S := (P.disjSum P).insertNone
  let U := 2 ^ (a + 1) - 1
  let V := 2 ^ (a + 1)
  let label : Option (ℕ ⊕ ℕ) → ℕ := fun i => i.elim labelNone (Sum.elim id L)
  let aFn : Option (ℕ ⊕ ℕ) → ℕ := fun i => i.elim (2 * t) (Sum.elim id (fun p => L p - 1))
  let bFn : Option (ℕ ⊕ ℕ) → ℕ := fun i => i.elim x (Sum.elim (fun p => p - 1) L)
  have hgt (p) (hp : p ∈ P) : 1 < p := (Nat.prime_of_mem_primeFactors hp).one_lt
  have hoddp (p) (hp : p ∈ P) : Odd p := hm.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
  have hless (p) (hp : p ∈ P) : p ≤ L p := by
    dsimp [L]
    rw [pow_succ']
    exact Nat.le_mul_of_pos_right p (pow_pos (hgt p hp).pos _)
  have hg_sum (p) (hp : p ∈ P) : g p = ∑ j ∈ range (e p + 1), p ^ j :=
    sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)
  have hL_sub (p) (hp : p ∈ P) : L p - 1 = (p - 1) * g p := by
    have hgeom := geom_sum_mul_add (p - 1) (e p + 1)
    rw [Nat.sub_add_cancel (hgt p hp).le, ← hg_sum p hp] at hgeom
    change g p * (p - 1) + 1 = L p at hgeom
    rw [mul_comm]
    omega
  have hL_eq (p) : L p = p * f p := pow_succ' p (e p)
  have hpf : P.prod f = m := (Nat.prod_primeFactors_pow_factorization hm.pos.ne').symm
  have hpg : P.prod g = sigma 1 m := (isMultiplicative_sigma.multiplicative_factorization _ hm.pos.ne').symm
  have hfull : U * S.prod aFn = V * S.prod bFn := by
    simp only [S, aFn, bFn, prod_insertNone, prod_disjSum, Option.elim, Sum.elim_inl, Sum.elim_inr,
      id_eq]
    have hLprod1 : (∏ p ∈ P, (L p - 1)) = (∏ p ∈ P, (p - 1)) * P.prod g := by
      rw [← prod_mul_distrib]
      exact prod_congr rfl hL_sub
    have hLprod2 : P.prod L = P.prod id * P.prod f := by
      rw [← prod_mul_distrib]
      exact prod_congr rfl (fun p _ => hL_eq p)
    rw [hLprod1, hLprod2, hpg, hpf]
    calc U * (2 * t * (P.prod id * ((∏ p ∈ P, (p - 1)) * sigma 1 m)))
        = (U * (sigma 1 m * (2 * t))) * (P.prod id * (∏ p ∈ P, (p - 1))) := by ring
      _ = (V * (m * x)) * (P.prod id * (∏ p ∈ P, (p - 1))) := by rw [hbal]
      _ = V * (x * ((∏ p ∈ P, (p - 1)) * (P.prod id * m))) := by ring
  have hcard : S.card ≤ 2 * k + 1 := by
    dsimp [S]
    rw [card_insertNone, card_disjSum]
    change P.card ≤ k at hk
    omega
  have hpair (i) (hi : i ∈ S) : 1 < label i ∧
      (aFn i = label i ∧ bFn i = label i - 1 ∨ aFn i = label i - 1 ∧ bFn i = label i) := by
    cases i with
    | none => exact hnone
    | some i =>
      have hm_ds := some_mem_insertNone.mp hi
      cases i with
      | inl p => exact ⟨hgt p (inl_mem_disjSum.mp hm_ds), .inl ⟨rfl, rfl⟩⟩
      | inr p =>
        have hp := inr_mem_disjSum.mp hm_ds
        exact ⟨(hgt p hp).trans_le (hless p hp), .inr ⟨rfl, rfl⟩⟩
  have hgap (T : ℕ) (hrem : ∃ i ∈ S, T < label i) :
      U * (S.filter (fun i => label i ≤ T)).prod aFn ≠
        V * (S.filter (fun i => label i ≤ T)).prod bFn := by
    intro hleft
    let left := S.filter (fun i => label i ≤ T)
    let rest := S.filter (fun i => T < label i)
    have hsplit (fn : Option (ℕ ⊕ ℕ) → ℕ) : left.prod fn * rest.prod fn = S.prod fn := by
      simpa only [left, rest, not_le] using
        S.prod_filter_mul_prod_filter_not (fun i => label i ≤ T) fn
    have hV_pos : 0 < V := by positivity
    have hb_pos : 0 < left.prod bFn := Finset.prod_pos fun i hi => by
      change 0 < bFn i
      rcases hpair i (mem_filter.mp hi).1 with ⟨hl, ⟨_, hb⟩ | ⟨_, hb⟩⟩ <;> (rw [hb]; omega)
    have hVb_pos : 0 < V * left.prod bFn := mul_pos hV_pos hb_pos
    have hmul : (V * left.prod bFn) * rest.prod aFn = (V * left.prod bFn) * rest.prod bFn := by
      calc (V * left.prod bFn) * rest.prod aFn
          = (U * left.prod aFn) * rest.prod aFn := by rw [hleft]
        _ = U * (left.prod aFn * rest.prod aFn) := by ring
        _ = U * S.prod aFn := by rw [hsplit]
        _ = V * S.prod bFn := hfull
        _ = V * (left.prod bFn * rest.prod bFn) := by rw [hsplit]
        _ = (V * left.prod bFn) * rest.prod bFn := by ring
    have hrest : rest.prod aFn = rest.prod bFn := Nat.eq_of_mul_eq_mul_left hVb_pos hmul
    let u := P.filter (fun p => T < p)
    let c' := P.filter (fun p => T < L p)
    let o := c' \ u
    have huc : u ⊆ c' := fun p hp =>
      mem_filter.mpr ⟨(mem_filter.mp hp).1, (mem_filter.mp hp).2.trans_le (hless p (mem_filter.mp hp).1)⟩
    have hoP : o ⊆ P := sdiff_subset.trans (filter_subset _ _)
    have huP : u ⊆ P := filter_subset _ _
    have hrest_prod (fn : Option (ℕ ⊕ ℕ) → ℕ) : rest.prod fn =
        (if T < label none then fn none else 1) *
          ((∏ p ∈ u, fn (some (.inl p))) * (∏ p ∈ c', fn (some (.inr p)))) := by
      simp only [rest, S, prod_filter, prod_insertNone, prod_disjSum, u, c']
      rfl
    rw [hrest_prod, hrest_prod] at hrest
    have hc_a : (∏ p ∈ c', aFn (some (.inr p))) =
        (∏ p ∈ o, (L p - 1)) * (∏ p ∈ u, (p - 1)) * (∏ p ∈ u, g p) := by
      rw [← prod_sdiff huc]
      have h_u : (∏ p ∈ u, aFn (some (.inr p))) = (∏ p ∈ u, (p - 1)) * (∏ p ∈ u, g p) := by
        rw [← prod_mul_distrib]
        exact prod_congr rfl (fun p hp => hL_sub p (huP hp))
      change (∏ p ∈ o, (L p - 1)) * (∏ p ∈ u, aFn (some (.inr p))) = _
      rw [h_u, mul_assoc]
    have hc_b : (∏ p ∈ c', bFn (some (.inr p))) =
        (∏ p ∈ o, L p) * (∏ p ∈ u, p) * (∏ p ∈ u, f p) := by
      rw [← prod_sdiff huc]
      have h_u : (∏ p ∈ u, bFn (some (.inr p))) = (∏ p ∈ u, p) * (∏ p ∈ u, f p) := by
        rw [← prod_mul_distrib]
        exact prod_congr rfl (fun p _ => hL_eq p)
      change (∏ p ∈ o, L p) * (∏ p ∈ u, bFn (some (.inr p))) = _
      rw [h_u, mul_assoc]
    have hK_pos : 0 < (∏ p ∈ u, p) * (∏ p ∈ u, (p - 1)) :=
      mul_pos (prod_pos fun p hp => (hgt p (huP hp)).pos)
        (prod_pos fun p hp => Nat.sub_pos_of_lt (hgt p (huP hp)))
    have hcancel : (if T < label none then aFn none else 1) * (∏ p ∈ o, (L p - 1)) * (∏ p ∈ u, g p) =
        (if T < label none then bFn none else 1) * (∏ p ∈ o, L p) * (∏ p ∈ u, f p) := by
      apply Nat.eq_of_mul_eq_mul_right hK_pos
      have hl_a : (∏ p ∈ u, aFn (some (.inl p))) = ∏ p ∈ u, p := rfl
      have hl_b : (∏ p ∈ u, bFn (some (.inl p))) = ∏ p ∈ u, (p - 1) := rfl
      calc ((if T < label none then aFn none else 1) * (∏ p ∈ o, (L p - 1)) * (∏ p ∈ u, g p)) *
              ((∏ p ∈ u, p) * (∏ p ∈ u, (p - 1)))
          = (if T < label none then aFn none else 1) *
              ((∏ p ∈ u, aFn (some (.inl p))) * (∏ p ∈ c', aFn (some (.inr p)))) := by
            rw [hc_a, hl_a]; ring
        _ = (if T < label none then bFn none else 1) *
              ((∏ p ∈ u, bFn (some (.inl p))) * (∏ p ∈ c', bFn (some (.inr p)))) := hrest
        _ = ((if T < label none then bFn none else 1) * (∏ p ∈ o, L p) * (∏ p ∈ u, f p)) *
              ((∏ p ∈ u, p) * (∏ p ∈ u, (p - 1))) := by
            rw [hc_b, hl_b]; ring
    have hL_odd : ∀ p ∈ P, Odd (L p) := fun p hp => (hoddp p hp).pow
    have hf_odd : ∀ p ∈ P, Odd (f p) := fun p hp => (hoddp p hp).pow
    have ho_prod_odd : Odd (∏ p ∈ o, L p) :=
      prod_induction L Odd (fun _ _ => Odd.mul) odd_one (fun p hp => hL_odd p (hoP hp))
    have hu_prod_odd : Odd (∏ p ∈ u, f p) :=
      prod_induction f Odd (fun _ _ => Odd.mul) odd_one (fun p hp => hf_odd p (huP hp))
    by_cases hT : T < label none
    · simp only [hT, ↓reduceIte, aFn, bFn, Option.elim] at hcancel
      have hlhs_even : 2 ∣ (2 * t) * (∏ p ∈ o, (L p - 1)) * (∏ p ∈ u, g p) :=
        ⟨t * (∏ p ∈ o, (L p - 1)) * (∏ p ∈ u, g p), by ring⟩
      have hrhs_odd : Odd (x * (∏ p ∈ o, L p) * (∏ p ∈ u, f p)) :=
        (hx_odd.mul ho_prod_odd).mul hu_prod_odd
      exact hrhs_odd.not_two_dvd_nat (hcancel ▸ hlhs_even)
    · simp only [hT, ↓reduceIte, one_mul] at hcancel
      rcases o.eq_empty_or_nonempty with ho_empty | ⟨p, hp⟩
      · have hu_ne : u.Nonempty := by
          obtain ⟨i, hiS, hTi⟩ := hrem
          cases i with
          | none => exact (hT hTi).elim
          | some j =>
            have hj := some_mem_insertNone.mp hiS
            cases j with
            | inl q => exact ⟨q, mem_filter.mpr ⟨inl_mem_disjSum.mp hj, hTi⟩⟩
            | inr q =>
              have hq_c' : q ∈ c' := mem_filter.mpr ⟨inr_mem_disjSum.mp hj, hTi⟩
              have hq_u : q ∈ u := by
                by_contra hnu
                have : q ∈ o := mem_sdiff.mpr ⟨hq_c', hnu⟩
                simp [ho_empty] at this
              exact ⟨q, hq_u⟩
        simp only [ho_empty, prod_empty, one_mul] at hcancel
        have hlt : ∏ q ∈ u, f q < ∏ q ∈ u, g q := by
          apply Finset.prod_lt_prod_of_nonempty₀
          · intro q hq
            exact pow_pos (hgt q (huP hq)).pos _
          · intro q hq
            have hqP := huP hq
            have heq : 0 < e q := (Nat.prime_of_mem_primeFactors hqP).factorization_pos_of_dvd
              hm.pos.ne' (Nat.dvd_of_mem_primeFactors hqP)
            have h1f : 1 < f q := one_lt_pow₀ (hgt q hqP) heq.ne'
            exact self_lt_sigma_one h1f
          · exact hu_ne
        exact hlt.ne hcancel.symm
      · have hpL_odd : Odd (L p) := hL_odd p (hoP hp)
        have hpL_pos : 1 ≤ L p := hpL_odd.pos
        have hpL_even : 2 ∣ L p - 1 := by
          obtain ⟨r, hr⟩ := hpL_odd
          exact ⟨r, by omega⟩
        have hlhs_even : 2 ∣ (∏ q ∈ o, (L q - 1)) * (∏ q ∈ u, g q) :=
          dvd_mul_of_dvd_left (hpL_even.trans (dvd_prod_of_mem (fun q => L q - 1) hp)) _
        have hrhs_odd : Odd ((∏ q ∈ o, L q) * (∏ q ∈ u, f q)) := ho_prod_odd.mul hu_prod_odd
        exact hrhs_odd.not_two_dvd_nat (hcancel ▸ hlhs_even)
  have hmax : max U V = 2 ^ (a + 1) := max_eq_right (Nat.sub_le _ _)
  intro p hp
  have hbound := labels_bounded_of_weighted_no_balanced_prefix S label aFn bFn hcard hfull hpair hgap
    (some (.inr p)) (some_mem_insertNone.mpr (inr_mem_disjSum.mpr hp))
  rwa [hmax] at hbound

private theorem le_of_bounded_prime_count_two_val_aux {n k A t x labelNone : ℕ}
    (hn_pos : 0 < n) (hk : n.primeFactors.card ≤ k) (hA : n.factorization 2 ≤ A)
    (hbal_n : (2 ^ (n.factorization 2 + 1) - 1) * (sigma 1 (ordCompl[2] n) * (2 * t)) =
      2 ^ (n.factorization 2 + 1) * (ordCompl[2] n * x))
    (hx_odd : Odd x)
    (hnone : 1 < labelNone ∧
      (2 * t = labelNone ∧ x = labelNone - 1 ∨ 2 * t = labelNone - 1 ∧ x = labelNone)) :
    n ≤ 2 ^ A * (max 1 (weightedLabelBound (2 * k + 1) (2 ^ (A + 1)) (2 * k + 1) 1)) ^ k := by
  set a := n.factorization 2
  set m := ordCompl[2] n
  have hm_pos : 0 < m := Nat.ordCompl_pos 2 hn_pos.ne'
  have hm_odd : Odd m := Nat.odd_iff.mpr (by
    have hnd := Nat.not_dvd_ordCompl Nat.prime_two hn_pos.ne'
    omega)
  have hm_cards : m.primeFactors.card ≤ k :=
    (Finset.card_le_card (Nat.primeFactors_mono (Nat.ordCompl_dvd n 2) hn_pos.ne')).trans hk
  have hcomp := odd_part_component_bound hm_odd hm_cards hbal_n hx_odd hnone
  let B := max 1 (weightedLabelBound (2 * k + 1) (2 ^ (A + 1)) (2 * k + 1) 1)
  have hmono : weightedLabelBound (2 * k + 1) (2 ^ (a + 1)) (2 * k + 1) 1 ≤
      weightedLabelBound (2 * k + 1) (2 ^ (A + 1)) (2 * k + 1) 1 :=
    weightedLabelBound_mono_M (2 * k + 1) (2 * k + 1)
      (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right hA 1))
  have hm_le : m ≤ B ^ k := by
    rw [Nat.prod_primeFactors_pow_factorization hm_pos.ne']
    have hcap (p) (hp : p ∈ m.primeFactors) : p ^ m.factorization p ≤ B :=
      (Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hp).pos (Nat.le_succ _)).trans
        ((hcomp p hp).trans (hmono.trans (le_max_right _ _)))
    have hprod := Finset.prod_le_prod₀
      (fun p (_ : p ∈ m.primeFactors) => Nat.zero_le (p ^ m.factorization p)) hcap
    rw [Finset.prod_const] at hprod
    exact hprod.trans (Nat.pow_le_pow_right (le_max_left 1 _) hm_cards)
  have hn_eq : 2 ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  rw [← hn_eq]
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hA) hm_le

/-- Explicit size bound for any deficient-perfect number with at most `k` distinct
prime factors and `2`-adic valuation at most `A`. -/
theorem DeficientPerfectWith.le_of_bounded_prime_count_two_val {n d k A : ℕ}
    (h : DeficientPerfectWith n d) (hk : n.primeFactors.card ≤ k) (hA : n.factorization 2 ≤ A) :
    n ≤ 2 ^ A * (max 1 (weightedLabelBound (2 * k + 1) (2 ^ (A + 1)) (2 * k + 1) 1)) ^ k := by
  have hn_pos : 0 < n := Nat.pos_of_ne_zero fun h0 => by
    have hd := h.1
    subst h0
    simp at hd
  obtain ⟨⟨t, ht⟩, hlt⟩ := Nat.mem_properDivisors.mp h.1
  have ht2 : 2 ≤ t := by
    by_contra! ht1
    exact hlt.not_ge (ht ▸ (Nat.mul_le_mul_left d (by omega : t ≤ 1)).trans_eq (Nat.mul_one d))
  set a := n.factorization 2
  set m := ordCompl[2] n
  have hm_odd : Odd m := Nat.odd_iff.mpr (by
    have hnd := Nat.not_dvd_ordCompl Nat.prime_two hn_pos.ne'
    omega)
  have hn_eq : 2 ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hcop : Nat.Coprime (2 ^ a) m := hm_odd.coprime_two_right.symm.pow_left a
  have hσ : sigma 1 n = (2 ^ (a + 1) - 1) * sigma 1 m := by
    rw [← hn_eq, isMultiplicative_sigma.map_mul_of_coprime hcop,
      Theorems100.Nat.sigma_two_pow_eq_mersenne_succ, mersenne]
  have hbal_n : (2 ^ (a + 1) - 1) * (sigma 1 m * (2 * t)) = 2 ^ (a + 1) * (m * (2 * t - 1)) := by
    have h2 : sigma 1 n + d = 2 * n := h.2
    have h1 : 1 ≤ 2 ^ (a + 1) := Nat.one_le_pow _ _ (by decide)
    have ht1 : 1 ≤ 2 * t := by omega
    have hmul : (sigma 1 n + d) * (2 * t) = (2 * n) * (2 * t) := congrArg (· * (2 * t)) h2
    have hdt : d * (2 * t) = 2 * n := by rw [ht]; ring
    rw [add_mul, hdt, hσ, ← hn_eq] at hmul
    zify [h1, ht1]
    have hmul_z : (((2 ^ (a + 1) - 1 : ℕ) : ℤ) * (sigma 1 m : ℤ)) * (2 * (t : ℤ)) +
        2 * ((2 : ℤ) ^ a * (m : ℤ)) =
        2 * ((2 : ℤ) ^ a * (m : ℤ)) * (2 * (t : ℤ)) := by
      exact_mod_cast hmul
    rw [Nat.cast_sub h1] at hmul_z
    push_cast at hmul_z ⊢
    rw [pow_succ'] at hmul_z ⊢
    linarith
  have hx_odd : Odd (2 * t - 1) := Nat.odd_iff.mpr (by omega)
  have hnone : 1 < 2 * t ∧ (2 * t = 2 * t ∧ 2 * t - 1 = 2 * t - 1 ∨
      2 * t = 2 * t - 1 ∧ 2 * t - 1 = 2 * t) := ⟨by omega, .inl ⟨rfl, rfl⟩⟩
  exact le_of_bounded_prime_count_two_val_aux hn_pos hk hA hbal_n hx_odd hnone

/-- Explicit size bound for any near-perfect number with at most `k` distinct
prime factors and `2`-adic valuation at most `A`. -/
theorem NearPerfectWith.le_of_bounded_prime_count_two_val {n d k A : ℕ}
    (h : NearPerfectWith n d) (hk : n.primeFactors.card ≤ k) (hA : n.factorization 2 ≤ A) :
    n ≤ 2 ^ A * (max 1 (weightedLabelBound (2 * k + 1) (2 ^ (A + 1)) (2 * k + 1) 1)) ^ k := by
  obtain ⟨hd_mem, h2⟩ := nearPerfectWith_iff.mp h
  have hn_pos : 0 < n := Nat.pos_of_ne_zero fun h0 => by
    subst h0
    simp at hd_mem
  obtain ⟨⟨t, ht⟩, hlt⟩ := Nat.mem_properDivisors.mp hd_mem
  have ht2 : 2 ≤ t := by
    by_contra! ht1
    exact hlt.not_ge (ht ▸ (Nat.mul_le_mul_left d (by omega : t ≤ 1)).trans_eq (Nat.mul_one d))
  set a := n.factorization 2
  set m := ordCompl[2] n
  have hm_odd : Odd m := Nat.odd_iff.mpr (by
    have hnd := Nat.not_dvd_ordCompl Nat.prime_two hn_pos.ne'
    omega)
  have hn_eq : 2 ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hcop : Nat.Coprime (2 ^ a) m := hm_odd.coprime_two_right.symm.pow_left a
  have hσ : sigma 1 n = (2 ^ (a + 1) - 1) * sigma 1 m := by
    rw [← hn_eq, isMultiplicative_sigma.map_mul_of_coprime hcop,
      Theorems100.Nat.sigma_two_pow_eq_mersenne_succ, mersenne]
  have hbal_n : (2 ^ (a + 1) - 1) * (sigma 1 m * (2 * t)) = 2 ^ (a + 1) * (m * (2 * t + 1)) := by
    have hmul : sigma 1 n * (2 * t) = (2 * n + d) * (2 * t) := congrArg (· * (2 * t)) h2
    have hdt : d * (2 * t) = 2 * n := by rw [ht]; ring
    rw [add_mul, hdt, hσ, ← hn_eq] at hmul
    calc (2 ^ (a + 1) - 1) * (sigma 1 m * (2 * t))
        = ((2 ^ (a + 1) - 1) * sigma 1 m) * (2 * t) := by ring
      _ = 2 * (2 ^ a * m) * (2 * t) + 2 * (2 ^ a * m) := hmul
      _ = (2 * 2 ^ a) * (m * (2 * t + 1)) := by ring
      _ = 2 ^ (a + 1) * (m * (2 * t + 1)) := by rw [← pow_succ']
  have hx_odd : Odd (2 * t + 1) := ⟨t, by ring⟩
  have hnone : 1 < 2 * t + 1 ∧ (2 * t = 2 * t + 1 ∧ 2 * t + 1 = 2 * t + 1 - 1 ∨
      2 * t = 2 * t + 1 - 1 ∧ 2 * t + 1 = 2 * t + 1) := ⟨by omega, .inr ⟨rfl, rfl⟩⟩
  exact le_of_bounded_prime_count_two_val_aux hn_pos hk hA hbal_n hx_odd hnone

/-- Only finitely many deficient-perfect pairs `(n, d)` have at most `k` distinct
prime factors and `2`-adic valuation at most `A`. -/
theorem finite_deficientPerfect_pairs_of_bounded_prime_count_two_val (k A : ℕ) :
    Set.Finite {v : ℕ × ℕ | v.1.primeFactors.card ≤ k ∧ v.1.factorization 2 ≤ A ∧
      DeficientPerfectWith v.1 v.2} := by
  let N := 2 ^ A * (max 1 (weightedLabelBound (2 * k + 1) (2 ^ (A + 1)) (2 * k + 1) 1)) ^ k
  apply ((Set.finite_le_nat N).prod (Set.finite_le_nat N)).subset
  rintro ⟨n, d⟩ ⟨hk, hA, h⟩
  have hn := h.le_of_bounded_prime_count_two_val hk hA
  exact ⟨hn, (Nat.mem_properDivisors.mp h.1).2.le.trans hn⟩

/-- Only finitely many near-perfect pairs `(n, d)` have at most `k` distinct
prime factors and `2`-adic valuation at most `A`. -/
theorem finite_nearPerfect_pairs_of_bounded_prime_count_two_val (k A : ℕ) :
    Set.Finite {v : ℕ × ℕ | v.1.primeFactors.card ≤ k ∧ v.1.factorization 2 ≤ A ∧
      NearPerfectWith v.1 v.2} := by
  let N := 2 ^ A * (max 1 (weightedLabelBound (2 * k + 1) (2 ^ (A + 1)) (2 * k + 1) 1)) ^ k
  apply ((Set.finite_le_nat N).prod (Set.finite_le_nat N)).subset
  rintro ⟨n, d⟩ ⟨hk, hA, h⟩
  have hn := h.le_of_bounded_prime_count_two_val hk hA
  exact ⟨hn, (Nat.mem_properDivisors.mp (nearPerfectWith_iff.mp h).1).2.le.trans hn⟩

/-- Only finitely many deficient-perfect numbers `n` have at most `k` distinct
prime factors and `2`-adic valuation at most `A`. -/
theorem finite_deficientPerfect_of_bounded_prime_count_two_val (k A : ℕ) :
    Set.Finite {n : ℕ | n.primeFactors.card ≤ k ∧ n.factorization 2 ≤ A ∧
      ∃ d, DeficientPerfectWith n d} := by
  let N := 2 ^ A * (max 1 (weightedLabelBound (2 * k + 1) (2 ^ (A + 1)) (2 * k + 1) 1)) ^ k
  apply (Set.finite_le_nat N).subset
  rintro n ⟨hk, hA, d, h⟩
  exact h.le_of_bounded_prime_count_two_val hk hA

/-- Only finitely many near-perfect numbers `n` have at most `k` distinct
prime factors and `2`-adic valuation at most `A`. -/
theorem finite_nearPerfect_of_bounded_prime_count_two_val (k A : ℕ) :
    Set.Finite {n : ℕ | n.primeFactors.card ≤ k ∧ n.factorization 2 ≤ A ∧
      ∃ d, NearPerfectWith n d} := by
  let N := 2 ^ A * (max 1 (weightedLabelBound (2 * k + 1) (2 ^ (A + 1)) (2 * k + 1) 1)) ^ k
  apply (Set.finite_le_nat N).subset
  rintro n ⟨hk, hA, d, h⟩
  exact h.le_of_bounded_prime_count_two_val hk hA

end OddPerfect
