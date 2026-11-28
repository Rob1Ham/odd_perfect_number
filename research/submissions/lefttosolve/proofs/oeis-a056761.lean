import OMAStatements.S_oeis_a056761

-- Problem: A056761: Odd numbers less than the cube of their number of divisors.
-- Statement: statements/oeis-a056761.lean
-- Credit: @Rob1Ham

namespace OMA.S_oeis_a056761

private lemma card_divisors_prime_pow {p e : ℕ} (hp : p.Prime) :
    (p ^ e).divisors.card = e + 1 := by
  rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]

private lemma cube_step_one {k : ℕ} (hk : 1 ≤ k) : (k + 2) ^ 3 ≤ 4 * (k + 1) ^ 3 := by
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
  have h : 4 * (t + 1 + 1) ^ 3 = (t + 1 + 2) ^ 3 + (3 * t ^ 3 + 15 * t ^ 2 + 21 * t + 5) := by
    ring
  omega

private lemma cube_step_two {k : ℕ} (hk : 2 ≤ k) : (k + 2) ^ 3 ≤ 3 * (k + 1) ^ 3 := by
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 2 := ⟨k - 2, by omega⟩
  have h : 3 * (t + 2 + 1) ^ 3 = (t + 2 + 2) ^ 3 + (2 * t ^ 3 + 15 * t ^ 2 + 33 * t + 17) := by
    ring
  omega

private lemma eleven_pow_bound {p e : ℕ} (hp : 11 ≤ p) (he : 1 ≤ e) :
    p * (e + 1) ^ 3 ≤ 8 * p ^ e := by
  induction e with
  | zero => omega
  | succ k ih =>
    rcases eq_or_ne k 0 with rfl | hk0
    · simp [mul_comm]
    · have hk1 : 1 ≤ k := by omega
      have hih := ih hk1
      have hstep := cube_step_one hk1
      have h4p : 4 * (k + 1) ^ 3 ≤ p * (k + 1) ^ 3 :=
        Nat.mul_le_mul_right _ (by omega)
      calc p * (k + 1 + 1) ^ 3
          = p * (k + 2) ^ 3 := by ring
        _ ≤ p * (p * (k + 1) ^ 3) := Nat.mul_le_mul_left p (hstep.trans h4p)
        _ ≤ p * (8 * p ^ k) := Nat.mul_le_mul_left p hih
        _ = 8 * p ^ (k + 1) := by rw [pow_succ']; ring

private lemma ge_eleven_pow_le {p e : ℕ} (hp : 11 ≤ p) :
    (e + 1) ^ 3 ≤ p ^ e := by
  rcases eq_or_ne e 0 with rfl | he0
  · simp
  · have h1 := eleven_pow_bound (e := e) hp (by omega)
    have h2 : 8 * p ^ e ≤ p * p ^ e := Nat.mul_le_mul_right _ (by omega)
    exact Nat.le_of_mul_le_mul_left (h1.trans h2) (show 0 < p by omega)

private lemma seven_pow_bound (e : ℕ) : 7 * (e + 1) ^ 3 ≤ 8 * 7 ^ e := by
  induction e with
  | zero => decide
  | succ k ih =>
    rcases eq_or_ne k 0 with rfl | hk0
    · decide
    · have hk1 : 1 ≤ k := by omega
      have hstep : (k + 2) ^ 3 ≤ 7 * (k + 1) ^ 3 :=
        (cube_step_one hk1).trans (Nat.mul_le_mul_right _ (by decide))
      calc 7 * (k + 1 + 1) ^ 3
          = 7 * (k + 2) ^ 3 := by ring
        _ ≤ 7 * (7 * (k + 1) ^ 3) := Nat.mul_le_mul_left 7 hstep
        _ ≤ 7 * (8 * 7 ^ k) := Nat.mul_le_mul_left 7 ih
        _ = 8 * 7 ^ (k + 1) := by rw [pow_succ']; ring

private lemma five_pow_bound (e : ℕ) : 5 * (e + 1) ^ 3 ≤ 8 * 5 ^ e := by
  induction e with
  | zero => decide
  | succ k ih =>
    rcases eq_or_ne k 0 with rfl | hk0
    · decide
    · have hk1 : 1 ≤ k := by omega
      have hstep : (k + 2) ^ 3 ≤ 5 * (k + 1) ^ 3 :=
        (cube_step_one hk1).trans (Nat.mul_le_mul_right _ (by decide))
      calc 5 * (k + 1 + 1) ^ 3
          = 5 * (k + 2) ^ 3 := by ring
        _ ≤ 5 * (5 * (k + 1) ^ 3) := Nat.mul_le_mul_left 5 hstep
        _ ≤ 5 * (8 * 5 ^ k) := Nat.mul_le_mul_left 5 ih
        _ = 8 * 5 ^ (k + 1) := by rw [pow_succ']; ring

private lemma three_pow_bound (e : ℕ) : (e + 1) ^ 3 ≤ 3 * 3 ^ e := by
  induction e with
  | zero => decide
  | succ k ih =>
    rcases eq_or_ne k 0 with rfl | hk0
    · decide
    · rcases eq_or_ne k 1 with rfl | hk1
      · decide
      · have hk2 : 2 ≤ k := by omega
        have hstep := cube_step_two hk2
        calc (k + 1 + 1) ^ 3
            = (k + 2) ^ 3 := by ring
          _ ≤ 3 * (k + 1) ^ 3 := hstep
          _ ≤ 3 * (3 * 3 ^ k) := Nat.mul_le_mul_left 3 ih
          _ = 3 * 3 ^ (k + 1) := by rw [pow_succ']

private lemma bound_ge_11 {m : ℕ} (hm : 0 < m) (h11 : ∀ p : ℕ, p.Prime → p ∣ m → 11 ≤ p) :
    m.divisors.card ^ 3 ≤ m := by
  revert hm h11
  refine Nat.strongRecOn m fun m ih hm h11 => ?_
  rcases eq_or_ne m 1 with rfl | hm1
  · simp
  · set p := m.minFac
    have hp : p.Prime := Nat.minFac_prime hm1
    have hp_dvd : p ∣ m := Nat.minFac_dvd m
    have hp11 : 11 ≤ p := h11 p hp hp_dvd
    obtain ⟨e, r, hr, hm_eq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p hp.ne_one
    have he_pos : 0 < e := by
      by_contra he0
      have hez : e = 0 := by omega
      rw [hez, pow_zero, one_mul] at hm_eq
      exact hr (hm_eq ▸ hp_dvd)
    have hr_pos : 0 < r := by
      by_contra hr0
      have hrz : r = 0 := by omega
      rw [hrz, mul_zero] at hm_eq
      omega
    have hp_pow_gt : 1 < p ^ e := one_lt_pow₀ hp.one_lt he_pos.ne'
    have hr_lt : r < m := by
      calc r = 1 * r := (one_mul r).symm
        _ < p ^ e * r := Nat.mul_lt_mul_of_pos_right hp_pow_gt hr_pos
        _ = m := hm_eq.symm
    have hr11 : ∀ q : ℕ, q.Prime → q ∣ r → 11 ≤ q := fun q hq hqr =>
      h11 q hq (hm_eq ▸ dvd_mul_of_dvd_right hqr _)
    have hcop : (p ^ e).Coprime r := (hp.coprime_iff_not_dvd.mpr hr).pow_left e
    have hcard : m.divisors.card = (e + 1) * r.divisors.card := by
      rw [hm_eq, hcop.card_divisors_mul, card_divisors_prime_pow hp]
    rw [hcard, mul_pow, hm_eq]
    exact Nat.mul_le_mul (ge_eleven_pow_le hp11) (ih r hr_lt hr_pos hr11)

private lemma bound_ge_11_gt_one {m a : ℕ} (hm : 1 < m) (ha : 11 ≤ a)
    (hmin : ∀ p : ℕ, p.Prime → p ∣ m → a ≤ p) :
    a * m.divisors.card ^ 3 ≤ 8 * m := by
  set p := m.minFac
  have hp : p.Prime := Nat.minFac_prime hm.ne'
  have hp_dvd : p ∣ m := Nat.minFac_dvd m
  have hpa : a ≤ p := hmin p hp hp_dvd
  have hp11 : 11 ≤ p := ha.trans hpa
  obtain ⟨e, r, hr, hm_eq⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : m ≠ 0) p hp.ne_one
  have he_pos : 1 ≤ e := by
    by_contra he0
    have hez : e = 0 := by omega
    rw [hez, pow_zero, one_mul] at hm_eq
    exact hr (hm_eq ▸ hp_dvd)
  have hr_pos : 0 < r := by
    by_contra hr0
    have hrz : r = 0 := by omega
    rw [hrz, mul_zero] at hm_eq
    omega
  have hr11 : ∀ q : ℕ, q.Prime → q ∣ r → 11 ≤ q := fun q hq hqr =>
    ha.trans (hmin q hq (hm_eq ▸ dvd_mul_of_dvd_right hqr _))
  have hcop : (p ^ e).Coprime r := (hp.coprime_iff_not_dvd.mpr hr).pow_left e
  have hcard : m.divisors.card = (e + 1) * r.divisors.card := by
    rw [hm_eq, hcop.card_divisors_mul, card_divisors_prime_pow hp]
  have hpe : a * (e + 1) ^ 3 ≤ 8 * p ^ e :=
    (Nat.mul_le_mul_right _ hpa).trans (eleven_pow_bound hp11 he_pos)
  have hre : r.divisors.card ^ 3 ≤ r := bound_ge_11 hr_pos hr11
  calc a * m.divisors.card ^ 3
      = (a * (e + 1) ^ 3) * r.divisors.card ^ 3 := by rw [hcard, mul_pow]; ring
    _ ≤ (8 * p ^ e) * r := Nat.mul_le_mul hpe hre
    _ = 8 * m := by rw [hm_eq]; ring

private lemma peel_prime_bound {m p₀ : ℕ} (A B C D : ℕ) (hm : 0 < m) (hp₀ : p₀.Prime)
    (hloc : ∀ e : ℕ, A * (e + 1) ^ 3 ≤ B * p₀ ^ e)
    (hrem : ∀ r : ℕ, 0 < r → ¬ p₀ ∣ r → (∀ q : ℕ, q.Prime → q ∣ r → q ∣ m) →
      C * r.divisors.card ^ 3 ≤ D * r) :
    (A * C) * m.divisors.card ^ 3 ≤ (B * D) * m := by
  obtain ⟨e, r, hr, hm_eq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p₀ hp₀.ne_one
  have hr_pos : 0 < r := by
    by_contra hr0
    have hrz : r = 0 := by omega
    rw [hrz, mul_zero] at hm_eq
    omega
  have hcop : (p₀ ^ e).Coprime r := (hp₀.coprime_iff_not_dvd.mpr hr).pow_left e
  have hcard : m.divisors.card = (e + 1) * r.divisors.card := by
    rw [hm_eq, hcop.card_divisors_mul, card_divisors_prime_pow hp₀]
  have hr_bound := hrem r hr_pos hr (fun q _ hqr => hm_eq ▸ dvd_mul_of_dvd_right hqr _)
  calc (A * C) * m.divisors.card ^ 3
      = (A * (e + 1) ^ 3) * (C * r.divisors.card ^ 3) := by rw [hcard, mul_pow]; ring
    _ ≤ (B * p₀ ^ e) * (D * r) := Nat.mul_le_mul (hloc e) hr_bound
    _ = (B * D) * m := by rw [hm_eq]; ring

private lemma bound_ge_7 {m : ℕ} (hm : 0 < m) (h7 : ∀ p : ℕ, p.Prime → p ∣ m → 7 ≤ p) :
    7 * m.divisors.card ^ 3 ≤ 8 * m := by
  have h := peel_prime_bound 7 8 1 1 hm (by decide : Nat.Prime 7) seven_pow_bound
    (fun r hr_pos hr7 hsub => by
      simpa only [one_mul] using bound_ge_11 hr_pos (fun q hq hqr => by
        have hq7 := h7 q hq (hsub q hq hqr)
        have hne7 : q ≠ 7 := fun h => hr7 (h ▸ hqr)
        have hne8 : q ≠ 8 := fun h => by subst h; exact absurd hq (by decide)
        have hne9 : q ≠ 9 := fun h => by subst h; exact absurd hq (by decide)
        have hne10 : q ≠ 10 := fun h => by subst h; exact absurd hq (by decide)
        omega))
  simpa using h

private lemma bound_ge_5 {m : ℕ} (hm : 0 < m) (h5 : ∀ p : ℕ, p.Prime → p ∣ m → 5 ≤ p) :
    35 * m.divisors.card ^ 3 ≤ 64 * m := by
  have h := peel_prime_bound 5 8 7 8 hm (by decide : Nat.Prime 5) five_pow_bound
    (fun r hr_pos hr5 hsub => bound_ge_7 hr_pos (fun q hq hqr => by
      have hq5 := h5 q hq (hsub q hq hqr)
      have hne5 : q ≠ 5 := fun h => hr5 (h ▸ hqr)
      have hne6 : q ≠ 6 := fun h => by subst h; exact absurd hq (by decide)
      omega))
  simpa using h

private lemma bound_ge_3 {m : ℕ} (hm : 0 < m) (h3 : ∀ p : ℕ, p.Prime → p ∣ m → 3 ≤ p) :
    35 * m.divisors.card ^ 3 ≤ 192 * m := by
  have h := peel_prime_bound 1 3 35 64 hm (by decide : Nat.Prime 3)
    (fun e => by simpa only [one_mul] using three_pow_bound e)
    (fun r hr_pos hr3 hsub => bound_ge_5 hr_pos (fun q hq hqr => by
      have hq3 := h3 q hq (hsub q hq hqr)
      have hne3 : q ≠ 3 := fun h => hr3 (h ▸ hqr)
      have hne4 : q ≠ 4 := fun h => by subst h; exact absurd hq (by decide)
      omega))
  simpa using h

private lemma bound_odd {m : ℕ} (ho : Odd m) :
    35 * m.divisors.card ^ 3 ≤ 192 * m :=
  bound_ge_3 ho.pos fun p hp hpm => by
    have hp2 := hp.two_le
    have hne2 : p ≠ 2 := fun h => ho.not_two_dvd_nat (h ▸ hpm)
    omega

private lemma component_strict_ineq {n p e r : ℕ} (h : IsA056761 n) (hp : p.Prime)
    (hn : n = p ^ e * r) (hr : ¬ p ∣ r) :
    35 * p ^ e < 192 * (e + 1) ^ 3 := by
  obtain ⟨ho, hlt⟩ := h
  have hr_odd : Odd r := ho.of_dvd_nat ⟨p ^ e, by rw [hn, mul_comm]⟩
  have hcop : (p ^ e).Coprime r := (hp.coprime_iff_not_dvd.mpr hr).pow_left e
  have hcard : n.divisors.card = (e + 1) * r.divisors.card := by
    rw [hn, hcop.card_divisors_mul, card_divisors_prime_pow hp]
  have hrb := bound_odd hr_odd
  have hmul : (35 * p ^ e) * r < (192 * (e + 1) ^ 3) * r := by
    calc (35 * p ^ e) * r
        = 35 * n := by rw [hn]; ring
      _ < 35 * n.divisors.card ^ 3 := Nat.mul_lt_mul_of_pos_left hlt (by decide)
      _ = (e + 1) ^ 3 * (35 * r.divisors.card ^ 3) := by rw [hcard, mul_pow]; ring
      _ ≤ (e + 1) ^ 3 * (192 * r) := Nat.mul_le_mul_left _ hrb
      _ = (192 * (e + 1) ^ 3) * r := by ring
  exact Nat.lt_of_mul_lt_mul_right hmul

private lemma no_prime_ge_47 {n p : ℕ} (h : IsA056761 n) (hp : p.Prime) (hpn : p ∣ n) :
    p ≤ 43 := by
  by_contra hp44
  have hp47 : 47 ≤ p := by
    have hne44 : p ≠ 44 := fun h => by subst h; exact absurd hp (by decide)
    have hne45 : p ≠ 45 := fun h => by subst h; exact absurd hp (by decide)
    have hne46 : p ≠ 46 := fun h => by subst h; exact absurd hp (by decide)
    omega
  obtain ⟨e, r, hr, hn_eq⟩ := Nat.exists_eq_pow_mul_and_not_dvd h.1.pos.ne' p hp.ne_one
  have he1 : 1 ≤ e := by
    by_contra he0
    have hez : e = 0 := by omega
    rw [hez, pow_zero, one_mul] at hn_eq
    exact hr (hn_eq ▸ hpn)
  have hlt := component_strict_ineq h hp hn_eq hr
  have h11 := eleven_pow_bound (show 11 ≤ p by omega) he1
  have hle : 8 * (192 * (e + 1) ^ 3) ≤ 8 * (35 * p ^ e) := by
    calc 8 * (192 * (e + 1) ^ 3)
        = 1536 * (e + 1) ^ 3 := by ring
      _ ≤ (35 * p) * (e + 1) ^ 3 := Nat.mul_le_mul_right _ (by omega)
      _ = 35 * (p * (e + 1) ^ 3) := by ring
      _ ≤ 35 * (8 * p ^ e) := Nat.mul_le_mul_left 35 h11
      _ = 8 * (35 * p ^ e) := by ring
  have := Nat.le_of_mul_le_mul_left hle (by decide)
  omega

private lemma tail_pow_bound {p e₀ e : ℕ} (hp3 : 3 ≤ p) (he₀ : 2 ≤ e₀)
    (hbase : 192 * (e₀ + 1) ^ 3 ≤ 35 * p ^ e₀) (hle : e₀ ≤ e) :
    192 * (e + 1) ^ 3 ≤ 35 * p ^ e := by
  induction e, hle using Nat.le_induction with
  | base => exact hbase
  | succ k hk ih =>
    have hk2 : 2 ≤ k := he₀.trans hk
    have hstep := cube_step_two hk2
    have h3p : 3 * (k + 1) ^ 3 ≤ p * (k + 1) ^ 3 := Nat.mul_le_mul_right _ hp3
    calc 192 * (k + 1 + 1) ^ 3
        = 192 * (k + 2) ^ 3 := by ring
      _ ≤ 192 * (p * (k + 1) ^ 3) := Nat.mul_le_mul_left 192 (hstep.trans h3p)
      _ = p * (192 * (k + 1) ^ 3) := by ring
      _ ≤ p * (35 * p ^ k) := Nat.mul_le_mul_left p ih
      _ = 35 * p ^ (k + 1) := by rw [pow_succ']; ring

private def specs : List (ℕ × ℕ × ℕ × ℕ) :=
  [(3, 7, 192, 35), (5, 4, 64, 35), (7, 3, 8, 7),
   (11, 2, 1, 1), (13, 2, 1, 1), (17, 2, 1, 1),
   (19, 1, 1, 1), (23, 1, 1, 1), (29, 1, 1, 1),
   (31, 1, 1, 1), (37, 1, 1, 1), (41, 1, 1, 1), (43, 1, 1, 1)]

private def genExp (p D T : ℕ) (f : ℕ → ℕ → List ℕ) : ℕ → ℕ → List ℕ
  | 0, e => f (D * p ^ e) (T * (e + 1))
  | k + 1, e => f (D * p ^ e) (T * (e + 1)) ++ genExp p D T f k (e + 1)

private def gen (D T : ℕ) : List (ℕ × ℕ × ℕ × ℕ) → List ℕ
  | [] => if D < T ^ 3 then [D] else []
  | (p, maxE, num, den) :: rest =>
      if T ^ 3 * num ≤ D * den then []
      else if 11 ≤ p ∧ 8 * T ^ 3 ≤ p * D then (if D < T ^ 3 then [D] else [])
      else genExp p D T (fun D' T' => gen D' T' rest) maxE 0

private lemma mem_genExp_iff {p D T : ℕ} {f : ℕ → ℕ → List ℕ} :
    ∀ k e₀ x, x ∈ genExp p D T f k e₀ ↔
      ∃ j ≤ k, x ∈ f (D * p ^ (e₀ + j)) (T * (e₀ + j + 1))
  | 0, e₀, x => by
    simp only [genExp, Nat.le_zero, exists_eq_left, add_zero]
  | k + 1, e₀, x => by
    simp only [genExp, List.mem_append, mem_genExp_iff k (e₀ + 1) x]
    constructor
    · rintro (h0 | ⟨j, hj, hmem⟩)
      · exact ⟨0, Nat.zero_le _, by simpa using h0⟩
      · refine ⟨j + 1, Nat.succ_le_succ hj, ?_⟩
        have he1 : e₀ + 1 + j = e₀ + (j + 1) := by omega
        rwa [he1] at hmem
    · rintro ⟨j, hj, hmem⟩
      rcases j with _ | j
      · exact Or.inl (by simpa using hmem)
      · refine Or.inr ⟨j, Nat.le_of_succ_le_succ hj, ?_⟩
        have he1 : e₀ + 1 + j = e₀ + (j + 1) := by omega
        rwa [he1]

private def SpecOK : ℕ → List (ℕ × ℕ × ℕ × ℕ) → Prop
  | _, [] => True
  | D, (p, maxE, _, _) :: rest =>
      p.Prime ∧ Odd p ∧ ¬ p ∣ D ∧
      2 ≤ maxE + 1 ∧ 192 * (maxE + 2) ^ 3 ≤ 35 * p ^ (maxE + 1) ∧
      (∀ item ∈ rest, p < item.1) ∧
      SpecOK D rest

private lemma specOK_mul_pow {D p e : ℕ} {rest : List (ℕ × ℕ × ℕ × ℕ)}
    (hp : p.Prime) (hlt : ∀ item ∈ rest, p < item.1) (hok : SpecOK D rest) :
    SpecOK (D * p ^ e) rest := by
  induction rest generalizing D with
  | nil => trivial
  | cons hd tl ih =>
    rcases hd with ⟨q, mE, n1, d1⟩
    obtain ⟨hq, hqo, hqD, hm1, hm2, hqtl, htl⟩ := hok
    have hpq : p < q := hlt (q, mE, n1, d1) (List.mem_cons_self ..)
    have hq_ndvd : ¬ q ∣ D * p ^ e := by
      intro hdvd
      rcases hq.dvd_mul.mp hdvd with h1 | h2
      · exact hqD h1
      · have hqp := hq.dvd_of_dvd_pow h2
        have := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
        omega
    exact ⟨hq, hqo, hq_ndvd, hm1, hm2, hqtl,
      ih (fun item hitem => hlt item (List.mem_cons_of_mem _ hitem)) htl⟩

private lemma gen_dvd_form {D T q : ℕ} {s : List (ℕ × ℕ × ℕ × ℕ)} (hq : q.Prime)
    (hok : SpecOK D s) (hgt : ∀ item ∈ s, q < item.1) :
    ∀ x ∈ gen D T s, ∃ u : ℕ, x = D * u ∧ ¬ q ∣ u := by
  induction s generalizing D T with
  | nil =>
    intro x hx
    simp only [gen] at hx
    split_ifs at hx with hlt
    · simp only [List.mem_singleton] at hx
      exact ⟨1, by rw [hx, mul_one], hq.not_dvd_one⟩
    · simp at hx
  | cons hd tl ih =>
    rcases hd with ⟨p, maxE, num, den⟩
    obtain ⟨hp, _, _, _, _, hlt_tl, htl_ok⟩ := hok
    intro x hx
    simp only [gen] at hx
    split_ifs at hx with h1 h2 h3
    · simp at hx
    · simp only [List.mem_singleton] at hx
      exact ⟨1, by rw [hx, mul_one], hq.not_dvd_one⟩
    · simp at hx
    · obtain ⟨j, _, hjmem⟩ := (mem_genExp_iff maxE 0 x).mp hx
      simp only [zero_add] at hjmem
      have hqp : q < p := hgt (p, maxE, num, den) (List.mem_cons_self ..)
      have htl_gt : ∀ item ∈ tl, q < item.1 := fun item hi =>
        hgt item (List.mem_cons_of_mem _ hi)
      obtain ⟨u, rfl, hqu⟩ := ih (specOK_mul_pow hp hlt_tl htl_ok) htl_gt x hjmem
      refine ⟨p ^ j * u, by ring, ?_⟩
      intro hdvd
      rcases hq.dvd_mul.mp hdvd with hqp_pow | hqu'
      · have hqp_dvd := hq.dvd_of_dvd_pow hqp_pow
        have := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp_dvd
        omega
      · exact hqu hqu'

private lemma gen_sound {D T : ℕ} {s : List (ℕ × ℕ × ℕ × ℕ)}
    (hodd : Odd D) (hcard : D.divisors.card = T) (hok : SpecOK D s) :
    ∀ x ∈ gen D T s, IsA056761 x := by
  induction s generalizing D T with
  | nil =>
    intro x hx
    simp only [gen] at hx
    split_ifs at hx with hlt
    · simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨hodd, hcard ▸ hlt⟩
    · simp at hx
  | cons hd tl ih =>
    rcases hd with ⟨p, maxE, num, den⟩
    obtain ⟨hp, hpo, hpD, _, _, hlt, htl⟩ := hok
    intro x hx
    simp only [gen] at hx
    split_ifs at hx with h1 h2 h3
    · simp at hx
    · simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨hodd, hcard ▸ h3⟩
    · simp at hx
    · obtain ⟨j, _, hjmem⟩ := (mem_genExp_iff maxE 0 x).mp hx
      simp only [zero_add] at hjmem
      have hcop : D.Coprime (p ^ j) := (hp.coprime_iff_not_dvd.mpr hpD).symm.pow_right j
      have hcard' : (D * p ^ j).divisors.card = T * (j + 1) := by
        rw [hcop.card_divisors_mul, hcard, card_divisors_prime_pow hp]
      exact ih (hodd.mul (hpo.pow)) hcard' (specOK_mul_pow hp hlt htl) x hjmem

private lemma genExp_nodup {p D T : ℕ} {f : ℕ → ℕ → List ℕ} (hp : p.Prime) (hpD : ¬ p ∣ D) :
    ∀ k e₀,
      (∀ j ≤ k, (f (D * p ^ (e₀ + j)) (T * (e₀ + j + 1))).Nodup) →
      (∀ j ≤ k, ∀ x ∈ f (D * p ^ (e₀ + j)) (T * (e₀ + j + 1)),
        ∃ u : ℕ, x = (D * p ^ (e₀ + j)) * u ∧ ¬ p ∣ u) →
      (genExp p D T f k e₀).Nodup
  | 0, e₀, hnd, _ => by
    simpa [genExp] using hnd 0 (Nat.le_refl 0)
  | k + 1, e₀, hnd, hdvd => by
    rw [genExp, List.nodup_append']
    refine ⟨?_, ?_, ?_⟩
    · simpa using hnd 0 (Nat.zero_le _)
    · refine genExp_nodup hp hpD k (e₀ + 1) (fun j hj => ?_) (fun j hj => ?_)
      · have he1 : e₀ + 1 + j = e₀ + (j + 1) := by omega
        rw [he1]
        exact hnd (j + 1) (Nat.succ_le_succ hj)
      · have he1 : e₀ + 1 + j = e₀ + (j + 1) := by omega
        rw [he1]
        exact hdvd (j + 1) (Nat.succ_le_succ hj)
    · intro x hx1 hx2
      obtain ⟨u₁, hx1_eq, hpu₁⟩ := hdvd 0 (Nat.zero_le _) x (by simpa using hx1)
      simp only [add_zero] at hx1_eq
      obtain ⟨j, hj, hjmem⟩ := (mem_genExp_iff k (e₀ + 1) x).mp hx2
      have he1 : e₀ + 1 + j = e₀ + (j + 1) := by omega
      rw [he1] at hjmem
      obtain ⟨u₂, hx2_eq, _⟩ := hdvd (j + 1) (Nat.succ_le_succ hj) x hjmem
      have heq : p ^ e₀ * (D * u₁) = p ^ e₀ * (p * (p ^ j * D * u₂)) := by
        calc p ^ e₀ * (D * u₁)
            = (D * p ^ e₀) * u₁ := by ring
          _ = x := hx1_eq.symm
          _ = (D * p ^ (e₀ + (j + 1))) * u₂ := hx2_eq
          _ = p ^ e₀ * (p * (p ^ j * D * u₂)) := by rw [pow_add, pow_add, pow_one]; ring
      have hcancel := Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos e₀) heq
      have hp_dvd_Du : p ∣ D * u₁ := ⟨p ^ j * D * u₂, hcancel⟩
      rcases hp.dvd_mul.mp hp_dvd_Du with hD | hu
      · exact hpD hD
      · exact hpu₁ hu

private lemma gen_nodup {D T : ℕ} {s : List (ℕ × ℕ × ℕ × ℕ)} (hok : SpecOK D s) :
    (gen D T s).Nodup := by
  induction s generalizing D T with
  | nil =>
    simp only [gen]
    split_ifs <;> simp
  | cons hd tl ih =>
    rcases hd with ⟨p, maxE, num, den⟩
    obtain ⟨hp, _, hpD, _, _, hlt, htl⟩ := hok
    simp only [gen]
    split_ifs
    · simp
    · simp
    · simp
    · refine genExp_nodup hp hpD maxE 0 (fun j _ => ?_) (fun j _ => ?_)
      · simp only [zero_add]
        exact ih (specOK_mul_pow hp hlt htl)
      · simp only [zero_add]
        exact gen_dvd_form hp (specOK_mul_pow hp hlt htl) hlt

private def MinPrimeFor : List (ℕ × ℕ × ℕ × ℕ) → ℕ → Prop
  | [], m => ∀ q : ℕ, q.Prime → q ∣ m → 47 ≤ q
  | (p, _, _, _) :: _, m => ∀ q : ℕ, q.Prime → q ∣ m → p ≤ q

private def NextPrimeMin : ℕ → List (ℕ × ℕ × ℕ × ℕ) → Prop
  | p, [] => ∀ q : ℕ, q.Prime → p < q → 47 ≤ q
  | p, (q₀, _, _, _) :: _ => ∀ q : ℕ, q.Prime → p < q → q₀ ≤ q

private def EnvOK : List (ℕ × ℕ × ℕ × ℕ) → Prop
  | [] => True
  | (p, _, num, den) :: rest =>
      0 < den ∧
      (∀ m : ℕ, 0 < m → (∀ q : ℕ, q.Prime → q ∣ m → p ≤ q) →
        den * m.divisors.card ^ 3 ≤ num * m) ∧
      NextPrimeMin p rest ∧
      EnvOK rest

private lemma gen_complete {D T m : ℕ} {s : List (ℕ × ℕ × ℕ × ℕ)}
    (hD : 0 < D) (hm : 0 < m) (hcard : (D * m).divisors.card = T * m.divisors.card)
    (hterm : IsA056761 (D * m)) (hok : SpecOK D s) (henv : EnvOK s)
    (hmin : MinPrimeFor s m) :
    D * m ∈ gen D T s := by
  induction s generalizing D T m with
  | nil =>
    have hm1 : m = 1 := by
      by_contra hm_ne1
      set q := m.minFac
      have hq : q.Prime := Nat.minFac_prime hm_ne1
      have hqm : q ∣ m := Nat.minFac_dvd m
      have hq47 : 47 ≤ q := hmin q hq hqm
      have hq43 : q ≤ 43 := no_prime_ge_47 hterm hq (dvd_mul_of_dvd_right hqm D)
      omega
    subst hm1
    simp only [mul_one, Nat.divisors_one, Finset.card_singleton] at hcard hterm ⊢
    have hlt : D < T ^ 3 := hcard ▸ hterm.2
    simp [gen, hlt]
  | cons hd tl ih =>
    rcases hd with ⟨p, maxE, num, den⟩
    obtain ⟨hp, hpo, hpD, hmax1, hmax2, hlt_tl, htl_ok⟩ := hok
    obtain ⟨hden_pos, hbound, hnext, htl_env⟩ := henv
    change ∀ q : ℕ, q.Prime → q ∣ m → p ≤ q at hmin
    have hnot_cut1 : ¬ T ^ 3 * num ≤ D * den := by
      intro hcut
      have hm_b := hbound m hm hmin
      have hbad := hterm.2
      rw [hcard, mul_pow] at hbad
      have h1 : (D * m) * den < (T ^ 3 * m.divisors.card ^ 3) * den :=
        Nat.mul_lt_mul_of_pos_right hbad hden_pos
      have h2 : (T ^ 3 * m.divisors.card ^ 3) * den ≤ (D * m) * den := by
        calc (T ^ 3 * m.divisors.card ^ 3) * den
            = T ^ 3 * (den * m.divisors.card ^ 3) := by ring
          _ ≤ T ^ 3 * (num * m) := Nat.mul_le_mul_left _ hm_b
          _ = (T ^ 3 * num) * m := by ring
          _ ≤ (D * den) * m := Nat.mul_le_mul_right _ hcut
          _ = (D * m) * den := by ring
      exact h1.not_ge h2
    by_cases hcut2 : 11 ≤ p ∧ 8 * T ^ 3 ≤ p * D
    · have hm1 : m = 1 := by
        by_contra hm_ne1
        have hm_gt1 : 1 < m := by omega
        have h11_gt := bound_ge_11_gt_one hm_gt1 hcut2.1 hmin
        have hbad := hterm.2
        rw [hcard, mul_pow] at hbad
        have h1 : p * (D * m) < p * (T ^ 3 * m.divisors.card ^ 3) :=
          Nat.mul_lt_mul_of_pos_left hbad hp.pos
        have h2 : p * (T ^ 3 * m.divisors.card ^ 3) ≤ p * (D * m) := by
          calc p * (T ^ 3 * m.divisors.card ^ 3)
              = T ^ 3 * (p * m.divisors.card ^ 3) := by ring
            _ ≤ T ^ 3 * (8 * m) := Nat.mul_le_mul_left _ h11_gt
            _ = (8 * T ^ 3) * m := by ring
            _ ≤ (p * D) * m := Nat.mul_le_mul_right _ hcut2.2
            _ = p * (D * m) := by ring
        exact h1.not_ge h2
      subst hm1
      simp only [mul_one, Nat.divisors_one, Finset.card_singleton] at hcard hterm ⊢
      have hlt_D : D < T ^ 3 := hcard ▸ hterm.2
      simp [gen, hnot_cut1, hcut2, hlt_D]
    · simp only [gen, hnot_cut1, hcut2, ↓reduceIte]
      obtain ⟨e, r, hr, hm_eq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p hp.ne_one
      have hr_pos : 0 < r := by
        by_contra hr0
        have hrz : r = 0 := by omega
        rw [hrz, mul_zero] at hm_eq
        omega
      have hDr_ndvd : ¬ p ∣ D * r := by
        intro hdvd
        rcases hp.dvd_mul.mp hdvd with h1 | h2
        · exact hpD h1
        · exact hr h2
      have hDm_eq : D * m = p ^ e * (D * r) := by rw [hm_eq]; ring
      have he_le : e ≤ maxE := by
        by_contra he_gt
        have hp3 : 3 ≤ p := by
          have hp2 := hp.two_le
          have hne2 : p ≠ 2 := fun h => hpo.not_two_dvd_nat (h ▸ dvd_rfl)
          omega
        have htail := tail_pow_bound hp3 hmax1 hmax2 (show maxE + 1 ≤ e by omega)
        have hstrict := component_strict_ineq hterm hp hDm_eq hDr_ndvd
        omega
      have hcop_pe_r : (p ^ e).Coprime r := (hp.coprime_iff_not_dvd.mpr hr).pow_left e
      have hm_card : m.divisors.card = (e + 1) * r.divisors.card := by
        rw [hm_eq, hcop_pe_r.card_divisors_mul, card_divisors_prime_pow hp]
      have hDpe_r : (D * p ^ e) * r = D * m := by rw [hm_eq]; ring
      have hcard' : ((D * p ^ e) * r).divisors.card = (T * (e + 1)) * r.divisors.card := by
        rw [hDpe_r, hcard, hm_card, mul_assoc]
      have hterm' : IsA056761 ((D * p ^ e) * r) := hDpe_r.symm ▸ hterm
      have hr_min : MinPrimeFor tl r := by
        cases tl with
        | nil =>
          intro q hq hqr
          have hqp : p ≤ q := hmin q hq (hm_eq ▸ dvd_mul_of_dvd_right hqr _)
          have hne : q ≠ p := fun h => hr (h ▸ hqr)
          exact hnext q hq (by omega)
        | cons hd2 tl2 =>
          rcases hd2 with ⟨q₀, m2, n2, d2⟩
          intro q hq hqr
          have hqp : p ≤ q := hmin q hq (hm_eq ▸ dvd_mul_of_dvd_right hqr _)
          have hne : q ≠ p := fun h => hr (h ▸ hqr)
          exact hnext q hq (by omega)
      have hmem_tl := ih (Nat.mul_pos hD (pow_pos hp.pos e)) hr_pos hcard' hterm'
        (specOK_mul_pow hp hlt_tl htl_ok) htl_env hr_min
      rw [hDpe_r] at hmem_tl
      exact (mem_genExp_iff maxE 0 (D * m)).mpr ⟨e, he_le, by simpa using hmem_tl⟩

private lemma gap_no_prime {a b : ℕ} (hgap : ∀ j ∈ Finset.Ioo a b, ¬ j.Prime) :
    ∀ q : ℕ, q.Prime → a < q → b ≤ q := by
  intro q hq haq
  by_contra hqb
  exact hgap q (Finset.mem_Ioo.mpr ⟨haq, by omega⟩) hq

private lemma specOK_specs : SpecOK 1 specs := by
  dsimp [specs, SpecOK]
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, trivial⟩

private lemma envOK_specs : EnvOK specs := by
  have b11 : ∀ p : ℕ, 11 ≤ p → ∀ m : ℕ, 0 < m →
      (∀ q : ℕ, q.Prime → q ∣ m → p ≤ q) → 1 * m.divisors.card ^ 3 ≤ 1 * m := by
    intro p hp m hm hmin
    simpa using bound_ge_11 hm (fun q hq hqm => hp.trans (hmin q hq hqm))
  dsimp [specs, EnvOK, NextPrimeMin]
  refine ⟨by decide, fun m hm h => bound_ge_3 hm h, gap_no_prime (by decide), ?_⟩
  refine ⟨by decide, fun m hm h => bound_ge_5 hm h, gap_no_prime (by decide), ?_⟩
  refine ⟨by decide, fun m hm h => bound_ge_7 hm h, gap_no_prime (by decide), ?_⟩
  refine ⟨by decide, b11 11 (by decide), gap_no_prime (by decide), ?_⟩
  refine ⟨by decide, b11 13 (by decide), gap_no_prime (by decide), ?_⟩
  refine ⟨by decide, b11 17 (by decide), gap_no_prime (by decide), ?_⟩
  refine ⟨by decide, b11 19 (by decide), gap_no_prime (by decide), ?_⟩
  refine ⟨by decide, b11 23 (by decide), gap_no_prime (by decide), ?_⟩
  refine ⟨by decide, b11 29 (by decide), gap_no_prime (by decide), ?_⟩
  refine ⟨by decide, b11 31 (by decide), gap_no_prime (by decide), ?_⟩
  refine ⟨by decide, b11 37 (by decide), gap_no_prime (by decide), ?_⟩
  refine ⟨by decide, b11 41 (by decide), gap_no_prime (by decide), ?_⟩
  exact ⟨by decide, b11 43 (by decide), gap_no_prime (by decide), trivial⟩

private theorem mem_gen_iff (n : ℕ) : n ∈ gen 1 1 specs ↔ IsA056761 n := by
  constructor
  · exact gen_sound odd_one (by simp) specOK_specs n
  · intro hn
    have h1n : 1 * n = n := one_mul n
    have hmem := gen_complete (D := 1) (T := 1) (m := n) (s := specs)
      (by decide) hn.1.pos (by simp) (by rwa [h1n]) specOK_specs envOK_specs
      (fun q hq hqn => by
        have hq2 := hq.two_le
        have hne2 : q ≠ 2 := fun h => hn.1.not_two_dvd_nat (h ▸ hqn)
        omega)
    rwa [h1n] at hmem

private def listMax : List ℕ → ℕ
  | [] => 0
  | x :: xs => max x (listMax xs)

private def listMem (a : ℕ) : List ℕ → Bool
  | [] => false
  | x :: xs => (a == x) || listMem a xs

private lemma le_listMax {x : ℕ} {l : List ℕ} (hx : x ∈ l) : x ≤ listMax l := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hys
    · exact le_max_left x (listMax ys)
    · exact (ih hys).trans (le_max_right y (listMax ys))

private lemma mem_of_listMem {a : ℕ} {l : List ℕ} (h : listMem a l = true) : a ∈ l := by
  induction l with
  | nil => simp [listMem] at h
  | cons y ys ih =>
    simp only [listMem, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | hys
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih hys)

set_option maxRecDepth 20000 in
private lemma gen_len : (gen 1 1 specs).length = 267 := rfl

set_option maxRecDepth 20000 in
private lemma gen_max : listMax (gen 1 1 specs) = 883575 := rfl

set_option maxRecDepth 20000 in
private lemma gen_has_883575 : listMem 883575 (gen 1 1 specs) = true := rfl

theorem solution_lemma :
    IsA056761 883575 ∧
    (∀ n : ℕ, IsA056761 n → n ≤ 883575) ∧
    {n : ℕ | IsA056761 n}.ncard = 267 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (mem_gen_iff 883575).mp (mem_of_listMem gen_has_883575)
  · intro n hn
    have hmem : n ∈ gen 1 1 specs := (mem_gen_iff n).mpr hn
    exact gen_max ▸ le_listMax hmem
  · have hset : {n : ℕ | IsA056761 n} = ((gen 1 1 specs).toFinset : Set ℕ) := by
      ext n
      simp [mem_gen_iff]
    rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup (gen_nodup specOK_specs), gen_len]

end OMA.S_oeis_a056761

theorem OMA.solution : type_of% @OMA.S_oeis_a056761.main := by
  exact OMA.S_oeis_a056761.solution_lemma
