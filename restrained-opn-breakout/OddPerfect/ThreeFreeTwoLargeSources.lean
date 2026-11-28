module

public import OddPerfect.ThreeFreeRestrainedClosure
public import OddPerfect.ZelinskyFullSlope
public import OddPerfect.Euler
public import OddPerfect.Forcing
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Sort
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Three-Free Two-Large-Sources Obstruction (`OddPerfect.ThreeFreeTwoLargeSources`)

Strengthens the three-free restrained elimination (`Two_le_largeSources_of_three_free`) by
constraining the `1 [MOD 3]` vs `2 [MOD 3]` partition of `largeSources N q`:

1. `seven_le_twoModThreeLarge_and_cardFactors_of_oneModThreeLarge_empty`:
   If `¬ 3 ∣ N` and `oneModThreeLargeSources N q = ∅`, then
   `7 ≤ (twoModThreeLargeSources N q).card ∧ 29 ≤ cardFactors N`.
2. `oneModThreeLarge_nonempty_or_seven_le_largeSources_of_three_free`:
   If `¬ 3 ∣ N`, then `(oneModThreeLargeSources N q).Nonempty ∨ 7 ≤ (largeSources N q).card`.
3. `two_le_oneModThreeLarge_or_three_le_largeSources_of_three_free`:
   If `¬ 3 ∣ N`, then `2 ≤ (oneModThreeLargeSources N q).card ∨ 3 ≤ (largeSources N q).card`.
4. `three_free_card_largeSources_two_forces_all_oneModThree`:
   If `¬ 3 ∣ N` and `(largeSources N q).card = 2`, then `(oneModThreeLargeSources N q).card = 2`,
   `twoModThreeLargeSources N q = ∅`, and `∀ r ∈ largeSources N q, r % 3 = 1`.
-/

public section

namespace OddPerfect

open ArithmeticFunction

/-- For every `3`-free odd perfect number `N`, the Euler prime `q` satisfies
`q % 12 = 1` and `13 ≤ q`. -/
theorem three_free_euler_prime_mod_twelve {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (h3 : ¬ 3 ∣ N) :
    q % 12 = 1 ∧ 13 ≤ q := by
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hq_dvd_N : q ∣ N := Nat.dvd_of_mem_primeFactors hq
  have hsplit : N = q ^ N.factorization q * ordCompl[q] N :=
    (Nat.ordProj_mul_ordCompl_eq_self N q).symm
  have hq_ndvd : ¬ q ∣ ordCompl[q] N := Nat.not_dvd_ordCompl hq_prime ho.pos.ne'
  have hsig_dvd : sigma 1 (q ^ N.factorization q) ∣ 2 * ordCompl[q] N :=
    sigma_exact_pow_dvd_twice_cofactor hN hq_prime hsplit hq_ndvd
  have he_odd : Odd (N.factorization q) := Nat.odd_iff.mpr (by omega)
  have hq1_dvd : q + 1 ∣ 2 * N :=
    (succ_dvd_sigma_prime_pow hq_prime he_odd).trans
      (hsig_dvd.trans (Nat.mul_dvd_mul_left 2 (Nat.ordCompl_dvd N q)))
  have hq3_ne0 : q % 3 ≠ 0 := fun h0 =>
    h3 ((Nat.dvd_of_mod_eq_zero h0).trans hq_dvd_N)
  have hq3_ne2 : q % 3 ≠ 2 := by
    intro h2
    have h3_dvd_q1 : 3 ∣ q + 1 := Nat.dvd_of_mod_eq_zero (by omega)
    have h3_dvd_2N : 3 ∣ 2 * N := h3_dvd_q1.trans hq1_dvd
    rcases (by decide : Nat.Prime 3).dvd_mul.mp h3_dvd_2N with h32 | h3N
    · exact (by decide : ¬ 3 ∣ 2) h32
    · exact h3 h3N
  have := hq_prime.two_le
  exact ⟨by omega, by omega⟩


open Finset ArithmeticFunction

private lemma nat_mul_lt_mul_tfl {a b c d : ℕ} (h1 : a < b) (h2 : c < d) : a * c < b * d :=
  lt_of_le_of_lt (Nat.mul_le_mul_right c h1.le) (Nat.mul_lt_mul_of_pos_left h2 (by omega))

private lemma eq_pow_of_primeFactors_subset_tfl {n p : ℕ} (hn : n ≠ 0) (hsub : n.primeFactors ⊆ {p}) :
    n = p ^ n.factorization p := by
  have hprod := Nat.prod_primeFactors_pow_factorization hn
  by_cases hp : p ∈ n.primeFactors
  · have heq : n.primeFactors = {p} :=
      Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hp)
    rw [heq, Finset.prod_singleton] at hprod
    exact hprod
  · have heq : n.primeFactors = ∅ := by
      ext x
      simp only [Finset.notMem_empty, iff_false]
      intro hx
      exact hp (Finset.mem_singleton.mp (hsub hx) ▸ hx)
    have hfz : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    rw [heq, Finset.prod_empty] at hprod
    rw [hfz, pow_zero]
    exact hprod

private lemma eq_mul_pow_of_primeFactors_subset_pair_tfl {n p r : ℕ} (hn : n ≠ 0) (hpr : p ≠ r)
    (hsub : n.primeFactors ⊆ {p, r}) :
    n = p ^ n.factorization p * r ^ n.factorization r := by
  have hprod := Nat.prod_primeFactors_pow_factorization hn
  have hmul : (∏ x ∈ n.primeFactors, x ^ n.factorization x) =
      ∏ x ∈ ({p, r} : Finset ℕ), x ^ n.factorization x := by
    apply Finset.prod_subset hsub
    intro x _ hx_not
    have hfz : n.factorization x = 0 := Finsupp.notMem_support_iff.mp hx_not
    rw [hfz, pow_zero]
  conv_lhs => rw [hprod, hmul, Finset.prod_pair hpr]

private lemma sigma_prime_pow_ratio_lt_tfl {p k c₁ c₂ : ℕ} (hp : p.Prime) (hc₁ : 0 < c₁)
    (hcoef : c₁ * p ≤ c₂ * (p - 1)) :
    c₁ * sigma 1 (p ^ k) < c₂ * p ^ k := by
  have hgeom : (p - 1) * sigma 1 (p ^ k) < p * p ^ k := by
    rw [mul_comm (p - 1), mul_comm p, sigma_one_apply_prime_pow hp]
    have h := geom_sum_mul_add (p - 1) (k + 1)
    rw [Nat.sub_add_cancel hp.one_lt.le, pow_succ] at h
    omega
  have h1 : (p - 1) * (c₁ * sigma 1 (p ^ k)) < (p - 1) * (c₂ * p ^ k) := by
    calc
      (p - 1) * (c₁ * sigma 1 (p ^ k))
          = c₁ * ((p - 1) * sigma 1 (p ^ k)) := by ring
      _ < c₁ * (p * p ^ k) := Nat.mul_lt_mul_of_pos_left hgeom hc₁
      _ = (c₁ * p) * p ^ k := by ring
      _ ≤ (c₂ * (p - 1)) * p ^ k := Nat.mul_le_mul_right (p ^ k) hcoef
      _ = (p - 1) * (c₂ * p ^ k) := by ring
  exact Nat.lt_of_mul_lt_mul_left h1

private lemma sq_prod_ratio_lt_tfl {u₀ P Q c₁ c₂ : ℕ} (hc₁ : 0 < c₁)
    (hgap_prod : 3 * u₀ * P < (3 * u₀ + 4) * Q)
    (hcoef : c₁ * (3 * u₀ + 4) ≤ c₂ * (3 * u₀)) :
    c₁ * P < c₂ * Q := by
  have h1 : (3 * u₀) * (c₁ * P) < (3 * u₀) * (c₂ * Q) := by
    calc
      (3 * u₀) * (c₁ * P) = c₁ * (3 * u₀ * P) := by ring
      _ < c₁ * ((3 * u₀ + 4) * Q) := Nat.mul_lt_mul_of_pos_left hgap_prod hc₁
      _ = (c₁ * (3 * u₀ + 4)) * Q := by ring
      _ ≤ (c₂ * (3 * u₀)) * Q := Nat.mul_le_mul_right Q hcoef
      _ = (3 * u₀) * (c₂ * Q) := by ring
  exact Nat.lt_of_mul_lt_mul_left h1

private lemma abundancy_contradiction3_le {N σq PS PQ q_pow QS QQ cq dq cs ds cQ dQ : ℕ}
    (_hN_pos : 0 < N)
    (hσ_eq : σq * PS * PQ = 2 * N)
    (hN_eq : q_pow * QS * QQ = N)
    (hq : cq * σq < dq * q_pow)
    (hs : cs * PS < ds * QS)
    (hPQ_pos : 0 < cQ * PQ)
    (hPQ : cQ * PQ ≤ dQ * QQ)
    (hineq : dq * ds * dQ ≤ 2 * (cq * cs * cQ)) : False := by
  have hlt2 : (cq * σq) * (cs * PS) < (dq * q_pow) * (ds * QS) :=
    nat_mul_lt_mul_tfl hq hs
  have hprod : ((cq * σq) * (cs * PS)) * (cQ * PQ) <
      ((dq * q_pow) * (ds * QS)) * (dQ * QQ) :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlt2 hPQ_pos) (Nat.mul_le_mul_left _ hPQ)
  have hLHS : ((cq * σq) * (cs * PS)) * (cQ * PQ) = (cq * cs * cQ) * (σq * PS * PQ) := by ring
  have hRHS : ((dq * q_pow) * (ds * QS)) * (dQ * QQ) = (dq * ds * dQ) * (q_pow * QS * QQ) := by ring
  rw [hLHS, hRHS, hσ_eq, hN_eq] at hprod
  have hle : (dq * ds * dQ) * N ≤ (2 * (cq * cs * cQ)) * N := Nat.mul_le_mul_right N hineq
  have hlt : (2 * (cq * cs * cQ)) * N < (2 * (cq * cs * cQ)) * N := by
    calc
      (2 * (cq * cs * cQ)) * N = (cq * cs * cQ) * (2 * N) := by ring
      _ < (dq * ds * dQ) * N := hprod
      _ ≤ (2 * (cq * cs * cQ)) * N := hle
  exact lt_irrefl _ hlt

private lemma abundancy_contradiction5_le
    {N σq σ1 σ2 Pev Pod q_pow r1_pow r2_pow Qev Qod cq dq cr1 dr1 cr2 dr2 cev dev cod dod : ℕ}
    (_hN_pos : 0 < N)
    (hσ_eq : σq * σ1 * σ2 * Pev * Pod = 2 * N)
    (hN_eq : q_pow * r1_pow * r2_pow * Qev * Qod = N)
    (hq : cq * σq < dq * q_pow)
    (hr1 : cr1 * σ1 < dr1 * r1_pow)
    (hr2 : cr2 * σ2 < dr2 * r2_pow)
    (hpev_pos : 0 < cev * Pev)
    (hpev : cev * Pev ≤ dev * Qev)
    (hpod_pos : 0 < cod * Pod)
    (hpod : cod * Pod ≤ dod * Qod)
    (hineq : dq * dr1 * dr2 * dev * dod ≤ 2 * (cq * cr1 * cr2 * cev * cod)) : False := by
  have hlt2 : (cq * σq) * (cr1 * σ1) < (dq * q_pow) * (dr1 * r1_pow) :=
    nat_mul_lt_mul_tfl hq hr1
  have hlt3 : ((cq * σq) * (cr1 * σ1)) * (cr2 * σ2) <
      ((dq * q_pow) * (dr1 * r1_pow)) * (dr2 * r2_pow) :=
    nat_mul_lt_mul_tfl hlt2 hr2
  have hlt4 : (((cq * σq) * (cr1 * σ1)) * (cr2 * σ2)) * (cev * Pev) <
      (((dq * q_pow) * (dr1 * r1_pow)) * (dr2 * r2_pow)) * (dev * Qev) :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlt3 hpev_pos) (Nat.mul_le_mul_left _ hpev)
  have hprod : ((((cq * σq) * (cr1 * σ1)) * (cr2 * σ2)) * (cev * Pev)) * (cod * Pod) <
      ((((dq * q_pow) * (dr1 * r1_pow)) * (dr2 * r2_pow)) * (dev * Qev)) * (dod * Qod) :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlt4 hpod_pos) (Nat.mul_le_mul_left _ hpod)
  have hLHS : ((((cq * σq) * (cr1 * σ1)) * (cr2 * σ2)) * (cev * Pev)) * (cod * Pod) =
      (cq * cr1 * cr2 * cev * cod) * (σq * σ1 * σ2 * Pev * Pod) := by ring
  have hRHS : ((((dq * q_pow) * (dr1 * r1_pow)) * (dr2 * r2_pow)) * (dev * Qev)) * (dod * Qod) =
      (dq * dr1 * dr2 * dev * dod) * (q_pow * r1_pow * r2_pow * Qev * Qod) := by ring
  rw [hLHS, hRHS, hσ_eq, hN_eq] at hprod
  have hle : (dq * dr1 * dr2 * dev * dod) * N ≤ (2 * (cq * cr1 * cr2 * cev * cod)) * N :=
    Nat.mul_le_mul_right N hineq
  have hlt : (2 * (cq * cr1 * cr2 * cev * cod)) * N <
      (2 * (cq * cr1 * cr2 * cev * cod)) * N := by
    calc
      (2 * (cq * cr1 * cr2 * cev * cod)) * N = (cq * cr1 * cr2 * cev * cod) * (2 * N) := by ring
      _ < (dq * dr1 * dr2 * dev * dod) * N := hprod
      _ ≤ (2 * (cq * cr1 * cr2 * cev * cod)) * N := hle
  exact lt_irrefl _ hlt

private def evenIdx : List ℕ → List ℕ
  | [] => []
  | [x] => [x]
  | x :: _ :: xs => x :: evenIdx xs

private def oddIdx : List ℕ → List ℕ
  | [] => []
  | [_] => []
  | _ :: y :: xs => y :: oddIdx xs

private lemma prod_map_evenIdx_mul_oddIdx (f : ℕ → ℕ) :
    ∀ L : List ℕ, (L.map f).prod = ((evenIdx L).map f).prod * ((oddIdx L).map f).prod
  | [] => by simp [evenIdx, oddIdx]
  | [x] => by simp [evenIdx, oddIdx]
  | x :: y :: xs => by
      simp only [evenIdx, oddIdx, List.map_cons, List.prod_cons]
      rw [prod_map_evenIdx_mul_oddIdx f xs]
      ring

private lemma mem_evenIdx_subset : ∀ {L : List ℕ} {x : ℕ}, x ∈ evenIdx L → x ∈ L
  | [], _ => by simp [evenIdx]
  | [a], x => by simp [evenIdx]
  | a :: b :: xs, x => by
      simp only [evenIdx, List.mem_cons]
      rintro (rfl | hx)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (mem_evenIdx_subset hx))

private lemma mem_oddIdx_subset : ∀ {L : List ℕ} {x : ℕ}, x ∈ oddIdx L → x ∈ L
  | [], _ => by simp [oddIdx]
  | [a], _ => by simp [oddIdx]
  | a :: b :: xs, x => by
      simp only [oddIdx, List.mem_cons]
      rintro (rfl | hx)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (mem_oddIdx_subset hx))

private lemma oddIdx_mem_tail : ∀ {h : ℕ} {t : List ℕ} {y : ℕ}, y ∈ oddIdx (h :: t) → y ∈ t
  | _, [], _ => by simp [oddIdx]
  | _, b :: xs, y => by
      simp only [oddIdx, List.mem_cons]
      rintro (rfl | hy)
      · exact Or.inl rfl
      · exact Or.inr (mem_oddIdx_subset hy)

private lemma evenIdx_head?_cons (a : ℕ) (t : List ℕ) : (evenIdx (a :: t)).head? = some a := by
  cases t with
  | nil => simp [evenIdx]
  | cons b xs => simp [evenIdx]

private lemma evenIdx_isChain {R : ℕ → ℕ → Prop} :
    ∀ L : List ℕ, L.IsChain (· < ·) →
      (∀ a b c, a ∈ L → b ∈ L → c ∈ L → a < b → b < c → R a c) →
      (evenIdx L).IsChain R
  | [], _, _ => by simp [evenIdx]
  | [x], _, _ => by simp [evenIdx]
  | [x, y], _, _ => by simp [evenIdx]
  | x :: y :: z :: xs, hchain, hR => by
      have htail : (z :: xs).IsChain (· < ·) := hchain.tail.tail
      have hR' : ∀ a b c, a ∈ z :: xs → b ∈ z :: xs → c ∈ z :: xs → a < b → b < c → R a c :=
        fun a b c ha hb hc hab hbc =>
          hR a b c (by simp [ha]) (by simp [hb]) (by simp [hc]) hab hbc
      have ih := evenIdx_isChain (z :: xs) htail hR'
      have hxy : x < y := hchain.rel
      have hyz : y < z := hchain.tail.rel
      have hxz : R x z := hR x y z (by simp) (by simp) (by simp) hxy hyz
      rw [evenIdx]
      refine ih.cons ?_
      intro v hv
      rw [evenIdx_head?_cons] at hv
      injection hv with hv
      subst hv
      exact hxz

private lemma oddIdx_isChain {R : ℕ → ℕ → Prop} :
    ∀ L : List ℕ, L.IsChain (· < ·) →
      (∀ a b c, a ∈ L → b ∈ L → c ∈ L → a < b → b < c → R a c) →
      (oddIdx L).IsChain R
  | [], _, _ => by simp [oddIdx]
  | [_], _, _ => by simp [oddIdx]
  | [_, y], _, _ => by simp [oddIdx]
  | [_, y, _], _, _ => by simp [oddIdx]
  | x :: y :: z :: w :: xs, hchain, hR => by
      have htail : (z :: w :: xs).IsChain (· < ·) := hchain.tail.tail
      have hR' : ∀ a b c, a ∈ z :: w :: xs → b ∈ z :: w :: xs → c ∈ z :: w :: xs →
          a < b → b < c → R a c :=
        fun a b c ha hb hc hab hbc =>
          hR a b c (by simp [ha]) (by simp [hb]) (by simp [hc]) hab hbc
      have ih := oddIdx_isChain (z :: w :: xs) htail hR'
      have hyz : y < z := hchain.tail.rel
      have hzw : z < w := hchain.tail.tail.rel
      have hyw : R y w := hR y z w (by simp) (by simp) (by simp) hyz hzw
      simp only [oddIdx] at ih ⊢
      refine ih.cons ?_
      intro v hv
      simp only [List.head?_cons] at hv
      injection hv with hv
      subst hv
      exact hyw

private lemma largeSources_eq_union_one_two_tfl (N p : ℕ) :
    largeSources N p = oneModThreeLargeSources N p ∪ twoModThreeLargeSources N p := by
  ext r
  simp only [oneModThreeLargeSources, twoModThreeLargeSources, Finset.mem_union, Finset.mem_filter]
  by_cases h : r % 3 = 1 <;> tauto

private lemma oneModThreeLargeSources_disjoint_two_tfl (N p : ℕ) :
    Disjoint (oneModThreeLargeSources N p) (twoModThreeLargeSources N p) := by
  apply Finset.disjoint_left.mpr
  intro r h1 h2
  exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2

private lemma prod_sub_one_le_prod : ∀ B : List ℕ, (B.map (fun b => b - 1)).prod ≤ B.prod
  | [] => by simp
  | b :: bs => by
      simp only [List.map_cons, List.prod_cons]
      exact Nat.mul_le_mul (Nat.sub_le b 1) (prod_sub_one_le_prod bs)

private lemma prod_sigma_le_of_chain_bounds (e : ℕ → ℕ) :
    ∀ (B L : List ℕ),
      (∀ b ∈ B, 2 ≤ b) →
      L.length ≤ B.length →
      L.Pairwise (· < ·) →
      (∀ r ∈ L, r.Prime ∧ Odd r ∧ r % 3 = 2) →
      B.IsChain (fun a b => ∀ x, x.Prime → Odd x → x % 3 = 2 → a < x → b ≤ x) →
      (∀ b ∈ B.head?, ∀ r ∈ L, b ≤ r) →
      (B.map (fun b => b - 1)).prod * (L.map (fun r => sigma 1 (r ^ e r))).prod ≤
        B.prod * (L.map (fun r => r ^ e r)).prod
  | [], [], _, _, _, _, _, _ => by simp
  | [], _ :: _, _, hlen, _, _, _, _ => by simp at hlen
  | b :: bs, [], _, _, _, _, _, _ => by
      simp only [List.map_nil, List.prod_nil, mul_one]
      exact prod_sub_one_le_prod (b :: bs)
  | b :: bs, r :: rs, hB2, hlen, hL_pair, hL_prop, hB_chain, hhead => by
      have hb2 : 2 ≤ b := hB2 b (by simp)
      have hbr : b ≤ r := hhead b (by simp) r (by simp)
      have hr_prime : r.Prime := (hL_prop r (by simp)).1
      have hcoef : (b - 1) * r ≤ b * (r - 1) := by
        have hr1 : 1 ≤ r := hr_prime.one_lt.le
        zify [show 1 ≤ b by omega, hr1]
        nlinarith
      have hr_lt : (b - 1) * sigma 1 (r ^ e r) < b * r ^ e r :=
        sigma_prime_pow_ratio_lt_tfl hr_prime (by omega) hcoef
      have hlen' : rs.length ≤ bs.length := by
        simpa using hlen
      have hpair' : rs.Pairwise (· < ·) := (List.pairwise_cons.mp hL_pair).2
      have hprop' : ∀ x ∈ rs, x.Prime ∧ Odd x ∧ x % 3 = 2 := fun x hx =>
        hL_prop x (by simp [hx])
      have hchain' : bs.IsChain (fun a b => ∀ x, x.Prime → Odd x → x % 3 = 2 → a < x → b ≤ x) :=
        hB_chain.tail
      have hhead' : ∀ b' ∈ bs.head?, ∀ x ∈ rs, b' ≤ x := by
        intro b' hb' x hx
        have hr_lt_x : r < x := (List.pairwise_cons.mp hL_pair).1 x hx
        have hb_lt_x : b < x := lt_of_le_of_lt hbr hr_lt_x
        have hstep : ∀ y, y.Prime → Odd y → y % 3 = 2 → b < y → b' ≤ y := by
          cases bs with
          | nil => simp at hb'
          | cons b'' bs' =>
              simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb'
              subst hb'
              exact hB_chain.rel
        have hx_prop := hprop' x hx
        exact hstep x hx_prop.1 hx_prop.2.1 hx_prop.2.2 hb_lt_x
      have ih := prod_sigma_le_of_chain_bounds e bs rs
        (fun x hx => hB2 x (by simp [hx])) hlen' hpair' hprop' hchain' hhead'
      have hmul := Nat.mul_le_mul hr_lt.le ih
      simp only [List.map_cons, List.prod_cons]
      calc
        ((b - 1) * (bs.map (fun x => x - 1)).prod) *
            (sigma 1 (r ^ e r) * (rs.map (fun x => sigma 1 (x ^ e x))).prod)
            = ((b - 1) * sigma 1 (r ^ e r)) *
                ((bs.map (fun x => x - 1)).prod * (rs.map (fun x => sigma 1 (x ^ e x))).prod) := by
              ring
        _ ≤ (b * r ^ e r) * (bs.prod * (rs.map (fun x => x ^ e x)).prod) := hmul
        _ = (b * bs.prod) * (r ^ e r * (rs.map (fun x => x ^ e x)).prod) := by ring

private lemma twoModThree_primes_le_six_bound {Q : Finset ℕ} (e : ℕ → ℕ)
    (hcard : Q.card ≤ 6) (hQ : ∀ r ∈ Q, r.Prime ∧ Odd r ∧ r % 3 = 2) :
    4 * 10 * 16 * 22 * 28 * 40 * (∏ r ∈ Q, sigma 1 (r ^ e r)) ≤
      5 * 11 * 17 * 23 * 29 * 41 * (∏ r ∈ Q, r ^ e r) := by
  let B : List ℕ := [5, 11, 17, 23, 29, 41]
  let L : List ℕ := Q.sort
  have hB2 : ∀ b ∈ B, 2 ≤ b := by
    intro b hb
    simp only [B, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hlen : L.length ≤ B.length := by
    simpa [B, L, Finset.length_sort] using hcard
  have hL_pair : L.Pairwise (· < ·) := (Finset.sortedLT_sort Q).pairwise
  have hL_mem : ∀ r, r ∈ L ↔ r ∈ Q := fun r => Finset.mem_sort (· ≤ ·)
  have hL_prop : ∀ r ∈ L, r.Prime ∧ Odd r ∧ r % 3 = 2 := fun r hr =>
    hQ r ((hL_mem r).mp hr)
  have hB_chain : B.IsChain (fun a b => ∀ x, x.Prime → Odd x → x % 3 = 2 → a < x → b ≤ x) := by
    refine List.isChain_cons_cons.mpr ⟨?_, List.isChain_cons_cons.mpr ⟨?_, List.isChain_cons_cons.mpr
      ⟨?_, List.isChain_cons_cons.mpr ⟨?_, List.isChain_cons_cons.mpr ⟨?_, List.isChain_singleton _⟩⟩⟩⟩⟩
    · intro x _ hx_odd hx3 hx5
      have hx2 : x % 2 = 1 := Nat.odd_iff.mp hx_odd
      omega
    · intro x _ hx_odd hx3 hx11
      have hx2 : x % 2 = 1 := Nat.odd_iff.mp hx_odd
      omega
    · intro x _ hx_odd hx3 hx17
      have hx2 : x % 2 = 1 := Nat.odd_iff.mp hx_odd
      omega
    · intro x _ hx_odd hx3 hx23
      have hx2 : x % 2 = 1 := Nat.odd_iff.mp hx_odd
      omega
    · intro x hx_p hx_odd hx3 hx29
      have hx2 : x % 2 = 1 := Nat.odd_iff.mp hx_odd
      have hne35 : x ≠ 35 := fun h => by
        subst h
        exact absurd hx_p (by decide)
      omega
  have hhead : ∀ b ∈ B.head?, ∀ r ∈ L, b ≤ r := by
    intro b hb r hr
    simp only [B, List.head?_cons, Option.mem_def, Option.some.injEq] at hb
    subst hb
    have hr_prop := hL_prop r hr
    have hr2 : r % 2 = 1 := Nat.odd_iff.mp hr_prop.2.1
    have hr3 : r % 3 = 2 := hr_prop.2.2
    omega
  have hbound := prod_sigma_le_of_chain_bounds e B L hB2 hlen hL_pair hL_prop hB_chain hhead
  have hprod_sort : ∀ f : ℕ → ℕ, (∏ r ∈ Q, f r) = (L.map f).prod := by
    intro f
    rw [← Finset.prod_map_toList Q f]
    exact ((Finset.sort_perm_toList Q (· ≤ ·)).map f).prod_eq.symm
  rw [← hprod_sort (fun r => sigma 1 (r ^ e r)), ← hprod_sort (fun r => r ^ e r)] at hbound
  have hB_lhs : (B.map (fun b => b - 1)).prod = 4 * 10 * 16 * 22 * 28 * 40 := by decide
  have hB_rhs : B.prod = 5 * 11 * 17 * 23 * 29 * 41 := by decide
  rw [hB_lhs, hB_rhs] at hbound
  exact hbound

/-- If a three-free odd perfect number `N` has no `1 [MOD 3]` large prime factors, then it has
at least `7` large prime factors congruent to `2 [MOD 3]` and `29 ≤ cardFactors N`. -/
theorem seven_le_twoModThreeLarge_and_cardFactors_of_oneModThreeLarge_empty {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) (hempty : oneModThreeLargeSources N q = ∅) :
    7 ≤ (twoModThreeLargeSources N q).card ∧ 29 ≤ cardFactors N := by
  obtain ⟨hq12, hq13⟩ := three_free_euler_prime_mod_twelve ho hN hq hq4 he h3
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have h3not : 3 ∉ N.primeFactors := fun h => h3 (Nat.dvd_of_mem_primeFactors h)
  have hsq1_zero : (squareSourcesOne N).card = 0 := by
    have h3zero : N.factorization 3 = 0 := Finsupp.notMem_support_iff.mp h3not
    have := squareSourcesOne_card_le_three_exponent hN
    omega
  let S := squareSources N
  let Q₂₃ := twoModThreeLargeSources N q
  have hL_eq : largeSources N q = Q₂₃ := by
    rw [largeSources_eq_union_one_two_tfl, hempty, Finset.empty_union]
  have hQ_prop : ∀ r ∈ Q₂₃, r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ q ∧
      4 ≤ N.factorization r ∧ r % 3 = 2 := by
    intro r hr
    have hr_large : r ∈ largeSources N q := by rw [hL_eq]; exact hr
    obtain ⟨hr_mem, hr3, hrq, hre⟩ := Finset.mem_filter.mp hr_large
    have hr_ne1 : r % 3 ≠ 1 := (Finset.mem_filter.mp hr).2
    have hrp := Nat.prime_of_mem_primeFactors hr_mem
    have hr_odd := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr_mem)
    have hr_mod3 : r % 3 = 2 := by
      by_contra! hne2
      have h0 : r % 3 = 0 := by omega
      have hd3 : 3 ∣ r := Nat.dvd_of_mod_eq_zero h0
      have heq3 := (Nat.dvd_prime hrp).mp hd3
      have := hrp.two_le
      omega
    exact ⟨hrp, hr_odd, hr3, hrq, hre, hr_mod3⟩
  have hpart : N.primeFactors = insert q (S ∪ Q₂₃) := by
    ext r
    simp only [Finset.mem_insert, Finset.mem_union, S, squareSources, Finset.mem_filter]
    constructor
    · intro hr
      by_cases hrq : r = q
      · exact Or.inl hrq
      · have hr3 : r ≠ 3 := fun h => h3not (h ▸ hr)
        have hpos : 0 < N.factorization r := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
        obtain ⟨k, hk⟩ := hev r hrq
        by_cases htwo : N.factorization r = 2
        · exact Or.inr (Or.inl ⟨hr, hr3, htwo⟩)
        · have hlarge_r : r ∈ largeSources N q :=
            Finset.mem_filter.mpr ⟨hr, hr3, hrq, by omega⟩
          rw [hL_eq] at hlarge_r
          exact Or.inr (Or.inr hlarge_r)
    · rintro (rfl | ⟨hr, _, _⟩ | hrQ)
      · exact hq
      · exact hr
      · exact (Finset.mem_filter.mp ((Finset.mem_filter.mp hrQ).1)).1
  have hq_not_ins : q ∉ S ∪ Q₂₃ := by
    intro h
    rcases Finset.mem_union.mp h with hqS | hqQ
    · have := (Finset.mem_filter.mp hqS).2.2
      omega
    · exact (hQ_prop q hqQ).2.2.2.1 rfl
  have hSQ_disj : Disjoint S Q₂₃ := by
    apply Finset.disjoint_left.mpr
    intro r hrS hrQ
    have h1 := (Finset.mem_filter.mp hrS).2.2
    have h2 := (hQ_prop r hrQ).2.2.2.2.1
    omega
  have h7 : 7 ≤ Q₂₃.card := by
    by_contra! hlt7
    have hQ_le6 : Q₂₃.card ≤ 6 := by omega
    have hS_prop : ∀ u ∈ S,
        u.Prime ∧ Odd u ∧ N.factorization u = 2 ∧ u % 3 = 2 ∧ 29 ≤ u ∧
        sigma 1 (u ^ N.factorization u) = u ^ 2 + u + 1 ∧
        (u ^ 2 + u + 1) = q ^ (u ^ 2 + u + 1).factorization q := by
      intro u hu
      obtain ⟨hu_mem, _, hu_exp2⟩ := Finset.mem_filter.mp hu
      have hup := Nat.prime_of_mem_primeFactors hu_mem
      have hu_odd := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hu_mem)
      have hu_mod3 : u % 3 = 2 := by
        by_contra! hne2
        have h0or1 : u % 3 = 0 ∨ u % 3 = 1 := by omega
        rcases h0or1 with h0 | h1
        · have hd3 : 3 ∣ u := Nat.dvd_of_mod_eq_zero h0
          have heq3 := (Nat.dvd_prime hup).mp hd3
          have := hup.two_le
          omega
        · have hu_sq1 : u ∈ squareSourcesOne N := Finset.mem_filter.mpr ⟨hu, h1⟩
          have hpos : 0 < (squareSourcesOne N).card := Finset.card_pos.mpr ⟨u, hu_sq1⟩
          omega
      have hu5 : 5 ≤ u := by
        have := hup.two_le
        have := Nat.odd_iff.mp hu_odd
        omega
      have hsig : sigma 1 (u ^ N.factorization u) = u ^ 2 + u + 1 := by
        rw [hu_exp2, sigma_one_apply_prime_pow hup]
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_zero]
        ring
      have hsub : (u ^ 2 + u + 1).primeFactors ⊆ {q} := by
        intro w hw
        obtain ⟨hw_prime, hw_dvd, _⟩ := Nat.mem_primeFactors.mp hw
        have hsum_odd : Odd (u ^ 2 + u + 1) :=
          ((hu_odd.pow).add_odd hu_odd).add_odd (by decide : Odd 1)
        have hw_odd : Odd w := hsum_odd.of_dvd_nat hw_dvd
        have hw_ne3 : w ≠ 3 := by
          intro h
          subst h
          have hsum_mod3 : (u ^ 2 + u + 1) % 3 = 1 := by
            rw [Nat.add_mod, Nat.add_mod (u ^ 2), Nat.pow_mod, hu_mod3]
          omega
        have hw_mod3 : w % 3 = 1 :=
          (prime_dvd_sq_add_self_add_one hw_prime hw_dvd).resolve_left hw_ne3
        have hwN : w ∣ N := by
          apply dvd_perfect_of_exact_prime_pow hN hup (Nat.ordProj_dvd N u) _ hw_prime hw_odd
          · rw [← sigma_one_apply, hsig]
            exact hw_dvd
          · rw [hup.pow_dvd_iff_le_factorization hN.2.ne']
            omega
        have hw_mem := Nat.mem_primeFactors.mpr ⟨hw_prime, hwN, hN.2.ne'⟩
        rw [hpart, Finset.mem_insert, Finset.mem_union] at hw_mem
        rcases hw_mem with rfl | hwS | hwQ
        · exact Finset.mem_singleton_self _
        · have hw_sq1 : w ∈ squareSourcesOne N := Finset.mem_filter.mpr ⟨hwS, hw_mod3⟩
          have hpos : 0 < (squareSourcesOne N).card := Finset.card_pos.mpr ⟨w, hw_sq1⟩
          omega
        · exfalso
          have := (hQ_prop w hwQ).2.2.2.2.2
          omega
      have hpow : u ^ 2 + u + 1 = q ^ (u ^ 2 + u + 1).factorization q :=
        eq_pow_of_primeFactors_subset_tfl (by omega) hsub
      have hq_dvd : q ∣ u ^ 2 + u + 1 := by
        have hgt1 : 1 < u ^ 2 + u + 1 := by nlinarith [hu5]
        have hpos_exp : 0 < (u ^ 2 + u + 1).factorization q := by
          by_contra! h0
          have he0 : (u ^ 2 + u + 1).factorization q = 0 := by omega
          rw [he0, pow_zero] at hpow
          omega
        rw [hpow]
        exact dvd_pow_self q (by omega)
      have hu29 : 29 ≤ u :=
        sq_add_self_add_one_ge_29_of_one_mod_twelve_prime_dvd hu_odd hu_mod3 hq_prime hq12 hq_dvd
      exact ⟨hup, hu_odd, hu_exp2, hu_mod3, hu29, hsig, hpow⟩
    let PS := ∏ u ∈ S, (u ^ 2 + u + 1)
    let QS := ∏ u ∈ S, u ^ 2
    let PQ := ∏ r ∈ Q₂₃, sigma 1 (r ^ N.factorization r)
    let QQ := ∏ r ∈ Q₂₃, r ^ N.factorization r
    have hN_eq : q ^ N.factorization q * QS * QQ = N := by
      have hfac := Nat.prod_primeFactors_pow_factorization hN.2.ne'
      rw [hpart, Finset.prod_insert hq_not_ins, Finset.prod_union hSQ_disj] at hfac
      have hS_prod : (∏ u ∈ S, u ^ N.factorization u) = QS :=
        Finset.prod_congr rfl fun u hu => by rw [(hS_prop u hu).2.2.1]
      rw [hS_prod, ← mul_assoc] at hfac
      exact hfac.symm
    have hσ_eq : sigma 1 (q ^ N.factorization q) * PS * PQ = 2 * N := by
      have hσN : sigma 1 N = 2 * N :=
        (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN)
      have hmul : sigma 1 N = ∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p) :=
        isMultiplicative_sigma.multiplicative_factorization (sigma 1) hN.2.ne'
      rw [hσN, hpart, Finset.prod_insert hq_not_ins, Finset.prod_union hSQ_disj] at hmul
      have hS_prod : (∏ u ∈ S, sigma 1 (u ^ N.factorization u)) = PS :=
        Finset.prod_congr rfl fun u hu => (hS_prop u hu).2.2.2.2.2.1
      rw [hS_prod, ← mul_assoc] at hmul
      exact hmul.symm
    have hq_coef : 12 * q ≤ 13 * (q - 1) := by
      have hq1 : 1 ≤ q := le_trans (by decide) hq13
      zify [hq1]
      linarith [hq13]
    have hq_ratio : 12 * sigma 1 (q ^ N.factorization q) < 13 * q ^ N.factorization q :=
      sigma_prime_pow_ratio_lt_tfl hq_prime (by decide) hq_coef
    have hS_ratio : 87 * PS < 91 * QS := by
      rcases S.eq_empty_or_nonempty with hS_emp | hS_ne
      · simp [PS, QS, hS_emp]
      · have hS_ge5 : ∀ u ∈ S, 5 ≤ u := fun u hu => by
          have := (hS_prop u hu).2.2.2.2.1
          omega
        have hS_gap : ∀ u ∈ S, ∀ v ∈ S, u < v → 5 * u ^ 2 < v := by
          intro u hu v hv huv
          exact sq_add_self_add_one_prime_pow_gap hq_prime (by omega : q % 3 = 1)
            (hS_prop u hu).2.1 (hS_prop v hv).2.1
            (hS_prop u hu).2.2.2.1 (hS_prop v hv).2.2.2.1
            huv (hS_prop u hu).2.2.2.2.2.2 (hS_prop v hv).2.2.2.2.2.2
        have hgap_prod := prod_sq_abundancy_lt_of_five_sq_gap S hS_ne hS_ge5 hS_gap
        have hm29 : 29 ≤ S.min' hS_ne := (hS_prop _ (S.min'_mem hS_ne)).2.2.2.2.1
        have hcoef_S : 87 * (3 * S.min' hS_ne + 4) ≤ 91 * (3 * S.min' hS_ne) := by omega
        exact sq_prod_ratio_lt_tfl (by decide) hgap_prod hcoef_S
    have hQ_ratio : 4 * 10 * 16 * 22 * 28 * 40 * PQ ≤ 5 * 11 * 17 * 23 * 29 * 41 * QQ :=
      twoModThree_primes_le_six_bound (N.factorization) hQ_le6 fun r hr =>
        ⟨(hQ_prop r hr).1, (hQ_prop r hr).2.1, (hQ_prop r hr).2.2.2.2.2⟩
    have hPQ_pos : 0 < (4 * 10 * 16 * 22 * 28 * 40) * PQ := by
      refine Nat.mul_pos (by decide) (Finset.prod_pos fun r hr => ?_)
      have hrp := (hQ_prop r hr).1
      have hre := (hQ_prop r hr).2.2.2.2.1
      have hgt1 : 1 < r ^ N.factorization r := one_lt_pow₀ hrp.one_lt (by omega)
      exact lt_trans (by decide) (hgt1.trans (self_lt_sigma_of_one_lt hgt1))
    exact abundancy_contradiction3_le (cq := 12) (dq := 13) (cs := 87) (ds := 91)
      (cQ := 4 * 10 * 16 * 22 * 28 * 40) (dQ := 5 * 11 * 17 * 23 * 29 * 41)
      hN.2 hσ_eq hN_eq hq_ratio hS_ratio hPQ_pos hQ_ratio (by norm_num)
  have hcf29 : 29 ≤ cardFactors N := by
    have hsub_ins : insert q Q₂₃ ⊆ N.primeFactors := by
      rw [hpart]
      intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hrQ
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right S hrQ)
    have hq_not_Q : q ∉ Q₂₃ := fun hqQ => (hQ_prop q hqQ).2.2.2.1 rfl
    have hq_pos : 1 ≤ N.factorization q := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hq)
    have hQ_sum : 4 * Q₂₃.card ≤ ∑ r ∈ Q₂₃, N.factorization r := by
      calc
        4 * Q₂₃.card = ∑ _r ∈ Q₂₃, 4 := by simp [Finset.sum_const, mul_comm]
        _ ≤ ∑ r ∈ Q₂₃, N.factorization r :=
          Finset.sum_le_sum fun r hr => (hQ_prop r hr).2.2.2.2.1
    have hcf_eq : cardFactors N = ∑ r ∈ N.primeFactors, N.factorization r := by
      rw [cardFactors_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
    have hsum_sub : ∑ r ∈ insert q Q₂₃, N.factorization r ≤
        ∑ r ∈ N.primeFactors, N.factorization r :=
      Finset.sum_le_sum_of_subset hsub_ins
    rw [Finset.sum_insert hq_not_Q] at hsum_sub
    omega
  exact ⟨h7, hcf29⟩

/-- On any three-free odd perfect number (`¬ 3 ∣ N`), either `oneModThreeLargeSources N q` is
nonempty or `7 ≤ (largeSources N q).card`. -/
theorem oneModThreeLarge_nonempty_or_seven_le_largeSources_of_three_free {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) (h3 : ¬ 3 ∣ N) :
    (oneModThreeLargeSources N q).Nonempty ∨ 7 ≤ (largeSources N q).card := by
  by_cases hne : (oneModThreeLargeSources N q).Nonempty
  · exact Or.inl hne
  · right
    have hempty : oneModThreeLargeSources N q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have h7 := (seven_le_twoModThreeLarge_and_cardFactors_of_oneModThreeLarge_empty
      ho hN hq hq4 he hev h3 hempty).1
    rw [largeSources_eq_union_one_two_tfl, hempty, Finset.empty_union]
    exact h7

/-- On any three-free odd perfect number (`¬ 3 ∣ N`), either at least two large non-Euler
primes are `1 [MOD 3]` or at least three large non-Euler primes exist. -/
theorem two_le_oneModThreeLarge_or_three_le_largeSources_of_three_free {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) (h3 : ¬ 3 ∣ N) :
    2 ≤ (oneModThreeLargeSources N q).card ∨ 3 ≤ (largeSources N q).card := by
  by_contra! hlt
  obtain ⟨hlt1, hlt3⟩ := hlt
  have h2 := two_le_largeSources_of_three_free ho hN hq hq4 he hev h3
  have hcard2 : (largeSources N q).card = 2 := by omega
  have hor := oneModThreeLarge_nonempty_or_seven_le_largeSources_of_three_free
    ho hN hq hq4 he hev h3
  have h1_nonempty : (oneModThreeLargeSources N q).Nonempty := by
    rcases hor with hne | h7
    · exact hne
    · omega
  have h1_card_pos : 0 < (oneModThreeLargeSources N q).card := Finset.card_pos.mpr h1_nonempty
  have h1_card : (oneModThreeLargeSources N q).card = 1 := by omega
  have hsum_card : (oneModThreeLargeSources N q).card + (twoModThreeLargeSources N q).card =
      (largeSources N q).card := by
    rw [← Finset.card_union_of_disjoint (oneModThreeLargeSources_disjoint_two_tfl N q),
      ← largeSources_eq_union_one_two_tfl]
  have h2_card : (twoModThreeLargeSources N q).card = 1 := by omega
  obtain ⟨r₁, hr₁⟩ := Finset.card_eq_one.mp h1_card
  obtain ⟨r₂, hr₂⟩ := Finset.card_eq_one.mp h2_card
  have hr₁_mem1 : r₁ ∈ oneModThreeLargeSources N q := by rw [hr₁]; exact Finset.mem_singleton_self r₁
  have hr₂_mem2 : r₂ ∈ twoModThreeLargeSources N q := by rw [hr₂]; exact Finset.mem_singleton_self r₂
  have hr₁_large : r₁ ∈ largeSources N q := (Finset.mem_filter.mp hr₁_mem1).1
  have hr₂_large : r₂ ∈ largeSources N q := (Finset.mem_filter.mp hr₂_mem2).1
  obtain ⟨hr₁_mem, hr₁3_ne, hr₁q, hr₁_exp⟩ := Finset.mem_filter.mp hr₁_large
  obtain ⟨hr₂_mem, hr₂3_ne, hr₂q, hr₂_exp⟩ := Finset.mem_filter.mp hr₂_large
  have hr₁_mod3 : r₁ % 3 = 1 := (Finset.mem_filter.mp hr₁_mem1).2
  have hr₂_ne1 : r₂ % 3 ≠ 1 := (Finset.mem_filter.mp hr₂_mem2).2
  obtain ⟨hq12, hq13⟩ := three_free_euler_prime_mod_twelve ho hN hq hq4 he h3
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hq_odd : Odd q := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)
  have hr₁_prime : r₁.Prime := Nat.prime_of_mem_primeFactors hr₁_mem
  have hr₁_odd : Odd r₁ := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr₁_mem)
  have hr₁7 : 7 ≤ r₁ := by
    have := hr₁_prime.two_le
    have := Nat.odd_iff.mp hr₁_odd
    omega
  have hr₂_prime : r₂.Prime := Nat.prime_of_mem_primeFactors hr₂_mem
  have hr₂_odd : Odd r₂ := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr₂_mem)
  have hr₂_mod3 : r₂ % 3 = 2 := by
    by_contra! hne2
    have h0 : r₂ % 3 = 0 := by omega
    have hd3 : 3 ∣ r₂ := Nat.dvd_of_mod_eq_zero h0
    have heq3 := (Nat.dvd_prime hr₂_prime).mp hd3
    have := hr₂_prime.two_le
    omega
  have hr₂5 : 5 ≤ r₂ := by
    have := hr₂_prime.two_le
    have := Nat.odd_iff.mp hr₂_odd
    omega
  have hr₁₂ : r₁ ≠ r₂ := by omega
  have h3not : 3 ∉ N.primeFactors := fun h => h3 (Nat.dvd_of_mem_primeFactors h)
  have hsq1_zero : (squareSourcesOne N).card = 0 := by
    have h3zero : N.factorization 3 = 0 := Finsupp.notMem_support_iff.mp h3not
    have := squareSourcesOne_card_le_three_exponent hN
    omega
  let S := squareSources N
  have hL_pair_set : largeSources N q = {r₁, r₂} := by
    rw [largeSources_eq_union_one_two_tfl, hr₁, hr₂]
    ext x
    simp [Finset.mem_singleton, Finset.mem_insert]
  have hpart : N.primeFactors = insert q (insert r₁ (insert r₂ S)) := by
    ext r
    simp only [Finset.mem_insert, S, squareSources, Finset.mem_filter]
    constructor
    · intro hr
      by_cases hrq : r = q
      · exact Or.inl hrq
      · have hr3 : r ≠ 3 := fun h => h3not (h ▸ hr)
        have hpos : 0 < N.factorization r := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
        obtain ⟨k, hk⟩ := hev r hrq
        by_cases htwo : N.factorization r = 2
        · exact Or.inr (Or.inr (Or.inr ⟨hr, hr3, htwo⟩))
        · have hlarge_r : r ∈ largeSources N q :=
            Finset.mem_filter.mpr ⟨hr, hr3, hrq, by omega⟩
          rw [hL_pair_set, Finset.mem_insert, Finset.mem_singleton] at hlarge_r
          rcases hlarge_r with rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
    · rintro (rfl | rfl | rfl | ⟨hr, _, _⟩)
      · exact hq
      · exact hr₁_mem
      · exact hr₂_mem
      · exact hr
  have hr₂_not_S : r₂ ∉ S := by
    intro h
    have := (Finset.mem_filter.mp h).2.2
    omega
  have hr₁_not_ins : r₁ ∉ insert r₂ S := by
    intro h
    rcases Finset.mem_insert.mp h with h12 | h1S
    · exact hr₁₂ h12
    · have := (Finset.mem_filter.mp h1S).2.2
      omega
  have hq_not_ins : q ∉ insert r₁ (insert r₂ S) := by
    intro h
    rcases Finset.mem_insert.mp h with hqr1 | hq'
    · exact hr₁q hqr1.symm
    · rcases Finset.mem_insert.mp hq' with hqr2 | hqS
      · exact hr₂q hqr2.symm
      · have := (Finset.mem_filter.mp hqS).2.2
        omega
  have hS_prop : ∀ u ∈ S,
      u.Prime ∧ Odd u ∧ N.factorization u = 2 ∧ u % 3 = 2 ∧ 5 ≤ u ∧
      sigma 1 (u ^ N.factorization u) = u ^ 2 + u + 1 ∧
      (u ^ 2 + u + 1).primeFactors ⊆ {q, r₁} := by
    intro u hu
    obtain ⟨hu_mem, _, hu_exp2⟩ := Finset.mem_filter.mp hu
    have hup := Nat.prime_of_mem_primeFactors hu_mem
    have hu_odd := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hu_mem)
    have hu_mod3 : u % 3 = 2 := by
      by_contra! hne2
      have h0or1 : u % 3 = 0 ∨ u % 3 = 1 := by omega
      rcases h0or1 with h0 | h1
      · have hd3 : 3 ∣ u := Nat.dvd_of_mod_eq_zero h0
        have heq3 := (Nat.dvd_prime hup).mp hd3
        have := hup.two_le
        omega
      · have hu_sq1 : u ∈ squareSourcesOne N := Finset.mem_filter.mpr ⟨hu, h1⟩
        have hpos : 0 < (squareSourcesOne N).card := Finset.card_pos.mpr ⟨u, hu_sq1⟩
        omega
    have hu5 : 5 ≤ u := by
      have := hup.two_le
      have := Nat.odd_iff.mp hu_odd
      omega
    have hsig : sigma 1 (u ^ N.factorization u) = u ^ 2 + u + 1 := by
      rw [hu_exp2, sigma_one_apply_prime_pow hup]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero]
      ring
    have hsub : (u ^ 2 + u + 1).primeFactors ⊆ {q, r₁} := by
      intro w hw
      obtain ⟨hw_prime, hw_dvd, _⟩ := Nat.mem_primeFactors.mp hw
      have hsum_odd : Odd (u ^ 2 + u + 1) :=
        ((hu_odd.pow).add_odd hu_odd).add_odd (by decide : Odd 1)
      have hw_odd : Odd w := hsum_odd.of_dvd_nat hw_dvd
      have hw_ne3 : w ≠ 3 := by
        intro h
        subst h
        have hsum_mod3 : (u ^ 2 + u + 1) % 3 = 1 := by
          rw [Nat.add_mod, Nat.add_mod (u ^ 2), Nat.pow_mod, hu_mod3]
        omega
      have hw_mod3 : w % 3 = 1 :=
        (prime_dvd_sq_add_self_add_one hw_prime hw_dvd).resolve_left hw_ne3
      have hwN : w ∣ N := by
        apply dvd_perfect_of_exact_prime_pow hN hup (Nat.ordProj_dvd N u) _ hw_prime hw_odd
        · rw [← sigma_one_apply, hsig]
          exact hw_dvd
        · rw [hup.pow_dvd_iff_le_factorization hN.2.ne']
          omega
      have hw_mem := Nat.mem_primeFactors.mpr ⟨hw_prime, hwN, hN.2.ne'⟩
      rw [hpart, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert] at hw_mem
      rcases hw_mem with rfl | rfl | rfl | hwS
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · omega
      · have hw_sq1 : w ∈ squareSourcesOne N := Finset.mem_filter.mpr ⟨hwS, hw_mod3⟩
        have hpos : 0 < (squareSourcesOne N).card := Finset.card_pos.mpr ⟨w, hw_sq1⟩
        omega
    exact ⟨hup, hu_odd, hu_exp2, hu_mod3, hu5, hsig, hsub⟩
  have hS_not_11 : 11 ∉ S := by
    intro h11
    have hsub := (hS_prop 11 h11).2.2.2.2.2.2
    have h7_mem : 7 ∈ (11 ^ 2 + 11 + 1).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨by norm_num, by norm_num, by norm_num⟩
    have h19_mem : 19 ∈ (11 ^ 2 + 11 + 1).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨by norm_num, by norm_num, by norm_num⟩
    have h7 := Finset.mem_insert.mp (hsub h7_mem)
    have h19 := Finset.mem_insert.mp (hsub h19_mem)
    rcases h7 with h7q | h7r <;> rcases h19 with h19q | h19r
    · omega
    · omega
    · omega
    · rw [Finset.mem_singleton] at h7r h19r
      omega
  have hS_not_23 : 23 ∉ S := by
    intro h23
    have hsub := (hS_prop 23 h23).2.2.2.2.2.2
    have h7_mem : 7 ∈ (23 ^ 2 + 23 + 1).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨by norm_num, by norm_num, by norm_num⟩
    have h79_mem : 79 ∈ (23 ^ 2 + 23 + 1).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨by norm_num, by norm_num, by norm_num⟩
    have h7 := Finset.mem_insert.mp (hsub h7_mem)
    have h79 := Finset.mem_insert.mp (hsub h79_mem)
    rcases h7 with h7q | h7r <;> rcases h79 with h79q | h79r
    · omega
    · omega
    · omega
    · rw [Finset.mem_singleton] at h7r h79r
      omega
  have h5_r1 : 5 ∈ S → r₁ = 31 := by
    intro h5
    have hsub := (hS_prop 5 h5).2.2.2.2.2.2
    have h31_mem : 31 ∈ (5 ^ 2 + 5 + 1).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨by norm_num, by norm_num, by norm_num⟩
    rcases Finset.mem_insert.mp (hsub h31_mem) with hq31 | hr31
    · omega
    · exact (Finset.mem_singleton.mp hr31).symm
  have h17_r1 : 17 ∈ S → r₁ = 307 := by
    intro h17
    have hsub := (hS_prop 17 h17).2.2.2.2.2.2
    have h307_mem : 307 ∈ (17 ^ 2 + 17 + 1).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨by norm_num, by norm_num, by norm_num⟩
    rcases Finset.mem_insert.mp (hsub h307_mem) with hq307 | hr307
    · omega
    · exact (Finset.mem_singleton.mp hr307).symm
  have h5_17_excl : ¬ (5 ∈ S ∧ 17 ∈ S) := by
    rintro ⟨h5, h17⟩
    have := h5_r1 h5
    have := h17_r1 h17
    omega
  have hS_cases : ∀ u ∈ S, u = 5 ∨ u = 17 ∨ 29 ≤ u := by
    intro u hu
    obtain ⟨_, hu_odd, _, hu3, hu5, _, _⟩ := hS_prop u hu
    have hu2 : u % 2 = 1 := Nat.odd_iff.mp hu_odd
    have hne11 : u ≠ 11 := fun h => hS_not_11 (h ▸ hu)
    have hne23 : u ≠ 23 := fun h => hS_not_23 (h ▸ hu)
    omega
  have hS_pow : ∀ u ∈ S,
      u ^ 2 + u + 1 =
        q ^ (u ^ 2 + u + 1).factorization q * r₁ ^ (u ^ 2 + u + 1).factorization r₁ := by
    intro u hu
    exact eq_mul_pow_of_primeFactors_subset_pair_tfl (by omega) hr₁q.symm
      (hS_prop u hu).2.2.2.2.2.2
  have hq_coef : 12 * q ≤ 13 * (q - 1) := by
    have hq1 : 1 ≤ q := le_trans (by decide) hq13
    zify [hq1]
    linarith [hq13]
  have hq_ratio : 12 * sigma 1 (q ^ N.factorization q) < 13 * q ^ N.factorization q :=
    sigma_prime_pow_ratio_lt_tfl hq_prime (by decide) hq_coef
  have hN_fac := Nat.prod_primeFactors_pow_factorization hN.2.ne'
  rw [hpart, Finset.prod_insert hq_not_ins, Finset.prod_insert hr₁_not_ins,
    Finset.prod_insert hr₂_not_S] at hN_fac
  have hσN_eq : sigma 1 N = 2 * N :=
    (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN)
  have hσ_mul : sigma 1 N = ∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p) :=
    isMultiplicative_sigma.multiplicative_factorization (sigma 1) hN.2.ne'
  rw [hσN_eq, hpart, Finset.prod_insert hq_not_ins, Finset.prod_insert hr₁_not_ins,
    Finset.prod_insert hr₂_not_S] at hσ_mul
  by_cases h5 : 5 ∈ S
  · have hr1_eq : r₁ = 31 := h5_r1 h5
    have hnot17 : 17 ∉ S := fun h17 => h5_17_excl ⟨h5, h17⟩
    have hr2_ne5 : r₂ ≠ 5 := by
      intro h
      subst h
      have := (hS_prop 5 h5).2.2.1
      omega
    have hr2_11 : 11 ≤ r₂ := by
      have := Nat.odd_iff.mp hr₂_odd
      omega
    have hr1_coef : 30 * r₁ ≤ 31 * (r₁ - 1) := by omega
    have hr1_ratio : 30 * sigma 1 (r₁ ^ N.factorization r₁) < 31 * r₁ ^ N.factorization r₁ :=
      sigma_prime_pow_ratio_lt_tfl hr₁_prime (by decide) hr1_coef
    have hr2_coef : 10 * r₂ ≤ 11 * (r₂ - 1) := by
      have hr2_1 : 1 ≤ r₂ := le_trans (by decide) hr2_11
      zify [hr2_1]
      linarith [hr2_11]
    have hr2_ratio : 10 * sigma 1 (r₂ ^ N.factorization r₂) < 11 * r₂ ^ N.factorization r₂ :=
      sigma_prime_pow_ratio_lt_tfl hr₂_prime (by decide) hr2_coef
    let S' := S.erase 5
    let L' := S'.sort
    have hL'_chain_lt : L'.IsChain (· < ·) := (Finset.sortedLT_sort S').isChain
    have hL'_pair_lt : L'.Pairwise (· < ·) := (Finset.sortedLT_sort S').pairwise
    have hL'_mem : ∀ x, x ∈ L' ↔ x ∈ S' := fun x => Finset.mem_sort (· ≤ ·)
    have hprod_sort' : ∀ f : ℕ → ℕ, (∏ u ∈ S', f u) = (L'.map f).prod := by
      intro f
      rw [← Finset.prod_map_toList S' f]
      exact ((Finset.sort_perm_toList S' (· ≤ ·)).map f).prod_eq.symm
    let P_ev_num := ((evenIdx L').map (fun u => u ^ 2 + u + 1)).prod
    let P_ev_den := ((evenIdx L').map (fun u => u ^ 2)).prod
    let P_od_num := ((oddIdx L').map (fun u => u ^ 2 + u + 1)).prod
    let P_od_den := ((oddIdx L').map (fun u => u ^ 2)).prod
    have hS'_mem : ∀ x ∈ S', x ∈ S ∧ x ≠ 5 ∧ x ≠ 17 ∧ 29 ≤ x := by
      intro x hx
      have hxS := Finset.mem_of_mem_erase hx
      have hx5 := Finset.ne_of_mem_erase hx
      have hx17 : x ≠ 17 := fun h => hnot17 (h ▸ hxS)
      rcases hS_cases x hxS with rfl | rfl | h29
      · exact (hx5 rfl).elim
      · exact (hx17 rfl).elim
      · exact ⟨hxS, hx5, hx17, h29⟩
    have hN_eq : q ^ N.factorization q * r₁ ^ N.factorization r₁ *
        (25 * r₂ ^ N.factorization r₂) * P_ev_den * P_od_den = N := by
      have hS_prod : (∏ u ∈ S, u ^ N.factorization u) = 25 * (P_ev_den * P_od_den) := by
        rw [← Finset.insert_erase h5, Finset.prod_insert (Finset.notMem_erase 5 S)]
        have h5_fac : 5 ^ N.factorization 5 = 25 := by
          rw [(hS_prop 5 h5).2.2.1]
          norm_num
        have hS'_prod : (∏ u ∈ S', u ^ N.factorization u) = P_ev_den * P_od_den := by
          have h1 : (∏ u ∈ S', u ^ N.factorization u) = ∏ u ∈ S', u ^ 2 :=
            Finset.prod_congr rfl fun u hu => by rw [(hS_prop u (hS'_mem u hu).1).2.2.1]
          rw [h1, hprod_sort']
          exact prod_map_evenIdx_mul_oddIdx (fun u => u ^ 2) L'
        rw [h5_fac, hS'_prod]
      rw [hS_prod] at hN_fac
      calc
        q ^ N.factorization q * r₁ ^ N.factorization r₁ *
            (25 * r₂ ^ N.factorization r₂) * P_ev_den * P_od_den
            = q ^ N.factorization q * (r₁ ^ N.factorization r₁ *
                (r₂ ^ N.factorization r₂ * (25 * (P_ev_den * P_od_den)))) := by ring
        _ = N := hN_fac.symm
    have hσ_eq : sigma 1 (q ^ N.factorization q) * sigma 1 (r₁ ^ N.factorization r₁) *
        (31 * sigma 1 (r₂ ^ N.factorization r₂)) * P_ev_num * P_od_num = 2 * N := by
      have hS_prod : (∏ u ∈ S, sigma 1 (u ^ N.factorization u)) = 31 * (P_ev_num * P_od_num) := by
        rw [← Finset.insert_erase h5, Finset.prod_insert (Finset.notMem_erase 5 S)]
        have h5_sig : sigma 1 (5 ^ N.factorization 5) = 31 := by
          rw [(hS_prop 5 h5).2.2.2.2.2.1]
          norm_num
        have hS'_prod : (∏ u ∈ S', sigma 1 (u ^ N.factorization u)) = P_ev_num * P_od_num := by
          have h1 : (∏ u ∈ S', sigma 1 (u ^ N.factorization u)) = ∏ u ∈ S', (u ^ 2 + u + 1) :=
            Finset.prod_congr rfl fun u hu => (hS_prop u (hS'_mem u hu).1).2.2.2.2.2.1
          rw [h1, hprod_sort']
          exact prod_map_evenIdx_mul_oddIdx (fun u => u ^ 2 + u + 1) L'
        rw [h5_sig, hS'_prod]
      rw [hS_prod] at hσ_mul
      calc
        sigma 1 (q ^ N.factorization q) * sigma 1 (r₁ ^ N.factorization r₁) *
            (31 * sigma 1 (r₂ ^ N.factorization r₂)) * P_ev_num * P_od_num
            = sigma 1 (q ^ N.factorization q) * (sigma 1 (r₁ ^ N.factorization r₁) *
                (sigma 1 (r₂ ^ N.factorization r₂) * (31 * (P_ev_num * P_od_num)))) := by ring
        _ = 2 * N := hσ_mul.symm
    have hstep_triple : ∀ a b c, a ∈ L' → b ∈ L' → c ∈ L' → a < b → b < c → 5 * a + 3 ≤ 2 * c := by
      intro a b c ha hb hc hab hbc
      rw [hL'_mem] at ha hb hc
      have haS := (hS'_mem a ha).1
      have hbS := (hS'_mem b hb).1
      have hcS := (hS'_mem c hc).1
      obtain ⟨_, ha_odd, _, ha3, ha5, _, _⟩ := hS_prop a haS
      obtain ⟨_, hb_odd, _, hb3, _, _, _⟩ := hS_prop b hbS
      obtain ⟨_, hc_odd, _, hc3, _, _, _⟩ := hS_prop c hcS
      exact (two_prime_smooth_sq_add_self_add_one_step
        hq_prime hq_odd (by omega : q % 3 = 1) hr₁_prime hr₁_odd hr₁_mod3
        hab hbc ha_odd hb_odd hc_odd ha5 ha3 hb3 hc3
        (hS_pow a haS) (hS_pow b hbS) (hS_pow c hcS)).2
    have hev_chain : (evenIdx L').IsChain (fun x y => 5 * x + 3 ≤ 2 * y) :=
      evenIdx_isChain L' hL'_chain_lt hstep_triple
    have hod_chain : (oddIdx L').IsChain (fun x y => 5 * x + 3 ≤ 2 * y) :=
      oddIdx_isChain L' hL'_chain_lt hstep_triple
    have hev_ge5 : ∀ x ∈ evenIdx L', 5 ≤ x := fun x hx =>
      (hS_prop x (hS'_mem x ((hL'_mem x).mp (mem_evenIdx_subset hx))).1).2.2.2.2.1
    have hod_ge5 : ∀ x ∈ oddIdx L', 5 ≤ x := fun x hx =>
      (hS_prop x (hS'_mem x ((hL'_mem x).mp (mem_oddIdx_subset hx))).1).2.2.2.2.1
    have hP_ev_pos : 0 < P_ev_num := List.prod_pos (by
      intro y hy
      rcases List.mem_map.mp hy with ⟨u, _, rfl⟩
      positivity)
    have hP_od_pos : 0 < P_od_num := List.prod_pos (by
      intro y hy
      rcases List.mem_map.mp hy with ⟨u, _, rfl⟩
      positivity)
    have hev_head : ∀ x ∈ (evenIdx L').head?, 29 ≤ x := fun x hx =>
      (hS'_mem x ((hL'_mem x).mp (mem_evenIdx_subset (List.mem_of_head? hx)))).2.2.2
    have hP_ev_bd : 58 * P_ev_num ≤ 63 * P_ev_den := by
      simpa using prod_sq_abundancy_le_of_five_halves_step
        (evenIdx L') hev_chain hev_ge5 29 (by decide) hev_head
    have hod_head : ∀ y ∈ (oddIdx L').head?, 41 ≤ y := by
      intro y hy
      cases hL_eq : L' with
      | nil => simp [hL_eq, oddIdx] at hy
      | cons h t =>
          have hy_od : y ∈ oddIdx (h :: t) := by
            rw [← hL_eq]
            exact List.mem_of_head? hy
          have hy_t : y ∈ t := oddIdx_mem_tail hy_od
          have hpair' : (h :: t).Pairwise (· < ·) := hL_eq ▸ hL'_pair_lt
          have hh_lt : h < y := (List.pairwise_cons.mp hpair').1 y hy_t
          have hh_S' : h ∈ S' := (hL'_mem h).mp (hL_eq ▸ List.mem_cons_self)
          have hy_S' : y ∈ S' := (hL'_mem y).mp (hL_eq ▸ List.mem_cons_of_mem _ hy_t)
          have hh29 : 29 ≤ h := (hS'_mem h hh_S').2.2.2
          have hy_prop := hS_prop y (hS'_mem y hy_S').1
          have hy2 : y % 2 = 1 := Nat.odd_iff.mp hy_prop.2.1
          have hy3 : y % 3 = 2 := hy_prop.2.2.2.1
          have hne35 : y ≠ 35 := fun heq => by
            subst heq
            exact absurd hy_prop.1 (by decide)
          omega
    have hP_od_bd : 82 * P_od_num ≤ 87 * P_od_den := by
      simpa using prod_sq_abundancy_le_of_five_halves_step
        (oddIdx L') hod_chain hod_ge5 41 (by decide) hod_head
    have h25_ratio : (10 * 25) * (31 * sigma 1 (r₂ ^ N.factorization r₂)) <
        (11 * 31) * (25 * r₂ ^ N.factorization r₂) := by
      calc
        (10 * 25) * (31 * sigma 1 (r₂ ^ N.factorization r₂))
            = (25 * 31) * (10 * sigma 1 (r₂ ^ N.factorization r₂)) := by ring
        _ < (25 * 31) * (11 * r₂ ^ N.factorization r₂) :=
            Nat.mul_lt_mul_of_pos_left hr2_ratio (by decide)
        _ = (11 * 31) * (25 * r₂ ^ N.factorization r₂) := by ring
    exact abundancy_contradiction5_le (cq := 12) (dq := 13) (cr1 := 30) (dr1 := 31)
      (cr2 := 10 * 25) (dr2 := 11 * 31) (cev := 58) (dev := 63) (cod := 82) (dod := 87)
      hN.2 hσ_eq hN_eq hq_ratio hr1_ratio h25_ratio
      (Nat.mul_pos (by decide) hP_ev_pos) hP_ev_bd
      (Nat.mul_pos (by decide) hP_od_pos) hP_od_bd
      (by norm_num)
  · let L := S.sort
    have hL_chain_lt : L.IsChain (· < ·) := (Finset.sortedLT_sort S).isChain
    have hL_pair_lt : L.Pairwise (· < ·) := (Finset.sortedLT_sort S).pairwise
    have hL_mem : ∀ x, x ∈ L ↔ x ∈ S := fun x => Finset.mem_sort (· ≤ ·)
    have hprod_sort : ∀ f : ℕ → ℕ, (∏ u ∈ S, f u) = (L.map f).prod := by
      intro f
      rw [← Finset.prod_map_toList S f]
      exact ((Finset.sort_perm_toList S (· ≤ ·)).map f).prod_eq.symm
    let P_ev_num := ((evenIdx L).map (fun u => u ^ 2 + u + 1)).prod
    let P_ev_den := ((evenIdx L).map (fun u => u ^ 2)).prod
    let P_od_num := ((oddIdx L).map (fun u => u ^ 2 + u + 1)).prod
    let P_od_den := ((oddIdx L).map (fun u => u ^ 2)).prod
    have hN_eq : q ^ N.factorization q * r₁ ^ N.factorization r₁ * r₂ ^ N.factorization r₂ *
        P_ev_den * P_od_den = N := by
      have hS_prod : (∏ u ∈ S, u ^ N.factorization u) = P_ev_den * P_od_den := by
        have h1 : (∏ u ∈ S, u ^ N.factorization u) = ∏ u ∈ S, u ^ 2 :=
          Finset.prod_congr rfl fun u hu => by rw [(hS_prop u hu).2.2.1]
        rw [h1, hprod_sort]
        exact prod_map_evenIdx_mul_oddIdx (fun u => u ^ 2) L
      rw [hS_prod] at hN_fac
      calc
        q ^ N.factorization q * r₁ ^ N.factorization r₁ * r₂ ^ N.factorization r₂ *
            P_ev_den * P_od_den
            = q ^ N.factorization q * (r₁ ^ N.factorization r₁ *
                (r₂ ^ N.factorization r₂ * (P_ev_den * P_od_den))) := by ring
        _ = N := hN_fac.symm
    have hσ_eq : sigma 1 (q ^ N.factorization q) * sigma 1 (r₁ ^ N.factorization r₁) *
        sigma 1 (r₂ ^ N.factorization r₂) * P_ev_num * P_od_num = 2 * N := by
      have hS_prod : (∏ u ∈ S, sigma 1 (u ^ N.factorization u)) = P_ev_num * P_od_num := by
        have h1 : (∏ u ∈ S, sigma 1 (u ^ N.factorization u)) = ∏ u ∈ S, (u ^ 2 + u + 1) :=
          Finset.prod_congr rfl fun u hu => (hS_prop u hu).2.2.2.2.2.1
        rw [h1, hprod_sort]
        exact prod_map_evenIdx_mul_oddIdx (fun u => u ^ 2 + u + 1) L
      rw [hS_prod] at hσ_mul
      calc
        sigma 1 (q ^ N.factorization q) * sigma 1 (r₁ ^ N.factorization r₁) *
            sigma 1 (r₂ ^ N.factorization r₂) * P_ev_num * P_od_num
            = sigma 1 (q ^ N.factorization q) * (sigma 1 (r₁ ^ N.factorization r₁) *
                (sigma 1 (r₂ ^ N.factorization r₂) * (P_ev_num * P_od_num))) := by ring
        _ = 2 * N := hσ_mul.symm
    have hstep_triple : ∀ a b c, a ∈ L → b ∈ L → c ∈ L → a < b → b < c → 5 * a + 3 ≤ 2 * c := by
      intro a b c ha hb hc hab hbc
      rw [hL_mem] at ha hb hc
      obtain ⟨_, ha_odd, _, ha3, ha5, _, _⟩ := hS_prop a ha
      obtain ⟨_, hb_odd, _, hb3, _, _, _⟩ := hS_prop b hb
      obtain ⟨_, hc_odd, _, hc3, _, _, _⟩ := hS_prop c hc
      exact (two_prime_smooth_sq_add_self_add_one_step
        hq_prime hq_odd (by omega : q % 3 = 1) hr₁_prime hr₁_odd hr₁_mod3
        hab hbc ha_odd hb_odd hc_odd ha5 ha3 hb3 hc3
        (hS_pow a ha) (hS_pow b hb) (hS_pow c hc)).2
    have hev_chain : (evenIdx L).IsChain (fun x y => 5 * x + 3 ≤ 2 * y) :=
      evenIdx_isChain L hL_chain_lt hstep_triple
    have hod_chain : (oddIdx L).IsChain (fun x y => 5 * x + 3 ≤ 2 * y) :=
      oddIdx_isChain L hL_chain_lt hstep_triple
    have hev_ge5 : ∀ x ∈ evenIdx L, 5 ≤ x := fun x hx =>
      (hS_prop x ((hL_mem x).mp (mem_evenIdx_subset hx))).2.2.2.2.1
    have hod_ge5 : ∀ x ∈ oddIdx L, 5 ≤ x := fun x hx =>
      (hS_prop x ((hL_mem x).mp (mem_oddIdx_subset hx))).2.2.2.2.1
    have hP_ev_pos : 0 < P_ev_num := List.prod_pos (by
      intro y hy
      rcases List.mem_map.mp hy with ⟨u, _, rfl⟩
      positivity)
    have hP_od_pos : 0 < P_od_num := List.prod_pos (by
      intro y hy
      rcases List.mem_map.mp hy with ⟨u, _, rfl⟩
      positivity)
    have hr2_coef : 4 * r₂ ≤ 5 * (r₂ - 1) := by
      have hr2_1 : 1 ≤ r₂ := le_trans (by decide) hr₂5
      zify [hr2_1]
      linarith [hr₂5]
    have hr2_ratio : 4 * sigma 1 (r₂ ^ N.factorization r₂) < 5 * r₂ ^ N.factorization r₂ :=
      sigma_prime_pow_ratio_lt_tfl hr₂_prime (by decide) hr2_coef
    have hod_head_gt : ∀ y ∈ (oddIdx L).head?, ∃ h ∈ S, h < y ∧ y ∈ S := by
      intro y hy
      cases hL_eq : L with
      | nil => simp [hL_eq, oddIdx] at hy
      | cons h t =>
          have hy_od : y ∈ oddIdx (h :: t) := by
            rw [← hL_eq]
            exact List.mem_of_head? hy
          have hy_t : y ∈ t := oddIdx_mem_tail hy_od
          have hpair' : (h :: t).Pairwise (· < ·) := hL_eq ▸ hL_pair_lt
          have hh_lt : h < y := (List.pairwise_cons.mp hpair').1 y hy_t
          have hh_S : h ∈ S := (hL_mem h).mp (hL_eq ▸ List.mem_cons_self)
          have hy_S : y ∈ S := (hL_mem y).mp (hL_eq ▸ List.mem_cons_of_mem _ hy_t)
          exact ⟨h, hh_S, hh_lt, hy_S⟩
    by_cases h17 : 17 ∈ S
    · have hr1_eq : r₁ = 307 := h17_r1 h17
      have hr1_coef : 306 * r₁ ≤ 307 * (r₁ - 1) := by omega
      have hr1_ratio : 306 * sigma 1 (r₁ ^ N.factorization r₁) <
          307 * r₁ ^ N.factorization r₁ :=
        sigma_prime_pow_ratio_lt_tfl hr₁_prime (by decide) hr1_coef
      have hev_head : ∀ x ∈ (evenIdx L).head?, 17 ≤ x := by
        intro x hx
        have hx_S : x ∈ S := (hL_mem x).mp (mem_evenIdx_subset (List.mem_of_head? hx))
        rcases hS_cases x hx_S with rfl | rfl | h29
        · exact (h5 hx_S).elim
        · omega
        · omega
      have hP_ev_bd : 34 * P_ev_num ≤ 39 * P_ev_den := by
        simpa using prod_sq_abundancy_le_of_five_halves_step
          (evenIdx L) hev_chain hev_ge5 17 (by decide) hev_head
      have hod_head : ∀ y ∈ (oddIdx L).head?, 29 ≤ y := by
        intro y hy
        obtain ⟨h, hh_S, hh_lt, hy_S⟩ := hod_head_gt y hy
        have hh17 : 17 ≤ h := by
          rcases hS_cases h hh_S with rfl | rfl | h29
          · exact (h5 hh_S).elim
          · omega
          · omega
        rcases hS_cases y hy_S with rfl | rfl | h29
        · exact (h5 hy_S).elim
        · omega
        · exact h29
      have hP_od_bd : 58 * P_od_num ≤ 63 * P_od_den := by
        simpa using prod_sq_abundancy_le_of_five_halves_step
          (oddIdx L) hod_chain hod_ge5 29 (by decide) hod_head
      exact abundancy_contradiction5_le (cq := 12) (dq := 13) (cr1 := 306) (dr1 := 307)
        (cr2 := 4) (dr2 := 5) (cev := 34) (dev := 39) (cod := 58) (dod := 63)
        hN.2 hσ_eq hN_eq hq_ratio hr1_ratio hr2_ratio
        (Nat.mul_pos (by decide) hP_ev_pos) hP_ev_bd
        (Nat.mul_pos (by decide) hP_od_pos) hP_od_bd
        (by norm_num)
    · have hr1_coef : 6 * r₁ ≤ 7 * (r₁ - 1) := by
        have hr1_1 : 1 ≤ r₁ := le_trans (by decide) hr₁7
        zify [hr1_1]
        linarith [hr₁7]
      have hr1_ratio : 6 * sigma 1 (r₁ ^ N.factorization r₁) < 7 * r₁ ^ N.factorization r₁ :=
        sigma_prime_pow_ratio_lt_tfl hr₁_prime (by decide) hr1_coef
      have hS_ge29 : ∀ x ∈ S, 29 ≤ x := by
        intro x hx
        rcases hS_cases x hx with rfl | rfl | h29
        · exact (h5 hx).elim
        · exact (h17 hx).elim
        · exact h29
      have hev_head : ∀ x ∈ (evenIdx L).head?, 29 ≤ x := fun x hx =>
        hS_ge29 x ((hL_mem x).mp (mem_evenIdx_subset (List.mem_of_head? hx)))
      have hP_ev_bd : 58 * P_ev_num ≤ 63 * P_ev_den := by
        simpa using prod_sq_abundancy_le_of_five_halves_step
          (evenIdx L) hev_chain hev_ge5 29 (by decide) hev_head
      have hod_head : ∀ y ∈ (oddIdx L).head?, 41 ≤ y := by
        intro y hy
        obtain ⟨h, hh_S, hh_lt, hy_S⟩ := hod_head_gt y hy
        have hh29 : 29 ≤ h := hS_ge29 h hh_S
        have hy_prop := hS_prop y hy_S
        have hy2 : y % 2 = 1 := Nat.odd_iff.mp hy_prop.2.1
        have hy3 : y % 3 = 2 := hy_prop.2.2.2.1
        have hne35 : y ≠ 35 := fun heq => by
          subst heq
          exact absurd hy_prop.1 (by decide)
        omega
      have hP_od_bd : 82 * P_od_num ≤ 87 * P_od_den := by
        simpa using prod_sq_abundancy_le_of_five_halves_step
          (oddIdx L) hod_chain hod_ge5 41 (by decide) hod_head
      exact abundancy_contradiction5_le (cq := 12) (dq := 13) (cr1 := 6) (dr1 := 7)
        (cr2 := 4) (dr2 := 5) (cev := 58) (dev := 63) (cod := 82) (dod := 87)
        hN.2 hσ_eq hN_eq hq_ratio hr1_ratio hr2_ratio
        (Nat.mul_pos (by decide) hP_ev_pos) hP_ev_bd
        (Nat.mul_pos (by decide) hP_od_pos) hP_od_bd
        (by norm_num)

/-- If a three-free odd perfect number (`¬ 3 ∣ N`) has exactly `2` large non-Euler prime
factors, then both of them satisfy `r ≡ 1 [MOD 3]` and `twoModThreeLargeSources N q = ∅`. -/
theorem three_free_card_largeSources_two_forces_all_oneModThree {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) (hcard2 : (largeSources N q).card = 2) :
    (oneModThreeLargeSources N q).card = 2 ∧ twoModThreeLargeSources N q = ∅ ∧
      ∀ r ∈ largeSources N q, r % 3 = 1 := by
  have hor := two_le_oneModThreeLarge_or_three_le_largeSources_of_three_free ho hN hq hq4 he hev h3
  have h1_ge2 : 2 ≤ (oneModThreeLargeSources N q).card := by
    rcases hor with h2 | h3c
    · exact h2
    · omega
  have h1_le2 : (oneModThreeLargeSources N q).card ≤ 2 := by
    rw [← hcard2]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have h1_eq2 : (oneModThreeLargeSources N q).card = 2 := by omega
  have hsum_card : (oneModThreeLargeSources N q).card + (twoModThreeLargeSources N q).card =
      (largeSources N q).card := by
    rw [← Finset.card_union_of_disjoint (oneModThreeLargeSources_disjoint_two_tfl N q),
      ← largeSources_eq_union_one_two_tfl]
  have h2_zero : (twoModThreeLargeSources N q).card = 0 := by omega
  have h2_empty : twoModThreeLargeSources N q = ∅ := Finset.card_eq_zero.mp h2_zero
  refine ⟨h1_eq2, h2_empty, ?_⟩
  intro r hr
  rw [largeSources_eq_union_one_two_tfl, h2_empty, Finset.union_empty] at hr
  exact (Finset.mem_filter.mp hr).2

end OddPerfect
