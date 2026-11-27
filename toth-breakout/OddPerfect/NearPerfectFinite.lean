module

public import OddPerfect.NearPerfectPrefix
import OddPerfect.Cuts
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect
open Finset ArithmeticFunction

/-- An odd near-perfect number has a uniformly bounded closing label at each
prime component when its number of distinct prime divisors is bounded. -/
theorem NearPerfectWith.component_bound {n d k : ℕ} (h : NearPerfectWith n d) (ho : Odd n)
    (hc : n.primeFactors.card≤k) : ∀ p∈n.primeFactors,
      p^(n.factorization p+1) ≤ productLabelBound (2*k+1) (2*k+1) 1 := by
  obtain ⟨hd, hsum⟩ := nearPerfectWith_iff_erase.mp h
  have hσ2 : sigma 1 n = 2 * n + d := by
    have ha := Finset.add_sum_erase n.properDivisors (fun i => i) hd
    rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
    omega
  obtain ⟨⟨t,hn⟩,_⟩ := Nat.mem_properDivisors.mp hd
  have oddt := ho.of_dvd_nat (hn ▸ dvd_mul_left t d : t∣n)
  have oddσ : Odd (sigma 1 n) := (odd_sigma_iff_square_of_odd ho).mpr (h.isSquare_of_odd ho)
  let P := n.primeFactors
  let L := fun p => p^(n.factorization p+1)
  let f := fun p => p^n.factorization p
  let g := fun p => ∑ j∈range (n.factorization p+1),p^j
  let x := 2*t+1
  let S := (P.disjSum P).insertNone
  let label : Option (ℕ ⊕ ℕ) → ℕ := fun i => i.elim x (Sum.elim id L)
  let a : Option (ℕ ⊕ ℕ) → ℕ := fun i => i.elim (2*t) (Sum.elim id (fun p => L p-1))
  let b : Option (ℕ ⊕ ℕ) → ℕ := fun i => i.elim x (Sum.elim (fun p => p-1) L)
  have gt (p) (hp : p∈P) := (Nat.prime_of_mem_primeFactors hp).one_lt
  have oddp (p) (hp : p∈P) := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
  have less (p) (hp : p∈P) : p≤L p := by
    dsimp [L]; rw [pow_succ]; exact Nat.le_mul_of_pos_left _ (pow_pos (gt p hp).le _)
  have exactg (p) (hp : p∈P) : g p = sigma 1 (f p) := (sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)).symm
  have pf : P.prod f=n := (Nat.prod_primeFactors_pow_factorization ho.pos.ne').symm
  have pg : P.prod g=sigma 1 n := (prod_congr rfl exactg).trans
    (isMultiplicative_sigma.multiplicative_factorization _ ho.pos.ne').symm
  have balance : t*P.prod g = x*P.prod f := by
    rw [pg,pf,hσ2,hn]; dsimp [x]; ring
  have full : S.prod a=2*S.prod b := by
    simp only [S,a,b,prod_insertNone,prod_disjSum,Option.elim,Sum.elim_inl,Sum.elim_inr,id_eq]
    rw [show 2*(x*((∏ i∈P,(i-1))*P.prod L))=(2*x)*((∏ i∈P,(i-1))*P.prod L) by ring]
    apply (NearPrefix.clear_completed P P id (fun p => n.factorization p) (2*t) (2*x) (by rfl) gt).mpr
    simpa only [id_eq,sdiff_self,bot_eq_empty,prod_empty,mul_one,mul_assoc] using congrArg (2*·) balance
  have card : S.card ≤ 2*k+1 := by dsimp [S]; rw [card_insertNone,card_disjSum]; change P.card≤k at hc; omega
  have pair (i) (hi : i∈S) : 1<label i ∧
      (a i=label i ∧ b i=label i-1 ∨ a i=label i-1 ∧ b i=label i) := by
    cases i with
    | none => exact ⟨(by dsimp [label,x]; have := oddt.pos; omega),.inr ⟨rfl,rfl⟩⟩
    | some i =>
      have hm : i∈P.disjSum P := some_mem_insertNone.mp hi
      cases i with
      | inl p => exact ⟨gt p (inl_mem_disjSum.mp hm),.inl ⟨rfl,rfl⟩⟩
      | inr p => exact ⟨(gt p (inr_mem_disjSum.mp hm)).trans_le (less p (inr_mem_disjSum.mp hm)),.inr ⟨rfl,rfl⟩⟩
  have gap (T : ℕ) (remaining : ∃ i∈S,T<label i) :
      (S.filter (fun i => label i≤T)).prod a ≠ 2*(S.filter (fun i => label i≤T)).prod b := by
    let l := P.filter (fun p => p≤T)
    let c := P.filter (fun p => L p≤T)
    have cl : c⊆l := fun p hp => mem_filter.mpr ⟨(mem_filter.mp hp).1,
      (less p (mem_filter.mp hp).1).trans (mem_filter.mp hp).2⟩
    have cp : c⊆P := filter_subset _ _
    have op : l \ c ⊆ P := sdiff_subset.trans (filter_subset _ _)
    have filtered (v : Option (ℕ ⊕ ℕ) → ℕ) : (S.filter (fun i => label i≤T)).prod v =
        (if x≤T then v none else 1)*((∏ p∈l,v (some (.inl p)))*∏ p∈c,v (some (.inr p))) := by
      simp only [S,prod_filter,prod_insertNone,prod_disjSum,l,c]; rfl
    rw [filtered,filtered]
    by_cases seen : x≤T
    · simp only [seen, ↓reduceIte, a, b, L, Option.elim, Sum.elim_inl, Sum.elim_inr]
      have right : ∀ y, 2*(x*y)=(2*x)*y := fun _ => (Nat.mul_assoc ..).symm
      rw [right]
      intro eq
      have clear := (NearPrefix.clear_completed l c id (fun p => n.factorization p) (2*t) (2*x)
        cl (fun i hi => gt i (cp hi))).mp (by simpa only [id_eq] using eq)
      have proper : c ⊂ P := by
        apply (ssubset_iff_of_subset cp).mpr
        obtain ⟨i,hi,lt⟩ := remaining
        cases i with
        | none => exact (lt.not_ge seen).elim
        | some i =>
          have hm := some_mem_insertNone.mp hi
          cases i with
          | inl p =>
            have hp := inl_mem_disjSum.mp hm
            exact ⟨p,hp,fun hc => lt.not_ge ((less p hp).trans (mem_filter.mp hc).2)⟩
          | inr p => exact ⟨p,inr_mem_disjSum.mp hm,fun hc => lt.not_ge (mem_filter.mp hc).2⟩
      have comp (p) (hp : p∈P) : 0<f p ∧ f p<g p := by
        have hf : 1<f p := one_lt_pow₀ (gt p hp) (Finsupp.mem_support_iff.mp hp)
        exact ⟨hf.le,exactg p hp ▸ self_lt_sigma_of_one_lt hf⟩
      apply NearPrefix.with_extra oddt proper op (pg ▸ oddσ) oddp comp balance
      simp only [mul_assoc, id_eq] at clear
      exact Nat.eq_of_mul_eq_mul_left (by decide : 0<2) clear
    · simp only [seen, ↓reduceIte, a, b, L, Option.elim, Sum.elim_inl, Sum.elim_inr, one_mul]
      intro eq
      have clear := (NearPrefix.clear_completed l c id (fun p => n.factorization p) 1 2
        cl (fun i hi => gt i (cp hi))).mp (by simpa only [one_mul, id_eq] using eq)
      exact NearPrefix.without_extra (pg ▸ oddσ) cp (fun p hp => oddp p (op hp)) _
        (by simpa only [one_mul, id_eq] using clear)
  intro p hp
  exact labels_bounded_of_no_balanced_prefix S label a b card full pair gap
    (some (.inr p)) (some_mem_insertNone.mpr (inr_mem_disjSum.mpr hp))

/-- The odd branch of the fixed-rank near-perfect finiteness question. -/
theorem finite_odd_nearPerfect_of_bounded_prime_count (k : ℕ) :
    Set.Finite {n : ℕ | Odd n ∧ n.primeFactors.card≤k ∧ ∃ d, NearPerfectWith n d} := by
  let B := max 1 (productLabelBound (2*k+1) (2*k+1) 1)
  apply (Set.finite_le_nat (B^k)).subset
  rintro n ⟨ho,hk,d,h⟩
  have cap (p) (hp : p∈n.primeFactors) : p^n.factorization p≤B :=
    (Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hp).pos (Nat.le_succ _)).trans
      ((h.component_bound ho hk p hp).trans (le_max_right _ _))
  change n ≤ B^k
  rw [Nat.prod_primeFactors_pow_factorization ho.pos.ne']
  have bound := prod_le_prod₀ (fun p (_:p∈n.primeFactors) => Nat.zero_le (p^n.factorization p)) cap
  rw [prod_const] at bound
  exact bound.trans (Nat.pow_le_pow_right (le_max_left 1 _) hk)

end OddPerfect
