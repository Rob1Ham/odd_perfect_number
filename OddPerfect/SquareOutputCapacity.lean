module

public import OddPerfect.SixthPowerFreeQuarticCollisionPinch
public import OddPerfect.SixthPowerFreeBipartiteParity
import all OddPerfect.SixthPowerFreeBipartiteParity
import Mathlib.Data.Nat.ModEq
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases

/-!
# Residue of square-source outputs and their target budget

BRANCH_MAP: A1_SPF

The modulo-five target budget excludes the square-ramified count family at every
positive scale and leaves a smaller named residual.

The local residue calculation and finite-set count are followed by a direct
specialization to the square-source set of a sixth-power-free odd perfect
number. The last count example evaluates the inequality on the named family.
-/

public section

namespace OddPerfect.SquareOutputCapacity

open ArithmeticFunction

private theorem list_prod_mod_five (L : List ℕ) (h : ∀ p ∈ L, p ≡ 3 [MOD 5]) :
    L.prod ≡ 3 ^ L.length [MOD 5] := by
  induction L with
  | nil => rfl
  | cons a l ih =>
    simpa [pow_succ, Nat.mul_comm] using
      (h a (.head l)).mul (ih fun p hp => h p (.tail a hp))

/-- If a square source is one modulo five and every prime factor of its
divisor sum is three modulo five, the total multiplicity is one modulo four. -/
theorem square_output_multiplicity_mod_four {s : ℕ} (hs : s % 5 = 1)
    (hf : ∀ p ∈ (s ^ 2 + s + 1).primeFactors, p % 5 = 3) :
    cardFactors (s ^ 2 + s + 1) % 4 = 1 := by
  let n := s ^ 2 + s + 1
  let k := cardFactors n
  have hpos : n ≠ 0 := by dsimp [n]; positivity
  have hbase : s ≡ 1 [MOD 5] := hs
  have hn : n ≡ 3 [MOD 5] := ((hbase.pow 2).add hbase).add (Nat.ModEq.refl 1)
  have hp : n ≡ 3 ^ k [MOD 5] := by
    have hl := list_prod_mod_five n.primeFactorsList (fun p hp =>
      hf p (Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hp))
    simpa [Nat.prod_primeFactorsList hpos, k, cardFactors_apply] using hl
  have hcycle : (3 ^ 4 : ℕ) ≡ 1 [MOD 5] := by decide
  have hred : 3 ^ k ≡ 3 ^ (k % 4) [MOD 5] := by
    calc
      3 ^ k = 3 ^ (k % 4 + 4 * (k / 4)) := by rw [Nat.mod_add_div]
      _ = 3 ^ (k % 4) * (3 ^ 4) ^ (k / 4) := by rw [pow_add, pow_mul]
      _ ≡ 3 ^ (k % 4) * 1 ^ (k / 4) [MOD 5] :=
        (Nat.ModEq.refl _).mul (hcycle.pow _)
      _ = 3 ^ (k % 4) := by simp
  have heq : 3 ^ (k % 4) % 5 = 3 := (hred.symm.trans hp.symm).trans hn
  change k % 4 = 1
  have hlt := Nat.mod_lt k (by decide : 0 < 4)
  generalize k % 4 = r at *
  interval_cases r <;> norm_num at *

/-- Any composite square output of multiplicity at most four from a source one
modulo five spends at least one valuation on a target outside class three. -/
theorem exists_exceptional_target {s : ℕ} (hs : s % 5 = 1)
    (hlo : 2 ≤ cardFactors (s ^ 2 + s + 1)) (hhi : cardFactors (s ^ 2 + s + 1) ≤ 4) :
    ∃ p ∈ (s ^ 2 + s + 1).primeFactors, p % 5 ≠ 3 := by
  by_contra! h
  have := square_output_multiplicity_mod_four hs h
  omega

/-- S counts square sources, Q the exponent-four targets one modulo three and
U the square sources outside class one modulo five. P and B count prime and
semiprime outputs. D counts exceptional composite outputs, and M counts all
output prime factors with multiplicity. Each input hypothesis is a budget. -/
theorem bound_of_target_budgets {S Q U P B D M : ℕ}
    (hup : P + B ≤ Q + 1)
    (hcapacity : M ≤ 4 * Q + 1)
    (hexceptional : D + 4 * P ≤ 4 * (Q + 1) + 5 * U)
    (hthree : 3 * S ≤ M + 2 * P + B)
    (hfive : 5 * S ≤ M + 4 * P + 2 * D + B) :
    10 * S ≤ 19 * Q + 5 * U + 10 := by omega

/-- The square-ramified count profile violates the residue budget at every
positive scale. This is a theorem about counts. -/
theorem square_ramified_profile_violates_bound {m : ℕ} (hm : 0 < m) :
    ¬ (10 * (4 * m + 1) ≤ 19 * (2 * m) + 5 * 0 + 10) := by omega

@[expose] def output (s : ℕ) := s^2+s+1

/-- Assemble the modulo-five budget on finite source and target sets. The caller
supplies the root-slot bound for outputs of multiplicity one or two, coverage of
prime factors, and the valuation budgets supplied by perfection. -/
theorem bound_of_square_source_sets (S T : Finset ℕ) (Q : ℕ)
    (hT : T.card = Q + 1)
    (hpos : ∀ s ∈ S, 0 < cardFactors (output s))
    (hcover : ∀ s ∈ S, (output s).primeFactors ⊆ T)
    (hshort : (S.filter (fun s => cardFactors (output s) = 1)).card +
      (S.filter (fun s => cardFactors (output s) = 2)).card ≤ T.card)
    (hweight : ∑ s ∈ S, cardFactors (output s) ≤ 4 * Q + 1)
    (hper : ∀ t ∈ T, ∑ s ∈ S, (output s).factorization t ≤ 4) :
    10 * S.card ≤ 19 * Q + 5 * (S.filter (fun s => s % 5 ≠ 1)).card + 10 := by
  classical
  let P := S.filter (fun s => cardFactors (output s) = 1)
  let B := S.filter (fun s => cardFactors (output s) = 2)
  let U := S.filter (fun s => s % 5 ≠ 1)
  let bad := T.filter (fun t => t % 5 ≠ 3)
  let w (s : ℕ) := ∑ t ∈ bad, (output s).factorization t
  have hP : P.card ≤ (T.filter (fun t => t % 5 = 3)).card + U.card := by
    have hg : (P.filter (fun s => s % 5 = 1)).card ≤ (T.filter (fun t => t % 5 = 3)).card := by
      apply Finset.card_le_card_of_injOn output
      · intro s hs
        obtain ⟨hsP, hs1⟩ := Finset.mem_filter.mp hs
        obtain ⟨hsS, hprime⟩ := Finset.mem_filter.mp hsP
        have hpr := cardFactors_eq_one_iff_prime.mp hprime
        have ho : output s ≡ 3 [MOD 5] :=
          ((((show s ≡ 1 [MOD 5] from hs1).pow 2).add (show s ≡ 1 [MOD 5] from hs1)).add (Nat.ModEq.refl 1))
        exact Finset.mem_filter.mpr ⟨hcover s hsS (Nat.mem_primeFactors.mpr ⟨hpr, dvd_rfl, hpr.ne_zero⟩), ho⟩
      · intro a _ b _ heq
        dsimp [output] at heq
        rcases lt_trichotomy a b with hab | he | hba
        · nlinarith [Nat.pow_lt_pow_left hab (by decide : 2 ≠ 0)]
        · exact he
        · nlinarith [Nat.pow_lt_pow_left hba (by decide : 2 ≠ 0)]
    have hb : P.filter (fun s => s % 5 ≠ 1) ⊆ U := by
      intro s hs
      obtain ⟨hp, h1⟩ := Finset.mem_filter.mp hs
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, h1⟩
    have hpartition := Finset.card_filter_add_card_filter_not (s := P) (fun s => s % 5 = 1)
    have hle := Finset.card_le_card hb
    change (P.filter (fun s => s % 5 = 1)).card + (P.filter (fun s => s % 5 ≠ 1)).card = P.card at hpartition
    omega
  have hbcard : bad.card + P.card ≤ Q + 1 + U.card := by
    have := Finset.card_filter_add_card_filter_not (s := T) (fun t => t % 5 = 3)
    dsimp [bad]
    omega
  have hw : ∑ s ∈ S, w s ≤ 4 * bad.card := by
    unfold w
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _t ∈ bad, 4 := Finset.sum_le_sum (fun t ht => hper t (Finset.mem_filter.mp ht).1)
      _ = _ := by simp [Nat.mul_comm]
  have hpoint (s : ℕ) (hs : s ∈ S) :
      3 ≤ cardFactors (output s) + 2 * (if cardFactors (output s) = 1 then 1 else 0) +
        (if cardFactors (output s) = 2 then 1 else 0) ∧
      5 ≤ cardFactors (output s) + 4 * (if cardFactors (output s) = 1 then 1 else 0) +
        2 * ((if s % 5 ≠ 1 then 1 else 0) + w s) +
        (if cardFactors (output s) = 2 then 1 else 0) := by
    have hpos' := hpos s hs
    by_cases h₁ : cardFactors (output s) = 1
    · simp [h₁]
    by_cases h₂ : 5 ≤ cardFactors (output s)
    · simp [h₁]; omega
    have hc : 1 ≤ (if s % 5 ≠ 1 then 1 else 0) + w s := by
      by_cases hu : s % 5 = 1
      · obtain ⟨p, hp, hp5⟩ := exists_exceptional_target hu (show 2 ≤ cardFactors (output s) by omega) (show cardFactors (output s) ≤ 4 by omega)
        have hf : 0 < (output s).factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
        have hw' : (output s).factorization p ≤ w s :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_filter.mpr ⟨hcover s hs hp,hp5⟩)
        omega
      · simp [hu]
    by_cases he : cardFactors (output s) = 2 <;> simp only [h₁, ite_false, he, ite_true] <;> omega
  have h₃ := Finset.sum_le_sum (fun s hs => (hpoint s hs).1)
  have h₅ := Finset.sum_le_sum (fun s hs => (hpoint s hs).2)
  dsimp [P, B, U] at *
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.card_filter,
    Finset.sum_const, smul_eq_mul] at h₃ h₅
  omega

/-- The residue budget for the square sources of a sixth-power-free odd perfect
number, with no auxiliary counting hypotheses. -/
theorem sixth_power_free_square_output_capacity {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    10 * (squareSources N).card ≤ 19 * (oneModThreeLargeSources N q).card +
      5 * ((squareSources N).filter (fun s => s % 5 ≠ 1)).card + 10 := by
  classical
  let S := squareSources N
  let Q := oneModThreeLargeSources N q
  let T := Insert.insert q Q
  obtain ⟨h3, _, hq1, _, hsprop, hlprop, hparts, _, _⟩ :=
    sixth_power_free_source_invariants_local ho hN hq hq4 he hev hfree
  have ssub : S ⊆ N.primeFactors := Finset.filter_subset _ _
  have qout : q ∉ Q := fun h => (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2.2.1 rfl
  have tcard : T.card = Q.card + 1 := Finset.card_insert_of_notMem qout
  have tsub : T ⊆ N.primeFactors := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hq
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
  have hlocal (s : ℕ) (hs : s ∈ S) : output s = sigma 1 (s ^ N.factorization s) := by
    obtain ⟨hp, _, _, _, _, _, hex⟩ := hsprop s hs
    rw [hex, sigma_one_apply_prime_pow hp]
    simp [output, Finset.sum_range_succ]
    ring
  have hcover (s : ℕ) (hs : s ∈ S) : (output s).primeFactors ⊆ T := by
    intro t ht
    obtain ⟨tp, td, _⟩ := Nat.mem_primeFactors.mp ht
    obtain ⟨sp, sm, _, _, _, _, hex⟩ := hsprop s hs
    have so := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors (ssub hs))
    have todd : Odd t := ((so.pow.add_odd so).add_one : Odd (output s)).of_dvd_nat td
    have hd : t ∣ N := by
      apply dvd_perfect_of_exact_prime_pow (k := N.factorization s) hN sp (Nat.ordProj_dvd N s)
        ((sp.pow_dvd_iff_le_factorization hN.2.ne').not.mpr (by omega)) tp todd
      rwa [← sigma_one_apply, ← hlocal s hs]
    have tm : t % 3 = 1 := (prime_dvd_sq_add_self_add_one tp td).resolve_left (fun h => h3 (h ▸ hd))
    have htN := Nat.mem_primeFactors.mpr ⟨tp, hd, hN.2.ne'⟩
    rcases Finset.mem_insert.mp (hparts ▸ htN) with rfl | hU
    · exact Finset.mem_insert_self _ _
    rcases Finset.mem_union.mp hU with hS | hL
    · have := (hsprop t hS).2.1
      omega
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hL, tm⟩)
  have hct (t : ℕ) (ht : t ∈ T) :
      ∑ s ∈ S, (output s).factorization t ≤ N.factorization t := by
    have tn := tsub ht
    rw [factorization_eq_sum_sigma_factorizations hN (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors tn))
      (Nat.prime_of_mem_primeFactors tn)]
    calc
      _ = ∑ s ∈ S, (sigma 1 (s ^ N.factorization s)).factorization t :=
        Finset.sum_congr rfl (fun s hs => by rw [hlocal s hs])
      _ ≤ _ := Finset.sum_le_sum_of_subset ssub
  have hsum := sum_cardFactors_le_target_exponents hN S T output ssub
    (fun s hs => (hlocal s hs).symm ▸ dvd_rfl) hcover
    (fun t ht => ⟨Nat.prime_of_mem_primeFactors (tsub ht), ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors (tsub ht))⟩)
  have hqsum : ∑ t ∈ Q, N.factorization t = 4 * Q.card := by
    calc
      _ = ∑ _t ∈ Q, 4 := Finset.sum_congr rfl fun t ht =>
        (hlprop t (Finset.mem_filter.mp ht).1).2.2.2.2.2.2
      _ = _ := by simp [Nat.mul_comm]
  change _ ≤ ∑ t ∈ insert q Q, N.factorization t at hsum
  rw [Finset.sum_insert qout,hqsum,hq1] at hsum
  let PB := S.filter fun s => cardFactors (output s) = 1 ∨ cardFactors (output s) = 2
  have hwit : ∀ s ∈ PB, ∃ t ∈ T, s < t ∧ t ∈ (output s).primeFactors := by
    intro s hs
    obtain ⟨hsS, h₁ | h₂⟩ := Finset.mem_filter.mp hs
    · have hp := cardFactors_eq_one_iff_prime.mp h₁
      have hm := Nat.mem_primeFactors.mpr ⟨hp,dvd_rfl,hp.ne_zero⟩
      exact ⟨output s, hcover s hsS hm, by dsimp [output]; omega, hm⟩
    · have sm := (hsprop s hsS).2.1
      have heq : normalizedSquareSum s = output s := by
        simp [normalizedSquareSum, output, show s % 3 ≠ 1 by omega]
      obtain ⟨t, ht, hlt⟩ := squareSourcesTwo_semiprime_exists_gt (show s % 3 ≠ 1 by omega)
        (heq ▸ h₂)
      rw [heq] at ht
      exact ⟨t, hcover s hsS ht,hlt,ht⟩
  choose! g hgT hglt hgpf using hwit
  have hinj : PB.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn g hgT
    intro a ha b hb hab
    have gp := Nat.prime_of_mem_primeFactors (hgpf a ha)
    have hd := Nat.dvd_of_mem_primeFactors (hgpf a ha)
    have hmod : g a % 3 = 1 := (prime_dvd_sq_add_self_add_one gp hd).resolve_left (fun h =>
      h3 (h ▸ Nat.dvd_of_mem_primeFactors (tsub (hgT a ha))))
    apply Finset.card_le_one.mp (card_twoModThree_dvd_sq_add_self_add_one_le_one gp hmod)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hglt a ha), (hsprop a (Finset.mem_filter.mp ha).1).2.1, hd⟩
    · rw [hab]
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hglt b hb), (hsprop b (Finset.mem_filter.mp hb).1).2.1,
        Nat.dvd_of_mem_primeFactors (hgpf b hb)⟩
  have hpbeq : PB = (S.filter (fun s => cardFactors (output s) = 1)) ∪
      (S.filter (fun s => cardFactors (output s) = 2)) := by ext; simp [PB, and_or_left]
  have hdj : Disjoint (S.filter (fun s => cardFactors (output s) = 1))
      (S.filter (fun s => cardFactors (output s) = 2)) := by
    refine Finset.disjoint_left.mpr fun s h hs => ?_
    have := (Finset.mem_filter.mp h).2
    have := (Finset.mem_filter.mp hs).2
    omega
  rw [hpbeq,Finset.card_union_of_disjoint hdj] at hinj
  apply bound_of_square_source_sets S T Q.card tcard _ hcover hinj (by omega)
  · intro t ht
    have hc := hct t ht
    rcases Finset.mem_insert.mp ht with rfl | hQ
    · omega
    · have := (hlprop t (Finset.mem_filter.mp hQ).1).2.2.2.2.2.2
      omega
  · intro s hs
    apply cardFactors_pos_iff_one_lt.mpr
    dsimp [output]
    have := (hsprop s hs).1.two_le
    omega

/-- BRANCH_MAP: A1_SPF_HIGH_SQUARE. If all square sources are one modulo five,
their number cannot reach twice the number of quartic sources one modulo three. -/
theorem no_high_square_count_of_all_one_mod_five {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hall : ((squareSources N).filter (fun s => s % 5 ≠ 1)).card = 0)
    (hmany : 2 * (oneModThreeLargeSources N q).card ≤ (squareSources N).card) :
    False := by
  have budget := sixth_power_free_square_output_capacity ho hN hq hq4 he hev hfree
  have floor := sixth_power_free_oneModThreeLarge_ge_80 ho hN hq hq4 he hev hfree
  omega

end OddPerfect.SquareOutputCapacity
