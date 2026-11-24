module

public import OddPerfect.CubeFreeSpoof
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Primality

public section

namespace OddPerfect

open Finset ArithmeticFunction

private def componentSum (z : ℕ × ℕ) := ∑ j ∈ range (z.2+1), z.1^j

private theorem selected_sums_dvd (X : List (ℕ × ℕ)) (T : Finset (ℕ × ℕ))
    (hm : ∀ w ∈ T, w ∈ X) : T.prod componentSum ∣ listFormalSigma X := by
  induction X generalizing T with
  | nil =>
    have ht : T = ∅ := eq_empty_iff_forall_notMem.mpr (fun w hw => List.not_mem_nil (hm w hw))
    simp [ht]
  | cons z zs ih =>
    change T.prod componentSum ∣ componentSum z * listFormalSigma zs
    by_cases hz : z ∈ T
    · rw [← mul_prod_erase T componentSum hz]
      apply Nat.mul_dvd_mul_left
      apply ih _ (fun w hw => (List.mem_cons.mp (hm w (mem_of_mem_erase hw))).resolve_left (ne_of_mem_erase hw))
    · apply dvd_mul_of_dvd_right _ _
      apply ih T (fun w hw => (List.mem_cons.mp (hm w hw)).resolve_left (fun h => hz (h ▸ hw)))

set_option maxRecDepth 8192 in
/-- If every prime of an odd formally balanced product has a square entry,
the order-three factor chains force at least four copies of three. -/
theorem three_fourth_dvd_of_all_square_entries {N : ℕ} {X : List (ℕ × ℕ)}
    (ho : Odd N) (hgt : 1 < N) (hbal : listFormalSigma X = 2*N)
    (hcover : ∀ p : ℕ, p.Prime → p ∣ N → (p,2) ∈ X) : 3^4 ∣ N := by
  have quad (p : ℕ) (hp : p.Prime) (hd : p ∣ N) : p^2+p+1 ∣ N := by
    have hgeo := selected_sums_dvd X {(p,2)} (by simpa using hcover p hp hd)
    rw [hbal, prod_singleton] at hgeo
    have hpol : componentSum (p,2) = p^2+p+1 := by simp [componentSum, sum_range_succ]; ring
    rw [hpol] at hgeo
    have hpodd := ho.of_dvd_nat hd
    have hodd : Odd (p^2+p+1) := (hpodd.pow.add_odd hpodd).add_odd odd_one
    exact hodd.coprime_two_right.dvd_of_dvd_mul_left hgeo
  let p := N.minFac
  have hp : p.Prime := Nat.minFac_prime hgt.ne'
  have hquad := quad p hp (Nat.minFac_dvd N)
  let r := (p^2+p+1).minFac
  have hr : r.Prime := Nat.minFac_prime (by have := hp.pos; nlinarith)
  have hdr : r ∣ p^2+p+1 := Nat.minFac_dvd _
  have hrN := hdr.trans hquad
  have h3 : 3 ∣ N := by
    rcases prime_dvd_sq_add_self_add_one hr hdr with h | h
    · exact h ▸ hrN
    · have hdiv : 3 ∣ r^2+r+1 := by
        apply Nat.dvd_of_mod_eq_zero
        have hr1 : r ≡ 1 [MOD 3] := h
        exact ((hr1.pow 2).add hr1).add_right 1
      exact hdiv.trans (quad r hr hrN)
  have h13 := (by decide : 13 ∣ 3^2+3+1).trans (quad 3 (by decide) h3)
  have h61 := (by decide : 61 ∣ 13^2+13+1).trans (quad 13 (by decide) h13)
  have h97 := (by decide : 97 ∣ 61^2+61+1).trans (quad 61 (by decide) h61)
  have h3169 := (by decide : 3169 ∣ 97^2+97+1).trans (quad 97 (by decide) h97)
  let T : Finset (ℕ × ℕ) := {(13,2),(61,2),(97,2),(3169,2)}
  have hmult := selected_sums_dvd X T (by
    intro w hw
    simp only [T, mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact hcover 13 (by decide) h13
    · exact hcover 61 (by decide) h61
    · exact hcover 97 (by decide) h97
    · exact hcover 3169 (by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2,3,11] }])) h3169)
  have hd : 3^4 ∣ T.prod componentSum := by decide +kernel
  rw [hbal] at hmult
  exact (by decide : Nat.Coprime (3^4) 2).dvd_of_dvd_mul_left (hd.trans hmult)

/-- Distinct prime bases give the actual divisor sum even when the input is an ordered list. -/
theorem listFormalSigma_eq_of_distinct_primes {X : List (ℕ × ℕ)}
    (hp : ∀ z ∈ X, z.1.Prime) (hn : X.Pairwise (fun z w => z.1 ≠ w.1)) :
    listFormalSigma X = sigma 1 (listValue X) := by
  induction X with
  | nil => simp [listFormalSigma, listValue]
  | cons z zs ih =>
    obtain ⟨hneq, ht⟩ := List.pairwise_cons.mp hn
    have hpz := hp z (.head _)
    have hcop : z.1.Coprime (listValue zs) := by
      apply hpz.coprime_iff_not_dvd.mpr
      intro hd
      obtain ⟨w, hw, hdiv⟩ := prime_dvd_value hpz zs hd
      exact hneq w hw ((Nat.prime_dvd_prime_iff_eq hpz (hp w (.tail _ hw))).mp hdiv)
    change _ * listFormalSigma zs = sigma 1 (z.1^z.2 * listValue zs)
    rw [isMultiplicative_sigma.map_mul_of_coprime (hcop.pow_left _), sigma_one_apply_prime_pow hpz,
      ih (fun w hw => hp w (.tail _ hw)) ht]

private theorem distinct_without_mixed_entries (X : List (ℕ × ℕ))
    (hc : ∀ p : ℕ, p.Prime → ¬p^4 ∣ listValue X)
    (hshape : ∀ z ∈ X, z.1.Prime ∧ (z.2=1 ∨ z.2=2))
    (hlin : (X.filter (fun z => z.2 == 1)).length ≤ 1)
    (hmix : ∀ p, (p,1) ∈ X → (p,2) ∉ X) : X.Pairwise (fun z w => z.1 ≠ w.1) := by
  induction X with
  | nil => simp
  | cons z zs ih =>
    apply List.pairwise_cons.mpr
    constructor
    · intro w hw heq
      rcases hshape z (.head _) with ⟨hp, he1|he2⟩
      · rcases (hshape w (.tail _ hw)).2 with h1|h2
        · have hmem : w ∈ zs.filter (fun z => z.2 == 1) := List.mem_filter.mpr ⟨hw, by simp [h1]⟩
          have := List.length_pos_of_mem hmem
          rw [List.filter_cons_of_pos (p := fun z : ℕ × ℕ => z.2 == 1) (by simp [he1])] at hlin
          simp only [List.length_cons] at hlin
          omega
        · have hw' : (w.1,w.2) ∈ z::zs := .tail _ hw
          rw [← heq,h2] at hw'
          exact hmix z.1 (by simp [← he1]) hw'
      · rcases (hshape w (.tail _ hw)).2 with h1|h2
        · have hw' : (w.1,w.2) ∈ z::zs := .tail _ hw
          rw [← heq,h1] at hw'
          exact hmix z.1 hw' (by simp [← he2])
        · apply hc z.1 hp
          change z.1^4 ∣ z.1^z.2 * listValue zs
          rw [he2, show z.1^4=z.1^2*z.1^2 by ring]
          apply Nat.mul_dvd_mul_left
          simpa [heq,h2] using entry_dvd_value hw
    · apply ih (fun p hp hd => hc p hp (dvd_mul_of_dvd_right hd _)) (fun w hw => hshape w (.tail _ hw))
      · rw [List.filter_cons] at hlin
        split at hlin
        · simp only [List.length_cons] at hlin
          omega
        · exact hlin
      · exact fun p h1 h2 => hmix p (.tail _ h1) (.tail _ h2)

/-- A genuine prime fourth power is necessary even on Dittmer's
existential class of normalized odd spoof candidates. -/
theorem exists_prime_fourth_of_normalized_spoof {N : ℕ} (h : N ∈ normalizedSpoofCandidates) :
    ∃ p : ℕ, p.Prime ∧ p^4 ∣ N := by
  obtain ⟨ho, X, hv, hs, hparts, q, hqm, hq, _, hlin⟩ := h
  by_contra! hc
  have hshape (z : ℕ × ℕ) (hz : z ∈ X) : z.1.Prime ∧ (z.2=1 ∨ z.2=2) := by
    obtain ⟨p, hm, d, hd, hx, hl⟩ := hparts z hz
    have hp := Nat.prime_of_mem_primeFactors hm
    by_cases h1 : z.2=1
    · have hmem : z ∈ X.filter (fun z => z.2 == 1) := List.mem_filter.mpr ⟨hz, by simp [h1]⟩
      rw [hlin] at hmem
      have := List.mem_singleton.mp hmem
      exact ⟨this ▸ hq, Or.inl h1⟩
    · have hpow := entry_dvd_value hz
      rw [hv, hx, ← pow_mul] at hpow
      have hsmall : d*z.2 < 4 := by
        by_contra! hh
        exact hc p hp ((pow_dvd_pow p hh).trans hpow)
      have hpos := hl.one_lt
      have he2 : 2 ≤ z.2 := by omega
      have hd1 : d=1 := by
        by_contra! hn
        have := Nat.mul_le_mul (by omega : 2 ≤ d) he2
        omega
      rw [hd1, one_mul] at hsmall
      have h3 : z.2 ≠ 3 := by
        intro heq
        rw [heq] at hl
        exact (by decide : ¬Nat.Prime 4) hl
      exact ⟨by simpa [hx,hd1] using hp, Or.inr (by omega)⟩
  by_cases hq2 : (q,2) ∈ X
  · have hgt := hq.two_le.trans (Nat.le_of_dvd ho.pos (Nat.dvd_of_mem_primeFactors hqm))
    apply hc 3 (by decide)
    apply three_fourth_dvd_of_all_square_entries ho hgt hs
    intro p hp hd
    obtain ⟨w, hw, hdiv⟩ := prime_dvd_value hp X (hv ▸ hd)
    have heq := (Nat.prime_dvd_prime_iff_eq hp (hshape w hw).1).mp hdiv
    rcases (hshape w hw).2 with h1 | h2
    · have hmem : w ∈ X.filter (fun z => z.2 == 1) := List.mem_filter.mpr ⟨hw, by simp [h1]⟩
      rw [hlin] at hmem
      have hqeq : w = (q,1) := List.mem_singleton.mp hmem
      simpa [heq,hqeq] using hq2
    · simpa [heq, ← h2] using hw
  · have hmix (p : ℕ) (h1 : (p,1) ∈ X) : (p,2) ∉ X := by
      have hmem : (p,1) ∈ X.filter (fun z => z.2 == 1) := List.mem_filter.mpr ⟨h1,rfl⟩
      rw [hlin] at hmem
      have hpq : p=q := congrArg Prod.fst (List.mem_singleton.mp hmem)
      rwa [hpq]
    have htrue := listFormalSigma_eq_of_distinct_primes (fun z hz => (hshape z hz).1)
      (distinct_without_mixed_entries X (hv.symm ▸ hc) hshape (by rw [hlin]; rfl) hmix)
    rw [hs,hv,sigma_one_apply] at htrue
    have hN := (Nat.perfect_iff_sum_divisors_eq_two_mul ho.pos).mpr htrue.symm
    obtain ⟨_, _, _, _, p, hp, _, _, he⟩ := steuerwald ho hN
    exact hc p (Nat.prime_of_mem_primeFactors hp)
      (((Nat.prime_of_mem_primeFactors hp).pow_dvd_iff_le_factorization hN.2.ne').mpr he)

end OddPerfect
