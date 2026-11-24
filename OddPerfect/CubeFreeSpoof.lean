module

public import OddPerfect.QuasiFactors
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction

theorem entry_dvd_value {z : ℕ × ℕ} {X : List (ℕ × ℕ)} (hz : z ∈ X) :
    z.1 ^ z.2 ∣ listValue X :=
  List.dvd_prod (List.mem_map.mpr ⟨z, hz, rfl⟩)

theorem prime_dvd_value {p : ℕ} (hp : p.Prime) (X : List (ℕ × ℕ)) :
    p ∣ listValue X → ∃ z ∈ X, p ∣ z.1 := by
  induction X with
  | nil => exact fun h => (hp.not_dvd_one h).elim
  | cons z zs ih =>
    intro h
    rcases hp.dvd_mul.mp h with h | h
    · exact ⟨z, .head _, hp.dvd_of_dvd_pow h⟩
    · obtain ⟨w, hw, hd⟩ := ih h
      exact ⟨w, .tail _ hw, hd⟩

/-- With at most one linear entry, no two true-prime components in a
cube-free product can share a base. Its formal sum is then the actual sum. -/
theorem formalSigma_eq_of_cube_free {X : List (ℕ × ℕ)}
    (hc : ∀ p : ℕ, p.Prime → ¬p^3 ∣ listValue X)
    (hb : ∀ z ∈ X, z.1.Prime ∧ 0 < z.2)
    (hlin : (X.filter (fun z => z.2 == 1)).length ≤ 1) :
    listFormalSigma X = sigma 1 (listValue X) := by
  induction X with
  | nil => simp [listValue, listFormalSigma]
  | cons z zs ih =>
    obtain ⟨hp, he⟩ := hb z (.head _)
    have htail (p : ℕ) (hp' : p.Prime) (hd : p^3 ∣ listValue zs) : False :=
      hc p hp' (dvd_mul_of_dvd_right hd (z.1^z.2))
    have hlin' : (zs.filter (fun z => z.2 == 1)).length ≤ 1 := by
      rw [List.filter_cons] at hlin
      split at hlin
      · simp only [List.length_cons] at hlin
        omega
      · exact hlin
    have hcop : z.1.Coprime (listValue zs) := by
      apply hp.coprime_iff_not_dvd.mpr
      intro hd
      obtain ⟨w, hw, hdiv⟩ := prime_dvd_value hp zs hd
      obtain ⟨hpw, hew⟩ := hb w (.tail _ hw)
      have heq := (Nat.prime_dvd_prime_iff_eq hp hpw).mp hdiv
      have hpow : z.1^(z.2+w.2) ∣ listValue (z::zs) := by
        rw [pow_add]
        exact Nat.mul_dvd_mul (dvd_refl _) (heq.symm ▸ entry_dvd_value hw)
      apply hc z.1 hp
      apply dvd_trans _ hpow
      apply pow_dvd_pow
      by_contra! hlen
      have h1 : z.2 = 1 := by omega
      have h2 : w.2 = 1 := by omega
      have hmem : w ∈ zs.filter (fun z => z.2 == 1) := List.mem_filter.mpr ⟨hw, by simp [h2]⟩
      have hpos := List.length_pos_of_mem hmem
      rw [List.filter_cons_of_pos (p := fun z : ℕ × ℕ => z.2 == 1) (by simp [h1])] at hlin
      simp only [List.length_cons] at hlin
      omega
    change (∑ j ∈ Finset.range (z.2+1), z.1^j) * listFormalSigma zs =
      sigma 1 (z.1^z.2 * listValue zs)
    rw [isMultiplicative_sigma.map_mul_of_coprime (hcop.pow_left _), sigma_one_apply_prime_pow hp,
      ih htail (fun w hw => hb w (.tail _ hw)) hlin']

/-- Dittmer's normalized candidate class contains no cube-free numbers.
A composite prime-power base would contribute a cube outside the unique
linear entry, and the linear entry already has a prime base. -/
theorem exists_prime_cube_of_normalized_spoof {N : ℕ} (h : N ∈ normalizedSpoofCandidates) :
    ∃ p : ℕ, p.Prime ∧ p^3 ∣ N := by
  obtain ⟨ho, X, hv, hs, hparts, q, _, hq, _, hlin⟩ := h
  by_contra! hc
  have hc' (p : ℕ) (hp : p.Prime) : ¬p^3 ∣ listValue X := hv.symm ▸ hc p hp
  have hbase (z : ℕ × ℕ) (hz : z ∈ X) : z.1.Prime ∧ 0 < z.2 := by
    obtain ⟨p, hpm, d, hd, hx, hl⟩ := hparts z hz
    have he := hl.one_lt
    refine ⟨?_, by omega⟩
    by_cases h1 : z.2 = 1
    · have hm : z ∈ X.filter (fun z => z.2 == 1) := List.mem_filter.mpr ⟨hz, by simp [h1]⟩
      rw [hlin] at hm
      have heq := List.mem_singleton.mp hm
      simpa [heq] using hq
    · have hp := Nat.prime_of_mem_primeFactors hpm
      have hpow := entry_dvd_value hz
      rw [hx, ← pow_mul] at hpow
      have hd1 : d = 1 := by
        by_contra! hne
        apply hc' p hp
        refine (pow_dvd_pow _ ?_).trans hpow
        have hd2 : 2 ≤ d := by omega
        have he2 : 2 ≤ z.2 := by omega
        exact (by decide : 3 ≤ 2*2).trans (Nat.mul_le_mul hd2 he2)
      simpa [hx, hd1] using hp
  have htrue := formalSigma_eq_of_cube_free hc' hbase (by rw [hlin]; rfl)
  rw [hs, hv, sigma_one_apply] at htrue
  have hN := (Nat.perfect_iff_sum_divisors_eq_two_mul ho.pos).mpr htrue.symm
  obtain ⟨_, _, _, _, p, hp, _, _, he⟩ := steuerwald ho hN
  exact hc p (Nat.prime_of_mem_primeFactors hp)
    (((Nat.prime_of_mem_primeFactors hp).pow_dvd_iff_le_factorization hN.2.ne').mpr (by omega))

theorem descartes_not_mem_normalized_spoof : 198585576189 ∉ normalizedSpoofCandidates := by
  intro h
  obtain ⟨p, hp, hd⟩ := exists_prime_cube_of_normalized_spoof h
  exact descartes_no_prime_cube p hp hd

end OddPerfect
