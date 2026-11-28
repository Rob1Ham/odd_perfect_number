module

public import OddPerfect.CountExcess
public import OddPerfect.ChainScript
import Mathlib.Tactic.Primality

/-! Exclude the only count pair that could give excess five using a high-support factor chain. -/

public section

namespace OddPerfect
namespace FactorBudget.ExcessSeven

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def primes : List ℕ := [3, 5, 7, 11, 13, 17, 19, 29, 31, 37, 43, 61, 67, 71, 73, 79, 97, 109, 127, 131, 151, 157, 163, 199, 211, 271, 281, 307, 331, 379, 421, 431, 433, 541, 547, 613, 617, 631, 701, 733, 743, 757, 761, 769, 787, 811, 911, 967, 1051, 1093, 1499, 1621, 1693, 1801, 2671, 2801, 3169, 3217, 3221, 3229, 3931, 4447, 4733, 4933, 5209, 5419, 7561, 11299, 17293, 18457, 21491, 30941, 33151, 39103, 70841, 86353, 398581, 732541, 1866871, 2180921, 5229043, 6619231, 10378063, 262209281, 366340651, 917087137, 52379047267, 297134095231, 31747594185191]

private theorem primes_valid : ∀ p∈primes, p.Prime := by
  simp only [primes,List.forall_mem_cons]
  exact ⟨by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 269] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 7, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 269] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 769] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 11, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 29, 421] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 20743] }, .lucas { root := 5, primeFactors := [2, 3, 3457] }, .lucas { root := 7, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 7789] }, .lucas { root := 2, primeFactors := [2, 3, 11, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 7, 13, 61, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 73547] }, .lucas { root := 2, primeFactors := [2, 11, 3343] }, .lucas { root := 5, primeFactors := [2, 3, 557] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 179, 3221] }, .lucas { root := 10, primeFactors := [2, 5, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 127, 1613] }, .lucas { root := 3, primeFactors := [2, 13, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 17, 43, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 19, 31, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 31, 61, 97, 523] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 17, 557, 16603] }, .lucas { root := 2, primeFactors := [2, 3, 2767] }, .lucas { root := 3, primeFactors := [2, 3, 461] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 13, 244212262963] }, .lucas { root := 3, primeFactors := [2, 3, 19, 3001, 713833] }, .lucas { root := 14, primeFactors := [2, 3, 5] }, .lucas { root := 5, primeFactors := [2, 3, 7, 607] }]), by simp⟩

-- Exact component 3^2 * 13.
private noncomputable def witnessPart2 : Script :=
  .split 7 [
    (2, .split 19 [
      (2, .split 127 [
        (4, .split 262209281 [
          (4, .groups [5]),
          (6, .split 43 [])]),
        (6, .split 43 [
          (4, .split 86353 [])])]),
      (4, .split 151 [
        (2, .split 911 [
          (2, .split 1093 [
            (4, .groups [11])]),
          (4, .groups [5])]),
        (4, .groups [5]),
        (6, .split 911 [
          (2, .split 1499 [
            (2, .split 199 [
              (2, .split 11299 [])])])])]),
      (6, .split 701 [
        (2, .split 70841 [
          (2, .split 39103 [
            (2, .split 7561 [
              (4, .groups [5])]),
            (4, .groups [11])]),
          (4, .groups [5])]),
        (4, .groups [5])])]),
    (4, .split 2801 [
      (2, .split 37 [
        (2, .split 43 [
          (2, .split 67 [
            (4, .split 631 [
              (4, .groups [5])]),
            (6, .split 631 [])]),
          (4, .split 67 [
            (2, .groups [31]),
            (4, .split 761 [
              (2, .split 4933 [
                (2, .split 127 [])])])]),
          (6, .split 67 [])]),
        (4, .groups [11]),
        (6, .split 43 [
          (2, .split 71 [
            (2, .split 631 [
              (2, .split 307 [])])])])]),
      (4, .groups [5]),
      (6, .split 71 [
        (2, .split 211 [])])]),
    (6, .split 29 [
      (4, .split 4733 [
        (2, .split 732541 [
          (2, .split 43 [
            (2, .split 271 [])])])])]),
    (8, .split 19 [])]

-- Exact component 3^2 * 13^2.
private noncomputable def witnessPart3 : Script :=
  .split 61 [
    (1, .split 31 [
      (2, .split 331 [
        (4, .split 5 []),
        (6, .split 2180921 [
          (2, .split 3217 [
            (4, .split 11 [
              (2, .groups [7])])]),
          (4, .split 5 [])])]),
      (4, .groups [5, 11]),
      (6, .split 917087137 [
        (2, .split 43 [
          (4, .split 4447 [])]),
        (4, .split 31747594185191 [
          (2, .split 2671 [
            (2, .split 7 [])])])])]),
    (2, .split 97 [
      (1, .split 7 [
        (4, .split 2801 [
          (2, .split 37 [
            (4, .groups [11]),
            (6, .split 43 [])]),
          (4, .groups [5]),
          (6, .split 71 [
            (2, .split 211 [])])]),
        (6, .split 29 [
          (4, .split 4733 [
            (2, .split 732541 [])])])]),
      (4, .split 11 [
        (2, .groups [7]),
        (4, .groups [5]),
        (6, .split 31 [])]),
      (6, .split 43 [
        (4, .split 967 [])])]),
    (4, .split 5 [
      (1, .split 131 [
        (2, .split 17293 [
          (4, .split 21491 [
            (2, .split 421 [])]),
          (6, .split 21491 [
            (2, .split 421 [])])]),
        (6, .split 127 [])]),
      (2, .groups [31]),
      (4, .groups [11]),
      (6, .groups [131])]),
    (5, .split 7 [
      (4, .split 31 [])]),
    (6, .split 52379047267 [
      (2, .split 6619231 [
        (4, .groups [5, 11])]),
      (4, .split 297134095231 [
        (2, .split 18457 [
          (1, .split 11 [
            (2, .groups [7, 19])])])])])]

-- Exact component 3^2 * 13^4.
private noncomputable def witnessPart4 : Script :=
  .split 30941 [
    (2, .split 157 [
      (1, .split 79 [
        (2, .split 7 [
          (2, .groups [19, 43, 433]),
          (4, .split 43 [
            (2, .split 433 [
              (4, .groups [11])]),
            (4, .split 433 [
              (2, .split 37 [])])]),
          (6, .split 29 [
            (2, .groups [43, 67])])]),
        (4, .split 433 [
          (2, .split 37 [
            (2, .split 7 [
              (4, .split 67 [])]),
            (4, .split 11 [
              (2, .groups [7])])]),
          (4, .split 11 [
            (2, .groups [7])])]),
        (6, .split 281 [
          (2, .split 109 [
            (2, .split 7 [
              (2, .split 19 [])])])])]),
      (2, .split 433 [
        (1, .split 7 [
          (2, .split 19 [
            (4, .groups [31]),
            (6, .groups [31])]),
          (4, .split 31 [
            (2, .split 331 [
              (4, .groups [5])]),
            (4, .groups [5])]),
          (6, .split 29 [
            (2, .split 31 [
              (2, .groups [67])])])]),
        (2, .split 37 [
          (1, .split 19 [
            (4, .split 151 [
              (4, .groups [5])]),
            (6, .split 701 [
              (2, .split 1693 [])])]),
          (4, .split 11 [
            (2, .groups [7]),
            (4, .groups [5])]),
          (6, .split 71 [
            (2, .split 1693 [
              (1, .groups [7, 11])])])]),
        (4, .split 11 [
          (2, .groups [7, 19]),
          (4, .groups [5])]),
        (5, .split 7 []),
        (6, .split 743 [
          (2, .split 5209 [
            (1, .split 5 [
              (2, .groups [31])]),
            (2, .split 43 [])])])]),
      (4, .split 11 [
        (2, .groups [7, 19]),
        (4, .groups [5])]),
      (5, .split 7 [
        (2, .split 19 [])]),
      (6, .split 433 [
        (1, .split 7 [
          (2, .split 19 [
            (2, .groups [31])])]),
        (2, .split 37 [
          (1, .split 19 [
            (2, .split 127 [])]),
          (2, .split 7 [])])])]),
    (4, .groups [5, 11]),
    (6, .split 7 [
      (2, .split 19 [
        (2, .split 127 [])])])]

-- Exact component 3^2.
private noncomputable def witnessPart1 : Script :=
  .split 13 [
    (1, witnessPart2),
    (2, witnessPart3),
    (4, witnessPart4),
    (5, .split 7 [
      (2, .split 19 [
        (4, .split 61 [])]),
      (4, .split 61 [
        (2, .split 97 [])])]),
    (6, .split 5229043 [
      (2, .split 31 [
        (2, .split 331 [
          (4, .split 5 [])]),
        (4, .groups [5, 11])]),
      (4, .split 151 [
        (2, .split 7 [
          (2, .split 19 [])])])]),
    (8, .split 61 [
      (1, .split 31 [])])]

-- Exact component 3^6 * 1093^2.
private noncomputable def witnessPart6 : Script :=
  .split 398581 [
    (1, .split 17 [
      (2, .split 19 [
        (2, .split 127 [
          (2, .split 307 [
            (2, .split 43 [
              (2, .split 617 [
                (2, .split 97 [
                  (2, .split 631 [
                    (4, .groups [5])]),
                  (4, .groups [11, 31, 631, 733, 3931, 5419, 262321])]),
                (4, .split 631 [
                  (2, .split 433 [])])]),
              (4, .split 617 [
                (2, .split 97 [
                  (2, .split 733 [
                    (2, .split 3169 [])])])])]),
            (4, .split 617 [
              (2, .split 97 [
                (2, .split 1051 [
                  (2, .split 1621 [
                    (2, .groups [7, 13])])])])])]),
          (4, .split 307 [
            (2, .split 43 [
              (2, .split 617 [
                (2, .split 97 [
                  (2, .split 631 [
                    (2, .split 433 [])])])])])])]),
        (4, .split 151 [
          (2, .split 7 [
            (2, .split 307 [
              (2, .groups [43])])])])]),
      (4, .split 19 [
        (2, .split 127 [
          (2, .split 617 [
            (2, .split 97 [
              (2, .split 3169 [
                (2, .split 3931 [
                  (2, .groups [7, 31])])])])])])])]),
    (2, .split 1621 [
      (1, .split 811 [
        (2, .split 31 [
          (2, .split 73 [
            (2, .split 97 [
              (2, .split 331 [
                (4, .split 5 [
                  (2, .split 1801 [])])]),
              (4, .split 11 [
                (2, .groups [7, 19])])]),
            (4, .split 97 [
              (2, .split 331 [
                (2, .split 7 [])])])]),
          (4, .groups [5, 11])]),
        (4, .split 5 [
          (2, .split 31 [
            (2, .split 331 [
              (2, .groups [7])])])])]),
      (2, .split 7 [
        (2, .split 13 [
          (1, .split 19 [
            (2, .groups [127]),
            (4, .groups [151, 911])]),
          (2, .groups [19, 61]),
          (4, .split 19 [
            (2, .groups [127])])]),
        (4, .split 13 [
          (1, .split 2801 [
            (2, .split 37 [
              (2, .groups [43, 67])])]),
          (2, .split 61 [
            (1, .split 31 [
              (2, .split 331 [
                (2, .split 2801 [
                  (2, .groups [37])])])]),
            (2, .split 97 [
              (1, .split 2801 [
                (2, .groups [37])]),
              (2, .split 2801 [
                (2, .groups [37])])])])])]),
      (4, .split 5 [
        (1, .split 11 [
          (2, .groups [7])]),
        (2, .groups [11])])]),
    (4, .split 5 [
      (1, .split 1866871 [
        (2, .split 19 [
          (2, .split 127 [
            (2, .split 331 [
              (2, .groups [7])])])])]),
      (2, .split 31 [
        (2, .split 331 [
          (2, .groups [7])])])])]

-- Exact component 3^6.
private noncomputable def witnessPart5 : Script :=
  .split 1093 [
    (1, .split 547 [
      (2, .split 163 [
        (2, .split 7 [
          (2, .split 19 [
            (2, .split 67 [
              (4, .split 127 [
                (2, .split 613 [
                  (2, .split 761 [
                    (2, .split 5419 [])])])])]),
            (4, .split 67 [])]),
          (4, .split 19 [
            (2, .split 67 [
              (2, .split 31 [
                (2, .split 127 [
                  (2, .split 331 [])])])])])]),
        (4, .split 11 [
          (2, .groups [7, 19])])]),
      (4, .split 431 [
        (2, .split 7 [
          (2, .split 19 [
            (2, .split 67 [])])])])]),
    (2, witnessPart6),
    (4, .split 11 [
      (2, .groups [7, 19, 31])])]

private noncomputable def witness : Script :=
  .split 3 [
    (2, witnessPart1),
    (4, .split 11 [
      (2, .split 7 [
        (2, .groups [19]),
        (4, .groups [19]),
        (6, .groups [19])]),
      (4, .split 5 [
        (1, .split 3221 [
          (2, .split 10378063 [
            (2, .split 769 [
              (2, .groups [31]),
              (4, .split 541 [
                (2, .groups [7])])]),
            (4, .split 33151 [
              (2, .split 366340651 [
                (2, .split 3229 [
                  (2, .groups [7])])])])])])]),
      (6, .split 43 [
        (2, .split 631 [
          (2, .split 307 [
            (2, .split 433 [
              (1, .groups [7, 31, 733]),
              (2, .split 37 [
                (1, .split 19 [])])])])])])]),
    (6, witnessPart5),
    (8, .split 13 [
      (1, .split 7 [
        (2, .split 19 [
          (2, .groups [127, 757])])]),
      (2, .split 61 [
        (1, .split 31 [
          (2, .split 331 [
            (2, .split 7 [
              (2, .groups [19])])])]),
        (2, .split 97 [
          (1, .split 7 [
            (2, .groups [19])]),
          (2, .split 757 [
            (1, .split 379 [
              (2, .split 787 [
                (2, .split 37 [
                  (2, .groups [7, 67, 151])])])])])])])])]

private theorem checked : replayScript primes 3 1 37 16 31 38 root witness = true := by
  decide +kernel

theorem exclude {N : ℕ} (H : Conditions N 37 16) (h3 : 3∣N) : False := by
  apply replayScript_correct H h3 (Nat.coprime_one_left N) ?_ primes primes_valid 38 (root_realizes N) witness checked
  have := ochem_rao_prime_factor_count H.odd H.perfect
  have hcount : N.primeFactorsList.length ≤ 37 := H.count
  omega

end FactorBudget.ExcessSeven

/-- A count pair attaining the previous additive lower bound would require
37 prime factors with multiplicity and 16 distinct factors, including three. -/
theorem seven_le_prime_factor_count_excess {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    2 * N.primeFactors.card + 7 ≤ N.primeFactorsList.length := by
  by_cases h3 : 3∣N
  · by_contra! opposite
    have := Nat.odd_iff.mp (odd_total_prime_factor_count ho hN)
    have := thirty_seven_le_total_prime_factor_count ho hN
    have := ochem_rao_prime_factor_count ho hN
    apply FactorBudget.ExcessSeven.exclude (N:=N) _ h3
    refine ⟨ho,hN,?_,by omega⟩
    change N.primeFactorsList.length ≤ 37
    omega
  · exact seven_le_prime_factor_count_excess_of_three_free ho hN h3

end OddPerfect
