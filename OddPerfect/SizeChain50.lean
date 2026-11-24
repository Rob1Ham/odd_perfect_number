module

public import OddPerfect.SizeChain
import Mathlib.Tactic.Primality

/-! Replay data for the exact-exponent factor-count certificates. -/

public section

namespace OddPerfect.FactorBudget

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private noncomputable def splitPrimes : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 127, 131, 139, 151, 157, 163, 181, 191, 199, 211, 223, 271, 281, 307, 313, 331, 379, 397, 409, 419, 431, 433, 443, 467, 487, 491, 521, 547, 599, 613, 617, 631, 683, 701, 733, 757, 761, 769, 787, 811, 829, 859, 883, 911, 967, 1051, 1093, 1123, 1151, 1223, 1361, 1451, 1499, 1597, 1621, 1723, 1801, 1861, 1871, 2281, 2551, 2557, 2633, 2801, 3169, 3187, 3221, 3313, 3499, 3541, 3851, 4561, 4651, 4733, 5113, 5233, 5419, 8951, 8971, 13537, 14009, 14713, 15797, 16651, 17293, 17351, 17707, 19531, 29251, 30941, 39103, 42407, 43609, 45319, 70841, 86353, 104281, 175897, 187123, 292561, 368089, 398581, 579281, 732541, 797161, 1609669, 1717451, 1806113, 2180921, 3044803, 5229043, 10378063, 12207031, 12865927, 13097927, 22406023, 262209281, 305175781, 917087137, 16148168401, 52379047267, 50544702849929377, 6115909044841454629, 109912203092239643840221, 751670559138758105956097]

private theorem prime_proofs : ∀ p ∈ splitPrimes, p.Prime := by
  simp only [splitPrimes, List.forall_mem_cons]
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
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 17, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 613] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 359] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 347] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 13, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 23, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 13, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 11, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 5, 11, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 2399] }, .lucas { root := 11, primeFactors := [2, 11, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 23, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 313] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 13, 557] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 29, 421] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7, 13, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 61, 733] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 701] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11, 733] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 7789] }, .lucas { root := 2, primeFactors := [2, 3, 11, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 29851] }, .lucas { root := 2, primeFactors := [2, 3, 5, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 7, 13, 61, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 179, 3221] }, .lucas { root := 10, primeFactors := [2, 5, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 71, 521] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19, 112859] }, .lucas { root := 2, primeFactors := [2, 73, 773] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 37, 263, 673] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 263, 4733] }, .lucas { root := 5, primeFactors := [2, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 127, 1613] }, .lucas { root := 3, primeFactors := [2, 13, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 13, 31, 601] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 19, 31, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 5, 7, 13, 19, 43, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 31, 61, 97, 523] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 17, 61, 7321, 6304673] }, .lucas { root := 7, primeFactors := [2, 3, 5, 61] }, .lucas { root := 3, primeFactors := [2, 11, 17911] }, .lucas { root := 3, primeFactors := [2, 3, 5, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 7, 11, 19, 37, 590077, 1772893] }, .lucas { root := 6, primeFactors := [2, 3, 37, 443] }, .lucas { root := 17, primeFactors := [2, 3, 11, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 19, 127, 199, 523, 29989, 236377] }, .lucas { root := 2, primeFactors := [2, 3, 7, 17] }, .lucas { root := 10, primeFactors := [2, 3, 7, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 17, 31, 37, 409, 1129, 25085030513] }, .lucas { root := 11, primeFactors := [2, 3, 47] }, .lucas { root := 3, primeFactors := [2, 1229, 1275683] }, .lucas { root := 2, primeFactors := [2, 307] }, .lucas { root := 2, primeFactors := [2, 637841] }, .lucas { root := 21, primeFactors := [2, 5, 7, 17, 67] }]), by simp⟩

-- Exact component 3^2 * 13 * 7^2.
private noncomputable def seed3Part3 : Script :=
  .split 19 [
    (2, .split 127 [
      (4, .split 262209281 []),
      (6, .split 43 [
        (4, .split 86353 [])]),
      (10, .groups [23])]),
    (4, .split 151 [
      (2, .split 911 [
        (2, .split 1093 [
          (4, .groups [11])]),
        (4, .groups [5])]),
      (4, .groups [5]),
      (6, .split 911 [
        (2, .split 1499 [])])]),
    (6, .split 701 [
      (2, .split 70841 [
        (2, .split 39103 [])]),
      (4, .groups [5]),
      (6, .split 70841 [])]),
    (10, .split 104281 [
      (2, .split 43 [])]),
    (12, .split 599 [
      (2, .split 29251 [])]),
    (14, .groups [31, 127, 151]),
    (16, .split 3044803 []),
    (18, .split 109912203092239643840221 [])]

-- Exact component 3^2 * 13.
private noncomputable def seed3Part2 : Script :=
  .split 7 [
    (2, seed3Part3),
    (4, .split 2801 [
      (2, .split 37 [
        (2, .split 43 [
          (2, .split 67 [
            (4, .split 631 []),
            (6, .split 631 [])]),
          (4, .split 67 [
            (2, .groups [31]),
            (4, .split 761 [])]),
          (6, .split 67 [])]),
        (4, .groups [11]),
        (6, .split 43 [
          (2, .split 71 [
            (2, .split 631 [])]),
          (4, .split 71 [])]),
        (8, .split 43 []),
        (10, .split 43 [])]),
      (4, .groups [5]),
      (6, .split 71 [])]),
    (6, .split 29 [
      (4, .split 4733 [
        (2, .split 732541 []),
        (4, .groups [11])]),
      (6, .split 4733 [
        (2, .split 22406023 [])]),
      (10, .split 23 [
        (2, .split 79 [
          (2, .groups [43])]),
        (4, .split 4733 [])]),
      (12, .split 521 [])]),
    (8, .split 19 [
      (4, .split 37 [
        (4, .groups [11]),
        (6, .groups [71, 151])]),
      (6, .split 37 [
        (4, .groups [11]),
        (6, .groups [71, 701, 1063])]),
      (10, .split 37 []),
      (12, .split 37 [])]),
    (10, .split 1123 [
      (2, .split 127 [
        (2, .split 3313 []),
        (4, .split 3313 [])]),
      (4, .split 41 [
        (2, .split 1723 [])])]),
    (12, .split 16148168401 []),
    (14, .split 19 [
      (2, .split 31 [
        (4, .groups [5]),
        (6, .split 127 [])]),
      (4, .split 31 [
        (2, .groups [151, 331, 911]),
        (4, .groups [5])]),
      (6, .split 31 [
        (2, .split 331 []),
        (4, .groups [5])]),
      (10, .split 31 [])]),
    (16, .split 14009 [
      (2, .split 223 [
        (2, .split 16651 [])])]),
    (18, .split 419 []),
    (20, .split 19 [
      (2, .split 29 [
        (4, .split 127 [])]),
      (4, .split 29 []),
      (6, .split 29 [])]),
    (22, .split 47 [
      (2, .split 37 [
        (2, .split 61 [])])]),
    (24, .split 2551 []),
    (28, .split 59 [])]

-- Exact component 3^2 * 13^2 * 61^2.
private noncomputable def seed3Part5 : Script :=
  .split 97 [
    (1, .split 7 [
      (4, .split 2801 [
        (2, .split 37 [
          (4, .groups [11]),
          (6, .split 43 [])]),
        (4, .groups [5])]),
      (6, .split 29 [
        (4, .split 4733 [
          (2, .split 732541 [])]),
        (6, .split 4733 [
          (2, .split 22406023 [])]),
        (10, .groups [23])]),
      (10, .split 1123 [
        (4, .split 41 [])]),
      (12, .split 16148168401 []),
      (16, .split 14009 [
        (2, .split 223 [])]),
      (18, .split 419 []),
      (22, .split 47 [
        (2, .split 37 [])]),
      (24, .split 2551 [])]),
    (4, .split 11 [
      (2, .groups [7]),
      (4, .groups [5]),
      (6, .split 31 [
        (4, .groups [5])]),
      (8, .groups [7]),
      (10, .split 31 []),
      (12, .split 31 [])]),
    (6, .split 43 [
      (4, .split 967 []),
      (6, .split 7 [])]),
    (9, .groups [7, 11]),
    (10, .split 89 [])]

-- Exact component 3^2 * 13^2.
private noncomputable def seed3Part4 : Script :=
  .split 61 [
    (1, .split 31 [
      (2, .split 331 [
        (4, .split 5 []),
        (6, .split 2180921 [])]),
      (4, .groups [5, 11]),
      (6, .split 917087137 [
        (2, .split 43 [])]),
      (10, .split 23 [
        (2, .split 7 [
          (2, .groups [19])]),
        (4, .split 397 []),
        (6, .split 29 [])]),
      (12, .split 42407 []),
      (14, .groups [5, 11])]),
    (2, seed3Part5),
    (4, .split 5 [
      (1, .split 131 [
        (2, .split 17293 []),
        (6, .split 127 []),
        (8, .groups [19])]),
      (2, .groups [31]),
      (4, .groups [11]),
      (6, .groups [131]),
      (8, .groups [19]),
      (9, .groups [11]),
      (10, .groups [131]),
      (12, .groups [131]),
      (13, .groups [29]),
      (14, .groups [11]),
      (16, .groups [131]),
      (18, .groups [131]),
      (20, .groups [31]),
      (21, .groups [23]),
      (22, .groups [131])]),
    (5, .split 7 [
      (4, .split 31 [
        (4, .groups [5]),
        (6, .split 97 [])]),
      (6, .groups [29, 31, 97]),
      (10, .split 31 [
        (4, .groups [5])]),
      (12, .split 31 [
        (4, .groups [5])]),
      (16, .split 31 []),
      (18, .split 31 [])]),
    (6, .split 52379047267 []),
    (9, .groups [5, 11]),
    (10, .split 199 [
      (2, .split 859 [])]),
    (12, .split 187123 []),
    (13, .split 31 [])]

-- Exact component 3^2 * 13^4.
private noncomputable def seed3Part6 : Script :=
  .split 30941 [
    (2, .split 157 [
      (1, .split 79 [
        (2, .split 7 [
          (2, .groups [19, 43, 433]),
          (4, .split 43 [
            (2, .split 433 []),
            (4, .split 433 [])]),
          (6, .split 29 [
            (2, .groups [43, 67]),
            (4, .split 43 [])]),
          (10, .split 43 []),
          (12, .split 43 [])]),
        (4, .split 433 [
          (2, .split 37 [])]),
        (6, .split 281 [])]),
      (2, .split 433 [
        (1, .split 7 [
          (2, .split 19 [
            (4, .groups [31]),
            (6, .groups [31])]),
          (4, .split 31 [
            (2, .split 331 []),
            (4, .groups [5])]),
          (6, .split 29 [
            (2, .split 31 [
              (2, .groups [67])])]),
          (10, .split 31 [])]),
        (2, .split 37 [
          (1, .split 19 [
            (4, .split 151 [])]),
          (4, .split 11 [])]),
        (4, .split 11 [])]),
      (4, .split 11 [
        (2, .groups [7, 19]),
        (4, .groups [5])]),
      (5, .split 7 [
        (2, .split 19 []),
        (4, .split 79 [])]),
      (6, .split 433 [
        (1, .split 7 [])])]),
    (4, .groups [5, 11])]

-- Exact component 3^2 * 13^5.
private noncomputable def seed3Part7 : Script :=
  .split 7 [
    (2, .split 19 [
      (4, .split 61 [
        (4, .groups [5]),
        (6, .split 151 [])]),
      (6, .split 61 [
        (4, .groups [5]),
        (6, .split 157 [])]),
      (10, .split 61 []),
      (12, .split 61 [])]),
    (4, .split 61 [
      (2, .split 97 [
        (4, .groups [11]),
        (6, .split 43 [])]),
      (4, .groups [5]),
      (6, .split 157 [
        (2, .split 2801 [])])]),
    (6, .split 29 [
      (2, .split 61 [
        (2, .split 67 [
          (4, .split 97 []),
          (6, .split 97 [])]),
        (4, .groups [5]),
        (6, .split 67 [
          (2, .groups [31])])]),
      (4, .split 61 [
        (2, .split 97 [
          (4, .groups [11])]),
        (4, .groups [5])]),
      (6, .split 61 [
        (2, .split 97 []),
        (4, .groups [5])]),
      (8, .split 61 [
        (2, .split 67 [])]),
      (10, .groups [23, 61])]),
    (10, .split 61 [
      (2, .split 97 [
        (4, .groups [11])]),
      (4, .groups [5]),
      (6, .split 157 [])]),
    (12, .split 61 [
      (2, .split 97 [
        (4, .groups [11])]),
      (4, .groups [5])]),
    (14, .groups [19, 31, 61]),
    (16, .split 61 [
      (2, .split 97 [])]),
    (18, .split 61 [
      (2, .split 97 [])]),
    (20, .groups [19, 29, 61]),
    (22, .split 47 [])]

-- Exact component 3^2 * 13^8.
private noncomputable def seed3Part8 : Script :=
  .split 61 [
    (1, .split 31 [
      (4, .groups [5, 11]),
      (6, .split 1609669 []),
      (10, .split 23 [])]),
    (4, .split 5 [
      (2, .groups [31]),
      (4, .groups [11]),
      (6, .groups [131]),
      (8, .groups [19]),
      (10, .groups [131]),
      (12, .groups [131]),
      (14, .groups [11])]),
    (6, .split 1609669 [
      (1, .split 5 [
        (2, .groups [31]),
        (4, .groups [11])])]),
    (9, .groups [5, 11])]

-- Exact component 3^2 * 13^10.
private noncomputable def seed3Part9 : Script :=
  .split 23 [
    (2, .split 7 [
      (2, .groups [19]),
      (4, .split 79 [
        (2, .split 43 [
          (2, .split 419 [
            (2, .split 631 [])]),
          (4, .split 419 [])]),
        (4, .split 419 [])]),
      (6, .groups [29, 79, 419]),
      (8, .groups [19]),
      (10, .split 79 [
        (2, .split 43 [])]),
      (12, .split 79 []),
      (14, .groups [19])]),
    (4, .split 419 [
      (2, .split 859 [
        (2, .split 13537 [])])]),
    (6, .split 29 [
      (1, .groups [5]),
      (2, .split 67 [
        (2, .groups [7, 31])]),
      (4, .split 419 []),
      (5, .groups [5])]),
    (8, .groups [7, 19, 79, 419, 859]),
    (10, .split 11 [])]

-- Exact component 3^2 * 13^12.
private noncomputable def seed3Part10 : Script :=
  .split 53 [
    (2, .split 7 [
      (2, .split 19 [
        (2, .split 127 []),
        (4, .split 151 [
          (2, .split 409 [])]),
        (6, .split 409 [])]),
      (4, .split 409 [
        (1, .groups [5]),
        (2, .split 2801 [
          (1, .split 467 [])])]),
      (6, .split 29 [
        (1, .groups [5]),
        (2, .split 67 [
          (2, .groups [31])])]),
      (8, .groups [19, 37]),
      (10, .split 409 [])]),
    (4, .split 11 [
      (2, .groups [7]),
      (4, .groups [5])]),
    (6, .split 29 [
      (1, .split 5 []),
      (2, .split 67 [])])]

-- Exact component 3^2 * 13^13.
private noncomputable def seed3Part11 : Script :=
  .split 7 [
    (2, .split 19 [
      (2, .groups [29, 127]),
      (4, .groups [29, 151]),
      (6, .split 29 [
        (2, .groups [67])])]),
    (4, .split 29 [
      (2, .split 67 [
        (2, .split 31 [
          (2, .split 331 [])])]),
      (4, .split 2801 [])]),
    (6, .split 29 [
      (2, .split 67 [
        (2, .split 31 [
          (2, .split 331 [])])]),
      (4, .split 4733 [])]),
    (8, .groups [19, 29, 37]),
    (10, .split 29 [
      (2, .split 67 [])]),
    (12, .split 29 [])]

-- Exact component 3^2.
private noncomputable def seed3Part1 : Script :=
  .split 13 [
    (1, seed3Part2),
    (2, seed3Part4),
    (4, seed3Part6),
    (5, seed3Part7),
    (6, .split 5229043 [
      (2, .split 31 [
        (2, .split 331 []),
        (4, .groups [5, 11])])]),
    (8, seed3Part8),
    (9, .split 7 [
      (2, .groups [11, 19]),
      (4, .split 11 []),
      (6, .groups [11, 29]),
      (8, .groups [11, 19]),
      (10, .split 11 []),
      (12, .split 11 []),
      (14, .groups [11, 19]),
      (16, .split 11 [])]),
    (10, seed3Part9),
    (12, seed3Part10),
    (13, seed3Part11),
    (14, .split 61 [
      (1, .split 31 [
        (2, .split 331 []),
        (4, .groups [5, 11]),
        (6, .split 4651 [])]),
      (2, .split 97 [
        (1, .split 7 [
          (4, .split 2801 []),
          (6, .split 29 [
            (2, .split 67 [])])]),
        (4, .split 11 [])]),
      (4, .split 5 [
        (1, .split 131 []),
        (2, .groups [31]),
        (4, .groups [11])]),
      (5, .split 7 [])]),
    (16, .split 103 [
      (2, .split 443 [])]),
    (17, .split 7 [
      (4, .split 19 []),
      (6, .groups [19, 29, 61])]),
    (18, .split 12865927 []),
    (20, .split 43 [
      (2, .split 61 [])]),
    (21, .split 7 [
      (2, .groups [19, 23, 419])])]

-- Exact component 3^4 * 11^6.
private noncomputable def seed3Part13 : Script :=
  .split 43 [
    (2, .split 631 [
      (2, .split 307 [
        (2, .split 433 [
          (1, .groups [7, 31, 733]),
          (2, .split 37 [
            (1, .split 19 [
              (4, .split 151 [])]),
            (4, .split 41 [])]),
          (4, .split 733 [])]),
        (4, .split 433 [
          (1, .groups [7, 31, 1051])])]),
      (4, .groups [5]),
      (6, .split 7 [])]),
    (4, .split 45319 [
      (2, .split 127 [
        (2, .split 5419 [])])]),
    (6, .split 7 [
      (2, .groups [19]),
      (4, .split 2801 [
        (1, .split 467 [
          (2, .groups [19])]),
        (2, .groups [37])]),
      (6, .groups [29]),
      (8, .groups [19]),
      (10, .split 1123 [])]),
    (8, .split 19 [
      (2, .split 127 [
        (2, .split 181 [
          (1, .groups [7])])]),
      (4, .split 151 [])]),
    (10, .split 45319 [])]

-- Exact component 3^4.
private noncomputable def seed3Part12 : Script :=
  .split 11 [
    (2, .split 7 [
      (2, .groups [19]),
      (4, .groups [19]),
      (6, .groups [19]),
      (8, .groups [19]),
      (10, .groups [19]),
      (12, .groups [19]),
      (14, .groups [19]),
      (16, .groups [19]),
      (18, .groups [19]),
      (20, .groups [19]),
      (22, .groups [19]),
      (24, .groups [19]),
      (26, .groups [19])]),
    (4, .split 5 [
      (1, .split 3221 [
        (2, .split 10378063 [
          (2, .split 769 [])]),
        (6, .groups [7])])]),
    (6, seed3Part13),
    (8, .split 7 [
      (2, .groups [19]),
      (4, .groups [19]),
      (6, .groups [19]),
      (8, .groups [19]),
      (10, .groups [19]),
      (12, .groups [19]),
      (14, .groups [19]),
      (16, .groups [19]),
      (18, .groups [19])]),
    (10, .split 15797 [
      (1, .split 2633 [
        (2, .split 19 [
          (2, .split 127 [
            (2, .split 5419 [])]),
          (4, .split 151 [])]),
        (4, .split 1717451 [])]),
      (2, .split 1806113 [
        (1, .split 17 [
          (2, .split 307 []),
          (4, .split 17707 [])])])]),
    (12, .split 1093 [
      (1, .split 547 [
        (2, .split 163 [
          (2, .groups [7, 19, 67])]),
        (4, .split 431 [])]),
      (2, .split 398581 [
        (1, .split 17 [
          (2, .split 19 [
            (2, .split 127 [])]),
          (4, .split 19 [])])]),
      (4, .split 31 [])]),
    (14, .groups [5, 7]),
    (16, .split 50544702849929377 []),
    (18, .split 6115909044841454629 []),
    (20, .groups [7, 19, 43]),
    (22, .split 829 [])]

-- Exact component 3^6 * 1093.
private noncomputable def seed3Part15 : Script :=
  .split 547 [
    (2, .split 163 [
      (2, .split 7 [
        (2, .split 19 [
          (2, .split 67 [
            (4, .split 127 [
              (2, .split 613 [])]),
            (6, .split 127 [])]),
          (4, .split 67 [
            (4, .split 151 [])]),
          (6, .split 67 []),
          (8, .split 67 []),
          (10, .split 67 [])]),
        (4, .split 19 [
          (2, .split 67 [
            (2, .split 31 [
              (2, .split 127 [
                (2, .split 331 [])]),
              (4, .groups [5])]),
            (4, .split 127 [])]),
          (4, .split 67 [
            (2, .split 31 [
              (2, .split 151 [])])]),
          (6, .split 67 [
            (2, .split 31 [
              (2, .split 331 [])])]),
          (8, .split 67 [])]),
        (6, .split 19 [
          (2, .split 29 [
            (2, .groups [13]),
            (4, .split 67 [
              (2, .groups [31])])]),
          (4, .split 29 [
            (2, .groups [13])]),
          (6, .split 29 [])]),
        (8, .split 19 [
          (2, .split 37 [
            (2, .split 67 []),
            (4, .groups [11])]),
          (4, .split 37 [
            (2, .split 67 [
              (2, .groups [31])])]),
          (6, .split 37 [])]),
        (10, .split 19 [
          (2, .split 67 [
            (2, .split 31 [
              (2, .split 127 [])])]),
          (4, .split 67 [])]),
        (12, .split 19 [
          (2, .split 67 [
            (2, .split 31 [])])]),
        (14, .split 19 [
          (2, .split 31 [])]),
        (16, .split 19 [])]),
      (4, .split 11 [
        (2, .groups [7, 19]),
        (4, .groups [5, 31]),
        (6, .split 31 [
          (2, .split 43 [])]),
        (8, .groups [7, 19])]),
      (6, .split 613 [
        (2, .split 7 [])]),
      (8, .split 7 [])]),
    (4, .split 431 [
      (2, .split 7 [
        (2, .split 19 [
          (2, .split 67 []),
          (4, .split 67 [])]),
        (4, .split 67 [
          (2, .split 31 [
            (2, .split 331 [])])]),
        (6, .split 29 [
          (2, .split 13 [])]),
        (8, .split 19 [])]),
      (4, .split 5 [
        (2, .split 31 [])])]),
    (6, .split 7 [
      (2, .split 19 [
        (2, .split 29 [
          (2, .groups [13])]),
        (4, .split 29 [])]),
      (4, .split 29 [
        (2, .split 13 [])]),
      (6, .split 29 [])]),
    (8, .split 163 [])]

-- Exact component 3^6 * 1093^2.
private noncomputable def seed3Part16 : Script :=
  .split 398581 [
    (1, .split 17 [
      (2, .split 19 [
        (2, .split 127 [
          (2, .split 307 [
            (2, .split 43 [
              (2, .split 617 [])])]),
          (4, .split 307 [
            (2, .split 43 [])])]),
        (4, .split 151 [
          (2, .split 7 [
            (2, .split 307 [
              (2, .groups [43])]),
            (4, .split 307 [
              (2, .groups [43])]),
            (6, .groups [29]),
            (8, .groups [37])]),
          (4, .groups [5])]),
        (6, .split 307 [
          (2, .split 43 [
            (2, .split 617 [])])]),
        (8, .split 127 [
          (2, .split 307 [])]),
        (10, .split 307 [])]),
      (4, .split 19 [
        (2, .split 127 [
          (2, .split 617 [
            (2, .split 97 [])]),
          (4, .split 617 [])]),
        (4, .split 151 [
          (2, .split 7 [
            (2, .split 617 [
              (2, .split 97 [])]),
            (4, .split 617 []),
            (6, .groups [29])])]),
        (6, .split 617 []),
        (8, .split 127 [])]),
      (6, .split 19 [
        (2, .split 127 [
          (2, .split 617 [])]),
        (4, .split 151 [
          (2, .split 7 [
            (2, .split 617 [])])]),
        (6, .split 617 [])]),
      (8, .split 19 [
        (2, .split 127 [
          (2, .split 307 [])]),
        (4, .split 151 [
          (2, .split 7 [
            (2, .split 307 [])])])]),
      (10, .split 19 [
        (2, .split 127 [])]),
      (12, .split 19 [])]),
    (2, .split 1621 [
      (1, .split 811 [
        (2, .split 31 [
          (2, .split 73 [])])]),
      (2, .split 7 [
        (2, .split 13 [
          (1, .split 19 [
            (2, .groups [127])]),
          (2, .groups [19, 61]),
          (4, .split 19 [])]),
        (4, .split 13 [
          (1, .split 2801 []),
          (2, .split 61 [])]),
        (6, .split 13 [
          (1, .split 29 [])])])])]

-- Exact component 3^6.
private noncomputable def seed3Part14 : Script :=
  .split 1093 [
    (1, seed3Part15),
    (2, seed3Part16),
    (4, .split 11 [
      (2, .groups [7, 19, 31]),
      (4, .groups [5, 31]),
      (6, .split 31 [
        (2, .split 43 [
          (2, .split 331 [])]),
        (4, .groups [5])]),
      (8, .groups [7, 19, 31]),
      (10, .split 31 []),
      (12, .split 31 [])]),
    (5, .split 547 [
      (2, .split 163 [
        (2, .split 7 [
          (2, .split 19 [])])])]),
    (6, .split 7 [
      (2, .split 19 [
        (2, .split 29 [
          (1, .groups [5]),
          (2, .groups [13])])]),
      (4, .split 29 [
        (1, .groups [5]),
        (2, .split 13 [
          (1, .split 67 [])])]),
      (6, .split 29 [])])]

-- Exact component 3^8 * 13.
private noncomputable def seed3Part18 : Script :=
  .split 7 [
    (2, .split 19 [
      (2, .groups [127, 757]),
      (4, .groups [151, 757, 911]),
      (6, .split 701 [
        (2, .split 757 []),
        (4, .groups [5])]),
      (8, .groups [127, 523]),
      (10, .split 757 []),
      (12, .split 599 [
        (2, .split 757 [])]),
      (14, .groups [31])]),
    (4, .split 757 [
      (4, .groups [11]),
      (6, .split 2801 [])]),
    (6, .split 29 [
      (4, .split 757 [
        (4, .groups [11])]),
      (6, .split 757 []),
      (10, .groups [23])]),
    (8, .groups [19, 37]),
    (10, .split 757 [
      (4, .groups [11])]),
    (12, .split 757 [
      (4, .groups [11])]),
    (14, .groups [19, 31]),
    (16, .split 757 []),
    (18, .split 419 []),
    (20, .groups [19, 29]),
    (22, .split 47 []),
    (24, .split 757 [])]

-- Exact component 3^8 * 13^2 * 61^2.
private noncomputable def seed3Part20 : Script :=
  .split 97 [
    (1, .split 7 [
      (2, .groups [19]),
      (4, .split 757 [
        (4, .groups [11])]),
      (6, .groups [29]),
      (8, .groups [19]),
      (10, .split 757 []),
      (12, .split 757 []),
      (14, .groups [19]),
      (16, .split 757 []),
      (18, .split 419 []),
      (20, .groups [19])]),
    (2, .split 757 [
      (1, .split 379 [
        (2, .split 787 [
          (2, .split 37 [
            (2, .groups [7, 67, 151]),
            (4, .split 11 [
              (2, .groups [7])])]),
          (4, .split 3169 [])]),
        (4, .split 11 [
          (2, .groups [7]),
          (4, .groups [5])])]),
      (4, .split 11 [
        (2, .groups [7]),
        (4, .groups [5])])]),
    (4, .split 11 [
      (2, .groups [7]),
      (4, .groups [5]),
      (6, .split 31 [
        (2, .split 43 [
          (2, .split 331 [])]),
        (4, .groups [5])]),
      (8, .groups [7]),
      (10, .split 31 [])]),
    (5, .split 7 [
      (2, .groups [19]),
      (4, .split 67 [
        (2, .groups [31]),
        (4, .split 139 [])]),
      (6, .groups [29]),
      (8, .groups [19]),
      (10, .split 67 [])]),
    (6, .split 43 [
      (2, .split 631 [
        (2, .split 307 [])]),
      (4, .split 757 [])]),
    (8, .split 757 [
      (1, .split 379 [])]),
    (9, .groups [7, 11])]

-- Exact component 3^8 * 13^2.
private noncomputable def seed3Part19 : Script :=
  .split 61 [
    (1, .split 31 [
      (2, .split 331 [
        (2, .split 7 [
          (2, .groups [19]),
          (4, .split 757 [
            (2, .split 2801 [
              (2, .groups [37])]),
            (4, .groups [11])]),
          (6, .groups [29]),
          (8, .groups [19]),
          (10, .groups [757, 1123]),
          (12, .split 757 [
            (2, .split 5233 [])]),
          (14, .groups [19]),
          (16, .split 757 [])]),
        (4, .groups [5]),
        (6, .split 757 [])]),
      (4, .groups [5]),
      (6, .split 757 [
        (2, .split 14713 [
          (2, .split 19 [])]),
        (4, .split 11 [])]),
      (8, .split 331 [
        (2, .split 7 [
          (2, .groups [19]),
          (4, .groups [757, 2801, 3637, 5233])])]),
      (10, .split 23 [
        (2, .groups [7])]),
      (12, .split 757 [])]),
    (2, seed3Part20),
    (4, .split 5 [
      (1, .split 131 [
        (2, .split 757 [
          (2, .split 14713 [
            (2, .groups [19])]),
          (4, .groups [11])]),
        (6, .groups [127])])]),
    (5, .split 7 [
      (2, .groups [19]),
      (4, .groups [31, 97]),
      (6, .groups [29, 31]),
      (8, .groups [19]),
      (10, .groups [31, 97]),
      (12, .groups [31, 97]),
      (14, .groups [19])]),
    (6, .split 757 [
      (1, .split 379 [
        (2, .split 787 [
          (2, .split 37 [
            (2, .split 7 [])])])]),
      (2, .split 14713 [
        (1, .split 7 [
          (2, .groups [19]),
          (4, .split 1051 [])]),
        (2, .split 19 [])])]),
    (8, .split 19 [
      (2, .split 97 [
        (1, .groups [7]),
        (2, .split 127 [])]),
      (4, .split 97 [
        (1, .groups [7]),
        (2, .split 151 [])]),
      (6, .split 97 [])]),
    (9, .groups [5, 11]),
    (10, .split 199 [])]

-- Exact component 3^8 * 13^4.
private noncomputable def seed3Part21 : Script :=
  .split 757 [
    (1, .split 379 [
      (2, .split 61 [
        (2, .split 97 [
          (2, .split 787 [
            (2, .split 37 [
              (2, .groups [7, 67])])]),
          (4, .split 11 [
            (2, .groups [7])])]),
        (4, .groups [5, 131]),
        (6, .split 787 [])]),
      (4, .split 11 [
        (2, .groups [7]),
        (4, .groups [5]),
        (6, .split 41 [])]),
      (6, .split 7 [
        (2, .groups [19, 43])])]),
    (2, .split 14713 [
      (1, .split 7 [
        (2, .split 19 [
          (2, .groups [127]),
          (4, .groups [151]),
          (6, .groups [701]),
          (8, .groups [127])]),
        (4, .split 1051 [
          (2, .split 2801 [])]),
        (6, .split 29 [
          (2, .split 67 [
            (2, .groups [31])]),
          (4, .split 1051 [])]),
        (8, .groups [19, 37]),
        (10, .split 1051 []),
        (12, .split 1051 []),
        (14, .groups [19, 31])]),
      (2, .split 19 [
        (2, .split 127 [
          (2, .split 5419 [])]),
        (4, .split 151 [
          (2, .split 7 [])]),
        (6, .split 701 [
          (1, .split 30941 [])])])]),
    (4, .split 11 [
      (2, .groups [7]),
      (4, .groups [5]),
      (6, .split 43 [])]),
    (5, .split 163 [
      (2, .groups [7, 19, 67, 379])]),
    (6, .split 7 [
      (2, .split 19 [])])]

-- Exact component 3^8 * 13^5.
private noncomputable def seed3Part22 : Script :=
  .split 7 [
    (2, .groups [19, 61]),
    (4, .split 61 [
      (2, .split 97 [
        (2, .split 157 [
          (2, .split 757 [
            (2, .split 2801 [])]),
          (4, .groups [11])]),
        (4, .groups [11]),
        (6, .groups [43, 157])]),
      (4, .groups [5]),
      (6, .split 157 [
        (2, .split 757 [])]),
      (8, .groups [19])]),
    (6, .groups [29, 61, 157]),
    (8, .groups [19, 37]),
    (10, .split 61 [
      (2, .split 97 [
        (2, .split 157 [
          (2, .split 757 [])])]),
      (4, .groups [5])]),
    (12, .split 61 [
      (2, .split 97 [
        (2, .split 157 [])]),
      (4, .groups [5])]),
    (14, .groups [19, 31]),
    (16, .split 61 [
      (2, .split 97 [])]),
    (18, .split 61 []),
    (20, .groups [19, 29])]

-- Exact component 3^8 * 13^6.
private noncomputable def seed3Part23 : Script :=
  .split 757 [
    (1, .split 379 [
      (2, .split 61 [
        (2, .split 97 [
          (2, .split 787 [
            (2, .split 37 [])]),
          (4, .split 11 [])]),
        (4, .groups [5, 131]),
        (6, .split 787 [])]),
      (4, .split 11 [
        (2, .groups [7]),
        (4, .groups [5])])]),
    (2, .split 14713 [
      (1, .split 7 [
        (2, .split 19 [
          (2, .groups [127]),
          (4, .groups [151]),
          (6, .groups [701])]),
        (4, .split 1051 [
          (2, .split 2801 [])]),
        (6, .split 29 [
          (2, .split 67 [
            (2, .groups [31])])]),
        (8, .groups [19, 37]),
        (10, .split 1051 [])]),
      (2, .split 19 [
        (2, .split 127 [
          (2, .split 5419 [])]),
        (4, .split 151 [])])]),
    (4, .split 11 [
      (2, .groups [7]),
      (4, .groups [5])]),
    (5, .split 163 [])]

-- Exact component 3^8 * 13^8.
private noncomputable def seed3Part24 : Script :=
  .split 61 [
    (1, .split 31 [
      (2, .split 331 [
        (2, .split 7 [
          (2, .groups [19]),
          (4, .groups [757, 2801]),
          (6, .groups [29]),
          (8, .groups [19])]),
        (4, .groups [5])]),
      (4, .groups [5]),
      (6, .split 757 [
        (2, .split 14713 [])]),
      (8, .split 331 [])]),
    (2, .split 97 [
      (1, .split 7 [
        (2, .groups [19]),
        (4, .split 757 [
          (2, .split 2801 [])]),
        (6, .groups [29]),
        (8, .groups [19]),
        (10, .split 757 []),
        (12, .split 757 [])]),
      (2, .split 757 [
        (1, .split 379 [
          (2, .split 787 [
            (2, .split 37 [])])]),
        (2, .split 3169 [
          (1, .groups [5]),
          (2, .split 14713 [])])]),
      (4, .split 11 [
        (2, .groups [7]),
        (4, .groups [5])]),
      (5, .split 7 [
        (2, .groups [19]),
        (4, .split 67 [])]),
      (6, .split 43 [])]),
    (4, .groups [5, 131, 757]),
    (5, .split 7 [
      (2, .groups [19]),
      (4, .groups [31, 97]),
      (6, .groups [29, 31]),
      (8, .groups [19])]),
    (6, .split 757 [
      (1, .split 379 [])]),
    (8, .split 19 [])]

-- Exact component 3^8.
private noncomputable def seed3Part17 : Script :=
  .split 13 [
    (1, seed3Part18),
    (2, seed3Part19),
    (4, seed3Part21),
    (5, seed3Part22),
    (6, seed3Part23),
    (8, seed3Part24),
    (9, .groups [7, 11]),
    (10, .split 23 [
      (2, .split 7 [
        (2, .groups [19]),
        (4, .groups [79]),
        (6, .groups [29]),
        (8, .groups [19]),
        (10, .groups [79])]),
      (4, .split 419 [
        (2, .split 757 [
          (1, .split 379 [])])]),
      (6, .split 29 [
        (1, .groups [5]),
        (2, .split 67 [])]),
      (8, .groups [7, 19])]),
    (12, .split 53 [
      (1, .split 757 [
        (2, .split 14713 [])]),
      (2, .split 7 [
        (2, .groups [19]),
        (4, .split 409 [
          (1, .groups [5])]),
        (6, .groups [29, 409])]),
      (4, .split 11 [
        (2, .groups [7])]),
      (5, .split 7 [
        (2, .groups [19])])]),
    (13, .split 7 [
      (2, .groups [19, 29]),
      (4, .split 29 [
        (2, .split 67 [
          (2, .groups [31])])]),
      (6, .split 29 [
        (2, .split 67 [
          (2, .groups [31])])]),
      (8, .groups [19, 29])]),
    (14, .split 61 [
      (1, .split 31 [
        (2, .split 331 []),
        (4, .groups [5])]),
      (2, .split 97 [
        (1, .split 7 [
          (2, .groups [19]),
          (4, .split 757 [])]),
        (2, .split 757 [
          (1, .split 379 [])])]),
      (4, .groups [5, 131, 757])]),
    (16, .split 103 [
      (2, .split 443 [])]),
    (17, .groups [7, 19, 61, 157, 271]),
    (18, .split 757 [
      (1, .split 379 [])])]

-- Exact component 3^10 * 23^2 * 7^4.
private noncomputable def seed3Part27 : Script :=
  .split 79 [
    (2, .split 43 [
      (2, .split 631 [
        (2, .split 307 [
          (2, .split 433 [
            (1, .split 31 [
              (2, .split 331 [])]),
            (2, .split 37 [
              (1, .groups [19])])])]),
        (4, .groups [5])]),
      (4, .split 2801 [
        (1, .split 467 [
          (2, .groups [19])]),
        (2, .split 37 [
          (1, .groups [19]),
          (2, .split 67 [])])]),
      (6, .split 2801 [
        (1, .split 467 []),
        (2, .split 37 [])]),
      (8, .groups [19, 181])]),
    (4, .split 2801 [
      (1, .split 467 [
        (2, .split 19 [
          (2, .split 127 [])])]),
      (2, .split 37 [
        (1, .groups [19]),
        (2, .split 43 [])])]),
    (6, .split 281 [
      (1, .split 47 [
        (2, .split 37 [])]),
      (2, .split 109 [
        (1, .groups [5])])]),
    (8, .split 43 [])]

-- Exact component 3^10 * 23^2.
private noncomputable def seed3Part26 : Script :=
  .split 7 [
    (2, .split 19 [
      (2, .split 79 [
        (4, .split 127 [
          (2, .split 3851 [
            (2, .groups [13])]),
          (4, .split 3851 [])]),
        (6, .split 127 [
          (2, .split 281 [
            (1, .groups [47])])])]),
      (4, .split 79 [
        (4, .split 151 [
          (2, .split 911 [])]),
        (6, .split 151 [])]),
      (6, .split 79 [
        (4, .split 701 [
          (1, .groups [13])])]),
      (8, .split 79 [
        (4, .split 127 [])]),
      (10, .split 79 []),
      (12, .split 79 [])]),
    (4, seed3Part27),
    (6, .split 29 [
      (1, .groups [5]),
      (2, .groups [13]),
      (4, .split 79 [
        (2, .split 43 [
          (2, .split 631 [
            (2, .split 307 [])]),
          (4, .split 3851 [])]),
        (4, .split 3851 [])]),
      (5, .groups [5]),
      (6, .split 79 [
        (2, .split 43 [
          (2, .split 631 [])])]),
      (8, .groups [13]),
      (9, .groups [5]),
      (10, .split 79 [])]),
    (8, .groups [19, 37, 79]),
    (10, .split 79 [
      (2, .split 43 [
        (2, .split 631 [
          (2, .split 307 [])]),
        (4, .split 1123 [])]),
      (4, .split 1123 [])]),
    (12, .split 79 [
      (2, .split 43 [
        (2, .split 631 [
          (2, .split 307 [])]),
        (4, .split 3851 [])]),
      (4, .split 3851 [])]),
    (14, .groups [19, 31, 79]),
    (16, .split 79 [
      (2, .split 43 [
        (2, .split 631 [])])]),
    (18, .split 79 [
      (2, .split 43 [])]),
    (20, .groups [19, 29, 79])]

-- Exact component 3^10 * 23^4.
private noncomputable def seed3Part28 : Script :=
  .split 3851 [
    (2, .split 13 [
      (1, .split 7 [
        (2, .groups [19]),
        (4, .split 2801 [
          (2, .groups [37])]),
        (6, .groups [29]),
        (8, .groups [19]),
        (10, .split 1123 [])]),
      (2, .split 61 [
        (1, .split 31 [
          (2, .split 331 [
            (2, .groups [7])]),
          (4, .groups [5])]),
        (2, .split 97 [
          (1, .split 7 []),
          (2, .split 3169 [
            (1, .groups [5])])]),
        (4, .groups [5]),
        (5, .groups [7, 31])]),
      (4, .split 30941 [
        (1, .split 191 [
          (2, .groups [7, 31])])]),
      (5, .split 7 [
        (2, .groups [19]),
        (4, .groups [61]),
        (6, .groups [29])]),
      (6, .split 292561 [
        (1, .split 19 [])]),
      (8, .split 61 [
        (1, .split 31 []),
        (2, .split 97 [])]),
      (9, .groups [7, 11]),
      (10, .split 419 [])]),
    (4, .split 5 [
      (1, .split 292561 []),
      (2, .groups [31]),
      (4, .groups [11]),
      (5, .groups [7])])]

-- Exact component 3^10 * 23^6.
private noncomputable def seed3Part29 : Script :=
  .split 29 [
    (1, .split 5 []),
    (2, .split 13 [
      (1, .groups [7, 67]),
      (2, .split 61 [
        (1, .split 31 [
          (2, .split 67 [
            (2, .groups [7])]),
          (4, .groups [5]),
          (6, .split 67 [])]),
        (2, .split 67 [
          (2, .groups [7]),
          (4, .split 97 [])]),
        (4, .groups [5]),
        (5, .groups [7])]),
      (4, .split 67 [
        (2, .groups [7]),
        (4, .split 761 [])]),
      (5, .groups [7]),
      (6, .split 67 [
        (2, .groups [7])]),
      (8, .split 61 [
        (1, .split 31 []),
        (2, .split 67 [])]),
      (9, .groups [7]),
      (10, .split 67 [])]),
    (4, .split 3851 [
      (2, .split 13 [
        (1, .split 7 []),
        (2, .split 61 [])])]),
    (5, .groups [5, 13]),
    (6, .split 7 [
      (2, .split 19 [
        (2, .groups [127])]),
      (4, .split 2801 [
        (1, .split 467 [])]),
      (6, .split 3851 [])]),
    (8, .split 13 [
      (1, .groups [7, 67]),
      (2, .split 61 [])]),
    (9, .groups [5, 11])]

-- Exact component 3^10.
private noncomputable def seed3Part25 : Script :=
  .split 23 [
    (2, seed3Part26),
    (4, seed3Part28),
    (6, seed3Part29),
    (8, .split 7 [
      (2, .split 19 [
        (2, .split 79 [
          (4, .split 127 [])]),
        (4, .split 79 []),
        (6, .split 79 []),
        (8, .split 79 [])]),
      (4, .split 19 [
        (2, .split 79 [
          (2, .groups [43])]),
        (4, .split 79 [
          (2, .groups [43])])]),
      (6, .groups [19, 29, 79]),
      (8, .groups [19, 37, 79]),
      (10, .split 19 [
        (2, .split 79 [])]),
      (12, .split 19 [])]),
    (10, .split 11 [
      (2, .groups [7, 19]),
      (4, .groups [5]),
      (6, .split 43 [])]),
    (12, .split 3851 []),
    (14, .split 7 [
      (2, .split 19 [])])]

-- Exact component 3^12.
private noncomputable def seed3Part30 : Script :=
  .split 797161 [
    (1, .split 398581 [
      (2, .split 1621 [
        (2, .split 7 [
          (2, .split 13 [
            (2, .groups [19, 61])]),
          (4, .split 13 [])])])]),
    (2, .split 61 [
      (1, .split 31 [
        (2, .split 151 [
          (2, .split 7 [
            (2, .split 19 [
              (2, .split 127 []),
              (4, .split 331 [])]),
            (4, .split 331 []),
            (6, .split 29 [])]),
          (4, .split 5 [])]),
        (4, .groups [5, 11]),
        (6, .split 151 [])]),
      (2, .split 13 [
        (1, .split 7 [
          (2, .groups [19]),
          (4, .split 97 [
            (2, .split 151 [])]),
          (6, .groups [29, 97]),
          (8, .groups [19])]),
        (2, .split 97 [
          (1, .split 7 [
            (2, .groups [19]),
            (4, .split 151 [
              (2, .split 1093 [])]),
            (6, .groups [29]),
            (8, .groups [19])]),
          (2, .split 151 [
            (2, .split 7 [
              (2, .groups [19])])]),
          (4, .split 11 [])]),
        (4, .split 97 [
          (1, .split 7 [
            (2, .groups [19]),
            (4, .split 151 [])]),
          (2, .split 151 [])]),
        (5, .split 7 [
          (2, .groups [19]),
          (4, .split 97 [])]),
        (6, .split 97 [
          (1, .split 7 [
            (2, .groups [19])])]),
        (8, .split 97 [
          (1, .split 7 [])])]),
      (4, .split 5 [
        (1, .split 131 [
          (2, .split 151 [])]),
        (2, .split 31 [
          (2, .split 131 [])]),
        (4, .groups [11]),
        (5, .groups [7]),
        (6, .split 131 [])]),
      (5, .split 7 [
        (2, .groups [13, 19])]),
      (6, .split 151 [])])]

-- Exact component 3^14 * 11^6.
private noncomputable def seed3Part32 : Script :=
  .split 13 [
    (1, .groups [7]),
    (2, .split 43 [
      (2, .split 61 [
        (1, .split 31 [
          (2, .split 331 [
            (2, .groups [7])]),
          (4, .groups [5]),
          (6, .split 631 [])]),
        (2, .split 97 [
          (1, .groups [7]),
          (2, .split 631 [
            (2, .split 307 [])]),
          (4, .split 31 [])]),
        (4, .groups [5]),
        (5, .groups [7])]),
      (4, .split 61 [
        (1, .split 31 [
          (2, .split 331 []),
          (4, .groups [5])]),
        (2, .split 97 [
          (1, .groups [7]),
          (2, .split 3169 [])])]),
      (6, .groups [7])]),
    (4, .split 43 [
      (2, .split 631 [
        (2, .split 307 [
          (2, .split 433 [])])]),
      (4, .split 4561 [
        (1, .split 2281 [])]),
      (6, .groups [7])]),
    (5, .groups [7]),
    (6, .split 43 [
      (2, .split 631 [
        (2, .split 307 [])]),
      (4, .split 4561 [])]),
    (8, .split 43 [
      (2, .split 61 [
        (1, .split 31 [
          (2, .split 331 [])]),
        (2, .split 97 [
          (1, .groups [7])])])]),
    (9, .groups [7]),
    (10, .split 23 [
      (2, .groups [7])]),
    (12, .split 43 [])]

-- Exact component 3^14.
private noncomputable def seed3Part31 : Script :=
  .split 11 [
    (2, .groups [7, 13]),
    (4, .groups [5, 13]),
    (6, seed3Part32),
    (8, .groups [7, 13]),
    (10, .split 13 [
      (1, .groups [7]),
      (2, .split 61 [
        (1, .split 31 [
          (2, .split 331 [
            (2, .groups [7])]),
          (4, .groups [5])]),
        (2, .split 97 [
          (1, .groups [7]),
          (2, .split 3169 [
            (1, .groups [5])])]),
        (4, .groups [5]),
        (5, .groups [7])]),
      (4, .split 4561 [
        (1, .split 2281 [])]),
      (5, .groups [7]),
      (6, .split 4561 [
        (1, .split 2281 [])]),
      (8, .split 61 [
        (1, .split 31 [])]),
      (9, .groups [7])]),
    (12, .split 13 [
      (1, .groups [7]),
      (2, .split 61 [
        (1, .split 31 [
          (2, .split 331 [])]),
        (2, .split 97 [
          (1, .groups [7]),
          (2, .split 1093 [])])]),
      (4, .split 1093 [
        (1, .split 547 [])]),
      (5, .groups [7]),
      (6, .split 1093 [])]),
    (14, .groups [5, 7]),
    (16, .split 13 [
      (1, .groups [7]),
      (2, .split 61 [
        (1, .split 31 [])])]),
    (18, .split 13 [
      (1, .groups [7])])]

-- Exact component 3^16.
private noncomputable def seed3Part33 : Script :=
  .split 1871 [
    (2, .split 7 [
      (2, .split 19 [
        (2, .split 127 [
          (2, .split 157 [
            (1, .split 79 []),
            (2, .split 3187 [])]),
          (4, .split 157 [
            (1, .split 79 [])])]),
        (4, .split 151 [
          (2, .split 157 [
            (1, .split 79 []),
            (2, .split 911 [])])]),
        (6, .split 157 [
          (1, .split 79 []),
          (2, .split 701 [
            (1, .groups [13])])]),
        (8, .split 127 [])]),
      (4, .split 157 [
        (1, .split 79 [
          (2, .split 43 [
            (2, .split 631 [
              (2, .split 307 [])]),
            (4, .split 2801 [])]),
          (4, .split 2801 [])]),
        (2, .split 2801 [
          (1, .split 467 [
            (2, .split 19 [])]),
          (2, .split 37 [
            (1, .split 19 [])])]),
        (4, .split 11 [
          (2, .groups [19])]),
        (5, .split 79 [])]),
      (6, .split 29 [
        (1, .groups [5]),
        (2, .split 13 [
          (1, .split 67 [
            (2, .groups [31])]),
          (2, .groups [61, 67]),
          (4, .groups [67, 157]),
          (5, .groups [61, 67])]),
        (4, .split 157 [
          (1, .split 79 [])]),
        (5, .groups [5]),
        (6, .split 157 [])]),
      (8, .split 19 [
        (2, .split 37 [
          (1, .split 127 [
            (2, .split 157 [])]),
          (2, .split 67 [
            (2, .groups [31, 127])])]),
        (4, .split 37 [
          (1, .split 151 []),
          (2, .split 67 [])])]),
      (10, .split 157 [
        (1, .split 79 [
          (2, .split 43 [])]),
        (2, .split 1123 [])]),
      (12, .split 157 [
        (1, .split 79 [])]),
      (14, .split 19 [])]),
    (4, .split 5 [
      (1, .split 71 [
        (2, .split 151 [
          (2, .groups [7])])]),
      (2, .split 31 [
        (2, .split 71 [])]),
      (4, .groups [11]),
      (5, .groups [7]),
      (6, .split 71 []),
      (8, .groups [19, 31]),
      (9, .groups [11])])]

-- Exact component 3^18.
private noncomputable def seed3Part34 : Script :=
  .split 1597 [
    (1, .split 17 [
      (2, .split 47 [
        (2, .split 37 [
          (2, .split 7 [
            (2, .groups [19]),
            (4, .groups [61, 67]),
            (6, .groups [29]),
            (8, .groups [19]),
            (10, .groups [61, 67])]),
          (4, .split 11 [
            (2, .groups [7]),
            (4, .groups [5])]),
          (6, .split 61 [])]),
        (4, .split 11 [
          (2, .groups [7]),
          (4, .groups [5]),
          (6, .split 31 [])]),
        (6, .split 43 [
          (2, .split 307 [])]),
        (8, .split 19 [])]),
      (4, .split 47 [
        (2, .split 37 [
          (2, .split 7 [
            (2, .groups [19]),
            (4, .groups [61, 67]),
            (6, .groups [29]),
            (8, .groups [19])]),
          (4, .split 11 [
            (2, .groups [7])])]),
        (4, .split 11 [
          (2, .groups [7]),
          (4, .groups [5])]),
        (6, .split 43 [])]),
      (6, .split 47 [
        (2, .split 37 [
          (2, .split 7 [
            (2, .groups [19]),
            (4, .groups [61, 67])]),
          (4, .split 11 [])]),
        (4, .split 11 [
          (2, .groups [7])])]),
      (8, .split 19 [
        (2, .split 47 [
          (2, .split 37 [])]),
        (4, .split 47 [])]),
      (10, .split 47 [
        (2, .split 37 [])]),
      (12, .split 47 [])]),
    (2, .split 43 [
      (2, .split 73 [
        (1, .split 37 [
          (2, .split 7 [
            (2, .groups [19, 67, 271, 631]),
            (4, .split 67 [
              (2, .split 31 [])]),
            (6, .split 29 []),
            (8, .groups [19, 67, 271])]),
          (4, .split 11 [
            (2, .groups [7])]),
          (6, .split 71 [])]),
        (2, .split 271 [
          (2, .split 631 [])]),
        (4, .split 271 []),
        (5, .split 7 [
          (2, .split 19 [])])]),
      (4, .split 73 [
        (1, .split 37 [
          (2, .split 7 [
            (2, .split 19 [
              (2, .groups [67, 127])]),
            (4, .split 67 [])])]),
        (2, .split 271 [
          (2, .split 1801 [])])]),
      (6, .split 7 [
        (2, .split 19 [
          (2, .split 73 [])])])]),
    (4, .split 31 [
      (2, .split 331 [])]),
    (5, .split 17 [
      (2, .split 43 [])])]

-- Exact component 3^20 * 13.
private noncomputable def seed3Part36 : Script :=
  .split 7 [
    (2, .split 19 [
      (2, .groups [127, 1093]),
      (4, .groups [151, 911, 1093]),
      (6, .split 701 [
        (2, .split 1093 [])]),
      (8, .groups [127, 523]),
      (10, .split 1093 [])]),
    (4, .split 1093 [
      (2, .split 2801 [
        (2, .split 37 [
          (2, .groups [43, 67])])]),
      (4, .groups [11])]),
    (6, .split 29 [
      (4, .split 1093 [
        (2, .split 4733 [])]),
      (6, .split 1093 [])]),
    (8, .groups [19, 37]),
    (10, .split 1093 [
      (2, .split 1123 [])]),
    (12, .split 1093 [
      (2, .split 368089 [])]),
    (14, .groups [19, 31]),
    (16, .split 1093 []),
    (18, .split 419 [])]

-- Exact component 3^20 * 13^2.
private noncomputable def seed3Part37 : Script :=
  .split 61 [
    (1, .split 31 [
      (2, .split 331 [
        (2, .split 7 [
          (2, .groups [19]),
          (4, .split 1093 [
            (2, .split 2801 [])]),
          (6, .groups [29]),
          (8, .groups [19])]),
        (4, .groups [5])]),
      (4, .groups [5]),
      (6, .split 1093 [
        (2, .split 368089 [])]),
      (8, .split 331 [])]),
    (2, .split 97 [
      (1, .split 7 [
        (2, .groups [19]),
        (4, .split 1093 [
          (2, .split 2801 [])]),
        (6, .groups [29]),
        (8, .groups [19]),
        (10, .split 1093 []),
        (12, .split 1093 []),
        (14, .groups [19])]),
      (2, .split 1093 [
        (1, .split 547 [
          (2, .split 163 [
            (2, .groups [7, 19])])]),
        (2, .split 3169 [
          (1, .groups [5])])]),
      (4, .split 11 [
        (2, .groups [7]),
        (4, .groups [5])]),
      (5, .split 7 [
        (2, .groups [19]),
        (4, .split 67 [])]),
      (6, .split 43 [])]),
    (4, .split 5 [
      (1, .split 131 [
        (2, .split 1093 [
          (2, .split 17293 [])])])]),
    (5, .split 7 [
      (2, .groups [19]),
      (4, .groups [31, 97]),
      (6, .groups [29, 31]),
      (8, .groups [19])]),
    (6, .split 1093 [
      (1, .split 547 [])]),
    (8, .split 19 [])]

-- Exact component 3^20.
private noncomputable def seed3Part35 : Script :=
  .split 13 [
    (1, seed3Part36),
    (2, seed3Part37),
    (4, .split 1093 [
      (1, .split 547 [
        (2, .split 163 [
          (2, .groups [7, 19, 67])]),
        (4, .split 431 [])]),
      (2, .split 30941 [
        (1, .split 191 [
          (2, .split 7 [
            (2, .groups [19]),
            (4, .split 31 [])])]),
        (2, .split 157 [])]),
      (4, .split 11 [])]),
    (5, .split 7 [
      (2, .groups [19, 61]),
      (4, .split 61 [
        (2, .split 97 [
          (2, .split 157 [
            (2, .split 1093 [])])]),
        (4, .groups [5])]),
      (6, .groups [29, 61, 157]),
      (8, .groups [19, 37]),
      (10, .split 61 [
        (2, .split 97 [])]),
      (12, .split 61 [])]),
    (6, .split 1093 [
      (1, .split 547 [
        (2, .split 163 [
          (2, .groups [7, 19, 67])])]),
      (2, .split 368089 [
        (1, .split 5 [])])]),
    (8, .split 61 [
      (1, .split 31 [
        (2, .split 331 [
          (2, .split 7 [
            (2, .groups [19])])]),
        (4, .groups [5])]),
      (2, .split 97 [
        (1, .split 7 [
          (2, .groups [19]),
          (4, .split 1093 []),
          (6, .groups [29])]),
        (2, .split 1093 [
          (1, .split 547 [])])]),
      (4, .split 5 [
        (1, .split 131 [])]),
      (5, .split 7 [])]),
    (9, .groups [7, 11]),
    (10, .split 23 [
      (2, .split 7 [
        (2, .groups [19])])]),
    (12, .split 53 [
      (1, .split 1093 [])]),
    (13, .split 7 [
      (2, .groups [19, 29])]),
    (14, .split 61 [])]

-- Exact component 3^22.
private noncomputable def seed3Part38 : Script :=
  .split 47 [
    (2, .split 37 [
      (1, .split 19 [
        (2, .split 61 [
          (2, .split 13 [
            (2, .split 97 [
              (2, .split 127 [
                (2, .split 3169 [])])]),
            (4, .split 97 [
              (2, .split 127 [])]),
            (6, .split 97 []),
            (8, .split 97 [])]),
          (4, .groups [5])]),
        (4, .split 61 [
          (2, .split 13 [
            (2, .split 97 [
              (2, .split 151 [])]),
            (4, .split 97 [])]),
          (4, .groups [5])]),
        (6, .split 61 [
          (2, .split 13 [
            (2, .split 97 [])])]),
        (8, .split 61 [])]),
      (2, .split 7 [
        (2, .split 19 [
          (2, .groups [61, 67, 127]),
          (4, .groups [61, 67, 151]),
          (6, .split 61 [
            (1, .groups [31])])]),
        (4, .split 61 [
          (1, .split 31 [
            (2, .split 67 [
              (2, .split 331 [
                (2, .split 2801 [])])]),
            (4, .groups [5])]),
          (2, .groups [13]),
          (4, .groups [5])]),
        (6, .split 29 [
          (1, .groups [5]),
          (2, .groups [13])]),
        (8, .split 19 [
          (2, .groups [61, 67]),
          (4, .groups [61, 67])]),
        (10, .split 61 [
          (1, .split 31 [])]),
        (12, .split 61 [])]),
      (4, .split 11 [
        (2, .groups [7, 19]),
        (4, .groups [5]),
        (6, .split 41 [
          (1, .groups [7])])]),
      (5, .groups [7, 19, 31, 43]),
      (6, .split 61 [
        (1, .split 31 [
          (2, .split 71 [])]),
        (2, .split 13 [
          (1, .groups [7, 71, 97]),
          (2, .split 71 [])])]),
      (8, .split 7 [])]),
    (4, .split 11 [
      (2, .groups [7, 19]),
      (4, .groups [5]),
      (6, .split 31 [
        (2, .split 43 [])]),
      (8, .groups [7, 19])]),
    (6, .split 43 [
      (2, .split 631 [])]),
    (8, .split 19 [
      (2, .split 37 [
        (1, .split 61 [])])])]

-- Exact component 3^24.
private noncomputable def seed3Part39 : Script :=
  .split 11 [
    (2, .split 7 [
      (2, .groups [19]),
      (4, .groups [19]),
      (6, .groups [19]),
      (8, .groups [19]),
      (10, .groups [19]),
      (12, .groups [19]),
      (14, .groups [19])]),
    (4, .split 5 [
      (1, .split 3221 [
        (2, .split 8951 [])])]),
    (6, .split 43 [
      (2, .split 631 [
        (2, .split 307 [])]),
      (4, .split 8951 [])]),
    (8, .split 7 [
      (2, .groups [19]),
      (4, .groups [19]),
      (6, .groups [19]),
      (8, .groups [19])]),
    (10, .split 8951 []),
    (12, .split 1093 [
      (1, .split 547 [])])]

-- Exact component 3^26.
private noncomputable def seed3Part40 : Script :=
  .split 13 [
    (1, .split 7 [
      (2, .groups [19, 109, 433]),
      (4, .split 109 [
        (2, .split 433 [
          (2, .split 37 [
            (2, .split 67 [])])]),
        (4, .split 31 [])]),
      (6, .split 29 [
        (4, .split 109 [])]),
      (8, .groups [19, 37]),
      (10, .split 109 [
        (2, .split 433 [])]),
      (12, .split 109 []),
      (14, .groups [19, 31])]),
    (2, .split 61 [
      (1, .split 31 [
        (2, .split 109 [
          (2, .split 7 []),
          (4, .split 191 [])]),
        (4, .groups [5]),
        (6, .split 109 [])]),
      (2, .split 97 [
        (1, .split 7 [
          (2, .groups [19]),
          (4, .split 109 [
            (2, .split 433 [])]),
          (6, .groups [29]),
          (8, .groups [19]),
          (10, .split 109 [])]),
        (2, .split 109 [
          (1, .groups [5]),
          (2, .split 7 [
            (2, .groups [19]),
            (4, .split 433 [])])]),
        (4, .split 11 [
          (2, .groups [7])]),
        (5, .split 7 [])]),
      (4, .groups [5, 109, 131]),
      (5, .split 7 [
        (2, .groups [19]),
        (4, .groups [31, 97])]),
      (6, .split 109 [
        (1, .groups [5, 11])])]),
    (4, .split 109 [
      (1, .groups [5, 11]),
      (2, .split 7 [
        (2, .groups [19]),
        (4, .split 433 [
          (1, .split 31 [
            (2, .split 331 [])])]),
        (6, .split 29 [
          (1, .groups [5])])]),
      (4, .split 31 [])]),
    (5, .split 7 [
      (2, .groups [19, 61]),
      (4, .split 61 [
        (2, .split 97 [
          (2, .split 109 [])])]),
      (6, .groups [29, 61, 109]),
      (8, .groups [19, 37])]),
    (6, .split 109 [
      (1, .groups [5, 11]),
      (2, .split 7 [
        (2, .groups [19]),
        (4, .split 433 [])])]),
    (8, .split 61 [
      (1, .split 31 [
        (2, .split 109 [])]),
      (2, .split 97 [
        (1, .split 7 [
          (2, .groups [19])])])]),
    (9, .groups [7, 11]),
    (10, .split 23 [])]

-- Exact component 3^28.
private noncomputable def seed3Part41 : Script :=
  .split 59 [
    (2, .split 3541 [
      (1, .split 7 [
        (2, .groups [11, 19]),
        (4, .groups [11, 23]),
        (6, .groups [11, 23]),
        (8, .groups [11, 19])]),
      (2, .split 19 [
        (2, .split 37 [
          (2, .split 7 [])])])]),
    (4, .split 11 [
      (2, .groups [7, 19]),
      (4, .groups [5])]),
    (6, .split 43 [])]

-- Exact component 3^30.
private noncomputable def seed3Part42 : Script :=
  .split 683 [
    (2, .split 7 [
      (2, .split 19 [
        (2, .split 127 [
          (2, .split 5419 [])]),
        (4, .split 151 [])]),
      (4, .split 2801 [
        (1, .split 467 [])]),
      (6, .split 29 [
        (1, .groups [5])]),
      (8, .split 19 [])]),
    (4, .split 1151 [])]

-- Exact component 3^32.
private noncomputable def seed3Part43 : Script :=
  .split 13 [
    (1, .split 7 [
      (2, .groups [19, 23]),
      (4, .split 23 [
        (2, .split 79 [
          (2, .groups [43])]),
        (4, .split 2801 [])]),
      (6, .groups [23, 29]),
      (8, .groups [19, 23]),
      (10, .split 23 [])]),
    (2, .split 23 [
      (2, .split 7 [
        (2, .groups [19]),
        (4, .groups [61]),
        (6, .groups [29]),
        (8, .groups [19])]),
      (4, .split 61 [
        (1, .split 31 [
          (2, .split 331 [])]),
        (2, .split 97 [
          (1, .split 7 [])])]),
      (6, .split 29 [
        (1, .groups [5])])]),
    (4, .split 23 [
      (2, .split 7 [
        (2, .groups [19]),
        (4, .groups [79])]),
      (4, .split 3851 [])]),
    (5, .split 7 [
      (2, .groups [19, 23]),
      (4, .groups [23, 61]),
      (6, .groups [23, 29])]),
    (6, .split 23 [
      (2, .split 7 [
        (2, .groups [19])])]),
    (8, .split 23 []),
    (9, .groups [7, 11])]

-- Exact component 3^38.
private noncomputable def seed3Part44 : Script :=
  .split 13 [
    (2, .split 61 [
      (1, .split 31 [
        (2, .split 313 [])])]),
    (4, .split 313 [
      (1, .split 157 [])]),
    (5, .split 7 [
      (2, .groups [19, 61])]),
    (6, .split 313 [
      (1, .split 157 [])])]

private noncomputable def seed3Script : Script :=
  .split 3 [
    (2, seed3Part1),
    (4, seed3Part12),
    (6, seed3Part14),
    (8, seed3Part17),
    (10, seed3Part25),
    (12, seed3Part30),
    (14, seed3Part31),
    (16, seed3Part33),
    (18, seed3Part34),
    (20, seed3Part35),
    (22, seed3Part38),
    (24, seed3Part39),
    (26, seed3Part40),
    (28, seed3Part41),
    (30, seed3Part42),
    (32, seed3Part43),
    (34, .split 11 [
      (2, .groups [7, 19, 71]),
      (4, .groups [5, 71]),
      (6, .split 43 [
        (2, .split 71 [])]),
      (8, .groups [7, 19, 71])]),
    (36, .split 13097927 []),
    (38, seed3Part44),
    (40, .split 83 [
      (2, .split 19 [
        (2, .split 127 [])])]),
    (42, .split 431 [
      (2, .split 7 [])]),
    (44, .split 11 [
      (2, .groups [7, 13]),
      (4, .groups [5, 13])]),
    (46, .split 1223 []),
    (48, .split 491 []),
    (50, .split 13 [
      (1, .split 7 [])]),
    (52, .split 107 [])]

-- Exact component 5^2 * 31^4.
private noncomputable def seed5Part2 : Script :=
  .split 11 [
    (2, .split 7 [
      (4, .split 19 [
        (4, .split 151 [
          (4, .split 911 [])]),
        (6, .split 701 [
          (2, .split 2801 [])]),
        (10, .split 2801 [])]),
      (6, .split 19 [
        (4, .split 29 [
          (2, .split 13 [
            (1, .split 67 []),
            (4, .split 67 [])]),
          (4, .split 151 []),
          (6, .split 151 [])]),
        (6, .split 29 [
          (2, .split 13 [
            (1, .split 67 [])]),
          (4, .split 701 [])]),
        (10, .split 29 [])]),
      (10, .split 19 [
        (4, .split 151 []),
        (6, .split 701 [])]),
      (12, .split 19 [
        (4, .split 151 []),
        (6, .split 701 [])]),
      (16, .split 19 []),
      (18, .split 19 [])]),
    (4, .split 3221 [
      (2, .split 17351 [
        (2, .split 13 [
          (1, .split 7 [])])])]),
    (6, .split 43 [
      (4, .split 17351 [
        (2, .split 13 [
          (1, .split 7 [])])]),
      (6, .split 7 [
        (4, .split 2801 [])])]),
    (8, .split 7 [
      (4, .split 19 [
        (4, .split 151 []),
        (6, .split 701 [])]),
      (6, .split 19 [
        (4, .split 29 [])]),
      (10, .split 19 []),
      (12, .split 19 [])]),
    (10, .split 15797 [
      (2, .split 17351 [])]),
    (12, .split 1093 [
      (1, .split 547 [])]),
    (14, .split 7 [
      (4, .split 19 []),
      (6, .split 19 [])]),
    (16, .split 17351 []),
    (18, .split 17351 [])]

-- Exact component 5^2.
private noncomputable def seed5Part1 : Script :=
  .split 31 [
    (4, seed5Part2),
    (6, .split 917087137 [
      (1, .split 11 [
        (2, .split 7 [
          (4, .split 19 [
            (4, .split 151 [])]),
          (6, .split 19 [
            (4, .split 29 [])]),
          (10, .split 19 [])]),
        (4, .split 1451 [
          (2, .split 7 [])]),
        (6, .split 43 []),
        (8, .split 7 [
          (4, .split 19 [])]),
        (10, .split 1451 [])])]),
    (10, .split 23 [
      (2, .split 7 [
        (4, .split 79 []),
        (6, .split 29 [
          (2, .split 13 [
            (1, .split 67 [])])])]),
      (4, .split 397 [
        (1, .split 199 [])]),
      (6, .split 29 [])]),
    (12, .split 42407 []),
    (16, .split 751670559138758105956097 [])]

-- Exact component 5^4 * 11^2.
private noncomputable def seed5Part4 : Script :=
  .split 7 [
    (4, .split 19 [
      (4, .split 71 [
        (2, .split 151 [
          (4, .split 911 [])]),
        (4, .split 151 [
          (4, .split 211 [])]),
        (6, .split 151 [])]),
      (6, .split 71 [
        (2, .split 701 [
          (2, .split 2801 [])]),
        (4, .split 211 []),
        (6, .split 701 [])]),
      (10, .split 71 [
        (2, .split 2801 [])]),
      (12, .split 71 [
        (2, .split 599 [])])]),
    (6, .split 19 [
      (4, .split 29 [
        (2, .split 13 [
          (1, .split 67 [
            (4, .split 71 [
              (2, .split 151 [])])]),
          (4, .split 67 []),
          (6, .split 67 []),
          (9, .split 67 [])]),
        (4, .split 71 [
          (2, .split 151 []),
          (4, .split 151 [])]),
        (6, .split 71 [
          (2, .split 151 [])]),
        (8, .split 13 [
          (1, .split 67 [])])]),
      (6, .split 29 [
        (2, .split 13 [
          (1, .split 67 [
            (4, .split 71 [])]),
          (4, .split 67 []),
          (6, .split 67 [])]),
        (4, .split 71 [
          (2, .split 701 [])]),
        (6, .split 71 [])]),
      (10, .split 29 [
        (2, .split 13 [
          (1, .split 67 [])])]),
      (12, .split 29 [])]),
    (10, .split 19 [
      (4, .split 71 [
        (2, .split 151 []),
        (4, .split 151 [])]),
      (6, .split 71 [
        (2, .split 701 [])]),
      (10, .split 71 [])]),
    (12, .split 19 [
      (4, .split 71 [
        (2, .split 151 []),
        (4, .split 151 [])]),
      (6, .split 71 [
        (2, .split 701 [])])]),
    (16, .split 19 [
      (4, .split 71 [
        (2, .split 151 [])]),
      (6, .split 71 [])]),
    (18, .split 19 [
      (4, .split 71 [])]),
    (22, .split 19 []),
    (24, .split 19 [])]

-- Exact component 5^4.
private noncomputable def seed5Part3 : Script :=
  .split 11 [
    (2, seed5Part4),
    (4, .split 71 [
      (2, .split 3221 [
        (2, .split 5113 [
          (1, .split 2557 [])]),
        (4, .split 5113 [
          (1, .split 2557 [])])]),
      (4, .split 211 [
        (4, .split 1361 [
          (2, .split 13 [
            (1, .split 7 [])])]),
        (6, .split 7 [])]),
      (6, .split 7 [
        (4, .split 883 []),
        (6, .split 29 [
          (2, .split 13 [
            (1, .split 67 [])])]),
        (10, .split 883 [])]),
      (8, .split 37 [
        (1, .split 19 [])]),
      (10, .split 23 [])]),
    (6, .split 43 [
      (4, .split 71 [
        (2, .split 5113 [
          (1, .split 2557 [])]),
        (4, .split 211 []),
        (6, .split 7 [])]),
      (6, .split 7 [
        (4, .split 71 [
          (2, .split 2801 [])]),
        (6, .split 29 [
          (2, .split 13 [
            (1, .split 67 [])])])]),
      (10, .split 71 [])]),
    (8, .split 7 [
      (4, .split 19 [
        (4, .split 71 [
          (2, .split 151 []),
          (4, .split 151 [])]),
        (6, .split 71 [
          (2, .split 701 [])])]),
      (6, .split 19 [
        (4, .split 29 [
          (2, .split 13 [
            (1, .split 67 [])]),
          (4, .split 71 [])]),
        (6, .split 29 [
          (2, .split 13 [
            (1, .split 67 [])])])]),
      (10, .split 19 [
        (4, .split 71 [])]),
      (12, .split 19 [
        (4, .split 71 [])]),
      (16, .split 19 [])]),
    (10, .split 71 [
      (2, .split 5113 [
        (1, .split 2557 [])]),
      (4, .split 211 []),
      (6, .split 7 [])]),
    (12, .split 71 [
      (2, .split 1093 [
        (1, .split 547 [])]),
      (4, .split 211 [])]),
    (14, .split 7 [
      (4, .split 19 [
        (4, .split 71 [])]),
      (6, .split 19 []),
      (10, .split 19 [])]),
    (16, .split 71 [
      (2, .split 5113 [
        (1, .split 2557 [])]),
      (4, .split 211 [])]),
    (18, .split 71 [
      (2, .split 5113 [])]),
    (20, .split 7 [])]

-- Exact component 5^8.
private noncomputable def seed5Part5 : Script :=
  .split 19 [
    (4, .split 31 [
      (4, .split 11 [
        (2, .split 7 [
          (4, .split 151 []),
          (6, .split 29 [
            (2, .split 13 [
              (1, .split 67 [])])]),
          (10, .split 151 [])]),
        (4, .split 151 []),
        (6, .split 43 []),
        (8, .split 7 []),
        (10, .split 151 [])]),
      (6, .split 151 []),
      (10, .split 23 [])]),
    (6, .split 31 [
      (4, .split 11 [
        (2, .split 7 [
          (4, .split 701 []),
          (6, .split 29 [])]),
        (4, .split 701 []),
        (6, .split 43 []),
        (8, .split 7 [])]),
      (6, .split 701 [])]),
    (10, .split 31 [
      (4, .split 11 [
        (2, .split 7 [])])]),
    (12, .split 31 [])]

-- Exact component 5^14.
private noncomputable def seed5Part6 : Script :=
  .split 11 [
    (2, .split 7 [
      (4, .split 19 [
        (4, .split 31 [
          (4, .split 71 [])]),
        (6, .split 31 [])]),
      (6, .split 19 [
        (4, .split 29 [
          (2, .groups [13, 31, 67, 71])]),
        (6, .split 29 [])]),
      (10, .split 19 [
        (4, .split 31 [])]),
      (12, .split 19 []),
      (16, .split 19 [])]),
    (4, .split 31 [
      (4, .split 71 [
        (2, .split 181 [
          (1, .split 7 [
            (4, .split 13 [])])]),
        (4, .split 181 [
          (1, .split 7 [])])]),
      (6, .split 71 [
        (2, .split 181 [])])]),
    (6, .split 31 [
      (4, .split 43 []),
      (6, .split 43 [])]),
    (8, .split 7 [
      (4, .split 19 []),
      (6, .split 19 [])]),
    (10, .split 31 [
      (4, .split 71 [])]),
    (12, .split 31 []),
    (14, .split 7 [])]

private noncomputable def seed5Script : Script :=
  .split 5 [
    (2, seed5Part1),
    (4, seed5Part3),
    (6, .split 19531 [
      (4, .split 191 [
        (2, .split 7 [])])]),
    (8, seed5Part5),
    (10, .split 12207031 []),
    (12, .split 305175781 [
      (1, .split 3499 [
        (4, .split 43609 [])])]),
    (14, seed5Part6),
    (16, .split 409 [
      (1, .split 41 [
        (2, .split 1723 []),
        (4, .split 579281 []),
        (6, .split 43 []),
        (8, .split 487 [])]),
      (4, .split 71 [
        (2, .split 5113 [
          (1, .split 2557 [])])])]),
    (18, .split 191 [
      (2, .split 7 [
        (4, .split 13 [
          (4, .split 31 []),
          (6, .split 31 [])]),
        (6, .split 13 [
          (4, .split 29 [])]),
        (10, .split 13 [])]),
      (4, .split 11 [
        (2, .split 7 [
          (4, .split 19 [])]),
        (4, .split 1871 [])])]),
    (20, .split 31 [
      (4, .split 11 [
        (2, .split 7 [
          (4, .split 19 [])]),
        (4, .split 379 []),
        (6, .split 43 [])]),
      (6, .split 379 [])]),
    (22, .split 8971 []),
    (24, .split 11 [
      (2, .split 7 [
        (4, .split 19 []),
        (6, .split 19 [])]),
      (4, .split 71 [
        (2, .split 101 [])]),
      (6, .split 43 []),
      (8, .split 7 [])]),
    (26, .split 19 [
      (4, .split 31 [])]),
    (28, .split 59 [
      (2, .split 3541 [
        (1, .split 7 [])])]),
    (30, .split 1861 [
      (1, .split 7 [])]),
    (32, .split 31 []),
    (34, .split 11 [])]

-- Exact component 7^6.
private noncomputable def seed7Part1 : Script :=
  .split 29 [
    (2, .split 13 [
      (1, .split 67 [
        (4, .split 761 [
          (2, .split 4733 [])]),
        (6, .split 4733 [
          (2, .split 175897 [])])]),
      (4, .split 67 [
        (4, .split 761 [
          (2, .split 4733 [])]),
        (6, .split 4733 [])]),
      (6, .split 67 [
        (4, .split 761 [
          (2, .split 4733 [])]),
        (6, .split 4733 [])]),
      (9, .split 11 [
        (2, .split 19 [
          (4, .split 67 [])])]),
      (10, .split 23 [
        (2, .split 67 []),
        (4, .split 67 []),
        (6, .split 67 [])]),
      (12, .split 53 [
        (2, .split 67 [])]),
      (13, .split 67 []),
      (16, .split 67 [])]),
    (4, .split 4733 [
      (2, .split 732541 [
        (1, .split 47 [])]),
      (4, .split 11 [])]),
    (6, .split 4733 [
      (2, .split 22406023 [])]),
    (8, .split 13 [
      (1, .split 67 [
        (4, .split 761 [])]),
      (4, .split 67 []),
      (6, .split 67 [])]),
    (10, .split 23 [
      (2, .split 79 []),
      (4, .split 4733 [])]),
    (12, .split 521 [])]

private noncomputable def seed7Script : Script :=
  .split 7 [
    (4, .split 2801 [
      (2, .split 37 [
        (1, .split 19 [
          (4, .split 43 [
            (4, .split 151 []),
            (6, .split 151 [])]),
          (6, .split 43 [
            (4, .split 701 [])]),
          (10, .split 43 [])]),
        (4, .split 11 [
          (2, .split 19 [
            (4, .split 41 [
              (2, .split 43 [])]),
            (6, .split 41 [
              (2, .split 43 [])])]),
          (6, .split 41 [
            (2, .split 43 [])]),
          (8, .split 19 [])]),
        (6, .split 43 [
          (4, .split 71 [])]),
        (9, .split 11 []),
        (10, .split 43 [])])]),
    (6, seed7Part1),
    (10, .split 1123 [
      (4, .split 41 [
        (2, .split 1723 [])])]),
    (12, .split 16148168401 [
      (1, .split 103 [])]),
    (16, .split 14009 [
      (2, .split 223 [])]),
    (18, .split 419 [
      (2, .split 13 [
        (1, .split 13537 []),
        (4, .split 13537 [])])]),
    (22, .split 47 [
      (2, .split 37 [
        (1, .split 19 [])])]),
    (24, .split 2551 [])]

private theorem seed3Check :
    replaySize splitPrimes 3 1 (10^50) 5 31 37 105 105 root seed3Script = true := by
  decide +kernel

theorem exclude_3_size_50 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hw : 5 ≤ N.primeFactors.card)
    (hsize : N ≤ 10^50) (hlow : 37 ≤ N.primeFactorsList.length) (hseed : 3 ∣ N) : False :=
  replaySize_correct ho hN hw hseed (Nat.coprime_one_left N) hsize (ochem_rao_prime_factor_count ho hN) hlow splitPrimes prime_proofs 105
    (root_realizes N) seed3Script seed3Check

private theorem seed5Check :
    replaySize splitPrimes 5 3 (10^50) 8 15 37 72 72 root seed5Script = true := by
  decide +kernel

theorem exclude_5_size_50 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hw : 8 ≤ N.primeFactors.card)
    (hsize : N ≤ 10^50) (hlow : 37 ≤ N.primeFactorsList.length) (h3 : ¬ 3 ∣ N) (hseed : 5 ∣ N) : False :=
  replaySize_correct ho hN hw hseed ((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr h3) hsize ((ochem_rao_count_cases ho hN).2 h3) hlow splitPrimes prime_proofs 72
    (root_realizes N) seed5Script seed5Check

private theorem seed7Check :
    replaySize splitPrimes 7 15 (10^50) 15 15 37 60 60 root seed7Script = true := by
  decide +kernel

theorem exclude_7_size_50 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hw : 15 ≤ N.primeFactors.card)
    (hsize : N ≤ 10^50) (hlow : 37 ≤ N.primeFactorsList.length) (h3 : ¬ 3 ∣ N) (h5 : ¬ 5 ∣ N) (hseed : 7 ∣ N) : False :=
  replaySize_correct ho hN hw hseed (((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr h3).mul_left ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr h5)) hsize ((ochem_rao_count_cases ho hN).2 h3) hlow splitPrimes prime_proofs 60
    (root_realizes N) seed7Script seed7Check

end OddPerfect.FactorBudget
