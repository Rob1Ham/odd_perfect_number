module

public import OddPerfect.ChainCheckpoint
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.FactorBudget.Count35

set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] noncomputable def primes1 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

private theorem primes1_valid : ∀ p ∈ primes1, p.Prime := by
  simp only [primes1, List.forall_mem_cons]
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
    by norm_num, by simp⟩

@[expose] noncomputable def primes2 : List ℕ := [101, 103, 109, 113, 127, 131, 137, 139, 151, 157, 163, 181, 191, 193, 197, 199, 211, 223, 229, 239, 251, 263, 271, 277]

private theorem primes2_valid : ∀ p ∈ primes2, p.Prime := by
  simp only [primes2, List.forall_mem_cons]
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
    by norm_num, by simp⟩

@[expose] noncomputable def primes3 : List ℕ := [281, 283, 307, 311, 313, 331, 337, 353, 367, 373, 379, 397, 409, 419, 421, 431, 433, 443, 449, 457, 461, 463, 467, 487]

private theorem primes3_valid : ∀ p ∈ primes3, p.Prime := by
  simp only [primes3, List.forall_mem_cons]
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
    by norm_num, by simp⟩

@[expose] noncomputable def primes4 : List ℕ := [521, 523, 541, 547, 571, 577, 599, 613, 617, 631, 647, 659, 661, 673, 677, 691, 701, 727, 733, 743, 751, 757, 761, 769]

private theorem primes4_valid : ∀ p ∈ primes4, p.Prime := by
  simp only [primes4, List.forall_mem_cons]
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
    by norm_num, by simp⟩

@[expose] noncomputable def primes5 : List ℕ := [787, 811, 821, 823, 829, 859, 883, 911, 937, 947, 953, 967, 991, 1009, 1031, 1051, 1063, 1093, 1123, 1171, 1231, 1279, 1291, 1301]

private theorem primes5_valid : ∀ p ∈ primes5, p.Prime := by
  simp only [primes5, List.forall_mem_cons]
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
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13] }]), by simp⟩

@[expose] noncomputable def primes6 : List ℕ := [1361, 1381, 1429, 1451, 1459, 1471, 1483, 1499, 1597, 1621, 1693, 1699, 1723, 1787, 1801, 1811, 1831, 1871, 1933, 2029, 2053, 2069, 2113, 2129]

private theorem primes6_valid : ∀ p ∈ primes6, p.Prime := by
  simp only [primes6, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 19] }]), by simp⟩

@[expose] noncomputable def primes7 : List ℕ := [2131, 2221, 2243, 2281, 2311, 2347, 2381, 2503, 2551, 2557, 2633, 2663, 2671, 2801, 3011, 3041, 3067, 3137, 3169, 3187, 3217, 3221, 3229, 3313]

private theorem primes7_valid : ∀ p ∈ primes7, p.Prime := by
  simp only [primes7, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 269] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 23] }]), by simp⟩

@[expose] noncomputable def primes8 : List ℕ := [3319, 3491, 3499, 3541, 3571, 3719, 3851, 3911, 3931, 4027, 4049, 4051, 4159, 4201, 4261, 4271, 4447, 4561, 4591, 4651, 4729, 4733, 4751, 4933]

private theorem primes8_valid : ∀ p ∈ primes8, p.Prime := by
  simp only [primes8, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 17, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 137] }]), by simp⟩

@[expose] noncomputable def primes9 : List ℕ := [5113, 5209, 5233, 5419, 5641, 5827, 5839, 6101, 6133, 6221, 6301, 6491, 6781, 7151, 7561, 7603, 7621, 7673, 7699, 7717, 8011, 8059, 8269, 8387]

private theorem primes9_valid : ∀ p ∈ primes9, p.Prime := by
  simp only [primes9, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 7, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 971] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 311] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1283] }, .lucas { root := 2, primeFactors := [2, 641] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 643] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 599] }]), by simp⟩

@[expose] noncomputable def primes10 : List ℕ := [8581, 8647, 8807, 8971, 9241, 9431, 9631, 9851, 9871, 9967, 10303, 10847, 11299, 11503, 11807, 12011, 12157, 12601, 12853, 12893, 13267, 13537, 14009, 14083]

private theorem primes10_valid : ∀ p ∈ primes10, p.Prime := by
  simp only [primes10, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 17, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 23, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 17, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 269] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 5903] }, .lucas { root := 5, primeFactors := [2, 13, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1201] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1013] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 293] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 17, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2347] }, .lucas { root := 3, primeFactors := [2, 3, 17, 23] }]), by simp⟩

@[expose] noncomputable def primes11 : List ℕ := [14281, 14713, 14939, 15797, 15889, 16481, 16651, 17137, 17293, 17351, 17707, 17881, 17911, 17923, 18041, 18457, 19441, 19531, 19571, 20161, 21433, 21491, 21613, 22079]

private theorem primes11_valid : ∀ p ∈ primes11, p.Prime := by
  simp only [primes11, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 613] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 11, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 359] }]),
    by primality (cert := .witnesses [.lucas { root := 21, primeFactors := [2, 3, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 347] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 769] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 19, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1801] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 19, 83] }]), by simp⟩

@[expose] noncomputable def primes12 : List ℕ := [22093, 24517, 24571, 25307, 28057, 28387, 28729, 29251, 30103, 30941, 33151, 34511, 37861, 39103, 42407, 43609, 44371, 45121, 45319, 47251, 48541, 49547, 51343, 51487]

private theorem primes12_valid : ∀ p ∈ primes12, p.Prime := by
  simp only [primes12, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 263] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 12653] }, .lucas { root := 2, primeFactors := [2, 3163] }, .lucas { root := 3, primeFactors := [2, 3, 17, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 29, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 17, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 631] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 13, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 23, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 13, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 809] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 3539] }, .lucas { root := 2, primeFactors := [2, 29, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 43, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 8581] }, .lucas { root := 6, primeFactors := [2, 3, 5, 11, 13] }]), by simp⟩

@[expose] noncomputable def primes13 : List ℕ := [52807, 55897, 56773, 59023, 59581, 64661, 67411, 70001, 70841, 72931, 73181, 86143, 86353, 88741, 95857, 104281, 147073, 147739, 151201, 151841, 160967, 169691, 178601, 187123]

private theorem primes13_valid : ∀ p ∈ primes13, p.Prime := by
  simp only [primes13, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 677] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1093] }, .lucas { root := 5, primeFactors := [2, 3, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 53, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 11, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 11, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 3659] }, .lucas { root := 2, primeFactors := [2, 31, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 293] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 1997] }, .lucas { root := 2, primeFactors := [2, 499] }]),
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 5, 11, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 383] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 24623] }, .lucas { root := 5, primeFactors := [2, 13, 947] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 41, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 71, 239] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 19, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 2399] }, .lucas { root := 11, primeFactors := [2, 11, 109] }]), by simp⟩

@[expose] noncomputable def primes14 : List ℕ := [189967, 202519, 204781, 257611, 262321, 264031, 264581, 286001, 292561, 293459, 337901, 349927, 363889, 365017, 368089, 384481, 398581, 456451, 459007, 492103, 552793, 570821, 579281, 583367]

private theorem primes14_valid : ∀ p ∈ primes14, p.Prime := by
  simp only [primes14, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 4523] }, .lucas { root := 5, primeFactors := [2, 7, 17, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11251] }, .lucas { root := 13, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 3413] }, .lucas { root := 2, primeFactors := [2, 853] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 31, 277] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 1093] }, .lucas { root := 5, primeFactors := [2, 3, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 13, 677] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13229] }, .lucas { root := 2, primeFactors := [2, 3307] }, .lucas { root := 2, primeFactors := [2, 3, 19, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 23, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 13339] }, .lucas { root := 2, primeFactors := [2, 3, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 31, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 58321] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 67, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 313] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 17, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 113, 677] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 13, 701] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 31, 743] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 28541] }, .lucas { root := 2, primeFactors := [2, 5, 1427] }, .lucas { root := 2, primeFactors := [2, 23, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 13, 557] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 41669] }, .lucas { root := 2, primeFactors := [2, 11, 947] }]), by simp⟩

@[expose] noncomputable def primes15 : List ℕ := [672901, 732541, 733591, 797161, 830833, 878837, 900329, 973001, 990151, 1018177, 1141081, 1222567, 1372537, 1386659, 1509997, 1609669, 1645747, 1674289, 1717451, 1774921, 1806113, 1866871, 1867147, 1956611]

private theorem primes15_valid : ∀ p ∈ primes15, p.Prime := by
  simp only [primes15, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 2243] }, .lucas { root := 2, primeFactors := [2, 19, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 29, 421] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7, 13, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 19, 911] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 31387] }, .lucas { root := 2, primeFactors := [2, 3, 5231] }, .lucas { root := 7, primeFactors := [2, 5, 523] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 13, 787] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 7, 23, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5303] }, .lucas { root := 5, primeFactors := [2, 11, 241] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 37, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 203761] }, .lucas { root := 11, primeFactors := [2, 3, 5, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 1733] }, .lucas { root := 2, primeFactors := [2, 433] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 13, 19, 401] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 5471] }, .lucas { root := 7, primeFactors := [2, 5, 547] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 61, 733] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 59, 4649] }, .lucas { root := 3, primeFactors := [2, 7, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 7, 11, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 701] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 7, 2113] }, .lucas { root := 5, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11, 733] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 20743] }, .lucas { root := 5, primeFactors := [2, 3, 3457] }, .lucas { root := 7, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 43, 7237] }, .lucas { root := 2, primeFactors := [2, 3, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 23, 47, 181] }]), by simp⟩

@[expose] noncomputable def primes16 : List ℕ := [2180921, 2261887, 2289401, 2332903, 2380141, 2384047, 2426789, 2695351, 3044803, 3093121, 3330391, 3348577, 3500201, 3798019, 4534567, 4760281, 5229043, 5336717, 5390701, 5471551, 6038099, 6294091, 6586781, 6619231]

private theorem primes16_valid : ∀ p ∈ primes16, p.Prime := by
  simp only [primes16, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 7789] }, .lucas { root := 2, primeFactors := [2, 3, 11, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 43, 797] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11447] }, .lucas { root := 5, primeFactors := [2, 59, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 13, 2719] }, .lucas { root := 3, primeFactors := [2, 3, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 1889] }, .lucas { root := 3, primeFactors := [2, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 17, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 13, 59, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 17, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 29851] }, .lucas { root := 2, primeFactors := [2, 3, 5, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 15859] }, .lucas { root := 2, primeFactors := [2, 3, 881] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 11, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 37, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43, 701] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 251, 3011] }, .lucas { root := 2, primeFactors := [2, 5, 7, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 7, 1889] }, .lucas { root := 3, primeFactors := [2, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 7, 13, 61, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11, 17327] }, .lucas { root := 5, primeFactors := [2, 8663] }, .lucas { root := 5, primeFactors := [2, 61, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 17, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 23, 11933] }, .lucas { root := 2, primeFactors := [2, 19, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 11, 19073] }, .lucas { root := 3, primeFactors := [2, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 61, 5399] }, .lucas { root := 7, primeFactors := [2, 2699] }, .lucas { root := 2, primeFactors := [2, 19, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 73547] }, .lucas { root := 2, primeFactors := [2, 11, 3343] }, .lucas { root := 5, primeFactors := [2, 3, 557] }]), by simp⟩

@[expose] noncomputable def primes17 : List ℕ := [7063513, 7834583, 7908811, 9065531, 9069133, 10332211, 10378063, 12207031, 12865927, 17311991, 19271071, 19622651, 20241187, 22406023, 22576753, 22996651, 25646167, 26466301, 28792661, 32668561, 34770289, 38786029, 39449441, 43435141]

private theorem primes17_valid : ∀ p ∈ primes17, p.Prime := by
  simp only [primes17, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 294313] }, .lucas { root := 10, primeFactors := [2, 3, 12263] }, .lucas { root := 5, primeFactors := [2, 6131] }, .lucas { root := 2, primeFactors := [2, 5, 613] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 23, 29, 839] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 2897] }, .lucas { root := 3, primeFactors := [2, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 109, 8317] }, .lucas { root := 6, primeFactors := [2, 3, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 251, 3011] }, .lucas { root := 2, primeFactors := [2, 5, 7, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 49201] }, .lucas { root := 7, primeFactors := [2, 3, 5, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 179, 3221] }, .lucas { root := 10, primeFactors := [2, 5, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 71, 521] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19, 112859] }, .lucas { root := 2, primeFactors := [2, 73, 773] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 1731199] }, .lucas { root := 6, primeFactors := [2, 3, 7, 47, 877] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 7, 13, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 601, 653] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 17, 28349] }, .lucas { root := 2, primeFactors := [2, 19, 373] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 263, 4733] }, .lucas { root := 5, primeFactors := [2, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 4751] }, .lucas { root := 19, primeFactors := [2, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 19, 8069] }, .lucas { root := 2, primeFactors := [2, 2017] }, .lucas { root := 5, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 13, 17, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 4201] }, .lucas { root := 11, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13, 37, 41, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 17, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 103483] }, .lucas { root := 2, primeFactors := [2, 3, 5749] }, .lucas { root := 2, primeFactors := [2, 3, 479] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 367, 8807] }, .lucas { root := 5, primeFactors := [2, 7, 17, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 79, 3121] }, .lucas { root := 7, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 19, 5443] }, .lucas { root := 2, primeFactors := [2, 3, 907] }]), by simp⟩

@[expose] noncomputable def primes18 : List ℕ := [46574123, 47691619, 48037081, 52932601, 60055811, 62060021, 66166691, 77572057, 87653303, 88009573, 93853931, 104670301, 115847929, 127159831, 157920029, 168820969, 170638711, 201252871, 208097431, 249561007, 251101831, 262209281, 305175781, 366340651]

private theorem primes18_valid : ∀ p ∈ primes18, p.Prime := by
  simp only [primes18, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 83, 149, 269] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 137, 4463] }, .lucas { root := 5, primeFactors := [2, 23, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7, 13, 53, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 4201] }, .lucas { root := 11, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 29, 37, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 282091] }, .lucas { root := 3, primeFactors := [2, 3, 5, 9403] }, .lucas { root := 3, primeFactors := [2, 3, 1567] }, .lucas { root := 3, primeFactors := [2, 3, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 29, 151, 1511] }, .lucas { root := 11, primeFactors := [2, 5, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 367, 8807] }, .lucas { root := 5, primeFactors := [2, 7, 17, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 1129, 3529] }, .lucas { root := 11, primeFactors := [2, 3, 47] }, .lucas { root := 17, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 7, 337, 3109] }, .lucas { root := 6, primeFactors := [2, 3, 7, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 181, 51853] }, .lucas { root := 11, primeFactors := [2, 3, 29, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 49843] }, .lucas { root := 2, primeFactors := [2, 3, 13, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 31, primeFactors := [2, 3, 7, 17, 4507] }, .lucas { root := 2, primeFactors := [2, 3, 751] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 17, 31, 383] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 41, 151, 911] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 73, 167, 577] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11, 517087] }, .lucas { root := 3, primeFactors := [2, 3, 23, 1249] }, .lucas { root := 7, primeFactors := [2, 3, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 33, primeFactors := [2, 3, 5, 7, 13, 8191] }, .lucas { root := 17, primeFactors := [2, 3, 5, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 131, 52951] }, .lucas { root := 3, primeFactors := [2, 3, 5, 353] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2633, 15797] }, .lucas { root := 3, primeFactors := [2, 7, 47] }, .lucas { root := 2, primeFactors := [2, 11, 359] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 1195723] }, .lucas { root := 2, primeFactors := [2, 3, 11, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 127, 1613] }, .lucas { root := 3, primeFactors := [2, 13, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 13, 31, 601] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 17, 43, 257] }]), by simp⟩

@[expose] noncomputable def primes19 : List ℕ := [381510691, 398137391, 466344409, 527532101, 591694601, 604842197, 656276671, 875335231, 917087137, 1394714501, 1478526139, 1579264051, 2666986681, 2767631689, 3158528101, 3202878953, 3276517921, 4164418987, 4400521837, 4802611441, 5908670381, 7210204801, 12081356831, 12346432697]

private theorem primes19_valid : ∀ p ∈ primes19, p.Prime := by
  simp only [primes19, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 19, 71, 857] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 37, 347, 443] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 17, 31, 36871] }, .lucas { root := 15, primeFactors := [2, 3, 5, 1229] }, .lucas { root := 2, primeFactors := [2, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 310313] }, .lucas { root := 3, primeFactors := [2, 79, 491] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 173, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 131, 269, 613] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 17, 29, 2113] }, .lucas { root := 5, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 11, 126311] }, .lucas { root := 23, primeFactors := [2, 5, 17, 743] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 19, 31, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 97, 149, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 419, 196039] }, .lucas { root := 3, primeFactors := [2, 3, 10891] }, .lucas { root := 2, primeFactors := [2, 3, 5, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 127, 911] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 19, 227, 5153] }, .lucas { root := 5, primeFactors := [2, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 29, primeFactors := [2, 3, 17, 71, 31847] }, .lucas { root := 5, primeFactors := [2, 15923] }, .lucas { root := 2, primeFactors := [2, 19, 419] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 127, 911] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 13, 37, 118907] }, .lucas { root := 2, primeFactors := [2, 59453] }, .lucas { root := 2, primeFactors := [2, 89, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 13, 239] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13, 7627141] }, .lucas { root := 13, primeFactors := [2, 3, 5, 42373] }, .lucas { root := 5, primeFactors := [2, 3, 11, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 366710153] }, .lucas { root := 3, primeFactors := [2, 45838769] }, .lucas { root := 3, primeFactors := [2, 151, 18973] }, .lucas { root := 2, primeFactors := [2, 3, 17, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 29, primeFactors := [2, 3, 5, 11, 263, 6917] }, .lucas { root := 2, primeFactors := [2, 7, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 139, 277, 7673] }, .lucas { root := 3, primeFactors := [2, 7, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 37, 53, 383] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 61, 2833, 6991] }, .lucas { root := 5, primeFactors := [2, 3, 59] }, .lucas { root := 6, primeFactors := [2, 3, 5, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 13, 61, 1123, 1733] }, .lucas { root := 2, primeFactors := [2, 3, 11, 17] }, .lucas { root := 2, primeFactors := [2, 433] }]), by simp⟩

@[expose] noncomputable def primes20 : List ℕ := [12936304421, 13080080081, 16148168401, 16656709681, 19408913261, 24903325661, 26403131021, 37028483467, 46685826619, 49275341281, 50689400581, 52379047267, 62995328779, 136850668961, 153436090543, 232611722621, 297134095231, 395950646197, 502628805631, 934415109937, 1653850268201, 1957650063931, 2141993519227, 3090276117871]

private theorem primes20_valid : ∀ p ∈ primes20, p.Prime := by
  simp only [primes20, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13, 41, 277, 337] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 71, 1433, 1607] }, .lucas { root := 3, primeFactors := [2, 179] }, .lucas { root := 5, primeFactors := [2, 11, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 5, 7, 13, 19, 43, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 13, 359, 4957] }, .lucas { root := 2, primeFactors := [2, 3, 7, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 17, 373, 13913] }, .lucas { root := 3, primeFactors := [2, 37, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 199, 397, 15761] }, .lucas { root := 3, primeFactors := [2, 5, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 188593793] }, .lucas { root := 3, primeFactors := [2, 1473389] }, .lucas { root := 2, primeFactors := [2, 7, 101, 521] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 474724147] }, .lucas { root := 2, primeFactors := [2, 3, 13, 1553, 3919] }, .lucas { root := 3, primeFactors := [2, 97] }, .lucas { root := 3, primeFactors := [2, 3, 653] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 41, 127, 1009, 1481] }, .lucas { root := 3, primeFactors := [2, 5, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 11, 61, 89, 191] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 13, 61, 97, 523] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 31, 61, 97, 523] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 43, 244167941] }, .lucas { root := 7, primeFactors := [2, 5, 17, 89, 8069] }, .lucas { root := 2, primeFactors := [2, 2017] }, .lucas { root := 5, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 855316681] }, .lucas { root := 11, primeFactors := [2, 3, 5, 7127639] }, .lucas { root := 7, primeFactors := [2, 7, 257, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 37, 73, 751, 1801] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 389, 3767, 7937] }, .lucas { root := 5, primeFactors := [2, 7, 269] }, .lucas { root := 3, primeFactors := [2, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 17, 557, 16603] }, .lucas { root := 2, primeFactors := [2, 3, 2767] }, .lucas { root := 3, primeFactors := [2, 3, 461] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 2311, 226631] }, .lucas { root := 3, primeFactors := [2, 3, 5, 7, 11] }, .lucas { root := 13, primeFactors := [2, 5, 131, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 89, 373, 8011] }, .lucas { root := 14, primeFactors := [2, 3, 5, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 7, 11, 43, 151, 12979] }, .lucas { root := 2, primeFactors := [2, 3, 7, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13, 23, 27656359] }, .lucas { root := 3, primeFactors := [2, 3, 4609393] }, .lucas { root := 5, primeFactors := [2, 3, 109, 881] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 107, 1129, 16369] }, .lucas { root := 11, primeFactors := [2, 3, 47] }, .lucas { root := 7, primeFactors := [2, 3, 11, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17, 71, 101, 88741] }, .lucas { root := 2, primeFactors := [2, 3, 5, 17, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 17, 29851, 202987] }, .lucas { root := 2, primeFactors := [2, 3, 5, 199] }, .lucas { root := 2, primeFactors := [2, 3, 7, 179] }]), by simp⟩

@[expose] noncomputable def primes21 : List ℕ := [3737657091169, 4172851565741, 9468940004449, 11016462577051, 18871143464293, 31747594185191, 138161295607249, 219241969146019, 251059142817757, 304018940824561, 1437263292796553, 1648012040336791, 1812169199976451, 1940350890330343, 2703853428809791, 50544702849929377, 81750272028928231, 365834083876629007, 6115909044841454629, 18855337777262169791, 22280841470107301759731, 109912203092239643840221, 398341412240537151131351, 751670559138758105956097]

private theorem primes21_valid : ∀ p ∈ primes21, p.Prime := by
  simp only [primes21, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 37, primeFactors := [2, 3, 7, 11, 13, 19, 151, 4519] }, .lucas { root := 3, primeFactors := [2, 3, 251] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 11, 13, 181, 1429, 5641] }, .lucas { root := 6, primeFactors := [2, 3, 7, 17] }, .lucas { root := 14, primeFactors := [2, 3, 5, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 19, 4603, 1127809] }, .lucas { root := 2, primeFactors := [2, 3, 13, 59] }, .lucas { root := 17, primeFactors := [2, 3, 11, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 31, 103, 149, 7351] }, .lucas { root := 6, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 19, 41, 67, 163, 26407] }, .lucas { root := 5, primeFactors := [2, 3, 163] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 13, 244212262963] }, .lucas { root := 3, primeFactors := [2, 3, 19, 3001, 713833] }, .lucas { root := 14, primeFactors := [2, 3, 5] }, .lucas { root := 5, primeFactors := [2, 3, 7, 607] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 959453441717] }, .lucas { root := 5, primeFactors := [2, 7, 11, 17, 19, 1377757] }, .lucas { root := 5, primeFactors := [2, 3, 12757] }, .lucas { root := 2, primeFactors := [2, 3, 1063] }, .lucas { root := 3, primeFactors := [2, 3, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 7, 13, 17, 61, 307, 140143] }, .lucas { root := 5, primeFactors := [2, 3, 23357] }, .lucas { root := 2, primeFactors := [2, 5839] }, .lucas { root := 6, primeFactors := [2, 3, 7, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 7, 13, 43, 251, 1471, 1609] }, .lucas { root := 6, primeFactors := [2, 3, 5, 7] }, .lucas { root := 7, primeFactors := [2, 3, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 13, 10826885357] }, .lucas { root := 2, primeFactors := [2, 7, 55239211] }, .lucas { root := 2, primeFactors := [2, 3, 5, 13, 31, 1523] }, .lucas { root := 2, primeFactors := [2, 761] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 53, 25423, 10256527] }, .lucas { root := 3, primeFactors := [2, 3, 19, 223] }, .lucas { root := 3, primeFactors := [2, 3, 7, 81401] }, .lucas { root := 3, primeFactors := [2, 5, 11, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 283, 64704045557] }, .lucas { root := 2, primeFactors := [2, 23, 31, 37, 613169] }, .lucas { root := 3, primeFactors := [2, 19, 2017] }, .lucas { root := 5, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 7, 19, 349, 2143, 121453] }, .lucas { root := 3, primeFactors := [2, 3, 7, 17] }, .lucas { root := 6, primeFactors := [2, 3, 29, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 19, 59, 61, 97, 353, 6577] }, .lucas { root := 5, primeFactors := [2, 3, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 137, 657871880489] }, .lucas { root := 3, primeFactors := [2, 82233985061] }, .lucas { root := 2, primeFactors := [2, 5, 149, 27595297] }, .lucas { root := 5, primeFactors := [2, 3, 19, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 17, 61, 7321, 6304673] }, .lucas { root := 7, primeFactors := [2, 3, 5, 61] }, .lucas { root := 3, primeFactors := [2, 11, 17911] }, .lucas { root := 3, primeFactors := [2, 3, 5, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 13, 4013, 7462037027] }, .lucas { root := 2, primeFactors := [2, 17, 59] }, .lucas { root := 2, primeFactors := [2, 173, 283, 76207] }, .lucas { root := 3, primeFactors := [2, 3, 13, 977] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1373, 73421, 604842197] }, .lucas { root := 2, primeFactors := [2, 7] }, .lucas { root := 2, primeFactors := [2, 5, 3671] }, .lucas { root := 13, primeFactors := [2, 5, 367] }, .lucas { root := 2, primeFactors := [2, 7, 131, 269, 613] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 7, 11, 19, 37, 590077, 1772893] }, .lucas { root := 6, primeFactors := [2, 3, 37, 443] }, .lucas { root := 17, primeFactors := [2, 3, 11, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 67, 28142295189943537] }, .lucas { root := 5, primeFactors := [2, 3, 7, 17, 547430267467] }, .lucas { root := 2, primeFactors := [2, 3, 31, 981057827] }, .lucas { root := 2, primeFactors := [2, 7, 70075559] }, .lucas { root := 7, primeFactors := [2, 7, 37, 135281] }, .lucas { root := 6, primeFactors := [2, 5, 19, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 191, 113381713, 293121781] }, .lucas { root := 5, primeFactors := [2, 3, 43, 18311] }, .lucas { root := 13, primeFactors := [2, 5, 1831] }, .lucas { root := 3, primeFactors := [2, 3, 5, 61] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7, 697909] }, .lucas { root := 2, primeFactors := [2, 3, 19, 3061] }, .lucas { root := 6, primeFactors := [2, 3, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 19, 127, 199, 523, 29989, 236377] }, .lucas { root := 2, primeFactors := [2, 3, 7, 17] }, .lucas { root := 10, primeFactors := [2, 3, 7, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 11, 23, 229, 251101831, 547620341] }, .lucas { root := 6, primeFactors := [2, 3, 5, 7, 1195723] }, .lucas { root := 2, primeFactors := [2, 3, 11, 61] }, .lucas { root := 10, primeFactors := [2, 5, 23, 29, 41051] }, .lucas { root := 2, primeFactors := [2, 5, 821] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 17, 31, 37, 409, 1129, 25085030513] }, .lucas { root := 11, primeFactors := [2, 3, 47] }, .lucas { root := 3, primeFactors := [2, 1229, 1275683] }, .lucas { root := 2, primeFactors := [2, 307] }, .lucas { root := 2, primeFactors := [2, 637841] }, .lucas { root := 21, primeFactors := [2, 5, 7, 17, 67] }]), by simp⟩

@[expose] noncomputable def primes22 : List ℕ := [1285983178319318482443211013887, 62065212901958868055012327674641, 42823405115868247139117302138464781, 154522673919080310634923725508989347, 1247451159302262598804596798564656994853573, 19256021298645399074821884828797791764310604858317]

private theorem primes22_valid : ∀ p ∈ primes22, p.Prime := by
  simp only [primes22, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 23, 43, 67, 2267, 104281, 179743, 10874422681] }, .lucas { root := 2, primeFactors := [2, 11, 103] }, .lucas { root := 26, primeFactors := [2, 3, 5, 11, 79] }, .lucas { root := 3, primeFactors := [2, 3, 29, 1033] }, .lucas { root := 5, primeFactors := [2, 3, 43] }, .lucas { root := 7, primeFactors := [2, 3, 5, 11, 79, 104281] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 17, 97, 233, 941, 189977, 230512752775793] }, .lucas { root := 3, primeFactors := [2, 23747] }, .lucas { root := 2, primeFactors := [2, 31, 383] }, .lucas { root := 3, primeFactors := [2, 31, 106747, 4353691] }, .lucas { root := 2, primeFactors := [2, 3, 17791] }, .lucas { root := 3, primeFactors := [2, 3, 5, 593] }, .lucas { root := 2, primeFactors := [2, 3, 5, 11, 79, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 11, 13, 17, 31, 37, 409, 769, 6367, 17393, 590593, 1777609] }, .lucas { root := 3, primeFactors := [2, 3, 1061] }, .lucas { root := 2, primeFactors := [2, 5, 53] }, .lucas { root := 3, primeFactors := [2, 1087] }, .lucas { root := 3, primeFactors := [2, 3, 181] }, .lucas { root := 15, primeFactors := [2, 3, 769] }, .lucas { root := 13, primeFactors := [2, 3, 7, 3527] }, .lucas { root := 5, primeFactors := [2, 41, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 7, 13, 43, 47, 67, 271, 7793, 732541, 15349897, 88013053] }, .lucas { root := 3, primeFactors := [2, 487] }, .lucas { root := 10, primeFactors := [2, 3, 5, 29, 421] }, .lucas { root := 5, primeFactors := [2, 3, 213193] }, .lucas { root := 5, primeFactors := [2, 3, 7, 47] }, .lucas { root := 2, primeFactors := [2, 3, 1009, 2423] }, .lucas { root := 5, primeFactors := [2, 7, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 73, 179, 857, 3221, 3643, 6053, 10378063, 107637315400441] }, .lucas { root := 10, primeFactors := [2, 5, 7, 23] }, .lucas { root := 2, primeFactors := [2, 3, 607] }, .lucas { root := 2, primeFactors := [2, 17, 89] }, .lucas { root := 11, primeFactors := [2, 3, 179, 3221] }, .lucas { root := 19, primeFactors := [2, 3, 5, 7, 23, 179, 3221] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 73, 97, 137, 163, 547, 613, 1621, 1747, 3079, 39799, 299359, 5111046132733] }, .lucas { root := 2, primeFactors := [2, 3, 5] }, .lucas { root := 2, primeFactors := [2, 3, 97] }, .lucas { root := 6, primeFactors := [2, 3, 19] }, .lucas { root := 3, primeFactors := [2, 3, 11, 67] }, .lucas { root := 6, primeFactors := [2, 3, 16631] }, .lucas { root := 19, primeFactors := [2, 5, 1663] }, .lucas { root := 3, primeFactors := [2, 3, 277] }, .lucas { root := 2, primeFactors := [2, 3, 15774833743] }, .lucas { root := 5, primeFactors := [2, 3, 2629138957] }, .lucas { root := 2, primeFactors := [2, 3, 29, 157, 48121] }, .lucas { root := 13, primeFactors := [2, 3, 5, 401] }]), by simp⟩

@[expose] noncomputable def splitPrimes : List ℕ :=
  primes1 ++ (primes2 ++ (primes3 ++ (primes4 ++ (primes5 ++ (primes6 ++ (primes7 ++ (primes8 ++ (primes9 ++ (primes10 ++ (primes11 ++ (primes12 ++ (primes13 ++ (primes14 ++ (primes15 ++ (primes16 ++ (primes17 ++ (primes18 ++ (primes19 ++ (primes20 ++ (primes21 ++ (primes22)))))))))))))))))))))

theorem prime_proofs : ∀ p ∈ splitPrimes, p.Prime := by
  simp only [splitPrimes, List.forall_mem_append]
  exact ⟨primes1_valid, primes2_valid, primes3_valid, primes4_valid, primes5_valid, primes6_valid, primes7_valid, primes8_valid, primes9_valid, primes10_valid, primes11_valid, primes12_valid, primes13_valid, primes14_valid, primes15_valid, primes16_valid, primes17_valid, primes18_valid, primes19_valid, primes20_valid, primes21_valid, primes22_valid⟩

end OddPerfect.FactorBudget.Count35
