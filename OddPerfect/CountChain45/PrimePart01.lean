module

public import OddPerfect.ChainCheckpoint
import Mathlib.Tactic.Primality
public import OddPerfect.LargeOrderCube

public section

namespace OddPerfect.FactorBudget.Count45

set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] noncomputable def primes1 : List ℕ := [7, 19, 43, 67, 2801, 31, 29, 127, 11, 151, 37, 13, 23, 79, 331, 71, 97, 701, 61, 631, 911, 617, 4733, 433]

theorem primes1_valid : ∀ p ∈ primes1, p.Prime := by
  simp only [primes1, List.forall_mem_cons]
  exact ⟨by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7] }]),
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
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 13] }]),
    by norm_num, by simp⟩

@[expose] noncomputable def primes2 : List ℕ := [5, 157, 5419, 307, 41, 5113, 211, 761, 1093, 1123, 613, 89, 53, 3169, 131, 757, 30941, 199, 397, 3221, 292561, 4933, 101, 181]

theorem primes2_valid : ∀ p ∈ primes2, p.Prime := by
  simp only [primes2, List.forall_mem_cons]
  exact ⟨by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }]),
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 71] }]),
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17] }]),
    by norm_num,
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11] }]),
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 13, 17] }]),
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 23, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 137] }]),
    by norm_num,
    by norm_num, by simp⟩

@[expose] noncomputable def primes3 : List ℕ := [467, 3851, 113, 547, 47, 1499, 191, 73, 1723, 70841, 732541, 419, 409, 2557, 379, 45319, 859, 523, 1063, 991, 1693, 883, 103, 17351]

theorem primes3_valid : ∀ p ∈ primes3, p.Prime := by
  simp only [primes3, List.forall_mem_cons]
  exact ⟨by norm_num,
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 11] }]),
    by norm_num,
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 107] }]),
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 11, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 29, 421] }]),
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 71] }]),
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 13, 83] }]),
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 59] }]),
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 47] }]),
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 347] }]), by simp⟩

@[expose] noncomputable def primes4 : List ℕ := [281, 733, 239, 1051, 1621, 8011, 313, 109, 1806113, 271, 829, 1031, 26881, 599, 3931, 787, 3313, 17, 139, 2221, 163, 229, 15797, 17293]

theorem primes4_valid : ∀ p ∈ primes4, p.Prime := by
  simp only [primes4, List.forall_mem_cons]
  exact ⟨by norm_num,
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 89] }]),
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11, 733] }]),
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7] }]),
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 131] }]),
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 23] }]),
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37] }]),
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 359] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 131] }]), by simp⟩

@[expose] noncomputable def primes5 : List ℕ := [337, 9631, 367, 967, 8269, 398581, 14713, 3500201, 10378063, 83, 743, 104281, 39103, 1361, 571, 659, 10303, 1451, 431, 521, 449, 13441, 14939, 821]

theorem primes5_valid : ∀ p ∈ primes5, p.Prime := by
  simp only [primes5, List.forall_mem_cons]
  exact ⟨by norm_num,
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 107] }]),
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 613] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 37, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 179, 3221] }, .lucas { root := 10, primeFactors := [2, 5, 7, 23] }]),
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 5, 11, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 17] }]),
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 29] }]),
    by norm_num,
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 11, 97] }]),
    by norm_num, by simp⟩

@[expose] noncomputable def primes6 : List ℕ := [691, 4751, 1609669, 917087137, 1699, 193, 277, 1801, 17923, 175897, 262209281, 137, 197, 88741, 5229043, 1291, 22406023, 1811, 4051, 19531, 2180921, 3571, 443, 811]

theorem primes6_valid : ∀ p ∈ primes6, p.Prime := by
  simp only [primes6, List.forall_mem_cons]
  exact ⟨by norm_num,
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 61, 733] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 19, 31, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 283] }]),
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 127, 1613] }, .lucas { root := 3, primeFactors := [2, 13, 31] }]),
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 7, 13, 61, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 263, 4733] }, .lucas { root := 5, primeFactors := [2, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 7789] }, .lucas { root := 2, primeFactors := [2, 3, 11, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 17] }]),
    by norm_num,
    by norm_num, by simp⟩

@[expose] noncomputable def primes7 : List ℕ := [10687, 28729, 251, 3187, 1141081, 673, 14083, 263, 4561, 14009, 1866871, 1153, 1471, 3541, 5209, 937, 3798019, 1009, 5233, 13267, 463, 2663, 7699, 830833]

theorem primes7_valid : ∀ p ∈ primes7, p.Prime := by
  simp only [primes7, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 7, 19] }]),
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 37, 257] }]),
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2347] }, .lucas { root := 3, primeFactors := [2, 3, 17, 23] }]),
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 17, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 20743] }, .lucas { root := 5, primeFactors := [2, 3, 3457] }, .lucas { root := 7, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 7, 31] }]),
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43, 701] }]),
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 67] }]),
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1283] }, .lucas { root := 2, primeFactors := [2, 641] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 19, 911] }]), by simp⟩

@[expose] noncomputable def primes8 : List ℕ := [11299, 33151, 947, 8647, 461, 13537, 21491, 491, 1483, 6101, 8387, 12011, 24517, 42407, 39449441, 421, 3491, 4271, 187123, 3348577, 1231, 17707, 50359, 70001]

theorem primes8_valid : ∀ p ∈ primes8, p.Prime := by
  simp only [primes8, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 269] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 17] }]),
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 131] }]),
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 307] }]),
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 599] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1201] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 13, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 79, 3121] }, .lucas { root := 7, primeFactors := [2, 3, 5, 13] }]),
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 2399] }, .lucas { root := 11, primeFactors := [2, 11, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 11, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7] }]), by simp⟩

@[expose] noncomputable def primes9 : List ℕ := [25646167, 32668561, 727, 1597, 1871, 5839, 18041, 88009573, 59, 1657, 2281, 4651, 55897, 151841, 1774921, 7561, 2384047, 1459, 12503, 13080080081, 52379047267, 373, 499, 2467]

theorem primes9_valid : ∀ p ∈ primes9, p.Prime := by
  simp only [primes9, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 13, 17, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 17, 157] }]),
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 7, 337, 3109] }, .lucas { root := 6, primeFactors := [2, 3, 7, 37] }]),
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 7, 2113] }, .lucas { root := 5, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 17, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 19, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 71, 1433, 1607] }, .lucas { root := 3, primeFactors := [2, 179] }, .lucas { root := 5, primeFactors := [2, 11, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 31, 61, 97, 523] }]),
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 137] }]), by simp⟩

@[expose] noncomputable def primes10 : List ℕ := [4027, 5479, 6491, 11807, 19571, 37861, 264031, 1645747, 249561007, 2671, 4049, 29251, 878837, 5336717, 16148168401, 311, 487, 953, 3217, 4591, 552793, 1957650063931, 283, 8527]

theorem primes10_valid : ∀ p ∈ primes10, p.Prime := by
  simp only [primes10, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 5903] }, .lucas { root := 5, primeFactors := [2, 13, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 19, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 631] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 13, 677] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 59, 4649] }, .lucas { root := 3, primeFactors := [2, 7, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2633, 15797] }, .lucas { root := 3, primeFactors := [2, 7, 47] }, .lucas { root := 2, primeFactors := [2, 11, 359] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 31387] }, .lucas { root := 2, primeFactors := [2, 3, 5231] }, .lucas { root := 7, primeFactors := [2, 5, 523] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11, 17327] }, .lucas { root := 5, primeFactors := [2, 8663] }, .lucas { root := 5, primeFactors := [2, 61, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 5, 7, 13, 19, 43, 181] }]),
    by norm_num,
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 31, 743] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 107, 1129, 16369] }, .lucas { root := 11, primeFactors := [2, 3, 47] }, .lucas { root := 7, primeFactors := [2, 3, 11, 31] }]),
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 29] }]), by simp⟩

@[expose] noncomputable def primes11 : List ℕ := [10847, 20161, 1956611, 381510691, 223, 3121, 3697, 4159, 7673, 11831, 21787, 368089, 579281, 990151, 5390701, 22996651, 3158528101, 647, 1429, 2179, 11503, 22079, 31747594185191, 227]

theorem primes11_valid : ∀ p ∈ primes11, p.Prime := by
  simp only [primes11, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 17, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 23, 47, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 19, 71, 857] }]),
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 3631] }, .lucas { root := 15, primeFactors := [2, 3, 5, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 313] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 13, 557] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 7, 23, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 17, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 19, 8069] }, .lucas { root := 2, primeFactors := [2, 2017] }, .lucas { root := 5, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 127, 911] }]),
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 19, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 13, 244212262963] }, .lucas { root := 3, primeFactors := [2, 3, 19, 3001, 713833] }, .lucas { root := 14, primeFactors := [2, 3, 5] }, .lucas { root := 5, primeFactors := [2, 3, 7, 607] }]),
    by norm_num, by simp⟩

@[expose] noncomputable def primes12 : List ℕ := [241, 577, 677, 2083, 2381, 2503, 3637, 15731, 24571, 47251, 86353, 363889, 570821, 579883, 12207031, 739, 1381, 1747, 2347, 2633, 3319, 27581, 583367, 672901]

theorem primes12_valid : ∀ p ∈ primes12, p.Prime := by
  simp only [primes12, List.forall_mem_cons]
  exact ⟨by norm_num,
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 347] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 28541] }, .lucas { root := 2, primeFactors := [2, 5, 1427] }, .lucas { root := 2, primeFactors := [2, 23, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 127, 761] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 71, 521] }]),
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 41669] }, .lucas { root := 2, primeFactors := [2, 11, 947] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 2243] }, .lucas { root := 2, primeFactors := [2, 19, 59] }]), by simp⟩

@[expose] noncomputable def primes13 : List ℕ := [2426789, 8715961, 1373, 3011, 4447, 5581, 7603, 24421, 59581, 98887, 293459, 365017, 384481, 973001, 1372537, 5471551, 6619231, 104670301, 26403131021, 661, 2053, 2129, 6781, 7151]

theorem primes13_valid : ∀ p ∈ primes13, p.Prime := by
  simp only [primes13, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 13, 59, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 11, 31, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 11, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 16481] }, .lucas { root := 6, primeFactors := [2, 5, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 13339] }, .lucas { root := 2, primeFactors := [2, 3, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 67, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 1733] }, .lucas { root := 2, primeFactors := [2, 433] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 73547] }, .lucas { root := 2, primeFactors := [2, 11, 3343] }, .lucas { root := 5, primeFactors := [2, 3, 557] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 49843] }, .lucas { root := 2, primeFactors := [2, 3, 13, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 188593793] }, .lucas { root := 3, primeFactors := [2, 1473389] }, .lucas { root := 2, primeFactors := [2, 7, 101, 521] }]),
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 11, 13] }]), by simp⟩

@[expose] noncomputable def primes14 : List ℕ := [6038099, 7908811, 47691619, 127159831, 297134095231, 401, 541, 827, 1171, 2311, 3499, 3673, 3691, 6301, 8059, 9439, 12157, 12601, 44983, 108263, 2695351, 3044803, 17311991, 22576753]

theorem primes14_valid : ∀ p ∈ primes14, p.Prime := by
  simp only [primes14, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 23, 11933] }, .lucas { root := 2, primeFactors := [2, 19, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 2897] }, .lucas { root := 3, primeFactors := [2, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 137, 4463] }, .lucas { root := 5, primeFactors := [2, 23, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 17, 31, 383] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 17, 557, 16603] }, .lucas { root := 2, primeFactors := [2, 3, 2767] }, .lucas { root := 3, primeFactors := [2, 3, 461] }]),
    by norm_num,
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1013] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 11, 19, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 17, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 29851] }, .lucas { root := 2, primeFactors := [2, 3, 5, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 1731199] }, .lucas { root := 6, primeFactors := [2, 3, 7, 47, 877] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 4751] }, .lucas { root := 19, primeFactors := [2, 5, 19] }]), by simp⟩

@[expose] noncomputable def primes15 : List ℕ := [323683781, 502628805631, 457, 751, 881, 1279, 1301, 2003, 2069, 3463, 3911, 5641, 6871, 7027, 8971, 63337, 134707, 142591, 6654649, 28792661, 1579264051, 2767631689, 12346432697, 14421466756460791]

theorem primes15_valid : ∀ p ∈ primes15, p.Prime := by
  simp only [primes15, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 2312027] }, .lucas { root := 2, primeFactors := [2, 1156013] }, .lucas { root := 2, primeFactors := [2, 11, 13, 43, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 89, 373, 8011] }, .lucas { root := 14, primeFactors := [2, 3, 5, 89] }]),
    by norm_num,
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 577] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 17, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 229] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1171] }, .lucas { root := 2, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 13, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 7, 11, 13, 277] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13, 37, 41, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 127, 911] }]),
    by primality (cert := .witnesses [.lucas { root := 29, primeFactors := [2, 3, 17, 71, 31847] }, .lucas { root := 5, primeFactors := [2, 15923] }, .lucas { root := 2, primeFactors := [2, 19, 419] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 13, 61, 1123, 1733] }, .lucas { root := 2, primeFactors := [2, 3, 11, 17] }, .lucas { root := 2, primeFactors := [2, 433] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 13, 47, 2903, 90339707] }, .lucas { root := 5, primeFactors := [2, 1451] }, .lucas { root := 2, primeFactors := [2, 5, 29] }, .lucas { root := 2, primeFactors := [2, 45169853] }, .lucas { root := 2, primeFactors := [2, 7, 13, 31, 4003] }, .lucas { root := 2, primeFactors := [2, 3, 23, 29] }]), by simp⟩

@[expose] noncomputable def primes16 : List ℕ := [22280841470107301759731, 619, 1511, 2423, 3041, 4421, 12853, 25307, 30241, 34511, 42337, 53551, 75013, 151201, 184511, 189967, 204781, 212057, 246247, 257611, 307189, 368551, 459007, 492103]

theorem primes16_valid : ∀ p ∈ primes16, p.Prime := by
  simp only [primes16, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 191, 113381713, 293121781] }, .lucas { root := 5, primeFactors := [2, 3, 43, 18311] }, .lucas { root := 13, primeFactors := [2, 5, 1831] }, .lucas { root := 3, primeFactors := [2, 3, 5, 61] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7, 697909] }, .lucas { root := 2, primeFactors := [2, 3, 19, 3061] }, .lucas { root := 6, primeFactors := [2, 3, 5, 17] }]),
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 12653] }, .lucas { root := 2, primeFactors := [2, 3163] }, .lucas { root := 3, primeFactors := [2, 3, 17, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 17, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 19, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 18451] }, .lucas { root := 3, primeFactors := [2, 3, 5, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 4523] }, .lucas { root := 5, primeFactors := [2, 7, 17, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 3413] }, .lucas { root := 2, primeFactors := [2, 853] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 2039] }, .lucas { root := 7, primeFactors := [2, 1019] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11, 13, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 31, 277] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 7, 23, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 113, 677] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 13, 701] }]), by simp⟩

@[expose] noncomputable def primes17 : List ℕ := [900329, 2289401, 9065531, 10332211, 20241187, 62060021, 305175781, 1531, 1567, 1951, 2531, 2791, 3511, 3613, 4729, 6133, 7793, 28447, 45121, 162709, 178601, 262321, 1674289, 3060947]

theorem primes17_valid : ∀ p ∈ primes17, p.Prime := by
  simp only [primes17, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 13, 787] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11447] }, .lucas { root := 5, primeFactors := [2, 59, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 109, 8317] }, .lucas { root := 6, primeFactors := [2, 3, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 49201] }, .lucas { root := 7, primeFactors := [2, 3, 5, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 17, 28349] }, .lucas { root := 2, primeFactors := [2, 19, 373] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 282091] }, .lucas { root := 3, primeFactors := [2, 3, 5, 9403] }, .lucas { root := 3, primeFactors := [2, 3, 1567] }, .lucas { root := 3, primeFactors := [2, 3, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 13, 31, 601] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 487] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 431] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 19, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 1093] }, .lucas { root := 5, primeFactors := [2, 3, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 7, 11, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 131, 1669] }, .lucas { root := 2, primeFactors := [2, 3, 139] }]), by simp⟩

@[expose] noncomputable def primes18 : List ℕ := [9069133, 48037081, 66166691, 208097431, 591694601, 4189129561, 3737657091169, 219241969146019, 178250690949465223, 353, 1013, 1277, 2243, 3019, 3083, 3191, 3719, 3769, 3823, 4231, 7541, 8389, 12211, 14251]

theorem primes18_valid : ∀ p ∈ primes18, p.Prime := by
  simp only [primes18, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 251, 3011] }, .lucas { root := 2, primeFactors := [2, 5, 7, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7, 13, 53, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 29, 151, 1511] }, .lucas { root := 11, primeFactors := [2, 5, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 131, 52951] }, .lucas { root := 3, primeFactors := [2, 3, 5, 353] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 173, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 11, 21589] }, .lucas { root := 2, primeFactors := [2, 3, 7, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 37, primeFactors := [2, 3, 7, 11, 13, 19, 151, 4519] }, .lucas { root := 3, primeFactors := [2, 3, 251] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 7, 13, 17, 61, 307, 140143] }, .lucas { root := 5, primeFactors := [2, 3, 23357] }, .lucas { root := 2, primeFactors := [2, 5839] }, .lucas { root := 6, primeFactors := [2, 3, 7, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 53, 131, 2011, 3851, 5581] }, .lucas { root := 3, primeFactors := [2, 3, 5, 67] }, .lucas { root := 2, primeFactors := [2, 5, 7, 11] }, .lucas { root := 6, primeFactors := [2, 3, 5, 31] }]),
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 503] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 23, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 11, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 19] }]), by simp⟩

@[expose] noncomputable def primes19 : List ℕ := [14437, 21169, 21613, 29989, 33457, 37181, 42073, 49547, 73181, 140813, 147739, 148123, 169691, 237997, 292661, 578267, 733591, 1222567, 2261887, 3093121, 4534567, 6032531, 32009891, 86524531]

theorem primes19_valid : ∀ p ∈ primes19, p.Prime := by
  simp only [primes19, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 401] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1801] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 17, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1753] }, .lucas { root := 7, primeFactors := [2, 3, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 3539] }, .lucas { root := 2, primeFactors := [2, 29, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 3659] }, .lucas { root := 2, primeFactors := [2, 31, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 47, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 24623] }, .lucas { root := 5, primeFactors := [2, 13, 947] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 211] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 71, 239] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 601] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 14633] }, .lucas { root := 3, primeFactors := [2, 31, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 23, 967] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 203761] }, .lucas { root := 11, primeFactors := [2, 3, 5, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 43, 797] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 251, 3011] }, .lucas { root := 2, primeFactors := [2, 5, 7, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 86179] }, .lucas { root := 2, primeFactors := [2, 3, 53, 271] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 290999] }, .lucas { root := 7, primeFactors := [2, 83, 1753] }, .lucas { root := 7, primeFactors := [2, 3, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 2884151] }, .lucas { root := 7, primeFactors := [2, 5, 37, 1559] }, .lucas { root := 19, primeFactors := [2, 19, 41] }]), by simp⟩

@[expose] noncomputable def primes20 : List ℕ := [604842197, 3202878953, 2141993519227, 751670559138758105956097, 154522673919080310634923725508989347, 823, 839, 853, 919, 1237, 1741, 1787, 1831, 2017, 2267, 2393, 2591, 3323, 3529, 8933, 8951, 9967, 11701, 12893]

theorem primes20_valid : ∀ p ∈ primes20, p.Prime := by
  simp only [primes20, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 131, 269, 613] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 13, 37, 118907] }, .lucas { root := 2, primeFactors := [2, 59453] }, .lucas { root := 2, primeFactors := [2, 89, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17, 71, 101, 88741] }, .lucas { root := 2, primeFactors := [2, 3, 5, 17, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 17, 31, 37, 409, 1129, 25085030513] }, .lucas { root := 11, primeFactors := [2, 3, 47] }, .lucas { root := 3, primeFactors := [2, 1229, 1275683] }, .lucas { root := 2, primeFactors := [2, 307] }, .lucas { root := 2, primeFactors := [2, 637841] }, .lucas { root := 21, primeFactors := [2, 5, 7, 17, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 7, 13, 43, 47, 67, 271, 7793, 732541, 15349897, 88013053] }, .lucas { root := 3, primeFactors := [2, 487] }, .lucas { root := 10, primeFactors := [2, 3, 5, 29, 421] }, .lucas { root := 5, primeFactors := [2, 3, 213193] }, .lucas { root := 5, primeFactors := [2, 3, 7, 47] }, .lucas { root := 2, primeFactors := [2, 3, 1009, 2423] }, .lucas { root := 5, primeFactors := [2, 7, 173] }]),
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 11, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 293] }]), by simp⟩

@[expose] noncomputable def primes21 : List ℕ := [13001, 24509, 27457, 28057, 29683, 40751, 44371, 55829, 56773, 72931, 85121, 292969, 337901, 360851, 473201, 522061, 1129019, 1477807, 1509997, 1902839, 69655517, 157920029, 1478526139, 4164418987]

theorem primes21_valid : ∀ p ∈ primes21, p.Prime := by
  simp only [primes21, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 557] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 17, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 163] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 821] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 11, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 13, 313] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 31, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 1031] }, .lucas { root := 14, primeFactors := [2, 5, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 11, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 19, 37, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 22391] }, .lucas { root := 13, primeFactors := [2, 5, 2239] }, .lucas { root := 3, primeFactors := [2, 3, 373] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 5471] }, .lucas { root := 7, primeFactors := [2, 5, 547] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 7, 199, 683] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 2487697] }, .lucas { root := 5, primeFactors := [2, 3, 51827] }, .lucas { root := 2, primeFactors := [2, 25913] }, .lucas { root := 3, primeFactors := [2, 41, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 41, 151, 911] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 419, 196039] }, .lucas { root := 3, primeFactors := [2, 3, 10891] }, .lucas { root := 2, primeFactors := [2, 3, 5, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13, 7627141] }, .lucas { root := 13, primeFactors := [2, 3, 5, 42373] }, .lucas { root := 5, primeFactors := [2, 3, 11, 107] }]), by simp⟩

@[expose] noncomputable def primes22 : List ℕ := [19828441783, 232611722621, 1653850268201, 829007553280001, 50544702849929377, 241562563680036301, 6765811783780036261, 18855337777262169791, 195163150047313020008802835877656364030813707064261, 709, 1021, 1181, 1409, 1667, 2383, 2551, 2731, 2969, 3301, 3889, 4091, 4657, 5531, 6427]

theorem primes22_valid : ∀ p ∈ primes22, p.Prime := by
  simp only [primes22, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7823, 140813] }, .lucas { root := 5, primeFactors := [2, 3911] }, .lucas { root := 13, primeFactors := [2, 5, 17, 23] }, .lucas { root := 2, primeFactors := [2, 7, 47, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 389, 3767, 7937] }, .lucas { root := 5, primeFactors := [2, 7, 269] }, .lucas { root := 3, primeFactors := [2, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13, 23, 27656359] }, .lucas { root := 3, primeFactors := [2, 3, 4609393] }, .lucas { root := 5, primeFactors := [2, 3, 109, 881] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 229, 2828219] }, .lucas { root := 2, primeFactors := [2, 23, 61483] }, .lucas { root := 2, primeFactors := [2, 3, 10247] }, .lucas { root := 5, primeFactors := [2, 47, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 17, 61, 7321, 6304673] }, .lucas { root := 7, primeFactors := [2, 3, 5, 61] }, .lucas { root := 3, primeFactors := [2, 11, 17911] }, .lucas { root := 3, primeFactors := [2, 3, 5, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 13, 17, 3643477581901] }, .lucas { root := 2, primeFactors := [2, 3, 5, 13, 17, 31, 1772723] }, .lucas { root := 2, primeFactors := [2, 7, 18089] }, .lucas { root := 3, primeFactors := [2, 7, 17, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 13, 19, 31, 37, 43, 67, 137, 144061] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 67, 28142295189943537] }, .lucas { root := 5, primeFactors := [2, 3, 7, 17, 547430267467] }, .lucas { root := 2, primeFactors := [2, 3, 31, 981057827] }, .lucas { root := 2, primeFactors := [2, 7, 70075559] }, .lucas { root := 7, primeFactors := [2, 7, 37, 135281] }, .lucas { root := 6, primeFactors := [2, 5, 19, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 443, 557, 843714919, 93826513133, 133655902201, 3737657091169] }, .lucas { root := 3, primeFactors := [2, 3, 46873051] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7, 44641] }, .lucas { root := 19, primeFactors := [2, 3, 5, 31] }, .lucas { root := 2, primeFactors := [2, 11, 2132420753] }, .lucas { root := 3, primeFactors := [2, 7, 11, 157351] }, .lucas { root := 21, primeFactors := [2, 3, 5, 1049] }, .lucas { root := 3, primeFactors := [2, 131] }, .lucas { root := 17, primeFactors := [2, 3, 5, 47, 526619] }, .lucas { root := 2, primeFactors := [2, 179, 1471] }, .lucas { root := 6, primeFactors := [2, 3, 5, 7] }, .lucas { root := 37, primeFactors := [2, 3, 7, 11, 13, 19, 151, 4519] }, .lucas { root := 3, primeFactors := [2, 3, 251] }]),
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 397] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 409] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 7, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 17] }]), by simp⟩

@[expose] noncomputable def primes23 : List ℕ := [6991, 7393, 8431, 8581, 8719, 8893, 9851, 10133, 11551, 14281, 16651, 18313, 22093, 28099, 28537, 37363, 37507, 38047, 38611, 48541, 51343, 66683, 78049, 79231]

theorem primes23_valid : ∀ p ∈ primes23, p.Prime := by
  simp only [primes23, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 281] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1453] }, .lucas { root := 2, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 263] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 223] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 29, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 479] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 7, 19, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 373] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 809] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 43, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 11, 433] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 271] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 19, 139] }]), by simp⟩

@[expose] noncomputable def primes24 : List ℕ := [128341, 146407, 260191, 264581, 286001, 1080091, 1460743, 2332903, 7063513, 42759529, 168820969, 223188661, 4400521837, 153436090543, 875296605041, 304018940824561, 27935336611728311, 398341412240537151131351, 141451988078598368963321713, 349, 607, 643, 683, 769]

theorem primes24_valid : ∀ p ∈ primes24, p.Prime := by
  simp only [primes24, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 23, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 1877] }, .lucas { root := 2, primeFactors := [2, 7, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13229] }, .lucas { root := 2, primeFactors := [2, 3307] }, .lucas { root := 2, primeFactors := [2, 3, 19, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11, 1091] }, .lucas { root := 2, primeFactors := [2, 5, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 14321] }, .lucas { root := 3, primeFactors := [2, 5, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 13, 2719] }, .lucas { root := 3, primeFactors := [2, 3, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 294313] }, .lucas { root := 10, primeFactors := [2, 3, 12263] }, .lucas { root := 5, primeFactors := [2, 6131] }, .lucas { root := 2, primeFactors := [2, 5, 613] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 199, 1279] }, .lucas { root := 3, primeFactors := [2, 3, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 73, 167, 577] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 83, 14939] }, .lucas { root := 2, primeFactors := [2, 7, 11, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 366710153] }, .lucas { root := 3, primeFactors := [2, 45838769] }, .lucas { root := 3, primeFactors := [2, 151, 18973] }, .lucas { root := 2, primeFactors := [2, 3, 17, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 37, 73, 751, 1801] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 13, 967, 7193] }, .lucas { root := 3, primeFactors := [2, 29, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 13, 10826885357] }, .lucas { root := 2, primeFactors := [2, 7, 55239211] }, .lucas { root := 2, primeFactors := [2, 3, 5, 13, 31, 1523] }, .lucas { root := 2, primeFactors := [2, 761] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 19, 71, 16811, 123182329] }, .lucas { root := 7, primeFactors := [2, 5, 41] }, .lucas { root := 11, primeFactors := [2, 3, 5132597] }, .lucas { root := 2, primeFactors := [2, 7, 183307] }, .lucas { root := 2, primeFactors := [2, 3, 137, 223] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 11, 23, 229, 251101831, 547620341] }, .lucas { root := 6, primeFactors := [2, 3, 5, 7, 1195723] }, .lucas { root := 2, primeFactors := [2, 3, 11, 61] }, .lucas { root := 10, primeFactors := [2, 5, 23, 29, 41051] }, .lucas { root := 2, primeFactors := [2, 5, 821] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 13, 19, 61, 151, 877, 1093, 22651, 8522341] }, .lucas { root := 5, primeFactors := [2, 3, 7, 13] }, .lucas { root := 3, primeFactors := [2, 3, 5, 151] }, .lucas { root := 2, primeFactors := [2, 3, 5, 142039] }, .lucas { root := 3, primeFactors := [2, 3, 13, 607] }]),
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num, by simp⟩

@[expose] noncomputable def primes25 : List ℕ := [941, 997, 1061, 1151, 1489, 1559, 1609, 1613, 1933, 2029, 2081, 2131, 2251, 2617, 2647, 2683, 2857, 2971, 3137, 4261, 4327, 4759, 6221, 6547]

theorem primes25_valid : ∀ p ∈ primes25, p.Prime := by
  simp only [primes25, List.forall_mem_cons]
  exact ⟨by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 19, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 311] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1091] }, .lucas { root := 2, primeFactors := [2, 5, 109] }]), by simp⟩

@[expose] noncomputable def primes26 : List ℕ := [6553, 7219, 7547, 8353, 9319, 9437, 9791, 10837, 10979, 11987, 12377, 13729, 13931, 15263, 15269, 15809, 15971, 16661, 16729, 19441, 19993, 22271, 23189, 28387]

theorem primes26_valid : ∀ p ∈ primes26, p.Prime := by
  simp only [primes26, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 401] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1553] }, .lucas { root := 3, primeFactors := [2, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 337] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 11, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 499] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 461] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 7, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 587] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 347] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1597] }, .lucas { root := 11, primeFactors := [2, 3, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 17, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 17, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 17, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 83] }]), by simp⟩

@[expose] noncomputable def primes27 : List ℕ := [30103, 36389, 42967, 43177, 43609, 52837, 55333, 67411, 84449, 111187, 158341, 202519, 299861, 336901, 499607, 689261, 915769, 1386659, 1589299, 1717451, 1803647, 2624353, 2792809, 3297113]

theorem primes27_valid : ∀ p ∈ primes27, p.Prime := by
  simp only [primes27, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 29, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 827] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 23, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 17, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 29, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 13, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 29, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11251] }, .lucas { root := 13, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 29, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 1123] }, .lucas { root := 2, primeFactors := [2, 3, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 23, 10861] }, .lucas { root := 2, primeFactors := [2, 3, 5, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 5, 11, 13, 241] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 23, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 13, 19, 401] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 37, 7159] }, .lucas { root := 3, primeFactors := [2, 3, 1193] }, .lucas { root := 3, primeFactors := [2, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 701] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 69371] }, .lucas { root := 2, primeFactors := [2, 5, 7, 991] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 27337] }, .lucas { root := 5, primeFactors := [2, 3, 17, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 79, 491] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 13, 647] }]), by simp⟩

@[expose] noncomputable def primes28 : List ℕ := [4760281, 7094233, 9170197, 22939801, 29387639, 31179359, 34770289, 63284371, 72577051, 85581973, 133338869, 135495361, 148768021, 250291159, 366340651, 466344409, 656276671, 37028483467, 50689400581, 145159381141, 171686630257, 395950646197, 934415109937, 4534166740403]

theorem primes28_valid : ∀ p ∈ primes28, p.Prime := by
  simp only [primes28, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 7, 1889] }, .lucas { root := 3, primeFactors := [2, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 37, 2663] }, .lucas { root := 5, primeFactors := [2, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 109169] }, .lucas { root := 3, primeFactors := [2, 6823] }, .lucas { root := 3, primeFactors := [2, 3, 379] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 13, 17, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 1427, 1471] }, .lucas { root := 2, primeFactors := [2, 23, 31] }, .lucas { root := 6, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 227, 9811] }, .lucas { root := 3, primeFactors := [2, 3, 5, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 103483] }, .lucas { root := 2, primeFactors := [2, 3, 5749] }, .lucas { root := 2, primeFactors := [2, 3, 479] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 124087] }, .lucas { root := 3, primeFactors := [2, 3, 20681] }, .lucas { root := 3, primeFactors := [2, 5, 11, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 409] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 479, 709] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 29, 3049] }, .lucas { root := 11, primeFactors := [2, 3, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 7, 11, 13, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 17, 61, 797] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 73, 113, 389] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 17, 43, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 17, 31, 36871] }, .lucas { root := 15, primeFactors := [2, 3, 5, 1229] }, .lucas { root := 2, primeFactors := [2, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 17, 29, 2113] }, .lucas { root := 5, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 474724147] }, .lucas { root := 2, primeFactors := [2, 3, 13, 1553, 3919] }, .lucas { root := 3, primeFactors := [2, 97] }, .lucas { root := 3, primeFactors := [2, 3, 653] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 13, 61, 97, 523] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 103, 617, 38069] }, .lucas { root := 2, primeFactors := [2, 31, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 373, 9589289] }, .lucas { root := 3, primeFactors := [2, 1198661] }, .lucas { root := 2, primeFactors := [2, 5, 73, 821] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 2311, 226631] }, .lucas { root := 3, primeFactors := [2, 3, 5, 7, 11] }, .lucas { root := 13, primeFactors := [2, 5, 131, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 7, 11, 43, 151, 12979] }, .lucas { root := 2, primeFactors := [2, 3, 7, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 19, 15913, 576791] }, .lucas { root := 5, primeFactors := [2, 3, 13, 17] }, .lucas { root := 13, primeFactors := [2, 5, 57679] }, .lucas { root := 3, primeFactors := [2, 3, 9613] }, .lucas { root := 2, primeFactors := [2, 3, 89] }]), by simp⟩

@[expose] noncomputable def primes29 : List ℕ := [11016462577051, 18944890940537, 138161295607249, 2703853428809791, 40911050578149780601, 1809873235795386729241, 2346320474383711003267, 120547934639675608922684101, 2041648288605040221889024691, 1247451159302262598804596798564656994853573, 1137043309874106587329369739133088789635301921798771999, 107, 167, 233, 1091, 1201, 1327, 1549, 1579, 1607, 1709, 1721, 1753, 1861]

theorem primes29_valid : ∀ p ∈ primes29, p.Prime := by
  simp only [primes29, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 31, 103, 149, 7351] }, .lucas { root := 6, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 109, 149, 1205047] }, .lucas { root := 3, primeFactors := [2, 3, 66947] }, .lucas { root := 2, primeFactors := [2, 11, 17, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 959453441717] }, .lucas { root := 5, primeFactors := [2, 7, 11, 17, 19, 1377757] }, .lucas { root := 5, primeFactors := [2, 3, 12757] }, .lucas { root := 2, primeFactors := [2, 3, 1063] }, .lucas { root := 3, primeFactors := [2, 3, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 137, 657871880489] }, .lucas { root := 3, primeFactors := [2, 82233985061] }, .lucas { root := 2, primeFactors := [2, 5, 149, 27595297] }, .lucas { root := 5, primeFactors := [2, 3, 19, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 11, 13, 37, 43, 139, 631, 3416953] }, .lucas { root := 13, primeFactors := [2, 3, 7, 11, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 7, 13, 59, 163, 1741, 3541, 931837] }, .lucas { root := 2, primeFactors := [2, 3, 5, 29] }, .lucas { root := 7, primeFactors := [2, 3, 5, 59] }, .lucas { root := 2, primeFactors := [2, 3, 19, 61, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 23, 71, 101, 137, 881, 5591, 319411] }, .lucas { root := 11, primeFactors := [2, 5, 13, 43] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 17, 31, 73, 103, 149, 653, 7351, 519349] }, .lucas { root := 6, primeFactors := [2, 3, 5, 7] }, .lucas { root := 2, primeFactors := [2, 3, 113, 383] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 1031, 1811, 29014303, 76912263247] }, .lucas { root := 14, primeFactors := [2, 5, 103] }, .lucas { root := 6, primeFactors := [2, 5, 181] }, .lucas { root := 13, primeFactors := [2, 3, 4835717] }, .lucas { root := 2, primeFactors := [2, 757, 1597] }, .lucas { root := 11, primeFactors := [2, 3, 7, 19] }, .lucas { root := 6, primeFactors := [2, 3, 7, 13, 109, 1292339] }, .lucas { root := 2, primeFactors := [2, 646169] }, .lucas { root := 3, primeFactors := [2, 37, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 73, 179, 857, 3221, 3643, 6053, 10378063, 107637315400441] }, .lucas { root := 10, primeFactors := [2, 5, 7, 23] }, .lucas { root := 2, primeFactors := [2, 3, 607] }, .lucas { root := 2, primeFactors := [2, 17, 89] }, .lucas { root := 11, primeFactors := [2, 3, 179, 3221] }, .lucas { root := 19, primeFactors := [2, 3, 5, 7, 23, 179, 3221] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 11, 13, 4441901338060465343, 99448802215121337100401104792839] }, .lucas { root := 5, primeFactors := [2, 7, 117242539, 2706173627] }, .lucas { root := 2, primeFactors := [2, 3, 7, 787, 3547] }, .lucas { root := 2, primeFactors := [2, 3, 197] }, .lucas { root := 6, primeFactors := [2, 13, 1459, 71339] }, .lucas { root := 3, primeFactors := [2, 3] }, .lucas { root := 2, primeFactors := [2, 53, 673] }, .lucas { root := 13, primeFactors := [2, 3, 131413, 32767877, 1283040652669610291] }, .lucas { root := 2, primeFactors := [2, 3, 47, 233] }, .lucas { root := 2, primeFactors := [2, 8191969] }, .lucas { root := 13, primeFactors := [2, 3, 85333] }, .lucas { root := 5, primeFactors := [2, 3, 13, 547] }, .lucas { root := 2, primeFactors := [2, 5, 31, 54366643, 76128313] }, .lucas { root := 2, primeFactors := [2, 3, 11, 274579] }, .lucas { root := 2, primeFactors := [2, 3, 45763] }, .lucas { root := 5, primeFactors := [2, 3, 29, 263] }, .lucas { root := 11, primeFactors := [2, 3, 13, 17, 31, 463] }]),
    by norm_num,
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 263] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 31] }]), by simp⟩

@[expose] noncomputable def primes30 : List ℕ := [1873, 1877, 1879, 1973, 1999, 2063, 2269, 2287, 2293, 2297, 2333, 2351, 2377, 2543, 2687, 2843, 2851, 3067, 3229, 3271, 3307, 3389, 3391, 4567]

theorem primes30_valid : ∀ p ∈ primes30, p.Prime := by
  simp only [primes30, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 313] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 1031] }, .lucas { root := 14, primeFactors := [2, 5, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 191] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 31, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 17, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 269] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 761] }]), by simp⟩

@[expose] noncomputable def primes31 : List ℕ := [4603, 4783, 4993, 5591, 5827, 6163, 6217, 6271, 6689, 6733, 6961, 7057, 7621, 7717, 7823, 8191, 8807, 9241, 9257, 9431, 9871, 10151, 10949, 11047]

theorem primes31_valid : ∀ p ∈ primes31, p.Prime := by
  simp only [primes31, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 797] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 13, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 971] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 11, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 643] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3911] }, .lucas { root := 13, primeFactors := [2, 5, 17, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 17, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 23, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 17, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 263] }]), by simp⟩

end OddPerfect.FactorBudget.Count45
