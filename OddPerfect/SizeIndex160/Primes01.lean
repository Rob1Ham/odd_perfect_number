module

public import OddPerfect.IndexReplay
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.IndexComponent.Size160

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def bankLeaf1 : PrimeBank := .leaf [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59]

theorem bankLeaf1_valid : bankLeaf1.Certified := by
  simp only [bankLeaf1, PrimeBank.Certified, List.forall_mem_cons]
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
    by norm_num, by simp⟩

@[expose] noncomputable def bankLeaf2 : PrimeBank := .leaf [61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 109, 113, 127, 131, 139, 151]

theorem bankLeaf2_valid : bankLeaf2.Certified := by
  simp only [bankLeaf2, PrimeBank.Certified, List.forall_mem_cons]
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
    by norm_num, by simp⟩

@[expose] noncomputable def bankLeaf3 : PrimeBank := .leaf [157, 163, 179, 181, 191, 193, 199, 211, 223, 227, 233, 241, 251, 263, 271, 277]

theorem bankLeaf3_valid : bankLeaf3.Certified := by
  simp only [bankLeaf3, PrimeBank.Certified, List.forall_mem_cons]
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
    by norm_num, by simp⟩

@[expose] noncomputable def bankLeaf4 : PrimeBank := .leaf [281, 283, 307, 311, 313, 317, 331, 337, 349, 353, 367, 373, 379, 397, 409, 421]

theorem bankLeaf4_valid : bankLeaf4.Certified := by
  simp only [bankLeaf4, PrimeBank.Certified, List.forall_mem_cons]
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
    by norm_num, by simp⟩

@[expose] noncomputable def bankLeaf5 : PrimeBank := .leaf [433, 439, 443, 449, 457, 463, 467, 487, 491, 499, 521, 541, 547, 557, 571, 577]

theorem bankLeaf5_valid : bankLeaf5.Certified := by
  simp only [bankLeaf5, PrimeBank.Certified, List.forall_mem_cons]
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
    by norm_num, by simp⟩

@[expose] noncomputable def bankLeaf6 : PrimeBank := .leaf [599, 601, 613, 617, 619, 631, 643, 661, 673, 683, 701, 709, 727, 733, 739, 751]

theorem bankLeaf6_valid : bankLeaf6.Certified := by
  simp only [bankLeaf6, PrimeBank.Certified, List.forall_mem_cons]
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
    by norm_num, by simp⟩

@[expose] noncomputable def bankLeaf7 : PrimeBank := .leaf [757, 769, 811, 823, 827, 859, 877, 881, 883, 907, 911, 967, 991, 1009, 1021, 1031]

theorem bankLeaf7_valid : bankLeaf7.Certified := by
  simp only [bankLeaf7, PrimeBank.Certified, List.forall_mem_cons]
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
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 103] }]), by simp⟩

@[expose] noncomputable def bankLeaf8 : PrimeBank := .leaf [1033, 1051, 1063, 1087, 1091, 1093, 1117, 1123, 1201, 1231, 1237, 1279, 1291, 1301, 1303, 1321]

theorem bankLeaf8_valid : bankLeaf8.Certified := by
  simp only [bankLeaf8, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 11] }]), by simp⟩

@[expose] noncomputable def bankLeaf9 : PrimeBank := .leaf [1373, 1381, 1409, 1423, 1429, 1453, 1471, 1481, 1483, 1499, 1511, 1549, 1567, 1583, 1597, 1609]

theorem bankLeaf9_valid : bankLeaf9.Certified := by
  simp only [bankLeaf9, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 67] }]), by simp⟩

@[expose] noncomputable def bankLeaf10 : PrimeBank := .leaf [1613, 1621, 1693, 1721, 1723, 1783, 1787, 1801, 1811, 1831, 1867, 1871, 1873, 1879, 1973, 1987]

theorem bankLeaf10_valid : bankLeaf10.Certified := by
  simp only [bankLeaf10, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 311] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 313] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 331] }]), by simp⟩

@[expose] noncomputable def bankLeaf11 : PrimeBank := .leaf [2011, 2017, 2053, 2081, 2083, 2089, 2131, 2161, 2203, 2281, 2287, 2339, 2347, 2351, 2371, 2377]

theorem bankLeaf11_valid : bankLeaf11.Certified := by
  simp only [bankLeaf11, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 347] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 367] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11] }]), by simp⟩

@[expose] noncomputable def bankLeaf12 : PrimeBank := .leaf [2389, 2423, 2467, 2539, 2591, 2617, 2647, 2659, 2791, 2801, 2833, 2851, 2857, 2927, 2971, 3001]

theorem bankLeaf12_valid : bankLeaf12.Certified := by
  simp only [bankLeaf12, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 443] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 11, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5] }]), by simp⟩

@[expose] noncomputable def bankLeaf13 : PrimeBank := .leaf [3109, 3137, 3169, 3187, 3191, 3221, 3259, 3271, 3313, 3373, 3389, 3499, 3511, 3529, 3631, 3691]

theorem bankLeaf13_valid : bankLeaf13.Certified := by
  simp only [bankLeaf13, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 11, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 281] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 5, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 41] }]), by simp⟩

@[expose] noncomputable def bankLeaf14 : PrimeBank := .leaf [3727, 3739, 3823, 3851, 3889, 3911, 4021, 4027, 4051, 4099, 4111, 4261, 4357, 4441, 4561, 4567]

theorem bankLeaf14_valid : bankLeaf14.Certified := by
  simp only [bankLeaf14, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 7, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 17, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 683] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 21, primeFactors := [2, 3, 5, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 761] }]), by simp⟩

@[expose] noncomputable def bankLeaf15 : PrimeBank := .leaf [4583, 4591, 4621, 4729, 4733, 4783, 4801, 4817, 4831, 4933, 4987, 5023, 5101, 5107, 5119, 5197]

theorem bankLeaf15_valid : bankLeaf15.Certified := by
  simp only [bankLeaf15, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 29, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 797] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 277] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 853] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 433] }]), by simp⟩

@[expose] noncomputable def bankLeaf16 : PrimeBank := .leaf [5231, 5233, 5279, 5413, 5419, 5521, 5623, 5743, 5779, 5827, 6037, 6043, 6073, 6121, 6163, 6199]

theorem bankLeaf16_valid : bankLeaf16.Certified := by
  simp only [bankLeaf16, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 523] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 13, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 937] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 971] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 503] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1033] }, .lucas { root := 5, primeFactors := [2, 3, 43] }]), by simp⟩

@[expose] noncomputable def bankLeaf17 : PrimeBank := .leaf [6301, 6343, 6421, 6491, 6733, 6781, 6829, 6967, 6991, 7057, 7069, 7151, 7351, 7489, 7541, 7547]

theorem bankLeaf17_valid : bankLeaf17.Certified := by
  simp only [bankLeaf17, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 569] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 11] }]), by simp⟩

@[expose] noncomputable def bankLeaf18 : PrimeBank := .leaf [7561, 7741, 7907, 8081, 8179, 8191, 8263, 8269, 8353, 8431, 8647, 9109, 9157, 9181, 9277, 9461]

theorem bankLeaf18_valid : bankLeaf18.Certified := by
  simp only [bankLeaf18, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 59, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 281] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 773] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 43] }]), by simp⟩

@[expose] noncomputable def bankLeaf19 : PrimeBank := .leaf [9511, 9781, 9857, 9949, 9967, 9973, 10091, 10181, 10271, 10303, 10391, 10651, 10789, 11083, 11239, 11311]

theorem bankLeaf19_valid : bankLeaf19.Certified := by
  simp only [bankLeaf19, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 317] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 163] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 829] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 277] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1009] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 509] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 13, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 5, 1039] }, .lucas { root := 3, primeFactors := [2, 3, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1847] }, .lucas { root := 5, primeFactors := [2, 13, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1873] }, .lucas { root := 10, primeFactors := [2, 3, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 29] }]), by simp⟩

@[expose] noncomputable def bankLeaf20 : PrimeBank := .leaf [11719, 11807, 12097, 12109, 12253, 12277, 12301, 12373, 12637, 12973, 13001, 13267, 13567, 13723, 13931, 14009]

theorem bankLeaf20_valid : bankLeaf20.Certified := by
  simp only [bankLeaf20, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 5903] }, .lucas { root := 5, primeFactors := [2, 13, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 1009] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1021] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1031] }, .lucas { root := 14, primeFactors := [2, 5, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 23, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 17, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 2287] }, .lucas { root := 19, primeFactors := [2, 3, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 17, 103] }]), by simp⟩

@[expose] noncomputable def bankLeaf21 : PrimeBank := .leaf [14011, 14083, 14251, 14281, 14327, 14389, 14401, 14621, 14797, 14821, 14891, 14939, 15101, 15401, 15451, 15541]

theorem bankLeaf21_valid : bankLeaf21.Certified := by
  simp only [bankLeaf21, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 467] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2347] }, .lucas { root := 3, primeFactors := [2, 3, 17, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 19, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1489] }, .lucas { root := 14, primeFactors := [2, 3, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 11, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 37] }]), by simp⟩

@[expose] noncomputable def bankLeaf22 : PrimeBank := .leaf [15667, 15901, 16057, 16141, 16651, 17293, 17299, 17351, 17431, 17509, 17599, 17707, 17923, 17959, 17971, 18041]

theorem bankLeaf22_valid : bankLeaf22.Certified := by
  simp only [bankLeaf22, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 373] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 223] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 269] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 347] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1459] }, .lucas { root := 3, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 419] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 41, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 599] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 41] }]), by simp⟩

@[expose] noncomputable def bankLeaf23 : PrimeBank := .leaf [18541, 18661, 19531, 19571, 20101, 20161, 20323, 20431, 20707, 20857, 20959, 21019, 21143, 21211, 21487, 21491]

theorem bankLeaf23_valid : bankLeaf23.Certified := by
  simp only [bankLeaf23, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 311] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 19, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1129] }, .lucas { root := 11, primeFactors := [2, 3, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 17, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 7, 499] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 31, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 11, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 3581] }, .lucas { root := 2, primeFactors := [2, 5, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 307] }]), by simp⟩

@[expose] noncomputable def bankLeaf24 : PrimeBank := .leaf [21529, 21577, 21787, 21863, 22063, 22511, 22543, 22571, 23269, 24061, 24077, 25621, 25981, 26479, 26683, 26801]

theorem bankLeaf24_valid : bankLeaf24.Certified := by
  simp only [bankLeaf24, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 13, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 29, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 3631] }, .lucas { root := 15, primeFactors := [2, 3, 5, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 17, 643] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 3677] }, .lucas { root := 2, primeFactors := [2, 919] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 2251] }, .lucas { root := 7, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 37, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 277] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 401] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 463] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 433] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1471] }, .lucas { root := 6, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 4447] }, .lucas { root := 3, primeFactors := [2, 3, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 67] }]), by simp⟩

@[expose] noncomputable def bankLeaf25 : PrimeBank := .leaf [26881, 27061, 27277, 28537, 28663, 28723, 29251, 29611, 30241, 30941, 31051, 32341, 32443, 32999, 33331, 33391]

theorem bankLeaf25_valid : bankLeaf25.Certified := by
  simp only [bankLeaf25, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 2273] }, .lucas { root := 3, primeFactors := [2, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 29, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 281] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 4787] }, .lucas { root := 2, primeFactors := [2, 2393] }, .lucas { root := 3, primeFactors := [2, 13, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5407] }, .lucas { root := 3, primeFactors := [2, 3, 17, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 2357] }, .lucas { root := 2, primeFactors := [2, 19, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 53] }]), by simp⟩

@[expose] noncomputable def bankLeaf26 : PrimeBank := .leaf [34061, 34511, 34589, 36353, 36389, 36871, 37861, 37987, 37991, 38047, 38431, 38677, 39103, 39409, 40531, 40867]

theorem bankLeaf26_valid : bankLeaf26.Certified := by
  simp only [bankLeaf26, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 17, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 8647] }, .lucas { root := 3, primeFactors := [2, 3, 11, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 827] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 5, 1229] }, .lucas { root := 2, primeFactors := [2, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 631] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 487] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 29, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 373] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 293] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 821] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 139] }]), by simp⟩

@[expose] noncomputable def bankLeaf27 : PrimeBank := .leaf [41081, 41233, 41593, 41611, 41969, 42043, 42073, 42299, 42407, 42451, 43609, 45007, 45319, 45943, 46153, 46411]

theorem bankLeaf27_valid : bankLeaf27.Certified := by
  simp only [bankLeaf27, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 859] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1733] }, .lucas { root := 2, primeFactors := [2, 433] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 19, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 43, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1753] }, .lucas { root := 7, primeFactors := [2, 3, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 21149] }, .lucas { root := 3, primeFactors := [2, 17, 311] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 13, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 23, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 577] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 13, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 13, 19, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 641] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 13, 17] }]), by simp⟩

@[expose] noncomputable def bankLeaf28 : PrimeBank := .leaf [46601, 46807, 47251, 47711, 47977, 48247, 49333, 49801, 49823, 51361, 53551, 53881, 54367, 55163, 55333, 55511]

theorem bankLeaf28_valid : bankLeaf28.Certified := by
  simp only [bankLeaf28, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 29, 269] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 13, 367] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 1999] }, .lucas { root := 3, primeFactors := [2, 3, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 17, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 4111] }, .lucas { root := 12, primeFactors := [2, 3, 5, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 29, 859] }]),
    by primality (cert := .witnesses [.lucas { root := 37, primeFactors := [2, 3, 5, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 31, primeFactors := [2, 3, 5, 449] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 17, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 27581] }, .lucas { root := 2, primeFactors := [2, 5, 7, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 29, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 7, 13, 61] }]), by simp⟩

@[expose] noncomputable def bankLeaf29 : PrimeBank := .leaf [55897, 57047, 57697, 57773, 59221, 59471, 60089, 60919, 61603, 62071, 62581, 63601, 64171, 65029, 67057, 67411]

theorem bankLeaf29_valid : bankLeaf29.Certified := by
  simp only [bankLeaf29, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 11, 2593] }, .lucas { root := 7, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 601] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 13, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 19, 313] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 29, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 13, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 10267] }, .lucas { root := 2, primeFactors := [2, 3, 29, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 2069] }, .lucas { root := 2, primeFactors := [2, 11, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 23, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5419] }, .lucas { root := 3, primeFactors := [2, 3, 7, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 107] }]), by simp⟩

@[expose] noncomputable def bankLeaf30 : PrimeBank := .leaf [67579, 67927, 68209, 68743, 70001, 70051, 70841, 71941, 71999, 72229, 73421, 74449, 75181, 75931, 75989, 77477]

theorem bankLeaf30_valid : bankLeaf30.Certified := by
  simp only [bankLeaf30, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 7, 1609] }, .lucas { root := 7, primeFactors := [2, 3, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11321] }, .lucas { root := 3, primeFactors := [2, 5, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 467] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 11, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 35999] }, .lucas { root := 13, primeFactors := [2, 41, 439] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 463] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 3671] }, .lucas { root := 13, primeFactors := [2, 5, 367] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 11, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 2531] }, .lucas { root := 2, primeFactors := [2, 5, 11, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 2767] }, .lucas { root := 3, primeFactors := [2, 3, 461] }]), by simp⟩

end OddPerfect.IndexComponent.Size160
