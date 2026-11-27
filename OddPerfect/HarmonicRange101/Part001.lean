module

public import OddPerfect.HarmonicRange
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicRange101

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf101_0 : PrimeBank := .leaf [2, 3, 7, 11, 13, 19, 23, 31, 37, 43, 53, 61, 67, 71, 73, 79]
theorem leaf101_0_valid : leaf101_0.Certified := by
  simp only [leaf101_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf101_1 : PrimeBank := .leaf [97, 103, 109, 127, 139, 151, 163, 181, 199, 211, 229, 239, 277, 283, 307, 317]
theorem leaf101_1_valid : leaf101_1.Certified := by
  simp only [leaf101_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf101_2 : PrimeBank := .leaf [331, 367, 379, 409, 457, 487, 499, 547, 571, 619, 631, 653, 709, 727, 733, 787]
theorem leaf101_2_valid : leaf101_2.Certified := by
  simp only [leaf101_2,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf101_3 : PrimeBank := .leaf [823, 827, 883, 967, 991, 1009, 1051, 1063, 1087, 1093, 1279, 1327, 1471, 1619, 1693, 1699]
theorem leaf101_3_valid : leaf101_3.Certified := by
  simp only [leaf101_3,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 59] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 181] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 71] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 17] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 809] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 47] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 283] }]), by simp⟩

@[expose] def leaf101_4 : PrimeBank := .leaf [1783, 1801, 1879, 2053, 2083, 2143, 2287, 2389, 2557, 2617, 2707, 3019, 3169, 3463, 3499, 3571]
theorem leaf101_4_valid : leaf101_4.Certified := by
  simp only [leaf101_4,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 313] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 347] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 17] }]), by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 127] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 199] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 71] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 109] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 41] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 503] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 577] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 53] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 17] }]), by simp⟩

@[expose] def leaf101_5 : PrimeBank := .leaf [3769, 4111, 4219, 4603, 4639, 4861, 5107, 5113, 5233, 5347, 5419, 5659, 5827, 5851, 6037, 6211]
theorem leaf101_5_valid : leaf101_5.Certified := by
  simp only [leaf101_5,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 157] }]), by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 137] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 37] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 59] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 773] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 37] }]), by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 71] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 109] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 41] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 971] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 503] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 23] }]), by simp⟩

@[expose] def leaf101_6 : PrimeBank := .leaf [6343, 6529, 6577, 6619, 7027, 7351, 7459, 7669, 7789, 7951, 8191, 8263, 8269, 8527, 8647, 9277]
theorem leaf101_6_valid : leaf101_6.Certified := by
  simp only [leaf101_6,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 151] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 17] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 137] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1103] }, .lucas { root := 5, primeFactors := [2, 19, 29] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1171] }, .lucas { root := 2, primeFactors := [2, 3, 5, 13] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 113] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 71] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 59] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 53] }]), by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7, 13] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 53] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 29] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 131] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 773] }]), by simp⟩

@[expose] def leaf101_7 : PrimeBank := .leaf [9463, 9721, 9967, 10243, 10303, 10837, 11317, 11503, 11833, 13267, 13537, 13963, 14029, 14401, 15901, 16381]
theorem leaf101_7_valid : leaf101_7.Certified := by
  simp only [leaf101_7,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 83] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 151] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 569] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 101] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 43] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 41] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 71] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 29] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 67] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 47] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 179] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 167] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 53] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13] }]), by simp⟩

@[expose] def leaf101_8 : PrimeBank := .leaf [16651, 17293, 19441, 19501, 21673, 23029, 23971, 24571, 25423, 26227, 28057, 28099, 29611, 30103, 33391, 35617]
theorem leaf101_8_valid : leaf101_8.Certified := by
  simp only [leaf101_8,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 131] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 43] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 101] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 17, 47] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 13] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 223] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 31, 47] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 167] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 223] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 47] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 29, 173] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 53] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 53] }]), by simp⟩

@[expose] def leaf101_9 : PrimeBank := .leaf [42073, 51343, 51787, 55897, 59221, 65323, 65551, 86143, 109819, 116803, 125017, 134077, 147073, 152083, 154543, 158791]
theorem leaf101_9_valid : leaf101_9.Certified := by
  simp only [leaf101_9,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1753] }, .lucas { root := 7, primeFactors := [2, 3, 73] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 43, 199] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 137] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 137] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 47] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 191] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 19, 23] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 293] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 6101] }, .lucas { root := 2, primeFactors := [2, 5, 61] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 103] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 5209] }, .lucas { root := 17, primeFactors := [2, 3, 7, 31] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11173] }, .lucas { root := 5, primeFactors := [2, 3, 7, 19] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 383] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 17, 71] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 43, 599] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 67, 79] }]), by simp⟩

@[expose] def leaf101_10 : PrimeBank := .leaf [169789, 176419, 260191, 398581, 470359, 684757, 780991, 1009153, 1242217, 3256411, 4864429, 7668337, 9531919, 11413351, 20185213, 42695269]
theorem leaf101_10_valid : leaf101_10.Certified := by
  simp only [leaf101_10,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 14149] }, .lucas { root := 6, primeFactors := [2, 3, 131] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 59] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 73] }]), by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 7, 3733] }, .lucas { root := 2, primeFactors := [2, 3, 311] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 23, 827] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 3719] }, .lucas { root := 7, primeFactors := [2, 11, 13] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 73] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 71] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 19, 29, 197] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 73, 617] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 12289] }, .lucas { root := 11, primeFactors := [2, 3] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 11, 1783] }, .lucas { root := 10, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 13, 1951] }, .lucas { root := 3, primeFactors := [2, 3, 5, 13] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1682101] }, .lucas { root := 22, primeFactors := [2, 3, 5, 7, 89] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 11, 23, 41] }]), by simp⟩

@[expose] def leaf101_11 : PrimeBank := .leaf [64993111, 156580201, 176785957, 201252871]
theorem leaf101_11_valid : leaf101_11.Certified := by
  simp only [leaf101_11,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 13, 19, 179] }]), by primality (cert := .witnesses [.lucas { root := 33, primeFactors := [2, 3, 5, 7, 17, 43] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 101, 853] }]), by primality (cert := .witnesses [.lucas { root := 33, primeFactors := [2, 3, 5, 7, 13, 8191] }, .lucas { root := 17, primeFactors := [2, 3, 5, 7, 13] }]), by simp⟩

@[expose] def pool101 : PrimeBank := (.branch 6343 (.branch 823 (.branch 97 leaf101_0 (.branch 331 leaf101_1 leaf101_2)) (.branch 1783 leaf101_3 (.branch 3769 leaf101_4 leaf101_5))) (.branch 42073 (.branch 9463 leaf101_6 (.branch 16651 leaf101_7 leaf101_8)) (.branch 169789 leaf101_9 (.branch 64993111 leaf101_10 leaf101_11))))
theorem pool101_valid : pool101.Certified := ⟨⟨⟨leaf101_0_valid,⟨leaf101_1_valid,leaf101_2_valid⟩⟩,⟨leaf101_3_valid,⟨leaf101_4_valid,leaf101_5_valid⟩⟩⟩,⟨⟨leaf101_6_valid,⟨leaf101_7_valid,leaf101_8_valid⟩⟩,⟨leaf101_9_valid,⟨leaf101_10_valid,leaf101_11_valid⟩⟩⟩⟩

theorem covered101 : Range 101 125 :=
  scan_sound pool101 pool101_valid 7 101 [0, 0, 3, 0, 0, 3, 0, 5, 3, 7, 11, 3] [[(2,(.split 10303 [(2,(.split 5827 []))])), (5,(.split 10303 []))], [(2,(.split 3571 [(2,(.split 139 [(2,(.raise [(499,1)]))]))]))], [(2,(.split 127 [(2,(.split 5419 []))]))], [(2,(.split 571 [(2,(.split 151 [(2,(.raise [(103,1), (7,3)]))]))])), (5,(.raise [(571,1), (11,1), (7,1)]))], [(2,(.split 991 [(2,(.split 13 [(3,(.split 277 [(1,(.split 139 []))])), (5,(.split 277 []))]))])), (5,(.raise [(4219,1), (991,1)]))]]
    (by decide) (by decide +kernel)

theorem covered125 : Range 125 149 :=
  scan_sound pool101 pool101_valid 8 125 [5, 0, 3, 0, 7, 3, 0, 0, 3, 11, 5, 3] [[(2,(.split 5419 [(2,(.split 1009 [(1,(.split 31 []))]))]))], [(2,(.split 17293 [(1,(.split 8647 [(2,(.raise [(7,1)]))])), (2,(.split 7668337 []))]))], [(2,(.split 73 [(1,(.split 37 [(2,(.split 67 [(2,(.split 7 []))])), (3,(.split 19 [(2,(.split 127 [(2,(.raise [(5419,1)]))]))])), (5,(.raise [(67,1), (43,1)]))])), (2,(.split 1801 [(1,(.split 53 [(1,(.split 7 [(2,(.split 19 [(2,(.raise [(127,1)]))]))])), (2,(.split 409 [])), (3,(.raise [(7,1)]))])), (2,(.raise [(154543,1)]))])), (3,(.split 37 [(2,(.split 67 [])), (3,(.split 19 []))]))])), (5,(.raise [(6211,1), (23,1)]))], [(2,(.split 499 [(2,(.split 109 [(2,(.split 571 [])), (3,(.raise [(11,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered149 : Range 149 173 :=
  scan_sound pool101 pool101_valid 8 149 [0, 0, 3, 5, 0, 3, 7, 0, 3, 0, 13, 3] [[(2,(.split 103 [(2,(.split 3571 []))])), (5,(.raise [(7351,1)]))], [(2,(.split 1093 [(1,(.split 547 [(2,(.split 163 []))])), (2,(.split 398581 [(1,(.raise [(19,1), (7,1)]))])), (3,(.raise [(547,1)]))]))], [(2,(.split 8269 [(1,(.split 827 [(2,(.split 684757 []))])), (2,(.raise [(3256411,1)]))])), (5,(.raise [(3499,1)]))], [(2,(.split 67 [(2,(.split 7 [(8,(.raise [(1063,1)]))]))]))], [(2,(.split 28057 [(1,(.split 14029 [(1,(.split 23 [(2,(.split 79 []))]))])), (2,(.split 20185213 []))]))]]
    (by decide) (by decide +kernel)

theorem covered173 : Range 173 197 :=
  scan_sound pool101 pool101_valid 8 173 [0, 5, 3, 0, 0, 3, 5, 11, 3, 0, 0, 3] [[(2,(.split 30103 [(2,(.raise [(51787,1)]))])), (5,(.raise [(30103,1)]))], [(2,(.split 4603 [(2,(.split 1009153 []))]))], [(2,(.split 139 [(2,(.split 499 [(2,(.raise [(79,1)]))]))])), (5,(.raise [(1051,1)]))], [(2,(.split 31 [(2,(.split 331 [(2,(.split 5233 [(1,(.split 2617 []))]))]))]))], [(2,(.split 1783 [(2,(.split 1279 []))])), (5,(.raise [(1783,1)]))]]
    (by decide) (by decide +kernel)

theorem covered197 : Range 197 221 :=
  scan_sound pool101 pool101_valid 8 197 [0, 0, 3, 7, 5, 3, 11, 0, 3, 5, 7, 3] [[(2,(.split 2053 [(1,(.split 79 [(2,(.split 43 [(2,(.raise [(631,1)]))]))])), (2,(.split 1279 []))])), (5,(.raise [(211,1), (19,1)]))], [(2,(.split 13267 [(2,(.split 7669 []))]))], [(2,(.split 31 [(2,(.split 331 [(2,(.split 5233 [(1,(.raise [(7,1)]))]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered221 : Range 221 245 :=
  scan_sound pool101 pool101_valid 9 221 [13, 0, 3, 0, 0, 3, 0, 5, 3, 0, 0, 3] [[(2,(.split 16651 [(2,(.split 4864429 []))]))], [(2,(.split 709 [(1,(.split 71 [(2,(.split 5113 [(1,(.split 2557 []))]))])), (2,(.split 23971 [])), (3,(.raise [(71,1)]))]))], [(2,(.split 181 [(1,(.split 97 [(1,(.split 7 [(8,(.raise [(1063,1)]))])), (2,(.split 3169 [(1,(.split 317 [(1,(.split 53 [(1,(.split 7 [(2,(.raise [(19,1)]))]))]))]))])), (3,(.split 7 []))])), (2,(.split 139 [(2,(.raise [(499,1), (79,1)]))])), (3,(.split 16381 [(1,(.raise [(8191,1)]))]))])), (5,(.raise [(7459,1)]))], [(2,(.split 7789 [(1,(.split 19 [(2,(.split 127 [(2,(.raise [(5419,1)]))]))])), (2,(.raise [(470359,1)]))])), (5,(.raise [(487,1)]))], [(2,(.split 3019 [(2,(.split 367 []))]))], [(2,(.split 19441 [(1,(.split 9721 [(1,(.split 4861 [(1,(.split 11 [(2,(.raise [(19,1)]))]))]))])), (2,(.raise [(619,1)]))])), (5,(.raise [(8263,1)]))]]
    (by decide) (by decide +kernel)

theorem covered245 : Range 245 269 :=
  scan_sound pool101 pool101_valid 9 245 [5, 13, 3, 0, 11, 3, 0, 7, 3, 0, 5, 3] [[(2,(.split 1471 [(2,(.split 823 []))]))], [(2,(.split 1087 [(2,(.split 283 []))])), (5,(.raise [(1087,1)]))], [(2,(.split 109 [(1,(.split 11 [(2,(.split 7 []))])), (2,(.split 571 [(2,(.raise [(151,1)]))])), (3,(.split 457 [(1,(.split 229 [(1,(.raise [(23,1)]))]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered269 : Range 269 293 :=
  scan_sound pool101 pool101_valid 9 269 [0, 0, 3, 5, 0, 3, 0, 0, 3, 7, 17, 3] [[(2,(.split 151 [(2,(.split 1093 [(1,(.split 547 []))]))])), (5,(.raise [(151,1)]))], [(2,(.split 24571 [(2,(.raise [(201252871,1)]))]))], [(2,(.split 19 [(2,(.split 127 [(2,(.split 5419 []))]))])), (5,(.raise [(139,1)]))], [(2,(.split 727 [(2,(.split 176419 []))])), (5,(.raise [(26227,1)]))], [(2,(.split 367 [(2,(.split 3463 []))]))]]
    (by decide) (by decide +kernel)

theorem covered293 : Range 293 317 :=
  scan_sound pool101 pool101_valid 9 293 [0, 5, 3, 13, 7, 3, 5, 0, 3, 0, 0, 3] [[(2,(.split 86143 [])), (5,(.raise [(86143,1)]))], [(2,(.split 43 [(2,(.split 631 [(2,(.split 733 [(1,(.raise [(367,1)]))]))]))]))], [(2,(.split 5107 [(2,(.split 1242217 []))]))], [(2,(.split 181 [(2,(.split 139 [(2,(.raise [(499,1), (79,1)]))])), (3,(.split 16381 [(1,(.raise [(8191,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered317 : Range 317 341 :=
  scan_sound pool101 pool101_valid 9 317 [0, 11, 3, 17, 5, 3, 7, 0, 3, 5, 0, 3] [[(2,(.split 14401 [(1,(.split 379 [(2,(.raise [(787,1)]))])), (2,(.split 125017 []))])), (5,(.raise [(33391,1)]))], [(2,(.split 5233 [(1,(.split 2617 [(1,(.split 11 [(2,(.split 7 []))])), (2,(.split 11833 []))])), (2,(.split 42073 []))]))], [(2,(.split 883 [(2,(.raise [(260191,1), (43,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered341 : Range 341 365 :=
  scan_sound pool101 pool101_valid 9 341 [11, 7, 3, 0, 0, 3, 0, 5, 3, 0, 19, 3] [[(2,(.split 1327 [(2,(.split 2707 []))]))], [(2,(.split 2143 [(2,(.split 35617 [(1,(.raise [(1619,1)]))]))]))], [(2,(.split 6577 [(1,(.split 23 [(2,(.split 79 [(2,(.raise [(43,1)]))]))])), (2,(.raise [(31,1), (19,1), (7,1)]))]))], [(2,(.split 499 [(2,(.split 109 [(2,(.raise [(571,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered365 : Range 365 389 :=
  scan_sound pool101 pool101_valid 9 365 [5, 0, 3, 7, 0, 3, 13, 0, 3, 0, 5, 3] [[(2,(.split 3463 [(2,(.raise [(65551,1)]))]))], [(2,(.split 73 [(1,(.split 7 [(2,(.split 19 [(2,(.split 127 [(2,(.raise [(5419,1)]))]))])), (8,(.raise [(1063,1)]))])), (2,(.split 1801 [(1,(.split 53 [(1,(.split 7 [(2,(.split 19 [(2,(.raise [(127,1)]))]))])), (2,(.split 7 []))]))])), (3,(.split 13 [(2,(.split 61 [(1,(.split 31 []))])), (3,(.split 7 []))]))]))], [(2,(.split 787 [(2,(.split 151 []))]))], [(2,(.split 147073 [(1,(.split 487 [(2,(.raise [(151,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered389 : Range 389 413 :=
  scan_sound pool101 pool101_valid 9 389 [0, 17, 3, 5, 0, 3, 0, 13, 3, 11, 0, 3] [[(2,(.split 21673 [(1,(.split 10837 [(1,(.split 5419 []))])), (2,(.split 156580201 []))]))], [(2,(.split 1699 [(2,(.split 2389 [(1,(.raise [(239,1)]))]))]))], [(2,(.split 23029 [(1,(.split 7 [])), (2,(.split 176785957 []))]))], [(2,(.split 55897 [(1,(.split 1471 [(2,(.raise [(823,1)]))])), (2,(.raise [(158791,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered413 : Range 413 437 :=
  scan_sound pool101 pool101_valid 9 413 [7, 5, 3, 0, 0, 3, 5, 7, 3, 0, 0, 3] [[(2,(.split 13537 [(1,(.split 967 [(2,(.raise [(67,1)]))])), (2,(.raise [(116803,1)]))]))], [(2,(.split 59221 [(1,(.split 29611 [])), (2,(.raise [(152083,1)]))]))], [(2,(.split 67 [(2,(.split 7 []))]))], [(2,(.split 1693 [(1,(.split 11 [(2,(.split 19 [(2,(.split 127 []))]))])), (2,(.raise [(487,1), (151,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered437 : Range 437 461 :=
  scan_sound pool101 pool101_valid 9 437 [19, 0, 3, 0, 5, 3, 0, 11, 3, 5, 0, 3] [[(2,(.split 67 [(2,(.split 31 []))]))], [(2,(.split 28099 [(2,(.raise [(780991,1)]))]))], [(2,(.split 2083 [(2,(.split 15901 [(1,(.raise [(7951,1)]))]))]))], [(2,(.split 9967 [(2,(.split 134077 []))]))]]
    (by decide) (by decide +kernel)

theorem covered461 : Range 461 485 :=
  scan_sound pool101 pool101_valid 9 461 [0, 0, 3, 0, 7, 3, 11, 5, 3, 0, 13, 3] [[(2,(.split 571 [(2,(.split 151 []))]))], [(2,(.split 3769 [(1,(.split 19 [(2,(.split 127 [(2,(.raise [(5419,1)]))]))])), (2,(.split 2287 []))]))], [(2,(.split 11503 [(2,(.raise [(8527,1)]))]))], [(2,(.split 5347 [(2,(.raise [(9531919,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered485 : Range 485 509 :=
  scan_sound pool101 pool101_valid 9 485 [5, 0, 3, 0, 17, 3, 7, 0, 3, 0, 5, 3] [[(2,(.split 11317 [(1,(.split 5659 [])), (2,(.split 42695269 []))]))], [(2,(.split 6529 [(1,(.split 653 [(1,(.split 109 [(1,(.split 11 [(2,(.split 19 []))])), (2,(.raise [(571,1)]))])), (2,(.split 19 []))])), (2,(.raise [(25423,1)]))]))], [(2,(.split 109 [(2,(.split 571 [(2,(.raise [(151,1), (103,1)]))])), (3,(.split 457 [(1,(.split 229 [(1,(.raise [(23,1), (11,1)]))]))]))]))], [(2,(.split 19501 [(1,(.split 199 [(2,(.raise [(13267,1)]))])), (2,(.raise [(163,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered509 : Range 509 533 :=
  scan_sound pool101 pool101_valid 9 509 [0, 7, 3, 5, 11, 3, 0, 0, 3, 17, 23, 3] [[(2,(.split 6037 [(1,(.split 3019 [])), (2,(.split 6529 []))]))], [(2,(.split 283 [(2,(.split 367 []))]))], [(2,(.split 7027 [(2,(.raise [(1879,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered533 : Range 533 557 :=
  scan_sound pool101 pool101_valid 9 533 [13, 5, 3, 7, 0, 3, 5, 0, 3, 19, 7, 3] [[(2,(.split 13963 [(2,(.raise [(64993111,1)]))]))], [(2,(.split 163 [(2,(.split 67 [(2,(.raise [(31,1), (19,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered557 : Range 557 581 :=
  scan_sound pool101 pool101_valid 9 557 [0, 13, 3, 0, 5, 3, 0, 0, 3, 5, 0, 3] [[(2,(.split 6343 [(2,(.split 169789 []))]))], [(2,(.split 10243 [(2,(.raise [(139,1)]))]))], [(2,(.split 6619 [(2,(.raise [(109819,1)]))]))], [(2,(.split 151 [(2,(.split 103 [(2,(.raise [(3571,1)]))]))]))], [(2,(.split 5851 [(2,(.raise [(11413351,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered581 : Range 581 605 :=
  scan_sound pool101 pool101_valid 9 581 [7, 11, 3, 0, 19, 3, 0, 5, 3, 0, 0, 3] [[(2,(.split 631 [(2,(.raise [(547,1), (307,1)]))]))], [(2,(.split 163 [(2,(.split 67 [(2,(.raise [(31,1), (19,1)]))]))]))], [(2,(.split 51343 []))], [(2,(.split 9277 [(1,(.split 4639 [])), (2,(.raise [(4111,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered605 : Range 605 613 :=
  scan_sound pool101 pool101_valid 9 605 [5, 0, 3, 13] [[(2,(.split 9463 [(2,(.raise [(65323,1)]))]))]]
    (by decide) (by decide +kernel)

theorem segment101 : Range 101 613 := (range_join (range_join (range_join (range_join covered101 covered125) (range_join covered149 (range_join covered173 covered197))) (range_join (range_join covered221 (range_join covered245 covered269)) (range_join covered293 (range_join covered317 covered341)))) (range_join (range_join (range_join covered365 covered389) (range_join covered413 (range_join covered437 covered461))) (range_join (range_join covered485 (range_join covered509 covered533)) (range_join covered557 (range_join covered581 covered605)))))

theorem through613 : Range 101 613 := segment101

end OddPerfect.HarmonicChain.HarmonicRange101
