module

public import OddPerfect.HarmonicRange
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicForestLow

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf3_0 : PrimeBank := .leaf [2, 3, 5, 7, 11, 13, 19, 31, 43, 53, 61, 79, 97, 127, 157, 193]
theorem leaf3_0_valid : leaf3_0.Certified := by
  simp only [leaf3_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf3_1 : PrimeBank := .leaf [307, 317, 331, 379, 523, 631, 733, 757, 787, 827, 941, 1051, 1063, 1171, 1861, 2617]
theorem leaf3_1_valid : leaf3_1.Certified := by
  simp only [leaf3_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 59] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 31] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 109] }]), by simp⟩

@[expose] def leaf3_2 : PrimeBank := .leaf [3169, 5167, 5233, 5419, 8269, 14281, 14713, 42073, 160967, 377011, 1155061, 1270657, 1609669, 1772893, 3348577]
theorem leaf3_2_valid : leaf3_2.Certified := by
  simp only [leaf3_2,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 41] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 109] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 53] }]), by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 7, 17] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 613] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1753] }, .lucas { root := 7, primeFactors := [2, 3, 73] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 41, 151] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 59, 71] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 23, 31] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1103] }, .lucas { root := 5, primeFactors := [2, 19, 29] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 61, 733] }]), by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 11, 37] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 11, 151] }]), by simp⟩

@[expose] def pool3 : PrimeBank := (.branch 307 leaf3_0 (.branch 3169 leaf3_1 leaf3_2))
theorem pool3_valid : pool3.Certified := ⟨leaf3_0_valid,⟨leaf3_1_valid,leaf3_2_valid⟩⟩

theorem covered3 : Range 3 7 :=
  scan_sound pool3 pool3_valid 12 3 [0, 0] [[(2,(.split 13 [(1,(.split 7 [(2,(.split 19 [(2,(.split 127 [(2,(.split 5419 []))])), (8,(.raise [(523,1)]))])), (8,(.split 1063 [(2,(.raise [(377011,1)]))]))])), (2,(.split 61 [(1,(.split 31 [(2,(.split 331 [(2,(.split 5233 [(1,(.split 2617 []))]))]))])), (2,(.split 97 [(1,(.split 7 [(2,(.split 19 [(2,(.split 127 [(2,(.raise [(5419,1)]))]))])), (8,(.raise [(1063,1)]))])), (2,(.split 3169 [(1,(.split 317 [(1,(.split 53 [(1,(.split 5 [(1,(.owed 3 2 17 [(7,[(2,(.split 19 []))]), (11,[(2,(.raise [(19,1)]))])])), (2,(.split 31 []))]))]))]))])), (3,(.split 941 [(1,(.split 157 [(1,(.raise [(79,1)]))]))]))])), (3,(.split 1861 [(1,(.split 31 [(2,(.raise [(331,1), (19,1)]))])), (2,(.raise [(31,1)]))])), (5,(.raise [(523,1), (31,1), (7,1)]))])), (3,(.split 7 [(2,(.split 19 [(2,(.split 127 [(2,(.split 5419 []))]))])), (8,(.split 1063 []))])), (5,(.split 157 [(1,(.split 79 [(2,(.split 7 []))])), (2,(.split 8269 [(1,(.raise [(827,1), (7,1)]))])), (3,(.raise [(79,1), (7,1)]))])), (7,(.split 14281 [(1,(.split 193 [(1,(.split 97 [(1,(.raise [(7,3)]))]))]))])), (8,(.split 1609669 [(1,(.raise [(160967,1)]))]))])), (8,(.split 757 [(1,(.split 379 [(2,(.split 787 []))])), (2,(.split 14713 [(1,(.split 1051 []))])), (3,(.raise [(379,1)]))]))], [(2,(.split 31 [(2,(.split 331 [(2,(.split 5233 [(1,(.split 2617 [(1,(.split 11 [(2,(.raise [(19,1)]))]))])), (2,(.split 42073 []))]))]))])), (5,(.split 31 [(2,(.split 331 [(2,(.split 5233 [(1,(.split 2617 [(1,(.raise [(11,1)]))]))]))]))])), (8,(.split 31 [(2,(.split 331 [(2,(.raise [(19,1), (7,1)]))]))])), (11,(.split 31 [(2,(.split 331 []))])), (17,(.raise [(5167,1)]))]]
    (by decide) (by decide +kernel)

theorem covered7 : Range 7 11 :=
  scan_sound pool3 pool3_valid 12 7 [0, 3] [[(2,(.split 19 [(2,(.split 127 [(2,(.split 5419 [(2,(.raise [(31,1)]))]))])), (8,(.raise [(523,1), (127,1)]))])), (8,(.split 1063 [(2,(.raise [(377011,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered11 : Range 11 15 :=
  scan_sound pool3 pool3_valid 12 11 [0, 0] [[(2,(.split 19 [(2,(.split 127 [(2,(.split 5419 []))])), (8,(.raise [(523,1)]))])), (8,(.split 1772893 [(1,(.raise [(1171,1)]))]))], [(2,(.split 61 [(1,(.split 31 [(2,(.split 331 [(2,(.split 5233 [(1,(.split 2617 [(1,(.raise [(11,1)]))]))]))]))])), (2,(.split 97 [(1,(.split 7 [(2,(.split 19 [(2,(.split 127 [(2,(.split 5419 []))]))])), (8,(.raise [(1063,1), (19,1)]))])), (2,(.split 3169 [(1,(.split 317 [(1,(.split 53 [(1,(.split 5 [(1,(.three (.owed 3 5 4 []) [(2,(.owed 3 2 17 [(7,[(2,(.split 19 []))]), (11,[(2,(.raise [(19,1)]))])]))])), (2,(.split 31 [])), (3,(.three (.owed 3 5 3 []) [])), (5,(.raise [(31,1)]))])), (2,(.raise [(7,1)]))])), (2,(.raise [(7,1)]))])), (2,(.split 3348577 []))])), (3,(.split 941 [(1,(.split 157 [(1,(.split 79 []))]))]))])), (3,(.split 1861 [(1,(.split 31 [(2,(.split 331 []))])), (2,(.split 1155061 []))])), (5,(.split 523 []))])), (5,(.split 157 [(1,(.split 79 [(2,(.split 7 []))])), (2,(.split 8269 [(1,(.split 827 []))])), (3,(.split 79 []))])), (8,(.split 1609669 [(1,(.raise [(160967,1)]))])), (11,(.raise [(7,1)]))]]
    (by decide) (by decide +kernel)

theorem covered15 : Range 15 19 :=
  scan_sound pool3 pool3_valid 12 15 [3, 0] [[(2,(.split 307 [(2,(.split 43 [(2,(.split 631 [(2,(.split 733 []))]))]))])), (5,(.split 307 [(2,(.split 43 [(2,(.raise [(631,1)]))]))])), (8,(.split 1270657 []))]]
    (by decide) (by decide +kernel)

theorem segment3 : Range 3 19 := (range_join (range_join covered3 covered7) (range_join covered11 covered15))

theorem through19 : Range 3 19 := segment3

end OddPerfect.HarmonicChain.HarmonicForestLow
