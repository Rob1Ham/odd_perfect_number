module

public import OddPerfect.HarmonicForestLow.Part004
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicForestLow

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf67_0 : PrimeBank := .leaf [2, 3, 5, 7, 13, 17, 19, 29, 31, 43, 47, 53, 61, 67, 79, 97]
theorem leaf67_0_valid : leaf67_0.Certified := by
  simp only [leaf67_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf67_1 : PrimeBank := .leaf [127, 157, 211, 281, 307, 313, 331, 379, 409, 421, 631, 727, 751, 757, 919, 1063]
theorem leaf67_1_valid : leaf67_1.Certified := by
  simp only [leaf67_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 59] }]), by simp⟩

@[expose] def leaf67_2 : PrimeBank := .leaf [1279, 1801, 1861, 2383, 2557, 2617, 3169, 5113, 5233, 5419, 6029, 55897, 154543, 8715961]
theorem leaf67_2_valid : leaf67_2.Certified := by
  simp only [leaf67_2,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 71] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 31] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 397] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 71] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 109] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 71] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 109] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 137] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 137] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 43, 599] }]), by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 11, 31, 71] }]), by simp⟩

@[expose] def pool67 : PrimeBank := (.branch 127 leaf67_0 (.branch 1279 leaf67_1 leaf67_2))
theorem pool67_valid : pool67.Certified := ⟨leaf67_0_valid,⟨leaf67_1_valid,leaf67_2_valid⟩⟩

theorem covered67 : Range 67 71 :=
  scan_sound pool67 pool67_valid 7 67 [0, 3] [[(2,(.split 31 [(2,(.split 331 [(2,(.split 5233 [(1,(.split 2617 []))]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered71 : Range 71 75 :=
  scan_sound pool67 pool67_valid 12 71 [0, 0] [[(2,(.split 5113 [(1,(.split 2557 [(1,(.split 1279 [(2,(.raise [(2383,1)]))])), (2,(.split 19 [(2,(.raise [(127,1)]))]))])), (2,(.split 8715961 []))]))], [(2,(.split 1801 [(1,(.split 53 [(1,(.split 17 [(1,(.three (.owed 3 5 26 [(5,[(2,(.split 31 [(2,(.split 331 [(2,(.raise [(7,1)]))]))])), (5,(.split 31 [(2,(.split 331 []))])), (8,(.split 31 [])), (11,(.raise [(31,1)]))]), (7,[(2,(.split 19 [(2,(.split 127 [(2,(.raise [(5419,1)]))]))])), (8,(.raise [(1063,1)]))]), (11,[(2,(.split 19 [(2,(.split 127 [(2,(.raise [(5419,1)]))]))]))]), (13,[(2,(.split 61 [(1,(.split 31 [(2,(.split 331 []))])), (2,(.split 97 [(1,(.split 7 [(2,(.split 19 []))])), (2,(.split 3169 []))])), (3,(.split 1861 []))])), (5,(.split 157 [(1,(.raise [(79,1)]))]))]), (19,[(2,(.split 127 [(2,(.raise [(5419,1)]))]))]), (23,[(2,(.split 79 [(2,(.split 7 []))]))])]) [(2,(.split 13 [(1,(.split 7 [(2,(.split 19 [(2,(.split 127 []))]))])), (2,(.split 61 [(1,(.split 31 [(2,(.split 331 []))])), (2,(.split 97 [(1,(.split 7 [(2,(.split 19 []))]))])), (3,(.raise [(31,1)]))])), (5,(.split 157 [(1,(.raise [(79,1)]))]))])), (8,(.split 757 [(1,(.split 379 []))]))])), (2,(.split 307 [(2,(.split 43 []))])), (3,(.split 29 [(1,(.split 5 [(2,(.split 31 [(2,(.split 331 []))])), (3,(.split 13 [(1,(.split 7 [(2,(.split 19 [(2,(.raise [(127,1)]))]))])), (2,(.split 61 [(1,(.split 31 [])), (2,(.split 97 []))])), (3,(.split 7 [(2,(.split 19 []))]))])), (5,(.split 31 [(2,(.raise [(331,1)]))])), (7,(.split 313 []))])), (2,(.split 67 [(2,(.raise [(31,1)]))])), (3,(.split 421 [(1,(.raise [(211,1)]))]))])), (5,(.split 307 []))])), (2,(.split 409 [(1,(.split 7 [(2,(.split 19 [(2,(.raise [(127,1)]))]))])), (2,(.split 55897 []))])), (3,(.split 281 [(1,(.split 47 [(2,(.split 61 []))])), (2,(.raise [(727,1)]))])), (5,(.raise [(919,1)]))])), (2,(.split 154543 [])), (3,(.split 6029 []))])), (5,(.split 751 []))]]
    (by decide) (by decide +kernel)

theorem covered75 : Range 75 79 :=
  scan_sound pool67 pool67_valid 12 75 [3, 7] []
    (by decide) (by decide +kernel)

theorem covered79 : Range 79 83 :=
  scan_sound pool67 pool67_valid 12 79 [0, 3] [[(2,(.split 43 [(2,(.split 631 [(2,(.split 307 []))]))]))]]
    (by decide) (by decide +kernel)

theorem segment67 : Range 67 83 := (range_join (range_join covered67 covered71) (range_join covered75 covered79))

theorem through83 : Range 3 83 := (range_join through67 segment67)

end OddPerfect.HarmonicChain.HarmonicForestLow
