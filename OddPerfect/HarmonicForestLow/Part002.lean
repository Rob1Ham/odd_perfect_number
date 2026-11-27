module

public import OddPerfect.HarmonicForestLow.Part001
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicForestLow

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf19_0 : PrimeBank := .leaf [2, 3, 7, 11, 19, 31, 43, 67, 79, 127, 271, 331, 523, 1009, 1063, 2617]
theorem leaf19_0_valid : leaf19_0.Certified := by
  simp only [leaf19_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 59] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 109] }]), by simp⟩

@[expose] def leaf19_1 : PrimeBank := .leaf [5233, 5419, 24571, 41203, 42073, 81343, 7792003]
theorem leaf19_1_valid : leaf19_1.Certified := by
  simp only [leaf19_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 109] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 13] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 109] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1753] }, .lucas { root := 7, primeFactors := [2, 3, 73] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 4519] }, .lucas { root := 3, primeFactors := [2, 3, 251] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 227, 1907] }, .lucas { root := 2, primeFactors := [2, 953] }]), by simp⟩

@[expose] def pool19 : PrimeBank := (.branch 5233 leaf19_0 leaf19_1)
theorem pool19_valid : pool19.Certified := ⟨leaf19_0_valid,leaf19_1_valid⟩

theorem covered19 : Range 19 23 :=
  scan_sound pool19 pool19_valid 6 19 [0, 3] [[(2,(.split 127 [(2,(.split 5419 [(2,(.split 1009 [(1,(.raise [(31,1)]))]))]))])), (8,(.raise [(523,1), (127,1)]))]]
    (by decide) (by decide +kernel)

theorem covered23 : Range 23 27 :=
  scan_sound pool19 pool19_valid 6 23 [0, 5] [[(2,(.split 79 [(2,(.split 7 [(8,(.raise [(1063,1), (43,1)]))]))])), (8,(.raise [(7792003,1)]))]]
    (by decide) (by decide +kernel)

theorem covered27 : Range 27 31 :=
  scan_sound pool19 pool19_valid 7 27 [3, 0] [[(2,(.split 67 [(2,(.split 31 [(2,(.split 331 [(2,(.split 5233 []))]))]))])), (5,(.split 271 [(2,(.raise [(24571,1)]))])), (8,(.raise [(41203,1)]))]]
    (by decide) (by decide +kernel)

theorem covered31 : Range 31 35 :=
  scan_sound pool19 pool19_valid 7 31 [0, 3] [[(2,(.split 331 [(2,(.split 5233 [(1,(.split 2617 [(1,(.split 11 [(2,(.raise [(19,1), (7,3)]))]))])), (2,(.split 42073 []))]))])), (8,(.raise [(81343,1)]))]]
    (by decide) (by decide +kernel)

theorem segment19 : Range 19 35 := (range_join (range_join covered19 covered23) (range_join covered27 covered31))

theorem through35 : Range 3 35 := (range_join through19 segment19)

end OddPerfect.HarmonicChain.HarmonicForestLow
