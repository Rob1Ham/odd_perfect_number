module

public import OddPerfect.HarmonicForestLow.Part002
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicForestLow

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf35_0 : PrimeBank := .leaf [2, 3, 7, 19, 31, 37, 53, 61, 67, 97, 127, 157, 307, 317, 331, 367]
theorem leaf35_0_valid : leaf35_0.Certified := by
  simp only [leaf35_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf35_1 : PrimeBank := .leaf [523, 631, 733, 941, 1063, 1723, 1861, 2617, 3169, 5233, 5419, 990151]
theorem leaf35_1_valid : leaf35_1.Certified := by
  simp only [leaf35_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 59] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 41] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 31] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 109] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 109] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }]), by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 7, 23, 41] }]), by simp⟩

@[expose] def pool35 : PrimeBank := (.branch 523 leaf35_0 leaf35_1)
theorem pool35_valid : pool35.Certified := ⟨leaf35_0_valid,leaf35_1_valid⟩

theorem covered35 : Range 35 39 :=
  scan_sound pool35 pool35_valid 5 35 [5, 0] [[(2,(.split 67 [(2,(.split 7 [(8,(.raise [(1063,1), (31,1), (19,1)]))]))])), (5,(.split 67 [(2,(.split 7 []))]))]]
    (by decide) (by decide +kernel)

theorem covered39 : Range 39 43 :=
  scan_sound pool35 pool35_valid 5 39 [3, 0] [[(2,(.split 1723 [(2,(.split 990151 []))])), (5,(.split 1723 []))]]
    (by decide) (by decide +kernel)

theorem covered43 : Range 43 47 :=
  scan_sound pool35 pool35_valid 6 43 [0, 3] [[(2,(.split 631 [(2,(.split 307 [(2,(.split 733 [(1,(.raise [(367,1)]))]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered47 : Range 47 51 :=
  scan_sound pool35 pool35_valid 9 47 [0, 7] [[(2,(.split 61 [(1,(.split 31 [(2,(.split 331 [(2,(.split 5233 [(1,(.split 2617 []))]))]))])), (2,(.split 97 [(1,(.split 7 [(2,(.split 19 [(2,(.split 127 [(2,(.raise [(5419,1)]))]))]))])), (2,(.split 3169 [(1,(.split 317 [(1,(.split 53 [(1,(.split 37 [(1,(.raise [(19,1)]))]))]))]))])), (3,(.split 941 [(1,(.split 157 []))]))])), (3,(.split 1861 [(1,(.split 31 [(2,(.raise [(331,1)]))]))])), (5,(.raise [(523,1)]))]))]]
    (by decide) (by decide +kernel)

theorem segment35 : Range 35 51 := (range_join (range_join covered35 covered39) (range_join covered43 covered47))

theorem through51 : Range 3 51 := (range_join through35 segment35)

end OddPerfect.HarmonicChain.HarmonicForestLow
