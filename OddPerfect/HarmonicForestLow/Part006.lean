module

public import OddPerfect.HarmonicForestLow.Part005
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicForestLow

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf83_0 : PrimeBank := .leaf [2, 3, 5, 7, 13, 19, 31, 43, 47, 53, 61, 127, 139, 157, 281, 313]
theorem leaf83_0_valid : leaf83_0.Certified := by
  simp only [leaf83_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf83_1 : PrimeBank := .leaf [317, 331, 367, 379, 409, 757, 773, 3169, 3463, 8011, 14401, 1645747, 1674289, 3348577]
theorem leaf83_1_valid : leaf83_1.Certified := by
  simp only [leaf83_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 577] }]), by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 89] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 59, 4649] }, .lucas { root := 3, primeFactors := [2, 7, 83] }]), by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 7, 11, 151] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 11, 151] }]), by simp⟩

@[expose] def pool83 : PrimeBank := (.branch 317 leaf83_0 leaf83_1)
theorem pool83_valid : pool83.Certified := ⟨leaf83_0_valid,leaf83_1_valid⟩

theorem covered83 : Range 83 87 :=
  scan_sound pool83 pool83_valid 5 83 [0, 5] [[(2,(.split 367 [(2,(.split 3463 []))]))]]
    (by decide) (by decide +kernel)

theorem covered87 : Range 87 91 :=
  scan_sound pool83 pool83_valid 5 87 [3, 0] [[(2,(.split 8011 [(2,(.raise [(1645747,1)]))])), (5,(.split 8011 []))]]
    (by decide) (by decide +kernel)

theorem covered91 : Range 91 95 :=
  scan_sound pool83 pool83_valid 5 91 [7, 3] []
    (by decide) (by decide +kernel)

theorem covered95 : Range 95 99 :=
  scan_sound pool83 pool83_valid 12 95 [5, 0] [[(2,(.split 3169 [(1,(.split 317 [(1,(.split 53 [(1,(.split 5 [(1,(.three (.owed 3 5 15 [(7,[(2,(.split 19 [(2,(.split 127 []))]))]), (11,[(2,(.split 19 [(2,(.split 127 []))]))]), (13,[(2,(.split 61 [(1,(.split 31 [(2,(.raise [(331,1)]))])), (2,(.owed 3 5 4 []))])), (5,(.split 157 []))])]) [(2,(.split 13 [(1,(.split 7 [(2,(.split 19 [(2,(.split 127 []))]))])), (2,(.split 61 [(1,(.split 31 [(2,(.raise [(331,1)]))])), (2,(.owed 3 2 17 [(7,[(2,(.split 19 []))]), (11,[(2,(.raise [(19,1)]))])]))])), (5,(.raise [(7,1)]))])), (8,(.split 757 [(1,(.raise [(379,1)]))]))])), (2,(.split 31 [(2,(.split 331 []))])), (3,(.split 13 [(1,(.split 7 [(2,(.split 19 [(2,(.split 127 []))]))])), (2,(.split 61 [(1,(.split 31 [(2,(.raise [(331,1)]))])), (2,(.three (.owed 3 5 3 []) []))])), (3,(.split 7 [(2,(.split 19 []))]))])), (5,(.split 31 [(2,(.raise [(331,1)]))])), (7,(.split 313 [(1,(.split 157 []))])), (8,(.raise [(31,1)]))])), (2,(.split 409 [(1,(.split 7 [(2,(.split 19 []))]))])), (3,(.split 281 [(1,(.split 47 []))]))])), (2,(.split 14401 [(1,(.raise [(379,1)]))])), (3,(.split 773 [(1,(.raise [(43,1)]))]))])), (2,(.split 3348577 [(1,(.split 1674289 []))]))])), (5,(.split 139 []))]]
    (by decide) (by decide +kernel)

theorem segment83 : Range 83 99 := (range_join (range_join covered83 covered87) (range_join covered91 covered95))

theorem through99 : Range 3 99 := (range_join through83 segment83)

end OddPerfect.HarmonicChain.HarmonicForestLow
