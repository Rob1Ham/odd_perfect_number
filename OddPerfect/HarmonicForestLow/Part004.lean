module

public import OddPerfect.HarmonicForestLow.Part003
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicForestLow

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf51_0 : PrimeBank := .leaf [2, 3, 5, 7, 13, 19, 23, 31, 53, 79, 97, 127, 139, 157, 163, 281]
theorem leaf51_0_valid : leaf51_0.Certified := by
  simp only [leaf51_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf51_1 : PrimeBank := .leaf [317, 409, 523, 919, 941, 1063, 1471, 3169, 3541, 5419, 14401, 55897, 83641, 3348577]
theorem leaf51_1_valid : leaf51_1.Certified := by
  simp only [leaf51_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 59] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 59] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 137] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 17, 41] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 11, 151] }]), by simp⟩

@[expose] def pool51 : PrimeBank := (.branch 317 leaf51_0 leaf51_1)
theorem pool51_valid : pool51.Certified := ⟨leaf51_0_valid,leaf51_1_valid⟩

theorem covered51 : Range 51 55 :=
  scan_sound pool51 pool51_valid 7 51 [3, 0] [[(2,(.split 409 [(1,(.split 7 [(2,(.split 19 [(2,(.split 127 [(2,(.raise [(5419,1)]))]))])), (8,(.raise [(1063,1)]))])), (2,(.split 55897 [(1,(.raise [(1471,1), (19,1), (7,1)]))])), (3,(.split 83641 [(1,(.raise [(7,1)]))]))])), (5,(.split 919 [(2,(.raise [(163,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered55 : Range 55 59 :=
  scan_sound pool51 pool51_valid 7 55 [5, 3] []
    (by decide) (by decide +kernel)

theorem covered59 : Range 59 63 :=
  scan_sound pool51 pool51_valid 12 59 [0, 0] [[(2,(.split 3541 [(1,(.split 23 [(2,(.split 79 [(2,(.split 7 []))]))])), (2,(.split 19 [(2,(.split 127 []))]))]))], [(2,(.split 97 [(1,(.split 7 [(2,(.split 19 [(2,(.split 127 [(2,(.split 5419 []))]))])), (8,(.split 1063 []))])), (2,(.split 3169 [(1,(.split 317 [(1,(.split 53 [(1,(.split 13 [(1,(.split 7 [(2,(.split 19 [(2,(.raise [(127,1)]))]))])), (2,(.split 5 [(1,(.three (.owed 3 5 4 []) [(2,(.owed 3 2 17 [(7,[(2,(.split 19 []))]), (11,[(2,(.raise [(19,1)]))])]))])), (2,(.split 31 [])), (3,(.three (.owed 3 5 3 []) [])), (5,(.raise [(31,1)]))])), (3,(.split 7 []))])), (2,(.split 409 [])), (3,(.split 281 []))])), (2,(.split 14401 []))])), (2,(.split 3348577 []))])), (3,(.split 941 [(1,(.split 157 [(1,(.split 79 []))]))])), (5,(.raise [(139,1)]))])), (5,(.split 523 []))]]
    (by decide) (by decide +kernel)

theorem covered63 : Range 63 67 :=
  scan_sound pool51 pool51_valid 12 63 [3, 5] []
    (by decide) (by decide +kernel)

theorem segment51 : Range 51 67 := (range_join (range_join covered51 covered55) (range_join covered59 covered63))

theorem through67 : Range 3 67 := (range_join through51 segment51)

end OddPerfect.HarmonicChain.HarmonicForestLow
