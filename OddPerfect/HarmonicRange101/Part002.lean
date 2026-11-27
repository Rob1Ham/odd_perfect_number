module

public import OddPerfect.HarmonicRange101.Part001
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicRange101

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf613_0 : PrimeBank := .leaf [2, 3, 7, 19, 23, 31, 37, 43, 53, 67, 79, 83, 103, 113, 127, 131]
theorem leaf613_0_valid : leaf613_0.Certified := by
  simp only [leaf613_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf613_1 : PrimeBank := .leaf [139, 151, 163, 199, 211, 239, 277, 283, 307, 331, 367, 379, 421, 439, 449, 463]
theorem leaf613_1_valid : leaf613_1.Certified := by
  simp only [leaf613_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf613_2 : PrimeBank := .leaf [499, 547, 617, 733, 751, 787, 811, 823, 839, 907, 919, 967, 991, 1051, 1063, 1087]
theorem leaf613_2_valid : leaf613_2.Certified := by
  simp only [leaf613_2,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 59] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 181] }]), by simp⟩

@[expose] def leaf613_3 : PrimeBank := .leaf [1093, 1423, 1567, 1759, 1987, 2083, 2383, 2677, 2683, 2851, 3271, 3571, 3769, 3931, 4051, 4591]
theorem leaf613_3_valid : leaf613_3.Certified := by
  simp only [leaf613_3,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 79] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 29] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 293] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 331] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 347] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 397] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 223] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 149] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 19] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 109] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 17] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 157] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 131] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 17] }]), by simp⟩

@[expose] def leaf613_4 : PrimeBank := .leaf [4657, 5023, 5233, 5419, 5503, 5647, 5879, 6367, 6733, 8389, 9181, 9391, 9439, 12799, 14071, 14713]
theorem leaf613_4_valid : leaf613_4.Certified := by
  simp only [leaf613_4,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 97] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 31] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 109] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 131] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 941] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 2939] }, .lucas { root := 2, primeFactors := [2, 13, 113] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1061] }, .lucas { root := 2, primeFactors := [2, 5, 53] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 233] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 313] }]), by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 11, 13] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 79] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 67] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 613] }]), by simp⟩

@[expose] def leaf613_5 : PrimeBank := .leaf [15217, 16097, 16729, 17293, 17923, 19609, 23743, 23971, 25127, 26041, 26893, 29297, 29611, 33457, 39019, 39217]
theorem leaf613_5_valid : leaf613_5.Certified := by
  simp only [leaf613_5,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 317] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 503] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 17, 41] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 131] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29, 103] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 19, 43] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1319] }, .lucas { root := 13, primeFactors := [2, 659] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 17, 47] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 17, 739] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 31] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 83] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 1831] }, .lucas { root := 3, primeFactors := [2, 3, 5, 61] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 47] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 17, 41] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 929] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 19, 43] }]), by simp⟩

@[expose] def leaf613_6 : PrimeBank := .leaf [40897, 58789, 59221, 59467, 60589, 63247, 66739, 72931, 96493, 136501, 145861, 148483, 151201, 160969, 165511, 176191]
theorem leaf613_6_valid : leaf613_6.Certified := by
  simp only [leaf613_6,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 71] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 71] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 47] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17, 53] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 83, 127] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 227] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 11, 13, 17] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 17, 43] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 13, 17] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 73, 113] }]), by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 19, 353] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 613] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 839] }]), by simp⟩

@[expose] def leaf613_7 : PrimeBank := .leaf [176419, 246247, 260191, 292969, 342379, 347821, 352381, 360187, 368551, 377011, 398581, 459007, 492103, 552793, 579883, 595687]
theorem leaf613_7_valid : leaf613_7.Certified := by
  simp only [leaf613_7,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11, 13, 41] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 59] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 13, 313] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 23, 827] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 17, 31] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 839] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 173, 347] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 13] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 59, 71] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 73] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 113, 677] }]), by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 13, 701] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 31, 743] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 127, 761] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 13, 1091] }, .lucas { root := 2, primeFactors := [2, 5, 109] }]), by simp⟩

@[expose] def leaf613_8 : PrimeBank := .leaf [598303, 684757, 704761, 735307, 830833, 1191373, 1204507, 2389669, 3798019, 5471551, 11897539, 29701387]
theorem leaf613_8_valid : leaf613_8.Certified := by
  simp only [leaf613_8,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 43, 773] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 23, 827] }]), by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 7, 839] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 13, 857] }]), by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 19, 911] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 13, 1091] }, .lucas { root := 2, primeFactors := [2, 5, 109] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 61, 1097] }, .lucas { root := 3, primeFactors := [2, 137] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 47, 223] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43, 701] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 193] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 457, 4339] }, .lucas { root := 10, primeFactors := [2, 3, 241] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 13, 1049] }, .lucas { root := 3, primeFactors := [2, 131] }]), by simp⟩

@[expose] def pool613 : PrimeBank := (.branch 4657 (.branch 499 (.branch 139 leaf613_0 leaf613_1) (.branch 1093 leaf613_2 leaf613_3)) (.branch 40897 (.branch 15217 leaf613_4 leaf613_5) (.branch 176419 leaf613_6 (.branch 598303 leaf613_7 leaf613_8))))
theorem pool613_valid : pool613.Certified := ⟨⟨⟨leaf613_0_valid,leaf613_1_valid⟩,⟨leaf613_2_valid,leaf613_3_valid⟩⟩,⟨⟨leaf613_4_valid,leaf613_5_valid⟩,⟨leaf613_6_valid,⟨leaf613_7_valid,leaf613_8_valid⟩⟩⟩⟩

theorem covered613 : Range 613 637 :=
  scan_sound pool613 pool613_valid 6 613 [0, 3, 0, 0, 3, 7, 5, 3, 17, 0, 3, 5] [[(2,(.split 17923 [(2,(.raise [(31,1)]))]))], [(2,(.split 3931 [(2,(.raise [(23743,1)]))]))], [(2,(.split 6733 [(1,(.split 19 [(2,(.split 127 [(2,(.raise [(5419,1)]))]))])), (2,(.raise [(907,1)]))]))], [(2,(.split 307 [(2,(.split 43 [(2,(.split 733 [(1,(.raise [(367,1)]))]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered637 : Range 637 661 :=
  scan_sound pool613 pool613_valid 6 637 [7, 3, 0, 0, 3, 0, 11, 3, 0, 5, 3, 0] [[(2,(.split 58789 [(1,(.split 5879 []))]))], [(2,(.split 1423 [(2,(.split 96493 []))]))], [(2,(.split 1987 [(2,(.raise [(211,1), (19,1)]))]))], [(2,(.split 19 [(2,(.split 127 [(2,(.split 5419 []))]))]))], [(2,(.split 33457 [(1,(.split 16729 [(1,(.split 239 []))]))]))]]
    (by decide) (by decide +kernel)

theorem covered661 : Range 661 685 :=
  scan_sound pool613 pool613_valid 6 661 [0, 3, 5, 23, 3, 11, 0, 3, 0, 7, 3, 0] [[(2,(.split 145861 [(1,(.split 72931 []))]))], [(2,(.split 151201 [(1,(.split 23 [(2,(.split 79 []))]))]))], [(2,(.split 459007 []))], [(2,(.split 66739 []))]]
    (by decide) (by decide +kernel)

theorem covered685 : Range 685 709 :=
  scan_sound pool613 pool613_valid 6 685 [5, 3, 13, 0, 3, 5, 17, 3, 0, 19, 3, 7] [[(2,(.split 8389 [(1,(.split 839 [(2,(.raise [(19,1)]))])), (2,(.raise [(379,1)]))]))], [(2,(.split 492103 []))]]
    (by decide) (by decide +kernel)

theorem covered709 : Range 709 733 :=
  scan_sound pool613 pool613_valid 6 709 [0, 3, 23, 5, 3, 0, 7, 3, 5, 0, 3, 17] [[(2,(.split 23971 [(2,(.raise [(39019,1)]))]))], [(2,(.split 1063 [(2,(.raise [(377011,1)]))]))], [(2,(.split 176419 []))]]
    (by decide) (by decide +kernel)

theorem covered733 : Range 733 757 :=
  scan_sound pool613 pool613_valid 7 733 [0, 3, 11, 0, 3, 0, 5, 3, 7, 0, 3, 5] [[(2,(.split 9439 [(2,(.raise [(29701387,1)]))]))], [(2,(.split 26041 [(1,(.split 449 [(1,(.split 7 [(2,(.split 19 [(2,(.raise [(127,1)]))]))])), (2,(.raise [(2083,1)]))])), (2,(.raise [(11897539,1)]))]))], [(2,(.split 552793 [(1,(.split 25127 []))]))], [(2,(.split 26893 [(1,(.split 113 [(1,(.split 19 [(2,(.split 127 []))])), (2,(.raise [(991,1)]))])), (2,(.raise [(1759,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered757 : Range 757 781 :=
  scan_sound pool613 pool613_valid 7 757 [0, 3, 0, 7, 3, 13, 0, 3, 0, 5, 3, 19] [[(2,(.split 14713 [(1,(.split 1051 [(2,(.raise [(368551,1)]))])), (2,(.raise [(3798019,1)]))]))], [(2,(.split 579883 []))], [(2,(.split 6367 [(2,(.raise [(31,1), (7,1)]))]))], [(2,(.split 598303 []))]]
    (by decide) (by decide +kernel)

theorem covered781 : Range 781 805 :=
  scan_sound pool613 pool613_valid 7 781 [11, 3, 5, 0, 3, 7, 13, 3, 0, 17, 3, 11] [[(2,(.split 151 [(2,(.split 37 [(2,(.split 67 [])), (3,(.raise [(19,1)]))]))]))], [(2,(.split 4051 [(2,(.raise [(5471551,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered805 : Range 805 829 :=
  scan_sound pool613 pool613_valid 7 805 [5, 3, 0, 0, 3, 5, 19, 3, 0, 0, 3, 0] [[(2,(.split 379 [(2,(.split 787 []))]))], [(2,(.split 31 [(2,(.split 331 [(2,(.split 5233 []))]))]))], [(2,(.split 421 [(1,(.split 211 [(2,(.split 31 []))])), (2,(.split 59221 [(1,(.raise [(29611,1)]))]))]))], [(2,(.split 751 [(2,(.split 26893 [(1,(.raise [(43,1)]))]))]))], [(2,(.split 684757 [(1,(.split 342379 []))]))]]
    (by decide) (by decide +kernel)

theorem covered829 : Range 829 853 :=
  scan_sound pool613 pool613_valid 7 829 [0, 3, 7, 5, 3, 0, 29, 3, 5, 7, 3, 23] [[(2,(.split 1087 [(2,(.raise [(283,1), (211,1)]))]))], [(2,(.split 704761 [(1,(.split 352381 [(1,(.raise [(176191,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered853 : Range 853 877 :=
  scan_sound pool613 pool613_valid 7 853 [0, 3, 0, 0, 3, 0, 5, 3, 11, 13, 3, 5] [[(2,(.split 5647 [(2,(.raise [(43,1), (31,1)]))]))], [(2,(.split 735307 []))], [(2,(.split 246247 []))], [(2,(.split 15217 [(1,(.split 1087 [])), (2,(.raise [(12799,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered877 : Range 877 901 :=
  scan_sound pool613 pool613_valid 7 877 [0, 3, 0, 0, 3, 0, 7, 3, 19, 5, 3, 29] [[(2,(.split 991 [(2,(.split 277 [(1,(.raise [(139,1)]))]))]))], [(2,(.split 40897 [(1,(.split 19 [(2,(.split 127 []))]))]))], [(2,(.split 260191 []))], [(2,(.split 60589 [(1,(.split 83 [(2,(.raise [(367,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered901 : Range 901 925 :=
  scan_sound pool613 pool613_valid 8 901 [17, 3, 5, 0, 3, 0, 11, 3, 7, 0, 3, 13] [[(2,(.split 39217 [(1,(.split 19609 [(1,(.split 53 [(1,(.split 7 [(2,(.split 19 []))]))]))]))]))], [(2,(.split 830833 [(1,(.split 3271 []))]))], [(2,(.split 163 [(2,(.split 67 [(2,(.raise [(31,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered925 : Range 925 949 :=
  scan_sound pool613 pool613_valid 8 925 [5, 3, 0, 7, 3, 5, 0, 3, 0, 23, 3, 0] [[(2,(.split 5503 [(2,(.raise [(165511,1)]))]))], [(2,(.split 292969 [(1,(.split 29297 [(1,(.split 19 [(2,(.raise [(127,1)]))]))]))]))], [(2,(.split 811 [(2,(.split 1093 [(1,(.raise [(547,1)]))]))]))], [(2,(.split 463 [(2,(.split 3769 [(1,(.raise [(19,1), (7,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered949 : Range 949 973 :=
  scan_sound pool613 pool613_valid 8 949 [13, 3, 0, 5, 3, 7, 31, 3, 5, 0, 3, 0] [[(2,(.split 5023 [(2,(.raise [(63247,1)]))]))], [(2,(.split 4657 [(1,(.split 67 [(2,(.split 31 [(2,(.raise [(331,1)]))]))])), (2,(.raise [(439,1)]))]))], [(2,(.split 919 [(2,(.raise [(163,1), (79,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered973 : Range 973 997 :=
  scan_sound pool613 pool613_valid 8 973 [7, 3, 0, 11, 3, 0, 5, 3, 23, 0, 3, 5] [[(2,(.split 136501 [(1,(.split 131 [(2,(.split 17293 []))]))]))], [(2,(.split 9391 [(2,(.raise [(103,1)]))]))], [(2,(.split 277 [(1,(.split 139 [(2,(.split 499 []))])), (2,(.split 19 [(2,(.split 127 []))])), (3,(.raise [(139,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered997 : Range 997 1021 :=
  scan_sound pool613 pool613_valid 8 997 [0, 3, 7, 17, 3, 19, 0, 3, 0, 5, 3, 0] [[(2,(.split 823 [(2,(.raise [(751,1), (43,1)]))]))], [(2,(.split 9181 [(1,(.split 4591 [])), (2,(.raise [(1423,1)]))]))], [(2,(.split 14071 [(2,(.raise [(19,1)]))]))], [(2,(.split 148483 []))]]
    (by decide) (by decide +kernel)

theorem covered1021 : Range 1021 1045 :=
  scan_sound pool613 pool613_valid 8 1021 [0, 3, 5, 13, 3, 0, 0, 3, 17, 0, 3, 7] [[(2,(.split 347821 [(1,(.split 2851 []))]))], [(2,(.split 1567 [(2,(.raise [(379,1), (7,1)]))]))], [(2,(.split 2677 [(1,(.split 103 [(2,(.raise [(3571,1), (19,1)]))])), (2,(.split 2389669 []))]))], [(2,(.split 360187 []))]]
    (by decide) (by decide +kernel)

theorem covered1045 : Range 1045 1069 :=
  scan_sound pool613 pool613_valid 8 1045 [5, 3, 0, 0, 3, 5, 7, 3, 0, 0, 3, 11] [[(2,(.split 439 [(2,(.split 67 []))]))], [(2,(.split 368551 []))], [(2,(.split 160969 [(1,(.split 16097 [(1,(.raise [(2683,1), (7,1)]))]))]))], [(2,(.split 377011 []))]]
    (by decide) (by decide +kernel)

theorem covered1069 : Range 1069 1093 :=
  scan_sound pool613 pool613_valid 8 1069 [0, 3, 29, 5, 3, 13, 23, 3, 5, 0, 3, 0] [[(2,(.split 211 [(2,(.split 139 []))]))], [(2,(.split 283 [(2,(.raise [(367,1), (199,1), (7,1)]))]))], [(2,(.split 1191373 [(1,(.split 595687 []))]))]]
    (by decide) (by decide +kernel)

theorem covered1093 : Range 1093 1117 :=
  scan_sound pool613 pool613_valid 8 1093 [0, 3, 0, 7, 3, 0, 5, 3, 0, 11, 3, 5] [[(2,(.split 398581 [(1,(.split 617 [(1,(.split 103 []))]))]))], [(2,(.split 1204507 []))], [(2,(.split 2383 [(2,(.raise [(151,1)]))]))], [(2,(.split 967 [(2,(.split 4657 []))]))]]
    (by decide) (by decide +kernel)

theorem covered1117 : Range 1117 1125 :=
  scan_sound pool613 pool613_valid 8 1117 [0, 3, 19, 0] [[(2,(.split 59467 []))], [(2,(.split 127 [(2,(.split 5419 []))]))]]
    (by decide) (by decide +kernel)

theorem segment613 : Range 613 1125 := (range_join (range_join (range_join (range_join covered613 covered637) (range_join covered661 (range_join covered685 covered709))) (range_join (range_join covered733 (range_join covered757 covered781)) (range_join covered805 (range_join covered829 covered853)))) (range_join (range_join (range_join covered877 covered901) (range_join covered925 (range_join covered949 covered973))) (range_join (range_join covered997 (range_join covered1021 covered1045)) (range_join covered1069 (range_join covered1093 covered1117)))))

theorem through1125 : Range 101 1125 := (range_join through613 segment613)

end OddPerfect.HarmonicChain.HarmonicRange101
