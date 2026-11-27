module

public import OddPerfect.HarmonicRange101.Part005
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicRange101

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf2661_0 : PrimeBank := .leaf [2, 3, 7, 17, 19, 31, 43, 47, 61, 79, 83, 127, 199, 211, 271, 307]
theorem leaf2661_0_valid : leaf2661_0.Certified := by
  simp only [leaf2661_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf2661_1 : PrimeBank := .leaf [331, 367, 479, 487, 613, 631, 643, 859, 1031, 1033, 1129, 1321, 1327, 1597, 1901, 2311]
theorem leaf2661_1_valid : leaf2661_1.Certified := by
  simp only [leaf2661_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 103] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 43] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 47] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 11] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 17] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 19] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 19] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 11] }]), by simp⟩

@[expose] def leaf2661_2 : PrimeBank := .leaf [2467, 2707, 2791, 3463, 3583, 3853, 3919, 4373, 4621, 4783, 4789, 4933, 4951, 5419, 5779, 7937]
theorem leaf2661_2_valid : leaf2661_2.Certified := by
  simp only [leaf2661_2,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 137] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 41] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 31] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 577] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 199] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 107] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 653] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 1093] }, .lucas { root := 5, primeFactors := [2, 3, 7, 13] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 11] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 797] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 19] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 137] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 107] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 31] }]), by simp⟩

@[expose] def leaf2661_3 : PrimeBank := .leaf [8161, 9283, 10867, 12043, 13267, 13591, 20749, 24697, 25087, 28387, 30367, 34939, 40771, 64633, 65983, 70607]
theorem leaf2661_3_valid : leaf2661_3.Certified := by
  simp only [leaf2661_3,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 17] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 17] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1811] }, .lucas { root := 6, primeFactors := [2, 5, 181] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 223] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 67] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 151] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 19] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 37, 113] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 83] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 241] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 647] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 151] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 2693] }, .lucas { root := 2, primeFactors := [2, 673] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 1571] }, .lucas { root := 2, primeFactors := [2, 5, 157] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 43, 821] }]), by simp⟩

@[expose] def leaf2661_4 : PrimeBank := .leaf [76519, 77023, 78713, 79531, 172759, 187963, 199807, 238967, 246247, 247069, 323647, 364717, 372667, 430957, 442831, 446323]
theorem leaf2661_4_valid : leaf2661_4.Certified := by
  simp only [leaf2661_4,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 109] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 389] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 9839] }, .lucas { root := 7, primeFactors := [2, 4919] }, .lucas { root := 13, primeFactors := [2, 2459] }, .lucas { root := 2, primeFactors := [2, 1229] }, .lucas { root := 2, primeFactors := [2, 307] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 241] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 28793] }, .lucas { root := 3, primeFactors := [2, 59, 61] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 31327] }, .lucas { root := 6, primeFactors := [2, 3, 23, 227] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 33301] }, .lucas { root := 2, primeFactors := [2, 3, 5, 37] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 13, 101] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11, 13, 41] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 6863] }, .lucas { root := 5, primeFactors := [2, 47, 73] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 19, 167] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 307] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 7, 19, 467] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11971] }, .lucas { root := 10, primeFactors := [2, 3, 5, 7, 19] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 29, 509] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 73, 1019] }]), by simp⟩

@[expose] def leaf2661_5 : PrimeBank := .leaf [506731, 555589, 1254619, 1674289, 2389669, 2465227, 2619871, 2676241, 2907721, 3161107, 3247921, 3348577, 4534567, 7094233, 7450171, 7781311]
theorem leaf2661_5_valid : leaf2661_5.Certified := by
  simp only [leaf2661_5,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 7, 19, 127] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 23, 61] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 47, 1483] }, .lucas { root := 2, primeFactors := [2, 3, 13, 19] }]), by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 7, 11, 151] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 47, 223] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 151, 907] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 11, 17, 467] }]), by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 7, 59] }]), by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 41, 197] }]), by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 13, 19, 79] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 13, 347] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 11, 151] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 251, 3011] }, .lucas { root := 2, primeFactors := [2, 5, 7, 43] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 37, 2663] }, .lucas { root := 5, primeFactors := [2, 11] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 13, 2729] }, .lucas { root := 3, primeFactors := [2, 11, 31] }]), by primality (cert := .witnesses [.lucas { root := 21, primeFactors := [2, 3, 5, 31, 2789] }, .lucas { root := 2, primeFactors := [2, 17, 41] }]), by simp⟩

@[expose] def leaf2661_6 : PrimeBank := .leaf [8746807, 8817931, 9069133, 9250723, 9843907]
theorem leaf2661_6_valid : leaf2661_6.Certified := by
  simp only [leaf2661_6,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 29, 2957] }, .lucas { root := 2, primeFactors := [2, 739] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 11, 2969] }, .lucas { root := 3, primeFactors := [2, 7, 53] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 251, 3011] }, .lucas { root := 2, primeFactors := [2, 5, 7, 43] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 13, 3041] }, .lucas { root := 3, primeFactors := [2, 5, 19] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 523, 3137] }, .lucas { root := 3, primeFactors := [2, 7] }]), by simp⟩

@[expose] def pool2661 : PrimeBank := (.branch 8161 (.branch 331 leaf2661_0 (.branch 2467 leaf2661_1 leaf2661_2)) (.branch 506731 (.branch 76519 leaf2661_3 leaf2661_4) (.branch 8746807 leaf2661_5 leaf2661_6)))
theorem pool2661_valid : pool2661.Certified := ⟨⟨leaf2661_0_valid,⟨leaf2661_1_valid,leaf2661_2_valid⟩⟩,⟨⟨leaf2661_3_valid,leaf2661_4_valid⟩,⟨leaf2661_5_valid,leaf2661_6_valid⟩⟩⟩

theorem covered2661 : Range 2661 2685 :=
  scan_sound pool2661 pool2661_valid 5 2661 [3, 0, 5, 3, 17, 0, 3, 5, 0, 3, 7, 0] [[(2,(.split 7094233 [(1,(.raise [(506731,1)]))]))], [(2,(.split 31 [(2,(.split 331 []))]))], [(2,(.split 2389669 [(1,(.raise [(238967,1)]))]))], [(2,(.split 2467 [(2,(.raise [(271,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered2685 : Range 2685 2709 :=
  scan_sound pool2661 pool2661_valid 6 2685 [3, 0, 0, 3, 0, 5, 3, 0, 37, 3, 5, 0] [[(2,(.split 555589 [(1,(.split 7937 [(1,(.split 7 []))]))]))], [(2,(.split 4951 [(2,(.raise [(487,1)]))]))], [(2,(.split 199 [(2,(.raise [(13267,1)]))]))], [(2,(.split 2791 [(2,(.raise [(199807,1)]))]))], [(2,(.split 187963 []))]]
    (by decide) (by decide +kernel)

theorem covered2709 : Range 2709 2733 :=
  scan_sound pool2661 pool2661_valid 6 2709 [3, 0, 0, 3, 11, 0, 3, 7, 5, 3, 0, 0] [[(2,(.split 28387 []))], [(2,(.split 3853 [(1,(.split 47 [(2,(.split 61 [(1,(.raise [(31,1)]))]))])), (2,(.raise [(30367,1)]))]))], [(2,(.split 2465227 []))], [(2,(.split 7450171 []))], [(2,(.split 40771 []))]]
    (by decide) (by decide +kernel)

theorem covered2733 : Range 2733 2757 :=
  scan_sound pool2661 pool2661_valid 6 2733 [3, 5, 7, 3, 0, 13, 3, 41, 0, 3, 0, 5] [[(2,(.split 13591 []))], [(2,(.split 3919 [(2,(.raise [(643,1)]))]))], [(2,(.split 34939 []))]]
    (by decide) (by decide +kernel)

theorem covered2757 : Range 2757 2781 :=
  scan_sound pool2661 pool2661_valid 6 2757 [3, 31, 11, 3, 5, 0, 3, 17, 47, 3, 0, 7] [[(2,(.split 364717 [(1,(.split 631 []))]))], [(2,(.split 79531 []))]]
    (by decide) (by decide +kernel)

theorem covered2781 : Range 2781 2805 :=
  scan_sound pool2661 pool2661_valid 6 2781 [3, 11, 5, 3, 0, 0, 3, 5, 0, 3, 0, 0] [[(2,(.split 7781311 []))], [(2,(.split 199807 []))], [(2,(.split 372667 []))], [(2,(.split 4933 [(1,(.split 2467 []))]))], [(2,(.split 2619871 []))]]
    (by decide) (by decide +kernel)

theorem covered2805 : Range 2805 2829 :=
  scan_sound pool2661 pool2661_valid 6 2805 [3, 7, 53, 3, 29, 5, 3, 0, 7, 3, 5, 11] [[(2,(.split 19 []))]]
    (by decide) (by decide +kernel)

theorem covered2829 : Range 2829 2853 :=
  scan_sound pool2661 pool2661_valid 8 2829 [3, 19, 0, 3, 0, 17, 3, 0, 5, 3, 7, 0] [[(2,(.split 2676241 [(1,(.split 78713 [(1,(.split 4373 [(1,(.split 17 [(1,(.three (.owed 3 11 2 []) []))]))]))]))]))], [(2,(.split 859 [(2,(.raise [(246247,1)]))]))], [(2,(.split 9283 []))], [(2,(.split 5779 []))]]
    (by decide) (by decide +kernel)

theorem covered2853 : Range 2853 2877 :=
  scan_sound pool2661 pool2661_valid 8 2853 [3, 5, 0, 3, 0, 7, 3, 47, 19, 3, 13, 5] [[(2,(.split 4621 [(1,(.split 2311 [])), (2,(.raise [(3583,1)]))]))], [(2,(.split 430957 [(1,(.split 1031 []))]))]]
    (by decide) (by decide +kernel)

theorem covered2877 : Range 2877 2901 :=
  scan_sound pool2661 pool2661_valid 8 2877 [3, 0, 43, 3, 5, 0, 3, 7, 11, 3, 0, 13] [[(2,(.split 10867 []))], [(2,(.split 64633 [(1,(.split 1901 [(1,(.split 43 []))]))]))], [(2,(.split 77023 []))]]
    (by decide) (by decide +kernel)

theorem covered2901 : Range 2901 2925 :=
  scan_sound pool2661 pool2661_valid 8 2901 [3, 0, 5, 3, 0, 41, 3, 5, 0, 3, 23, 37] [[(2,(.split 8161 [(1,(.split 1033 [(1,(.split 47 []))]))]))], [(2,(.split 172759 []))], [(2,(.split 65983 []))]]
    (by decide) (by decide +kernel)

theorem covered2925 : Range 2925 2949 :=
  scan_sound pool2661 pool2661_valid 8 2925 [3, 0, 29, 3, 7, 5, 3, 0, 17, 3, 5, 7] [[(2,(.split 5779 []))], [(2,(.split 211 [(2,(.split 1321 [(1,(.split 31 []))]))]))]]
    (by decide) (by decide +kernel)

theorem covered2949 : Range 2949 2973 :=
  scan_sound pool2661 pool2661_valid 8 2949 [3, 13, 0, 3, 0, 11, 3, 0, 5, 3, 0, 0] [[(2,(.split 2907721 [(1,(.raise [(76519,1)]))]))], [(2,(.split 8746807 []))], [(2,(.split 1254619 []))], [(2,(.split 8817931 []))], [(2,(.split 1597 [(1,(.split 47 [(2,(.split 19 []))])), (2,(.raise [(271,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered2973 : Range 2973 2997 :=
  scan_sound pool2661 pool2661_valid 8 2973 [3, 5, 13, 3, 11, 19, 3, 29, 7, 3, 41, 5] []
    (by decide) (by decide +kernel)

theorem covered2997 : Range 2997 3021 :=
  scan_sound pool2661 pool2661_valid 8 2997 [3, 0, 0, 3, 5, 31, 3, 0, 23, 3, 7, 0] [[(2,(.split 1129 [(1,(.split 613 [(1,(.split 307 []))])), (2,(.raise [(79,1)]))]))], [(2,(.split 1327 [(2,(.raise [(2707,1)]))]))], [(2,(.split 9069133 [(1,(.raise [(4534567,1)]))]))], [(2,(.split 367 [(2,(.raise [(3463,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered3021 : Range 3021 3045 :=
  scan_sound pool2661 pool2661_valid 8 3021 [3, 0, 5, 3, 13, 7, 3, 5, 0, 3, 0, 17] [[(2,(.split 247069 [(1,(.split 31 [(2,(.raise [(331,1)]))]))]))], [(2,(.split 4783 []))], [(2,(.split 9250723 []))]]
    (by decide) (by decide +kernel)

theorem covered3045 : Range 3045 3069 :=
  scan_sound pool2661 pool2661_valid 8 3045 [3, 11, 0, 3, 43, 5, 3, 7, 0, 3, 5, 0] [[(2,(.split 442831 []))], [(2,(.split 446323 []))], [(2,(.split 24697 [(1,(.split 127 [(2,(.raise [(5419,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered3069 : Range 3069 3093 :=
  scan_sound pool2661 pool2661_valid 8 3069 [3, 37, 7, 3, 17, 0, 3, 0, 5, 3, 0, 11] [[(2,(.split 3161107 []))], [(2,(.split 25087 []))], [(2,(.split 43 [(2,(.split 631 []))]))]]
    (by decide) (by decide +kernel)

theorem covered3093 : Range 3093 3117 :=
  scan_sound pool2661 pool2661_valid 8 3093 [3, 5, 19, 3, 7, 29, 3, 13, 0, 3, 11, 5] [[(2,(.split 4789 [(1,(.split 479 []))]))]]
    (by decide) (by decide +kernel)

theorem covered3117 : Range 3117 3141 :=
  scan_sound pool2661 pool2661_valid 8 3117 [3, 0, 0, 3, 5, 53, 3, 31, 13, 3, 0, 43] [[(2,(.split 20749 [(1,(.split 83 [(2,(.raise [(367,1)]))]))]))], [(2,(.split 3247921 [(1,(.raise [(70607,1)]))]))], [(2,(.split 9843907 []))]]
    (by decide) (by decide +kernel)

theorem covered3141 : Range 3141 3165 :=
  scan_sound pool2661 pool2661_valid 8 3141 [3, 7, 5, 3, 47, 23, 3, 5, 7, 3, 29, 0] [[(2,(.split 12043 []))]]
    (by decide) (by decide +kernel)

theorem covered3165 : Range 3165 3173 :=
  scan_sound pool2661 pool2661_valid 8 3165 [3, 0, 0, 3] [[(2,(.split 323647 []))], [(2,(.split 3348577 [(1,(.split 1674289 []))]))]]
    (by decide) (by decide +kernel)

theorem segment2661 : Range 2661 3173 := (range_join (range_join (range_join (range_join covered2661 covered2685) (range_join covered2709 (range_join covered2733 covered2757))) (range_join (range_join covered2781 (range_join covered2805 covered2829)) (range_join covered2853 (range_join covered2877 covered2901)))) (range_join (range_join (range_join covered2925 covered2949) (range_join covered2973 (range_join covered2997 covered3021))) (range_join (range_join covered3045 (range_join covered3069 covered3093)) (range_join covered3117 (range_join covered3141 covered3165)))))

theorem through3173 : Range 101 3173 := (range_join through2661 segment2661)

end OddPerfect.HarmonicChain.HarmonicRange101
