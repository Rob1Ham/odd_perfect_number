module

public import OddPerfect.HarmonicRange101.Part009
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicRange101

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf4709_0 : PrimeBank := .leaf [2, 3, 7, 19, 23, 31, 43, 47, 67, 79, 83, 107, 127, 139, 151, 163]
theorem leaf4709_0_valid : leaf4709_0.Certified := by
  simp only [leaf4709_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf4709_1 : PrimeBank := .leaf [229, 271, 283, 331, 491, 547, 571, 613, 631, 787, 821, 907, 1033, 1093, 1129, 1291]
theorem leaf4709_1_valid : leaf4709_1.Certified := by
  simp only [leaf4709_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 43] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 47] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 43] }]), by simp⟩

@[expose] def leaf4709_2 : PrimeBank := .leaf [1609, 2003, 2543, 2551, 2683, 2767, 3793, 5419, 5647, 7489, 8209, 9103, 9337, 14143, 15149, 16183]
theorem leaf4709_2_valid : leaf4709_2.Certified := by
  simp only [leaf4709_2,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 67] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 11, 13] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 31, 41] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 17] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 149] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 461] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 79] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 941] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 13] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 19] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 37, 41] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 389] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2357] }, .lucas { root := 2, primeFactors := [2, 19, 31] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 541] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 29, 31] }]), by simp⟩

@[expose] def leaf4709_3 : PrimeBank := .leaf [16693, 26683, 28711, 47737, 53323, 61879, 63247, 64879, 65729, 78283, 84871, 92723, 96079, 120947, 123757, 129757]
theorem leaf4709_3_valid : leaf4709_3.Certified := by
  simp only [leaf4709_3,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 107] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 4447] }, .lucas { root := 3, primeFactors := [2, 3, 13, 19] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11, 29] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 17] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 8887] }, .lucas { root := 3, primeFactors := [2, 3, 1481] }, .lucas { root := 3, primeFactors := [2, 5, 37] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 10313] }, .lucas { root := 3, primeFactors := [2, 1289] }, .lucas { root := 6, primeFactors := [2, 7, 23] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 83, 127] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 11, 983] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 79] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 4349] }, .lucas { root := 2, primeFactors := [2, 1087] }, .lucas { root := 3, primeFactors := [2, 3, 181] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 23, 41] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 37, 179] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 67, 239] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 53, 163] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 10313] }, .lucas { root := 3, primeFactors := [2, 1289] }, .lucas { root := 6, primeFactors := [2, 7, 23] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 983] }]), by simp⟩

@[expose] def leaf4709_4 : PrimeBank := .leaf [470653, 503593, 624031, 657289, 863497, 1187383, 1242217, 1248061, 1763089, 1792507, 3585013, 3785251, 3823219, 3842401, 3847273, 7550947]
theorem leaf4709_4_valid : leaf4709_4.Certified := by
  simp only [leaf4709_4,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13, 431] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 20983] }, .lucas { root := 3, primeFactors := [2, 3, 13, 269] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 11, 31, 61] }]), by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 17, 179] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 67, 179] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 17, 1663] }, .lucas { root := 3, primeFactors := [2, 3, 277] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 71] }]), by primality (cert := .witnesses [.lucas { root := 18, primeFactors := [2, 3, 5, 11, 31, 61] }]), by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 23, 1597] }, .lucas { root := 11, primeFactors := [2, 3, 7, 19] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 179, 1669] }, .lucas { root := 2, primeFactors := [2, 3, 139] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 179, 1669] }, .lucas { root := 2, primeFactors := [2, 3, 139] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 103] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 19, 1597] }, .lucas { root := 11, primeFactors := [2, 3, 7, 19] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 1601] }, .lucas { root := 3, primeFactors := [2, 5] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 13, 19, 59] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 23, 61] }]), by simp⟩

@[expose] def leaf4709_5 : PrimeBank := .leaf [7646437, 7684801, 8192269, 8331667, 8715961, 8901019, 9004669, 12698281, 22292563, 22406023, 22576753, 23790007, 23907211, 24735703, 25035013, 25396561]
theorem leaf4709_5_valid : leaf4709_5.Certified := by
  simp only [leaf4709_5,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 19, 1597] }, .lucas { root := 11, primeFactors := [2, 3, 7, 19] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 1601] }, .lucas { root := 3, primeFactors := [2, 5] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 19, 29, 59] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 17, 1667] }, .lucas { root := 2, primeFactors := [2, 7, 17] }]), by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 11, 31, 71] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 41, 1723] }, .lucas { root := 3, primeFactors := [2, 3, 7, 41] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 433, 1733] }, .lucas { root := 2, primeFactors := [2, 433] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 5039] }, .lucas { root := 11, primeFactors := [2, 11, 229] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 787, 4721] }, .lucas { root := 6, primeFactors := [2, 5, 59] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 263, 4733] }, .lucas { root := 5, primeFactors := [2, 7, 13] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 4751] }, .lucas { root := 19, primeFactors := [2, 5, 19] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 271, 4877] }, .lucas { root := 2, primeFactors := [2, 23, 53] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 163, 4889] }, .lucas { root := 3, primeFactors := [2, 13, 47] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 829, 4973] }, .lucas { root := 2, primeFactors := [2, 11, 113] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 139, 5003] }, .lucas { root := 2, primeFactors := [2, 41, 61] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 5039] }, .lucas { root := 11, primeFactors := [2, 11, 229] }]), by simp⟩

@[expose] def leaf4709_6 : PrimeBank := .leaf [25882657]
theorem leaf4709_6_valid : leaf4709_6.Certified := by
  simp only [leaf4709_6,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 53, 5087] }, .lucas { root := 5, primeFactors := [2, 2543] }, .lucas { root := 5, primeFactors := [2, 31, 41] }]), by simp⟩

@[expose] def pool4709 : PrimeBank := (.branch 16693 (.branch 229 leaf4709_0 (.branch 1609 leaf4709_1 leaf4709_2)) (.branch 7646437 (.branch 470653 leaf4709_3 leaf4709_4) (.branch 25882657 leaf4709_5 leaf4709_6)))
theorem pool4709_valid : pool4709.Certified := ⟨⟨leaf4709_0_valid,⟨leaf4709_1_valid,leaf4709_2_valid⟩⟩,⟨⟨leaf4709_3_valid,leaf4709_4_valid⟩,⟨leaf4709_5_valid,leaf4709_6_valid⟩⟩⟩

theorem covered4709 : Range 4709 4733 :=
  scan_sound pool4709 pool4709_valid 4 4709 [17, 7, 3, 5, 53, 3, 0, 0, 3, 29, 0, 3] [[(2,(.split 22292563 []))], [(2,(.split 9103 []))], [(2,(.split 2683 []))]]
    (by decide) (by decide +kernel)

theorem covered4733 : Range 4733 4757 :=
  scan_sound pool4709 pool4709_valid 4 4733 [0, 5, 3, 7, 11, 3, 5, 47, 3, 0, 7, 3] [[(2,(.split 22406023 []))], [(2,(.split 22576753 [(1,(.raise [(2543,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered4757 : Range 4757 4781 :=
  scan_sound pool4709 pool4709_valid 4 4757 [67, 0, 3, 11, 5, 3, 19, 13, 3, 5, 17, 3] [[(2,(.split 7550947 []))]]
    (by decide) (by decide +kernel)

theorem covered4781 : Range 4781 4805 :=
  scan_sound pool4709 pool4709_valid 5 4781 [7, 0, 3, 0, 0, 3, 0, 5, 3, 0, 0, 3] [[(2,(.split 7 []))], [(2,(.split 1763089 [(1,(.split 283 []))]))], [(2,(.split 7646437 [(1,(.raise [(3823219,1)]))]))], [(2,(.split 5647 []))], [(2,(.split 151 [(2,(.split 1093 [(1,(.raise [(547,1)]))]))]))], [(2,(.split 7684801 [(1,(.split 3842401 []))]))]]
    (by decide) (by decide +kernel)

theorem covered4805 : Range 4805 4829 :=
  scan_sound pool4709 pool4709_valid 5 4805 [5, 11, 3, 17, 0, 3, 0, 61, 3, 7, 5, 3] [[(2,(.split 84871 []))], [(2,(.split 1291 [(2,(.raise [(907,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered4829 : Range 4829 4853 :=
  scan_sound pool4709 pool4709_valid 5 4829 [11, 0, 3, 5, 7, 3, 47, 29, 3, 37, 13, 3] [[(2,(.split 47737 [(1,(.split 163 []))]))]]
    (by decide) (by decide +kernel)

theorem covered4853 : Range 4853 4877 :=
  scan_sound pool4709 pool4709_valid 5 4853 [23, 5, 3, 43, 0, 3, 5, 31, 3, 0, 11, 3] [[(2,(.split 67 [(2,(.split 3793 [(1,(.raise [(271,1)]))]))]))], [(2,(.split 96079 []))]]
    (by decide) (by decide +kernel)

theorem covered4877 : Range 4877 4901 :=
  scan_sound pool4709 pool4709_valid 5 4877 [0, 7, 3, 19, 5, 3, 0, 67, 3, 5, 59, 3] [[(2,(.split 23790007 []))], [(2,(.split 23907211 []))]]
    (by decide) (by decide +kernel)

theorem covered4901 : Range 4901 4925 :=
  scan_sound pool4709 pool4709_valid 6 4901 [13, 0, 3, 7, 0, 3, 17, 5, 3, 0, 7, 3] [[(2,(.split 1129 [(1,(.split 31 [(2,(.split 331 []))])), (2,(.raise [(79,1)]))]))], [(2,(.split 19 [(2,(.split 127 [(2,(.raise [(5419,1)]))]))]))], [(2,(.split 26683 []))]]
    (by decide) (by decide +kernel)

theorem covered4925 : Range 4925 4949 :=
  scan_sound pool4709 pool4709_valid 7 4925 [5, 13, 3, 0, 0, 3, 0, 11, 3, 0, 5, 3] [[(2,(.split 657289 [(1,(.split 65729 []))]))], [(2,(.split 331 [(2,(.raise [(127,1), (7,1)]))]))], [(2,(.split 9337 [(1,(.split 23 [(2,(.raise [(79,1)]))]))]))], [(2,(.split 8209 [(1,(.split 821 [(1,(.split 229 [(1,(.split 23 []))]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered4949 : Range 4949 4973 :=
  scan_sound pool4709 pool4709_valid 7 4949 [7, 0, 3, 5, 0, 3, 11, 7, 3, 0, 0, 3] [[(2,(.split 43 [(2,(.split 631 []))]))], [(2,(.split 8192269 [(1,(.raise [(2003,1)]))]))], [(2,(.split 503593 [(1,(.raise [(2767,1), (7,3)]))]))], [(2,(.split 1033 [(1,(.split 47 [(2,(.split 613 []))])), (2,(.raise [(19,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered4973 : Range 4973 4997 :=
  scan_sound pool4709 pool4709_valid 7 4973 [0, 5, 3, 13, 17, 3, 5, 0, 3, 7, 0, 3] [[(2,(.split 24735703 []))], [(2,(.split 123757 [(1,(.raise [(61879,1), (67,1)]))]))], [(2,(.split 1187383 []))]]
    (by decide) (by decide +kernel)

theorem covered4997 : Range 4997 5021 :=
  scan_sound pool4709 pool4709_valid 7 4997 [19, 0, 3, 0, 5, 3, 0, 0, 3, 5, 29, 3] [[(2,(.split 8331667 []))], [(2,(.split 25035013 [(1,(.raise [(907,1)]))]))], [(2,(.split 3585013 [(1,(.raise [(1792507,1)]))]))], [(2,(.split 53323 []))]]
    (by decide) (by decide +kernel)

theorem covered5021 : Range 5021 5045 :=
  scan_sound pool4709 pool4709_valid 7 5021 [0, 0, 3, 11, 47, 3, 7, 5, 3, 0, 71, 3] [[(2,(.split 7489 [(1,(.split 107 []))]))], [(2,(.split 63247 []))], [(2,(.split 25396561 [(1,(.split 12698281 []))]))]]
    (by decide) (by decide +kernel)

theorem covered5045 : Range 5045 5069 :=
  scan_sound pool4709 pool4709_valid 7 5045 [5, 7, 3, 0, 31, 3, 13, 0, 3, 61, 5, 3] [[(2,(.split 2551 []))], [(2,(.split 78283 []))]]
    (by decide) (by decide +kernel)

theorem covered5069 : Range 5069 5093 :=
  scan_sound pool4709 pool4709_valid 7 5069 [37, 11, 3, 5, 0, 3, 0, 13, 3, 0, 7, 3] [[(2,(.split 1609 [(1,(.split 7 [])), (2,(.split 863497 []))]))], [(2,(.split 129757 [(1,(.raise [(64879,1)]))]))], [(2,(.split 25882657 [(1,(.raise [(120947,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered5093 : Range 5093 5117 :=
  scan_sound pool4709 pool4709_valid 7 5093 [11, 5, 3, 0, 0, 3, 5, 0, 3, 19, 0, 3] [[(2,(.split 127 [(2,(.raise [(5419,1)]))]))], [(2,(.split 787 [(2,(.split 151 []))]))], [(2,(.split 1242217 [(1,(.split 15149 [(1,(.raise [(7,1)]))]))]))], [(2,(.split 8715961 [(1,(.raise [(92723,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered5117 : Range 5117 5141 :=
  scan_sound pool4709 pool4709_valid 7 5117 [7, 0, 3, 47, 5, 3, 23, 7, 3, 5, 11, 3] [[(2,(.split 1248061 [(1,(.raise [(624031,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered5141 : Range 5141 5165 :=
  scan_sound pool4709 pool4709_valid 7 5141 [53, 37, 3, 0, 19, 3, 0, 5, 3, 7, 13, 3] [[(2,(.split 3785251 []))], [(2,(.split 16693 [(1,(.split 491 []))]))]]
    (by decide) (by decide +kernel)

theorem covered5165 : Range 5165 5189 :=
  scan_sound pool4709 pool4709_valid 7 5165 [5, 0, 3, 0, 7, 3, 31, 0, 3, 71, 5, 3] [[(2,(.split 8901019 []))], [(2,(.split 14143 []))], [(2,(.split 470653 [(1,(.split 139 []))]))]]
    (by decide) (by decide +kernel)

theorem covered5189 : Range 5189 5213 :=
  scan_sound pool4709 pool4709_valid 7 5189 [0, 29, 3, 5, 0, 3, 7, 11, 3, 41, 0, 3] [[(2,(.split 3847273 [(1,(.raise [(28711,1)]))]))], [(2,(.split 9004669 [(1,(.raise [(571,1), (83,1)]))]))], [(2,(.split 16183 []))]]
    (by decide) (by decide +kernel)

theorem covered5213 : Range 5213 5221 :=
  scan_sound pool4709 pool4709_valid 7 5213 [13, 5, 3, 17] []
    (by decide) (by decide +kernel)

theorem segment4709 : Range 4709 5221 := (range_join (range_join (range_join (range_join covered4709 covered4733) (range_join covered4757 (range_join covered4781 covered4805))) (range_join (range_join covered4829 (range_join covered4853 covered4877)) (range_join covered4901 (range_join covered4925 covered4949)))) (range_join (range_join (range_join covered4973 covered4997) (range_join covered5021 (range_join covered5045 covered5069))) (range_join (range_join covered5093 (range_join covered5117 covered5141)) (range_join covered5165 (range_join covered5189 covered5213)))))

theorem through5221 : Range 101 5221 := (range_join through4709 segment4709)

end OddPerfect.HarmonicChain.HarmonicRange101
