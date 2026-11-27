module

public import OddPerfect.HarmonicRange101.Part008
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicRange101

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf4197_0 : PrimeBank := .leaf [2, 3, 7, 19, 29, 31, 37, 41, 47, 67, 79, 83, 103, 199, 283, 307]
theorem leaf4197_0_valid : leaf4197_0.Certified := by
  simp only [leaf4197_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf4197_1 : PrimeBank := .leaf [331, 367, 379, 439, 443, 463, 487, 547, 631, 727, 751, 823, 907, 967, 1051, 1093]
theorem leaf4197_1_valid : leaf4197_1.Certified := by
  simp only [leaf4197_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13] }]), by simp⟩

@[expose] def leaf4197_2 : PrimeBank := .leaf [1201, 1291, 1723, 1933, 2011, 2179, 2203, 3361, 3583, 3769, 3863, 4603, 6043, 7219, 7639, 7741]
theorem leaf4197_2_valid : leaf4197_2.Certified := by
  simp only [leaf4197_2,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 43] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 41] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 23] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 67] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 367] }]), by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 5, 7] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 199] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 157] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 1931] }, .lucas { root := 2, primeFactors := [2, 5, 193] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 59] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19, 53] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 401] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 19, 67] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 43] }]), by simp⟩

@[expose] def leaf4197_3 : PrimeBank := .leaf [8929, 9931, 11057, 11923, 13999, 14699, 15307, 21163, 30403, 35447, 39937, 44641, 48409, 55333, 62851, 94151]
theorem leaf4197_3_valid : leaf4197_3.Certified := by
  simp only [leaf4197_3,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 31] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 331] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 691] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1987] }, .lucas { root := 2, primeFactors := [2, 3, 331] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2333] }, .lucas { root := 2, primeFactors := [2, 11, 53] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7349] }, .lucas { root := 2, primeFactors := [2, 11, 167] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2551] }, .lucas { root := 6, primeFactors := [2, 3, 5, 17] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 3527] }, .lucas { root := 5, primeFactors := [2, 41, 43] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 563] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 37, 479] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13] }]), by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 31] }]), by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 2017] }, .lucas { root := 5, primeFactors := [2, 3, 7] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 29, 53] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 419] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 269] }]), by simp⟩

@[expose] def leaf4197_4 : PrimeBank := .leaf [172423, 176419, 234139, 295759, 354391, 366001, 393577, 398581, 445747, 468277, 486331, 520963, 615617, 704567, 906673, 941509]
theorem leaf4197_4_valid : leaf4197_4.Certified := by
  simp only [leaf4197_4,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 31, 103] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 39023] }, .lucas { root := 5, primeFactors := [2, 109, 179] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5477] }, .lucas { root := 2, primeFactors := [2, 37] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11813] }, .lucas { root := 2, primeFactors := [2, 2953] }, .lucas { root := 13, primeFactors := [2, 3, 41] }]), by primality (cert := .witnesses [.lucas { root := 29, primeFactors := [2, 3, 5, 61] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 23, 31] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 73] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 10613] }, .lucas { root := 2, primeFactors := [2, 7, 379] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 39023] }, .lucas { root := 5, primeFactors := [2, 109, 179] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 13, 29, 43] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 6679] }, .lucas { root := 7, primeFactors := [2, 3, 7, 53] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 9619] }, .lucas { root := 2, primeFactors := [2, 3, 7, 229] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 151, 2333] }, .lucas { root := 2, primeFactors := [2, 11, 53] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 1453] }, .lucas { root := 2, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 26153] }, .lucas { root := 3, primeFactors := [2, 7, 467] }]), by simp⟩

@[expose] def leaf4197_5 : PrimeBank := .leaf [972661, 1009153, 1295953, 1487539, 2792809, 2846119, 3287821, 5884201, 6002431, 6053461, 6156169, 6329269, 6575641, 6790561, 6899317, 7045669]
theorem leaf4197_5_valid : leaf4197_5.Certified := by
  simp only [leaf4197_5,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 29, 43] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 73] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 19, 29] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 163] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 79, 491] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 29, 1487] }, .lucas { root := 5, primeFactors := [2, 743] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37, 1481] }, .lucas { root := 3, primeFactors := [2, 5, 37] }]), by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 7, 467] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 101, 283] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 29, 71] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 179, 1433] }, .lucas { root := 3, primeFactors := [2, 179] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11, 1453] }, .lucas { root := 2, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 37, 1481] }, .lucas { root := 3, primeFactors := [2, 5, 37] }]), by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 7, 43, 47] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 37, 41, 379] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 73, 383] }]), by simp⟩

@[expose] def leaf4197_6 : PrimeBank := .leaf [7174987, 17787307, 18143341, 19443691]
theorem leaf4197_6_valid : leaf4197_6.Certified := by
  simp only [leaf4197_6,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 17, 773] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 37, 4217] }, .lucas { root := 3, primeFactors := [2, 17, 31] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 71, 4259] }, .lucas { root := 2, primeFactors := [2, 2129] }, .lucas { root := 3, primeFactors := [2, 7, 19] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 4409] }, .lucas { root := 3, primeFactors := [2, 19, 29] }]), by simp⟩

@[expose] def pool4197 : PrimeBank := (.branch 8929 (.branch 331 leaf4197_0 (.branch 1201 leaf4197_1 leaf4197_2)) (.branch 972661 (.branch 172423 leaf4197_3 leaf4197_4) (.branch 7174987 leaf4197_5 leaf4197_6)))
theorem pool4197_valid : pool4197.Certified := ⟨⟨leaf4197_0_valid,⟨leaf4197_1_valid,leaf4197_2_valid⟩⟩,⟨⟨leaf4197_3_valid,leaf4197_4_valid⟩,⟨leaf4197_5_valid,leaf4197_6_valid⟩⟩⟩

theorem covered4197 : Range 4197 4221 :=
  scan_sound pool4197 pool4197_valid 4 4197 [3, 13, 0, 3, 5, 7, 3, 0, 11, 3, 0, 0] [[(2,(.split 5884201 [(1,(.raise [(35447,1)]))]))], [(2,(.split 13999 []))], [(2,(.split 17787307 []))], [(2,(.split 1291 [(2,(.raise [(907,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered4221 : Range 4221 4245 :=
  scan_sound pool4197 pool4197_valid 5 4221 [3, 41, 5, 3, 0, 0, 3, 5, 19, 3, 0, 0] [[(2,(.split 941509 [(1,(.raise [(94151,1)]))]))], [(2,(.split 9931 []))], [(2,(.split 44641 [(1,(.split 31 [(2,(.raise [(331,1)]))]))]))], [(2,(.split 6002431 []))]]
    (by decide) (by decide +kernel)

theorem covered4245 : Range 4245 4269 :=
  scan_sound pool4197 pool4197_valid 6 4245 [3, 31, 7, 3, 0, 5, 3, 0, 0, 3, 5, 17] [[(2,(.split 3361 [(1,(.split 41 [(2,(.raise [(1723,1)])), (3,(.split 29 []))]))]))], [(2,(.split 18143341 [(1,(.split 1295953 []))]))], [(2,(.split 6053461 [(1,(.split 7741 []))]))]]
    (by decide) (by decide +kernel)

theorem covered4269 : Range 4269 4293 :=
  scan_sound pool4197 pool4197_valid 6 4269 [3, 0, 0, 3, 7, 11, 3, 0, 5, 3, 0, 7] [[(2,(.split 331 [(2,(.raise [(199,1), (7,1)]))]))], [(2,(.split 468277 [(1,(.raise [(234139,1)]))]))], [(2,(.split 31 [(2,(.split 331 []))]))], [(2,(.split 823 [(2,(.raise [(751,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered4293 : Range 4293 4317 :=
  scan_sound pool4197 pool4197_valid 6 4293 [3, 5, 0, 3, 11, 13, 3, 59, 31, 3, 19, 5] [[(2,(.split 6156169 [(1,(.split 615617 []))]))]]
    (by decide) (by decide +kernel)

theorem covered4317 : Range 4317 4341 :=
  scan_sound pool4197 pool4197_valid 6 4317 [3, 7, 29, 3, 5, 0, 3, 61, 7, 3, 0, 0] [[(2,(.split 6043 []))], [(2,(.split 21163 []))], [(2,(.split 8929 [(1,(.split 47 [(2,(.split 37 []))]))]))]]
    (by decide) (by decide +kernel)

theorem covered4341 : Range 4341 4365 :=
  scan_sound pool4197 pool4197_valid 6 4341 [3, 43, 5, 3, 0, 19, 3, 5, 0, 3, 7, 0] [[(2,(.split 62851 []))], [(2,(.split 6329269 [(1,(.split 1201 [(1,(.raise [(31,1)]))]))]))], [(2,(.split 906673 [(1,(.split 11057 [(1,(.raise [(19,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered4365 : Range 4365 4389 :=
  scan_sound pool4197 pool4197_valid 6 4365 [3, 11, 17, 3, 0, 5, 3, 29, 13, 3, 5, 41] [[(2,(.split 631 [(2,(.raise [(307,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered4389 : Range 4389 4413 :=
  scan_sound pool4197 pool4197_valid 6 4389 [3, 0, 23, 3, 0, 53, 3, 7, 5, 3, 0, 11] [[(2,(.split 393577 [(1,(.split 79 []))]))], [(2,(.split 1487539 []))], [(2,(.split 19443691 []))]]
    (by decide) (by decide +kernel)

theorem covered4413 : Range 4413 4437 :=
  scan_sound pool4197 pool4197_valid 6 4413 [3, 5, 7, 3, 0, 0, 3, 19, 43, 3, 11, 5] [[(2,(.split 2792809 [(1,(.raise [(14699,1)]))]))], [(2,(.split 4603 []))]]
    (by decide) (by decide +kernel)

theorem covered4437 : Range 4437 4461 :=
  scan_sound pool4197 pool4197_valid 6 4437 [3, 23, 0, 3, 5, 0, 3, 0, 61, 3, 0, 7] [[(2,(.split 6575641 [(1,(.split 3287821 []))]))], [(2,(.split 11923 []))], [(2,(.split 295759 []))], [(2,(.split 1933 [(1,(.split 967 [])), (2,(.raise [(19,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered4461 : Range 4461 4485 :=
  scan_sound pool4197 pool4197_valid 6 4461 [3, 0, 5, 3, 41, 17, 3, 5, 11, 3, 0, 0] [[(2,(.split 2846119 []))], [(2,(.split 2179 []))], [(2,(.split 283 [(2,(.split 367 []))]))]]
    (by decide) (by decide +kernel)

theorem covered4485 : Range 4485 4509 :=
  scan_sound pool4197 pool4197_valid 6 4485 [3, 7, 67, 3, 0, 5, 3, 11, 7, 3, 5, 0] [[(2,(.split 7219 []))], [(2,(.split 520963 []))]]
    (by decide) (by decide +kernel)

theorem covered4509 : Range 4509 4533 :=
  scan_sound pool4197 pool4197_valid 6 4509 [3, 13, 0, 3, 0, 0, 3, 0, 5, 3, 7, 23] [[(2,(.split 6790561 [(1,(.split 83 []))]))], [(2,(.split 39937 [(1,(.raise [(1051,1), (19,1), (7,1)]))]))], [(2,(.split 972661 [(1,(.raise [(486331,1)]))]))], [(2,(.split 1093 [(1,(.split 547 [])), (2,(.split 398581 []))]))]]
    (by decide) (by decide +kernel)

theorem covered4533 : Range 4533 4557 :=
  scan_sound pool4197 pool4197_valid 6 4533 [3, 5, 13, 3, 19, 7, 3, 0, 0, 3, 29, 5] [[(2,(.split 15307 []))], [(2,(.split 6899317 [(1,(.raise [(3863,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered4557 : Range 4557 4581 :=
  scan_sound pool4197 pool4197_valid 6 4557 [3, 47, 0, 3, 5, 0, 3, 7, 17, 3, 23, 19] [[(2,(.split 439 [(2,(.raise [(67,1), (7,1)]))]))], [(2,(.split 366001 [(1,(.raise [(2011,1), (19,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered4581 : Range 4581 4605 :=
  scan_sound pool4197 pool4197_valid 6 4581 [3, 0, 5, 3, 13, 0, 3, 5, 0, 3, 43, 0] [[(2,(.split 30403 []))], [(2,(.split 55333 [(1,(.split 379 []))]))], [(2,(.split 7045669 [(1,(.raise [(704567,1)]))]))], [(2,(.split 1009153 [(1,(.raise [(443,1), (67,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered4605 : Range 4605 4629 :=
  scan_sound pool4197 pool4197_valid 6 4605 [3, 17, 11, 3, 7, 5, 3, 31, 0, 3, 5, 7] [[(2,(.split 3583 []))]]
    (by decide) (by decide +kernel)

theorem covered4629 : Range 4629 4653 :=
  scan_sound pool4197 pool4197_valid 6 4629 [3, 11, 41, 3, 0, 0, 3, 0, 5, 3, 0, 0] [[(2,(.split 487 [(2,(.raise [(79,1)]))]))], [(2,(.split 7174987 []))], [(2,(.split 727 [(2,(.raise [(176419,1)]))]))], [(2,(.split 354391 []))], [(2,(.split 463 [(2,(.split 3769 []))]))]]
    (by decide) (by decide +kernel)

theorem covered4653 : Range 4653 4677 :=
  scan_sound pool4197 pool4197_valid 6 4653 [3, 5, 0, 3, 59, 0, 3, 13, 7, 3, 0, 5] [[(2,(.split 439 [(2,(.raise [(67,1), (7,1)]))]))], [(2,(.split 7639 []))], [(2,(.split 445747 []))]]
    (by decide) (by decide +kernel)

theorem covered4677 : Range 4677 4701 :=
  scan_sound pool4197 pool4197_valid 6 4677 [3, 0, 31, 3, 5, 43, 3, 0, 13, 3, 7, 37] [[(2,(.split 172423 []))], [(2,(.split 2203 []))]]
    (by decide) (by decide +kernel)

theorem covered4701 : Range 4701 4709 :=
  scan_sound pool4197 pool4197_valid 6 4701 [3, 0, 5, 3] [[(2,(.split 48409 [(1,(.split 103 []))]))]]
    (by decide) (by decide +kernel)

theorem segment4197 : Range 4197 4709 := (range_join (range_join (range_join (range_join covered4197 covered4221) (range_join covered4245 (range_join covered4269 covered4293))) (range_join (range_join covered4317 (range_join covered4341 covered4365)) (range_join covered4389 (range_join covered4413 covered4437)))) (range_join (range_join (range_join covered4461 covered4485) (range_join covered4509 (range_join covered4533 covered4557))) (range_join (range_join covered4581 (range_join covered4605 covered4629)) (range_join covered4653 (range_join covered4677 covered4701)))))

theorem through4709 : Range 101 4709 := (range_join through4197 segment4197)

end OddPerfect.HarmonicChain.HarmonicRange101
