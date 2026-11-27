module

public import OddPerfect.HarmonicRange101.Part010
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicRange101

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf5221_0 : PrimeBank := .leaf [2, 3, 7, 19, 23, 31, 43, 47, 61, 67, 71, 79, 103, 127, 131, 163]
theorem leaf5221_0_valid : leaf5221_0.Certified := by
  simp only [leaf5221_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf5221_1 : PrimeBank := .leaf [167, 211, 331, 631, 967, 1009, 1123, 1279, 1531, 2027, 2647, 3019, 3343, 3407, 3877, 4651]
theorem leaf5221_1_valid : leaf5221_1.Certified := by
  simp only [leaf5221_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 71] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 1013] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 503] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 557] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 131] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 19] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 31] }]), by simp⟩

@[expose] def leaf5221_2 : PrimeBank := .leaf [5419, 5851, 6037, 6673, 7753, 9199, 12161, 12967, 16703, 17029, 20269, 28867, 34123, 36643, 39343, 41143]
theorem leaf5221_2_valid : leaf5221_2.Certified := by
  simp only [leaf5221_2,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 503] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 139] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 17, 19] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 73] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 19] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2161] }, .lucas { root := 23, primeFactors := [2, 3, 5] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 1193] }, .lucas { root := 3, primeFactors := [2, 149] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11, 43] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 563] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 283] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 47] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 31, 197] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 79, 83] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 6857] }, .lucas { root := 3, primeFactors := [2, 857] }]), by simp⟩

@[expose] def leaf5221_3 : PrimeBank := .leaf [42073, 42307, 96601, 108541, 134353, 136849, 155047, 165511, 173617, 193201, 217429, 246187, 267541, 273697, 342949, 347233]
theorem leaf5221_3_valid : leaf5221_3.Certified := by
  simp only [leaf5221_3,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1753] }, .lucas { root := 7, primeFactors := [2, 3, 73] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 641] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 23] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 67] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 311] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 2851] }, .lucas { root := 2, primeFactors := [2, 3, 5, 19] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 25841] }, .lucas { root := 3, primeFactors := [2, 5, 17, 19] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 613] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 3617] }, .lucas { root := 3, primeFactors := [2, 113] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 23] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 18119] }, .lucas { root := 17, primeFactors := [2, 9059] }, .lucas { root := 2, primeFactors := [2, 7, 647] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 47, 97] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 13] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 2851] }, .lucas { root := 2, primeFactors := [2, 3, 5, 19] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 28579] }, .lucas { root := 2, primeFactors := [2, 3, 11, 433] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 3617] }, .lucas { root := 3, primeFactors := [2, 113] }]), by simp⟩

@[expose] def leaf5221_4 : PrimeBank := .leaf [350983, 357619, 398491, 456679, 477721, 513001, 715237, 1029527, 1395523, 1477111, 1505893, 2045611, 2188171, 2257639, 2389531, 3909799]
theorem leaf5221_4_valid : leaf5221_4.Certified := by
  simp only [leaf5221_4,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 31, 37] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 3137] }, .lucas { root := 3, primeFactors := [2, 7] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 37, 359] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2819] }, .lucas { root := 2, primeFactors := [2, 1409] }, .lucas { root := 3, primeFactors := [2, 11] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 1327] }, .lucas { root := 3, primeFactors := [2, 3, 13, 17] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 19] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19, 3137] }, .lucas { root := 3, primeFactors := [2, 7] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 23, 22381] }, .lucas { root := 10, primeFactors := [2, 3, 5, 373] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 43, 601] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 53, 929] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 67, 1873] }, .lucas { root := 10, primeFactors := [2, 3, 13] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 17, 191] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 41, 593] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 139, 2707] }, .lucas { root := 2, primeFactors := [2, 3, 11, 41] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11, 13, 557] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 83, 2617] }, .lucas { root := 5, primeFactors := [2, 3, 109] }]), by simp⟩

@[expose] def leaf5221_5 : PrimeBank := .leaf [4018159, 4146451, 4630849, 5417851, 9446551, 9531919, 10295269, 10317511, 10608841, 10790137, 10835701, 28638553, 30266503]
theorem leaf5221_5_valid : leaf5221_5.Certified := by
  simp only [leaf5221_5,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 31, 379] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 11, 359] }]), by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 89, 271] }]), by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 5, 19, 1901] }, .lucas { root := 2, primeFactors := [2, 5, 19] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 71, 887] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 11, 1783] }, .lucas { root := 10, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 109, 463] }]), by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 7, 53, 103] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 11, 19, 47] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 79, 271] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 19, 1901] }, .lucas { root := 2, primeFactors := [2, 5, 19] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 223, 5351] }, .lucas { root := 11, primeFactors := [2, 5, 107] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 131, 5501] }, .lucas { root := 2, primeFactors := [2, 5, 11] }]), by simp⟩

@[expose] def pool5221 : PrimeBank := (.branch 42073 (.branch 167 leaf5221_0 (.branch 5419 leaf5221_1 leaf5221_2)) (.branch 350983 leaf5221_3 (.branch 4018159 leaf5221_4 leaf5221_5)))
theorem pool5221_valid : pool5221.Certified := ⟨⟨leaf5221_0_valid,⟨leaf5221_1_valid,leaf5221_2_valid⟩⟩,⟨leaf5221_3_valid,⟨leaf5221_4_valid,leaf5221_5_valid⟩⟩⟩

theorem covered5221 : Range 5221 5245 :=
  scan_sound pool5221 pool5221_valid 5 5221 [23, 3, 5, 0, 3, 0, 0, 3, 0, 13, 3, 7] [[(2,(.split 246187 []))], [(2,(.split 3909799 []))], [(2,(.split 42073 [(1,(.split 31 [(2,(.raise [(331,1)]))]))]))], [(2,(.split 347233 [(1,(.split 173617 []))]))]]
    (by decide) (by decide +kernel)

theorem covered5245 : Range 5245 5269 :=
  scan_sound pool5221 pool5221_valid 5 5245 [5, 3, 29, 59, 3, 5, 7, 3, 0, 19, 3, 23] [[(2,(.split 3343 []))]]
    (by decide) (by decide +kernel)

theorem covered5269 : Range 5269 5293 :=
  scan_sound pool5221 pool5221_valid 5 5269 [11, 3, 0, 5, 3, 0, 0, 3, 5, 17, 3, 11] [[(2,(.split 5851 []))], [(2,(.split 6673 [(1,(.split 71 [(2,(.raise [(47,1)]))]))]))], [(2,(.split 715237 [(1,(.raise [(357619,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered5293 : Range 5293 5317 :=
  scan_sound pool5221 pool5221_valid 5 5293 [67, 3, 0, 7, 3, 0, 5, 3, 0, 47, 3, 5] [[(2,(.split 155047 []))], [(2,(.split 4018159 []))], [(2,(.split 273697 [(1,(.split 136849 []))]))]]
    (by decide) (by decide +kernel)

theorem covered5317 : Range 5317 5341 :=
  scan_sound pool5221 pool5221_valid 5 5317 [13, 3, 17, 0, 3, 7, 73, 3, 0, 5, 3, 19] [[(2,(.split 9446551 []))], [(2,(.split 2188171 []))]]
    (by decide) (by decide +kernel)

theorem covered5341 : Range 5341 5365 :=
  scan_sound pool5221 pool5221_valid 5 5341 [7, 3, 5, 0, 3, 0, 53, 3, 11, 23, 3, 31] [[(2,(.split 9531919 []))], [(2,(.split 28638553 [(1,(.raise [(2045611,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered5365 : Range 5365 5389 :=
  scan_sound pool5221 pool5221_valid 5 5365 [5, 3, 7, 41, 3, 5, 19, 3, 0, 7, 3, 0] [[(2,(.split 61 [(2,(.split 43 [(2,(.raise [(631,1)]))])), (3,(.raise [(43,1), (31,1)]))]))], [(2,(.split 4146451 []))]]
    (by decide) (by decide +kernel)

theorem covered5389 : Range 5389 5413 :=
  scan_sound pool5221 pool5221_valid 5 5389 [17, 3, 0, 5, 3, 0, 11, 3, 5, 0, 3, 7] [[(2,(.split 398491 []))], [(2,(.split 134353 [(1,(.split 31 [(2,(.raise [(331,1)]))]))]))], [(2,(.split 513001 [(1,(.raise [(36643,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered5413 : Range 5413 5437 :=
  scan_sound pool5221 pool5221_valid 6 5413 [0, 3, 0, 0, 3, 11, 5, 3, 61, 0, 3, 5] [[(2,(.split 1395523 []))], [(2,(.split 2257639 []))], [(2,(.split 1009 [(1,(.split 31 [(2,(.split 331 []))])), (2,(.raise [(31,1)]))]))], [(2,(.split 9199 []))]]
    (by decide) (by decide +kernel)

theorem covered5437 : Range 5437 5461 :=
  scan_sound pool5221 pool5221_valid 6 5437 [0, 3, 0, 0, 3, 13, 0, 3, 7, 5, 3, 53] [[(2,(.split 4651 []))], [(2,(.split 127 [(2,(.raise [(5419,1)]))]))], [(2,(.split 108541 [(1,(.split 7753 [(1,(.split 3877 []))]))]))], [(2,(.split 267541 [(1,(.split 12161 [(1,(.raise [(2027,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered5461 : Range 5461 5485 :=
  scan_sound pool5221 pool5221_valid 6 5461 [43, 3, 5, 7, 3, 0, 13, 3, 0, 0, 3, 0] [[(2,(.split 211 [(2,(.split 20269 []))]))], [(2,(.split 1531 []))], [(2,(.split 2647 []))], [(2,(.split 163 [(2,(.raise [(67,1), (19,3)]))]))]]
    (by decide) (by decide +kernel)

theorem covered5485 : Range 5485 5509 :=
  scan_sound pool5221 pool5221_valid 6 5485 [5, 3, 11, 17, 3, 5, 23, 3, 0, 0, 3, 0] [[(2,(.split 30266503 []))], [(2,(.split 165511 []))], [(2,(.split 193201 [(1,(.split 96601 []))]))]]
    (by decide) (by decide +kernel)

theorem covered5509 : Range 5509 5533 :=
  scan_sound pool5221 pool5221_valid 6 5509 [7, 3, 37, 5, 3, 0, 0, 3, 5, 0, 3, 0] [[(2,(.split 17029 [(1,(.split 131 []))]))], [(2,(.split 41143 []))], [(2,(.split 6037 [(1,(.split 3019 []))]))], [(2,(.split 456679 []))]]
    (by decide) (by decide +kernel)

theorem covered5533 : Range 5533 5557 :=
  scan_sound pool5221 pool5221_valid 6 5533 [11, 3, 7, 29, 3, 23, 5, 3, 31, 7, 3, 5] []
    (by decide) (by decide +kernel)

theorem covered5557 : Range 5557 5581 :=
  scan_sound pool5221 pool5221_valid 6 5557 [0, 3, 67, 0, 3, 19, 0, 3, 0, 5, 3, 7] [[(2,(.split 10295269 [(1,(.raise [(1029527,1)]))]))], [(2,(.split 10317511 []))], [(2,(.split 1477111 []))], [(2,(.split 2389531 []))]]
    (by decide) (by decide +kernel)

theorem covered5581 : Range 5581 5605 :=
  scan_sound pool5221 pool5221_valid 6 5581 [0, 3, 5, 37, 3, 0, 7, 3, 29, 11, 3, 13] [[(2,(.split 1123 [(2,(.raise [(127,1)]))]))], [(2,(.split 42307 []))]]
    (by decide) (by decide +kernel)

theorem covered5605 : Range 5605 5629 :=
  scan_sound pool5221 pool5221_valid 6 5605 [5, 3, 71, 31, 3, 5, 41, 3, 7, 0, 3, 17] [[(2,(.split 1505893 [(1,(.raise [(3407,1), (7,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered5629 : Range 5629 5653 :=
  scan_sound pool5221 pool5221_valid 6 5629 [13, 3, 43, 5, 3, 0, 0, 3, 5, 0, 3, 0] [[(2,(.split 43 [(2,(.split 631 []))]))], [(2,(.split 10608841 [(1,(.raise [(167,1), (23,1)]))]))], [(2,(.split 342949 [(1,(.split 19 []))]))], [(2,(.split 350983 []))]]
    (by decide) (by decide +kernel)

theorem covered5653 : Range 5653 5677 :=
  scan_sound pool5221 pool5221_valid 6 5653 [0, 3, 0, 0, 3, 7, 5, 3, 0, 53, 3, 5] [[(2,(.split 217429 [(1,(.split 1279 []))]))], [(2,(.split 477721 [(1,(.raise [(34123,1)]))]))], [(2,(.split 967 [(2,(.raise [(67,1)]))]))], [(2,(.split 39343 []))]]
    (by decide) (by decide +kernel)

theorem covered5677 : Range 5677 5701 :=
  scan_sound pool5221 pool5221_valid 6 5677 [7, 3, 13, 0, 3, 11, 0, 3, 0, 5, 3, 41] [[(2,(.split 28867 []))], [(2,(.split 10790137 [(1,(.raise [(16703,1)]))]))], [(2,(.split 4630849 [(1,(.split 131 []))]))]]
    (by decide) (by decide +kernel)

theorem covered5701 : Range 5701 5725 :=
  scan_sound pool5221 pool5221_valid 6 5701 [0, 3, 5, 13, 3, 0, 29, 3, 0, 7, 3, 59] [[(2,(.split 10835701 [(1,(.raise [(5417851,1)]))]))], [(2,(.split 211 [(2,(.raise [(103,1), (79,1)]))]))], [(2,(.split 12967 []))]]
    (by decide) (by decide +kernel)

theorem covered5725 : Range 5725 5733 :=
  scan_sound pool5221 pool5221_valid 6 5725 [5, 3, 17, 11] []
    (by decide) (by decide +kernel)

theorem segment5221 : Range 5221 5733 := (range_join (range_join (range_join (range_join covered5221 covered5245) (range_join covered5269 (range_join covered5293 covered5317))) (range_join (range_join covered5341 (range_join covered5365 covered5389)) (range_join covered5413 (range_join covered5437 covered5461)))) (range_join (range_join (range_join covered5485 covered5509) (range_join covered5533 (range_join covered5557 covered5581))) (range_join (range_join covered5605 (range_join covered5629 covered5653)) (range_join covered5677 (range_join covered5701 covered5725)))))

theorem through5733 : Range 101 5733 := (range_join through5221 segment5221)

end OddPerfect.HarmonicChain.HarmonicRange101
