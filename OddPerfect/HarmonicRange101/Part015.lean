module

public import OddPerfect.HarmonicRange101.Part014
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicRange101

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf7269_0 : PrimeBank := .leaf [2, 3, 11, 19, 31, 79, 127, 151, 197, 271, 283, 331, 421, 487, 499, 571]
theorem leaf7269_0_valid : leaf7269_0.Certified := by
  simp only [leaf7269_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf7269_1 : PrimeBank := .leaf [643, 997, 1051, 1087, 1483, 1847, 1867, 1951, 2089, 2371, 2551, 2879, 3877, 4051, 4093, 5419]
theorem leaf7269_1_valid : leaf7269_1.Certified := by
  simp only [leaf7269_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 181] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 19] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 71] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 311] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 29] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 79] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 17] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 1439] }, .lucas { root := 7, primeFactors := [2, 719] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 19] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 31] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }]), by simp⟩

@[expose] def leaf7269_2 : PrimeBank := .leaf [5851, 6679, 6967, 7351, 7459, 8599, 11701, 19571, 19699, 24919, 27733, 28549, 28789, 38557, 41983, 48541]
theorem leaf7269_2_valid : leaf7269_2.Certified := by
  simp only [leaf7269_2,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 7, 53] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 43] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 113] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1433] }, .lucas { root := 3, primeFactors := [2, 179] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 13] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 19, 103] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 7, 67] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 4153] }, .lucas { root := 5, primeFactors := [2, 3, 173] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 2311] }, .lucas { root := 3, primeFactors := [2, 3, 5, 7, 11] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 61] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 2399] }, .lucas { root := 11, primeFactors := [2, 11, 109] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 17] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 6997] }, .lucas { root := 5, primeFactors := [2, 3, 11, 53] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 809] }]), by simp⟩

@[expose] def leaf7269_3 : PrimeBank := .leaf [56713, 62047, 72889, 75703, 79549, 112543, 121267, 129169, 139459, 143719, 146141, 153259, 159097, 162091, 175759, 258337]
theorem leaf7269_3_valid : leaf7269_3.Certified := by
  simp only [leaf7269_3,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 139] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 383] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 3037] }, .lucas { root := 2, primeFactors := [2, 3, 11, 23] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 31, 37] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 947] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 18757] }, .lucas { root := 2, primeFactors := [2, 3, 521] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 6737] }, .lucas { root := 3, primeFactors := [2, 421] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 13, 23] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 2113] }, .lucas { root := 5, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 17, 1409] }, .lucas { root := 3, primeFactors := [2, 11] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7307] }, .lucas { root := 2, primeFactors := [2, 13, 281] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 7, 41, 89] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 947] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 1801] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 11, 2663] }, .lucas { root := 5, primeFactors := [2, 11] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 23] }]), by simp⟩

@[expose] def leaf7269_4 : PrimeBank := .leaf [306517, 354259, 368551, 405799, 443227, 569659, 576391, 606049, 708517, 982151, 1006279, 1096957, 1369969, 1461409, 1858081, 2809783]
theorem leaf7269_4_valid : leaf7269_4.Certified := by
  simp only [leaf7269_4,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 41, 89] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19681] }, .lucas { root := 11, primeFactors := [2, 3, 5, 41] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 13] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 47, 1439] }, .lucas { root := 7, primeFactors := [2, 719] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 61, 173] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 263] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 19213] }, .lucas { root := 5, primeFactors := [2, 3, 1601] }, .lucas { root := 3, primeFactors := [2, 5] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 59, 107] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19681] }, .lucas { root := 11, primeFactors := [2, 3, 5, 41] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 13, 1511] }, .lucas { root := 11, primeFactors := [2, 5, 151] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 13, 19, 97] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 1451] }, .lucas { root := 2, primeFactors := [2, 5, 29] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 28541] }, .lucas { root := 2, primeFactors := [2, 5, 1427] }, .lucas { root := 2, primeFactors := [2, 23, 31] }]), by primality (cert := .witnesses [.lucas { root := 21, primeFactors := [2, 3, 13, 1171] }, .lucas { root := 2, primeFactors := [2, 3, 5, 13] }]), by primality (cert := .witnesses [.lucas { root := 38, primeFactors := [2, 3, 5, 7, 79] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 61, 853] }]), by simp⟩

@[expose] def leaf7269_5 : PrimeBank := .leaf [2810503, 2862703, 4629139, 8008951, 18310111, 18637669, 19210291, 19271071, 56964757]
theorem leaf7269_5_valid : leaf7269_5.Certified := by
  simp only [leaf7269_5,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 156139] }, .lucas { root := 7, primeFactors := [2, 3, 53, 491] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 41, 431] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 199, 3877] }, .lucas { root := 2, primeFactors := [2, 3, 17, 19] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 107, 499] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 13, 19, 353] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 89, 277] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11, 23, 2531] }, .lucas { root := 2, primeFactors := [2, 5, 11, 23] }]), by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 7, 13, 181] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 37, 7547] }, .lucas { root := 2, primeFactors := [2, 7, 11] }]), by simp⟩

@[expose] def pool7269 : PrimeBank := (.branch 56713 (.branch 643 leaf7269_0 (.branch 5851 leaf7269_1 leaf7269_2)) (.branch 306517 leaf7269_3 (.branch 2810503 leaf7269_4 leaf7269_5)))
theorem pool7269_valid : pool7269.Certified := ⟨⟨leaf7269_0_valid,⟨leaf7269_1_valid,leaf7269_2_valid⟩⟩,⟨leaf7269_3_valid,⟨leaf7269_4_valid,leaf7269_5_valid⟩⟩⟩

theorem covered7269 : Range 7269 7293 :=
  scan_sound pool7269 pool7269_valid 5 7269 [3, 11, 7, 3, 19, 29, 3, 0, 5, 3, 37, 23] [[(2,(.split 4093 [(1,(.split 997 [(1,(.raise [(499,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered7293 : Range 7293 7317 :=
  scan_sound pool7269 pool7269_valid 5 7293 [3, 5, 0, 3, 7, 67, 3, 0, 0, 3, 71, 5] [[(2,(.split 56713 [(1,(.split 4051 []))]))], [(2,(.split 2810503 []))], [(2,(.split 1369969 [(1,(.raise [(19571,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered7317 : Range 7317 7341 :=
  scan_sound pool7269 pool7269_valid 5 7317 [3, 13, 0, 3, 5, 17, 3, 0, 0, 3, 11, 41] [[(2,(.split 576391 []))], [(2,(.split 1096957 [(1,(.raise [(643,1)]))]))], [(2,(.split 41983 []))]]
    (by decide) (by decide +kernel)

theorem covered7341 : Range 7341 7365 :=
  scan_sound pool7269 pool7269_valid 5 7341 [3, 7, 5, 3, 0, 0, 3, 5, 7, 3, 17, 37] [[(2,(.split 6967 []))], [(2,(.split 1087 [(2,(.raise [(283,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered7365 : Range 7365 7389 :=
  scan_sound pool7269 pool7269_valid 5 7365 [3, 53, 0, 3, 73, 5, 3, 47, 11, 3, 5, 83] [[(2,(.split 175759 []))]]
    (by decide) (by decide +kernel)

theorem covered7389 : Range 7389 7413 :=
  scan_sound pool7269 pool7269_valid 5 7389 [3, 19, 0, 3, 13, 7, 3, 11, 5, 3, 31, 0] [[(2,(.split 8599 []))], [(2,(.split 18310111 []))]]
    (by decide) (by decide +kernel)

theorem covered7413 : Range 7413 7437 :=
  scan_sound pool7269 pool7269_valid 5 7413 [3, 5, 0, 3, 41, 13, 3, 7, 17, 3, 0, 5] [[(2,(.split 19699 []))], [(2,(.split 569659 []))]]
    (by decide) (by decide +kernel)

theorem covered7437 : Range 7437 7461 :=
  scan_sound pool7269 pool7269_valid 6 7437 [3, 43, 7, 3, 5, 11, 3, 0, 29, 3, 0, 0] [[(2,(.split 159097 [(1,(.split 79549 []))]))], [(2,(.split 72889 [(1,(.split 197 [(1,(.split 11 []))]))]))], [(2,(.split 139459 []))]]
    (by decide) (by decide +kernel)

theorem covered7461 : Range 7461 7485 :=
  scan_sound pool7269 pool7269_valid 6 7461 [3, 17, 5, 3, 7, 31, 3, 5, 0, 3, 0, 7] [[(2,(.split 18637669 [(1,(.split 421 []))]))], [(2,(.split 708517 [(1,(.raise [(354259,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered7485 : Range 7485 7509 :=
  scan_sound pool7269 pool7269_valid 6 7485 [3, 0, 0, 3, 59, 5, 3, 0, 13, 3, 5, 0] [[(2,(.split 8008951 []))], [(2,(.split 306517 [(1,(.raise [(153259,1)]))]))], [(2,(.split 7351 []))], [(2,(.split 606049 [(1,(.split 31 [(2,(.raise [(331,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered7509 : Range 7509 7533 :=
  scan_sound pool7269 pool7269_valid 6 7509 [3, 7, 11, 3, 0, 73, 3, 0, 5, 3, 0, 17] [[(2,(.split 28789 [(1,(.raise [(2879,1), (151,1)]))]))], [(2,(.split 27733 [(1,(.split 283 []))]))], [(2,(.split 3877 [(1,(.split 2089 [(1,(.raise [(19,1), (11,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered7533 : Range 7533 7557 :=
  scan_sound pool7269 pool7269_valid 6 7533 [3, 5, 0, 3, 0, 19, 3, 0, 0, 3, 7, 5] [[(2,(.split 1051 [(2,(.raise [(368551,1)]))]))], [(2,(.split 121267 []))], [(2,(.split 56964757 [(1,(.raise [(982151,1)]))]))], [(2,(.split 1461409 [(1,(.split 146141 []))]))]]
    (by decide) (by decide +kernel)

theorem covered7557 : Range 7557 7581 :=
  scan_sound pool7269 pool7269_valid 6 7557 [3, 0, 0, 3, 5, 7, 3, 67, 0, 3, 0, 11] [[(2,(.split 487 [(2,(.raise [(271,1)]))]))], [(2,(.split 443227 []))], [(2,(.split 1006279 []))], [(2,(.split 2371 []))]]
    (by decide) (by decide +kernel)

theorem covered7581 : Range 7581 7605 :=
  scan_sound pool7269 pool7269_valid 6 7581 [3, 0, 5, 3, 0, 0, 3, 5, 71, 3, 11, 0] [[(2,(.split 112543 []))], [(2,(.split 1858081 [(1,(.raise [(1847,1)]))]))], [(2,(.split 19210291 []))], [(2,(.split 19271071 []))]]
    (by decide) (by decide +kernel)

theorem covered7605 : Range 7605 7629 :=
  scan_sound pool7269 pool7269_valid 6 7605 [3, 0, 7, 3, 23, 5, 3, 19, 0, 3, 5, 29] [[(2,(.split 38557 [(1,(.raise [(1483,1), (79,1)]))]))], [(2,(.split 6679 []))]]
    (by decide) (by decide +kernel)

theorem covered7629 : Range 7629 7653 :=
  scan_sound pool7269 pool7269_valid 6 7629 [3, 13, 17, 3, 7, 0, 3, 0, 5, 3, 0, 7] [[(2,(.split 127 [(2,(.raise [(5419,1)]))]))], [(2,(.split 11701 [(1,(.split 5851 []))]))], [(2,(.split 162091 []))]]
    (by decide) (by decide +kernel)

theorem covered7653 : Range 7653 7677 :=
  scan_sound pool7269 pool7269_valid 6 7653 [3, 5, 13, 3, 47, 79, 3, 11, 0, 3, 0, 5] [[(2,(.split 75703 []))], [(2,(.split 62047 []))]]
    (by decide) (by decide +kernel)

theorem covered7677 : Range 7677 7701 :=
  scan_sound pool7269 pool7269_valid 6 7677 [3, 7, 0, 3, 5, 0, 3, 0, 7, 3, 43, 0] [[(2,(.split 2809783 []))], [(2,(.split 7459 []))], [(2,(.split 258337 [(1,(.split 129169 []))]))], [(2,(.split 24919 []))]]
    (by decide) (by decide +kernel)

theorem covered7701 : Range 7701 7725 :=
  scan_sound pool7269 pool7269_valid 6 7701 [3, 0, 5, 3, 13, 11, 3, 5, 0, 3, 7, 0] [[(2,(.split 2551 []))], [(2,(.split 48541 [(1,(.split 1867 []))]))], [(2,(.split 405799 []))]]
    (by decide) (by decide +kernel)

theorem covered7725 : Range 7725 7749 :=
  scan_sound pool7269 pool7269_valid 6 7725 [3, 0, 59, 3, 11, 5, 3, 71, 0, 3, 5, 61] [[(2,(.split 1951 []))], [(2,(.split 143719 []))]]
    (by decide) (by decide +kernel)

theorem covered7749 : Range 7749 7773 :=
  scan_sound pool7269 pool7269_valid 6 7749 [3, 23, 0, 3, 0, 0, 3, 7, 5, 3, 17, 19] [[(2,(.split 2862703 []))], [(2,(.split 4629139 []))], [(2,(.split 28549 [(1,(.split 571 []))]))]]
    (by decide) (by decide +kernel)

theorem covered7773 : Range 7773 7781 :=
  scan_sound pool7269 pool7269_valid 6 7773 [3, 5, 7, 3] []
    (by decide) (by decide +kernel)

theorem segment7269 : Range 7269 7781 := (range_join (range_join (range_join (range_join covered7269 covered7293) (range_join covered7317 (range_join covered7341 covered7365))) (range_join (range_join covered7389 (range_join covered7413 covered7437)) (range_join covered7461 (range_join covered7485 covered7509)))) (range_join (range_join (range_join covered7533 covered7557) (range_join covered7581 (range_join covered7605 covered7629))) (range_join (range_join covered7653 (range_join covered7677 covered7701)) (range_join covered7725 (range_join covered7749 covered7773)))))

theorem through7781 : Range 101 7781 := (range_join through7269 segment7269)

end OddPerfect.HarmonicChain.HarmonicRange101
