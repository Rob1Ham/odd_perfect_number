module

public import OddPerfect.HarmonicRange101.Part015
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicRange101

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf7781_0 : PrimeBank := .leaf [2, 3, 5, 7, 11, 31, 43, 61, 67, 79, 127, 139, 199, 211, 283, 331]
theorem leaf7781_0_valid : leaf7781_0.Certified := by
  simp only [leaf7781_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf7781_1 : PrimeBank := .leaf [367, 379, 409, 563, 607, 787, 827, 947, 991, 1039, 1103, 2791, 3181, 3769, 4231, 4999]
theorem leaf7781_1_valid : leaf7781_1.Certified := by
  simp only [leaf7781_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 173] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 19, 29] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 31] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 53] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 157] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 47] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 17] }]), by simp⟩

@[expose] def leaf7781_2 : PrimeBank := .leaf [5419, 5581, 6271, 6361, 8269, 9463, 9631, 10559, 12619, 18439, 23431, 25237, 26641, 28621, 33637, 53281]
theorem leaf7781_2_valid : leaf7781_2.Certified := by
  simp only [leaf7781_2,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 31] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 11, 19] }]), by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 53] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 53] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 83] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 107] }]), by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 5279] }, .lucas { root := 7, primeFactors := [2, 7, 13, 29] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 701] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 439] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11, 71] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 701] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 37] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 53] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 2803] }, .lucas { root := 2, primeFactors := [2, 3, 467] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 37] }]), by simp⟩

@[expose] def leaf7781_3 : PrimeBank := .leaf [55249, 56431, 57241, 74761, 103681, 127997, 132247, 173539, 230551, 261427, 309937, 369361, 466579, 470359, 475147, 787879]
theorem leaf7781_3_valid : leaf7781_3.Certified := by
  simp only [leaf7781_3,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 1151] }, .lucas { root := 17, primeFactors := [2, 5, 23] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11, 19] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 53] }]), by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 7, 89] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 2909] }, .lucas { root := 2, primeFactors := [2, 727] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 31, 79] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 31, 311] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 29, 53] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17, 233] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 587] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 19] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 23] }]), by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 7, 3733] }, .lucas { root := 2, primeFactors := [2, 3, 311] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 419] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 13, 37] }]), by simp⟩

@[expose] def leaf7781_4 : PrimeBank := .leaf [826717, 1279969, 1645747, 3019873, 3093121, 3256411, 4715467, 8676949, 8743879, 9343951, 10649341, 10809811, 20948419, 21075451, 21298681, 21619621]
theorem leaf7781_4_valid : leaf7781_4.Certified := by
  simp only [leaf7781_4,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 6263] }, .lucas { root := 5, primeFactors := [2, 31, 101] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 67, 199] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 59, 4649] }, .lucas { root := 3, primeFactors := [2, 7, 83] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 83, 379] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 179] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 19, 29, 197] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 43, 373] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 53, 1949] }, .lucas { root := 2, primeFactors := [2, 487] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 13, 43, 79] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 11, 809] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 13, 37, 41] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 61, 179] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 881, 1321] }, .lucas { root := 13, primeFactors := [2, 3, 5, 11] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 11, 53, 241] }]), by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 13, 37, 41] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 61, 179] }]), by simp⟩

@[expose] def leaf7781_5 : PrimeBank := .leaf [22203361, 22301407, 22366891, 22761811, 62149573, 62433703, 65504743, 67757593, 67856407]
theorem leaf7781_5_valid : leaf7781_5.Certified := by
  simp only [leaf7781_5,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 17, 907] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 29, 47, 101] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 13, 2731] }, .lucas { root := 3, primeFactors := [2, 3, 5, 7, 13] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 17, 19, 29] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 73, 7883] }, .lucas { root := 2, primeFactors := [2, 7, 563] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 439, 7901] }, .lucas { root := 2, primeFactors := [2, 5, 79] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 71, 8093] }, .lucas { root := 2, primeFactors := [2, 7, 17] }]), by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 7, 8231] }, .lucas { root := 11, primeFactors := [2, 5, 823] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1373, 8237] }, .lucas { root := 2, primeFactors := [2, 7] }, .lucas { root := 2, primeFactors := [2, 29, 71] }]), by simp⟩

@[expose] def pool7781 : PrimeBank := (.branch 55249 (.branch 367 leaf7781_0 (.branch 5419 leaf7781_1 leaf7781_2)) (.branch 826717 leaf7781_3 (.branch 22203361 leaf7781_4 leaf7781_5)))
theorem pool7781_valid : pool7781.Certified := ⟨⟨leaf7781_0_valid,⟨leaf7781_1_valid,leaf7781_2_valid⟩⟩,⟨leaf7781_3_valid,⟨leaf7781_4_valid,leaf7781_5_valid⟩⟩⟩

theorem covered7781 : Range 7781 7805 :=
  scan_sound pool7781 pool7781_valid 4 7781 [31, 43, 3, 13, 0, 3, 0, 5, 3, 11, 29, 3] [[(2,(.split 470359 []))], [(2,(.split 8676949 [(1,(.raise [(173539,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered7805 : Range 7805 7829 :=
  scan_sound pool7781 pool7781_valid 5 7805 [5, 37, 3, 73, 13, 3, 0, 7, 3, 0, 5, 3] [[(2,(.split 53281 [(1,(.split 26641 []))]))], [(2,(.split 8743879 []))]]
    (by decide) (by decide +kernel)

theorem covered7829 : Range 7829 7853 :=
  scan_sound pool7781 pool7781_valid 5 7829 [0, 41, 3, 5, 17, 3, 0, 11, 3, 7, 47, 3] [[(2,(.split 4715467 []))], [(2,(.split 4231 []))]]
    (by decide) (by decide +kernel)

theorem covered7853 : Range 7853 7877 :=
  scan_sound pool7781 pool7781_valid 5 7853 [0, 5, 3, 29, 7, 3, 5, 0, 3, 17, 0, 3] [[(2,(.split 309937 [(1,(.raise [(4999,1)]))]))], [(2,(.split 103681 [(1,(.raise [(1103,1), (199,1)]))]))], [(2,(.split 57241 [(1,(.split 28621 [(1,(.raise [(11,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered7877 : Range 7877 7901 :=
  scan_sound pool7781 pool7781_valid 5 7877 [0, 0, 3, 0, 5, 3, 7, 13, 3, 5, 53, 3] [[(2,(.split 466579 []))], [(2,(.split 283 [(2,(.raise [(367,1)]))]))], [(2,(.split 62149573 [(1,(.raise [(991,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered7901 : Range 7901 7925 :=
  scan_sound pool7781 pool7781_valid 5 7901 [0, 7, 3, 0, 11, 3, 41, 5, 3, 0, 89, 3] [[(2,(.component 62433703 2 [(62433703,1)]))], [(2,(.split 379 [(2,(.raise [(787,1)]))]))], [(2,(.split 1279969 [(1,(.split 127997 []))]))]]
    (by decide) (by decide +kernel)

theorem covered7925 : Range 7925 7949 :=
  scan_sound pool7781 pool7781_valid 5 7925 [5, 0, 3, 7, 0, 3, 0, 17, 3, 13, 5, 3] [[(2,(.split 20948419 []))], [(2,(.split 230551 []))], [(2,(.split 261427 []))]]
    (by decide) (by decide +kernel)

theorem covered7949 : Range 7949 7973 :=
  scan_sound pool7781 pool7781_valid 5 7949 [0, 0, 3, 5, 73, 3, 19, 0, 3, 31, 13, 3] [[(2,(.split 475147 []))], [(2,(.split 21075451 []))], [(2,(.split 3019873 [(1,(.raise [(10559,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered7973 : Range 7973 7997 :=
  scan_sound pool7781 pool7781_valid 5 7973 [7, 5, 3, 79, 23, 3, 5, 7, 3, 61, 0, 3] [[(2,(.split 21298681 [(1,(.split 10649341 []))]))]]
    (by decide) (by decide +kernel)

theorem covered7997 : Range 7997 8021 :=
  scan_sound pool7781 pool7781_valid 5 7997 [11, 19, 3, 53, 5, 3, 0, 0, 3, 5, 0, 3] [[(2,(.split 9631 []))], [(2,(.split 1645747 []))], [(2,(.split 33637 [(1,(.split 139 []))]))]]
    (by decide) (by decide +kernel)

theorem covered8021 : Range 8021 8045 :=
  scan_sound pool7781 pool7781_valid 5 8021 [13, 71, 3, 23, 7, 3, 29, 5, 3, 0, 11, 3] [[(2,(.split 5581 [(1,(.split 2791 []))]))]]
    (by decide) (by decide +kernel)

theorem covered8045 : Range 8045 8069 :=
  scan_sound pool7781 pool7781_valid 5 8045 [5, 13, 3, 83, 0, 3, 7, 0, 3, 11, 5, 3] [[(2,(.split 21619621 [(1,(.raise [(10809811,1)]))]))], [(2,(.split 3093121 [(1,(.raise [(563,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered8069 : Range 8069 8093 :=
  scan_sound pool7781 pool7781_valid 5 8069 [0, 7, 3, 5, 41, 3, 0, 59, 3, 0, 0, 3] [[(2,(.split 74761 [(1,(.split 67 []))]))], [(2,(.split 826717 [(1,(.raise [(79,1), (43,1)]))]))], [(2,(.split 9343951 []))], [(2,(.split 18439 []))]]
    (by decide) (by decide +kernel)

theorem covered8093 : Range 8093 8117 :=
  scan_sound pool7781 pool7781_valid 5 8093 [0, 5, 3, 7, 0, 3, 5, 11, 3, 0, 7, 3] [[(2,(.component 65504743 2 [(65504743,1)]))], [(2,(.split 607 [(2,(.raise [(9463,1)]))]))], [(2,(.split 8269 [(1,(.split 827 []))]))]]
    (by decide) (by decide +kernel)

theorem covered8117 : Range 8117 8141 :=
  scan_sound pool7781 pool7781_valid 5 8117 [0, 23, 3, 0, 5, 3, 11, 47, 3, 5, 79, 3] [[(2,(.split 25237 [(1,(.raise [(12619,1), (7,1)]))]))], [(2,(.split 132247 []))]]
    (by decide) (by decide +kernel)

theorem covered8141 : Range 8141 8165 :=
  scan_sound pool7781 pool7781_valid 5 8141 [7, 17, 3, 0, 29, 3, 31, 5, 3, 41, 0, 3] [[(2,(.split 127 [(2,(.raise [(5419,1)]))]))], [(2,(.split 22203361 [(1,(.raise [(947,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered8165 : Range 8165 8189 :=
  scan_sound pool7781 pool7781_valid 5 8165 [5, 0, 3, 0, 11, 3, 13, 0, 3, 7, 5, 3] [[(2,(.split 23431 []))], [(2,(.split 1039 []))], [(2,(.split 22301407 []))]]
    (by decide) (by decide +kernel)

theorem covered8189 : Range 8189 8213 :=
  scan_sound pool7781 pool7781_valid 5 8189 [19, 0, 3, 5, 7, 3, 59, 13, 3, 29, 0, 3] [[(2,(.split 22366891 []))], [(2,(.split 31 [(2,(.split 331 []))]))]]
    (by decide) (by decide +kernel)

theorem covered8213 : Range 8213 8237 :=
  scan_sound pool7781 pool7781_valid 6 8213 [43, 5, 3, 0, 0, 3, 5, 19, 3, 0, 0, 3] [[(2,(.split 6361 [(1,(.split 3181 [(1,(.split 43 []))]))]))], [(2,(.split 369361 [(1,(.split 3769 [(1,(.split 61 []))]))]))], [(2,(.split 67757593 [(1,(.raise [(787879,1)]))]))], [(2,(.split 55249 [(1,(.split 409 [(1,(.split 5 []))]))]))]]
    (by decide) (by decide +kernel)

theorem covered8237 : Range 8237 8261 :=
  scan_sound pool7781 pool7781_valid 6 8237 [0, 7, 3, 0, 5, 3, 73, 37, 3, 5, 23, 3] [[(2,(.component 67856407 2 [(67856407,1)]))], [(2,(.split 331 [(2,(.raise [(211,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered8261 : Range 8261 8285 :=
  scan_sound pool7781 pool7781_valid 6 8261 [11, 0, 3, 7, 0, 3, 0, 5, 3, 17, 7, 3] [[(2,(.split 22761811 []))], [(2,(.split 3256411 []))], [(2,(.split 56431 []))]]
    (by decide) (by decide +kernel)

theorem covered8285 : Range 8285 8293 :=
  scan_sound pool7781 pool7781_valid 6 8285 [5, 0, 3, 0] [[(2,(.split 607 [(2,(.raise [(9463,1)]))]))], [(2,(.split 6271 []))]]
    (by decide) (by decide +kernel)

theorem segment7781 : Range 7781 8293 := (range_join (range_join (range_join (range_join covered7781 covered7805) (range_join covered7829 (range_join covered7853 covered7877))) (range_join (range_join covered7901 (range_join covered7925 covered7949)) (range_join covered7973 (range_join covered7997 covered8021)))) (range_join (range_join (range_join covered8045 covered8069) (range_join covered8093 (range_join covered8117 covered8141))) (range_join (range_join covered8165 (range_join covered8189 covered8213)) (range_join covered8237 (range_join covered8261 covered8285)))))

theorem through8293 : Range 101 8293 := (range_join through7781 segment7781)

end OddPerfect.HarmonicChain.HarmonicRange101
