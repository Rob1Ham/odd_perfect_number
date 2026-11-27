module

public import OddPerfect.HarmonicRange101.Part016
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicRange101

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf8293_0 : PrimeBank := .leaf [2, 3, 7, 31, 43, 67, 79, 83, 103, 107, 127, 139, 151, 163, 199, 223]
theorem leaf8293_0_valid : leaf8293_0.Certified := by
  simp only [leaf8293_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf8293_1 : PrimeBank := .leaf [307, 379, 613, 787, 859, 1163, 1531, 1723, 3319, 3889, 4423, 5003, 5443, 6247, 8971, 12659]
theorem leaf8293_1_valid : leaf8293_1.Certified := by
  simp only [leaf8293_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 83] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 41] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 79] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 67] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 41, 61] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 907] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 347] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 23] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 6329] }, .lucas { root := 3, primeFactors := [2, 7, 113] }]), by simp⟩

@[expose] def leaf8293_2 : PrimeBank := .leaf [12919, 17923, 19181, 24877, 40039, 53881, 55117, 67129, 92671, 95317, 98047, 147289, 190633, 241177, 246247, 263611]
theorem leaf8293_2_valid : leaf8293_2.Certified := by
  simp only [leaf8293_2,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 2153] }, .lucas { root := 3, primeFactors := [2, 269] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29, 103] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 137] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 691] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 6673] }, .lucas { root := 5, primeFactors := [2, 3, 139] }]), by primality (cert := .witnesses [.lucas { root := 31, primeFactors := [2, 3, 5, 449] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1531] }, .lucas { root := 2, primeFactors := [2, 3, 5, 17] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 2797] }, .lucas { root := 2, primeFactors := [2, 3, 233] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 3089] }, .lucas { root := 3, primeFactors := [2, 193] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 47] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 419] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 17, 19] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 47] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 13, 773] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11, 13, 41] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 29, 101] }]), by simp⟩

@[expose] def leaf8293_3 : PrimeBank := .leaf [278497, 325021, 388471, 469939, 707797, 714781, 762031, 791851, 799621, 800977, 1250749, 1297393, 1815217, 2306027, 2544797, 3322903]
theorem leaf8293_3_valid : leaf8293_3.Certified := by
  simp only [leaf8293_3,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 967] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 5417] }, .lucas { root := 3, primeFactors := [2, 677] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 23, 563] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 67, 167] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 19661] }, .lucas { root := 2, primeFactors := [2, 5, 983] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 19] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 8467] }, .lucas { root := 2, primeFactors := [2, 3, 17, 83] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 5279] }, .lucas { root := 7, primeFactors := [2, 7, 13, 29] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 13327] }, .lucas { root := 3, primeFactors := [2, 3, 2221] }, .lucas { root := 2, primeFactors := [2, 3, 5, 37] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 37, 41] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 37, 313] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 151, 179] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 13, 2909] }, .lucas { root := 2, primeFactors := [2, 727] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 23, 50131] }, .lucas { root := 2, primeFactors := [2, 3, 5, 557] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 101, 6299] }, .lucas { root := 2, primeFactors := [2, 47, 67] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 23, 199] }]), by simp⟩

@[expose] def leaf8293_4 : PrimeBank := .leaf [3414217, 3585667, 3595591, 3630433, 3655423, 3690553, 3755803, 5213671, 5701807, 5813611, 10006933, 22927381, 23060269, 24239419, 25273519, 25447969]
theorem leaf8293_4_valid : leaf8293_4.Certified := by
  simp only [leaf8293_4,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 13, 31, 353] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 59, 1447] }, .lucas { root := 3, primeFactors := [2, 3, 241] }]), by primality (cert := .witnesses [.lucas { root := 29, primeFactors := [2, 3, 5, 23, 193] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 2909] }, .lucas { root := 2, primeFactors := [2, 727] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 139, 487] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 367, 419] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 661, 947] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 11, 37, 61] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 29, 331] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 79, 223] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 23, 2789] }, .lucas { root := 2, primeFactors := [2, 17, 41] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 79, 691] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 11, 47, 59] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 7, 29, 2843] }, .lucas { root := 2, primeFactors := [2, 7, 29] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 1451, 2903] }, .lucas { root := 2, primeFactors := [2, 5, 29] }, .lucas { root := 5, primeFactors := [2, 1451] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 13, 971] }]), by simp⟩

@[expose] def leaf8293_5 : PrimeBank := .leaf [35175079, 70350157, 72275503, 72991393, 74433757, 75160231, 75368443, 76413823, 76623763]
theorem leaf8293_5_valid : leaf8293_5.Certified := by
  simp only [leaf8293_5,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 233, 8387] }, .lucas { root := 2, primeFactors := [2, 7, 599] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 233, 8387] }, .lucas { root := 2, primeFactors := [2, 7, 599] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 109, 8501] }, .lucas { root := 7, primeFactors := [2, 5, 17] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 89, 8543] }, .lucas { root := 5, primeFactors := [2, 4271] }, .lucas { root := 7, primeFactors := [2, 5, 7, 61] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 719, 8627] }, .lucas { root := 2, primeFactors := [2, 19, 227] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 17, 8669] }, .lucas { root := 2, primeFactors := [2, 11, 197] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1447, 8681] }, .lucas { root := 3, primeFactors := [2, 3, 241] }, .lucas { root := 15, primeFactors := [2, 5, 7, 31] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 31, 47, 8741] }, .lucas { root := 2, primeFactors := [2, 5, 19, 23] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1459, 8753] }, .lucas { root := 3, primeFactors := [2, 3] }, .lucas { root := 3, primeFactors := [2, 547] }]), by simp⟩

@[expose] def pool8293 : PrimeBank := (.branch 278497 (.branch 307 leaf8293_0 (.branch 12919 leaf8293_1 leaf8293_2)) (.branch 3414217 leaf8293_3 (.branch 35175079 leaf8293_4 leaf8293_5)))
theorem pool8293_valid : pool8293.Certified := ⟨⟨leaf8293_0_valid,⟨leaf8293_1_valid,leaf8293_2_valid⟩⟩,⟨leaf8293_3_valid,⟨leaf8293_4_valid,leaf8293_5_valid⟩⟩⟩

theorem covered8293 : Range 8293 8317 :=
  scan_sound pool8293 pool8293_valid 4 8293 [0, 3, 0, 43, 3, 19, 5, 3, 7, 0, 3, 5] [[(2,(.split 22927381 [(1,(.raise [(1163,1)]))]))], [(2,(.split 5443 []))], [(2,(.split 469939 []))]]
    (by decide) (by decide +kernel)

theorem covered8317 : Range 8317 8341 :=
  scan_sound pool8293 pool8293_valid 4 8317 [0, 3, 53, 7, 3, 11, 0, 3, 13, 5, 3, 31] [[(2,(.split 23060269 [(1,(.raise [(2306027,1)]))]))], [(2,(.split 859 [(2,(.raise [(246247,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered8341 : Range 8341 8365 :=
  scan_sound pool8293 pool8293_valid 4 8341 [19, 3, 5, 17, 3, 7, 0, 3, 61, 13, 3, 0] [[(2,(.split 3322903 []))], [(2,(.split 40039 []))]]
    (by decide) (by decide +kernel)

theorem covered8365 : Range 8365 8389 :=
  scan_sound pool8293 pool8293_valid 5 8365 [5, 3, 0, 11, 3, 5, 0, 3, 17, 83, 3, 0] [[(2,(.split 10006933 [(1,(.split 714781 []))]))], [(2,(.split 241177 [(1,(.split 107 []))]))], [(2,(.split 70350157 [(1,(.raise [(35175079,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered8389 : Range 8389 8413 :=
  scan_sound pool8293 pool8293_valid 5 8389 [0, 3, 7, 5, 3, 37, 31, 3, 5, 7, 3, 13] [[(2,(.split 379 [(2,(.raise [(787,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered8413 : Range 8413 8437 :=
  scan_sound pool8293 pool8293_valid 5 8413 [47, 3, 19, 0, 3, 0, 5, 3, 0, 0, 3, 5] [[(2,(.split 98047 []))], [(2,(.split 67129 [(1,(.split 151 []))]))], [(2,(.split 3319 []))], [(2,(.split 388471 []))]]
    (by decide) (by decide +kernel)

theorem covered8437 : Range 8437 8461 :=
  scan_sound pool8293 pool8293_valid 5 8437 [11, 3, 23, 0, 3, 0, 7, 3, 79, 5, 3, 11] [[(2,(.split 1250749 [(1,(.raise [(5003,1)]))]))], [(2,(.split 3755803 []))]]
    (by decide) (by decide +kernel)

theorem covered8461 : Range 8461 8485 :=
  scan_sound pool8293 pool8293_valid 5 8461 [0, 3, 5, 0, 3, 43, 37, 3, 7, 61, 3, 17] [[(2,(.split 55117 [(1,(.raise [(127,1), (31,1), (7,1)]))]))], [(2,(.split 3414217 [(1,(.split 19181 []))]))]]
    (by decide) (by decide +kernel)

theorem covered8485 : Range 8485 8509 :=
  scan_sound pool8293 pool8293_valid 5 8485 [5, 3, 13, 7, 3, 5, 29, 3, 0, 11, 3, 47] [[(2,(.component 72275503 2 [(72275503,1)]))]]
    (by decide) (by decide +kernel)

theorem covered8509 : Range 8509 8533 :=
  scan_sound pool8293 pool8293_valid 5 8509 [67, 3, 0, 5, 3, 7, 0, 3, 5, 0, 3, 19] [[(2,(.split 325021 [(1,(.raise [(223,1), (163,1)]))]))], [(2,(.split 24877 [(1,(.split 139 []))]))], [(2,(.split 24239419 []))]]
    (by decide) (by decide +kernel)

theorem covered8533 : Range 8533 8557 :=
  scan_sound pool8293 pool8293_valid 5 8533 [7, 3, 0, 0, 3, 0, 5, 3, 83, 17, 3, 5] [[(2,(.split 800977 [(1,(.raise [(12919,1)]))]))], [(2,(.split 1531 []))], [(2,(.split 72991393 [(1,(.raise [(5213671,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered8557 : Range 8557 8581 :=
  scan_sound pool8293 pool8293_valid 5 8557 [43, 3, 7, 0, 3, 13, 11, 3, 0, 5, 3, 23] [[(2,(.split 6247 []))], [(2,(.split 1723 []))]]
    (by decide) (by decide +kernel)

theorem covered8581 : Range 8581 8605 :=
  scan_sound pool8293 pool8293_valid 5 8581 [0, 3, 5, 31, 3, 11, 13, 3, 0, 0, 3, 7] [[(2,(.split 791851 []))], [(2,(.split 762031 []))], [(2,(.split 1297393 [(1,(.raise [(92671,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered8605 : Range 8605 8629 :=
  scan_sound pool8293 pool8293_valid 5 8605 [5, 3, 0, 79, 3, 5, 7, 3, 37, 0, 3, 0] [[(2,(.split 5701807 []))], [(2,(.split 799621 [(1,(.raise [(83,1), (31,1)]))]))], [(2,(.split 74433757 [(1,(.raise [(7,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered8629 : Range 8629 8653 :=
  scan_sound pool8293 pool8293_valid 5 8629 [0, 3, 89, 5, 3, 53, 0, 3, 5, 0, 3, 41] [[(2,(.split 8971 []))], [(2,(.split 147289 [(1,(.split 103 []))]))], [(2,(.split 613 [(1,(.split 307 [])), (2,(.raise [(17923,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered8653 : Range 8653 8677 :=
  scan_sound pool8293 pool8293_valid 5 8653 [17, 3, 11, 7, 3, 0, 5, 3, 0, 13, 3, 5] [[(2,(.split 53881 [(1,(.split 199 []))]))], [(2,(.component 75160231 2 [(75160231,1)]))]]
    (by decide) (by decide +kernel)

theorem covered8677 : Range 8677 8701 :=
  scan_sound pool8293 pool8293_valid 5 8677 [0, 3, 0, 19, 3, 7, 0, 3, 0, 5, 3, 0] [[(2,(.split 3585667 []))], [(2,(.component 75368443 2 [(75368443,1)]))], [(2,(.split 3595591 []))], [(2,(.split 5813611 []))], [(2,(.split 190633 [(1,(.split 95317 []))]))]]
    (by decide) (by decide +kernel)

theorem covered8701 : Range 8701 8725 :=
  scan_sound pool8293 pool8293_valid 5 8701 [7, 3, 5, 0, 3, 31, 0, 3, 23, 0, 3, 11] [[(2,(.split 25273519 []))], [(2,(.split 79 [(2,(.split 43 []))]))], [(2,(.split 278497 [(1,(.raise [(12659,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered8725 : Range 8725 8749 :=
  scan_sound pool8293 pool8293_valid 5 8725 [5, 3, 7, 0, 3, 5, 0, 3, 0, 7, 3, 0] [[(2,(.split 3630433 [(1,(.split 1815217 []))]))], [(2,(.split 25447969 [(1,(.split 2544797 []))]))], [(2,(.component 76413823 2 [(76413823,1)]))], [(2,(.split 67 [(2,(.split 7 []))]))]]
    (by decide) (by decide +kernel)

theorem covered8749 : Range 8749 8773 :=
  scan_sound pool8293 pool8293_valid 5 8749 [13, 3, 0, 5, 3, 19, 0, 3, 5, 11, 3, 7] [[(2,(.component 76623763 2 [(76623763,1)]))], [(2,(.split 3655423 []))]]
    (by decide) (by decide +kernel)

theorem covered8773 : Range 8773 8797 :=
  scan_sound pool8293 pool8293_valid 5 8773 [31, 3, 67, 0, 3, 0, 5, 3, 11, 59, 3, 5] [[(2,(.split 4423 []))], [(2,(.split 707797 [(1,(.split 3889 []))]))]]
    (by decide) (by decide +kernel)

theorem covered8797 : Range 8797 8805 :=
  scan_sound pool8293 pool8293_valid 5 8797 [19, 3, 13, 0] [[(2,(.split 3690553 [(1,(.raise [(263611,1)]))]))]]
    (by decide) (by decide +kernel)

theorem segment8293 : Range 8293 8805 := (range_join (range_join (range_join (range_join covered8293 covered8317) (range_join covered8341 (range_join covered8365 covered8389))) (range_join (range_join covered8413 (range_join covered8437 covered8461)) (range_join covered8485 (range_join covered8509 covered8533)))) (range_join (range_join (range_join covered8557 covered8581) (range_join covered8605 (range_join covered8629 covered8653))) (range_join (range_join covered8677 (range_join covered8701 covered8725)) (range_join covered8749 (range_join covered8773 covered8797)))))

theorem through8805 : Range 101 8805 := (range_join through8293 segment8293)

end OddPerfect.HarmonicChain.HarmonicRange101
