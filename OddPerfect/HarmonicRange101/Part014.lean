module

public import OddPerfect.HarmonicRange101.Part013
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicRange101

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf6757_0 : PrimeBank := .leaf [2, 3, 5, 7, 23, 31, 67, 103, 127, 151, 163, 211, 229, 271, 331, 349]
theorem leaf6757_0_valid : leaf6757_0.Certified := by
  simp only [leaf6757_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf6757_1 : PrimeBank := .leaf [433, 439, 547, 571, 619, 877, 907, 967, 991, 1237, 1279, 1373, 1567, 1699, 1753, 1879]
theorem leaf6757_1_valid : leaf6757_1.Certified := by
  simp only [leaf6757_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 103] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 71] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 29] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 283] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 73] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 313] }]), by simp⟩

@[expose] def leaf6757_2 : PrimeBank := .leaf [1999, 2447, 2677, 2707, 3083, 3499, 3643, 3691, 5059, 5683, 5827, 5857, 6229, 10903, 13729, 17327]
theorem leaf6757_2_valid : leaf6757_2.Certified := by
  simp only [leaf6757_2,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 37] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 1223] }, .lucas { root := 5, primeFactors := [2, 13, 47] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 223] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 41] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 23, 67] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 53] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 607] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 41] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 281] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 947] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 971] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 61] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 173] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 23, 79] }]), by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 11, 13] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 8663] }, .lucas { root := 5, primeFactors := [2, 61, 71] }]), by simp⟩

@[expose] def leaf6757_3 : PrimeBank := .leaf [17749, 19249, 19543, 21649, 22051, 22543, 34303, 37897, 42283, 44101, 65581, 83431, 95143, 112207, 161599, 178813]
theorem leaf6757_3_valid : leaf6757_3.Certified := by
  simp only [leaf6757_3,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 29] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 401] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 3257] }, .lucas { root := 3, primeFactors := [2, 11, 37] }]), by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 11, 41] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 17] }]), by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5717] }, .lucas { root := 2, primeFactors := [2, 1429] }, .lucas { root := 6, primeFactors := [2, 3, 7, 17] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1579] }, .lucas { root := 3, primeFactors := [2, 3, 263] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 1093] }, .lucas { root := 5, primeFactors := [2, 3, 7, 13] }]), by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 103] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 101, 157] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 18701] }, .lucas { root := 2, primeFactors := [2, 5, 11, 17] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 23, 1171] }, .lucas { root := 2, primeFactors := [2, 3, 5, 13] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 4967] }, .lucas { root := 5, primeFactors := [2, 13, 191] }]), by simp⟩

@[expose] def leaf6757_4 : PrimeBank := .leaf [376837, 414313, 468619, 481531, 519307, 671557, 803623, 1126387, 1343113, 2256313, 2473717, 3610357, 3907789, 6741433, 6967039, 7220713]
theorem leaf6757_4_valid : leaf6757_4.Certified := by
  simp only [leaf6757_4,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 31, 1013] }]), by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 61, 283] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 83, 941] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 2293] }, .lucas { root := 2, primeFactors := [2, 3, 191] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 41, 2111] }, .lucas { root := 7, primeFactors := [2, 5, 211] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 191, 293] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 151, 887] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 409] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 191, 293] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 41, 2293] }, .lucas { root := 2, primeFactors := [2, 3, 191] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 601] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 23, 103, 127] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 137, 2377] }, .lucas { root := 5, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 109, 859] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 179, 499] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 23, 103, 127] }]), by simp⟩

@[expose] def leaf6757_5 : PrimeBank := .leaf [7503751, 16293691, 17489431, 45717883, 46124473, 46696723, 47851807, 49189183, 52265671, 52613263]
theorem leaf6757_5_valid : leaf6757_5.Certified := by
  simp only [leaf6757_5,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 23, 29] }]), by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 7, 37, 233] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 17, 23, 71] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 23, 6761] }, .lucas { root := 3, primeFactors := [2, 5, 13] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 283, 6791] }, .lucas { root := 7, primeFactors := [2, 5, 7, 97] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 67, 6833] }, .lucas { root := 3, primeFactors := [2, 7, 61] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1153, 6917] }, .lucas { root := 5, primeFactors := [2, 3] }, .lucas { root := 2, primeFactors := [2, 7, 13, 19] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 167, 7013] }, .lucas { root := 2, primeFactors := [2, 1753] }, .lucas { root := 7, primeFactors := [2, 3, 73] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 241, 7229] }, .lucas { root := 2, primeFactors := [2, 13, 139] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 31, 7253] }, .lucas { root := 2, primeFactors := [2, 7, 37] }]), by simp⟩

@[expose] def pool6757 : PrimeBank := (.branch 17749 (.branch 433 leaf6757_0 (.branch 1999 leaf6757_1 leaf6757_2)) (.branch 376837 leaf6757_3 (.branch 7503751 leaf6757_4 leaf6757_5)))
theorem pool6757_valid : pool6757.Certified := ⟨⟨leaf6757_0_valid,⟨leaf6757_1_valid,leaf6757_2_valid⟩⟩,⟨leaf6757_3_valid,⟨leaf6757_4_valid,leaf6757_5_valid⟩⟩⟩

theorem covered6757 : Range 6757 6781 :=
  scan_sound pool6757 pool6757_valid 5 6757 [29, 3, 0, 0, 3, 67, 7, 3, 13, 5, 3, 0] [[(2,(.component 45717883 2 [(45717883,1)]))], [(2,(.split 31 [(2,(.split 331 []))]))], [(2,(.split 42283 []))]]
    (by decide) (by decide +kernel)

theorem covered6781 : Range 6781 6805 :=
  scan_sound pool6757 pool6757_valid 5 6781 [0, 3, 5, 11, 3, 0, 0, 3, 7, 13, 3, 0] [[(2,(.split 414313 [(1,(.raise [(10903,1)]))]))], [(2,(.split 46124473 [(1,(.raise [(17327,1)]))]))], [(2,(.split 5683 []))], [(2,(.split 1567 []))]]
    (by decide) (by decide +kernel)

theorem covered6805 : Range 6805 6829 :=
  scan_sound pool6757 pool6757_valid 5 6805 [5, 3, 11, 7, 3, 5, 17, 3, 19, 0, 3, 0] [[(2,(.split 991 [(2,(.raise [(7,1)]))]))], [(2,(.split 44101 [(1,(.raise [(22051,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered6829 : Range 6829 6853 :=
  scan_sound pool6757 pool6757_valid 6 6829 [0, 3, 0, 5, 3, 7, 0, 3, 5, 41, 3, 13] [[(2,(.split 1753 [(1,(.split 877 [(1,(.split 439 []))]))]))], [(2,(.component 46696723 2 [(46696723,1)]))], [(2,(.split 3499 []))]]
    (by decide) (by decide +kernel)

theorem covered6853 : Range 6853 6877 :=
  scan_sound pool6757 pool6757_valid 6 6853 [7, 3, 0, 19, 3, 0, 5, 3, 0, 0, 3, 5] [[(2,(.split 19249 [(1,(.split 349 [(1,(.split 5 [(5,(.raise [(31,1)]))]))]))]))], [(2,(.split 3643 []))], [(2,(.split 6741433 [(1,(.raise [(481531,1)]))]))], [(2,(.split 907 [(2,(.raise [(67,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered6877 : Range 6877 6901 :=
  scan_sound pool6757 pool6757_valid 6 6877 [13, 3, 7, 0, 3, 71, 83, 3, 61, 5, 3, 0] [[(2,(.split 2256313 [(1,(.raise [(5059,1)]))]))], [(2,(.split 1279 []))]]
    (by decide) (by decide +kernel)

theorem covered6901 : Range 6901 6925 :=
  scan_sound pool6757 pool6757_valid 6 6901 [67, 3, 5, 0, 3, 0, 31, 3, 0, 11, 3, 7] [[(2,(.split 3691 []))], [(2,(.split 967 [(2,(.raise [(67,1)]))]))], [(2,(.component 47851807 2 [(47851807,1)]))]]
    (by decide) (by decide +kernel)

theorem covered6925 : Range 6925 6949 :=
  scan_sound pool6757 pool6757_valid 6 6925 [5, 3, 13, 29, 3, 5, 7, 3, 11, 53, 3, 0] [[(2,(.split 468619 []))]]
    (by decide) (by decide +kernel)

theorem covered6949 : Range 6949 6973 :=
  scan_sound pool6757 pool6757_valid 6 6949 [0, 3, 17, 5, 3, 0, 0, 3, 5, 0, 3, 0] [[(2,(.split 519307 []))], [(2,(.split 1126387 []))], [(2,(.split 571 [(2,(.raise [(151,1)]))]))], [(2,(.split 37897 [(1,(.split 2707 []))]))], [(2,(.split 5059 []))]]
    (by decide) (by decide +kernel)

theorem covered6973 : Range 6973 6997 :=
  scan_sound pool6757 pool6757_valid 6 6973 [19, 3, 0, 7, 3, 0, 5, 3, 29, 0, 3, 5] [[(2,(.split 211 [(2,(.split 17749 []))]))], [(2,(.split 6967039 []))], [(2,(.split 16293691 []))]]
    (by decide) (by decide +kernel)

theorem covered6997 : Range 6997 7021 :=
  scan_sound pool6757 pool6757_valid 6 6997 [0, 3, 0, 47, 3, 7, 43, 3, 0, 5, 3, 0] [[(2,(.split 67 [(2,(.split 2677 [(1,(.raise [(103,1)]))]))]))], [(2,(.split 803623 []))], [(2,(.component 49189183 2 [(49189183,1)]))], [(2,(.split 13729 [(1,(.split 1373 [(1,(.split 229 [(1,(.raise [(23,1)]))]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered7021 : Range 7021 7045 :=
  scan_sound pool6757 pool6757_valid 6 7021 [7, 3, 5, 0, 3, 79, 13, 3, 31, 0, 3, 0] [[(2,(.split 1879 []))], [(2,(.split 21649 [(1,(.split 433 [(1,(.split 31 []))]))]))], [(2,(.split 161599 []))]]
    (by decide) (by decide +kernel)

theorem covered7045 : Range 7045 7069 :=
  scan_sound pool6757 pool6757_valid 6 7045 [5, 3, 7, 11, 3, 5, 0, 3, 23, 7, 3, 37] [[(2,(.split 83431 []))]]
    (by decide) (by decide +kernel)

theorem covered7069 : Range 7069 7093 :=
  scan_sound pool6757 pool6757_valid 6 7069 [0, 3, 11, 5, 3, 0, 73, 3, 5, 19, 3, 7] [[(2,(.split 22543 []))], [(2,(.split 376837 [(1,(.raise [(2447,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered7093 : Range 7093 7117 :=
  scan_sound pool6757 pool6757_valid 6 7093 [41, 3, 47, 31, 3, 0, 5, 3, 0, 13, 3, 5] [[(2,(.split 34303 []))], [(2,(.split 7220713 [(1,(.split 3610357 []))]))]]
    (by decide) (by decide +kernel)

theorem covered7117 : Range 7117 7141 :=
  scan_sound pool6757 pool6757_valid 6 7117 [11, 3, 0, 17, 3, 0, 0, 3, 7, 5, 3, 11] [[(2,(.split 5857 [(1,(.split 1237 [(1,(.raise [(619,1)]))]))]))], [(2,(.split 3907789 [(1,(.split 127 []))]))], [(2,(.split 112207 []))]]
    (by decide) (by decide +kernel)

theorem covered7141 : Range 7141 7165 :=
  scan_sound pool6757 pool6757_valid 6 7141 [37, 3, 5, 7, 3, 0, 23, 3, 17, 0, 3, 13] [[(2,(.split 547 [(2,(.raise [(163,1)]))]))], [(2,(.split 211 [(2,(.split 6229 []))]))]]
    (by decide) (by decide +kernel)

theorem covered7165 : Range 7165 7189 :=
  scan_sound pool6757 pool6757_valid 6 7165 [5, 3, 67, 71, 3, 5, 0, 3, 43, 11, 3, 0] [[(2,(.split 5827 []))], [(2,(.split 1999 []))]]
    (by decide) (by decide +kernel)

theorem covered7189 : Range 7189 7213 :=
  scan_sound pool6757 pool6757_valid 6 7189 [7, 3, 0, 5, 3, 23, 19, 3, 5, 0, 3, 0] [[(2,(.split 1699 []))], [(2,(.split 2473717 [(1,(.raise [(95143,1)]))]))], [(2,(.split 65581 [(1,(.split 271 []))]))]]
    (by decide) (by decide +kernel)

theorem covered7213 : Range 7213 7237 :=
  scan_sound pool6757 pool6757_valid 6 7213 [0, 3, 7, 0, 3, 31, 5, 3, 0, 7, 3, 5] [[(2,(.split 178813 [(1,(.split 3083 []))]))], [(2,(.split 19543 []))], [(2,(.component 52265671 2 [(52265671,1)]))]]
    (by decide) (by decide +kernel)

theorem covered7237 : Range 7237 7261 :=
  scan_sound pool6757 pool6757_valid 6 7237 [0, 3, 13, 0, 3, 0, 11, 3, 0, 5, 3, 7] [[(2,(.split 1343113 [(1,(.split 671557 []))]))], [(2,(.split 17489431 []))], [(2,(.split 7503751 []))], [(2,(.component 52613263 2 [(52613263,1)]))]]
    (by decide) (by decide +kernel)

theorem covered7261 : Range 7261 7269 :=
  scan_sound pool6757 pool6757_valid 6 7261 [53, 3, 5, 13] []
    (by decide) (by decide +kernel)

theorem segment6757 : Range 6757 7269 := (range_join (range_join (range_join (range_join covered6757 covered6781) (range_join covered6805 (range_join covered6829 covered6853))) (range_join (range_join covered6877 (range_join covered6901 covered6925)) (range_join covered6949 (range_join covered6973 covered6997)))) (range_join (range_join (range_join covered7021 covered7045) (range_join covered7069 (range_join covered7093 covered7117))) (range_join (range_join covered7141 (range_join covered7165 covered7189)) (range_join covered7213 (range_join covered7237 covered7261)))))

theorem through7269 : Range 101 7269 := (range_join through6757 segment6757)

end OddPerfect.HarmonicChain.HarmonicRange101
