module

public import OddPerfect.HarmonicRange101.Part019
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicRange101

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf9829_0 : PrimeBank := .leaf [2, 3, 19, 47, 127, 199, 283, 367, 439, 787, 877, 1879, 4583, 13267, 19603, 20551]
theorem leaf9829_0_valid : leaf9829_0.Certified := by
  simp only [leaf9829_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 313] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 29, 79] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 67] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 137] }]), by simp⟩

@[expose] def leaf9829_1 : PrimeBank := .leaf [33199, 39679, 48487, 73363, 96973, 134077, 137477, 155821, 4674217, 5145403, 14067979, 32403247, 33156901]
theorem leaf9829_1_valid : leaf9829_1.Certified := by
  simp only [leaf9829_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 503] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 17, 389] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 8081] }, .lucas { root := 3, primeFactors := [2, 5, 101] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 12227] }, .lucas { root := 2, primeFactors := [2, 6113] }, .lucas { root := 3, primeFactors := [2, 191] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 8081] }, .lucas { root := 3, primeFactors := [2, 5, 101] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11173] }, .lucas { root := 5, primeFactors := [2, 3, 7, 19] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 34369] }, .lucas { root := 7, primeFactors := [2, 3, 179] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 53] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 59, 3301] }, .lucas { root := 6, primeFactors := [2, 3, 5, 11] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 857567] }, .lucas { root := 5, primeFactors := [2, 521, 823] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 709, 3307] }, .lucas { root := 2, primeFactors := [2, 3, 19, 29] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 31, 53, 173] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 19, 277] }]), by simp⟩

@[expose] def pool9829 : PrimeBank := (.branch 33199 leaf9829_0 leaf9829_1)
theorem pool9829_valid : pool9829.Certified := ⟨leaf9829_0_valid,leaf9829_1_valid⟩

theorem covered9829 : Range 9829 9853 :=
  scan_sound pool9829 pool9829_valid 4 9829 [0, 3, 0, 5, 3, 0, 13, 3, 5, 43, 3, 0] [[(2,(.split 73363 []))], [(2,(.split 39679 []))], [(2,(.split 20551 []))], [(2,(.split 787 []))]]
    (by decide) (by decide +kernel)

theorem covered9853 : Range 9853 9877 :=
  scan_sound pool9829 pool9829_valid 4 9853 [59, 3, 0, 0, 3, 7, 5, 3, 71, 0, 3, 5] [[(2,(.split 199 [(2,(.raise [(13267,1)]))]))], [(2,(.component 32403247 2 [(32403247,1)]))], [(2,(.split 19603 []))]]
    (by decide) (by decide +kernel)

theorem covered9877 : Range 9877 9901 :=
  scan_sound pool9829 pool9829_valid 4 9877 [7, 3, 41, 0, 3, 0, 11, 3, 13, 5, 3, 19] [[(2,(.split 1879 []))], [(2,(.split 5145403 []))]]
    (by decide) (by decide +kernel)

theorem covered9901 : Range 9901 9925 :=
  scan_sound pool9829 pool9829_valid 5 9901 [0, 3, 5, 0, 3, 11, 23, 3, 47, 7, 3, 0] [[(2,(.split 96973 [(1,(.raise [(48487,1)]))]))], [(2,(.split 4674217 [(1,(.split 137477 []))]))], [(2,(.split 14067979 []))]]
    (by decide) (by decide +kernel)

theorem covered9925 : Range 9925 9949 :=
  scan_sound pool9829 pool9829_valid 5 9925 [5, 3, 0, 0, 3, 5, 19, 3, 0, 61, 3, 7] [[(2,(.split 877 [(1,(.split 439 []))]))], [(2,(.split 155821 [(1,(.raise [(4583,1)]))]))], [(2,(.split 33199 []))]]
    (by decide) (by decide +kernel)

theorem covered9949 : Range 9949 9973 :=
  scan_sound pool9829 pool9829_valid 5 9949 [0, 3, 37, 5, 3, 23, 7, 3, 5, 0, 3, 13] [[(2,(.split 283 [(2,(.raise [(367,1)]))]))], [(2,(.split 134077 [(1,(.split 19 [(2,(.raise [(127,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered9973 : Range 9973 9997 :=
  scan_sound pool9829 pool9829_valid 5 9973 [0, 3, 11, 17, 3, 67, 5, 3, 7, 97, 3, 5] [[(2,(.split 33156901 [(1,(.raise [(47,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered9997 : Range 9997 10001 :=
  scan_sound pool9829 pool9829_valid 5 9997 [13, 3] []
    (by decide) (by decide +kernel)

theorem segment9829 : Range 9829 10001 := (range_join (range_join (range_join covered9829 covered9853) (range_join covered9877 covered9901)) (range_join (range_join covered9925 covered9949) (range_join covered9973 covered9997)))

theorem through10001 : Range 101 10001 := (range_join through9829 segment9829)

end OddPerfect.HarmonicChain.HarmonicRange101
