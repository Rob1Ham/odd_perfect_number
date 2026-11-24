module

public import OddPerfect.SizePrimeBank300.Primes02
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.IndexComponent.SizePrimeBank300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def bankLeaf47 : PrimeBank := .leaf [31981, 32413, 32579, 32779, 32969, 33151, 33161, 33287, 33331, 33457, 33829, 33937, 34511, 34607, 34721, 34807]

theorem bankLeaf47_valid : bankLeaf47.Certified := by
  simp only [bankLeaf47, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 13, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 37, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 7, 13, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 607] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 317] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 829] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 17, 89] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 17, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 2819] }, .lucas { root := 2, primeFactors := [2, 1409] }, .lucas { root := 3, primeFactors := [2, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 101] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5801] }, .lucas { root := 3, primeFactors := [2, 5, 29] }]), by simp⟩

@[expose] noncomputable def bankLeaf48 : PrimeBank := .leaf [34919, 35149, 35323, 36107, 36389, 36433, 36457, 37501, 37861, 37991, 38047, 38351, 38431, 38611, 38707, 39103]

theorem bankLeaf48_valid : bankLeaf48.Certified := by
  simp only [bankLeaf48, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 13, 17, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 2579] }, .lucas { root := 2, primeFactors := [2, 1289] }, .lucas { root := 6, primeFactors := [2, 7, 23] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 13, 59] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 6451] }, .lucas { root := 3, primeFactors := [2, 3, 5, 43] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf49 : PrimeBank := .leaf [39133, 39227, 39791, 39887, 40529, 40961, 40993, 41081, 41233, 41281, 41351, 41593, 41611, 41911, 41969, 42061]

theorem bankLeaf49_valid : bankLeaf49.Certified := by
  simp only [bankLeaf49, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1087] }, .lucas { root := 3, primeFactors := [2, 3, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 1783] }, .lucas { root := 10, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 23, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 11, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 17, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 61] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 827] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11, 127] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 701] }]), by simp⟩

@[expose] noncomputable def bankLeaf50 : PrimeBank := .leaf [42307, 42323, 42407, 42571, 42701, 42841, 42967, 43177, 43609, 43867, 44281, 44371, 44533, 45131, 45137, 45319]

theorem bankLeaf50_valid : bankLeaf50.Certified := by
  simp only [bankLeaf50, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 641] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 3023] }, .lucas { root := 5, primeFactors := [2, 1511] }, .lucas { root := 11, primeFactors := [2, 5, 151] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 257] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2437] }, .lucas { root := 2, primeFactors := [2, 3, 7, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1237] }, .lucas { root := 2, primeFactors := [2, 3, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 4513] }, .lucas { root := 7, primeFactors := [2, 3, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 13, 31] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf51 : PrimeBank := .leaf [45343, 45613, 45673, 45817, 46051, 46153, 46187, 46411, 46489, 46687, 46751, 47431, 47563, 47711, 48973, 49477]

theorem bankLeaf51_valid : bankLeaf51.Certified := by
  simp only [bankLeaf51, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 11, 229] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 23, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 307] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 3299] }, .lucas { root := 2, primeFactors := [2, 17, 97] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 29, primeFactors := [2, 3, 13, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 31, 251] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 17, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7927] }, .lucas { root := 3, primeFactors := [2, 3, 1321] }, .lucas { root := 13, primeFactors := [2, 3, 5, 11] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 11, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 19, 31] }]), by simp⟩

@[expose] noncomputable def bankLeaf52 : PrimeBank := .leaf [49531, 49549, 49801, 49823, 50093, 50159, 50359, 51031, 51283, 51349, 51437, 51949, 52051, 52697, 52711, 52783]

theorem bankLeaf52_valid : bankLeaf52.Certified := by
  simp only [bankLeaf52, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 13, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 4129] }, .lucas { root := 13, primeFactors := [2, 3, 43] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 1789] }, .lucas { root := 6, primeFactors := [2, 3, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 31, 809] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 11, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11, 389] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 11, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 347] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 941] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 7, 251] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19, 463] }]), by simp⟩

@[expose] noncomputable def bankLeaf53 : PrimeBank := .leaf [53551, 53719, 54367, 54829, 54869, 54907, 55147, 55163, 55213, 55333, 55631, 55681, 55721, 55897, 56197, 56629]

theorem bankLeaf53_valid : bankLeaf53.Certified := by
  simp only [bankLeaf53, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 1279] }, .lucas { root := 3, primeFactors := [2, 3, 71] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1523] }, .lucas { root := 2, primeFactors := [2, 761] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 29, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 9151] }, .lucas { root := 3, primeFactors := [2, 3, 5, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13, 101] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 43, 107] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 5563] }, .lucas { root := 2, primeFactors := [2, 3, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 199] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 223] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 13] }]), by simp⟩

@[expose] noncomputable def bankLeaf54 : PrimeBank := .leaf [56783, 58031, 58129, 58217, 59221, 59471, 59951, 60631, 60761, 61051, 61637, 61909, 62071, 62683, 63601, 63659]

theorem bankLeaf54_valid : bankLeaf54.Certified := by
  simp only [bankLeaf54, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 29, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 829] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 19, 383] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 11, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 43, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 811] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 11, 67] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 31, 337] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 4547] }, .lucas { root := 2, primeFactors := [2, 2273] }, .lucas { root := 3, primeFactors := [2, 71] }]), by simp⟩

@[expose] noncomputable def bankLeaf55 : PrimeBank := .leaf [64171, 64453, 64951, 65029, 65033, 65119, 65287, 65617, 66083, 66431, 66529, 66733, 67411, 68111, 69151, 69401]

theorem bankLeaf55_valid : bankLeaf55.Certified := by
  simp only [bankLeaf55, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 41, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 433] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 739] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 10853] }, .lucas { root := 2, primeFactors := [2, 2713] }, .lucas { root := 5, primeFactors := [2, 3, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 1367] }, .lucas { root := 5, primeFactors := [2, 683] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 37, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 13, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 67, 83] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 461] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 347] }]), by simp⟩

@[expose] noncomputable def bankLeaf56 : PrimeBank := .leaf [69439, 70001, 70841, 71941, 71999, 72073, 72229, 72367, 73121, 73417, 73421, 74449, 75181, 75211, 75709, 75991]

theorem bankLeaf56_valid : bankLeaf56.Certified := by
  simp only [bankLeaf56, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 71, 163] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 11, 13] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 1723] }, .lucas { root := 3, primeFactors := [2, 3, 7, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 457] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 19, 23] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 23, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 701] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 17, 149] }]), by simp⟩

@[expose] noncomputable def bankLeaf57 : PrimeBank := .leaf [76259, 76423, 76543, 76873, 77477, 78031, 78049, 78787, 79561, 79579, 79633, 80173, 80761, 81667, 81973, 82031]

theorem bankLeaf57_valid : bankLeaf57.Certified := by
  simp only [bankLeaf57, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 13, 419] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 47, 271] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 12757] }, .lucas { root := 2, primeFactors := [2, 3, 1063] }, .lucas { root := 3, primeFactors := [2, 3, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 3203] }, .lucas { root := 2, primeFactors := [2, 1601] }, .lucas { root := 3, primeFactors := [2, 5] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 17] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1459] }, .lucas { root := 3, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 4421] }, .lucas { root := 3, primeFactors := [2, 5, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 17, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 673] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 13, 631] }]), by simp⟩

@[expose] noncomputable def bankLeaf58 : PrimeBank := .leaf [82219, 83267, 83443, 84437, 84449, 85009, 85447, 86353, 86371, 87041, 87403, 87421, 87541, 87931, 88069, 89119]

theorem bankLeaf58_valid : bankLeaf58.Certified := by
  simp only [bankLeaf58, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 71, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 31, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13907] }, .lucas { root := 2, primeFactors := [2, 17, 409] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 13, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 11, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 47, 101] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 2879] }, .lucas { root := 7, primeFactors := [2, 1439] }, .lucas { root := 7, primeFactors := [2, 719] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 2081] }, .lucas { root := 3, primeFactors := [2, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 31, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 18, primeFactors := [2, 3, 5, 1459] }, .lucas { root := 3, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 977] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 41, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 4951] }, .lucas { root := 6, primeFactors := [2, 3, 5, 11] }]), by simp⟩

@[expose] noncomputable def bankLeaf59 : PrimeBank := .leaf [90793, 91411, 91921, 92041, 92051, 93151, 93251, 93811, 93871, 93979, 94261, 94529, 94777, 94873, 94907, 95089]

theorem bankLeaf59_valid : bankLeaf59.Certified := by
  simp only [bankLeaf59, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 383] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 13, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 263] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 373] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 23, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 1571] }, .lucas { root := 2, primeFactors := [2, 5, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 211] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11, 359] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 59, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 6779] }, .lucas { root := 2, primeFactors := [2, 3389] }, .lucas { root := 3, primeFactors := [2, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 283] }]), by simp⟩

@[expose] noncomputable def bankLeaf60 : PrimeBank := .leaf [95239, 95531, 95803, 96199, 96581, 97813, 98779, 99581, 99709, 101051, 101173, 101323, 101347, 102001, 102607, 104281]

theorem bankLeaf60_valid : bankLeaf60.Certified := by
  simp only [bankLeaf60, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 41, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 2281] }, .lucas { root := 7, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 16033] }, .lucas { root := 5, primeFactors := [2, 3, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 439] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 101, 163] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13, 383] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 1187] }, .lucas { root := 2, primeFactors := [2, 593] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 8431] }, .lucas { root := 3, primeFactors := [2, 3, 5, 281] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 433] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 19, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 31, primeFactors := [2, 3, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 349] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf61 : PrimeBank := .leaf [104707, 105337, 106747, 107599, 108421, 108541, 110557, 110563, 110881, 111191, 112501, 114769, 114847, 116539, 116911, 119827]

theorem bankLeaf61_valid : bankLeaf61.Certified := by
  simp only [bankLeaf61, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 277] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17791] }, .lucas { root := 3, primeFactors := [2, 3, 5, 593] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 79, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 13, 139] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 37, 83] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 69, primeFactors := [2, 3, 5, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 11119] }, .lucas { root := 3, primeFactors := [2, 3, 17, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 19141] }, .lucas { root := 2, primeFactors := [2, 3, 5, 11, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19423] }, .lucas { root := 3, primeFactors := [2, 3, 13, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 433] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 317] }]), by simp⟩

@[expose] noncomputable def bankLeaf62 : PrimeBank := .leaf [120077, 120691, 121921, 122131, 122201, 122827, 123127, 124249, 124633, 124771, 125407, 125539, 125731, 125887, 126127, 126457]

theorem bankLeaf62_valid : bankLeaf62.Certified := by
  simp only [bankLeaf62, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 2729] }, .lucas { root := 3, primeFactors := [2, 11, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 149] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 5, 23, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 1861] }, .lucas { root := 2, primeFactors := [2, 3, 5, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 20521] }, .lucas { root := 11, primeFactors := [2, 3, 5, 19] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 4159] }, .lucas { root := 3, primeFactors := [2, 3, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 6967] }, .lucas { root := 5, primeFactors := [2, 3, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 61] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 20981] }, .lucas { root := 2, primeFactors := [2, 5, 1049] }, .lucas { root := 3, primeFactors := [2, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 11, 479] }]), by simp⟩

@[expose] noncomputable def bankLeaf63 : PrimeBank := .leaf [127189, 128341, 128351, 129529, 130589, 130769, 130957, 131041, 131293, 132019, 135913, 136397, 136417, 137117, 139891, 140071]

theorem bankLeaf63_valid : bankLeaf63.Certified := by
  simp only [bankLeaf63, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 17, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 37, primeFactors := [2, 3, 7, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 32647] }, .lucas { root := 3, primeFactors := [2, 3, 5441] }, .lucas { root := 3, primeFactors := [2, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 743] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 1559] }, .lucas { root := 19, primeFactors := [2, 19, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 521] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 22003] }, .lucas { root := 2, primeFactors := [2, 3, 19, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 809] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 43, 61] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 59, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 4663] }, .lucas { root := 3, primeFactors := [2, 3, 7, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 30, primeFactors := [2, 3, 5, 7, 23, 29] }]), by simp⟩

@[expose] noncomputable def bankLeaf64 : PrimeBank := .leaf [140317, 140533, 141353, 141443, 141667, 143719, 144941, 145381, 147449, 148513, 150001, 151201, 151841, 152407, 153259, 154267]

theorem bankLeaf64_valid : bankLeaf64.Certified := by
  simp only [bankLeaf64, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 1063] }, .lucas { root := 3, primeFactors := [2, 3, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 239] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 17669] }, .lucas { root := 2, primeFactors := [2, 7, 631] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 10103] }, .lucas { root := 5, primeFactors := [2, 5051] }, .lucas { root := 2, primeFactors := [2, 5, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 3373] }, .lucas { root := 5, primeFactors := [2, 3, 281] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 17, 1409] }, .lucas { root := 3, primeFactors := [2, 11] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 2633] }, .lucas { root := 3, primeFactors := [2, 7, 47] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13, 73] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 7, 41, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 7, 3673] }, .lucas { root := 5, primeFactors := [2, 3, 17] }]), by simp⟩

@[expose] noncomputable def bankLeaf65 : PrimeBank := .leaf [154871, 156577, 156967, 157189, 158563, 159157, 160651, 160681, 161009, 161683, 162079, 162709, 163417, 164173, 164653, 165211]

theorem bankLeaf65_valid : bankLeaf65.Certified := by
  simp only [bankLeaf65, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 17, 911] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 26161] }, .lucas { root := 13, primeFactors := [2, 3, 5, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 13099] }, .lucas { root := 3, primeFactors := [2, 3, 37, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 383] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 4421] }, .lucas { root := 3, primeFactors := [2, 5, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 13, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 29, 347] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 26947] }, .lucas { root := 2, primeFactors := [2, 3, 499] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 17, 227] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13681] }, .lucas { root := 22, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13721] }, .lucas { root := 3, primeFactors := [2, 5, 7] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf66 : PrimeBank := .leaf [165511, 167107, 171007, 173743, 173977, 174631, 176419, 176779, 177917, 178987, 179743, 179947, 181123, 182701, 182713, 183361]

theorem bankLeaf66_valid : bankLeaf66.Certified := by
  simp only [bankLeaf66, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 613] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 27851] }, .lucas { root := 2, primeFactors := [2, 5, 557] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 2591] }, .lucas { root := 7, primeFactors := [2, 5, 7, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 23, 1259] }, .lucas { root := 2, primeFactors := [2, 17, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11, 659] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 5821] }, .lucas { root := 6, primeFactors := [2, 3, 5, 97] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 23, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 2341] }, .lucas { root := 7, primeFactors := [2, 3, 5, 13] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 769] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 30187] }, .lucas { root := 5, primeFactors := [2, 3, 13, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 29] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 191] }]), by simp⟩

@[expose] noncomputable def bankLeaf67 : PrimeBank := .leaf [184003, 184651, 185167, 185441, 185707, 187123, 188563, 189337, 190097, 191911, 192811, 193603, 194071, 196043, 198241, 199033]

theorem bankLeaf67_valid : bankLeaf67.Certified := by
  simp only [bankLeaf67, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 337] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 1231] }, .lucas { root := 3, primeFactors := [2, 3, 5, 41] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 19, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 2399] }, .lucas { root := 11, primeFactors := [2, 11, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 2857] }, .lucas { root := 11, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 23] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 6397] }, .lucas { root := 2, primeFactors := [2, 3, 13, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 6427] }, .lucas { root := 3, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 41, 787] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 6469] }, .lucas { root := 2, primeFactors := [2, 3, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 11, 19, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 7, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 8293] }, .lucas { root := 2, primeFactors := [2, 3, 691] }]), by simp⟩

end OddPerfect.IndexComponent.SizePrimeBank300
