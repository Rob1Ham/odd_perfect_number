module

public import OddPerfect.SizePrimeBank300.Primes01
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.IndexComponent.SizePrimeBank300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def bankLeaf24 : PrimeBank := .leaf [4933, 4951, 4967, 4969, 5011, 5023, 5107, 5119, 5171, 5197, 5231, 5279, 5281, 5419, 5441, 5443]

theorem bankLeaf24_valid : bankLeaf24.Certified := by
  simp only [bankLeaf24, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 191] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 167] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 47] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 11] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 907] }]), by simp⟩

@[expose] noncomputable def bankLeaf25 : PrimeBank := .leaf [5471, 5503, 5569, 5573, 5591, 5623, 5641, 5651, 5659, 5683, 5701, 5711, 5743, 5779, 5783, 5821]

theorem bankLeaf25_valid : bankLeaf25.Certified := by
  simp only [bankLeaf25, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 547] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 13, 43] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 947] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 5, 571] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 97] }]), by simp⟩

@[expose] noncomputable def bankLeaf26 : PrimeBank := .leaf [6073, 6079, 6101, 6151, 6199, 6229, 6257, 6271, 6287, 6301, 6311, 6317, 6343, 6397, 6421, 6449]

theorem bankLeaf26_valid : bankLeaf26.Certified := by
  simp only [bankLeaf26, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 1013] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 41] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 17, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 11, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 449] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 631] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 1579] }, .lucas { root := 3, primeFactors := [2, 3, 263] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 41] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 31] }]), by simp⟩

@[expose] noncomputable def bankLeaf27 : PrimeBank := .leaf [6481, 6491, 6661, 6709, 6733, 6781, 6791, 6829, 6869, 6871, 6883, 6911, 6961, 7019, 7069, 7151]

theorem bankLeaf27_valid : bankLeaf27.Certified := by
  simp only [bankLeaf27, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 43] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 97] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 229] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 31, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 691] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 29] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf28 : PrimeBank := .leaf [7211, 7219, 7309, 7321, 7333, 7411, 7481, 7489, 7541, 7547, 7561, 7589, 7687, 7723, 7741, 7789]

theorem bankLeaf28_valid : bankLeaf28.Certified := by
  simp only [bankLeaf28, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 401] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 13, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 11, 17] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 271] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 13] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 59] }]), by simp⟩

@[expose] noncomputable def bankLeaf29 : PrimeBank := .leaf [7853, 7927, 7951, 8053, 8089, 8093, 8101, 8111, 8161, 8171, 8191, 8233, 8263, 8269, 8317, 8329]

theorem bankLeaf29_valid : bankLeaf29.Certified := by
  simp only [bankLeaf29, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1321] }, .lucas { root := 13, primeFactors := [2, 3, 5, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 337] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 811] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 19, 43] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 347] }]), by simp⟩

@[expose] noncomputable def bankLeaf30 : PrimeBank := .leaf [8353, 8419, 8429, 8431, 8447, 8599, 8681, 8713, 8737, 8761, 8779, 8807, 8831, 8941, 8971, 9011]

theorem bankLeaf30_valid : bankLeaf30.Certified := by
  simp only [bankLeaf30, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 23, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 43] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 41, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1433] }, .lucas { root := 3, primeFactors := [2, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 5, 7, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 11, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 17, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 883] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 53] }]), by simp⟩

@[expose] noncomputable def bankLeaf31 : PrimeBank := .leaf [9013, 9043, 9049, 9127, 9151, 9157, 9181, 9221, 9281, 9283, 9319, 9337, 9391, 9397, 9403, 9419]

theorem bankLeaf31_valid : bankLeaf31.Certified := by
  simp only [bankLeaf31, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 751] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 13, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 61] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 461] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1553] }, .lucas { root := 3, primeFactors := [2, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 389] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 313] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1567] }, .lucas { root := 3, primeFactors := [2, 3, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 277] }]), by simp⟩

@[expose] noncomputable def bankLeaf32 : PrimeBank := .leaf [9431, 9433, 9439, 9521, 9551, 9623, 9649, 9661, 9697, 9733, 9769, 9949, 9967, 10037, 10091, 10099]

theorem bankLeaf32_valid : bankLeaf32.Certified := by
  simp only [bankLeaf32, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 23, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 191] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 17, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 811] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 11, 37] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 193] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17] }]), by simp⟩

@[expose] noncomputable def bankLeaf33 : PrimeBank := .leaf [10111, 10193, 10211, 10253, 10271, 10303, 10357, 10391, 10477, 10567, 10627, 10651, 10687, 10711, 10753, 10771]

theorem bankLeaf33_valid : bankLeaf33.Certified := by
  simp only [bankLeaf33, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 337] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 1021] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 233] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 863] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 587] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 11, 23] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 359] }]), by simp⟩

@[expose] noncomputable def bankLeaf34 : PrimeBank := .leaf [10789, 10939, 10987, 10993, 11071, 11173, 11243, 11311, 11317, 11321, 11471, 11551, 11681, 11719, 11779, 11789]

theorem bankLeaf34_valid : bankLeaf34.Certified := by
  simp only [bankLeaf34, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1823] }, .lucas { root := 5, primeFactors := [2, 911] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1831] }, .lucas { root := 3, primeFactors := [2, 3, 5, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 229] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 11, 73] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 31, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 73] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 421] }]), by simp⟩

@[expose] noncomputable def bankLeaf35 : PrimeBank := .leaf [11807, 11887, 12007, 12071, 12097, 12241, 12251, 12277, 12301, 12373, 12377, 12391, 12503, 12517, 12553, 12601]

theorem bankLeaf35_valid : bankLeaf35.Certified := by
  simp only [bankLeaf35, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 23, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 17, 71] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 7, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 5, 7, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 19, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 523] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7] }]), by simp⟩

@[expose] noncomputable def bankLeaf36 : PrimeBank := .leaf [12611, 12641, 12671, 12853, 12911, 13187, 13219, 13267, 13441, 13553, 13679, 13681, 13729, 13831, 13859, 13931]

theorem bankLeaf36_valid : bankLeaf36.Certified := by
  simp only [bankLeaf36, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 7, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 5, 1291] }, .lucas { root := 2, primeFactors := [2, 3, 5, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 347] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2203] }, .lucas { root := 5, primeFactors := [2, 3, 367] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 977] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 461] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 41] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf37 : PrimeBank := .leaf [14009, 14029, 14083, 14197, 14327, 14389, 14401, 14537, 14621, 14713, 14737, 15149, 15313, 15331, 15443, 15451]

theorem bankLeaf37_valid : bankLeaf37.Certified := by
  simp only [bankLeaf37, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 167] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 13] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 23, 79] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 613] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 541] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 1103] }, .lucas { root := 5, primeFactors := [2, 19, 29] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf38 : PrimeBank := .leaf [15607, 15661, 15731, 15797, 15901, 16073, 16091, 16411, 16453, 16651, 16661, 16703, 17029, 17107, 17137, 17299]

theorem bankLeaf38_valid : bankLeaf38.Certified := by
  simp only [bankLeaf38, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 359] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 1609] }, .lucas { root := 7, primeFactors := [2, 3, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 547] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 457] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 1193] }, .lucas { root := 3, primeFactors := [2, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2851] }, .lucas { root := 2, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 17] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf39 : PrimeBank := .leaf [17317, 17359, 17431, 17443, 17471, 17491, 17609, 17707, 17791, 17881, 17971, 17977, 18041, 18061, 18307, 18341]

theorem bankLeaf39_valid : bankLeaf39.Certified := by
  simp only [bankLeaf39, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 263] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 1747] }, .lucas { root := 2, primeFactors := [2, 3, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 31, 71] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 593] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 149] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 107] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 131] }]), by simp⟩

@[expose] noncomputable def bankLeaf40 : PrimeBank := .leaf [18451, 18493, 18503, 18661, 18701, 18859, 18973, 19163, 19309, 19429, 19441, 19531, 19543, 19571, 19699, 19853]

theorem bankLeaf40_valid : bankLeaf40.Certified := by
  simp only [bankLeaf40, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 29] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 449] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 13, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 1609] }, .lucas { root := 7, primeFactors := [2, 3, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 1619] }, .lucas { root := 2, primeFactors := [2, 809] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 3257] }, .lucas { root := 3, primeFactors := [2, 11, 37] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 7, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 709] }]), by simp⟩

@[expose] noncomputable def bankLeaf41 : PrimeBank := .leaf [19927, 19937, 19949, 20011, 20021, 20029, 20143, 20149, 20161, 20323, 20359, 20551, 20731, 20749, 20857, 20939]

theorem bankLeaf41_valid : bankLeaf41.Certified := by
  simp only [bankLeaf41, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 4987] }, .lucas { root := 2, primeFactors := [2, 3, 277] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 23, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1669] }, .lucas { root := 2, primeFactors := [2, 3, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 373] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 73] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 13, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 691] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 19] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 29] }]), by simp⟩

@[expose] noncomputable def bankLeaf42 : PrimeBank := .leaf [21061, 21143, 21269, 21407, 21481, 21487, 21491, 21893, 21997, 22073, 22171, 22511, 22543, 22571, 22621, 22717]

theorem bankLeaf42_valid : bankLeaf42.Certified := by
  simp only [bankLeaf42, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 13] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 409] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 11, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 179] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 421] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 13, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 31, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 739] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 631] }]), by simp⟩

@[expose] noncomputable def bankLeaf43 : PrimeBank := .leaf [22921, 22961, 23011, 23017, 23269, 23321, 23339, 23563, 23599, 23887, 24019, 24061, 24151, 24181, 24229, 24509]

theorem bankLeaf43_valid : bankLeaf43.Certified := by
  simp only [bankLeaf43, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 191] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 13, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 137] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 1667] }, .lucas { root := 2, primeFactors := [2, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1327] }, .lucas { root := 3, primeFactors := [2, 3, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 4003] }, .lucas { root := 2, primeFactors := [2, 3, 23, 29] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 13, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 673] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 557] }]), by simp⟩

@[expose] noncomputable def bankLeaf44 : PrimeBank := .leaf [24571, 24631, 24697, 25117, 25261, 25411, 25453, 25537, 25609, 25621, 25759, 25903, 25981, 26209, 26437, 26683]

theorem bankLeaf44_valid : bankLeaf44.Certified := by
  simp only [bankLeaf44, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 821] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 421] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 97] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1439] }, .lucas { root := 7, primeFactors := [2, 719] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 2203] }, .lucas { root := 5, primeFactors := [2, 3, 367] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf45 : PrimeBank := .leaf [26701, 26711, 26801, 26951, 27031, 27061, 27211, 27277, 27457, 27481, 27583, 27611, 27691, 27817, 27847, 28211]

theorem bankLeaf45_valid : bankLeaf45.Certified := by
  simp only [bankLeaf45, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 5, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 2671] }, .lucas { root := 7, primeFactors := [2, 3, 5, 89] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 17, 53] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 907] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 229] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 4597] }, .lucas { root := 5, primeFactors := [2, 3, 383] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 251] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 13, 31] }]), by simp⟩

@[expose] noncomputable def bankLeaf46 : PrimeBank := .leaf [28393, 28429, 28537, 28663, 29251, 29947, 29989, 30103, 30757, 30781, 30937, 30941, 31051, 31069, 31253, 31477]

theorem bankLeaf46_valid : bankLeaf46.Certified := by
  simp only [bankLeaf46, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 103] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 23, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 29, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 1289] }, .lucas { root := 6, primeFactors := [2, 7, 23] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 863] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 601] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 43, 61] }]), by simp⟩

end OddPerfect.IndexComponent.SizePrimeBank300
