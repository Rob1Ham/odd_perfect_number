module

public import OddPerfect.SizePrimeBank300.Primes03
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.IndexComponent.SizePrimeBank300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def bankLeaf68 : PrimeBank := .leaf [202183, 203653, 204511, 205171, 205661, 207469, 208121, 209623, 211213, 211949, 213721, 213881, 214741, 215143, 217081, 218149]

theorem bankLeaf68_valid : bankLeaf68.Certified := by
  simp only [bankLeaf68, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5657] }, .lucas { root := 3, primeFactors := [2, 7, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 17, 401] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 977] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 13, 113] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 23, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5867] }, .lucas { root := 5, primeFactors := [2, 7, 419] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 4817] }, .lucas { root := 3, primeFactors := [2, 7, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 13, 137] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 1193] }, .lucas { root := 3, primeFactors := [2, 149] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 53] }]), by simp⟩

@[expose] noncomputable def bankLeaf69 : PrimeBank := .leaf [218527, 219437, 220021, 220057, 220897, 221101, 221623, 224317, 225751, 226063, 226741, 227431, 228251, 228451, 231877, 235003]

theorem bankLeaf69_valid : bankLeaf69.Certified := by
  simp only [bankLeaf69, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 17, 461] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 19, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 53, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 5, 11, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 43, 859] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 31, 67] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19, 661] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 1523] }, .lucas { root := 2, primeFactors := [2, 761] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 53, 739] }]), by simp⟩

@[expose] noncomputable def bankLeaf70 : PrimeBank := .leaf [236773, 237373, 238339, 241363, 243101, 247087, 249541, 249811, 250501, 251483, 251533, 255209, 258809, 260671, 261241, 263089]

theorem bankLeaf70_valid : bankLeaf70.Certified := by
  simp only [bankLeaf70, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 6577] }, .lucas { root := 5, primeFactors := [2, 3, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 131, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13241] }, .lucas { root := 3, primeFactors := [2, 5, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 23, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 37, 53] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 757] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 11, 23, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 19, 23, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 11, 17, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 8689] }, .lucas { root := 13, primeFactors := [2, 3, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 311] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 29] }]), by simp⟩

@[expose] noncomputable def bankLeaf71 : PrimeBank := .leaf [263621, 264031, 265871, 267233, 267541, 269117, 269389, 269519, 273253, 274121, 274847, 280589, 283541, 283831, 284131, 286633]

theorem bankLeaf71_valid : bankLeaf71.Certified := by
  simp only [bankLeaf71, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 269] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 13, 677] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 11, 2417] }, .lucas { root := 3, primeFactors := [2, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 1193] }, .lucas { root := 3, primeFactors := [2, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 13] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 1069] }, .lucas { root := 6, primeFactors := [2, 3, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 17, 7927] }, .lucas { root := 3, primeFactors := [2, 3, 1321] }, .lucas { root := 13, primeFactors := [2, 3, 5, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 3253] }, .lucas { root := 2, primeFactors := [2, 3, 271] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 11, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 13, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 11, 911] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 14177] }, .lucas { root := 3, primeFactors := [2, 443] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 11, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 1327] }, .lucas { root := 3, primeFactors := [2, 3, 13, 17] }]), by simp⟩

@[expose] noncomputable def bankLeaf72 : PrimeBank := .leaf [287347, 287503, 291271, 291439, 293147, 293459, 294103, 294247, 297841, 298399, 300247, 301211, 301627, 302411, 306517, 307873]

theorem bankLeaf72_valid : bankLeaf72.Certified := by
  simp only [bankLeaf72, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 83, 577] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 47917] }, .lucas { root := 5, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 5, 7, 19, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 257] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 16339] }, .lucas { root := 2, primeFactors := [2, 3, 7, 389] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 5449] }, .lucas { root := 7, primeFactors := [2, 3, 227] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 41, 1213] }, .lucas { root := 2, primeFactors := [2, 3, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 163, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 13, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 1289] }, .lucas { root := 6, primeFactors := [2, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 30241] }, .lucas { root := 11, primeFactors := [2, 3, 5, 7] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1069] }, .lucas { root := 6, primeFactors := [2, 3, 89] }]), by simp⟩

@[expose] noncomputable def bankLeaf73 : PrimeBank := .leaf [309937, 312971, 313163, 316037, 320083, 321679, 322459, 323101, 325597, 327689, 330427, 331141, 331711, 331841, 331937, 332191]

theorem bankLeaf73_valid : bankLeaf73.Certified := by
  simp only [bankLeaf73, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 587] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 17, 263] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 31, 5051] }, .lucas { root := 2, primeFactors := [2, 5, 101] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 7621] }, .lucas { root := 2, primeFactors := [2, 3, 5, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 23, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 223, 241] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 359] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 43, 631] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 40961] }, .lucas { root := 3, primeFactors := [2, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 29, 211] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 5519] }, .lucas { root := 13, primeFactors := [2, 31, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11057] }, .lucas { root := 3, primeFactors := [2, 691] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 17, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 23, 41] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf74 : PrimeBank := .leaf [332749, 337901, 340913, 341017, 342241, 343253, 343583, 343631, 344083, 344173, 345221, 347071, 350809, 351023, 354259, 356693]

theorem bankLeaf74_valid : bankLeaf74.Certified := by
  simp only [bankLeaf74, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 13, 79] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 13, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 13, 1093] }, .lucas { root := 5, primeFactors := [2, 3, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 23, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 13, 23, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 37, 4643] }, .lucas { root := 5, primeFactors := [2, 11, 211] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 4909] }, .lucas { root := 6, primeFactors := [2, 3, 409] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 57347] }, .lucas { root := 2, primeFactors := [2, 53, 541] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 29, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 41, 421] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 23, 503] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 47, 311] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19681] }, .lucas { root := 11, primeFactors := [2, 3, 5, 41] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf75 : PrimeBank := .leaf [360541, 360851, 363481, 363889, 364393, 373861, 375511, 376679, 377011, 383941, 385267, 386641, 389651, 392549, 395803, 395851]

theorem bankLeaf75_valid : bankLeaf75.Certified := by
  simp only [bankLeaf75, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 13, 233] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 241] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 31, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 12517] }, .lucas { root := 6, primeFactors := [2, 3, 7, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 331, 569] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 9173] }, .lucas { root := 2, primeFactors := [2, 2293] }, .lucas { root := 2, primeFactors := [2, 3, 191] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 7549] }, .lucas { root := 2, primeFactors := [2, 3, 17, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 1999] }, .lucas { root := 3, primeFactors := [2, 3, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 13, 29] }]), by simp⟩

@[expose] noncomputable def bankLeaf76 : PrimeBank := .leaf [398581, 399647, 400381, 401173, 403331, 404197, 407599, 410341, 411751, 412303, 413411, 414313, 415669, 418813, 424891, 426331]

theorem bankLeaf76_valid : bankLeaf76.Certified := by
  simp only [bankLeaf76, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 19, 809] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 6673] }, .lucas { root := 5, primeFactors := [2, 3, 139] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 53, 761] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 13, 2591] }, .lucas { root := 7, primeFactors := [2, 5, 7, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 67933] }, .lucas { root := 2, primeFactors := [2, 3, 17, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 977] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11, 6247] }, .lucas { root := 5, primeFactors := [2, 3, 347] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 41341] }, .lucas { root := 2, primeFactors := [2, 3, 5, 13, 53] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 2053] }, .lucas { root := 2, primeFactors := [2, 3, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 4721] }, .lucas { root := 6, primeFactors := [2, 5, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 1579] }, .lucas { root := 3, primeFactors := [2, 3, 263] }]), by simp⟩

@[expose] noncomputable def bankLeaf77 : PrimeBank := .leaf [429227, 431203, 434479, 434803, 436801, 438833, 444893, 447331, 456451, 457421, 459257, 465649, 466153, 467629, 469823, 471161]

theorem bankLeaf77_valid : bankLeaf77.Certified := by
  simp only [bankLeaf77, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 71867] }, .lucas { root := 2, primeFactors := [2, 35933] }, .lucas { root := 2, primeFactors := [2, 13, 691] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 29, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 72467] }, .lucas { root := 2, primeFactors := [2, 19, 1907] }, .lucas { root := 2, primeFactors := [2, 953] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 13] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 15889] }, .lucas { root := 21, primeFactors := [2, 3, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 31, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 17, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 22871] }, .lucas { root := 7, primeFactors := [2, 5, 2287] }, .lucas { root := 19, primeFactors := [2, 3, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 59, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 89, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19423] }, .lucas { root := 3, primeFactors := [2, 3, 13, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 19, 293] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 61, 3851] }, .lucas { root := 2, primeFactors := [2, 5, 7, 11] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf78 : PrimeBank := .leaf [472319, 472669, 473441, 473971, 475483, 485417, 490267, 492103, 499159, 507431, 509221, 509797, 513511, 519619, 521557, 528391]

theorem bankLeaf78_valid : bankLeaf78.Certified := by
  simp only [bankLeaf78, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 11, 3067] }, .lucas { root := 2, primeFactors := [2, 3, 7, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 17, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 11, 269] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 37, 61] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 47, 1291] }, .lucas { root := 2, primeFactors := [2, 3, 5, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 1297] }, .lucas { root := 10, primeFactors := [2, 3] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 7, 11, 659] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 17117] }, .lucas { root := 3, primeFactors := [2, 11, 389] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 7873] }, .lucas { root := 5, primeFactors := [2, 3, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 887] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 19, 103] }]), by simp⟩

@[expose] noncomputable def bankLeaf79 : PrimeBank := .leaf [539947, 541061, 544807, 548557, 550531, 550789, 554419, 555589, 556859, 567661, 568237, 568441, 570821, 578267, 585061, 585271]

theorem bankLeaf79_valid : bankLeaf79.Certified := by
  simp only [bankLeaf79, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13, 2081] }, .lucas { root := 3, primeFactors := [2, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 19, 59] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 2039] }, .lucas { root := 7, primeFactors := [2, 1019] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 79, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 10267] }, .lucas { root := 2, primeFactors := [2, 3, 29, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 23, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 29, 9601] }, .lucas { root := 13, primeFactors := [2, 3, 5] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 47353] }, .lucas { root := 5, primeFactors := [2, 3, 1973] }, .lucas { root := 2, primeFactors := [2, 17, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 1579] }, .lucas { root := 3, primeFactors := [2, 3, 263] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 28541] }, .lucas { root := 2, primeFactors := [2, 5, 1427] }, .lucas { root := 2, primeFactors := [2, 23, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 23, 967] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 7, 929] }]), by simp⟩

@[expose] noncomputable def bankLeaf80 : PrimeBank := .leaf [587959, 591901, 596899, 597823, 602477, 609757, 612067, 617341, 621301, 622513, 629567, 633151, 637337, 638767, 644599, 646879]

theorem bankLeaf80_valid : bankLeaf80.Certified := by
  simp only [bankLeaf80, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 13999] }, .lucas { root := 3, primeFactors := [2, 3, 2333] }, .lucas { root := 2, primeFactors := [2, 11, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 1973] }, .lucas { root := 2, primeFactors := [2, 17, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 33161] }, .lucas { root := 3, primeFactors := [2, 5, 829] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 5861] }, .lucas { root := 3, primeFactors := [2, 5, 293] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 21517] }, .lucas { root := 5, primeFactors := [2, 3, 11, 163] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 17, 61] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 193, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 7, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 19, 599] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 23, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 131, 823] }]), by simp⟩

@[expose] noncomputable def bankLeaf81 : PrimeBank := .leaf [649751, 650669, 652937, 653641, 666019, 666667, 670297, 671357, 672151, 672901, 672943, 674731, 674831, 675071, 675863, 685519]

theorem bankLeaf81_valid : bankLeaf81.Certified := by
  simp only [bankLeaf81, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 23, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 47, 3461] }, .lucas { root := 2, primeFactors := [2, 5, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 17, 4801] }, .lucas { root := 7, primeFactors := [2, 3, 5] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 163, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 29, primeFactors := [2, 3, 7, 11, 13, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 2539] }, .lucas { root := 2, primeFactors := [2, 3, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 23977] }, .lucas { root := 5, primeFactors := [2, 3, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 4481] }, .lucas { root := 3, primeFactors := [2, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 2243] }, .lucas { root := 2, primeFactors := [2, 19, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19, 5903] }, .lucas { root := 5, primeFactors := [2, 13, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 33, primeFactors := [2, 5, 13, 29, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 11, 17, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 31, 991] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 61, 1873] }, .lucas { root := 10, primeFactors := [2, 3, 13] }]), by simp⟩

@[expose] noncomputable def bankLeaf82 : PrimeBank := .leaf [688453, 690841, 699157, 705751, 707071, 708517, 708599, 709981, 712093, 716351, 726697, 733591, 737873, 739103, 740989, 741859]

theorem bankLeaf82_valid : bankLeaf82.Certified := by
  simp only [bankLeaf82, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 19, 101] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 941] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 13, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19681] }, .lucas { root := 11, primeFactors := [2, 3, 5, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 11, 31, 1039] }, .lucas { root := 3, primeFactors := [2, 3, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11833] }, .lucas { root := 5, primeFactors := [2, 3, 17, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 59341] }, .lucas { root := 14, primeFactors := [2, 3, 5, 23, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 14327] }, .lucas { root := 5, primeFactors := [2, 13, 19, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 10093] }, .lucas { root := 2, primeFactors := [2, 3, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 107, 431] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 13, 31, 131] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 9511] }, .lucas { root := 3, primeFactors := [2, 3, 5, 317] }]), by simp⟩

@[expose] noncomputable def bankLeaf83 : PrimeBank := .leaf [746167, 754451, 759631, 765181, 776467, 779351, 782671, 783763, 785947, 794191, 796819, 797161, 799651, 800281, 809359, 822067]

theorem bankLeaf83_valid : bankLeaf83.Certified := by
  simp only [bankLeaf83, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 23, 5407] }, .lucas { root := 3, primeFactors := [2, 3, 17, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 79, 191] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 25321] }, .lucas { root := 19, primeFactors := [2, 3, 5, 211] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 4793] }, .lucas { root := 3, primeFactors := [2, 599] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 11, 13, 109] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 18661] }, .lucas { root := 10, primeFactors := [2, 3, 5, 311] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 12073] }, .lucas { root := 7, primeFactors := [2, 3, 503] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 1777] }, .lucas { root := 5, primeFactors := [2, 3, 37] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 12263] }, .lucas { root := 5, primeFactors := [2, 6131] }, .lucas { root := 2, primeFactors := [2, 5, 613] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 23, 37] }]), by simp⟩

@[expose] noncomputable def bankLeaf84 : PrimeBank := .leaf [830833, 833101, 833281, 837313, 840241, 845041, 850181, 853837, 860641, 861001, 869501, 877543, 878837, 885041, 886799, 887143]

theorem bankLeaf84_valid : bankLeaf84.Certified := by
  simp only [bankLeaf84, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 2777] }, .lucas { root := 3, primeFactors := [2, 347] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 31] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 389] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 503] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 42509] }, .lucas { root := 2, primeFactors := [2, 10627] }, .lucas { root := 5, primeFactors := [2, 3, 7, 11, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 71153] }, .lucas { root := 3, primeFactors := [2, 4447] }, .lucas { root := 3, primeFactors := [2, 3, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 11, 163] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 37, 47] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 31387] }, .lucas { root := 2, primeFactors := [2, 3, 5231] }, .lucas { root := 7, primeFactors := [2, 5, 523] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13, 23, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 11, 173, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 199, 743] }]), by simp⟩

@[expose] noncomputable def bankLeaf85 : PrimeBank := .leaf [891859, 895087, 900217, 914597, 917141, 925669, 926659, 927973, 934561, 937049, 939931, 955337, 961273, 965647, 975701, 975899]

theorem bankLeaf85_valid : bankLeaf85.Certified := by
  simp only [bankLeaf85, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 13513] }, .lucas { root := 5, primeFactors := [2, 3, 563] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 12503] }, .lucas { root := 5, primeFactors := [2, 7, 19, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 373, 613] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 6551] }, .lucas { root := 17, primeFactors := [2, 5, 131] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 149, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 11, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 29, 577] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 17, 19, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 119417] }, .lucas { root := 3, primeFactors := [2, 11, 23, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 4877] }, .lucas { root := 2, primeFactors := [2, 23, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 887] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 11, 6337] }, .lucas { root := 10, primeFactors := [2, 3, 11] }]), by simp⟩

@[expose] noncomputable def bankLeaf86 : PrimeBank := .leaf [988007, 996311, 996367, 1009153, 1010981, 1012397, 1032851, 1034879, 1043131, 1046677, 1049281, 1050323, 1058821, 1067207, 1079059, 1097113]

theorem bankLeaf86_valid : bankLeaf86.Certified := by
  simp only [bankLeaf86, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 17, 29059] }, .lucas { root := 2, primeFactors := [2, 3, 29, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 43, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 3389] }, .lucas { root := 3, primeFactors := [2, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 50549] }, .lucas { root := 2, primeFactors := [2, 12637] }, .lucas { root := 2, primeFactors := [2, 3, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11, 19, 173] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 11, 29, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 87223] }, .lucas { root := 3, primeFactors := [2, 3, 14537] }, .lucas { root := 3, primeFactors := [2, 23, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 1093] }, .lucas { root := 5, primeFactors := [2, 3, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 13, 29, 199] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 31, 2459] }, .lucas { root := 2, primeFactors := [2, 1229] }, .lucas { root := 2, primeFactors := [2, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 17, 71, 149] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf87 : PrimeBank := .leaf [1113617, 1124131, 1136203, 1146217, 1159201, 1166323, 1182073, 1182431, 1192109, 1195189, 1202447, 1218911, 1220411, 1222567, 1232941, 1238101]

theorem bankLeaf87_valid : bankLeaf87.Certified := by
  simp only [bankLeaf87, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 61, 163] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 53, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 409, 463] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 163, 293] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 23] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 49253] }, .lucas { root := 2, primeFactors := [2, 7, 1759] }, .lucas { root := 6, primeFactors := [2, 3, 293] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 5, 23, 53, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 47, 373] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 137, 727] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 85889] }, .lucas { root := 3, primeFactors := [2, 11, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 11, 1583] }, .lucas { root := 5, primeFactors := [2, 7, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 122041] }, .lucas { root := 7, primeFactors := [2, 3, 5, 113] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 20549] }, .lucas { root := 2, primeFactors := [2, 11, 467] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 4127] }, .lucas { root := 5, primeFactors := [2, 2063] }, .lucas { root := 5, primeFactors := [2, 1031] }, .lucas { root := 14, primeFactors := [2, 5, 103] }]), by simp⟩

end OddPerfect.IndexComponent.SizePrimeBank300
