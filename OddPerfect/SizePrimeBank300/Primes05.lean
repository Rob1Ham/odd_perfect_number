module

public import OddPerfect.SizePrimeBank300.Primes04
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.IndexComponent.SizePrimeBank300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def bankLeaf88 : PrimeBank := .leaf [1246591, 1248119, 1249121, 1250413, 1251121, 1259413, 1289513, 1290299, 1292989, 1305391, 1311127, 1312211, 1333691, 1339297, 1347919, 1351093]

theorem bankLeaf88_valid : bankLeaf88.Certified := by
  simp only [bankLeaf88, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 23, 43, 631] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 34, primeFactors := [2, 3, 5, 13, 401] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 11, 29, 47] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 645149] }, .lucas { root := 2, primeFactors := [2, 7, 23041] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 19, 53, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 53, 821] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 218521] }, .lucas { root := 17, primeFactors := [2, 3, 5, 607] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 131221] }, .lucas { root := 2, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 197, 677] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 1993] }, .lucas { root := 5, primeFactors := [2, 3, 83] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf89 : PrimeBank := .leaf [1363259, 1371511, 1372537, 1380277, 1400803, 1425091, 1434637, 1439561, 1454119, 1460743, 1477807, 1478251, 1480891, 1506341, 1509997, 1535719]

theorem bankLeaf89_valid : bankLeaf89.Certified := by
  simp only [bankLeaf89, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 52433] }, .lucas { root := 3, primeFactors := [2, 29, 113] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 17959] }, .lucas { root := 6, primeFactors := [2, 3, 41, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 67, 709] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 5693] }, .lucas { root := 2, primeFactors := [2, 1423] }, .lucas { root := 3, primeFactors := [2, 3, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 17, 29, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 29, 61, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 14321] }, .lucas { root := 3, primeFactors := [2, 5, 179] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 49363] }, .lucas { root := 2, primeFactors := [2, 3, 19, 433] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 41, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 5471] }, .lucas { root := 7, primeFactors := [2, 5, 547] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 311, 823] }]), by simp⟩

@[expose] noncomputable def bankLeaf90 : PrimeBank := .leaf [1554379, 1578961, 1581191, 1582381, 1586699, 1597289, 1599181, 1631059, 1644691, 1652701, 1660507, 1667353, 1672751, 1674289, 1682207, 1692283]

theorem bankLeaf90_valid : bankLeaf90.Certified := by
  simp only [bankLeaf90, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 17, 311] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 5, 13, 12163] }, .lucas { root := 5, primeFactors := [2, 3, 2027] }, .lucas { root := 2, primeFactors := [2, 1013] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 59, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 607, 1307] }, .lucas { root := 2, primeFactors := [2, 653] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11, 2593] }, .lucas { root := 7, primeFactors := [2, 3] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 13, 1901] }, .lucas { root := 2, primeFactors := [2, 5, 19] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 787] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 109, 2539] }, .lucas { root := 2, primeFactors := [2, 3, 47] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 6691] }, .lucas { root := 2, primeFactors := [2, 3, 5, 223] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf91 : PrimeBank := .leaf [1692337, 1697041, 1724059, 1733647, 1734769, 1747013, 1774921, 1776701, 1803647, 1806113, 1809421, 1814383, 1814693, 1818871, 1845751, 1854991]

theorem bankLeaf91_valid : bankLeaf91.Certified := by
  simp only [bankLeaf91, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 21, primeFactors := [2, 3, 5, 2357] }, .lucas { root := 2, primeFactors := [2, 19, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 4561] }, .lucas { root := 11, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 113, 2557] }, .lucas { root := 2, primeFactors := [2, 3, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 7, 1721] }, .lucas { root := 3, primeFactors := [2, 5, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 127, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 7, 2113] }, .lucas { root := 5, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 109, 163] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 18, primeFactors := [2, 3, 5, 53, 569] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 100799] }, .lucas { root := 17, primeFactors := [2, 101, 499] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 41243] }, .lucas { root := 2, primeFactors := [2, 17, 1213] }, .lucas { root := 2, primeFactors := [2, 3, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 19, 3191] }, .lucas { root := 11, primeFactors := [2, 5, 11, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 23, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 20611] }, .lucas { root := 2, primeFactors := [2, 3, 5, 229] }]), by simp⟩

@[expose] noncomputable def bankLeaf92 : PrimeBank := .leaf [1862687, 1867147, 1888171, 1909021, 1926611, 1937891, 1948783, 1949359, 1950391, 1964041, 1969921, 1973011, 1983851, 1984891, 1998233, 2004817]

theorem bankLeaf92_valid : bankLeaf92.Certified := by
  simp only [bankLeaf92, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 7, 83, 229] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 31817] }, .lucas { root := 3, primeFactors := [2, 41, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 17, 1619] }, .lucas { root := 2, primeFactors := [2, 809] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 193789] }, .lucas { root := 2, primeFactors := [2, 3, 7, 769] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 29527] }, .lucas { root := 3, primeFactors := [2, 3, 7, 19, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 324893] }, .lucas { root := 2, primeFactors := [2, 81223] }, .lucas { root := 5, primeFactors := [2, 3, 13537] }, .lucas { root := 7, primeFactors := [2, 3, 47] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 5059] }, .lucas { root := 2, primeFactors := [2, 3, 281] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 109, 607] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 249779] }, .lucas { root := 2, primeFactors := [2, 71, 1759] }, .lucas { root := 6, primeFactors := [2, 3, 293] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 3797] }, .lucas { root := 2, primeFactors := [2, 13, 73] }]), by simp⟩

@[expose] noncomputable def bankLeaf93 : PrimeBank := .leaf [2032507, 2044111, 2060389, 2064077, 2064379, 2064583, 2075273, 2113211, 2147081, 2163289, 2170939, 2180921, 2183063, 2196541, 2219869, 2242381]

theorem bankLeaf93_valid : bankLeaf93.Certified := by
  simp only [bankLeaf93, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 19, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 61, 1117] }, .lucas { root := 2, primeFactors := [2, 3, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 43] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 37, 547] }]),
    by primality (cert := .witnesses [.lucas { root := 21, primeFactors := [2, 3, 13, 17, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 149, 1741] }, .lucas { root := 2, primeFactors := [2, 3, 5, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 19211] }, .lucas { root := 6, primeFactors := [2, 5, 17, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13, 4129] }, .lucas { root := 13, primeFactors := [2, 3, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 23, 3919] }, .lucas { root := 3, primeFactors := [2, 3, 653] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 11, 37, 127] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 19, 29, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 12203] }, .lucas { root := 2, primeFactors := [2, 6101] }, .lucas { root := 2, primeFactors := [2, 5, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 23, 383] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 19, 281] }]), by simp⟩

@[expose] noncomputable def bankLeaf94 : PrimeBank := .leaf [2270159, 2278747, 2289401, 2291041, 2311333, 2324557, 2332903, 2334037, 2352289, 2362573, 2368181, 2368451, 2380141, 2385619, 2404291, 2409829]

theorem bankLeaf94_valid : bankLeaf94.Certified := by
  simp only [bankLeaf94, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 11, 19, 5431] }, .lucas { root := 3, primeFactors := [2, 3, 5, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 2221] }, .lucas { root := 2, primeFactors := [2, 3, 5, 37] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 29, primeFactors := [2, 3, 5, 37, 43] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 4967] }, .lucas { root := 5, primeFactors := [2, 13, 191] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 13, 2719] }, .lucas { root := 3, primeFactors := [2, 3, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 19, 29, 353] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 107, 229] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29, 31, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 118409] }, .lucas { root := 3, primeFactors := [2, 19, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 67, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 1889] }, .lucas { root := 3, primeFactors := [2, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 97, 4099] }, .lucas { root := 2, primeFactors := [2, 3, 683] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 107] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf95 : PrimeBank := .leaf [2415103, 2426789, 2428541, 2431489, 2468269, 2526913, 2537551, 2542879, 2556331, 2574587, 2580901, 2599783, 2608387, 2624711, 2641061, 2665001]

theorem bankLeaf95_valid : bankLeaf95.Certified := by
  simp only [bankLeaf95, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 402517] }, .lucas { root := 5, primeFactors := [2, 3, 3727] }, .lucas { root := 3, primeFactors := [2, 3, 23] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 31, 3917] }, .lucas { root := 2, primeFactors := [2, 11, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 1583] }, .lucas { root := 5, primeFactors := [2, 7, 113] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 41, 107] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 10867] }, .lucas { root := 2, primeFactors := [2, 3, 1811] }, .lucas { root := 6, primeFactors := [2, 5, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 37, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 173, 1063] }, .lucas { root := 3, primeFactors := [2, 3, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 1229] }, .lucas { root := 2, primeFactors := [2, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 23, 18839] }, .lucas { root := 7, primeFactors := [2, 9419] }, .lucas { root := 2, primeFactors := [2, 17, 277] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 11, 107, 223] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 37, 43, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13, 41] }]), by simp⟩

@[expose] noncomputable def bankLeaf96 : PrimeBank := .leaf [2687231, 2707091, 2729983, 2732491, 2746609, 2748401, 2770771, 2776351, 2780923, 2809087, 2829217, 2833279, 2889151, 2910031, 2922391, 2935811]

theorem bankLeaf96_valid : bankLeaf96.Certified := by
  simp only [bankLeaf96, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 13, 2953] }, .lucas { root := 13, primeFactors := [2, 3, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 270709] }, .lucas { root := 2, primeFactors := [2, 3, 17, 1327] }, .lucas { root := 3, primeFactors := [2, 3, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 67, 6791] }, .lucas { root := 7, primeFactors := [2, 5, 7, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 97, 313] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 6871] }, .lucas { root := 3, primeFactors := [2, 3, 5, 229] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 19, 4861] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 83, 223] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 66883] }, .lucas { root := 2, primeFactors := [2, 3, 71, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 2267] }, .lucas { root := 2, primeFactors := [2, 11, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 23, 419] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 11, 17, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 97001] }, .lucas { root := 3, primeFactors := [2, 5, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 19, 1709] }, .lucas { root := 3, primeFactors := [2, 7, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 173, 1697] }, .lucas { root := 3, primeFactors := [2, 53] }]), by simp⟩

@[expose] noncomputable def bankLeaf97 : PrimeBank := .leaf [3018317, 3044803, 3047441, 3047921, 3049537, 3080393, 3121057, 3142757, 3144079, 3167849, 3183751, 3198967, 3226441, 3264851, 3287587, 3287821]

theorem bankLeaf97_valid : bankLeaf97.Certified := by
  simp only [bankLeaf97, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 17, 373] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 29851] }, .lucas { root := 2, primeFactors := [2, 3, 5, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 3463] }, .lucas { root := 3, primeFactors := [2, 3, 577] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 31, 1229] }, .lucas { root := 2, primeFactors := [2, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 2269] }, .lucas { root := 2, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 67, 821] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 10837] }, .lucas { root := 2, primeFactors := [2, 3, 7, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 113, 409] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 7, 24953] }, .lucas { root := 3, primeFactors := [2, 3119] }, .lucas { root := 7, primeFactors := [2, 1559] }, .lucas { root := 19, primeFactors := [2, 19, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 17, 23293] }, .lucas { root := 5, primeFactors := [2, 3, 647] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 563, 947] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7, 23, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 23, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 367, 1493] }, .lucas { root := 2, primeFactors := [2, 373] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37, 1481] }, .lucas { root := 3, primeFactors := [2, 5, 37] }]), by simp⟩

@[expose] noncomputable def bankLeaf98 : PrimeBank := .leaf [3301169, 3329033, 3329761, 3330391, 3348577, 3349603, 3384389, 3400693, 3409261, 3447767, 3459751, 3470287, 3511271, 3535027, 3562849, 3563501]

theorem bankLeaf98_valid : bankLeaf98.Certified := by
  simp only [bankLeaf98, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 59, 269] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 59447] }, .lucas { root := 5, primeFactors := [2, 29723] }, .lucas { root := 2, primeFactors := [2, 7, 11, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 991] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 15859] }, .lucas { root := 2, primeFactors := [2, 3, 881] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 379, 491] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 120871] }, .lucas { root := 3, primeFactors := [2, 3, 5, 17, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 53, 5347] }, .lucas { root := 3, primeFactors := [2, 3, 11] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 383, 643] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 659] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 23, 25147] }, .lucas { root := 2, primeFactors := [2, 3, 11, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 103, 487] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 19, 2819] }, .lucas { root := 2, primeFactors := [2, 1409] }, .lucas { root := 3, primeFactors := [2, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 89, 139] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf99 : PrimeBank := .leaf [3587347, 3619843, 3641611, 3654361, 3658159, 3664781, 3666121, 3675989, 3680491, 3701917, 3706621, 3731137, 3731443, 3733049, 3737791, 3741053]

theorem bankLeaf99_valid : bankLeaf99.Certified := by
  simp only [bankLeaf99, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 71, 401] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 113, 281] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 10151] }, .lucas { root := 7, primeFactors := [2, 5, 7, 29] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 26177] }, .lucas { root := 3, primeFactors := [2, 409] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 137, 223] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 73, 12589] }, .lucas { root := 2, primeFactors := [2, 3, 1049] }, .lucas { root := 3, primeFactors := [2, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 11, 19, 587] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 151, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 163, 379] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19433] }, .lucas { root := 3, primeFactors := [2, 7, 347] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 13, 4349] }, .lucas { root := 2, primeFactors := [2, 1087] }, .lucas { root := 3, primeFactors := [2, 3, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 59, 719] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 7, 17, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 19087] }, .lucas { root := 19, primeFactors := [2, 3, 3181] }, .lucas { root := 7, primeFactors := [2, 3, 5, 53] }]), by simp⟩

@[expose] noncomputable def bankLeaf100 : PrimeBank := .leaf [3741541, 3777013, 3852949, 3867557, 3903337, 3909799, 3957647, 3981071, 3985297, 3994171, 4015513, 4046927, 4069279, 4071031, 4088839, 4092479]

theorem bankLeaf100_valid : bankLeaf100.Certified := by
  simp only [bankLeaf100, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 5669] }, .lucas { root := 3, primeFactors := [2, 13, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 104917] }, .lucas { root := 2, primeFactors := [2, 3, 7, 1249] }, .lucas { root := 7, primeFactors := [2, 3, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 11, 17, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 11, 29, 433] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 17, 1063] }, .lucas { root := 3, primeFactors := [2, 3, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 83, 2617] }, .lucas { root := 5, primeFactors := [2, 3, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 11, 31, 829] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 29, 409] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 29, 4591] }, .lucas { root := 11, primeFactors := [2, 3, 5, 17] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 31, 5021] }, .lucas { root := 3, primeFactors := [2, 5, 251] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2791] }, .lucas { root := 6, primeFactors := [2, 3, 5, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 135701] }, .lucas { root := 2, primeFactors := [2, 5, 23, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 13, 19, 31, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 31, primeFactors := [2, 13, 17, 47, 197] }]), by simp⟩

@[expose] noncomputable def bankLeaf101 : PrimeBank := .leaf [4129921, 4238761, 4252519, 4253747, 4257679, 4267927, 4288159, 4313591, 4355977, 4370521, 4377343, 4404047, 4418831, 4429057, 4547831, 4555237]

theorem bankLeaf101_valid : bankLeaf101.Certified := by
  simp only [bankLeaf101, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 239] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 35323] }, .lucas { root := 3, primeFactors := [2, 3, 7, 29] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 303839] }, .lucas { root := 7, primeFactors := [2, 43, 3533] }, .lucas { root := 2, primeFactors := [2, 883] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 61, 11633] }, .lucas { root := 3, primeFactors := [2, 727] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 23, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 34033] }, .lucas { root := 7, primeFactors := [2, 3, 709] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 97, 4447] }, .lucas { root := 3, primeFactors := [2, 3, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 181499] }, .lucas { root := 2, primeFactors := [2, 90749] }, .lucas { root := 2, primeFactors := [2, 7, 463] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 7, 11, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 729557] }, .lucas { root := 2, primeFactors := [2, 182389] }, .lucas { root := 6, primeFactors := [2, 3, 15199] }, .lucas { root := 6, primeFactors := [2, 3, 17, 149] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 13, 19, 1789] }, .lucas { root := 6, primeFactors := [2, 3, 149] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 64969] }, .lucas { root := 13, primeFactors := [2, 3, 2707] }, .lucas { root := 2, primeFactors := [2, 3, 11, 41] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf102 : PrimeBank := .leaf [4573633, 4574149, 4580731, 4593499, 4618291, 4647193, 4665461, 4666801, 4690303, 4700567, 4728697, 4760281, 4822039, 4873051, 4930927, 4960807]

theorem bankLeaf102_valid : bankLeaf102.Certified := by
  simp only [bankLeaf102, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 41, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 16573] }, .lucas { root := 2, primeFactors := [2, 3, 1381] }, .lucas { root := 2, primeFactors := [2, 3, 5, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 11, 661] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 13, 47, 179] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 29, 607] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 479, 487] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 3889] }, .lucas { root := 11, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19, 41143] }, .lucas { root := 3, primeFactors := [2, 3, 6857] }, .lucas { root := 3, primeFactors := [2, 857] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 13907] }, .lucas { root := 2, primeFactors := [2, 17, 409] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 4021] }, .lucas { root := 2, primeFactors := [2, 3, 5, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 7, 1889] }, .lucas { root := 3, primeFactors := [2, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 6869] }, .lucas { root := 2, primeFactors := [2, 17, 101] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 11, 13, 821] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 31, 149, 179] }]), by simp⟩

@[expose] noncomputable def bankLeaf103 : PrimeBank := .leaf [4966373, 5005129, 5076551, 5077297, 5112661, 5179063, 5187859, 5221123, 5228501, 5229043, 5267459, 5396621, 5426779, 5481409, 5492801, 5505377]

theorem bankLeaf103_valid : bankLeaf103.Certified := by
  simp only [bankLeaf103, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 347, 601] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 101531] }, .lucas { root := 2, primeFactors := [2, 5, 11, 13, 71] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 97, 8971] }, .lucas { root := 2, primeFactors := [2, 3, 5, 13, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 10457] }, .lucas { root := 3, primeFactors := [2, 1307] }, .lucas { root := 2, primeFactors := [2, 653] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 31, 53, 229] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 239, 1129] }, .lucas { root := 11, primeFactors := [2, 3, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 129209] }, .lucas { root := 3, primeFactors := [2, 31, 521] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 28549] }, .lucas { root := 2, primeFactors := [2, 3, 13, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 3433] }, .lucas { root := 5, primeFactors := [2, 3, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 43, 4001] }, .lucas { root := 3, primeFactors := [2, 5] }]), by simp⟩

@[expose] noncomputable def bankLeaf104 : PrimeBank := .leaf [5509073, 5513779, 5558221, 5583869, 5615587, 5687191, 5697487, 5715011, 5786761, 5860177, 5876179, 5885051, 6004651, 6061813, 6142993, 6154111]

theorem bankLeaf104_valid : bankLeaf104.Certified := by
  simp only [bankLeaf104, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 29, 31, 383] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 102107] }, .lucas { root := 2, primeFactors := [2, 19, 2687] }, .lucas { root := 5, primeFactors := [2, 17, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 47, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 53, 26339] }, .lucas { root := 2, primeFactors := [2, 13, 1013] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 29, 2179] }, .lucas { root := 7, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 105509] }, .lucas { root := 2, primeFactors := [2, 13, 2029] }, .lucas { root := 2, primeFactors := [2, 3, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 19, 4297] }, .lucas { root := 5, primeFactors := [2, 3, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 7, 107, 163] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 11, 23, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 117701] }, .lucas { root := 2, primeFactors := [2, 5, 11, 107] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 29, 17419] }, .lucas { root := 3, primeFactors := [2, 3, 2903] }, .lucas { root := 5, primeFactors := [2, 1451] }, .lucas { root := 2, primeFactors := [2, 5, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 127979] }, .lucas { root := 2, primeFactors := [2, 61, 1049] }, .lucas { root := 3, primeFactors := [2, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 23, 991] }]), by simp⟩

@[expose] noncomputable def bankLeaf105 : PrimeBank := .leaf [6157549, 6231037, 6266459, 6267119, 6294091, 6315307, 6335899, 6393083, 6483857, 6550081, 6557479, 6575641, 6578839, 6579701, 6619231, 6621847]

theorem bankLeaf105_valid : bankLeaf105.Certified := by
  simp only [bankLeaf105, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 10597] }, .lucas { root := 5, primeFactors := [2, 3, 883] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 284839] }, .lucas { root := 3, primeFactors := [2, 3, 29, 1637] }, .lucas { root := 2, primeFactors := [2, 409] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 11, 13, 17, 1289] }, .lucas { root := 6, primeFactors := [2, 7, 23] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 71, 107, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 37, 4547] }, .lucas { root := 2, primeFactors := [2, 2273] }, .lucas { root := 3, primeFactors := [2, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 405241] }, .lucas { root := 13, primeFactors := [2, 3, 5, 11, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 6823] }, .lucas { root := 3, primeFactors := [2, 3, 379] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 17, 53, 1213] }, .lucas { root := 2, primeFactors := [2, 3, 101] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf106 : PrimeBank := .leaf [6684907, 6713569, 6726821, 6766399, 6804911, 6883571, 7048567, 7070053, 7086103, 7105807, 7152367, 7221259, 7306771, 7493251, 7515499, 7522609]

theorem bankLeaf106_valid : bankLeaf106.Certified := by
  simp only [bankLeaf106, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 23311] }, .lucas { root := 3, primeFactors := [2, 3, 5, 7, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 179, 1879] }, .lucas { root := 6, primeFactors := [2, 3, 313] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 199, 1889] }, .lucas { root := 3, primeFactors := [2, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 97213] }, .lucas { root := 5, primeFactors := [2, 3, 8101] }, .lucas { root := 6, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 688357] }, .lucas { root := 5, primeFactors := [2, 3, 19121] }, .lucas { root := 6, primeFactors := [2, 5, 239] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 29, 643] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 19, 2819] }, .lucas { root := 2, primeFactors := [2, 1409] }, .lucas { root := 3, primeFactors := [2, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1181017] }, .lucas { root := 5, primeFactors := [2, 3, 47, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 14621] }, .lucas { root := 2, primeFactors := [2, 5, 17, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 47, 1951] }, .lucas { root := 3, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 12157] }, .lucas { root := 2, primeFactors := [2, 3, 1013] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 17, 14327] }, .lucas { root := 5, primeFactors := [2, 13, 19, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 97, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 103, 12161] }, .lucas { root := 3, primeFactors := [2, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 53, 2957] }, .lucas { root := 2, primeFactors := [2, 739] }]), by simp⟩

end OddPerfect.IndexComponent.SizePrimeBank300
