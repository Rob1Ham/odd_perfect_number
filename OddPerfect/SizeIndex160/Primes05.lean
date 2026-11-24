module

public import OddPerfect.SizeIndex160.Primes04
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.IndexComponent.Size160

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def bankLeaf82 : PrimeBank := .leaf [16497763013, 17189128703, 17257690903, 17532337451, 17834829893, 17984053429, 18195851983, 18622065431, 18708531953, 18813315461, 18976925081, 19937168287, 21349285621, 21392848667, 22028903203, 22216443433]

theorem bankLeaf82_valid : bankLeaf82.Certified := by
  simp only [bankLeaf82, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 23, 491, 521, 701] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 37, 232285523] }, .lucas { root := 2, primeFactors := [2, 7, 16591823] }, .lucas { root := 5, primeFactors := [2, 13, 638147] }, .lucas { root := 5, primeFactors := [2, 17, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2876281817] }, .lucas { root := 3, primeFactors := [2, 17, 21149131] }, .lucas { root := 2, primeFactors := [2, 3, 5, 31, 22741] }, .lucas { root := 7, primeFactors := [2, 3, 5, 379] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 251, 1396999] }, .lucas { root := 3, primeFactors := [2, 3, 77611] }, .lucas { root := 2, primeFactors := [2, 3, 5, 13, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 405337043] }, .lucas { root := 2, primeFactors := [2, 11, 18424411] }, .lucas { root := 10, primeFactors := [2, 3, 5, 614147] }, .lucas { root := 2, primeFactors := [2, 13, 23, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 11, 61, 2233489] }, .lucas { root := 7, primeFactors := [2, 3, 19, 31, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11, 617, 829] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 1862206543] }, .lucas { root := 3, primeFactors := [2, 3, 7, 1249, 11833] }, .lucas { root := 7, primeFactors := [2, 3, 13] }, .lucas { root := 5, primeFactors := [2, 3, 17, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 499, 213023] }, .lucas { root := 5, primeFactors := [2, 43, 2477] }, .lucas { root := 2, primeFactors := [2, 619] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 940665773] }, .lucas { root := 2, primeFactors := [2, 2521, 93283] }, .lucas { root := 17, primeFactors := [2, 3, 5, 7] }, .lucas { root := 2, primeFactors := [2, 3, 7, 2221] }, .lucas { root := 2, primeFactors := [2, 3, 5, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 107, 593, 7477] }, .lucas { root := 2, primeFactors := [2, 3, 7, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 474694483] }, .lucas { root := 2, primeFactors := [2, 3, 131, 603937] }, .lucas { root := 5, primeFactors := [2, 3, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 1123, 24373] }, .lucas { root := 2, primeFactors := [2, 3, 11, 17] }, .lucas { root := 7, primeFactors := [2, 3, 677] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 1733, 881743] }, .lucas { root := 2, primeFactors := [2, 433] }, .lucas { root := 5, primeFactors := [2, 3, 223, 659] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 41, 139, 827] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 925685143] }, .lucas { root := 3, primeFactors := [2, 3, 2857, 54001] }, .lucas { root := 11, primeFactors := [2, 3, 7, 17] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]), by simp⟩

@[expose] noncomputable def bankLeaf83 : PrimeBank := .leaf [22224771403, 22299994021, 22718419879, 24675748729, 24750362743, 25297495897, 26136721201, 26677735199, 26873095187, 26991238223, 27144927317, 27799873531, 28070044711, 28971231269, 30891909967, 34147320401]

theorem bankLeaf83_valid : bankLeaf83.Certified := by
  simp only [bankLeaf83, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 67, 55285501] }, .lucas { root := 2, primeFactors := [2, 3, 5, 36857] }, .lucas { root := 3, primeFactors := [2, 17, 271] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 101, 3679867] }, .lucas { root := 3, primeFactors := [2, 3, 204437] }, .lucas { root := 2, primeFactors := [2, 51109] }, .lucas { root := 10, primeFactors := [2, 3, 4259] }, .lucas { root := 2, primeFactors := [2, 2129] }, .lucas { root := 3, primeFactors := [2, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 11, 23, 43, 7103] }, .lucas { root := 5, primeFactors := [2, 53, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 31, primeFactors := [2, 3, 103, 9982099] }, .lucas { root := 2, primeFactors := [2, 3, 7, 227, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 127, 4640113] }, .lucas { root := 15, primeFactors := [2, 3, 23, 467] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1054062329] }, .lucas { root := 3, primeFactors := [2, 11, 661, 18121] }, .lucas { root := 23, primeFactors := [2, 3, 5, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 1193, 18257] }, .lucas { root := 3, primeFactors := [2, 149] }, .lucas { root := 5, primeFactors := [2, 7, 163] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 349, 38220251] }, .lucas { root := 2, primeFactors := [2, 5, 17, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 41, 43, 155539] }, .lucas { root := 2, primeFactors := [2, 3, 8641] }, .lucas { root := 17, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 151, 6874997] }, .lucas { root := 2, primeFactors := [2, 1718749] }, .lucas { root := 2, primeFactors := [2, 3, 47743] }, .lucas { root := 3, primeFactors := [2, 3, 73, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 11239, 46447] }, .lucas { root := 3, primeFactors := [2, 3, 1873] }, .lucas { root := 10, primeFactors := [2, 3, 13] }, .lucas { root := 3, primeFactors := [2, 3, 7741] }, .lucas { root := 7, primeFactors := [2, 3, 5, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 13, 223, 29059] }, .lucas { root := 2, primeFactors := [2, 3, 29, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 935668157] }, .lucas { root := 2, primeFactors := [2, 73, 541, 5923] }, .lucas { root := 2, primeFactors := [2, 3, 7, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 571, 1812061] }, .lucas { root := 7, primeFactors := [2, 3, 5, 10067] }, .lucas { root := 2, primeFactors := [2, 7, 719] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 269, 1321, 14489] }, .lucas { root := 13, primeFactors := [2, 3, 5, 11] }, .lucas { root := 3, primeFactors := [2, 1811] }, .lucas { root := 6, primeFactors := [2, 5, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 85368301] }, .lucas { root := 2, primeFactors := [2, 3, 5, 284561] }, .lucas { root := 3, primeFactors := [2, 5, 3557] }, .lucas { root := 2, primeFactors := [2, 7, 127] }]), by simp⟩

@[expose] noncomputable def bankLeaf84 : PrimeBank := .leaf [35761058621, 38151506317, 39131983229, 39652448401, 43268024731, 44198972119, 46685826619, 47851022071, 48837672001, 48873043253, 49236515971, 49276157093, 50390258557, 51479618587, 52379047267, 53738676221]

theorem bankLeaf84_valid : bankLeaf84.Certified := by
  simp only [bankLeaf84, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 19, 13444007] }, .lucas { root := 5, primeFactors := [2, 23, 97, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 11, 6089, 6781] }, .lucas { root := 3, primeFactors := [2, 761] }, .lucas { root := 2, primeFactors := [2, 3, 5, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 29, 2137, 12143] }, .lucas { root := 10, primeFactors := [2, 3, 89] }, .lucas { root := 10, primeFactors := [2, 13, 467] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 407947] }, .lucas { root := 3, primeFactors := [2, 3, 7, 11, 883] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 103, 2000371] }, .lucas { root := 2, primeFactors := [2, 3, 5, 131, 509] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 37, 9480689] }, .lucas { root := 3, primeFactors := [2, 7, 84649] }, .lucas { root := 13, primeFactors := [2, 3, 3527] }, .lucas { root := 5, primeFactors := [2, 41, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 41, 127, 1009, 1481] }, .lucas { root := 3, primeFactors := [2, 5, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 531678023] }, .lucas { root := 5, primeFactors := [2, 4549, 58439] }, .lucas { root := 6, primeFactors := [2, 3, 379] }, .lucas { root := 17, primeFactors := [2, 61, 479] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 13, 52177] }, .lucas { root := 5, primeFactors := [2, 3, 1087] }, .lucas { root := 3, primeFactors := [2, 3, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 23, 419, 115259] }, .lucas { root := 2, primeFactors := [2, 11, 13, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 1641217199] }, .lucas { root := 13, primeFactors := [2, 113, 7262023] }, .lucas { root := 3, primeFactors := [2, 3, 71, 17047] }, .lucas { root := 3, primeFactors := [2, 3, 947] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 12527, 57847] }, .lucas { root := 5, primeFactors := [2, 6263] }, .lucas { root := 5, primeFactors := [2, 31, 101] }, .lucas { root := 3, primeFactors := [2, 3, 31, 311] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 381744383] }, .lucas { root := 5, primeFactors := [2, 601, 317591] }, .lucas { root := 7, primeFactors := [2, 5, 7, 13, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 17, 45882013] }, .lucas { root := 5, primeFactors := [2, 3, 11, 347591] }, .lucas { root := 19, primeFactors := [2, 5, 34759] }, .lucas { root := 6, primeFactors := [2, 3, 1931] }, .lucas { root := 2, primeFactors := [2, 5, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 31, 61, 97, 523] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 19, 41, 3449209] }, .lucas { root := 17, primeFactors := [2, 3, 7, 419] }]), by simp⟩

@[expose] noncomputable def bankLeaf85 : PrimeBank := .leaf [54864211481, 57788001679, 59458298953, 59954796907, 60180994771, 64175509327, 64745079361, 66010998331, 66933648671, 67495678093, 68659639549, 72211650019, 72381100807, 75450374401, 75619334851, 75755912653]

theorem bankLeaf85_valid : bankLeaf85.Certified := by
  simp only [bankLeaf85, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 13, 107, 691, 1427] }, .lucas { root := 2, primeFactors := [2, 23, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 239, 3663497] }, .lucas { root := 3, primeFactors := [2, 97, 4721] }, .lucas { root := 6, primeFactors := [2, 5, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 190571471] }, .lucas { root := 46, primeFactors := [2, 5, 29, 311, 2113] }, .lucas { root := 5, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 443, 631, 35747] }, .lucas { root := 2, primeFactors := [2, 61, 293] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 23, 2179, 3079] }, .lucas { root := 7, primeFactors := [2, 3, 11] }, .lucas { root := 6, primeFactors := [2, 3, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 18257, 585853] }, .lucas { root := 5, primeFactors := [2, 7, 163] }, .lucas { root := 2, primeFactors := [2, 3, 48821] }, .lucas { root := 2, primeFactors := [2, 5, 2441] }, .lucas { root := 6, primeFactors := [2, 5, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 53, primeFactors := [2, 3, 5, 13, 17, 43, 47, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 19, 709, 18149] }, .lucas { root := 2, primeFactors := [2, 13, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 136599283] }, .lucas { root := 2, primeFactors := [2, 3, 241, 31489] }, .lucas { root := 7, primeFactors := [2, 3, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 37, 50672431] }, .lucas { root := 12, primeFactors := [2, 3, 5, 19, 29633] }, .lucas { root := 3, primeFactors := [2, 463] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 431, 811, 16369] }, .lucas { root := 7, primeFactors := [2, 3, 11, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 109, 1109, 99563] }, .lucas { root := 2, primeFactors := [2, 277] }, .lucas { root := 2, primeFactors := [2, 67, 743] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 307, 1871183] }, .lucas { root := 5, primeFactors := [2, 935591] }, .lucas { root := 13, primeFactors := [2, 5, 93559] }, .lucas { root := 3, primeFactors := [2, 3, 31, 503] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 3929707] }, .lucas { root := 12, primeFactors := [2, 3, 11, 89, 223] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 504128899] }, .lucas { root := 2, primeFactors := [2, 3, 7, 13, 53, 5807] }, .lucas { root := 5, primeFactors := [2, 2903] }, .lucas { root := 5, primeFactors := [2, 1451] }, .lucas { root := 2, primeFactors := [2, 5, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 17, 17683453] }, .lucas { root := 5, primeFactors := [2, 3, 19, 103, 251] }]), by simp⟩

@[expose] noncomputable def bankLeaf86 : PrimeBank := .leaf [78785754721, 84406199767, 84445082503, 86950696619, 87650274787, 90422310721, 90849403261, 95359493521, 107896304231, 112793887499, 113990869481, 116320750621, 116489924189, 116856733421, 117442848251, 117967608271]

theorem bankLeaf86_valid : bankLeaf86.Certified := by
  simp only [bankLeaf86, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 17, 103, 93739] }, .lucas { root := 3, primeFactors := [2, 3, 17, 919] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 643, 3125461] }, .lucas { root := 2, primeFactors := [2, 3, 5, 13, 4007] }, .lucas { root := 5, primeFactors := [2, 2003] }, .lucas { root := 5, primeFactors := [2, 7, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 1279470947] }, .lucas { root := 2, primeFactors := [2, 13, 3785417] }, .lucas { root := 3, primeFactors := [2, 61, 7757] }, .lucas { root := 2, primeFactors := [2, 7, 277] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 41, 167, 251, 617] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 14608379131] }, .lucas { root := 2, primeFactors := [2, 3, 5, 41, 1283, 9257] }, .lucas { root := 2, primeFactors := [2, 641] }, .lucas { root := 3, primeFactors := [2, 13, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 5, 7, 113, 17011] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 11, 19, 43, 71, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 43, 193, 15959] }, .lucas { root := 11, primeFactors := [2, 79, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 11, 13, 149, 38953] }, .lucas { root := 5, primeFactors := [2, 3, 541] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 56396943749] }, .lucas { root := 2, primeFactors := [2, 58237, 242101] }, .lucas { root := 15, primeFactors := [2, 3, 23, 211] }, .lucas { root := 7, primeFactors := [2, 3, 5, 269] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 23, 73, 173, 9811] }, .lucas { root := 3, primeFactors := [2, 3, 5, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 23, 73, 353, 3271] }, .lucas { root := 3, primeFactors := [2, 3, 5, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 2647498277] }, .lucas { root := 2, primeFactors := [2, 29, 227, 3467] }, .lucas { root := 2, primeFactors := [2, 1733] }, .lucas { root := 2, primeFactors := [2, 433] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 7, 23, 36290911] }, .lucas { root := 6, primeFactors := [2, 3, 5, 1209697] }, .lucas { root := 5, primeFactors := [2, 3, 12601] }, .lucas { root := 11, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 13, 59, 1483] }, .lucas { root := 2, primeFactors := [2, 3, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 97, 13512899] }, .lucas { root := 2, primeFactors := [2, 7, 29, 83, 401] }]), by simp⟩

@[expose] noncomputable def bankLeaf87 : PrimeBank := .leaf [120023424751, 124244862031, 125642407351, 128493601339, 129924628343, 134517327349, 135676061629, 136219001651, 138180033157, 143590301611, 151677497137, 152943249629, 154545688753, 171102215257, 172919530897, 173954764363]

theorem bankLeaf87_valid : bankLeaf87.Certified := by
  simp only [bankLeaf87, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 107, 449, 3331] }, .lucas { root := 3, primeFactors := [2, 3, 5, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 349, 1249, 3167] }, .lucas { root := 7, primeFactors := [2, 3, 13] }, .lucas { root := 5, primeFactors := [2, 1583] }, .lucas { root := 5, primeFactors := [2, 7, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 43, 97, 409, 491] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 2207, 9703489] }, .lucas { root := 5, primeFactors := [2, 1103] }, .lucas { root := 5, primeFactors := [2, 19, 29] }, .lucas { root := 7, primeFactors := [2, 3, 50539] }, .lucas { root := 2, primeFactors := [2, 3, 8423] }, .lucas { root := 5, primeFactors := [2, 4211] }, .lucas { root := 6, primeFactors := [2, 5, 421] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 29, 5839, 13229] }, .lucas { root := 6, primeFactors := [2, 3, 7, 139] }, .lucas { root := 2, primeFactors := [2, 3307] }, .lucas { root := 2, primeFactors := [2, 3, 19, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 353, 593, 53551] }, .lucas { root := 3, primeFactors := [2, 3, 5, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 12197, 926977] }, .lucas { root := 2, primeFactors := [2, 3049] }, .lucas { root := 11, primeFactors := [2, 3, 127] }, .lucas { root := 5, primeFactors := [2, 3, 17, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 160257649] }, .lucas { root := 11, primeFactors := [2, 3, 3338701] }, .lucas { root := 2, primeFactors := [2, 3, 5, 31, 359] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 19, 55095707] }, .lucas { root := 2, primeFactors := [2, 19, 79, 18353] }, .lucas { root := 3, primeFactors := [2, 31, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 17, 67, 600319] }, .lucas { root := 3, primeFactors := [2, 3, 11117] }, .lucas { root := 3, primeFactors := [2, 7, 397] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 151, 1902437] }, .lucas { root := 2, primeFactors := [2, 17, 101, 277] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 2941216339] }, .lucas { root := 2, primeFactors := [2, 3, 911, 538093] }, .lucas { root := 5, primeFactors := [2, 3, 14947] }, .lucas { root := 2, primeFactors := [2, 3, 47, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13, 193, 26189] }, .lucas { root := 2, primeFactors := [2, 6547] }, .lucas { root := 2, primeFactors := [2, 3, 1091] }, .lucas { root := 2, primeFactors := [2, 5, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 277, 525253] }, .lucas { root := 2, primeFactors := [2, 3, 7, 13, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 227, 2267143] }, .lucas { root := 5, primeFactors := [2, 3, 79, 4783] }, .lucas { root := 6, primeFactors := [2, 3, 797] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1163, 2543, 9803] }, .lucas { root := 5, primeFactors := [2, 7, 83] }, .lucas { root := 5, primeFactors := [2, 31, 41] }, .lucas { root := 2, primeFactors := [2, 13, 29] }]), by simp⟩

@[expose] noncomputable def bankLeaf88 : PrimeBank := .leaf [175384380151, 184070417581, 186583172059, 187039475551, 189343400041, 193091463181, 195572043853, 201842013691, 206357092717, 207837725713, 232611722621, 237959523803, 239337374873, 247174661801, 254169641233, 266337742171]

theorem bankLeaf88_valid : bankLeaf88.Certified := by
  simp only [bankLeaf88, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 19, 31, 94529] }, .lucas { root := 3, primeFactors := [2, 7, 211] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 41, 733, 4861] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 37, 1327, 70373] }, .lucas { root := 3, primeFactors := [2, 3, 13, 17] }, .lucas { root := 2, primeFactors := [2, 73, 241] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 12041, 34519] }, .lucas { root := 3, primeFactors := [2, 5, 7, 43] }, .lucas { root := 3, primeFactors := [2, 3, 11, 523] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 29, 2015149] }, .lucas { root := 2, primeFactors := [2, 3, 307, 547] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 11, 13931563] }, .lucas { root := 2, primeFactors := [2, 3, 151, 15377] }, .lucas { root := 3, primeFactors := [2, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 47, 5827, 59509] }, .lucas { root := 2, primeFactors := [2, 3, 971] }, .lucas { root := 10, primeFactors := [2, 3, 19, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 137, 119489] }, .lucas { root := 3, primeFactors := [2, 1867] }, .lucas { root := 2, primeFactors := [2, 3, 311] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 347, 49557419] }, .lucas { root := 2, primeFactors := [2, 2939, 8431] }, .lucas { root := 2, primeFactors := [2, 13, 113] }, .lucas { root := 3, primeFactors := [2, 3, 5, 281] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 29, 191, 781721] }, .lucas { root := 3, primeFactors := [2, 5, 19543] }, .lucas { root := 3, primeFactors := [2, 3, 3257] }, .lucas { root := 3, primeFactors := [2, 11, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 389, 3767, 7937] }, .lucas { root := 5, primeFactors := [2, 7, 269] }, .lucas { root := 3, primeFactors := [2, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 11, 13, 43, 2764207] }, .lucas { root := 5, primeFactors := [2, 3, 113, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 107, 279599737] }, .lucas { root := 5, primeFactors := [2, 3, 13, 197, 4549] }, .lucas { root := 6, primeFactors := [2, 3, 379] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 29, 352201] }, .lucas { root := 7, primeFactors := [2, 3, 5, 587] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 13, 677, 66851] }, .lucas { root := 2, primeFactors := [2, 5, 7, 191] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 31, 16846157] }, .lucas { root := 2, primeFactors := [2, 53, 229, 347] }]), by simp⟩

@[expose] noncomputable def bankLeaf89 : PrimeBank := .leaf [284101057787, 290770486991, 320374117039, 327668647153, 332207361361, 365442584509, 372649725281, 386626708057, 386855506153, 386859507301, 416450882401, 441019876741, 455350252171, 465900166691, 480771505499, 487880282891]

theorem bankLeaf89_valid : bankLeaf89.Certified := by
  simp only [bankLeaf89, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 13, 1560994823] }, .lucas { root := 5, primeFactors := [2, 780497411] }, .lucas { root := 6, primeFactors := [2, 5, 7, 11, 23, 44071] }, .lucas { root := 3, primeFactors := [2, 3, 5, 13, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 29077048699] }, .lucas { root := 3, primeFactors := [2, 3, 173, 211, 132761] }, .lucas { root := 3, primeFactors := [2, 5, 3319] }, .lucas { root := 6, primeFactors := [2, 3, 7, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 38011, 1404743] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7, 181] }, .lucas { root := 5, primeFactors := [2, 37, 41, 463] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 11, 12664991] }, .lucas { root := 11, primeFactors := [2, 5, 13, 97423] }, .lucas { root := 3, primeFactors := [2, 3, 13, 1249] }, .lucas { root := 7, primeFactors := [2, 3, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 23, 293, 9781] }, .lucas { root := 6, primeFactors := [2, 3, 5, 163] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 31, 43, 317, 24023] }, .lucas { root := 5, primeFactors := [2, 12011] }, .lucas { root := 2, primeFactors := [2, 5, 1201] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 31, 71, 151169] }, .lucas { root := 3, primeFactors := [2, 1181] }, .lucas { root := 7, primeFactors := [2, 5, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 23, 37, 43, 193, 2281] }, .lucas { root := 7, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 47, 7487, 15269] }, .lucas { root := 5, primeFactors := [2, 19, 197] }, .lucas { root := 2, primeFactors := [2, 11, 347] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 5, 7, 19, 359101] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 41, primeFactors := [2, 3, 5, 7, 3541249] }, .lucas { root := 7, primeFactors := [2, 3, 29, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 19, 67, 5774023] }, .lucas { root := 5, primeFactors := [2, 3, 97, 3307] }, .lucas { root := 2, primeFactors := [2, 3, 19, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 5813, 237373] }, .lucas { root := 2, primeFactors := [2, 1453] }, .lucas { root := 2, primeFactors := [2, 3, 11] }, .lucas { root := 2, primeFactors := [2, 3, 131, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 1123, 5926729] }, .lucas { root := 2, primeFactors := [2, 3, 11, 17] }, .lucas { root := 11, primeFactors := [2, 3, 246947] }, .lucas { root := 2, primeFactors := [2, 7, 31, 569] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 43, 328845079] }, .lucas { root := 3, primeFactors := [2, 3, 2917, 6263] }, .lucas { root := 5, primeFactors := [2, 3] }, .lucas { root := 5, primeFactors := [2, 31, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 11, 13, 17, 2867017] }, .lucas { root := 5, primeFactors := [2, 3, 17, 7027] }, .lucas { root := 2, primeFactors := [2, 3, 1171] }, .lucas { root := 2, primeFactors := [2, 3, 5, 13] }]), by simp⟩

@[expose] noncomputable def bankLeaf90 : PrimeBank := .leaf [495676706311, 498223764019, 508821419651, 521177973661, 528515019661, 529187865131, 562731116179, 565349006711, 583826053231, 586297360433, 633337333201, 642370334407, 705670360649, 734262067271, 735349796563, 738389740637]

theorem bankLeaf90_valid : bankLeaf90.Certified := by
  simp only [bankLeaf90, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 907, 674693] }, .lucas { root := 2, primeFactors := [2, 168673] }, .lucas { root := 5, primeFactors := [2, 3, 7, 251] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 135841, 203761] }, .lucas { root := 7, primeFactors := [2, 3, 5, 283] }, .lucas { root := 11, primeFactors := [2, 3, 5, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 83, 122607571] }, .lucas { root := 2, primeFactors := [2, 3, 5, 17, 19, 12653] }, .lucas { root := 2, primeFactors := [2, 3163] }, .lucas { root := 3, primeFactors := [2, 3, 17, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37, 79, 751, 1319] }, .lucas { root := 13, primeFactors := [2, 659] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 79, 739, 150881] }, .lucas { root := 6, primeFactors := [2, 5, 23, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 141499, 373987] }, .lucas { root := 13, primeFactors := [2, 3, 7, 1123] }, .lucas { root := 2, primeFactors := [2, 3, 11, 17] }, .lucas { root := 2, primeFactors := [2, 3, 79, 263] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11, 83, 1193, 12301] }, .lucas { root := 3, primeFactors := [2, 149] }, .lucas { root := 2, primeFactors := [2, 3, 5, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 463, 122105617] }, .lucas { root := 10, primeFactors := [2, 3, 83, 30649] }, .lucas { root := 7, primeFactors := [2, 3, 1277] }, .lucas { root := 2, primeFactors := [2, 11, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 7, 29, 53, 67, 8999] }, .lucas { root := 7, primeFactors := [2, 11, 409] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 23, 4157, 54751] }, .lucas { root := 2, primeFactors := [2, 1039] }, .lucas { root := 3, primeFactors := [2, 3, 173] }, .lucas { root := 6, primeFactors := [2, 3, 5, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 11, 13, 257, 4787] }, .lucas { root := 2, primeFactors := [2, 2393] }, .lucas { root := 3, primeFactors := [2, 13, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 73, 277, 5294581] }, .lucas { root := 10, primeFactors := [2, 3, 5, 79, 1117] }, .lucas { root := 2, primeFactors := [2, 3, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 29, 61, 4533059] }, .lucas { root := 2, primeFactors := [2, 19, 119291] }, .lucas { root := 2, primeFactors := [2, 5, 79, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 5, 17, 29, 61, 2441599] }, .lucas { root := 3, primeFactors := [2, 3, 229, 1777] }, .lucas { root := 5, primeFactors := [2, 3, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 37, 157, 1241059] }, .lucas { root := 2, primeFactors := [2, 3, 7, 13, 2273] }, .lucas { root := 3, primeFactors := [2, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 109, 33647, 50333] }, .lucas { root := 5, primeFactors := [2, 16823] }, .lucas { root := 5, primeFactors := [2, 13, 647] }, .lucas { root := 2, primeFactors := [2, 12583] }, .lucas { root := 5, primeFactors := [2, 3, 233] }]), by simp⟩

@[expose] noncomputable def bankLeaf91 : PrimeBank := .leaf [790579404481, 836561914831, 840139875599, 852460489981, 862459400731, 883519833247, 934415109937, 939372759037, 959675633479, 960563556131, 985698269197, 987900542491, 1037517185381, 1047550721851, 1335495402823, 1394813567261]

theorem bankLeaf91_valid : bankLeaf91.Certified := by
  simp only [bankLeaf91, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 521, 1580653] }, .lucas { root := 5, primeFactors := [2, 3, 23, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 9295132387] }, .lucas { root := 3, primeFactors := [2, 3, 19, 41, 1988689] }, .lucas { root := 11, primeFactors := [2, 3, 13, 3187] }, .lucas { root := 2, primeFactors := [2, 3, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 41, 53, 5861, 32983] }, .lucas { root := 3, primeFactors := [2, 5, 293] }, .lucas { root := 3, primeFactors := [2, 3, 23, 239] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 2423, 6581] }, .lucas { root := 5, primeFactors := [2, 7, 173] }, .lucas { root := 14, primeFactors := [2, 5, 7, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 251, 114536441] }, .lucas { root := 3, primeFactors := [2, 5, 199, 14389] }, .lucas { root := 2, primeFactors := [2, 3, 11, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 25633, 5744677] }, .lucas { root := 5, primeFactors := [2, 3, 89] }, .lucas { root := 2, primeFactors := [2, 3, 7, 68389] }, .lucas { root := 2, primeFactors := [2, 3, 41, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 7, 11, 43, 151, 12979] }, .lucas { root := 2, primeFactors := [2, 3, 7, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1439, 2014801] }, .lucas { root := 7, primeFactors := [2, 719] }, .lucas { root := 14, primeFactors := [2, 3, 5, 23, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 71, 107, 379, 18517] }, .lucas { root := 6, primeFactors := [2, 3, 1543] }, .lucas { root := 5, primeFactors := [2, 3, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 131, 367, 1997969] }, .lucas { root := 3, primeFactors := [2, 7, 17839] }, .lucas { root := 6, primeFactors := [2, 3, 991] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 82141522433] }, .lucas { root := 3, primeFactors := [2, 2447, 65563] }, .lucas { root := 5, primeFactors := [2, 1223] }, .lucas { root := 5, primeFactors := [2, 13, 47] }, .lucas { root := 3, primeFactors := [2, 3, 7, 223] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 101, 326039783] }, .lucas { root := 5, primeFactors := [2, 37, 53, 59, 1409] }, .lucas { root := 3, primeFactors := [2, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 13, 101, 1009, 39157] }, .lucas { root := 6, primeFactors := [2, 3, 13, 251] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 821, 2835433] }, .lucas { root := 5, primeFactors := [2, 3, 13127] }, .lucas { root := 5, primeFactors := [2, 6563] }, .lucas { root := 5, primeFactors := [2, 17, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 23, 13903, 99439] }, .lucas { root := 3, primeFactors := [2, 3, 7, 331] }, .lucas { root := 3, primeFactors := [2, 3, 16573] }, .lucas { root := 2, primeFactors := [2, 3, 1381] }, .lucas { root := 2, primeFactors := [2, 3, 5, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 37, 43, 79, 229, 2423] }, .lucas { root := 5, primeFactors := [2, 7, 173] }]), by simp⟩

@[expose] noncomputable def bankLeaf92 : PrimeBank := .leaf [1486680579049, 1552757273887, 1553418542761, 1653850268201, 1670048579431, 1691797368341, 1701208466821, 1780754182741, 1781434578409, 1811827857061, 1824910918879, 1861441475983, 1900421426047, 1957650063931, 1978111754051, 2033125998091]

theorem bankLeaf92_valid : bankLeaf92.Certified := by
  simp only [bankLeaf92, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 41, 1399, 154279] }, .lucas { root := 13, primeFactors := [2, 3, 233] }, .lucas { root := 3, primeFactors := [2, 3, 2857] }, .lucas { root := 11, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 13, 2953, 963047] }, .lucas { root := 13, primeFactors := [2, 3, 41] }, .lucas { root := 5, primeFactors := [2, 7, 31, 317] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 137, 1928371] }, .lucas { root := 3, primeFactors := [2, 3, 5, 64279] }, .lucas { root := 29, primeFactors := [2, 3, 3571] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13, 23, 27656359] }, .lucas { root := 3, primeFactors := [2, 3, 4609393] }, .lucas { root := 5, primeFactors := [2, 3, 109, 881] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 11, 11475631] }, .lucas { root := 3, primeFactors := [2, 3, 5, 127507] }, .lucas { root := 19, primeFactors := [2, 3, 79, 269] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 84589868417] }, .lucas { root := 3, primeFactors := [2, 809, 816883] }, .lucas { root := 5, primeFactors := [2, 3, 11, 12377] }, .lucas { root := 6, primeFactors := [2, 7, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 347, 4813, 5659] }, .lucas { root := 2, primeFactors := [2, 3, 401] }, .lucas { root := 2, primeFactors := [2, 3, 23, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 13, 439, 192611] }, .lucas { root := 18, primeFactors := [2, 5, 11, 17, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 829, 89537323] }, .lucas { root := 3, primeFactors := [2, 3, 7, 599, 3559] }, .lucas { root := 3, primeFactors := [2, 3, 593] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 23, 33664583] }, .lucas { root := 5, primeFactors := [2, 7, 2404613] }, .lucas { root := 2, primeFactors := [2, 7, 157, 547] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 127, 2394896219] }, .lucas { root := 6, primeFactors := [2, 11, 13, 79, 105997] }, .lucas { root := 5, primeFactors := [2, 3, 11, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 1553, 18160759] }, .lucas { root := 3, primeFactors := [2, 97] }, .lucas { root := 3, primeFactors := [2, 3, 7, 11, 13103] }, .lucas { root := 5, primeFactors := [2, 6551] }, .lucas { root := 17, primeFactors := [2, 5, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 13, 5881, 376627] }, .lucas { root := 31, primeFactors := [2, 3, 5, 7] }, .lucas { root := 2, primeFactors := [2, 3, 41, 1531] }, .lucas { root := 2, primeFactors := [2, 3, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 107, 1129, 16369] }, .lucas { root := 11, primeFactors := [2, 3, 47] }, .lucas { root := 7, primeFactors := [2, 3, 11, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 19, 3257, 639307] }, .lucas { root := 3, primeFactors := [2, 11, 37] }, .lucas { root := 2, primeFactors := [2, 3, 11839] }, .lucas { root := 3, primeFactors := [2, 3, 1973] }, .lucas { root := 2, primeFactors := [2, 17, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11, 1459, 4222747] }, .lucas { root := 3, primeFactors := [2, 3] }, .lucas { root := 3, primeFactors := [2, 3, 11, 7109] }, .lucas { root := 2, primeFactors := [2, 1777] }, .lucas { root := 5, primeFactors := [2, 3, 37] }]), by simp⟩

@[expose] noncomputable def bankLeaf93 : PrimeBank := .leaf [2049790620979, 2158316902961, 2168798562241, 2190130430567, 2202194614231, 2223673948273, 2246354414917, 2277499309493, 2317501006871, 2344750835831, 2357622555649, 2365788922631, 2387363771591, 2485641399781, 2521087073569, 2585122674619]

theorem bankLeaf93_valid : bankLeaf93.Certified := by
  simp only [bankLeaf93, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 43051, 2645171] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7, 41] }, .lucas { root := 2, primeFactors := [2, 5, 11, 139, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 71999, 374713] }, .lucas { root := 7, primeFactors := [2, 35999] }, .lucas { root := 13, primeFactors := [2, 41, 439] }, .lucas { root := 5, primeFactors := [2, 3, 13, 1201] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 2259165169] }, .lucas { root := 11, primeFactors := [2, 3, 13, 47, 317] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 17, 4955046223] }, .lucas { root := 3, primeFactors := [2, 3, 7, 3559, 33149] }, .lucas { root := 3, primeFactors := [2, 3, 593] }, .lucas { root := 2, primeFactors := [2, 8287] }, .lucas { root := 3, primeFactors := [2, 3, 1381] }, .lucas { root := 2, primeFactors := [2, 3, 5, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 13, 73, 2864867] }, .lucas { root := 2, primeFactors := [2, 127, 11279] }, .lucas { root := 7, primeFactors := [2, 5639] }, .lucas { root := 7, primeFactors := [2, 2819] }, .lucas { root := 2, primeFactors := [2, 1409] }, .lucas { root := 3, primeFactors := [2, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 1409, 4697003] }, .lucas { root := 3, primeFactors := [2, 11] }, .lucas { root := 2, primeFactors := [2, 37, 63473] }, .lucas { root := 3, primeFactors := [2, 3967] }, .lucas { root := 6, primeFactors := [2, 3, 661] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 241, 439, 1769357] }, .lucas { root := 2, primeFactors := [2, 19, 31, 751] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 29, 1784874067] }, .lucas { root := 2, primeFactors := [2, 3, 297479011] }, .lucas { root := 10, primeFactors := [2, 3, 5, 19, 23, 22691] }, .lucas { root := 2, primeFactors := [2, 5, 2269] }, .lucas { root := 2, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 157, 210873613] }, .lucas { root := 2, primeFactors := [2, 3, 17572801] }, .lucas { root := 23, primeFactors := [2, 3, 5, 7, 523] }]),
    by primality (cert := .witnesses [.lucas { root := 29, primeFactors := [2, 5, 13, 397, 45432103] }, .lucas { root := 13, primeFactors := [2, 3, 113, 593] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 17, 71, 635837] }, .lucas { root := 2, primeFactors := [2, 158959] }, .lucas { root := 3, primeFactors := [2, 3, 8831] }, .lucas { root := 7, primeFactors := [2, 5, 883] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 569, 59397161] }, .lucas { root := 3, primeFactors := [2, 5, 1484929] }, .lucas { root := 7, primeFactors := [2, 3, 1289] }, .lucas { root := 6, primeFactors := [2, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 162973, 209269] }, .lucas { root := 2, primeFactors := [2, 3, 503] }, .lucas { root := 2, primeFactors := [2, 3, 5813] }, .lucas { root := 2, primeFactors := [2, 1453] }, .lucas { root := 2, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 11, 538017619] }, .lucas { root := 2, primeFactors := [2, 3, 6379, 14057] }, .lucas { root := 2, primeFactors := [2, 3, 1063] }, .lucas { root := 3, primeFactors := [2, 3, 59] }, .lucas { root := 3, primeFactors := [2, 7, 251] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 7, 61, 20500643] }, .lucas { root := 2, primeFactors := [2, 1061, 9661] }, .lucas { root := 2, primeFactors := [2, 5, 53] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 39168525373] }, .lucas { root := 11, primeFactors := [2, 3, 23, 141914947] }, .lucas { root := 2, primeFactors := [2, 3, 17, 1391323] }, .lucas { root := 2, primeFactors := [2, 3, 67, 3461] }, .lucas { root := 2, primeFactors := [2, 5, 173] }]), by simp⟩

end OddPerfect.IndexComponent.Size160
