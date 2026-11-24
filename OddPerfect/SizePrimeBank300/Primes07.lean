module

public import OddPerfect.SizePrimeBank300.Primes06
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.IndexComponent.SizePrimeBank300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def bankLeaf124 : PrimeBank := .leaf [39649021, 39773329, 39987067, 39987851, 40260089, 40489321, 40606039, 40684711, 40935743, 41231471, 41408911, 41423623, 41472199, 41808163, 42168367, 42232441]

theorem bankLeaf124_valid : bankLeaf124.Certified := by
  simp only [bankLeaf124, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 660817] }, .lucas { root := 5, primeFactors := [2, 3, 13, 353] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 118373] }, .lucas { root := 2, primeFactors := [2, 101, 293] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 43, 2657] }, .lucas { root := 3, primeFactors := [2, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 19, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 337411] }, .lucas { root := 7, primeFactors := [2, 3, 5, 23, 163] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 11, 205081] }, .lucas { root := 11, primeFactors := [2, 3, 5, 1709] }, .lucas { root := 3, primeFactors := [2, 7, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 11, 31, 41, 97] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 589021] }, .lucas { root := 6, primeFactors := [2, 3, 5, 9817] }, .lucas { root := 5, primeFactors := [2, 3, 409] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 460099] }, .lucas { root := 10, primeFactors := [2, 3, 25561] }, .lucas { root := 11, primeFactors := [2, 3, 5, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 6903937] }, .lucas { root := 5, primeFactors := [2, 3, 13, 461] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2304011] }, .lucas { root := 2, primeFactors := [2, 5, 17, 13553] }, .lucas { root := 3, primeFactors := [2, 7, 11] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 2342687] }, .lucas { root := 5, primeFactors := [2, 1171343] }, .lucas { root := 5, primeFactors := [2, 585671] }, .lucas { root := 7, primeFactors := [2, 5, 58567] }, .lucas { root := 6, primeFactors := [2, 3, 43, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 19, 18523] }, .lucas { root := 3, primeFactors := [2, 3, 7] }]), by simp⟩

@[expose] noncomputable def bankLeaf125 : PrimeBank := .leaf [42441037, 42595031, 42945667, 43038337, 43355341, 43863971, 44049389, 44611351, 45025709, 45058231, 45119171, 45175567, 45427579, 45437789, 45661019, 46012163]

theorem bankLeaf125_valid : bankLeaf125.Certified := by
  simp only [bankLeaf125, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 29, 11087] }, .lucas { root := 5, primeFactors := [2, 23, 241] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 17, 71, 3529] }, .lucas { root := 17, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7157611] }, .lucas { root := 2, primeFactors := [2, 3, 5, 67, 1187] }, .lucas { root := 2, primeFactors := [2, 593] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 19, 1811] }, .lucas { root := 6, primeFactors := [2, 5, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 19, 230863] }, .lucas { root := 3, primeFactors := [2, 3, 109, 353] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 31, 37, 9601] }, .lucas { root := 13, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 42487] }, .lucas { root := 5, primeFactors := [2, 3, 73, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 13, 41, 431] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 37, 1933] }, .lucas { root := 5, primeFactors := [2, 3, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 4511917] }, .lucas { root := 5, primeFactors := [2, 3, 41777] }, .lucas { root := 3, primeFactors := [2, 7, 373] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7529261] }, .lucas { root := 2, primeFactors := [2, 5, 376463] }, .lucas { root := 5, primeFactors := [2, 41, 4591] }, .lucas { root := 11, primeFactors := [2, 3, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 7, 101, 10709] }, .lucas { root := 2, primeFactors := [2, 2677] }, .lucas { root := 2, primeFactors := [2, 3, 223] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 709, 2477] }, .lucas { root := 2, primeFactors := [2, 619] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 53, 62011] }, .lucas { root := 2, primeFactors := [2, 3, 5, 13, 53] }]), by simp⟩

@[expose] noncomputable def bankLeaf126 : PrimeBank := .leaf [46101931, 46606997, 47183809, 47206363, 47343671, 47462563, 47650987, 47783893, 48063373, 48071041, 48552947, 48797669, 49627843, 49722523, 49936897, 50062963]

theorem bankLeaf126_valid : bankLeaf126.Certified := by
  simp only [bankLeaf126, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 219533] }, .lucas { root := 2, primeFactors := [2, 71, 773] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 41, 73, 229] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 35107] }, .lucas { root := 2, primeFactors := [2, 3, 5851] }, .lucas { root := 2, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 1123961] }, .lucas { root := 3, primeFactors := [2, 5, 28099] }, .lucas { root := 2, primeFactors := [2, 3, 7, 223] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 11, 3557] }, .lucas { root := 2, primeFactors := [2, 7, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 376687] }, .lucas { root := 3, primeFactors := [2, 3, 17, 1231] }, .lucas { root := 3, primeFactors := [2, 3, 5, 41] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 572183] }, .lucas { root := 5, primeFactors := [2, 13, 59, 373] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 79, 154423] }, .lucas { root := 5, primeFactors := [2, 3, 23, 373] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf127 : PrimeBank := .leaf [50408381, 50559653, 51025717, 51360941, 52461511, 52739779, 52757797, 52758703, 52956313, 53046457, 53306107, 53405081, 53543431, 55067041, 55433533, 55849049]

theorem bankLeaf127_valid : bankLeaf127.Certified := by
  simp only [bankLeaf127, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 13, 157, 563] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 19, 10657] }, .lucas { root := 7, primeFactors := [2, 3, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1277, 2011] }, .lucas { root := 2, primeFactors := [2, 11, 29] }, .lucas { root := 3, primeFactors := [2, 3, 5, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 251, 6967] }, .lucas { root := 5, primeFactors := [2, 3, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 13799] }, .lucas { root := 7, primeFactors := [2, 6899] }, .lucas { root := 2, primeFactors := [2, 3449] }, .lucas { root := 3, primeFactors := [2, 431] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 13, 48313] }, .lucas { root := 5, primeFactors := [2, 3, 11, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 108557] }, .lucas { root := 2, primeFactors := [2, 7, 3877] }, .lucas { root := 2, primeFactors := [2, 3, 17, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 2206513] }, .lucas { root := 5, primeFactors := [2, 3, 7, 11, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 31, 37, 41, 47] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 23, 58049] }, .lucas { root := 3, primeFactors := [2, 907] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 66103] }, .lucas { root := 3, primeFactors := [2, 3, 23, 479] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7, 607] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 7, 11, 17, 3529] }, .lucas { root := 17, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 641, 10891] }, .lucas { root := 2, primeFactors := [2, 3, 5, 11] }]), by simp⟩

@[expose] noncomputable def bankLeaf128 : PrimeBank := .leaf [56094673, 56441899, 57344741, 57627421, 58530379, 59265571, 59501891, 59503651, 60025093, 60476569, 60571603, 61397681, 61511921, 61562537, 62060021, 62144713]

theorem bankLeaf128_valid : bankLeaf128.Certified := by
  simp only [bankLeaf128, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1168639] }, .lucas { root := 3, primeFactors := [2, 3, 31, 61, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 3135661] }, .lucas { root := 2, primeFactors := [2, 3, 5, 11, 4751] }, .lucas { root := 19, primeFactors := [2, 5, 19] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 23, 41759] }, .lucas { root := 7, primeFactors := [2, 20879] }, .lucas { root := 11, primeFactors := [2, 11, 13, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 73, 133631] }, .lucas { root := 7, primeFactors := [2, 5, 7, 23, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 13, 17, 1277] }, .lucas { root := 2, primeFactors := [2, 11, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 850027] }, .lucas { root := 3, primeFactors := [2, 3, 141671] }, .lucas { root := 17, primeFactors := [2, 5, 31, 457] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 337, 14843] }, .lucas { root := 2, primeFactors := [2, 41, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 23, 89, 1231] }, .lucas { root := 3, primeFactors := [2, 3, 5, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 13, 36979] }, .lucas { root := 3, primeFactors := [2, 3, 6163] }, .lucas { root := 3, primeFactors := [2, 3, 13, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 767471] }, .lucas { root := 11, primeFactors := [2, 5, 11, 6977] }, .lucas { root := 3, primeFactors := [2, 109] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 23, 47797] }, .lucas { root := 5, primeFactors := [2, 3, 7, 569] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 23, 1787] }, .lucas { root := 2, primeFactors := [2, 19, 47] }]), by simp⟩

@[expose] noncomputable def bankLeaf129 : PrimeBank := .leaf [62478139, 62563099, 63284371, 63799247, 63810001, 64050113, 64072051, 64124773, 64506331, 64525231, 66333529, 67444067, 67917427, 68392523, 68639539, 68678651]

theorem bankLeaf129_valid : bankLeaf129.Certified := by
  simp only [bankLeaf129, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 431, 1861] }, .lucas { root := 2, primeFactors := [2, 3, 5, 31] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 7, 29, 157141] }, .lucas { root := 2, primeFactors := [2, 3, 5, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 709] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 142969] }, .lucas { root := 11, primeFactors := [2, 3, 7, 23, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 139, 439] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 281249] }, .lucas { root := 3, primeFactors := [2, 11, 17, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 17, 19, 317] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 11, 9311] }, .lucas { root := 7, primeFactors := [2, 5, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 53, 17383] }, .lucas { root := 5, primeFactors := [2, 3, 2897] }, .lucas { root := 3, primeFactors := [2, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 1983649] }, .lucas { root := 11, primeFactors := [2, 3, 20663] }, .lucas { root := 5, primeFactors := [2, 10331] }, .lucas { root := 2, primeFactors := [2, 5, 1033] }, .lucas { root := 5, primeFactors := [2, 3, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11319571] }, .lucas { root := 7, primeFactors := [2, 3, 5, 29, 4337] }, .lucas { root := 3, primeFactors := [2, 271] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 3108751] }, .lucas { root := 3, primeFactors := [2, 3, 5, 829] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 59, 17627] }, .lucas { root := 2, primeFactors := [2, 7, 1259] }, .lucas { root := 2, primeFactors := [2, 17, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 79, 17387] }, .lucas { root := 2, primeFactors := [2, 8693] }, .lucas { root := 2, primeFactors := [2, 41, 53] }]), by simp⟩

@[expose] noncomputable def bankLeaf130 : PrimeBank := .leaf [68753227, 69153869, 69655517, 69662533, 70065607, 70414451, 70911041, 71497889, 72090103, 72185651, 72568031, 72598579, 73111721, 74739449, 76066181, 77572057]

theorem bankLeaf130_valid : bankLeaf130.Certified := by
  simp only [bankLeaf130, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 31, 79, 4679] }, .lucas { root := 11, primeFactors := [2, 2339] }, .lucas { root := 2, primeFactors := [2, 7, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 2469781] }, .lucas { root := 10, primeFactors := [2, 3, 5, 13721] }, .lucas { root := 3, primeFactors := [2, 5, 7] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 313, 1091] }, .lucas { root := 2, primeFactors := [2, 5, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 89, 10093] }, .lucas { root := 2, primeFactors := [2, 3, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 1408289] }, .lucas { root := 3, primeFactors := [2, 7, 6287] }, .lucas { root := 7, primeFactors := [2, 7, 449] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 7, 11, 29017] }, .lucas { root := 5, primeFactors := [2, 3, 13, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 43, 179, 223] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1443713] }, .lucas { root := 3, primeFactors := [2, 11279] }, .lucas { root := 7, primeFactors := [2, 5639] }, .lucas { root := 7, primeFactors := [2, 2819] }, .lucas { root := 2, primeFactors := [2, 1409] }, .lucas { root := 3, primeFactors := [2, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 19, 381937] }, .lucas { root := 5, primeFactors := [2, 3, 73, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 109, 8539] }, .lucas { root := 2, primeFactors := [2, 3, 1423] }, .lucas { root := 3, primeFactors := [2, 3, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 11, 89, 1867] }, .lucas { root := 2, primeFactors := [2, 3, 311] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 83, 45823] }, .lucas { root := 3, primeFactors := [2, 3, 7, 1091] }, .lucas { root := 2, primeFactors := [2, 5, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 367, 8807] }, .lucas { root := 5, primeFactors := [2, 7, 17, 37] }]), by simp⟩

@[expose] noncomputable def bankLeaf131 : PrimeBank := .leaf [77619973, 78169573, 80556323, 80679541, 81920243, 83323393, 83513081, 83742643, 83774233, 83871721, 83926109, 84253511, 84438671, 85044793, 85232629, 85251739]

theorem bankLeaf131_valid : bankLeaf131.Certified := by
  simp only [bankLeaf131, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 19, 59, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 7, 11, 523093] }, .lucas { root := 2, primeFactors := [2, 3, 43591] }, .lucas { root := 11, primeFactors := [2, 3, 5, 1453] }, .lucas { root := 2, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 79, 17021] }, .lucas { root := 2, primeFactors := [2, 5, 23, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 40960121] }, .lucas { root := 3, primeFactors := [2, 5, 907, 1129] }, .lucas { root := 11, primeFactors := [2, 3, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 3191] }, .lucas { root := 11, primeFactors := [2, 5, 11, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 298261] }, .lucas { root := 6, primeFactors := [2, 3, 5, 1657] }, .lucas { root := 11, primeFactors := [2, 3, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1511, 3079] }, .lucas { root := 11, primeFactors := [2, 5, 151] }, .lucas { root := 6, primeFactors := [2, 3, 19] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 77659] }, .lucas { root := 2, primeFactors := [2, 3, 7, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 2997361] }, .lucas { root := 17, primeFactors := [2, 3, 5, 23, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 11, 179, 389] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 17, 3571] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 11, 13, 67, 1483] }, .lucas { root := 2, primeFactors := [2, 3, 13, 19] }]), by simp⟩

@[expose] noncomputable def bankLeaf132 : PrimeBank := .leaf [85490971, 86524531, 87210971, 87345721, 87683177, 87914143, 88709167, 89218117, 89222701, 91123391, 92110001, 93469471, 93853931, 94111327, 96656723, 97802791]

theorem bankLeaf132_valid : bankLeaf132.Certified := by
  simp only [bankLeaf132, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 2849699] }, .lucas { root := 2, primeFactors := [2, 1424849] }, .lucas { root := 3, primeFactors := [2, 19, 43, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 2884151] }, .lucas { root := 7, primeFactors := [2, 5, 37, 1559] }, .lucas { root := 19, primeFactors := [2, 19, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 11, 53, 2137] }, .lucas { root := 10, primeFactors := [2, 3, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 37, primeFactors := [2, 3, 5, 7, 11, 23, 137] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 23, 212353] }, .lucas { root := 5, primeFactors := [2, 3, 7, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 13, 31, 1747] }, .lucas { root := 2, primeFactors := [2, 3, 97] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 42487] }, .lucas { root := 5, primeFactors := [2, 3, 73, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 9112339] }, .lucas { root := 11, primeFactors := [2, 3, 56249] }, .lucas { root := 3, primeFactors := [2, 79, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 61, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 23, 135463] }, .lucas { root := 3, primeFactors := [2, 3, 107, 211] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 647, 8081] }, .lucas { root := 3, primeFactors := [2, 5, 101] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf133 : PrimeBank := .leaf [100450747, 101285731, 103870649, 104557073, 104631707, 105533191, 105585173, 105878551, 106092913, 109291921, 109491307, 109695889, 110681491, 111327371, 111601811, 113413873]

theorem bankLeaf133_valid : bankLeaf133.Certified := by
  simp only [bankLeaf133, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 263, 643] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 5, 7, 13, 83, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 7, 1854833] }, .lucas { root := 3, primeFactors := [2, 7, 16561] }, .lucas { root := 7, primeFactors := [2, 3, 5, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 17, 269, 1429] }, .lucas { root := 6, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 71, 736843] }, .lucas { root := 2, primeFactors := [2, 3, 227, 541] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 127, 1319] }, .lucas { root := 13, primeFactors := [2, 659] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11, 29, 11821] }, .lucas { root := 2, primeFactors := [2, 3, 5, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 17, 41521] }, .lucas { root := 22, primeFactors := [2, 3, 5, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 31, 37, 41, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 47, 9689] }, .lucas { root := 3, primeFactors := [2, 7, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 18248551] }, .lucas { root := 3, primeFactors := [2, 3, 5, 19, 337] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 761777] }, .lucas { root := 3, primeFactors := [2, 47, 1013] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 53, 151, 461] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 11, 163, 887] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11160181] }, .lucas { root := 11, primeFactors := [2, 3, 5, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11, 13, 31, 41] }]), by simp⟩

@[expose] noncomputable def bankLeaf134 : PrimeBank := .leaf [116084359, 117145891, 119655719, 121617451, 122212901, 123152587, 124861049, 126860821, 127466959, 127473943, 127540261, 127584187, 128691691, 129356767, 129574807, 130154917]

theorem bankLeaf134_valid : bankLeaf134.Certified := by
  simp only [bankLeaf134, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 23, 21569] }, .lucas { root := 3, primeFactors := [2, 337] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 1301621] }, .lucas { root := 2, primeFactors := [2, 5, 151, 431] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 30029] }, .lucas { root := 2, primeFactors := [2, 7507] }, .lucas { root := 2, primeFactors := [2, 3, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1222129] }, .lucas { root := 7, primeFactors := [2, 3, 23, 41] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 101, 11887] }, .lucas { root := 3, primeFactors := [2, 3, 7, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 2114347] }, .lucas { root := 3, primeFactors := [2, 3, 13, 27107] }, .lucas { root := 2, primeFactors := [2, 13553] }, .lucas { root := 3, primeFactors := [2, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1559, 13627] }, .lucas { root := 19, primeFactors := [2, 19, 41] }, .lucas { root := 2, primeFactors := [2, 3, 757] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 43, 99761] }, .lucas { root := 3, primeFactors := [2, 5, 29, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11, 67, 199] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 617, 17579] }, .lucas { root := 2, primeFactors := [2, 11, 17, 47] }]), by simp⟩

@[expose] noncomputable def bankLeaf135 : PrimeBank := .leaf [131194841, 131500009, 132342307, 133333987, 133338869, 136819951, 137819029, 139017523, 140703931, 141437827, 141483161, 148074991, 149391727, 149467631, 149622301, 149854447]

theorem bankLeaf135_valid : bankLeaf135.Certified := by
  simp only [bankLeaf135, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 29, 107, 151] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 61, 229, 1579] }, .lucas { root := 3, primeFactors := [2, 3, 263] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 22222331] }, .lucas { root := 2, primeFactors := [2, 5, 13, 199, 859] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 19, 61, 787] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 311, 36929] }, .lucas { root := 3, primeFactors := [2, 577] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 19, 107, 769] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 873073] }, .lucas { root := 7, primeFactors := [2, 3, 43, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 13, 47, 827] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 705119] }, .lucas { root := 7, primeFactors := [2, 41, 8599] }, .lucas { root := 3, primeFactors := [2, 3, 1433] }, .lucas { root := 3, primeFactors := [2, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 73, 101, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 13, 421, 2731] }, .lucas { root := 3, primeFactors := [2, 3, 5, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 166247] }, .lucas { root := 5, primeFactors := [2, 101, 823] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 71, 2393] }, .lucas { root := 3, primeFactors := [2, 13, 23] }]), by simp⟩

@[expose] noncomputable def bankLeaf136 : PrimeBank := .leaf [149873257, 150332843, 152654153, 154054921, 155042347, 155390881, 157920029, 159807523, 159956351, 162960781, 164184967, 164277469, 164789683, 167017549, 170015941, 170203097]

theorem bankLeaf136_valid : bankLeaf136.Certified := by
  simp only [bankLeaf136, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 109, 113] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 17, 41, 3911] }, .lucas { root := 13, primeFactors := [2, 5, 17, 23] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 17, 137, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 41, 151, 911] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43, 12641] }, .lucas { root := 3, primeFactors := [2, 5, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 3199127] }, .lucas { root := 5, primeFactors := [2, 7, 228509] }, .lucas { root := 2, primeFactors := [2, 7, 8161] }, .lucas { root := 7, primeFactors := [2, 3, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 89, 30517] }, .lucas { root := 2, primeFactors := [2, 3, 2543] }, .lucas { root := 5, primeFactors := [2, 31, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 19, 2297] }, .lucas { root := 5, primeFactors := [2, 7, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 4563263] }, .lucas { root := 5, primeFactors := [2, 11, 31, 6691] }, .lucas { root := 2, primeFactors := [2, 3, 5, 223] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 541, 50767] }, .lucas { root := 5, primeFactors := [2, 3, 8461] }, .lucas { root := 6, primeFactors := [2, 3, 5, 47] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 944533] }, .lucas { root := 2, primeFactors := [2, 3, 26237] }, .lucas { root := 2, primeFactors := [2, 7, 937] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 3039341] }, .lucas { root := 2, primeFactors := [2, 5, 151967] }, .lucas { root := 5, primeFactors := [2, 75983] }, .lucas { root := 5, primeFactors := [2, 37991] }, .lucas { root := 7, primeFactors := [2, 5, 29, 131] }]), by simp⟩

@[expose] noncomputable def bankLeaf137 : PrimeBank := .leaf [171081431, 175924351, 177324031, 177416611, 178192951, 178238491, 182074271, 186049117, 186978817, 186981517, 188576741, 190353643, 190821403, 192062921, 192750517, 193360351]

theorem bankLeaf137_valid : bankLeaf137.Certified := by
  simp only [bankLeaf137, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 13, 173, 7607] }, .lucas { root := 5, primeFactors := [2, 3803] }, .lucas { root := 2, primeFactors := [2, 1901] }, .lucas { root := 2, primeFactors := [2, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 55849] }, .lucas { root := 14, primeFactors := [2, 3, 13, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 31, 4889] }, .lucas { root := 3, primeFactors := [2, 13, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 7, 844841] }, .lucas { root := 6, primeFactors := [2, 5, 21121] }, .lucas { root := 19, primeFactors := [2, 3, 5, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 91381] }, .lucas { root := 17, primeFactors := [2, 3, 5, 1523] }, .lucas { root := 2, primeFactors := [2, 761] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 5941283] }, .lucas { root := 2, primeFactors := [2, 107, 27763] }, .lucas { root := 3, primeFactors := [2, 3, 7, 661] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 193, 13477] }, .lucas { root := 2, primeFactors := [2, 3, 1123] }, .lucas { root := 2, primeFactors := [2, 3, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 23, 619] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 40577] }, .lucas { root := 3, primeFactors := [2, 317] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 5193931] }, .lucas { root := 12, primeFactors := [2, 3, 5, 7, 24733] }, .lucas { root := 2, primeFactors := [2, 3, 229] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 857167] }, .lucas { root := 5, primeFactors := [2, 3, 19, 73, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 107, 479, 619] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 10601189] }, .lucas { root := 2, primeFactors := [2, 13, 203869] }, .lucas { root := 10, primeFactors := [2, 3, 7, 809] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf138 : PrimeBank := .leaf [194086693, 194658851, 201252871, 204245563, 204352781, 206244761, 207326893, 208097431, 208124989, 212237107, 212714461, 215725987, 217138189, 217555099, 217629707, 218992561]

theorem bankLeaf138_valid : bankLeaf138.Certified := by
  simp only [bankLeaf138, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 37, 43, 2447] }, .lucas { root := 5, primeFactors := [2, 1223] }, .lucas { root := 5, primeFactors := [2, 13, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 33, primeFactors := [2, 3, 5, 7, 13, 8191] }, .lucas { root := 17, primeFactors := [2, 3, 5, 7, 13] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 331, 30869] }, .lucas { root := 2, primeFactors := [2, 7717] }, .lucas { root := 2, primeFactors := [2, 3, 643] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 41, 67, 1877] }, .lucas { root := 2, primeFactors := [2, 7, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17277241] }, .lucas { root := 17, primeFactors := [2, 3, 5, 143977] }, .lucas { root := 5, primeFactors := [2, 3, 7, 857] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 37, 67, 751] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 401, 421] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 641, 2671] }, .lucas { root := 7, primeFactors := [2, 3, 5, 89] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 79, 458977] }, .lucas { root := 10, primeFactors := [2, 3, 7, 683] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 137, 113467] }, .lucas { root := 3, primeFactors := [2, 3, 18911] }, .lucas { root := 14, primeFactors := [2, 5, 31, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 912469] }, .lucas { root := 2, primeFactors := [2, 3, 76039] }, .lucas { root := 12, primeFactors := [2, 3, 19, 23, 29] }]), by simp⟩

@[expose] noncomputable def bankLeaf139 : PrimeBank := .leaf [219577381, 221110919, 222678353, 223580911, 226000391, 226818061, 230329301, 232096537, 233464201, 236347801, 237909337, 238465861, 238722443, 240439651, 243677647, 245779361]

theorem bankLeaf139_valid : bankLeaf139.Certified := by
  simp only [bankLeaf139, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 443, 751] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 1070569] }, .lucas { root := 7, primeFactors := [2, 3, 14869] }, .lucas { root := 2, primeFactors := [2, 3, 7, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 1064671] }, .lucas { root := 6, primeFactors := [2, 3, 5, 23, 1543] }, .lucas { root := 5, primeFactors := [2, 3, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 11, 293507] }, .lucas { root := 2, primeFactors := [2, 101, 1453] }, .lucas { root := 2, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 179, 431] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 21929] }, .lucas { root := 3, primeFactors := [2, 2741] }, .lucas { root := 2, primeFactors := [2, 5, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 43, 9049] }, .lucas { root := 7, primeFactors := [2, 3, 13, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 13, 157, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 19, 73, 1021] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 1097, 3623] }, .lucas { root := 3, primeFactors := [2, 137] }, .lucas { root := 5, primeFactors := [2, 1811] }, .lucas { root := 6, primeFactors := [2, 5, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 83, 205441] }, .lucas { root := 13, primeFactors := [2, 3, 5, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 145721] }, .lucas { root := 3, primeFactors := [2, 5, 3643] }, .lucas { root := 2, primeFactors := [2, 3, 607] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 43, 34981] }, .lucas { root := 2, primeFactors := [2, 3, 5, 11, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 1536121] }, .lucas { root := 7, primeFactors := [2, 3, 5, 17, 251] }]), by simp⟩

end OddPerfect.IndexComponent.SizePrimeBank300
