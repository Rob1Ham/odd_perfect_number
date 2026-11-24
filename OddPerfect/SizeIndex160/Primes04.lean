module

public import OddPerfect.SizeIndex160.Primes03
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.IndexComponent.Size160

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def bankLeaf68 : PrimeBank := .leaf [280257881, 280314943, 283575373, 284758421, 295225751, 297903607, 305175781, 309804289, 310897033, 312410911, 316950847, 321703009, 323352761, 329422297, 333530011, 337708039]

theorem bankLeaf68_valid : bankLeaf68.Certified := by
  simp only [bankLeaf68, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 1000921] }, .lucas { root := 7, primeFactors := [2, 3, 5, 19, 439] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 2458903] }, .lucas { root := 3, primeFactors := [2, 3, 409817] }, .lucas { root := 3, primeFactors := [2, 11, 4657] }, .lucas { root := 15, primeFactors := [2, 3, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 173, 5939] }, .lucas { root := 2, primeFactors := [2, 2969] }, .lucas { root := 3, primeFactors := [2, 7, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 14237921] }, .lucas { root := 3, primeFactors := [2, 5, 23, 53, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 1180903] }, .lucas { root := 3, primeFactors := [2, 3, 196817] }, .lucas { root := 3, primeFactors := [2, 12301] }, .lucas { root := 2, primeFactors := [2, 3, 5, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11, 13, 193, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 13, 31, 601] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 403391] }, .lucas { root := 7, primeFactors := [2, 5, 13, 29, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 977, 13259] }, .lucas { root := 6, primeFactors := [2, 7, 947] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 29, 43, 1193] }, .lucas { root := 3, primeFactors := [2, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 4919, 10739] }, .lucas { root := 13, primeFactors := [2, 2459] }, .lucas { root := 2, primeFactors := [2, 1229] }, .lucas { root := 2, primeFactors := [2, 307] }, .lucas { root := 6, primeFactors := [2, 7, 13, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 304643] }, .lucas { root := 2, primeFactors := [2, 13, 11717] }, .lucas { root := 2, primeFactors := [2, 29, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 179, 45161] }, .lucas { root := 3, primeFactors := [2, 5, 1129] }, .lucas { root := 11, primeFactors := [2, 3, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 280121] }, .lucas { root := 3, primeFactors := [2, 5, 47, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 336899] }, .lucas { root := 2, primeFactors := [2, 168449] }, .lucas { root := 3, primeFactors := [2, 7, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 197, 285709] }, .lucas { root := 2, primeFactors := [2, 3, 29, 821] }]), by simp⟩

@[expose] noncomputable def bankLeaf69 : PrimeBank := .leaf [340304407, 344699521, 347419447, 359390389, 369023021, 376939231, 379687663, 383213683, 397403011, 405784411, 412450637, 414810691, 427884607, 446795101, 448408781, 458070961]

theorem bankLeaf69_valid : bankLeaf69.Certified := by
  simp only [bankLeaf69, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 13, 4362877] }, .lucas { root := 2, primeFactors := [2, 3, 7, 29, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 11, 19, 859] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 17, 19, 43, 379] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 29, 43, 47, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 18451151] }, .lucas { root := 11, primeFactors := [2, 5, 369023] }, .lucas { root := 5, primeFactors := [2, 184511] }, .lucas { root := 13, primeFactors := [2, 5, 18451] }, .lucas { root := 3, primeFactors := [2, 3, 5, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 31, 359, 1129] }, .lucas { root := 11, primeFactors := [2, 3, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 29, 80819] }, .lucas { root := 2, primeFactors := [2, 17, 2377] }, .lucas { root := 5, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 227, 93787] }, .lucas { root := 7, primeFactors := [2, 3, 7, 11, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 53, 9257] }, .lucas { root := 3, primeFactors := [2, 13, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 137, 98731] }, .lucas { root := 2, primeFactors := [2, 3, 5, 1097] }, .lucas { root := 3, primeFactors := [2, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 163, 48661] }, .lucas { root := 2, primeFactors := [2, 3, 5, 811] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 31, 63719] }, .lucas { root := 13, primeFactors := [2, 31859] }, .lucas { root := 2, primeFactors := [2, 17, 937] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 880421] }, .lucas { root := 2, primeFactors := [2, 5, 44021] }, .lucas { root := 2, primeFactors := [2, 5, 31, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 496439] }, .lucas { root := 11, primeFactors := [2, 401, 619] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 22420439] }, .lucas { root := 13, primeFactors := [2, 211, 53129] }, .lucas { root := 3, primeFactors := [2, 29, 229] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 61, 67, 467] }]), by simp⟩

@[expose] noncomputable def bankLeaf70 : PrimeBank := .leaf [466344409, 477869921, 478851301, 478880543, 486533891, 518172931, 518323723, 527135461, 549568273, 550413361, 552006661, 556717519, 568801829, 578093647, 596514349, 596578387]

theorem bankLeaf70_valid : bankLeaf70.Certified := by
  simp only [bankLeaf70, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 17, 31, 36871] }, .lucas { root := 15, primeFactors := [2, 3, 5, 1229] }, .lucas { root := 2, primeFactors := [2, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 271517] }, .lucas { root := 2, primeFactors := [2, 7, 9697] }, .lucas { root := 10, primeFactors := [2, 3, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 19, 41, 683] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 34205753] }, .lucas { root := 3, primeFactors := [2, 7, 610817] }, .lucas { root := 3, primeFactors := [2, 1193] }, .lucas { root := 3, primeFactors := [2, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 71, 103, 6653] }, .lucas { root := 2, primeFactors := [2, 1663] }, .lucas { root := 3, primeFactors := [2, 3, 277] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 174469] }, .lucas { root := 10, primeFactors := [2, 3, 7, 31, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 23, 41, 569] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 103, 85297] }, .lucas { root := 15, primeFactors := [2, 3, 1777] }, .lucas { root := 5, primeFactors := [2, 3, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 193, 5393] }, .lucas { root := 3, primeFactors := [2, 337] }]),
    by primality (cert := .witnesses [.lucas { root := 37, primeFactors := [2, 3, 5, 7, 59, 617] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 53, 10211] }, .lucas { root := 6, primeFactors := [2, 5, 1021] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 19, 139, 239] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 20314351] }, .lucas { root := 19, primeFactors := [2, 3, 5, 7, 6449] }, .lucas { root := 3, primeFactors := [2, 13, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 7411457] }, .lucas { root := 3, primeFactors := [2, 13, 17, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 149, 1951] }, .lucas { root := 3, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 99429731] }, .lucas { root := 7, primeFactors := [2, 5, 37, 268729] }, .lucas { root := 7, primeFactors := [2, 3, 11197] }, .lucas { root := 2, primeFactors := [2, 3, 311] }]), by simp⟩

@[expose] noncomputable def bankLeaf71 : PrimeBank := .leaf [599737009, 604799557, 604842197, 606299233, 612928711, 658679743, 684842713, 708196039, 728614573, 730314019, 744221591, 775940419, 817170061, 826632619, 829621381, 834019001]

theorem bankLeaf71_valid : bankLeaf71.Certified := by
  simp only [bankLeaf71, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 13, 961117] }, .lucas { root := 2, primeFactors := [2, 3, 13, 61, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 50399963] }, .lucas { root := 2, primeFactors := [2, 25199981] }, .lucas { root := 2, primeFactors := [2, 5, 13, 103, 941] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 131, 269, 613] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 11, 82021] }, .lucas { root := 22, primeFactors := [2, 3, 5, 1367] }, .lucas { root := 5, primeFactors := [2, 683] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 17, 400607] }, .lucas { root := 5, primeFactors := [2, 29, 6907] }, .lucas { root := 2, primeFactors := [2, 3, 1151] }, .lucas { root := 17, primeFactors := [2, 5, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 1742539] }, .lucas { root := 2, primeFactors := [2, 3, 7, 5927] }, .lucas { root := 5, primeFactors := [2, 2963] }, .lucas { root := 2, primeFactors := [2, 1481] }, .lucas { root := 3, primeFactors := [2, 5, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 71, 401903] }, .lucas { root := 5, primeFactors := [2, 23, 8737] }, .lucas { root := 5, primeFactors := [2, 3, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 1597, 6719] }, .lucas { root := 11, primeFactors := [2, 3, 7, 19] }, .lucas { root := 11, primeFactors := [2, 3359] }, .lucas { root := 11, primeFactors := [2, 23, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 2381, 3643] }, .lucas { root := 3, primeFactors := [2, 5, 7, 17] }, .lucas { root := 2, primeFactors := [2, 3, 607] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 29, 269, 743] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 10631737] }, .lucas { root := 5, primeFactors := [2, 3, 1823] }, .lucas { root := 5, primeFactors := [2, 911] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 17, 43, 1787] }, .lucas { root := 2, primeFactors := [2, 19, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 18, primeFactors := [2, 3, 5, 7, 59, 673] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 1523, 12923] }, .lucas { root := 2, primeFactors := [2, 761] }, .lucas { root := 2, primeFactors := [2, 7, 13, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 31, 63719] }, .lucas { root := 13, primeFactors := [2, 31859] }, .lucas { root := 2, primeFactors := [2, 17, 937] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 89, 9371] }, .lucas { root := 2, primeFactors := [2, 5, 937] }]), by simp⟩

@[expose] noncomputable def bankLeaf72 : PrimeBank := .leaf [843714919, 853390763, 861235321, 875335231, 902418613, 917087137, 938710207, 947239753, 955921051, 989942071, 989955251, 1001523179, 1024823381, 1037358851, 1051706471, 1125924491]

theorem bankLeaf72_valid : bankLeaf72.Certified := by
  simp only [bankLeaf72, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 46873051] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7, 44641] }, .lucas { root := 19, primeFactors := [2, 3, 5, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 8708069] }, .lucas { root := 2, primeFactors := [2, 269, 8093] }, .lucas { root := 2, primeFactors := [2, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 11, 652451] }, .lucas { root := 2, primeFactors := [2, 5, 13049] }, .lucas { root := 3, primeFactors := [2, 7, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 11, 126311] }, .lucas { root := 23, primeFactors := [2, 5, 17, 743] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 47, 1600033] }, .lucas { root := 5, primeFactors := [2, 3, 7, 2381] }, .lucas { root := 3, primeFactors := [2, 5, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 19, 31, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 809, 9209] }, .lucas { root := 3, primeFactors := [2, 1151] }, .lucas { root := 17, primeFactors := [2, 5, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 2663, 14821] }, .lucas { root := 5, primeFactors := [2, 11] }, .lucas { root := 2, primeFactors := [2, 3, 5, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 17, 17851] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 13, 2538313] }, .lucas { root := 5, primeFactors := [2, 3, 7, 29, 521] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 41, 96581] }, .lucas { root := 2, primeFactors := [2, 5, 11, 439] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 23, 29, 37, 103, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 163, 44909] }, .lucas { root := 2, primeFactors := [2, 103, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 1886107] }, .lucas { root := 2, primeFactors := [2, 3, 314351] }, .lucas { root := 7, primeFactors := [2, 5, 6287] }, .lucas { root := 7, primeFactors := [2, 7, 449] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 43, 2445829] }, .lucas { root := 2, primeFactors := [2, 3, 7, 11, 2647] }, .lucas { root := 3, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 2503, 44983] }, .lucas { root := 3, primeFactors := [2, 3, 139] }, .lucas { root := 3, primeFactors := [2, 3, 7, 17] }]), by simp⟩

@[expose] noncomputable def bankLeaf73 : PrimeBank := .leaf [1139535451, 1158061627, 1174989271, 1204720081, 1206193871, 1224116611, 1251279811, 1299754273, 1377020431, 1396830683, 1435874831, 1445413861, 1462507369, 1478526139, 1482570191, 1493913401]

theorem bankLeaf73_valid : bankLeaf73.Certified := by
  simp only [bankLeaf73, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 19, 133279] }, .lucas { root := 3, primeFactors := [2, 3, 97, 229] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 64336757] }, .lucas { root := 2, primeFactors := [2, 11, 1462199] }, .lucas { root := 7, primeFactors := [2, 491, 1489] }, .lucas { root := 14, primeFactors := [2, 3, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 13, 23, 18713] }, .lucas { root := 3, primeFactors := [2, 2339] }, .lucas { root := 2, primeFactors := [2, 7, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 19, 349, 757] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 61, 282481] }, .lucas { root := 28, primeFactors := [2, 3, 5, 11, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 19, 1031, 2083] }, .lucas { root := 14, primeFactors := [2, 5, 103] }, .lucas { root := 2, primeFactors := [2, 3, 347] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 11, 23, 179, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1721, 7867] }, .lucas { root := 3, primeFactors := [2, 5, 43] }, .lucas { root := 3, primeFactors := [2, 3, 19, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 15300227] }, .lucas { root := 2, primeFactors := [2, 29, 151, 1747] }, .lucas { root := 2, primeFactors := [2, 3, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 947, 56731] }, .lucas { root := 2, primeFactors := [2, 3, 5, 31, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 13, 11045191] }, .lucas { root := 6, primeFactors := [2, 3, 5, 13, 127, 223] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 59, 12373] }, .lucas { root := 2, primeFactors := [2, 3, 1031] }, .lucas { root := 14, primeFactors := [2, 5, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 19, 458179] }, .lucas { root := 3, primeFactors := [2, 3, 7, 10909] }, .lucas { root := 2, primeFactors := [2, 3, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 419, 196039] }, .lucas { root := 3, primeFactors := [2, 3, 10891] }, .lucas { root := 2, primeFactors := [2, 3, 5, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 19, 29, 269069] }, .lucas { root := 2, primeFactors := [2, 137, 491] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 409, 2609] }, .lucas { root := 3, primeFactors := [2, 163] }]), by simp⟩

@[expose] noncomputable def bankLeaf74 : PrimeBank := .leaf [1501489387, 1512597319, 1514770111, 1545952267, 1554678533, 1575222931, 1577431459, 1577512711, 1579264051, 1580015219, 1648412281, 1706822489, 1727870509, 1740100459, 1767059981, 1806482129]

theorem bankLeaf74_valid : bankLeaf74.Certified := by
  simp only [bankLeaf74, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 9268453] }, .lucas { root := 2, primeFactors := [2, 3, 85819] }, .lucas { root := 2, primeFactors := [2, 3, 14303] }, .lucas { root := 5, primeFactors := [2, 7151] }, .lucas { root := 7, primeFactors := [2, 5, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 252099553] }, .lucas { root := 10, primeFactors := [2, 3, 29, 83, 1091] }, .lucas { root := 2, primeFactors := [2, 5, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 23, 107, 977] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 85886237] }, .lucas { root := 2, primeFactors := [2, 1249, 17191] }, .lucas { root := 7, primeFactors := [2, 3, 13] }, .lucas { root := 3, primeFactors := [2, 3, 5, 191] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 659, 53617] }, .lucas { root := 5, primeFactors := [2, 3, 1117] }, .lucas { root := 2, primeFactors := [2, 3, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 19, 67, 4583] }, .lucas { root := 5, primeFactors := [2, 29, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 41, 2137441] }, .lucas { root := 7, primeFactors := [2, 3, 5, 61, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 29, 604411] }, .lucas { root := 3, primeFactors := [2, 3, 5, 20147] }, .lucas { root := 6, primeFactors := [2, 7, 1439] }, .lucas { root := 7, primeFactors := [2, 719] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 127, 911] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 37, 733, 29129] }, .lucas { root := 3, primeFactors := [2, 11, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 4578923] }, .lucas { root := 2, primeFactors := [2, 2289461] }, .lucas { root := 2, primeFactors := [2, 5, 114473] }, .lucas { root := 3, primeFactors := [2, 41, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 7, 613, 7103] }, .lucas { root := 5, primeFactors := [2, 53, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 175811] }, .lucas { root := 2, primeFactors := [2, 5, 17581] }, .lucas { root := 10, primeFactors := [2, 3, 5, 293] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 47, 1493, 4133] }, .lucas { root := 2, primeFactors := [2, 373] }, .lucas { root := 2, primeFactors := [2, 1033] }, .lucas { root := 5, primeFactors := [2, 3, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 1783, 7079] }, .lucas { root := 10, primeFactors := [2, 3, 11] }, .lucas { root := 7, primeFactors := [2, 3539] }, .lucas { root := 2, primeFactors := [2, 29, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 89, 115327] }, .lucas { root := 3, primeFactors := [2, 3, 43, 149] }]), by simp⟩

@[expose] noncomputable def bankLeaf75 : PrimeBank := .leaf [1831394497, 1890771811, 1942157131, 1991906923, 2038557977, 2129902711, 2161081063, 2235195191, 2238236249, 2295639937, 2309087647, 2366169307, 2378027611, 2395275511, 2485642321, 2528385577]

theorem bankLeaf75_valid : bankLeaf75.Certified := by
  simp only [bankLeaf75, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 19, 29531] }, .lucas { root := 2, primeFactors := [2, 5, 2953] }, .lucas { root := 13, primeFactors := [2, 3, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 23, 2740249] }, .lucas { root := 11, primeFactors := [2, 3, 7, 5437] }, .lucas { root := 5, primeFactors := [2, 3, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 31, 2088341] }, .lucas { root := 2, primeFactors := [2, 5, 104417] }, .lucas { root := 6, primeFactors := [2, 13, 251] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 31, 701, 15277] }, .lucas { root := 6, primeFactors := [2, 3, 19, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 13, 400031] }, .lucas { root := 7, primeFactors := [2, 5, 109, 367] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 5461289] }, .lucas { root := 3, primeFactors := [2, 7, 97523] }, .lucas { root := 2, primeFactors := [2, 48761] }, .lucas { root := 3, primeFactors := [2, 5, 23, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 131, 130927] }, .lucas { root := 5, primeFactors := [2, 3, 21821] }, .lucas { root := 2, primeFactors := [2, 5, 1091] }, .lucas { root := 2, primeFactors := [2, 5, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 17, 79, 149, 1117] }, .lucas { root := 2, primeFactors := [2, 3, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 41, 6823891] }, .lucas { root := 2, primeFactors := [2, 3, 5, 75821] }, .lucas { root := 2, primeFactors := [2, 5, 17, 223] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 23, 3767] }, .lucas { root := 5, primeFactors := [2, 7, 269] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 8719, 14713] }, .lucas { root := 3, primeFactors := [2, 3, 1453] }, .lucas { root := 2, primeFactors := [2, 3, 11] }, .lucas { root := 5, primeFactors := [2, 3, 613] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 97, 4065583] }, .lucas { root := 3, primeFactors := [2, 3, 19, 1877] }, .lucas { root := 2, primeFactors := [2, 7, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 1877, 2011] }, .lucas { root := 2, primeFactors := [2, 7, 67] }, .lucas { root := 3, primeFactors := [2, 3, 5, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 5, 59, 947, 1429] }, .lucas { root := 6, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 19, 101, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 1667, 63197] }, .lucas { root := 2, primeFactors := [2, 7, 17] }, .lucas { root := 2, primeFactors := [2, 7, 37, 61] }]), by simp⟩

@[expose] noncomputable def bankLeaf76 : PrimeBank := .leaf [2561074343, 2621373511, 2745256771, 2767631689, 2773167361, 2813416783, 3085351051, 3099719989, 3109622749, 3121033931, 3133157107, 3151176557, 3158528101, 3265059751, 3325881113, 3390805279]

theorem bankLeaf76_valid : bankLeaf76.Certified := by
  simp only [bankLeaf76, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 181, 1307, 5413] }, .lucas { root := 2, primeFactors := [2, 653] }, .lucas { root := 5, primeFactors := [2, 3, 11, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 29, 239, 1801] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 23, 31, 179, 239] }]),
    by primality (cert := .witnesses [.lucas { root := 29, primeFactors := [2, 3, 17, 71, 31847] }, .lucas { root := 5, primeFactors := [2, 15923] }, .lucas { root := 2, primeFactors := [2, 19, 419] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 61, 11839] }, .lucas { root := 3, primeFactors := [2, 3, 1973] }, .lucas { root := 2, primeFactors := [2, 17, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 5449, 7823] }, .lucas { root := 7, primeFactors := [2, 3, 227] }, .lucas { root := 5, primeFactors := [2, 3911] }, .lucas { root := 13, primeFactors := [2, 5, 17, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 43, 233, 2053] }, .lucas { root := 2, primeFactors := [2, 3, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 71, 127, 1061] }, .lucas { root := 2, primeFactors := [2, 5, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 259135229] }, .lucas { root := 2, primeFactors := [2, 11, 103, 57179] }, .lucas { root := 2, primeFactors := [2, 11, 23, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 211, 30187] }, .lucas { root := 5, primeFactors := [2, 3, 13, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 41, 553757] }, .lucas { root := 2, primeFactors := [2, 7, 19777] }, .lucas { root := 11, primeFactors := [2, 3, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 71617649] }, .lucas { root := 3, primeFactors := [2, 641, 6983] }, .lucas { root := 5, primeFactors := [2, 3491] }, .lucas { root := 2, primeFactors := [2, 5, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 127, 911] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 19, 229127] }, .lucas { root := 5, primeFactors := [2, 17, 23, 293] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 601, 691739] }, .lucas { root := 2, primeFactors := [2, 345869] }, .lucas { root := 2, primeFactors := [2, 86467] }, .lucas { root := 2, primeFactors := [2, 3, 14411] }, .lucas { root := 2, primeFactors := [2, 5, 11, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 17, 67, 23627] }, .lucas { root := 2, primeFactors := [2, 11813] }, .lucas { root := 2, primeFactors := [2, 2953] }, .lucas { root := 13, primeFactors := [2, 3, 41] }]), by simp⟩

@[expose] noncomputable def bankLeaf77 : PrimeBank := .leaf [3523057633, 3622746821, 3706509671, 3921031339, 3921827683, 3927085741, 3968312611, 4026779377, 4113098237, 4189129561, 4250224747, 4338835663, 4379212381, 4416852373, 4440731591, 4652746649]

theorem bankLeaf77_valid : bankLeaf77.Certified := by
  simp only [bankLeaf77, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1123, 3631] }, .lucas { root := 2, primeFactors := [2, 3, 11, 17] }, .lucas { root := 15, primeFactors := [2, 3, 5, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 11, 2352433] }, .lucas { root := 5, primeFactors := [2, 3, 49009] }, .lucas { root := 19, primeFactors := [2, 3, 1021] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 370650967] }, .lucas { root := 5, primeFactors := [2, 3, 7, 17, 519119] }, .lucas { root := 17, primeFactors := [2, 19, 719] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 93357889] }, .lucas { root := 23, primeFactors := [2, 3, 13, 113, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 331, 6833] }, .lucas { root := 3, primeFactors := [2, 7, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 67, 97, 373] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 132277087] }, .lucas { root := 5, primeFactors := [2, 3, 7348727] }, .lucas { root := 5, primeFactors := [2, 7, 11, 17, 401] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 43, 1950959] }, .lucas { root := 17, primeFactors := [2, 19, 51341] }, .lucas { root := 2, primeFactors := [2, 5, 17, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 79098043] }, .lucas { root := 3, primeFactors := [2, 3, 17, 367, 2113] }, .lucas { root := 5, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 11, 21589] }, .lucas { root := 2, primeFactors := [2, 3, 7, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29, 283, 28771] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 7, 107, 263, 3671] }, .lucas { root := 13, primeFactors := [2, 5, 367] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 72986873] }, .lucas { root := 3, primeFactors := [2, 7, 186191] }, .lucas { root := 13, primeFactors := [2, 5, 43, 433] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 257, 601, 2383] }, .lucas { root := 5, primeFactors := [2, 3, 397] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 444073159] }, .lucas { root := 3, primeFactors := [2, 3, 8223577] }, .lucas { root := 5, primeFactors := [2, 3, 277, 1237] }, .lucas { root := 2, primeFactors := [2, 3, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 631, 83791] }, .lucas { root := 3, primeFactors := [2, 3, 5, 7, 19] }]), by simp⟩

@[expose] noncomputable def bankLeaf78 : PrimeBank := .leaf [4748492087, 4757601581, 4802611441, 5196805069, 5265447391, 5319047759, 5470781959, 5490513541, 5927871379, 6080708173, 6178241683, 6199228913, 6228362269, 6305373793, 6367921363, 6915876949]

theorem bankLeaf78_valid : bankLeaf78.Certified := by
  simp only [bankLeaf78, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 182634311] }, .lucas { root := 13, primeFactors := [2, 5, 18263431] }, .lucas { root := 3, primeFactors := [2, 3, 5, 307, 661] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1787, 133117] }, .lucas { root := 2, primeFactors := [2, 19, 47] }, .lucas { root := 2, primeFactors := [2, 3, 11093] }, .lucas { root := 2, primeFactors := [2, 47, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 29, primeFactors := [2, 3, 5, 11, 263, 6917] }, .lucas { root := 2, primeFactors := [2, 7, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 1567, 3037] }, .lucas { root := 3, primeFactors := [2, 3, 29] }, .lucas { root := 2, primeFactors := [2, 3, 11, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 19, 20947] }, .lucas { root := 3, primeFactors := [2, 3, 3491] }, .lucas { root := 2, primeFactors := [2, 5, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 19, 23, 131, 46457] }, .lucas { root := 3, primeFactors := [2, 5807] }, .lucas { root := 5, primeFactors := [2, 2903] }, .lucas { root := 5, primeFactors := [2, 1451] }, .lucas { root := 2, primeFactors := [2, 5, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 97, 101, 383] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 23, 31, 179, 239] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 11, 13, 531457] }, .lucas { root := 5, primeFactors := [2, 3, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 11, 17, 387109] }, .lucas { root := 2, primeFactors := [2, 3, 10753] }, .lucas { root := 11, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 367, 311749] }, .lucas { root := 6, primeFactors := [2, 3, 83, 313] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 73, 1063, 4993] }, .lucas { root := 3, primeFactors := [2, 3, 59] }, .lucas { root := 5, primeFactors := [2, 3, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 57670021] }, .lucas { root := 11, primeFactors := [2, 3, 5, 320389] }, .lucas { root := 2, primeFactors := [2, 3, 26699] }, .lucas { root := 2, primeFactors := [2, 7, 1907] }, .lucas { root := 2, primeFactors := [2, 953] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 21893659] }, .lucas { root := 3, primeFactors := [2, 3, 3648943] }, .lucas { root := 5, primeFactors := [2, 3, 11, 6143] }, .lucas { root := 5, primeFactors := [2, 37, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 173, 185903] }, .lucas { root := 5, primeFactors := [2, 92951] }, .lucas { root := 11, primeFactors := [2, 5, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 67, 107, 127, 211] }]), by simp⟩

@[expose] noncomputable def bankLeaf79 : PrimeBank := .leaf [7397833357, 7440546193, 7563524537, 7742682019, 7960598843, 8155963183, 8209505981, 8690906729, 8824793797, 9196436593, 9285003751, 9370586851, 9383676751, 10012471081, 10177286401, 10253124001]

theorem bankLeaf79_valid : bankLeaf79.Certified := by
  simp only [bankLeaf79, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 71, 18917] }, .lucas { root := 2, primeFactors := [2, 4729] }, .lucas { root := 17, primeFactors := [2, 3, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 53, 379, 7717] }, .lucas { root := 2, primeFactors := [2, 3, 643] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 17, 55614151] }, .lucas { root := 3, primeFactors := [2, 3, 5, 83, 1489] }, .lucas { root := 14, primeFactors := [2, 3, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 101, 503, 8467] }, .lucas { root := 2, primeFactors := [2, 3, 17, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 568614203] }, .lucas { root := 2, primeFactors := [2, 13, 21869777] }, .lucas { root := 3, primeFactors := [2, 1366861] }, .lucas { root := 6, primeFactors := [2, 3, 5, 11, 19, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 311, 1087, 4021] }, .lucas { root := 3, primeFactors := [2, 3, 181] }, .lucas { root := 2, primeFactors := [2, 3, 5, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13, 37, 47, 67, 271] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 7, 155194763] }, .lucas { root := 2, primeFactors := [2, 97, 127, 6299] }, .lucas { root := 2, primeFactors := [2, 47, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 101, 149, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 7, 1129, 8081] }, .lucas { root := 11, primeFactors := [2, 3, 47] }, .lucas { root := 3, primeFactors := [2, 5, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11, 31, 53, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 1721, 36299] }, .lucas { root := 3, primeFactors := [2, 5, 43] }, .lucas { root := 2, primeFactors := [2, 18149] }, .lucas { root := 2, primeFactors := [2, 13, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 31, 19219] }, .lucas { root := 2, primeFactors := [2, 3, 3203] }, .lucas { root := 2, primeFactors := [2, 1601] }, .lucas { root := 3, primeFactors := [2, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 83437259] }, .lucas { root := 2, primeFactors := [2, 17, 1381, 1777] }, .lucas { root := 2, primeFactors := [2, 3, 5, 23] }, .lucas { root := 5, primeFactors := [2, 3, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 29, primeFactors := [2, 3, 5, 109, 1621] }, .lucas { root := 2, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 33, primeFactors := [2, 3, 5, 7, 23, 29, 61] }]), by simp⟩

@[expose] noncomputable def bankLeaf80 : PrimeBank := .leaf [10695665473, 10733843191, 10822630597, 10846282501, 10915625311, 10970125753, 11012427367, 11018941331, 11242578713, 12081356831, 12136610669, 12246841879, 12267153193, 12346432697, 12475678441, 12796663573]

theorem bankLeaf80_valid : bankLeaf80.Certified := by
  simp only [bankLeaf80, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 1033, 53927] }, .lucas { root := 5, primeFactors := [2, 3, 43] }, .lucas { root := 5, primeFactors := [2, 59, 457] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 37, 71, 19457] }, .lucas { root := 3, primeFactors := [2, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 31, 79, 113, 3259] }, .lucas { root := 3, primeFactors := [2, 3, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 23, 20959] }, .lucas { root := 7, primeFactors := [2, 3, 7, 499] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 467, 779131] }, .lucas { root := 2, primeFactors := [2, 3, 5, 11, 787] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 139, 1151, 2857] }, .lucas { root := 17, primeFactors := [2, 5, 23] }, .lucas { root := 11, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 43, 42683827] }, .lucas { root := 5, primeFactors := [2, 3, 983, 7237] }, .lucas { root := 2, primeFactors := [2, 3, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 79, 13948027] }, .lucas { root := 3, primeFactors := [2, 3, 647, 3593] }, .lucas { root := 3, primeFactors := [2, 449] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 29, 2203, 21997] }, .lucas { root := 5, primeFactors := [2, 3, 367] }, .lucas { root := 7, primeFactors := [2, 3, 13, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 61, 2833, 6991] }, .lucas { root := 5, primeFactors := [2, 3, 59] }, .lucas { root := 6, primeFactors := [2, 3, 5, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 13, 89, 109, 491] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 23, 8171, 10861] }, .lucas { root := 2, primeFactors := [2, 5, 19, 43] }, .lucas { root := 2, primeFactors := [2, 3, 5, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 61, 1197029] }, .lucas { root := 2, primeFactors := [2, 7, 42751] }, .lucas { root := 6, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 13, 61, 1123, 1733] }, .lucas { root := 2, primeFactors := [2, 3, 11, 17] }, .lucas { root := 2, primeFactors := [2, 433] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 31, 41, 157, 521] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 11, 17, 271553] }, .lucas { root := 3, primeFactors := [2, 4243] }, .lucas { root := 2, primeFactors := [2, 3, 7, 101] }]), by simp⟩

@[expose] noncomputable def bankLeaf81 : PrimeBank := .leaf [12926572181, 12936304421, 13144147169, 13189649827, 13658333419, 13739597803, 14632890871, 14827598491, 14870228231, 14970397181, 15100497917, 15428908531, 15783728797, 15995470741, 16020797851, 16148168401]

theorem bankLeaf81_valid : bankLeaf81.Certified := by
  simp only [bankLeaf81, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 646328609] }, .lucas { root := 3, primeFactors := [2, 20197769] }, .lucas { root := 6, primeFactors := [2, 17, 148513] }, .lucas { root := 5, primeFactors := [2, 3, 7, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13, 41, 277, 337] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 410754599] }, .lucas { root := 13, primeFactors := [2, 3011, 68209] }, .lucas { root := 2, primeFactors := [2, 5, 7, 43] }, .lucas { root := 13, primeFactors := [2, 3, 7, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5591, 393181] }, .lucas { root := 11, primeFactors := [2, 5, 13, 43] }, .lucas { root := 6, primeFactors := [2, 3, 5, 6553] }, .lucas { root := 10, primeFactors := [2, 3, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 211, 3596191] }, .lucas { root := 3, primeFactors := [2, 3, 5, 13, 9221] }, .lucas { root := 2, primeFactors := [2, 5, 461] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 71, 1535837] }, .lucas { root := 2, primeFactors := [2, 599, 641] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 83, 251, 1801] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 3623, 136421] }, .lucas { root := 5, primeFactors := [2, 1811] }, .lucas { root := 6, primeFactors := [2, 5, 181] }, .lucas { root := 3, primeFactors := [2, 5, 19, 359] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 11, 13, 10398761] }, .lucas { root := 3, primeFactors := [2, 5, 23, 89, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 1567, 477677] }, .lucas { root := 3, primeFactors := [2, 3, 29] }, .lucas { root := 2, primeFactors := [2, 119419] }, .lucas { root := 2, primeFactors := [2, 3, 13, 1531] }, .lucas { root := 2, primeFactors := [2, 3, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 31, 17396887] }, .lucas { root := 6, primeFactors := [2, 3, 13, 223037] }, .lucas { root := 2, primeFactors := [2, 11, 37, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 23, 683, 1559] }, .lucas { root := 19, primeFactors := [2, 19, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 163, 81509] }, .lucas { root := 2, primeFactors := [2, 7, 41, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37, 7205167] }, .lucas { root := 5, primeFactors := [2, 3, 29, 43, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 35601773] }, .lucas { root := 2, primeFactors := [2, 227, 39209] }, .lucas { root := 3, primeFactors := [2, 13, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 5, 7, 13, 19, 43, 181] }]), by simp⟩

end OddPerfect.IndexComponent.Size160
