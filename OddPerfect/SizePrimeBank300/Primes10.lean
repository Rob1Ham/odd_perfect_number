module

public import OddPerfect.SizePrimeBank300.Primes09
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.IndexComponent.SizePrimeBank300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def bankLeaf169 : PrimeBank := .leaf [14199470611, 14632890871, 14702780467, 14755191029, 14879180581, 15119485141, 15428908531, 15592926343, 15687634021, 15768033143, 15783728797, 15995470741, 16020797851, 16148168401, 16222061143, 16225434523]

theorem bankLeaf169_valid : bankLeaf169.Certified := by
  simp only [bankLeaf169, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 1327, 27437] }, .lucas { root := 3, primeFactors := [2, 3, 13, 17] }, .lucas { root := 2, primeFactors := [2, 19] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 227, 373, 877] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 41, 6151, 14627] }, .lucas { root := 3, primeFactors := [2, 3, 5, 41] }, .lucas { root := 2, primeFactors := [2, 71, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 22544213] }, .lucas { root := 2, primeFactors := [2, 43, 131071] }, .lucas { root := 3, primeFactors := [2, 3, 5, 17, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 59, 4271041] }, .lucas { root := 7, primeFactors := [2, 3, 5, 1483] }, .lucas { root := 2, primeFactors := [2, 3, 13, 19] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43, 8633957] }, .lucas { root := 2, primeFactors := [2, 397, 5437] }, .lucas { root := 5, primeFactors := [2, 3, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 41, 197, 32371] }, .lucas { root := 2, primeFactors := [2, 3, 5, 13, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 73, 547, 197441] }, .lucas { root := 6, primeFactors := [2, 5, 617] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 1361, 94597] }, .lucas { root := 3, primeFactors := [2, 5, 17] }, .lucas { root := 5, primeFactors := [2, 3, 7883] }, .lucas { root := 2, primeFactors := [2, 7, 563] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 19, 53, 4283] }, .lucas { root := 2, primeFactors := [2, 2141] }, .lucas { root := 2, primeFactors := [2, 5, 107] }]), by simp⟩

@[expose] noncomputable def bankLeaf170 : PrimeBank := .leaf [16311060529, 16497763013, 16520191511, 17189128703, 17257690903, 17259425773, 17361223741, 18035954329, 18038601283, 18366263737, 18542517953, 18693457687, 18813315461, 18839057791, 18972457177, 18988763011]

theorem bankLeaf170_valid : bankLeaf170.Certified := by
  simp only [bankLeaf170, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 7, 163, 431, 691] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 109, 2141, 7079] }, .lucas { root := 2, primeFactors := [2, 5, 107] }, .lucas { root := 7, primeFactors := [2, 3539] }, .lucas { root := 2, primeFactors := [2, 29, 61] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 457, 3147233] }, .lucas { root := 3, primeFactors := [2, 11, 8941] }, .lucas { root := 6, primeFactors := [2, 3, 5, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 2243, 6143] }, .lucas { root := 2, primeFactors := [2, 19, 59] }, .lucas { root := 5, primeFactors := [2, 37, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 7, 331, 324341] }, .lucas { root := 2, primeFactors := [2, 5, 16217] }, .lucas { root := 3, primeFactors := [2, 2027] }, .lucas { root := 2, primeFactors := [2, 1013] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 313, 738863] }, .lucas { root := 10, primeFactors := [2, 29, 12739] }, .lucas { root := 2, primeFactors := [2, 3, 11, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 23857, 32077] }, .lucas { root := 5, primeFactors := [2, 3, 7, 71] }, .lucas { root := 2, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 211, 196159] }, .lucas { root := 3, primeFactors := [2, 3, 32693] }, .lucas { root := 2, primeFactors := [2, 11, 743] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 19, 61, 52709] }, .lucas { root := 2, primeFactors := [2, 13177] }, .lucas { root := 5, primeFactors := [2, 3, 61] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 17, 757, 6971] }, .lucas { root := 2, primeFactors := [2, 5, 17, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 167, 4733647] }, .lucas { root := 3, primeFactors := [2, 3, 788941] }, .lucas { root := 2, primeFactors := [2, 3, 5, 487] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 4261, 21221] }, .lucas { root := 2, primeFactors := [2, 3, 5, 71] }, .lucas { root := 2, primeFactors := [2, 5, 1061] }, .lucas { root := 2, primeFactors := [2, 5, 53] }]), by simp⟩

@[expose] noncomputable def bankLeaf171 : PrimeBank := .leaf [19038018253, 19141890667, 19199332631, 19481464031, 19937168287, 20032891183, 20402696773, 21392848667, 21904630541, 21997956611, 22095845017, 22216443433, 22299994021, 22468639757, 22518207499, 22884801377]

theorem bankLeaf171_valid : bankLeaf171.Certified := by
  simp only [bankLeaf171, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 23, 29, 216233] }, .lucas { root := 3, primeFactors := [2, 151, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 3190315111] }, .lucas { root := 6, primeFactors := [2, 3, 5, 677, 157081] }, .lucas { root := 26, primeFactors := [2, 3, 5, 7, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 5, 2617, 733639] }, .lucas { root := 5, primeFactors := [2, 3, 109] }, .lucas { root := 3, primeFactors := [2, 3, 122273] }, .lucas { root := 3, primeFactors := [2, 3821] }, .lucas { root := 3, primeFactors := [2, 5, 191] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 6287, 44267] }, .lucas { root := 7, primeFactors := [2, 7, 449] }, .lucas { root := 2, primeFactors := [2, 22133] }, .lucas { root := 2, primeFactors := [2, 11, 503] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 41, 27144839] }, .lucas { root := 7, primeFactors := [2, 7, 59, 557] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29, 2203, 2957] }, .lucas { root := 5, primeFactors := [2, 3, 367] }, .lucas { root := 2, primeFactors := [2, 739] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13, 84248579] }, .lucas { root := 2, primeFactors := [2, 59, 173, 4127] }, .lucas { root := 5, primeFactors := [2, 2063] }, .lucas { root := 5, primeFactors := [2, 1031] }, .lucas { root := 14, primeFactors := [2, 5, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 19, 47, 50273] }, .lucas { root := 3, primeFactors := [2, 1571] }, .lucas { root := 2, primeFactors := [2, 5, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 8191, 16057] }, .lucas { root := 17, primeFactors := [2, 3, 5, 7, 13] }, .lucas { root := 7, primeFactors := [2, 3, 223] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 4001, 1403939] }, .lucas { root := 3, primeFactors := [2, 5] }, .lucas { root := 2, primeFactors := [2, 701969] }, .lucas { root := 3, primeFactors := [2, 73, 601] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 2381, 1576243] }, .lucas { root := 3, primeFactors := [2, 5, 7, 17] }, .lucas { root := 2, primeFactors := [2, 3, 67, 1307] }, .lucas { root := 2, primeFactors := [2, 653] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 151, 4736093] }, .lucas { root := 2, primeFactors := [2, 19, 101, 617] }]), by simp⟩

@[expose] noncomputable def bankLeaf172 : PrimeBank := .leaf [22917277423, 23374892729, 23415976777, 24050872253, 24425354521, 24612785597, 24675748729, 24750362743, 25297495897, 25491195671, 25674676553, 26264382337, 26403131021, 26677735199, 26991238223, 27829610537]

theorem bankLeaf172_valid : bankLeaf172.Certified := by
  simp only [bankLeaf172, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 163, 600841] }, .lucas { root := 13, primeFactors := [2, 3, 5, 1669] }, .lucas { root := 2, primeFactors := [2, 3, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 19, 269, 51971] }, .lucas { root := 2, primeFactors := [2, 5, 5197] }, .lucas { root := 7, primeFactors := [2, 3, 433] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 607, 1607357] }, .lucas { root := 2, primeFactors := [2, 401839] }, .lucas { root := 3, primeFactors := [2, 3, 66973] }, .lucas { root := 2, primeFactors := [2, 3, 5581] }, .lucas { root := 6, primeFactors := [2, 3, 5, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 546610733] }, .lucas { root := 2, primeFactors := [2, 23, 251, 23671] }, .lucas { root := 3, primeFactors := [2, 3, 5, 263] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 7, 17, 190051] }, .lucas { root := 7, primeFactors := [2, 3, 5, 7, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 879028057] }, .lucas { root := 7, primeFactors := [2, 3, 61, 263, 761] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 21, primeFactors := [2, 5, 7993, 318919] }, .lucas { root := 5, primeFactors := [2, 3, 37] }, .lucas { root := 6, primeFactors := [2, 3, 23, 2311] }, .lucas { root := 3, primeFactors := [2, 3, 5, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 6043, 75869] }, .lucas { root := 5, primeFactors := [2, 3, 19, 53] }, .lucas { root := 2, primeFactors := [2, 13, 1459] }, .lucas { root := 3, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 22798943] }, .lucas { root := 5, primeFactors := [2, 11399471] }, .lucas { root := 23, primeFactors := [2, 5, 467, 2441] }, .lucas { root := 6, primeFactors := [2, 5, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 188593793] }, .lucas { root := 3, primeFactors := [2, 1473389] }, .lucas { root := 2, primeFactors := [2, 7, 101, 521] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 13, 19, 2011973] }, .lucas { root := 2, primeFactors := [2, 79, 6367] }, .lucas { root := 3, primeFactors := [2, 3, 1061] }, .lucas { root := 2, primeFactors := [2, 5, 53] }]), by simp⟩

@[expose] noncomputable def bankLeaf173 : PrimeBank := .leaf [28269428573, 28304824831, 28312327387, 28490674369, 28653090269, 28744367857, 28905399097, 28971231269, 29965357699, 30569710139, 30629717273, 30705317647, 31402938311, 31448020871, 31567260539, 32308354513]

theorem bankLeaf173_valid : bankLeaf173.Certified := by
  simp only [bankLeaf173, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 11, 79, 349, 3329] }, .lucas { root := 3, primeFactors := [2, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 21, primeFactors := [2, 3, 5, 943494161] }, .lucas { root := 3, primeFactors := [2, 5, 7, 191, 8821] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 19, 257, 5113] }, .lucas { root := 19, primeFactors := [2, 3, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 13, 878041] }, .lucas { root := 19, primeFactors := [2, 3, 5, 271] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 127, 5127611] }, .lucas { root := 2, primeFactors := [2, 5, 512761] }, .lucas { root := 13, primeFactors := [2, 3, 5, 4273] }, .lucas { root := 5, primeFactors := [2, 3, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 35225941] }, .lucas { root := 10, primeFactors := [2, 3, 5, 71, 8269] }, .lucas { root := 2, primeFactors := [2, 3, 13, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 113, 217517] }, .lucas { root := 3, primeFactors := [2, 13, 47, 89] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 83, 60171401] }, .lucas { root := 15, primeFactors := [2, 5, 300857] }, .lucas { root := 3, primeFactors := [2, 37607] }, .lucas { root := 5, primeFactors := [2, 18803] }, .lucas { root := 5, primeFactors := [2, 7, 17, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 1389532279] }, .lucas { root := 3, primeFactors := [2, 3, 231588713] }, .lucas { root := 3, primeFactors := [2, 43, 673223] }, .lucas { root := 5, primeFactors := [2, 11, 71, 431] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 7, 11, 809, 61463] }, .lucas { root := 5, primeFactors := [2, 79, 389] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 101, 1327, 38183] }, .lucas { root := 3, primeFactors := [2, 3, 13, 17] }, .lucas { root := 5, primeFactors := [2, 17, 1123] }, .lucas { root := 2, primeFactors := [2, 3, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 31, 53, 1911317] }, .lucas { root := 2, primeFactors := [2, 11, 359] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 7, 37, 12142093] }, .lucas { root := 5, primeFactors := [2, 3, 89, 11369] }, .lucas { root := 3, primeFactors := [2, 7, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 829, 1730851] }, .lucas { root := 2, primeFactors := [2, 3, 5, 11, 1049] }, .lucas { root := 3, primeFactors := [2, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 32051939] }, .lucas { root := 2, primeFactors := [2, 16025969] }, .lucas { root := 3, primeFactors := [2, 7, 17, 19, 443] }]), by simp⟩

@[expose] noncomputable def bankLeaf174 : PrimeBank := .leaf [32402584631, 32475238801, 33567189193, 33658073731, 34025270113, 34151148991, 34156917917, 34317940117, 34441858081, 34666829081, 34966232809, 35337910669, 35703589963, 36023763577, 36157263917, 36374954029]

theorem bankLeaf174_valid : bankLeaf174.Certified := by
  simp only [bankLeaf174, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 13, 17, 66343] }, .lucas { root := 5, primeFactors := [2, 3, 11057] }, .lucas { root := 3, primeFactors := [2, 691] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 929, 29131] }, .lucas { root := 2, primeFactors := [2, 3, 5, 971] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 19, 2389, 10271] }, .lucas { root := 2, primeFactors := [2, 3, 199] }, .lucas { root := 7, primeFactors := [2, 5, 13, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 17, 23, 661, 1447] }, .lucas { root := 3, primeFactors := [2, 3, 241] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1091, 108289] }, .lucas { root := 2, primeFactors := [2, 5, 109] }, .lucas { root := 7, primeFactors := [2, 3, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 2371, 7621] }, .lucas { root := 2, primeFactors := [2, 3, 5, 79] }, .lucas { root := 2, primeFactors := [2, 3, 5, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 776293589] }, .lucas { root := 2, primeFactors := [2, 7, 27724771] }, .lucas { root := 2, primeFactors := [2, 3, 5, 107, 2879] }, .lucas { root := 7, primeFactors := [2, 1439] }, .lucas { root := 7, primeFactors := [2, 719] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 36013, 79411] }, .lucas { root := 2, primeFactors := [2, 3, 3001] }, .lucas { root := 14, primeFactors := [2, 3, 5] }, .lucas { root := 2, primeFactors := [2, 3, 5, 2647] }, .lucas { root := 3, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 7, 31, 110221] }, .lucas { root := 2, primeFactors := [2, 3, 5, 11, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13, 17, 439, 8933] }, .lucas { root := 2, primeFactors := [2, 7, 11, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 13, 17, 6592427] }, .lucas { root := 2, primeFactors := [2, 3296213] }, .lucas { root := 2, primeFactors := [2, 59, 13967] }, .lucas { root := 5, primeFactors := [2, 6983] }, .lucas { root := 5, primeFactors := [2, 3491] }, .lucas { root := 2, primeFactors := [2, 5, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 43, 631, 108533] }, .lucas { root := 2, primeFactors := [2, 43, 631] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5950598327] }, .lucas { root := 5, primeFactors := [2, 1021, 2914103] }, .lucas { root := 5, primeFactors := [2, 1457051] }, .lucas { root := 2, primeFactors := [2, 5, 7, 23, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 29, 59, 277, 3167] }, .lucas { root := 5, primeFactors := [2, 1583] }, .lucas { root := 5, primeFactors := [2, 7, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 29, 467, 811, 823] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 379, 1142573] }, .lucas { root := 2, primeFactors := [2, 285643] }, .lucas { root := 3, primeFactors := [2, 3, 7, 2267] }, .lucas { root := 2, primeFactors := [2, 11, 103] }]), by simp⟩

@[expose] noncomputable def bankLeaf175 : PrimeBank := .leaf [37445442403, 38151506317, 38442938353, 38549209243, 39079931731, 39287156231, 39294891169, 39447306533, 39553185589, 39652448401, 41442572371, 42137940881, 42887513411, 43268024731, 43505945101, 44093239591]

theorem bankLeaf175_valid : bankLeaf175.Certified := by
  simp only [bankLeaf175, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 167, 1966879] }, .lucas { root := 6, primeFactors := [2, 3, 113, 967] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 13, 101, 6703] }, .lucas { root := 5, primeFactors := [2, 3, 1117] }, .lucas { root := 2, primeFactors := [2, 3, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 587, 10945261] }, .lucas { root := 2, primeFactors := [2, 3, 5, 20269] }, .lucas { root := 2, primeFactors := [2, 3, 563] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 186094913] }, .lucas { root := 3, primeFactors := [2, 67, 43399] }, .lucas { root := 13, primeFactors := [2, 3, 2411] }, .lucas { root := 6, primeFactors := [2, 5, 241] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 17, 1367, 24151] }, .lucas { root := 5, primeFactors := [2, 683] }, .lucas { root := 6, primeFactors := [2, 3, 5, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 13, 503, 62597] }, .lucas { root := 2, primeFactors := [2, 15649] }, .lucas { root := 11, primeFactors := [2, 3, 163] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 19, 23, 569, 2333] }, .lucas { root := 2, primeFactors := [2, 11, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 139, 3387563] }, .lucas { root := 2, primeFactors := [2, 83, 20407] }, .lucas { root := 5, primeFactors := [2, 3, 19, 179] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 1381419079] }, .lucas { root := 3, primeFactors := [2, 3, 13, 17710501] }, .lucas { root := 11, primeFactors := [2, 3, 5, 11807] }, .lucas { root := 5, primeFactors := [2, 5903] }, .lucas { root := 5, primeFactors := [2, 13, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 75246323] }, .lucas { root := 2, primeFactors := [2, 1583, 23767] }, .lucas { root := 5, primeFactors := [2, 7, 113] }, .lucas { root := 3, primeFactors := [2, 3, 17, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 612678763] }, .lucas { root := 2, primeFactors := [2, 3, 149, 76147] }, .lucas { root := 2, primeFactors := [2, 3, 7, 37] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 59, 273107] }, .lucas { root := 2, primeFactors := [2, 19, 7187] }, .lucas { root := 2, primeFactors := [2, 3593] }, .lucas { root := 3, primeFactors := [2, 449] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 1061, 1385273] }, .lucas { root := 2, primeFactors := [2, 5, 53] }, .lucas { root := 3, primeFactors := [2, 7, 29, 853] }]), by simp⟩

@[expose] noncomputable def bankLeaf176 : PrimeBank := .leaf [44198972119, 44403575917, 45658008299, 45712301287, 46685826619, 48011072617, 48268513901, 48774625069, 48837672001, 48873043253, 49236515971, 49276157093, 50241311287, 50368353121, 50390258557, 50738998441]

theorem bankLeaf176_valid : bankLeaf176.Certified := by
  simp only [bankLeaf176, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 6569, 80471] }, .lucas { root := 3, primeFactors := [2, 821] }, .lucas { root := 17, primeFactors := [2, 5, 13, 619] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 17, 743, 258197] }, .lucas { root := 2, primeFactors := [2, 17, 3797] }, .lucas { root := 2, primeFactors := [2, 13, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 97, 193, 21419] }, .lucas { root := 2, primeFactors := [2, 10709] }, .lucas { root := 2, primeFactors := [2, 2677] }, .lucas { root := 2, primeFactors := [2, 3, 223] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 51293881] }, .lucas { root := 13, primeFactors := [2, 3, 5, 11, 12953] }, .lucas { root := 3, primeFactors := [2, 1619] }, .lucas { root := 2, primeFactors := [2, 809] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 19, 521, 48761] }, .lucas { root := 3, primeFactors := [2, 5, 23, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 312657853] }, .lucas { root := 2, primeFactors := [2, 3, 13, 107, 18731] }, .lucas { root := 2, primeFactors := [2, 5, 1873] }, .lucas { root := 10, primeFactors := [2, 3, 13] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 37, 433, 522661] }, .lucas { root := 6, primeFactors := [2, 3, 5, 31, 281] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 73, 53239] }, .lucas { root := 3, primeFactors := [2, 3, 19, 467] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 13, 2501923] }, .lucas { root := 3, primeFactors := [2, 3, 503, 829] }]), by simp⟩

@[expose] noncomputable def bankLeaf177 : PrimeBank := .leaf [51428739319, 51689284541, 52379047267, 52407378251, 52409388389, 52638536663, 52778228147, 53505560417, 53514928183, 53738676221, 54864211481, 56836159529, 57643774229, 58341660037, 59954796907, 60709918541]

theorem bankLeaf177_valid : bankLeaf177.Certified := by
  simp only [bankLeaf177, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 779223323] }, .lucas { root := 2, primeFactors := [2, 17, 4283, 5351] }, .lucas { root := 2, primeFactors := [2, 2141] }, .lucas { root := 2, primeFactors := [2, 5, 107] }, .lucas { root := 11, primeFactors := [2, 5, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 19, 136024433] }, .lucas { root := 3, primeFactors := [2, 37, 229771] }, .lucas { root := 12, primeFactors := [2, 3, 5, 23, 37] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 97, 2161129] }, .lucas { root := 7, primeFactors := [2, 3, 53, 1699] }, .lucas { root := 3, primeFactors := [2, 3, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 479, 3907649] }, .lucas { root := 3, primeFactors := [2, 61057] }, .lucas { root := 5, primeFactors := [2, 3, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 19, 103, 13448783] }, .lucas { root := 5, primeFactors := [2, 1627, 4133] }, .lucas { root := 3, primeFactors := [2, 3, 271] }, .lucas { root := 2, primeFactors := [2, 1033] }, .lucas { root := 5, primeFactors := [2, 3, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 71, 103, 193, 2671] }, .lucas { root := 7, primeFactors := [2, 3, 5, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11, 1699, 12781] }, .lucas { root := 3, primeFactors := [2, 3, 283] }, .lucas { root := 2, primeFactors := [2, 3, 5, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 3709, 2404733] }, .lucas { root := 2, primeFactors := [2, 3, 103] }, .lucas { root := 2, primeFactors := [2, 11, 31, 41, 43] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 197, 36063553] }, .lucas { root := 5, primeFactors := [2, 3, 7, 26833] }, .lucas { root := 5, primeFactors := [2, 3, 13, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 31, 37, 1321, 9511] }, .lucas { root := 13, primeFactors := [2, 3, 5, 11] }, .lucas { root := 3, primeFactors := [2, 3, 5, 317] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 18517, 23869] }, .lucas { root := 6, primeFactors := [2, 3, 1543] }, .lucas { root := 5, primeFactors := [2, 3, 257] }, .lucas { root := 2, primeFactors := [2, 3, 13, 17] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 10939, 277493] }, .lucas { root := 3, primeFactors := [2, 3, 1823] }, .lucas { root := 5, primeFactors := [2, 911] }, .lucas { root := 2, primeFactors := [2, 173, 401] }]), by simp⟩

@[expose] noncomputable def bankLeaf178 : PrimeBank := .leaf [61071495271, 61978819471, 62995328779, 64175509327, 64745079361, 65958721573, 66010998331, 67095696043, 67201361737, 67241197577, 67495678093, 68001766309, 68148966883, 68659639549, 72211650019, 72381100807]

theorem bankLeaf178_valid : bankLeaf178.Certified := by
  simp only [bankLeaf178, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 29, 101, 695021] }, .lucas { root := 2, primeFactors := [2, 5, 19, 31, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 17, 19, 89, 71867] }, .lucas { root := 2, primeFactors := [2, 35933] }, .lucas { root := 2, primeFactors := [2, 13, 691] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 43, 244167941] }, .lucas { root := 7, primeFactors := [2, 5, 17, 89, 8069] }, .lucas { root := 2, primeFactors := [2, 2017] }, .lucas { root := 5, primeFactors := [2, 3, 7] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5496560131] }, .lucas { root := 2, primeFactors := [2, 3, 5, 183218671] }, .lucas { root := 11, primeFactors := [2, 3, 5, 2035763] }, .lucas { root := 2, primeFactors := [2, 1017881] }, .lucas { root := 3, primeFactors := [2, 5, 25447] }, .lucas { root := 3, primeFactors := [2, 3, 4241] }, .lucas { root := 3, primeFactors := [2, 5, 53] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 14957, 249217] }, .lucas { root := 2, primeFactors := [2, 3739] }, .lucas { root := 7, primeFactors := [2, 3, 7, 89] }, .lucas { root := 5, primeFactors := [2, 3, 11, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 14177, 197507] }, .lucas { root := 3, primeFactors := [2, 443] }, .lucas { root := 2, primeFactors := [2, 17, 37, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 1200735671] }, .lucas { root := 11, primeFactors := [2, 5, 17, 53, 71, 1877] }, .lucas { root := 2, primeFactors := [2, 7, 67] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 19, 79, 179779] }, .lucas { root := 2, primeFactors := [2, 3, 19, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 167, 3673, 18517] }, .lucas { root := 5, primeFactors := [2, 3, 17] }, .lucas { root := 6, primeFactors := [2, 3, 1543] }, .lucas { root := 5, primeFactors := [2, 3, 257] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf179 : PrimeBank := .leaf [72849277001, 74451297871, 74824336159, 75427511821, 75619334851, 75755912653, 76126812043, 77635408621, 78785754721, 79028782411, 79100676007, 80835531031, 80882782483, 81760848073, 82316396807, 86950696619]

theorem bankLeaf179_valid : bankLeaf179.Certified := by
  simp only [bankLeaf179, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 72849277] }, .lucas { root := 2, primeFactors := [2, 3, 29, 69779] }, .lucas { root := 2, primeFactors := [2, 139, 251] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 17, 31, 109, 14401] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 13, 83, 12659] }, .lucas { root := 2, primeFactors := [2, 6329] }, .lucas { root := 3, primeFactors := [2, 7, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 103, 457, 1571] }, .lucas { root := 2, primeFactors := [2, 5, 157] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 8501, 78553] }, .lucas { root := 7, primeFactors := [2, 5, 17] }, .lucas { root := 5, primeFactors := [2, 3, 1091] }, .lucas { root := 2, primeFactors := [2, 5, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 11, 31, 542071] }, .lucas { root := 3, primeFactors := [2, 3, 5, 19, 317] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 61, 2777, 15551] }, .lucas { root := 3, primeFactors := [2, 347] }, .lucas { root := 7, primeFactors := [2, 5, 311] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 19, 3319931] }, .lucas { root := 2, primeFactors := [2, 5, 17, 59, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 79, 97, 117209] }, .lucas { root := 3, primeFactors := [2, 7, 13, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13480463747] }, .lucas { root := 2, primeFactors := [2, 37, 239, 762211] }, .lucas { root := 2, primeFactors := [2, 3, 5, 941] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 31, 4073, 26981] }, .lucas { root := 3, primeFactors := [2, 509] }, .lucas { root := 3, primeFactors := [2, 5, 19, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 47, 125100907] }, .lucas { root := 2, primeFactors := [2, 3, 7, 2978593] }, .lucas { root := 17, primeFactors := [2, 3, 19, 23, 71] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf180 : PrimeBank := .leaf [87245160311, 87650274787, 87840993949, 90523341079, 91330330501, 94030112653, 94301495279, 94846240721, 95002219309, 95359493521, 97435960519, 97598032277, 103745502061, 107136718849, 107896304231, 109106389471]

theorem bankLeaf180_valid : bankLeaf180.Certified := by
  simp only [bankLeaf180, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 11, 31, 107, 34159] }, .lucas { root := 3, primeFactors := [2, 3, 5693] }, .lucas { root := 2, primeFactors := [2, 1423] }, .lucas { root := 3, primeFactors := [2, 3, 79] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 491, 14908519] }, .lucas { root := 3, primeFactors := [2, 3, 269, 3079] }, .lucas { root := 6, primeFactors := [2, 3, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 61, 247331533] }, .lucas { root := 2, primeFactors := [2, 3, 7, 37, 79579] }, .lucas { root := 10, primeFactors := [2, 3, 4421] }, .lucas { root := 3, primeFactors := [2, 5, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 19, 1068191] }, .lucas { root := 11, primeFactors := [2, 5, 37, 2887] }, .lucas { root := 5, primeFactors := [2, 3, 13, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 37, 30254219] }, .lucas { root := 2, primeFactors := [2, 353, 42853] }, .lucas { root := 2, primeFactors := [2, 3, 3571] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 74873, 629743] }, .lucas { root := 3, primeFactors := [2, 7, 191] }, .lucas { root := 5, primeFactors := [2, 3, 103, 1019] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 11, 15397117] }, .lucas { root := 2, primeFactors := [2, 3, 7, 183299] }, .lucas { root := 2, primeFactors := [2, 37, 2477] }, .lucas { root := 2, primeFactors := [2, 619] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 11489, 689081] }, .lucas { root := 3, primeFactors := [2, 359] }, .lucas { root := 3, primeFactors := [2, 5, 7, 23, 107] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 5087, 245563] }, .lucas { root := 5, primeFactors := [2, 2543] }, .lucas { root := 5, primeFactors := [2, 31, 41] }, .lucas { root := 2, primeFactors := [2, 3, 40927] }, .lucas { root := 3, primeFactors := [2, 3, 19, 359] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 211, 283, 317, 1289] }, .lucas { root := 6, primeFactors := [2, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 59, 29306639] }, .lucas { root := 13, primeFactors := [2, 14653319] }, .lucas { root := 7, primeFactors := [2, 41, 83, 2153] }, .lucas { root := 3, primeFactors := [2, 269] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 1937513] }, .lucas { root := 3, primeFactors := [2, 127, 1907] }, .lucas { root := 2, primeFactors := [2, 953] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 13, 17, 421, 39089] }, .lucas { root := 3, primeFactors := [2, 7, 349] }]), by simp⟩

@[expose] noncomputable def bankLeaf181 : PrimeBank := .leaf [109162124431, 109449185539, 109707531023, 111660088297, 113990869481, 114787621229, 115232124547, 116222014483, 116680380199, 116856733421, 117442848251, 117856312921, 117967608271, 118058913923, 120023424751, 120082834831]

theorem bankLeaf181_valid : bankLeaf181.Certified := by
  simp only [bankLeaf181, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 19, 359, 701, 761] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 11, 83, 2854253] }, .lucas { root := 2, primeFactors := [2, 713563] }, .lucas { root := 5, primeFactors := [2, 3, 118927] }, .lucas { root := 3, primeFactors := [2, 3, 6607] }, .lucas { root := 3, primeFactors := [2, 3, 367] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 37, 313, 4736531] }, .lucas { root := 2, primeFactors := [2, 5, 311, 1523] }, .lucas { root := 2, primeFactors := [2, 761] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 17, 3761, 72767] }, .lucas { root := 3, primeFactors := [2, 5, 47] }, .lucas { root := 5, primeFactors := [2, 36383] }, .lucas { root := 5, primeFactors := [2, 18191] }, .lucas { root := 29, primeFactors := [2, 5, 17, 107] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 20161, 203341] }, .lucas { root := 13, primeFactors := [2, 3, 5, 7] }, .lucas { root := 7, primeFactors := [2, 3, 5, 3389] }, .lucas { root := 3, primeFactors := [2, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 11, 5939, 13999] }, .lucas { root := 2, primeFactors := [2, 2969] }, .lucas { root := 3, primeFactors := [2, 7, 53] }, .lucas { root := 3, primeFactors := [2, 3, 2333] }, .lucas { root := 2, primeFactors := [2, 11, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 8117, 340913] }, .lucas { root := 2, primeFactors := [2, 2029] }, .lucas { root := 2, primeFactors := [2, 3, 13] }, .lucas { root := 3, primeFactors := [2, 11, 13, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 19, 61, 16778887] }, .lucas { root := 3, primeFactors := [2, 3, 523, 5347] }, .lucas { root := 3, primeFactors := [2, 3, 11] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 73, 1583, 2833] }, .lucas { root := 5, primeFactors := [2, 7, 113] }, .lucas { root := 5, primeFactors := [2, 3, 59] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 31, 1904176031] }, .lucas { root := 21, primeFactors := [2, 5, 59, 3227417] }, .lucas { root := 3, primeFactors := [2, 17, 19, 1249] }, .lucas { root := 7, primeFactors := [2, 3, 13] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 41, 13946903] }, .lucas { root := 5, primeFactors := [2, 17, 410203] }, .lucas { root := 3, primeFactors := [2, 3, 13, 1753] }, .lucas { root := 7, primeFactors := [2, 3, 73] }]), by simp⟩

end OddPerfect.IndexComponent.SizePrimeBank300
