module

public import OddPerfect.SizeIndex160.Primes02
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.IndexComponent.Size160

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def bankLeaf51 : PrimeBank := .leaf [4252519, 4404047, 4429057, 4555237, 4618291, 4832521, 4873051, 4966373, 5077297, 5104249, 5112661, 5179063, 5187859, 5229043, 5496949, 5499979]

theorem bankLeaf51_valid : bankLeaf51.Certified := by
  simp only [bankLeaf51, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 31, 7621] }, .lucas { root := 2, primeFactors := [2, 3, 5, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 31, 251, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 73, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 61, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 257, 599] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 7, 11, 523] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 101, 647] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 23, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 212677] }, .lucas { root := 2, primeFactors := [2, 3, 37, 479] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 37, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 123311] }, .lucas { root := 11, primeFactors := [2, 5, 11, 19, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 227, 293] }]),
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 7, 13, 61, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 43, 53, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 167, 499] }]), by simp⟩

@[expose] noncomputable def bankLeaf52 : PrimeBank := .leaf [5601667, 5615587, 5781439, 5787763, 5831779, 5837399, 5877181, 6004651, 6053461, 6102253, 6157549, 6263783, 6294091, 6315307, 6543343, 6545261]

theorem bankLeaf52_valid : bankLeaf52.Certified := by
  simp only [bankLeaf52, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 41, 3253] }, .lucas { root := 2, primeFactors := [2, 3, 271] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 223, 1399] }, .lucas { root := 13, primeFactors := [2, 3, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 31, 797] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 29, 31, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 823, 1181] }, .lucas { root := 7, primeFactors := [2, 5, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 416957] }, .lucas { root := 2, primeFactors := [2, 104239] }, .lucas { root := 6, primeFactors := [2, 3, 5791] }, .lucas { root := 6, primeFactors := [2, 3, 5, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 103, 317] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 40031] }, .lucas { root := 19, primeFactors := [2, 5, 4003] }, .lucas { root := 2, primeFactors := [2, 3, 23, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 29, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 13, 17, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 171043] }, .lucas { root := 2, primeFactors := [2, 3, 29, 983] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 151, 2963] }, .lucas { root := 2, primeFactors := [2, 1481] }, .lucas { root := 3, primeFactors := [2, 5, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 11, 19073] }, .lucas { root := 3, primeFactors := [2, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1052551] }, .lucas { root := 3, primeFactors := [2, 3, 5, 2339] }, .lucas { root := 2, primeFactors := [2, 7, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 239] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 327263] }, .lucas { root := 10, primeFactors := [2, 13, 41, 307] }]), by simp⟩

@[expose] noncomputable def bankLeaf53 : PrimeBank := .leaf [6575641, 6578839, 6579701, 6619231, 6621847, 6660389, 6684907, 7305457, 7668337, 7834583, 7908811, 7926241, 7951679, 8242697, 8248369, 8401397]

theorem bankLeaf53_valid : bankLeaf53.Certified := by
  simp only [bankLeaf53, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 37, 1481] }, .lucas { root := 3, primeFactors := [2, 5, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 7459] }, .lucas { root := 2, primeFactors := [2, 3, 11, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 19, 3463] }, .lucas { root := 3, primeFactors := [2, 3, 577] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 73547] }, .lucas { root := 2, primeFactors := [2, 11, 3343] }, .lucas { root := 5, primeFactors := [2, 3, 557] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11, 1303] }, .lucas { root := 6, primeFactors := [2, 3, 7, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 127, 1873] }, .lucas { root := 10, primeFactors := [2, 3, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 29, 103, 373] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 152197] }, .lucas { root := 5, primeFactors := [2, 3, 11, 1153] }, .lucas { root := 5, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 12289] }, .lucas { root := 11, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 23, 29, 839] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 2897] }, .lucas { root := 3, primeFactors := [2, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 337] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 353, 1609] }, .lucas { root := 7, primeFactors := [2, 3, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11, 13381] }, .lucas { root := 10, primeFactors := [2, 3, 5, 223] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 239, 719] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 1307, 1607] }, .lucas { root := 2, primeFactors := [2, 653] }, .lucas { root := 5, primeFactors := [2, 11, 73] }]), by simp⟩

@[expose] noncomputable def bankLeaf54 : PrimeBank := .leaf [8407123, 8454841, 8964821, 8970971, 9170881, 9341851, 9466799, 9807089, 10074277, 10196539, 10275301, 10378063, 10688807, 10857851, 11158141, 11445877]

theorem bankLeaf54_valid : bankLeaf54.Certified := by
  simp only [bankLeaf54, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1401187] }, .lucas { root := 3, primeFactors := [2, 3, 347, 673] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 70457] }, .lucas { root := 3, primeFactors := [2, 8807] }, .lucas { root := 5, primeFactors := [2, 7, 17, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 448241] }, .lucas { root := 3, primeFactors := [2, 5, 13, 431] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 73, 12289] }, .lucas { root := 11, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 41, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 7, 31, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 11, 39119] }, .lucas { root := 11, primeFactors := [2, 19559] }, .lucas { root := 13, primeFactors := [2, 7, 11, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 71, 89, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 154493] }, .lucas { root := 2, primeFactors := [2, 13, 2971] }, .lucas { root := 10, primeFactors := [2, 3, 5, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 179, 3221] }, .lucas { root := 10, primeFactors := [2, 5, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 73, 179, 409] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 217157] }, .lucas { root := 2, primeFactors := [2, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 31, 857] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 37, 661] }]), by simp⟩

@[expose] noncomputable def bankLeaf55 : PrimeBank := .leaf [11631811, 11647327, 11677891, 11897351, 12040843, 12207031, 12562171, 12760031, 12833941, 12865927, 14073559, 14092193, 14374663, 14597959, 14720941, 14804653]

theorem bankLeaf55_valid : bankLeaf55.Certified := by
  simp only [bankLeaf55, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 387727] }, .lucas { root := 3, primeFactors := [2, 3, 64621] }, .lucas { root := 6, primeFactors := [2, 3, 5, 359] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1941221] }, .lucas { root := 2, primeFactors := [2, 5, 31, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 55609] }, .lucas { root := 13, primeFactors := [2, 3, 7, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 37, 59, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 241, 757] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 71, 521] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 418739] }, .lucas { root := 2, primeFactors := [2, 23, 9103] }, .lucas { root := 6, primeFactors := [2, 3, 37, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 17, 47, 1597] }, .lucas { root := 11, primeFactors := [2, 3, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 30557] }, .lucas { root := 2, primeFactors := [2, 7639] }, .lucas { root := 7, primeFactors := [2, 3, 19, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19, 112859] }, .lucas { root := 2, primeFactors := [2, 73, 773] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2345593] }, .lucas { root := 5, primeFactors := [2, 3, 17, 5749] }, .lucas { root := 2, primeFactors := [2, 3, 479] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 23, 41, 467] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 29, 82613] }, .lucas { root := 2, primeFactors := [2, 19, 1087] }, .lucas { root := 3, primeFactors := [2, 3, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 89, 27337] }, .lucas { root := 5, primeFactors := [2, 3, 17, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 13, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1233721] }, .lucas { root := 13, primeFactors := [2, 3, 5, 23, 149] }]), by simp⟩

@[expose] noncomputable def bankLeaf56 : PrimeBank := .leaf [15120433, 15251867, 15326501, 15349897, 15406931, 15479857, 15527627, 15852481, 16141907, 16293691, 16441151, 17027551, 17884211, 17895809, 19218301, 19587401]

theorem bankLeaf56_valid : bankLeaf56.Certified := by
  simp only [bankLeaf56, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 3889] }, .lucas { root := 11, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 487, 2237] }, .lucas { root := 2, primeFactors := [2, 13, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 5, 7, 29, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 213193] }, .lucas { root := 5, primeFactors := [2, 3, 7, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 11, 17, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 5119] }, .lucas { root := 3, primeFactors := [2, 3, 853] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 107, 72559] }, .lucas { root := 3, primeFactors := [2, 3, 29, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 337] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 19, 23, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 7, 37, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 5, 11, 167, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 12613] }, .lucas { root := 2, primeFactors := [2, 3, 1051] }, .lucas { root := 7, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 31, 1861] }, .lucas { root := 2, primeFactors := [2, 3, 5, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 7, 19973] }, .lucas { root := 2, primeFactors := [2, 4993] }, .lucas { root := 5, primeFactors := [2, 3, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 29, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 17, 823] }]), by simp⟩

@[expose] noncomputable def bankLeaf57 : PrimeBank := .leaf [19622651, 20143639, 20241187, 20305777, 20381027, 20437301, 20790271, 21251543, 21567673, 21935293, 22129571, 22406023, 22909811, 22926121, 22996651, 23007529]

theorem bankLeaf57_valid : bankLeaf57.Certified := by
  simp only [bankLeaf57, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 601, 653] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1119091] }, .lucas { root := 7, primeFactors := [2, 3, 5, 7, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 17, 28349] }, .lucas { root := 2, primeFactors := [2, 19, 373] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 127, 3331] }, .lucas { root := 3, primeFactors := [2, 3, 5, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 29, 351397] }, .lucas { root := 2, primeFactors := [2, 3, 43, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13, 79, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 25667] }, .lucas { root := 2, primeFactors := [2, 41, 313] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 37, 22091] }, .lucas { root := 2, primeFactors := [2, 5, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 42793] }, .lucas { root := 5, primeFactors := [2, 3, 1783] }, .lucas { root := 10, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 103, 17747] }, .lucas { root := 2, primeFactors := [2, 19, 467] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 353, 6269] }, .lucas { root := 2, primeFactors := [2, 1567] }, .lucas { root := 3, primeFactors := [2, 3, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 263, 4733] }, .lucas { root := 5, primeFactors := [2, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 11, 29753] }, .lucas { root := 3, primeFactors := [2, 3719] }, .lucas { root := 7, primeFactors := [2, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 41, primeFactors := [2, 3, 5, 7, 557] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 19, 8069] }, .lucas { root := 2, primeFactors := [2, 2017] }, .lucas { root := 5, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 17, 18797] }, .lucas { root := 3, primeFactors := [2, 37, 127] }]), by simp⟩

@[expose] noncomputable def bankLeaf58 : PrimeBank := .leaf [23159681, 23468881, 23615827, 24460537, 24576241, 25249969, 25384507, 25524791, 26010319, 26099221, 26626291, 26956151, 27763969, 28015921, 28294061, 28878847]

theorem bankLeaf58_valid : bankLeaf58.Certified := by
  simp only [bankLeaf58, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 36187] }, .lucas { root := 3, primeFactors := [2, 3, 37, 163] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 97787] }, .lucas { root := 2, primeFactors := [2, 13, 3761] }, .lucas { root := 3, primeFactors := [2, 5, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 302767] }, .lucas { root := 3, primeFactors := [2, 3, 50461] }, .lucas { root := 7, primeFactors := [2, 3, 5, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 241, 4229] }, .lucas { root := 2, primeFactors := [2, 7, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 13, 7877] }, .lucas { root := 2, primeFactors := [2, 11, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 21, primeFactors := [2, 3, 19483] }, .lucas { root := 2, primeFactors := [2, 3, 17, 191] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 127, 4759] }, .lucas { root := 3, primeFactors := [2, 3, 13, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 19, 134341] }, .lucas { root := 2, primeFactors := [2, 3, 5, 2239] }, .lucas { root := 3, primeFactors := [2, 3, 373] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 41, 105733] }, .lucas { root := 6, primeFactors := [2, 3, 11, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 62141] }, .lucas { root := 2, primeFactors := [2, 5, 13, 239] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 887543] }, .lucas { root := 5, primeFactors := [2, 443771] }, .lucas { root := 2, primeFactors := [2, 5, 199, 223] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 5, 13, 113, 367] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 36151] }, .lucas { root := 3, primeFactors := [2, 3, 5, 241] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 167, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1414703] }, .lucas { root := 5, primeFactors := [2, 19, 59, 631] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 23, 209267] }, .lucas { root := 2, primeFactors := [2, 19, 5507] }, .lucas { root := 2, primeFactors := [2, 2753] }, .lucas { root := 3, primeFactors := [2, 43] }]), by simp⟩

@[expose] noncomputable def bankLeaf59 : PrimeBank := .leaf [29040311, 29372479, 29763857, 29786959, 29866451, 31012561, 31029319, 32009891, 32668561, 32928979, 33425173, 33997211, 34009763, 34150141, 34199239, 34210243]

theorem bankLeaf59_valid : bankLeaf59.Certified := by
  simp only [bankLeaf59, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 33, primeFactors := [2, 5, 13, 29, 7703] }, .lucas { root := 5, primeFactors := [2, 3851] }, .lucas { root := 2, primeFactors := [2, 5, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 367, 13339] }, .lucas { root := 2, primeFactors := [2, 3, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 593, 3137] }, .lucas { root := 3, primeFactors := [2, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 311, 313] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 41, 857] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 19, 2267] }, .lucas { root := 2, primeFactors := [2, 11, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 19, 593] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 290999] }, .lucas { root := 7, primeFactors := [2, 83, 1753] }, .lucas { root := 7, primeFactors := [2, 3, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 17, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29, 97, 1951] }, .lucas { root := 3, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 84407] }, .lucas { root := 5, primeFactors := [2, 7, 6029] }, .lucas { root := 2, primeFactors := [2, 11, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 13, 103, 2539] }, .lucas { root := 2, primeFactors := [2, 3, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17004881] }, .lucas { root := 6, primeFactors := [2, 5, 212561] }, .lucas { root := 3, primeFactors := [2, 5, 2657] }, .lucas { root := 3, primeFactors := [2, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 63241] }, .lucas { root := 7, primeFactors := [2, 3, 5, 17, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 5699873] }, .lucas { root := 3, primeFactors := [2, 59, 3019] }, .lucas { root := 2, primeFactors := [2, 3, 503] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 57593] }, .lucas { root := 3, primeFactors := [2, 23, 313] }]), by simp⟩

@[expose] noncomputable def bankLeaf60 : PrimeBank := .leaf [35123017, 35595181, 35941459, 36855109, 38242661, 38533987, 39767719, 39987067, 40497241, 40935743, 41213191, 41615143, 41808163, 43038337, 43304141, 43680671]

theorem bankLeaf60_valid : bankLeaf60.Certified := by
  simp only [bankLeaf60, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1463459] }, .lucas { root := 2, primeFactors := [2, 731729] }, .lucas { root := 3, primeFactors := [2, 19, 29, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 29, 2273] }, .lucas { root := 3, primeFactors := [2, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 113, 7573] }, .lucas { root := 2, primeFactors := [2, 3, 631] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 23, 37, 401] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1912133] }, .lucas { root := 2, primeFactors := [2, 101, 4733] }, .lucas { root := 5, primeFactors := [2, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 431, 4967] }, .lucas { root := 5, primeFactors := [2, 13, 191] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 293, 22621] }, .lucas { root := 2, primeFactors := [2, 3, 5, 13, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 952073] }, .lucas { root := 3, primeFactors := [2, 11, 31, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 37, 1303] }, .lucas { root := 6, primeFactors := [2, 3, 7, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 43, 475997] }, .lucas { root := 2, primeFactors := [2, 127, 937] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 37, 107, 347] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 23, 43, 7013] }, .lucas { root := 2, primeFactors := [2, 1753] }, .lucas { root := 7, primeFactors := [2, 3, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 57587] }, .lucas { root := 2, primeFactors := [2, 28793] }, .lucas { root := 3, primeFactors := [2, 59, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11, 23, 443] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 196837] }, .lucas { root := 2, primeFactors := [2, 3, 47, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 11, 29, 13693] }, .lucas { root := 6, primeFactors := [2, 3, 7, 163] }]), by simp⟩

@[expose] noncomputable def bankLeaf61 : PrimeBank := .leaf [45437789, 47650987, 47783893, 47910479, 48071041, 48552947, 49627843, 49722523, 49936897, 50062963, 50408381, 50479787, 53306107, 54417721, 54560173, 55325371]

theorem bankLeaf61_valid : bankLeaf61.Certified := by
  simp only [bankLeaf61, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 23, 59, 761] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 115099] }, .lucas { root := 3, primeFactors := [2, 3, 19183] }, .lucas { root := 3, primeFactors := [2, 3, 23, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 157, 1951] }, .lucas { root := 3, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 11, 59, 5273] }, .lucas { root := 3, primeFactors := [2, 659] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 25037] }, .lucas { root := 2, primeFactors := [2, 11, 569] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 1867421] }, .lucas { root := 2, primeFactors := [2, 5, 93371] }, .lucas { root := 2, primeFactors := [2, 5, 9337] }, .lucas { root := 5, primeFactors := [2, 3, 389] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 389, 1933] }, .lucas { root := 5, primeFactors := [2, 3, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 47, 176321] }, .lucas { root := 3, primeFactors := [2, 5, 19, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 10837] }, .lucas { root := 2, primeFactors := [2, 3, 7, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 73, 114299] }, .lucas { root := 2, primeFactors := [2, 57149] }, .lucas { root := 2, primeFactors := [2, 7, 13, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 29, 7901] }, .lucas { root := 2, primeFactors := [2, 5, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 47, 76717] }, .lucas { root := 2, primeFactors := [2, 3, 2131] }, .lucas { root := 2, primeFactors := [2, 3, 5, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 1269193] }, .lucas { root := 10, primeFactors := [2, 3, 52883] }, .lucas { root := 2, primeFactors := [2, 137, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 64783] }, .lucas { root := 5, primeFactors := [2, 3, 59, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 97, 2467] }, .lucas { root := 2, primeFactors := [2, 3, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 1844179] }, .lucas { root := 2, primeFactors := [2, 3, 7, 19, 2311] }, .lucas { root := 3, primeFactors := [2, 3, 5, 7, 11] }]), by simp⟩

@[expose] noncomputable def bankLeaf62 : PrimeBank := .leaf [55918991, 56964757, 57344741, 57384601, 59503651, 61511921, 62060021, 62478139, 63284371, 65741959, 65829347, 68808391, 69655517, 70725371, 70911041, 74670499]

theorem bankLeaf62_valid : bankLeaf62.Certified := by
  simp only [bankLeaf62, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 5591899] }, .lucas { root := 2, primeFactors := [2, 3, 13, 23, 1039] }, .lucas { root := 3, primeFactors := [2, 3, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 37, 7547] }, .lucas { root := 2, primeFactors := [2, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 227, 743] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 13, 1051] }, .lucas { root := 7, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 29, 13679] }, .lucas { root := 7, primeFactors := [2, 7, 977] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 787, 977] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 282091] }, .lucas { root := 3, primeFactors := [2, 3, 5, 9403] }, .lucas { root := 3, primeFactors := [2, 3, 1567] }, .lucas { root := 3, primeFactors := [2, 3, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 10413023] }, .lucas { root := 5, primeFactors := [2, 5206511] }, .lucas { root := 7, primeFactors := [2, 5, 23, 22637] }, .lucas { root := 2, primeFactors := [2, 5659] }, .lucas { root := 2, primeFactors := [2, 3, 23, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 124087] }, .lucas { root := 3, primeFactors := [2, 3, 20681] }, .lucas { root := 3, primeFactors := [2, 5, 11, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 17, 23, 9341] }, .lucas { root := 2, primeFactors := [2, 5, 467] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 2992243] }, .lucas { root := 5, primeFactors := [2, 3, 11, 45337] }, .lucas { root := 5, primeFactors := [2, 3, 1889] }, .lucas { root := 3, primeFactors := [2, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 157, 2087] }, .lucas { root := 5, primeFactors := [2, 7, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 2487697] }, .lucas { root := 5, primeFactors := [2, 3, 51827] }, .lucas { root := 2, primeFactors := [2, 25913] }, .lucas { root := 3, primeFactors := [2, 41, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7072537] }, .lucas { root := 5, primeFactors := [2, 3, 157, 1877] }, .lucas { root := 2, primeFactors := [2, 7, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 19, 107, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 47, 467] }]), by simp⟩

@[expose] noncomputable def bankLeaf63 : PrimeBank := .leaf [74739449, 77619973, 83774233, 84438671, 85044793, 87550591, 87683177, 88009573, 89218117, 90385609, 91605427, 93033679, 93853931, 94769947, 95318081, 96656723]

theorem bankLeaf63_valid : bankLeaf63.Certified := by
  simp only [bankLeaf63, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 1334633] }, .lucas { root := 3, primeFactors := [2, 13, 41, 313] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 641, 10091] }, .lucas { root := 2, primeFactors := [2, 5, 1009] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 17, 68443] }, .lucas { root := 5, primeFactors := [2, 3, 11, 17, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 43, 131, 1499] }, .lucas { root := 2, primeFactors := [2, 7, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 10331] }, .lucas { root := 2, primeFactors := [2, 5, 1033] }, .lucas { root := 5, primeFactors := [2, 3, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 5, 193, 15121] }, .lucas { root := 11, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 19, 23, 3583] }, .lucas { root := 3, primeFactors := [2, 3, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 7, 337, 3109] }, .lucas { root := 6, primeFactors := [2, 3, 7, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 379, 503] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 181, 20807] }, .lucas { root := 5, primeFactors := [2, 101, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 1387961] }, .lucas { root := 15, primeFactors := [2, 5, 7, 4957] }, .lucas { root := 2, primeFactors := [2, 3, 7, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 59, 262807] }, .lucas { root := 3, primeFactors := [2, 3, 43801] }, .lucas { root := 31, primeFactors := [2, 3, 5, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 181, 51853] }, .lucas { root := 11, primeFactors := [2, 3, 29, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 263, 6673] }, .lucas { root := 5, primeFactors := [2, 3, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 13, 2083] }, .lucas { root := 2, primeFactors := [2, 3, 347] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 47, 1028263] }, .lucas { root := 3, primeFactors := [2, 3, 17, 593] }]), by simp⟩

@[expose] noncomputable def bankLeaf64 : PrimeBank := .leaf [97802791, 103641931, 104670301, 107119783, 109932967, 117781303, 119655719, 123152587, 123210869, 127473943, 127540261, 127584187, 129574807, 131500009, 131954891, 133338869]

theorem bankLeaf64_valid : bankLeaf64.Certified := by
  simp only [bankLeaf64, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 29, 79, 1423] }, .lucas { root := 3, primeFactors := [2, 3, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 677] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 49843] }, .lucas { root := 2, primeFactors := [2, 3, 13, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11, 61, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 13, 42709] }, .lucas { root := 6, primeFactors := [2, 3, 3559] }, .lucas { root := 3, primeFactors := [2, 3, 593] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19630217] }, .lucas { root := 3, primeFactors := [2, 29, 191, 443] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 13, 103, 491] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 20525431] }, .lucas { root := 3, primeFactors := [2, 3, 5, 23, 151, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 2800247] }, .lucas { root := 5, primeFactors := [2, 43, 32561] }, .lucas { root := 6, primeFactors := [2, 5, 11, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 317, 67021] }, .lucas { root := 7, primeFactors := [2, 3, 5, 1117] }, .lucas { root := 2, primeFactors := [2, 3, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 29, 53, 461] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 21264031] }, .lucas { root := 3, primeFactors := [2, 3, 5, 191, 1237] }, .lucas { root := 2, primeFactors := [2, 3, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 239, 90359] }, .lucas { root := 11, primeFactors := [2, 45179] }, .lucas { root := 6, primeFactors := [2, 7, 461] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 1826389] }, .lucas { root := 2, primeFactors := [2, 3, 1879] }, .lucas { root := 6, primeFactors := [2, 3, 313] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 233, 56633] }, .lucas { root := 3, primeFactors := [2, 7079] }, .lucas { root := 7, primeFactors := [2, 3539] }, .lucas { root := 2, primeFactors := [2, 29, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 29, 3049] }, .lucas { root := 11, primeFactors := [2, 3, 127] }]), by simp⟩

@[expose] noncomputable def bankLeaf65 : PrimeBank := .leaf [134458717, 134927809, 136151713, 136196659, 139017523, 147833671, 148768021, 150332843, 150650233, 154054921, 155042347, 160257697, 162352033, 163350799, 167017549, 188796709]

theorem bankLeaf65_valid : bankLeaf65.Certified := by
  simp only [bankLeaf65, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 1600699] }, .lucas { root := 3, primeFactors := [2, 3, 11, 79, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 43, 59, 277] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 37, 4259] }, .lucas { root := 2, primeFactors := [2, 2129] }, .lucas { root := 3, primeFactors := [2, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 582037] }, .lucas { root := 2, primeFactors := [2, 3, 7, 13, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 797, 4153] }, .lucas { root := 5, primeFactors := [2, 3, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 4927789] }, .lucas { root := 2, primeFactors := [2, 3, 136883] }, .lucas { root := 2, primeFactors := [2, 89, 769] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 17, 61, 797] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 73, 93607] }, .lucas { root := 3, primeFactors := [2, 3, 15601] }, .lucas { root := 23, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 6277093] }, .lucas { root := 2, primeFactors := [2, 3, 109, 4799] }, .lucas { root := 7, primeFactors := [2, 2399] }, .lucas { root := 11, primeFactors := [2, 11, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 23, 55817] }, .lucas { root := 3, primeFactors := [2, 6977] }, .lucas { root := 3, primeFactors := [2, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 31, 49033] }, .lucas { root := 10, primeFactors := [2, 3, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 1669351] }, .lucas { root := 15, primeFactors := [2, 3, 5, 31, 359] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 23, 73529] }, .lucas { root := 3, primeFactors := [2, 7, 13, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 1237, 1693] }, .lucas { root := 2, primeFactors := [2, 3, 103] }, .lucas { root := 2, primeFactors := [2, 3, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 13918129] }, .lucas { root := 29, primeFactors := [2, 3, 7, 23, 1801] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 61, 149, 577] }]), by simp⟩

@[expose] noncomputable def bankLeaf66 : PrimeBank := .leaf [192062921, 192750517, 193360351, 194086693, 199928467, 203447171, 204245563, 208097431, 208124989, 217138189, 219084919, 221110919, 227876947, 230329301, 236022613, 245001391]

theorem bankLeaf66_valid : bankLeaf66.Certified := by
  simp only [bankLeaf66, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 685939] }, .lucas { root := 3, primeFactors := [2, 3, 11, 19, 547] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 19, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 47, 27427] }, .lucas { root := 5, primeFactors := [2, 3, 7, 653] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 43, 13931] }, .lucas { root := 2, primeFactors := [2, 5, 7, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 23, 557] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 3083, 6599] }, .lucas { root := 2, primeFactors := [2, 23, 67] }, .lucas { root := 13, primeFactors := [2, 3299] }, .lucas { root := 2, primeFactors := [2, 17, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 34040927] }, .lucas { root := 5, primeFactors := [2, 823, 20681] }, .lucas { root := 3, primeFactors := [2, 5, 11, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 131, 52951] }, .lucas { root := 3, primeFactors := [2, 3, 5, 353] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 43, 149, 2707] }, .lucas { root := 2, primeFactors := [2, 3, 11, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 467, 38747] }, .lucas { root := 2, primeFactors := [2, 19373] }, .lucas { root := 2, primeFactors := [2, 29, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 37, 75913] }, .lucas { root := 5, primeFactors := [2, 3, 3163] }, .lucas { root := 3, primeFactors := [2, 3, 17, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 7, 97, 162821] }, .lucas { root := 11, primeFactors := [2, 5, 7, 1163] }, .lucas { root := 5, primeFactors := [2, 7, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 73, 47297] }, .lucas { root := 3, primeFactors := [2, 739] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 2303293] }, .lucas { root := 2, primeFactors := [2, 3, 367, 523] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 79, 5081] }, .lucas { root := 3, primeFactors := [2, 5, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 19, 429827] }, .lucas { root := 2, primeFactors := [2, 214913] }, .lucas { root := 6, primeFactors := [2, 23, 73] }]), by simp⟩

@[expose] noncomputable def bankLeaf67 : PrimeBank := .leaf [245520523, 246505309, 248875867, 249470743, 250590853, 250801819, 261085291, 262209281, 265837681, 267270691, 268088311, 270219331, 272571007, 275296261, 276763169, 278218153]

theorem bankLeaf67_valid : bankLeaf67.Certified := by
  simp only [bankLeaf67, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 293, 3581] }, .lucas { root := 2, primeFactors := [2, 5, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 2934587] }, .lucas { root := 2, primeFactors := [2, 47, 31219] }, .lucas { root := 10, primeFactors := [2, 3, 11, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1013, 13649] }, .lucas { root := 3, primeFactors := [2, 853] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 23, 1807759] }, .lucas { root := 3, primeFactors := [2, 3, 11159] }, .lucas { root := 7, primeFactors := [2, 7, 797] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 41, 169777] }, .lucas { root := 5, primeFactors := [2, 3, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 491, 85133] }, .lucas { root := 2, primeFactors := [2, 21283] }, .lucas { root := 11, primeFactors := [2, 3, 3547] }, .lucas { root := 2, primeFactors := [2, 3, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 8702843] }, .lucas { root := 5, primeFactors := [2, 29, 181, 829] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 127, 1613] }, .lucas { root := 3, primeFactors := [2, 13, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 23, 5351] }, .lucas { root := 11, primeFactors := [2, 5, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 8909023] }, .lucas { root := 3, primeFactors := [2, 3, 1484837] }, .lucas { root := 2, primeFactors := [2, 229, 1621] }, .lucas { root := 2, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 31, 37, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 19, 8317] }, .lucas { root := 6, primeFactors := [2, 3, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 151, 300851] }, .lucas { root := 2, primeFactors := [2, 5, 11, 547] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 4588271] }, .lucas { root := 7, primeFactors := [2, 5, 23, 19949] }, .lucas { root := 2, primeFactors := [2, 4987] }, .lucas { root := 2, primeFactors := [2, 3, 277] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 11, 83, 9473] }, .lucas { root := 3, primeFactors := [2, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 429349] }, .lucas { root := 2, primeFactors := [2, 3, 37, 967] }]), by simp⟩

end OddPerfect.IndexComponent.Size160
