module

public import OddPerfect.IndexRounding
public import OddPerfect.LargeOrderCube
public import OddPerfect.LargeOrderQuadratic
import Mathlib.Tactic.Primality

/-! The nine divisor sums singled out in §4 of Brent, Cohen and te Riele (1991). -/

public section

namespace OddPerfect.BrentHistorical

open IndexComponent

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def factorBank : PrimeBank := .leaf [107904371296112724878570673929, 31744233262482561015455983738381, 5730395978260105084320676489373993, 553788718707122198751861425724478919, 1544162265349605884331755125640208251, 678305068508062949122512002362273110362327, 924347763164985110217631744828987973503604101, 5519538714644097832143693263994602098520609053, 19646107790168407038221172121977104941258765589, 9491935586594867440367391646466925926211879363793, 36799120636249118806979649347305792642377421012261, 115818625571197592034031211634645997677055792367221, 8414791682134527238127200279472177729343785794299499, 14212211472699543013587080904252097825957437375827305902242030561, 138380262291250937488089581658960972202922697970747808890189599600370673, 148467031893746524227485026611653806025492334017387237830406481156482009, 15655651531940748110478789695839379295612322863079251957505662002537883633911, 8746781693759220836960579574321515651597080180989131549946798109975686695403479, 1038248742632101482564989131468295652419856857036517004815396175149317316827547313, 2795470346154518601095703317279482175240316831812233463788382148771684556965122038863701628739457]

theorem factorBank_valid : factorBank.Certified := by
  simp only [factorBank, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 41, 47, 929, 26252443126639745321] }, .lucas { root := 3, primeFactors := [2, 5, 223, 158443, 18575127997] }, .lucas { root := 3, primeFactors := [2, 3, 26407] }, .lucas { root := 5, primeFactors := [2, 3, 163] }, .lucas { root := 2, primeFactors := [2, 3, 17, 91054549] }, .lucas { root := 2, primeFactors := [2, 3, 13, 29, 6709] }, .lucas { root := 2, primeFactors := [2, 3, 13, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 19, 37, 619, 4150110197, 292959771852437] }, .lucas { root := 2, primeFactors := [2, 103, 677, 14879] }, .lucas { root := 7, primeFactors := [2, 43, 173] }, .lucas { root := 2, primeFactors := [2, 13, 5633841766393] }, .lucas { root := 10, primeFactors := [2, 3, 7, 11178257473] }, .lucas { root := 5, primeFactors := [2, 3, 107, 60457] }, .lucas { root := 13, primeFactors := [2, 3, 11, 229] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 23, 47, 251, 491, 3067, 38352282737, 45709739311] }, .lucas { root := 2, primeFactors := [2, 3, 7, 73] }, .lucas { root := 3, primeFactors := [2, 43, 1123, 49639] }, .lucas { root := 2, primeFactors := [2, 3, 11, 17] }, .lucas { root := 3, primeFactors := [2, 3, 8273] }, .lucas { root := 3, primeFactors := [2, 11, 47] }, .lucas { root := 3, primeFactors := [2, 3, 5, 23, 619, 107021] }, .lucas { root := 7, primeFactors := [2, 5, 5351] }, .lucas { root := 11, primeFactors := [2, 5, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 23, 31, 241, 769, 799950062123, 2619499501161329] }, .lucas { root := 2, primeFactors := [2, 67, 44087, 135409] }, .lucas { root := 5, primeFactors := [2, 7, 47, 67] }, .lucas { root := 11, primeFactors := [2, 3, 7, 13, 31] }, .lucas { root := 3, primeFactors := [2, 6689, 24475813847] }, .lucas { root := 3, primeFactors := [2, 11, 19] }, .lucas { root := 5, primeFactors := [2, 11, 307, 3623899] }, .lucas { root := 2, primeFactors := [2, 3, 29, 59, 353] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 23, 268549959191235805970740021850471] }, .lucas { root := 11, primeFactors := [2, 5, 223, 2411, 49948565188185652450695899] }, .lucas { root := 6, primeFactors := [2, 5, 241] }, .lucas { root := 6, primeFactors := [2, 7, 41, 251, 200383, 9779839, 176906921] }, .lucas { root := 5, primeFactors := [2, 3, 7, 13, 367] }, .lucas { root := 3, primeFactors := [2, 3, 719, 2267] }, .lucas { root := 2, primeFactors := [2, 11, 103] }, .lucas { root := 3, primeFactors := [2, 5, 4422673] }, .lucas { root := 5, primeFactors := [2, 3, 30713] }, .lucas { root := 3, primeFactors := [2, 11, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 47, 24641927, 177779852693, 235310853980756251777] }, .lucas { root := 5, primeFactors := [2, 37, 53, 61, 103] }, .lucas { root := 2, primeFactors := [2, 13, 29, 117891149] }, .lucas { root := 2, primeFactors := [2, 29, 1016303] }, .lucas { root := 5, primeFactors := [2, 7, 229, 317] }, .lucas { root := 10, primeFactors := [2, 3, 13, 1019, 3673, 13007, 968267] }, .lucas { root := 5, primeFactors := [2, 3, 17] }, .lucas { root := 5, primeFactors := [2, 7, 929] }, .lucas { root := 2, primeFactors := [2, 13, 167, 223] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37, 43, 277, 75991, 3623401, 590496293765716018743917] }, .lucas { root := 11, primeFactors := [2, 3, 5, 17, 149] }, .lucas { root := 13, primeFactors := [2, 3, 5, 11, 61] }, .lucas { root := 2, primeFactors := [2, 7, 11205769, 30002411, 62727983] }, .lucas { root := 31, primeFactors := [2, 3, 7, 66701] }, .lucas { root := 3, primeFactors := [2, 5, 23, 29] }, .lucas { root := 2, primeFactors := [2, 5, 271, 11071] }, .lucas { root := 3, primeFactors := [2, 3, 5, 41] }, .lucas { root := 5, primeFactors := [2, 31363991] }, .lucas { root := 7, primeFactors := [2, 5, 7, 448057] }, .lucas { root := 15, primeFactors := [2, 3, 7, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 43, 10696780454736623705704831906966283136667847] }, .lucas { root := 5, primeFactors := [2, 31, 223, 1949, 396958120438631349436110173928385279] }, .lucas { root := 2, primeFactors := [2, 487] }, .lucas { root := 6, primeFactors := [2, 3, 2026029917867, 10884947314339212627413] }, .lucas { root := 2, primeFactors := [2, 71, 14267816323] }, .lucas { root := 2, primeFactors := [2, 3, 2377969387] }, .lucas { root := 3, primeFactors := [2, 3, 13, 3499, 8713] }, .lucas { root := 2, primeFactors := [2, 3, 11, 53] }, .lucas { root := 5, primeFactors := [2, 3, 11] }, .lucas { root := 2, primeFactors := [2, 59, 1903670203, 24228281789] }, .lucas { root := 2, primeFactors := [2, 3, 7, 37, 73, 97, 173] }, .lucas { root := 2, primeFactors := [2, 23, 263350889] }, .lucas { root := 3, primeFactors := [2, 32918861] }, .lucas { root := 2, primeFactors := [2, 5, 13, 126611] }, .lucas { root := 2, primeFactors := [2, 5, 11, 1151] }, .lucas { root := 17, primeFactors := [2, 5, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 17, 23, 73, 987559, 5334512431, 2512556164876682876048527] }, .lucas { root := 3, primeFactors := [2, 3, 11, 13, 1151] }, .lucas { root := 17, primeFactors := [2, 5, 23] }, .lucas { root := 3, primeFactors := [2, 3, 5, 13, 281, 48677] }, .lucas { root := 2, primeFactors := [2, 43, 283] }, .lucas { root := 3, primeFactors := [2, 3, 11, 13, 317, 38749, 238401360478859] }, .lucas { root := 2, primeFactors := [2, 3, 3229] }, .lucas { root := 6, primeFactors := [2, 3, 269] }, .lucas { root := 2, primeFactors := [2, 8117, 19249, 762913] }, .lucas { root := 2, primeFactors := [2, 2029] }, .lucas { root := 2, primeFactors := [2, 3, 13] }, .lucas { root := 7, primeFactors := [2, 3, 401] }, .lucas { root := 5, primeFactors := [2, 3, 883] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 173, 50909, 8853328487, 2536099551894136063832432150881] }, .lucas { root := 2, primeFactors := [2, 11, 13, 89] }, .lucas { root := 5, primeFactors := [2, 4426664243] }, .lucas { root := 2, primeFactors := [2, 7, 11, 13, 201011] }, .lucas { root := 2, primeFactors := [2, 5, 20101] }, .lucas { root := 6, primeFactors := [2, 3, 5, 67] }, .lucas { root := 19, primeFactors := [2, 3, 5, 11, 53, 1627111, 5569796450417101237] }, .lucas { root := 3, primeFactors := [2, 3, 5, 101, 179] }, .lucas { root := 2, primeFactors := [2, 3, 2269, 501383, 135998063] }, .lucas { root := 2, primeFactors := [2, 3, 7] }, .lucas { root := 5, primeFactors := [2, 7, 59, 607] }, .lucas { root := 5, primeFactors := [2, 17, 229, 17467] }, .lucas { root := 3, primeFactors := [2, 3, 41, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 13, 37, 15359, 18712366476192793619, 403326515210280865961] }, .lucas { root := 11, primeFactors := [2, 7, 1097] }, .lucas { root := 3, primeFactors := [2, 137] }, .lucas { root := 2, primeFactors := [2, 41, 223, 13467947, 75981629] }, .lucas { root := 2, primeFactors := [2, 61, 101, 1093] }, .lucas { root := 5, primeFactors := [2, 3, 7, 13] }, .lucas { root := 2, primeFactors := [2, 181, 104947] }, .lucas { root := 5, primeFactors := [2, 3, 17491] }, .lucas { root := 3, primeFactors := [2, 3, 5, 11, 53] }, .lucas { root := 3, primeFactors := [2, 5, 71, 69615661, 2040006179] }, .lucas { root := 2, primeFactors := [2, 3, 5, 29, 40009] }, .lucas { root := 11, primeFactors := [2, 3, 1667] }, .lucas { root := 2, primeFactors := [2, 7, 17] }, .lucas { root := 2, primeFactors := [2, 7, 145714727] }, .lucas { root := 5, primeFactors := [2, 61, 1194383] }, .lucas { root := 5, primeFactors := [2, 7, 85313] }, .lucas { root := 3, primeFactors := [2, 31, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 29, 43, 3992722171, 15817679615533, 24510311847494380249747] }, .lucas { root := 7, primeFactors := [2, 3, 5, 17, 37, 457, 463] }, .lucas { root := 2, primeFactors := [2, 3, 109, 523, 971, 23813] }, .lucas { root := 2, primeFactors := [2, 5953] }, .lucas { root := 7, primeFactors := [2, 3, 31] }, .lucas { root := 2, primeFactors := [2, 3, 53, 26839, 473981, 6058909333] }, .lucas { root := 3, primeFactors := [2, 3, 7, 71] }, .lucas { root := 2, primeFactors := [2, 5, 13, 1823] }, .lucas { root := 5, primeFactors := [2, 911] }, .lucas { root := 6, primeFactors := [2, 3, 7, 29, 53, 15643] }, .lucas { root := 5, primeFactors := [2, 3, 11, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 47, 3851, 10831, 383159460743507771, 622373909205991486504613] }, .lucas { root := 2, primeFactors := [2, 5, 7, 11] }, .lucas { root := 7, primeFactors := [2, 3, 5, 19] }, .lucas { root := 10, primeFactors := [2, 5, 7, 9001, 18049, 33692839] }, .lucas { root := 7, primeFactors := [2, 3, 5] }, .lucas { root := 13, primeFactors := [2, 3, 47] }, .lucas { root := 13, primeFactors := [2, 3, 23, 29, 8419] }, .lucas { root := 3, primeFactors := [2, 3, 23, 61] }, .lucas { root := 2, primeFactors := [2, 67, 152140111, 15264158089069] }, .lucas { root := 3, primeFactors := [2, 3, 5, 499, 10163] }, .lucas { root := 2, primeFactors := [2, 5081] }, .lucas { root := 3, primeFactors := [2, 5, 127] }, .lucas { root := 6, primeFactors := [2, 3, 7, 43, 47, 113, 88411] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7, 421] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 23, 55633, 2715959, 25559841298085939541414270300679949547543014145811] }, .lucas { root := 5, primeFactors := [2, 3, 19, 61] }, .lucas { root := 7, primeFactors := [2, 7, 419, 463] }, .lucas { root := 2, primeFactors := [2, 3, 5, 62754317466697, 13576670806567880410538113673769391] }, .lucas { root := 10, primeFactors := [2, 3, 167, 34703, 50131] }, .lucas { root := 5, primeFactors := [2, 17351] }, .lucas { root := 11, primeFactors := [2, 5, 347] }, .lucas { root := 2, primeFactors := [2, 3, 5, 557] }, .lucas { root := 6, primeFactors := [2, 3, 5, 17, 47, 151, 2581583, 85469919035874306767] }, .lucas { root := 5, primeFactors := [2, 1290791] }, .lucas { root := 13, primeFactors := [2, 5, 29, 4451] }, .lucas { root := 2, primeFactors := [2, 5, 89] }, .lucas { root := 5, primeFactors := [2, 7, 17, 73, 28837, 170593860757] }, .lucas { root := 2, primeFactors := [2, 3, 89] }, .lucas { root := 2, primeFactors := [2, 3, 11, 6911, 187003] }, .lucas { root := 7, primeFactors := [2, 5, 691] }, .lucas { root := 3, primeFactors := [2, 3, 3463] }, .lucas { root := 3, primeFactors := [2, 3, 577] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 23, 43, 53, 131, 191, 322217029512509, 20465806001860985759597997077860305804806229959] }, .lucas { root := 3, primeFactors := [2, 13, 109, 4153, 13688527] }, .lucas { root := 5, primeFactors := [2, 3, 173] }, .lucas { root := 3, primeFactors := [2, 3, 83, 27487] }, .lucas { root := 3, primeFactors := [2, 3, 509] }, .lucas { root := 7, primeFactors := [2, 7, 17, 23, 101, 1180661, 22744193761, 81088263590357750160331] }, .lucas { root := 2, primeFactors := [2, 5, 13, 19, 239] }, .lucas { root := 17, primeFactors := [2, 3, 5, 367, 43037] }, .lucas { root := 2, primeFactors := [2, 7, 29, 53] }, .lucas { root := 7, primeFactors := [2, 3, 5, 13, 23102069398962321983] }, .lucas { root := 5, primeFactors := [2, 19, 1531, 516709, 768503891] }, .lucas { root := 2, primeFactors := [2, 3, 5, 17] }, .lucas { root := 2, primeFactors := [2, 3, 31, 463] }, .lucas { root := 2, primeFactors := [2, 5, 7, 11, 307, 3251] }, .lucas { root := 6, primeFactors := [2, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 31, 37, 47, 3733, 856813, 107630343513557369168917326338680943116090829380083891391] }, .lucas { root := 2, primeFactors := [2, 3, 311] }, .lucas { root := 23, primeFactors := [2, 3, 11, 6491] }, .lucas { root := 2, primeFactors := [2, 5, 11, 59] }, .lucas { root := 6, primeFactors := [2, 3, 5, 79, 35863103, 483192253738001, 2620707511862571813949155072049] }, .lucas { root := 5, primeFactors := [2, 11, 1630141] }, .lucas { root := 2, primeFactors := [2, 3, 5, 101, 269] }, .lucas { root := 6, primeFactors := [2, 5, 241596126869] }, .lucas { root := 2, primeFactors := [2, 46679, 1293923] }, .lucas { root := 17, primeFactors := [2, 23339] }, .lucas { root := 2, primeFactors := [2, 7, 1667] }, .lucas { root := 2, primeFactors := [2, 7, 17] }, .lucas { root := 2, primeFactors := [2, 7, 29, 3187] }, .lucas { root := 2, primeFactors := [2, 3, 59] }, .lucas { root := 11, primeFactors := [2, 3, 6960077, 2614821318969295859671] }, .lucas { root := 2, primeFactors := [2, 23, 75653] }, .lucas { root := 2, primeFactors := [2, 18913] }, .lucas { root := 7, primeFactors := [2, 3, 197] }, .lucas { root := 3, primeFactors := [2, 3, 5, 13, 19, 2528531, 139558253777] }, .lucas { root := 2, primeFactors := [2, 5, 149, 1697] }, .lucas { root := 3, primeFactors := [2, 53] }, .lucas { root := 3, primeFactors := [2, 127, 68680243] }, .lucas { root := 5, primeFactors := [2, 3, 3815569] }, .lucas { root := 11, primeFactors := [2, 3, 26497] }, .lucas { root := 5, primeFactors := [2, 3, 23] }]),
    (OddPerfect.prime_of_largeOrderCheck (b := 15273090577508251900774578837404659312833834356307634762584984262143084161639) (factors := [(307291954706395069856555953236635167909099113106281002943128530717, 1)]) (by simp only [List.forall_mem_cons]; exact ⟨(OddPerfect.prime_of_largeOrderPlusCheck (D := 2) (x := 223754322779656011347668842377083993616596268576619780497) (y := 158218198957298349459881872258693482837644320190122680252) (factors := [(4152593982518852295358864232927502269041879906841635174907142307, 1)]) (by simp only [List.forall_mem_cons]; exact ⟨(OddPerfect.prime_of_largeOrderCheck (b := 3680839598478000707046493135392586824700763418175096542763357424) (factors := [(170069820011562330111444762692491777469260856911789, 1)]) (by simp only [List.forall_mem_cons]; exact ⟨(OddPerfect.prime_of_largeOrderCheck (b := 112390939111281579041065661318292344082296469060528) (factors := [(57910460877304172782716793367851429211821979, 1)]) (by simp only [List.forall_mem_cons]; exact ⟨(OddPerfect.prime_of_largeOrderCheck (b := 25187600974542358920509860012491352951705292) (factors := [(2771621158858012713449011, 1)]) (by simp only [List.forall_mem_cons]; exact ⟨(OddPerfect.prime_of_largeOrderCheck (b := 1325487489024097198279132) (factors := [(55769709131369, 1)]) (by simp only [List.forall_mem_cons]; exact ⟨(OddPerfect.prime_of_largeOrderCheck (b := 19541641855406) (factors := [(36105499, 1)]) (by simp only [List.forall_mem_cons]; exact ⟨(OddPerfect.prime_of_largeOrderCubeCheck (b := 2630734) (factors := [(13, 3)]) (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by simp⟩) (by decide +kernel)), by simp⟩) (by decide +kernel)), by simp⟩) (by decide +kernel)), by simp⟩) (by decide +kernel)), by simp⟩) (by decide +kernel)), by simp⟩) (by decide +kernel)), by simp⟩) (by decide +kernel)), by simp⟩) (by decide +kernel)),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 31, 241, 769, 268904904532206419854387, 2830834580187035673391014420311757899345542652903] }, .lucas { root := 2, primeFactors := [2, 3, 1437511, 10392380554236007] }, .lucas { root := 6, primeFactors := [2, 3, 5, 47917] }, .lucas { root := 5, primeFactors := [2, 3, 11] }, .lucas { root := 3, primeFactors := [2, 3, 1732063425706001] }, .lucas { root := 6, primeFactors := [2, 5, 1459, 3359, 176713] }, .lucas { root := 3, primeFactors := [2, 3] }, .lucas { root := 11, primeFactors := [2, 23, 73] }, .lucas { root := 10, primeFactors := [2, 3, 37, 199] }, .lucas { root := 5, primeFactors := [2, 23, 257, 5417, 6473, 5125949, 57185279, 5751241819, 4050782646149] }, .lucas { root := 3, primeFactors := [2, 677] }, .lucas { root := 3, primeFactors := [2, 809] }, .lucas { root := 2, primeFactors := [2, 53, 24179] }, .lucas { root := 2, primeFactors := [2, 7, 11, 157] }, .lucas { root := 7, primeFactors := [2, 59, 484621] }, .lucas { root := 6, primeFactors := [2, 3, 5, 41, 197] }, .lucas { root := 3, primeFactors := [2, 3, 7, 2383, 8209] }, .lucas { root := 5, primeFactors := [2, 3, 397] }, .lucas { root := 7, primeFactors := [2, 3, 19] }, .lucas { root := 2, primeFactors := [2, 7, 29, 4988648579] }, .lucas { root := 2, primeFactors := [2, 163, 269, 349] }]),
    (OddPerfect.prime_of_largeOrderCubeCheck (b := 513758274556822722305242100848188671578485205561740739525118949993477889023819557) (factors := [(11779447662431, 1), (35596201, 1), (4330633, 1)]) (by simp only [List.forall_mem_cons]; exact ⟨(OddPerfect.prime_of_largeOrderCubeCheck (b := 3652226755784) (factors := [(128657, 1)]) (by simp only [List.forall_mem_cons]; exact ⟨(OddPerfect.prime_of_largeOrderCheck (b := 89068) (factors := [(43, 1), (17, 1)]) (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by norm_num, by simp⟩) (by decide +kernel)), by simp⟩) (by decide +kernel)), (OddPerfect.prime_of_largeOrderCubeCheck (b := 5199494) (factors := [(1447, 1)]) (by simp only [List.forall_mem_cons]; exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 241] }]), by simp⟩) (by decide +kernel)), (OddPerfect.prime_of_largeOrderCheck (b := 2293206) (factors := [(9497, 1)]) (by simp only [List.forall_mem_cons]; exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 1187] }, .lucas { root := 2, primeFactors := [2, 593] }]), by simp⟩) (by decide +kernel)), by simp⟩) (by decide +kernel)),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 173, 2551, 4021, 35677, 5219271593, 26163485659679, 1545323184116671, 61067471745406917391, 26768941395212633337691] }, .lucas { root := 6, primeFactors := [2, 3, 5, 17] }, .lucas { root := 2, primeFactors := [2, 3, 5, 67] }, .lucas { root := 2, primeFactors := [2, 3, 991] }, .lucas { root := 3, primeFactors := [2, 17, 67, 572791] }, .lucas { root := 6, primeFactors := [2, 3, 5, 61, 313] }, .lucas { root := 7, primeFactors := [2, 733829, 17826691] }, .lucas { root := 2, primeFactors := [2, 383, 479] }, .lucas { root := 7, primeFactors := [2, 3, 5, 7, 67, 181] }, .lucas { root := 6, primeFactors := [2, 3, 5, 7, 499, 14746857373] }, .lucas { root := 5, primeFactors := [2, 3, 13, 19, 1658441] }, .lucas { root := 3, primeFactors := [2, 5, 7, 5923] }, .lucas { root := 2, primeFactors := [2, 3, 7, 47] }, .lucas { root := 3, primeFactors := [2, 3, 5, 149, 13661626788681637] }, .lucas { root := 5, primeFactors := [2, 3, 653, 1743443949551] }, .lucas { root := 13, primeFactors := [2, 5, 23, 59, 25695563] }, .lucas { root := 2, primeFactors := [2, 19, 59, 73, 157] }, .lucas { root := 2, primeFactors := [2, 3, 5, 467, 99577, 130817, 146679641] }, .lucas { root := 5, primeFactors := [2, 3, 461] }, .lucas { root := 3, primeFactors := [2, 7, 73] }, .lucas { root := 3, primeFactors := [2, 5, 3666991] }, .lucas { root := 3, primeFactors := [2, 3, 5, 31, 3943] }, .lucas { root := 3, primeFactors := [2, 3, 73] }]), by simp⟩

structure FactorRecord where
  base : ℕ
  exponent : ℕ
  factors : List ℕ

/-- The ordering and exponent pairs follow cases (i) through (ix) of the paper. -/
@[expose] def records : List FactorRecord := [
  ⟨3221, 42, [138380262291250937488089581658960972202922697970747808890189599600370673, 15655651531940748110478789695839379295612322863079251957505662002537883633911]⟩,
  ⟨7, 172, [9491935586594867440367391646466925926211879363793, 2795470346154518601095703317279482175240316831812233463788382148771684556965122038863701628739457]⟩,
  ⟨612067, 22, [19646107790168407038221172121977104941258765589, 1038248742632101482564989131468295652419856857036517004815396175149317316827547313]⟩,
  ⟨3169, 36, [31744233262482561015455983738381, 924347763164985110217631744828987973503604101, 36799120636249118806979649347305792642377421012261]⟩,
  ⟨467, 46, [107904371296112724878570673929, 678305068508062949122512002362273110362327, 8414791682134527238127200279472177729343785794299499]⟩,
  ⟨191, 46, [5730395978260105084320676489373993, 148467031893746524227485026611653806025492334017387237830406481156482009]⟩,
  ⟨36389, 22, [1544162265349605884331755125640208251, 14212211472699543013587080904252097825957437375827305902242030561]⟩,
  ⟨191, 42, [5519538714644097832143693263994602098520609053, 115818625571197592034031211634645997677055792367221]⟩,
  ⟨3, 240, [553788718707122198751861425724478919, 8746781693759220836960579574321515651597080180989131549946798109975686695403479]⟩]

private theorem checked_records : records.all (fun v =>
    decide (SupportSieve.geomValue v.base (v.exponent+1) = v.factors.prod) &&
    v.factors.all factorBank.contains) = true := by decide +kernel

/-- Each recorded product is the entire geometric sum, and every displayed factor is prime. -/
theorem factorization_of_mem {v : FactorRecord} (hv : v ∈ records) :
    SupportSieve.geomValue v.base (v.exponent+1) = v.factors.prod ∧ ∀ p ∈ v.factors, p.Prime := by
  have h := List.all_eq_true.mp checked_records v hv
  simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at h
  exact ⟨h.1, fun p hp => factorBank.prime_of_contains factorBank_valid (h.2 p hp)⟩

private noncomputable def state_i : State := (root.extend 3221 42)

private theorem valid_i {N : ℕ} (hN : N.Perfect) (h3221 : 43 ∣ N.factorization 3221+1) : Valid state_i N := by
  have hstep0 := extend_valid (e := 42) (root_valid N) hN.2.ne' (by norm_num : Nat.Prime 3221) (by decide +kernel) h3221
  exact hstep0

/-- The rounded lower bound for published case (i). -/
theorem size_i {N : ℕ} (ho : Odd N) (hN : N.Perfect) (h3221 : 43 ∣ N.factorization 3221+1) : 10^370 < N := by
  by_contra! hx
  exact checkRound_false (valid_i hN h3221) ho hN hx factorBank factorBank_valid
    [(138380262291250937488089581658960972202922697970747808890189599600370673, 1), (15655651531940748110478789695839379295612322863079251957505662002537883633911, 1)] (by decide +kernel : state_i.checkRound factorBank (10^370) 138380262291250937488089581658960972202922697970747808890189599600370673 [(138380262291250937488089581658960972202922697970747808890189599600370673, 1), (15655651531940748110478789695839379295612322863079251957505662002537883633911, 1)] = true)

private noncomputable def state_ii : State := (root.extend 7 172)

private theorem valid_ii {N : ℕ} (hN : N.Perfect) (h7 : 173 ∣ N.factorization 7+1) : Valid state_ii N := by
  have hstep0 := extend_valid (e := 172) (root_valid N) hN.2.ne' (by norm_num : Nat.Prime 7) (by decide +kernel) h7
  exact hstep0

/-- The rounded lower bound for published case (ii). -/
theorem size_ii {N : ℕ} (ho : Odd N) (hN : N.Perfect) (h7 : 173 ∣ N.factorization 7+1) : 10^339 < N := by
  by_contra! hx
  exact checkRound_false (valid_ii hN h7) ho hN hx factorBank factorBank_valid
    [(9491935586594867440367391646466925926211879363793, 1), (2795470346154518601095703317279482175240316831812233463788382148771684556965122038863701628739457, 1)] (by decide +kernel : state_ii.checkRound factorBank (10^339) 2795470346154518601095703317279482175240316831812233463788382148771684556965122038863701628739457 [(9491935586594867440367391646466925926211879363793, 1), (2795470346154518601095703317279482175240316831812233463788382148771684556965122038863701628739457, 1)] = true)

private noncomputable def state_iii : State := (root.extend 612067 22)

private theorem valid_iii {N : ℕ} (hN : N.Perfect) (h612067 : 23 ∣ N.factorization 612067+1) : Valid state_iii N := by
  have hstep0 := extend_valid (e := 22) (root_valid N) hN.2.ne' (by norm_num : Nat.Prime 612067) (by decide +kernel) h612067
  exact hstep0

/-- The rounded lower bound for published case (iii). -/
theorem size_iii {N : ℕ} (ho : Odd N) (hN : N.Perfect) (h612067 : 23 ∣ N.factorization 612067+1) : 10^300 < N := by
  by_contra! hx
  exact checkRound_false (valid_iii hN h612067) ho hN hx factorBank factorBank_valid
    [(19646107790168407038221172121977104941258765589, 1), (1038248742632101482564989131468295652419856857036517004815396175149317316827547313, 1)] (by decide +kernel : state_iii.checkRound factorBank (10^300) 1038248742632101482564989131468295652419856857036517004815396175149317316827547313 [(19646107790168407038221172121977104941258765589, 1), (1038248742632101482564989131468295652419856857036517004815396175149317316827547313, 1)] = true)

private noncomputable def state_iv : State := (root.extend 3169 36)

private theorem valid_iv {N : ℕ} (hN : N.Perfect) (h3169 : 37 ∣ N.factorization 3169+1) : Valid state_iv N := by
  have hstep0 := extend_valid (e := 36) (root_valid N) hN.2.ne' (by norm_num : Nat.Prime 3169) (by decide +kernel) h3169
  exact hstep0

/-- The rounded lower bound for published case (iv). -/
theorem size_iv {N : ℕ} (ho : Odd N) (hN : N.Perfect) (h3169 : 37 ∣ N.factorization 3169+1) : 10^328 < N := by
  by_contra! hx
  exact checkRound_false (valid_iv hN h3169) ho hN hx factorBank factorBank_valid
    [(31744233262482561015455983738381, 1), (924347763164985110217631744828987973503604101, 1), (36799120636249118806979649347305792642377421012261, 1)] (by decide +kernel : state_iv.checkRound factorBank (10^328) 36799120636249118806979649347305792642377421012261 [(31744233262482561015455983738381, 1), (924347763164985110217631744828987973503604101, 1), (36799120636249118806979649347305792642377421012261, 1)] = true)

private noncomputable def state_v : State := (((root.extend 7 4).extend 2801 1).extend 467 46)

private theorem valid_v {N : ℕ} (hN : N.Perfect) (h7 : 5 ∣ N.factorization 7+1) (h2801 : 2 ∣ N.factorization 2801+1) (h467 : 47 ∣ N.factorization 467+1) : Valid state_v N := by
  have hstep0 := extend_valid (e := 4) (root_valid N) hN.2.ne' (by norm_num : Nat.Prime 7) (by decide +kernel) h7
  have hstep1 := extend_valid (e := 1) hstep0 hN.2.ne' (by norm_num : Nat.Prime 2801) (by decide +kernel) h2801
  have hstep2 := extend_valid (e := 46) hstep1 hN.2.ne' (by norm_num : Nat.Prime 467) (by decide +kernel) h467
  exact hstep2

/-- The rounded lower bound for published case (v). -/
theorem size_v {N : ℕ} (ho : Odd N) (hN : N.Perfect) (h7 : 5 ∣ N.factorization 7+1) (h2801 : 2 ∣ N.factorization 2801+1) (h467 : 47 ∣ N.factorization 467+1) : 10^375 < N := by
  by_contra! hx
  exact checkRound_false (valid_v hN h7 h2801 h467) ho hN hx factorBank factorBank_valid
    [(107904371296112724878570673929, 1), (678305068508062949122512002362273110362327, 1), (8414791682134527238127200279472177729343785794299499, 1)] (by decide +kernel : state_v.checkRound factorBank (10^375) 1 [(107904371296112724878570673929, 1), (678305068508062949122512002362273110362327, 1), (8414791682134527238127200279472177729343785794299499, 1)] = true)

private noncomputable def state_vi : State := (((root.extend 13 4).extend 30941 1).extend 191 46)

private theorem valid_vi {N : ℕ} (hN : N.Perfect) (h13 : 5 ∣ N.factorization 13+1) (h30941 : 2 ∣ N.factorization 30941+1) (h191 : 47 ∣ N.factorization 191+1) : Valid state_vi N := by
  have hstep0 := extend_valid (e := 4) (root_valid N) hN.2.ne' (by norm_num : Nat.Prime 13) (by decide +kernel) h13
  have hstep1 := extend_valid (e := 1) hstep0 hN.2.ne' (by norm_num : Nat.Prime 30941) (by decide +kernel) h30941
  have hstep2 := extend_valid (e := 46) hstep1 hN.2.ne' (by norm_num : Nat.Prime 191) (by decide +kernel) h191
  exact hstep2

/-- The rounded lower bound for published case (vi). -/
theorem size_vi {N : ℕ} (ho : Odd N) (hN : N.Perfect) (h13 : 5 ∣ N.factorization 13+1) (h30941 : 2 ∣ N.factorization 30941+1) (h191 : 47 ∣ N.factorization 191+1) : 10^325 < N := by
  by_contra! hx
  exact checkRound_false (valid_vi hN h13 h30941 h191) ho hN hx factorBank factorBank_valid
    [(5730395978260105084320676489373993, 1), (148467031893746524227485026611653806025492334017387237830406481156482009, 1)] (by decide +kernel : state_vi.checkRound factorBank (10^325) 1 [(5730395978260105084320676489373993, 1), (148467031893746524227485026611653806025492334017387237830406481156482009, 1)] = true)

private noncomputable def state_vii : State := (((root.extend 3 18).extend 363889 1).extend 36389 22)

private theorem valid_vii {N : ℕ} (hN : N.Perfect) (h3 : 19 ∣ N.factorization 3+1) (h363889 : 2 ∣ N.factorization 363889+1) (h36389 : 23 ∣ N.factorization 36389+1) : Valid state_vii N := by
  have hstep0 := extend_valid (e := 18) (root_valid N) hN.2.ne' (by norm_num : Nat.Prime 3) (by decide +kernel) h3
  have hstep1 := extend_valid (e := 1) hstep0 hN.2.ne' (by norm_num : Nat.Prime 363889) (by decide +kernel) h363889
  have hstep2 := extend_valid (e := 22) hstep1 hN.2.ne' (by norm_num : Nat.Prime 36389) (by decide +kernel) h36389
  exact hstep2

/-- The rounded lower bound for published case (vii). -/
theorem size_vii {N : ℕ} (ho : Odd N) (hN : N.Perfect) (h3 : 19 ∣ N.factorization 3+1) (h363889 : 2 ∣ N.factorization 363889+1) (h36389 : 23 ∣ N.factorization 36389+1) : 10^319 < N := by
  by_contra! hx
  exact checkRound_false (valid_vii hN h3 h363889 h36389) ho hN hx factorBank factorBank_valid
    [(1544162265349605884331755125640208251, 1), (14212211472699543013587080904252097825957437375827305902242030561, 1)] (by decide +kernel : state_vii.checkRound factorBank (10^319) 1 [(1544162265349605884331755125640208251, 1), (14212211472699543013587080904252097825957437375827305902242030561, 1)] = true)

private noncomputable def state_viii : State := (((root.extend 13 4).extend 30941 1).extend 191 42)

private theorem valid_viii {N : ℕ} (hN : N.Perfect) (h13 : 5 ∣ N.factorization 13+1) (h30941 : 2 ∣ N.factorization 30941+1) (h191 : 43 ∣ N.factorization 191+1) : Valid state_viii N := by
  have hstep0 := extend_valid (e := 4) (root_valid N) hN.2.ne' (by norm_num : Nat.Prime 13) (by decide +kernel) h13
  have hstep1 := extend_valid (e := 1) hstep0 hN.2.ne' (by norm_num : Nat.Prime 30941) (by decide +kernel) h30941
  have hstep2 := extend_valid (e := 42) hstep1 hN.2.ne' (by norm_num : Nat.Prime 191) (by decide +kernel) h191
  exact hstep2

private noncomputable def state_ix : State := (root.extend 3 240)

private theorem valid_ix {N : ℕ} (hN : N.Perfect) (h3 : 241 ∣ N.factorization 3+1) : Valid state_ix N := by
  have hstep0 := extend_valid (e := 240) (root_valid N) hN.2.ne' (by norm_num : Nat.Prime 3) (by decide +kernel) h3
  exact hstep0

/-- The rounded lower bound for published case (ix). -/
theorem size_ix {N : ℕ} (ho : Odd N) (hN : N.Perfect) (h3 : 241 ∣ N.factorization 3+1) : 10^343 < N := by
  by_contra! hx
  exact checkRound_false (valid_ix hN h3) ho hN hx factorBank factorBank_valid
    [(553788718707122198751861425724478919, 1), (8746781693759220836960579574321515651597080180989131549946798109975686695403479, 1)] (by decide +kernel : state_ix.checkRound factorBank (10^343) 1 [(553788718707122198751861425724478919, 1), (8746781693759220836960579574321515651597080180989131549946798109975686695403479, 1)] = true)

/-- In case (viii), the special prime 30941 forces at least four copies of 3.
Four copies force the already excluded 11, six force 1093, and eight suffice directly. -/
theorem size_viii {N : ℕ} (ho : Odd N) (hN : N.Perfect) (h11 : ¬11∣N)
    (h13 : 5∣N.factorization 13+1) (h30941 : 2∣N.factorization 30941+1)
    (h191 : 43∣N.factorization 191+1) : 10^300 < N := by
  have hv := valid_viii hN h13 h30941 h191
  have hU := joined_dvd hv hN
  have hsp : Odd (N.factorization 30941) := hv.special (by decide +kernel)
  obtain ⟨q, _, _, _, heven⟩ := euler_exponents ho hN
  have hq : q=30941 := by
    by_contra! h
    have := Nat.even_iff.mp (heven _ h.symm)
    have := Nat.odd_iff.mp hsp
    omega
  subst q
  let a : ℕ := 5519538714644097832143693263994602098520609053
  let b : ℕ := 115818625571197592034031211634645997677055792367221
  have square (p : ℕ) (hp : p.Prime) (hne : p≠30941) (hdiv : p∣state_viii.joined) : p^2∣N := by
    have pos := (hp.dvd_iff_one_le_factorization hN.2.ne').mp (hdiv.trans hU)
    have even := Nat.even_iff.mp (heven p hne)
    exact (hp.pow_dvd_iff_le_factorization hN.2.ne').mpr (by omega)
  have ha := square a (factorBank.prime_of_contains factorBank_valid (by decide +kernel))
    (by decide +kernel) (by decide +kernel)
  have hb := square b (factorBank.prime_of_contains factorBank_valid (by decide +kernel))
    (by decide +kernel) (by decide +kernel)
  let L := (state_viii.joined.lcm (a^2)).lcm (b^2)
  have hL : L∣N := Nat.lcm_dvd (Nat.lcm_dvd hU ha) hb
  have h3 : Nat.Prime 3 := by decide
  have hlo : 4 ≤ N.factorization 3 := (h3.pow_dvd_iff_le_factorization hN.2.ne').mp
    ((show 3^4∣state_viii.joined by decide +kernel).trans hU)
  by_cases h8 : 8 ≤ N.factorization 3
  · have hbound : L.lcm (3^8) ∣ N := Nat.lcm_dvd hL ((h3.pow_dvd_iff_le_factorization hN.2.ne').mpr h8)
    exact (by decide +kernel : 10^300 < L.lcm (3^8)).trans_le (Nat.le_of_dvd hN.2 hbound)
  have hpar := Nat.even_iff.mp (heven 3 (by decide))
  have hcases : N.factorization 3=4 ∨ N.factorization 3=6 := by omega
  rcases hcases with h4 | h6
  · have hn := extend_valid (e := 4) hv hN.2.ne' h3 (by decide +kernel) (by rw [h4])
    exact (h11 ((show 11∣(state_viii.extend 3 4).joined by decide +kernel).trans (joined_dvd hn hN))).elim
  · have hn := extend_valid (e := 6) hv hN.2.ne' h3 (by decide +kernel) (by rw [h6])
    have hnew : 1093∣N := (show 1093∣(state_viii.extend 3 6).joined by decide +kernel).trans (joined_dvd hn hN)
    exact (by decide +kernel : 10^300 < L.lcm 1093).trans_le (Nat.le_of_dvd hN.2 (Nat.lcm_dvd hL hnew))

end OddPerfect.BrentHistorical
