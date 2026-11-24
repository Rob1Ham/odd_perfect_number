module

public import OddPerfect.IndexAbundantReplay
public import OddPerfect.SizePrimeBank300.Bank
import Mathlib.Tactic.Primality
public import OddPerfect.LargeOrderPrime
public import OddPerfect.LargeOrderCube
public import OddPerfect.LargeOrderQuadratic

public section

namespace OddPerfect.IndexComponent.Size300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def bankLeaf349 : PrimeBank := .leaf [38904276017035188056372051839841219, 39061354749701320139643310061584099, 39546955636451768643571562540114219, 39794905409392396139272403153242163, 41714048449068420177806463620463823, 41851214104513068170325155787681691, 48104021569977256385982808904987959, 54495399712782679699156733066827579, 57710745113383297226474977257232621, 58364886340039271526342759525564007, 60165224719733315498728669512290881, 60226780120174584708613854132734173, 61193108785872099717343552299061871, 64148371425431627832601436220662527, 64941238353142879388943982194275831, 70665487723963214775207723678674929]

theorem bankLeaf349_valid : bankLeaf349.Certified := by
  simp only [bankLeaf349, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 29, 149, 214703072546509998971613654889] }, .lucas { root := 14, primeFactors := [2, 3, 364289353199, 24557295670449313] }, .lucas { root := 7, primeFactors := [2, 31, 197, 2477, 12041] }, .lucas { root := 2, primeFactors := [2, 619] }, .lucas { root := 3, primeFactors := [2, 5, 7, 43] }, .lucas { root := 5, primeFactors := [2, 3, 613, 417300429419] }, .lucas { root := 2, primeFactors := [2, 379, 1889, 291439] }, .lucas { root := 3, primeFactors := [2, 59] }, .lucas { root := 6, primeFactors := [2, 3, 7, 257] }]),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf350 : PrimeBank := .leaf [72351548014980190015557764637775111]

theorem bankLeaf350_valid : bankLeaf350.Certified := by
  simp only [bankLeaf350, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf359 : PrimeBank := .leaf [20190160335800936751198926476589330851, 21381838459758070023033083194026043147, 22997058678794290833044141354201238337, 25809494423403483277404013696925751121, 28343494036522194840123504160699775017, 28583991118304278404388234765612493959, 29624978358656025418485444023076424099, 30762911079533110898866150285320970579, 32114688199831920912408257521477051711, 35166923403152020033228542959565452947, 35656206228074199833528635038646710571, 35922462993765878557295703991437520493, 38280237973898212158647494954229824123, 38676837149795180081395279974646356487, 40957844886377442763169709027626155549, 45586854972493208415830044978733809519]

theorem bankLeaf359_valid : bankLeaf359.Certified := by
  simp only [bankLeaf359, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 89, 131, 23041, 1411523632885586045542863347] }, .lucas { root := 11, primeFactors := [2, 3, 5] }, .lucas { root := 2, primeFactors := [2, 600871996577, 1174562669692249] }, .lucas { root := 3, primeFactors := [2, 691, 27174023] }, .lucas { root := 5, primeFactors := [2, 43, 315977] }, .lucas { root := 3, primeFactors := [2, 127, 311] }, .lucas { root := 7, primeFactors := [2, 3, 1459, 57329, 585107] }, .lucas { root := 3, primeFactors := [2, 3] }, .lucas { root := 3, primeFactors := [2, 3583] }, .lucas { root := 3, primeFactors := [2, 3, 199] }, .lucas { root := 2, primeFactors := [2, 17, 17209] }, .lucas { root := 14, primeFactors := [2, 3, 239] }]),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf360 : PrimeBank := .leaf [46832111174371450604616850217838043873, 48105532969151269777790678536224865597]

theorem bankLeaf360_valid : bankLeaf360.Certified := by
  simp only [bankLeaf360, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 2715384029, 134211533961594041224530107] }, .lucas { root := 3, primeFactors := [2, 7, 29, 719, 4651] }, .lucas { root := 3, primeFactors := [2, 3, 5, 31] }, .lucas { root := 2, primeFactors := [2, 4827655811423, 13900279887811] }, .lucas { root := 5, primeFactors := [2, 2413827905711] }, .lucas { root := 47, primeFactors := [2, 5, 13, 3329, 5577623] }, .lucas { root := 3, primeFactors := [2, 13] }, .lucas { root := 5, primeFactors := [2, 509, 5479] }, .lucas { root := 3, primeFactors := [2, 3, 11, 83] }, .lucas { root := 2, primeFactors := [2, 3, 5, 107, 547, 879607] }, .lucas { root := 3, primeFactors := [2, 3, 7, 13, 179] }]), by simp⟩

@[expose] noncomputable def bankLeaf375 : PrimeBank := .leaf [1806470330447074775256302158071530980566583, 1861198638834710676163967579176998441153131, 2004878177703857376031383952494249216760523, 2210920323449641639724126880590439614580997, 2549561058117779520813143837022388797486293, 2684177863931427575235522828887908895012821, 2905349752593603568127896013865551612108363, 2938344312511812575066069630259275742025111, 3035261670550874661371246936598946343359921, 3287460620742105680032069863029403293800831, 3348533057527736197527567125205923290762027, 3392420147482768839966377445286704923659241, 3494080491360318683010920344106412999042043, 3712767172624444257778315033753177656228041, 3955651156092694836805161806316602227205569, 3968103991948333231574543962910183172742183]

theorem bankLeaf375_valid : bankLeaf375.Certified := by
  simp only [bankLeaf375, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 25319423850437091905876234377582702891609] }, .lucas { root := 7, primeFactors := [2, 3, 283, 114348885629446129, 32600495808523816331] }, .lucas { root := 11, primeFactors := [2, 3, 23, 103576889157107] }, .lucas { root := 2, primeFactors := [2, 503, 102959134351] }, .lucas { root := 3, primeFactors := [2, 3, 5, 686394229] }, .lucas { root := 2, primeFactors := [2, 3, 13, 19, 367, 631] }, .lucas { root := 2, primeFactors := [2, 5, 113, 34374409, 839287049] }, .lucas { root := 7, primeFactors := [2, 3, 17, 173, 487] }, .lucas { root := 3, primeFactors := [2, 2297, 45673] }, .lucas { root := 5, primeFactors := [2, 7, 41] }, .lucas { root := 5, primeFactors := [2, 3, 11, 173] }]),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf376 : PrimeBank := .leaf [3985908625189819904247611107302801645958249]

theorem bankLeaf376_valid : bankLeaf376.Certified := by
  simp only [bankLeaf376, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf378 : PrimeBank := .leaf [22989758668864328087586403746084268421181779, 24755751054171598929498710980184837014632391, 25528437114044074401130674498507857367195217, 27395631932423126416280468114484772969719691, 30912606380679039195454779999587171730310591, 36379600869079813407167833690281003289076473, 37584772487800093147106735073830996898204481, 37739778286868040700788332179475370591684041, 39828946269617282691472403638450635724153631, 40620804307688219921337959268706051453905769, 47104141373523161143798381165060954748808467, 47116606208061592383861405488479246600640221, 50108770334077047291351366118996698593241671, 50730658232911048435859512278424395157412567, 53822877469606411949192379259331015574780379, 59150752990166536513524713615381067397793501]

theorem bankLeaf378_valid : bankLeaf378.Certified := by
  simp only [bankLeaf378, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 29, 2161, 183422096003321642978078505689290306381] }, .lucas { root := 23, primeFactors := [2, 3, 5] }, .lucas { root := 6, primeFactors := [2, 3, 5, 49228247, 14568028175713, 4262704797952043] }, .lucas { root := 5, primeFactors := [2, 24614123] }, .lucas { root := 2, primeFactors := [2, 13, 946697] }, .lucas { root := 5, primeFactors := [2, 17, 6961] }, .lucas { root := 13, primeFactors := [2, 3, 5, 29] }, .lucas { root := 5, primeFactors := [2, 3, 11, 131, 857, 11171] }, .lucas { root := 2, primeFactors := [2, 5, 1117] }, .lucas { root := 2, primeFactors := [2, 3, 31] }, .lucas { root := 2, primeFactors := [2, 13, 67, 2447017679651] }, .lucas { root := 2, primeFactors := [2, 5, 17, 47, 61252007] }, .lucas { root := 5, primeFactors := [2, 2347, 13049] }, .lucas { root := 3, primeFactors := [2, 3, 17, 23] }, .lucas { root := 3, primeFactors := [2, 7, 233] }]),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 53, 141157, 18016192922760585377897610490501883] }, .lucas { root := 2, primeFactors := [2, 3, 1307] }, .lucas { root := 2, primeFactors := [2, 653] }, .lucas { root := 2, primeFactors := [2, 32303, 143428604672537, 1944260250097931] }, .lucas { root := 5, primeFactors := [2, 31, 521] }, .lucas { root := 3, primeFactors := [2, 173, 103633384879] }, .lucas { root := 13, primeFactors := [2, 3, 37, 157, 8929] }, .lucas { root := 11, primeFactors := [2, 3, 31] }, .lucas { root := 2, primeFactors := [2, 5, 1399, 138975000007] }, .lucas { root := 13, primeFactors := [2, 3, 233] }, .lucas { root := 3, primeFactors := [2, 3, 89, 163, 439, 3637] }, .lucas { root := 2, primeFactors := [2, 3, 101] }]),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf379 : PrimeBank := .leaf [60770344613049656874225196565535197391872233, 67030769473382849876436708076700005963531277]

theorem bankLeaf379_valid : bankLeaf379.Certified := by
  simp only [bankLeaf379, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf387 : PrimeBank := .leaf [118411743849830700692355177675805183114247863231, 127876091543425749918009800415499747563439592773, 136316836501190855419243369696076556180278677057, 141785047417170330875956138182105901767368657881, 145993280141956902993007746973287343501886912599, 152604122986834238903060602514366655456372952049, 153588519008122620578869545454577656752687790519, 166841145079410419543035902775079530383218007133, 184065236096494092094574928338134239077340652559, 187463623161013556106717947842041603097792112383, 192455121787427928165671689735087790357710202509, 205368060708076529554328672621790229394318528413, 217157768688721808489551017423654592466781186011, 226430841686668041233640740979872788693136283337, 237479082467754559684099752568103065896607562707, 260551495718621260054268273374657473120059796409]

theorem bankLeaf387_valid : bankLeaf387.Certified := by
  simp only [bankLeaf387, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 709691, 17707133, 242277571918936975230771604538209] }, .lucas { root := 10, primeFactors := [2, 5, 70969] }, .lucas { root := 11, primeFactors := [2, 3, 2957] }, .lucas { root := 2, primeFactors := [2, 739] }, .lucas { root := 2, primeFactors := [2, 17, 260399] }, .lucas { root := 17, primeFactors := [2, 130199] }, .lucas { root := 11, primeFactors := [2, 65099] }, .lucas { root := 2, primeFactors := [2, 11, 269] }, .lucas { root := 7, primeFactors := [2, 3, 595043529981029, 4241243842394837] }, .lucas { root := 2, primeFactors := [2, 107, 1390288621451] }, .lucas { root := 2, primeFactors := [2, 5, 87641, 317269] }, .lucas { root := 3, primeFactors := [2, 5, 7, 313] }, .lucas { root := 2, primeFactors := [2, 3, 7, 1259] }, .lucas { root := 2, primeFactors := [2, 17, 37] }, .lucas { root := 2, primeFactors := [2, 19, 55805840031511] }, .lucas { root := 3, primeFactors := [2, 3, 5, 56393, 3665141] }, .lucas { root := 3, primeFactors := [2, 7, 19, 53] }, .lucas { root := 2, primeFactors := [2, 5, 401, 457] }]),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf388 : PrimeBank := .leaf [272977983247258853313096765919753230104153145571, 304971297664201988898688683700564748747693245597, 331684566686138521272550493847047077726725188693, 333861247832731961503629158161923897180522538541, 374356982031375302506456579084978889473197343303, 383648610470176460447108648593863136411719282871, 383884290468461185925660191432698248743370748871, 407224223745777739427669509897906954434418411219, 407894065567398422895591407413946559138619063763, 427991014220624840610925147039189590679925445953, 447502945934301283161776096917629148402454445541, 452861683373336082467281481959745577386272566673, 457142175391812022188895836562718062881737887831, 508128421182745239048641572654453024113246604849, 522004282403474532166404858744420830406647584961, 528111989772321909941364227078092606399563643801]

theorem bankLeaf388_valid : bankLeaf388.Certified := by
  simp only [bankLeaf388, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 53, 7372071849569618161407770304188325477854183] }, .lucas { root := 5, primeFactors := [2, 67, 65428217, 1208500905398651, 695781208760789819] }, .lucas { root := 3, primeFactors := [2, 7, 1168361] }, .lucas { root := 3, primeFactors := [2, 5, 29209] }, .lucas { root := 7, primeFactors := [2, 3, 1217] }, .lucas { root := 3, primeFactors := [2, 19] }, .lucas { root := 2, primeFactors := [2, 5, 31, 199, 409, 9579413] }, .lucas { root := 2, primeFactors := [2, 103, 23251] }, .lucas { root := 2, primeFactors := [2, 3, 5, 31] }, .lucas { root := 2, primeFactors := [2, 901111, 386068535819] }, .lucas { root := 3, primeFactors := [2, 3, 5, 7, 613] }, .lucas { root := 2, primeFactors := [2, 7, 19, 1439, 1008607] }, .lucas { root := 7, primeFactors := [2, 719] }, .lucas { root := 3, primeFactors := [2, 3, 97, 1733] }, .lucas { root := 2, primeFactors := [2, 433] }]),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf389 : PrimeBank := .leaf [534143036537084362832447570692865651557998082691, 541275423929242862808856008001028521982577712499]

theorem bankLeaf389_valid : bankLeaf389.Certified := by
  simp only [bankLeaf389, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf391 : PrimeBank := .leaf [1531898772017194089595279647314108242896026401501, 1680335565654169270840643848241670783281707515977, 1684456552676079200937215167152468290997049965721, 2011662328141000386772803388818678359834507218991, 2285125789427381455409651943311414400780523582543, 2358680789697807356834136943635824066434739708333, 2916507202643844355422876997343172799810986988337, 3176910526270400229294250985909997863392499206739, 3237350394808285103075641617594465564146206546711, 3410228741835414681827363873347729558432398159557, 4220664214690363448000050143108419891813994478063, 4313016370613880652773372788298434532293960014237, 4458089037939243589600335968442165228154366154087, 4561764611500668699638496177119953507590109034017, 6351885141964057411259499526611848626072045955243, 6647910023442789120989346350302983626987758848799]

theorem bankLeaf391_valid : bankLeaf391.Certified := by
  simp only [bankLeaf391, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 1588455263135200114647125492954998931696249603369] }, .lucas { root := 3, primeFactors := [2, 7, 11, 19719121, 51176297, 6049116954401, 422421373631471329] }, .lucas { root := 26, primeFactors := [2, 3, 5, 82163] }, .lucas { root := 2, primeFactors := [2, 41081] }, .lucas { root := 3, primeFactors := [2, 5, 13, 79] }, .lucas { root := 3, primeFactors := [2, 101, 63337] }, .lucas { root := 5, primeFactors := [2, 3, 7, 13, 29] }, .lucas { root := 3, primeFactors := [2, 5, 13, 581645861] }, .lucas { root := 7, primeFactors := [2, 5, 19, 1530647] }, .lucas { root := 5, primeFactors := [2, 13, 17, 3463] }, .lucas { root := 3, primeFactors := [2, 3, 577] }, .lucas { root := 7, primeFactors := [2, 3, 43, 277, 1583, 8643343] }, .lucas { root := 5, primeFactors := [2, 7, 113] }, .lucas { root := 6, primeFactors := [2, 3, 1440557] }, .lucas { root := 2, primeFactors := [2, 13, 2131] }, .lucas { root := 2, primeFactors := [2, 3, 5, 71] }]),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf392 : PrimeBank := .leaf [6957596529882152968992225251835887181478451547013]

theorem bankLeaf392_valid : bankLeaf392.Certified := by
  simp only [bankLeaf392, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf394 : PrimeBank := .leaf [19256021298645399074821884828797791764310604858317, 19940949725580644621180382060068194688347786712249, 21725473066772863950504173513098364324584931693593, 22898167557805240362824718730100007611882028955979, 23415065069707640204392947799864167443670942372487, 24772285175707806384099574440402334706455060939751, 29250123049599147533858113260558877253329048079143, 36799120636249118806979649347305792642377421012261, 39142161322463429947510947236016017221408300438307, 46419313456592907636857201777405071452546406811377, 50645362436196135834421642283706575039296966047049, 53489014811148111678694572505473146058642537147509, 53749796710026252467472921924601285997088061429877, 66398616087174002265335853628774815585259904511103, 68141055822477632778023162393161554769187099016961, 68618354130992261250361621925551563109288767034369]

theorem bankLeaf394_valid : bankLeaf394.Certified := by
  simp only [bankLeaf394, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    (OddPerfect.prime_of_largeOrderPlusCheck (D := 3) (x := 2397022512488968953207135588762858450475822949428) (y := 17757952943743117190178398311320870680018982889321) (factors := [(493202120007257062236190803517483913639, 1)]) (by simp only [List.forall_mem_cons]; exact ⟨(OddPerfect.prime_of_largeOrderPlusCheck (D := 31) (x := 105462869277797000416834543845296076632) (y := 191163076652925934488063619224974331524) (factors := [(195715126987006770728647144252969807, 1)]) (by simp only [List.forall_mem_cons]; exact ⟨(OddPerfect.prime_of_largeOrderCubeCheck (b := 76659564435116460398702408302528504) (factors := [(2099932390632961, 1)]) (by simp only [List.forall_mem_cons]; exact ⟨(OddPerfect.prime_of_largeOrderCheck (b := 1785375388042652) (factors := [(88746737, 1)]) (by simp only [List.forall_mem_cons]; exact ⟨(OddPerfect.prime_of_largeOrderCubeCheck (b := 50437838) (factors := [(3257, 1)]) (by simp only [List.forall_mem_cons]; exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 37] }]), by simp⟩) (by decide +kernel)), by simp⟩) (by decide +kernel)), by simp⟩) (by decide +kernel)), by simp⟩) (by decide +kernel)), by simp⟩) (by decide +kernel)),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11, 151, 1699, 149938448003, 2139350670986959402486256833549] }, .lucas { root := 3, primeFactors := [2, 3, 283] }, .lucas { root := 5, primeFactors := [2, 7, 17, 79, 7974601] }, .lucas { root := 11, primeFactors := [2, 3, 5, 13291] }, .lucas { root := 2, primeFactors := [2, 3, 5, 443] }, .lucas { root := 6, primeFactors := [2, 3, 211, 5434307138231, 155479843891069] }, .lucas { root := 11, primeFactors := [2, 5, 19, 123311, 231947] }, .lucas { root := 11, primeFactors := [2, 5, 11, 19, 59] }, .lucas { root := 2, primeFactors := [2, 11, 13, 811] }, .lucas { root := 2, primeFactors := [2, 3, 12956653657589] }, .lucas { root := 2, primeFactors := [2, 41, 79003985717] }, .lucas { root := 2, primeFactors := [2, 19750996429] }, .lucas { root := 2, primeFactors := [2, 3, 1645916369] }, .lucas { root := 3, primeFactors := [2, 727, 141499] }, .lucas { root := 13, primeFactors := [2, 3, 7, 1123] }, .lucas { root := 2, primeFactors := [2, 3, 11, 17] }]),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf395 : PrimeBank := .leaf [76574672959050740219756384533876186628666339913941, 77602516170919717306074412477103227419813818215603, 78502102067780881464335234231178888128258220373507, 86002611765308630529123537449370925656697084619603, 93405926305602818503366746111204285215950653747431, 106692328601769896074408182939097444468285166483359, 109789633721172726495643902619680352783757802762319, 110997250014986885992304442256975000490342960018363, 111391001351022179008522138454295055950575820180161, 115818625571197592034031211634645997677055792367221, 118470123710219891706333708505740644829333323791367, 120333284591555577359492463316200337575802653745741, 122037805372896412007414968233017792829605246022013, 125470043458596098806451717206806024172874202481709, 138364619824953525297520160494079932676629423304297, 143691831909885691760575432292450544282827896784201]

theorem bankLeaf395_valid : bankLeaf395.Certified := by
  simp only [bankLeaf395, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 5698832223645563, 176604112298882413941227981115029] }, .lucas { root := 2, primeFactors := [2, 29, 4884619, 20115331] }, .lucas { root := 3, primeFactors := [2, 3, 277, 2939] }, .lucas { root := 2, primeFactors := [2, 13, 113] }, .lucas { root := 2, primeFactors := [2, 3, 5, 670511] }, .lucas { root := 14, primeFactors := [2, 5, 19, 3529] }, .lucas { root := 17, primeFactors := [2, 3, 7] }, .lucas { root := 2, primeFactors := [2, 7, 11, 111914458084511, 5123466483333031] }, .lucas { root := 11, primeFactors := [2, 5, 1861, 5351, 1123841] }, .lucas { root := 2, primeFactors := [2, 3, 5, 31] }, .lucas { root := 11, primeFactors := [2, 5, 107] }, .lucas { root := 3, primeFactors := [2, 5, 439] }, .lucas { root := 3, primeFactors := [2, 3, 5, 7, 233, 457, 1583, 48247] }, .lucas { root := 5, primeFactors := [2, 7, 113] }, .lucas { root := 3, primeFactors := [2, 3, 11, 17, 43] }]),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 401, 1532449, 21799777, 334502650504459152781957218041357] }, .lucas { root := 11, primeFactors := [2, 3, 17, 313] }, .lucas { root := 7, primeFactors := [2, 3, 227081] }, .lucas { root := 6, primeFactors := [2, 5, 7, 811] }, .lucas { root := 2, primeFactors := [2, 1303603665569, 64149606843590503331] }, .lucas { root := 3, primeFactors := [2, 71, 573769219] }, .lucas { root := 2, primeFactors := [2, 3, 11, 59, 147347] }, .lucas { root := 2, primeFactors := [2, 73673] }, .lucas { root := 3, primeFactors := [2, 9209] }, .lucas { root := 3, primeFactors := [2, 1151] }, .lucas { root := 17, primeFactors := [2, 5, 23] }, .lucas { root := 2, primeFactors := [2, 5, 13909367, 461197169099] }, .lucas { root := 10, primeFactors := [2, 17, 409099] }, .lucas { root := 2, primeFactors := [2, 3, 41, 1663] }, .lucas { root := 3, primeFactors := [2, 3, 277] }, .lucas { root := 2, primeFactors := [2, 37, 181, 257, 133981] }, .lucas { root := 6, primeFactors := [2, 3, 5, 7, 11, 29] }]),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf396 : PrimeBank := .leaf [152148290859593330149554542876521433539831497582793, 167676893338405384303641648007444400587092642212543, 178137130626632223577706933544126507968420645362333, 195163150047313020008802835877656364030813707064261, 217171599055284644648798525834594580991825499758079, 247844301073446432073571189153011918514923282850779, 257617584046114414754226314902854641086842966144383, 267117028772749033820000132580826043370441531574651, 345682503476776101923218570637351124413539535890981, 352543136592931780159519873787602252895251257440951, 427387421986058585403402593524941313464176846023061, 454943171687334063595189264919405759653528793403583, 484659285270119194936449216246169915874829114597769, 515380651092796114239414194849764516701117416486401, 599038420461060696413181332715356424078575978745199, 600990558184559183777724051749697130888724712684563]

theorem bankLeaf396_valid : bankLeaf396.Certified := by
  simp only [bankLeaf396, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 13, 569, 2686577, 1972213386615745585021984163644346281] }, .lucas { root := 3, primeFactors := [2, 167911] }, .lucas { root := 6, primeFactors := [2, 3, 5, 29, 193] }, .lucas { root := 33, primeFactors := [2, 3, 5, 13, 7873651687273, 12351217028915174987] }, .lucas { root := 10, primeFactors := [2, 3, 7, 2969, 2255063] }, .lucas { root := 3, primeFactors := [2, 7, 53] }, .lucas { root := 5, primeFactors := [2, 1127531] }, .lucas { root := 2, primeFactors := [2, 5, 47, 2399] }, .lucas { root := 11, primeFactors := [2, 11, 109] }, .lucas { root := 2, primeFactors := [2, 3823, 1615382818325291] }, .lucas { root := 3, primeFactors := [2, 3, 7, 13] }, .lucas { root := 2, primeFactors := [2, 5, 7, 19, 475679, 2553347] }, .lucas { root := 7, primeFactors := [2, 7, 61, 557] }, .lucas { root := 2, primeFactors := [2, 31, 41183] }, .lucas { root := 5, primeFactors := [2, 59, 349] }]),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.SizePrimeBank300.bank.prime_of_contains OddPerfect.IndexComponent.SizePrimeBank300.bank_valid (by decide +kernel), by simp⟩

end OddPerfect.IndexComponent.Size300
