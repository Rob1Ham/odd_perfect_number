module

public import OddPerfect.SizeIndex300.Bank

public section

namespace OddPerfect.IndexComponent.Size300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def state127_1 : State := ⟨1533849450216570883254289, 1561427351316116358029730, 1009⟩

private noncomputable def tree127_1 : AbundanceTree :=
  .split 139 [
    (2, .abundant [(3, 6), (5, 2), (13, 2)]),
    (4, .abundant [(3, 4), (5, 2), (31, 2), (41, 2), (79, 2), (101, 2)]),
    (6, .abundant [(3, 4), (5, 2), (29, 2), (31, 2), (79, 2)]),
    (10, .abundant [(3, 4), (5, 2), (31, 2), (79, 2), (101, 2), (127, 2), (139, 10), (181, 2), (199, 2)]),
    (12, .split 39506540104017949 [
      (2, .abundant [(3, 6), (5, 2), (7, 2)]),
      (4, .split 205661 [
        (2, .split 644599 [
          (2, .abundant [(3, 6), (5, 2), (7, 2)]),
          (4, .split 5569259952708194430671 []),
          (6, .abundant [(3, 4), (5, 2), (29, 2), (31, 2), (79, 2)])]),
        (4, .abundant [(3, 4), (5, 2), (11, 2)]),
        (6, .abundant [(3, 4), (5, 2), (7, 2)])]),
      (6, .split 205661 [
        (2, .round 1 [(79, 1), (101, 1), (6449, 1), (65617, 1), (644599, 1)])])]),
    (16, .split 388341648605203039829 [
      (2, .split 50368445538589 [
        (2, .abundant [(3, 6), (5, 2), (13, 2)]),
        (4, .abundant [(3, 4), (5, 2), (31, 2), (41, 2), (79, 2), (101, 2)])]),
      (4, .abundant [(3, 4), (5, 2), (11, 2)])]),
    (18, .split 2972543009343882370915626760369 [
      (2, .abundant [(3, 6), (5, 2), (31, 2), (79, 2), (101, 2), (127, 2), (139, 18), (151, 2)])]),
    (22, .abundant [(3, 4), (5, 2), (23, 2), (31, 2)]),
    (28, .abundant [(3, 4), (5, 2), (31, 2), (59, 2), (79, 2), (101, 2), (127, 2)]),
    (30, .split 12109715612437511229745421378703116402502896752168268807 []),
    (36, .split 101 [
      (2, .split 10303 [
        (2, .abundant [(3, 6), (5, 2), (31, 2), (79, 2), (101, 2), (127, 2), (139, 36), (181, 2)]),
        (4, .split 372649725281 [
          (2, .split 480831112093 [
            (2, .abundant [(3, 6), (5, 2), (31, 2), (79, 2), (101, 2), (127, 2), (139, 36), (181, 2)])])]),
        (6, .split 4513076485163 [
          (2, .abundant [(3, 4), (5, 2), (19, 2), (31, 2)])]),
        (10, .round 1 [(1738389269, 1), (7754112900847627986005248261117, 1)]),
        (12, .round 1 [(1430891000405086134482948961743541942606439992961, 1)])]),
      (4, .split 1381 [
        (2, .abundant [(3, 6), (5, 2), (7, 2)]),
        (4, .abundant [(3, 4), (5, 4), (31, 2), (79, 2), (101, 4), (127, 2), (139, 36)]),
        (6, .abundant [(3, 4), (5, 2), (31, 2), (71, 2), (79, 2), (101, 4), (127, 2)]),
        (10, .split 82056939999681659 []),
        (12, .round 1 [(609553239698506111739601414830194507, 1)]),
        (16, .round 1 [(58314696484892005003913, 1)])]),
      (6, .abundant [(3, 4), (5, 2), (31, 2), (71, 2), (79, 2), (101, 6), (127, 2)]),
      (10, .abundant [(3, 4), (5, 2), (23, 2), (31, 2)]),
      (12, .abundant [(3, 4), (5, 2), (31, 2), (79, 2), (101, 12), (127, 2), (139, 36), (157, 2)]),
      (16, .abundant [(3, 4), (5, 2), (31, 2), (79, 2), (101, 16), (127, 2), (139, 36), (181, 2), (239, 2)]),
      (18, .split 94474298622267623 []),
      (22, .abundant [(3, 4), (5, 2), (31, 2), (47, 2), (79, 2), (101, 22)]),
      (28, .round 1 [(12328309174325516340162112641276926381, 1)])]),
    (40, .split 9778893062881161967180792115514178576312960285966298525786093017447960149517690877 []),
    (42, .abundant [(3, 4), (5, 2), (31, 2), (79, 2), (101, 2), (127, 2), (139, 42), (173, 2), (181, 2)]),
    (46, .split 227228933612603124420886434653 []),
    (52, .split 101 [
      (2, .split 10303 [
        (2, .abundant [(3, 6), (5, 2), (31, 2), (79, 2), (101, 2), (127, 2), (139, 52), (181, 2)]),
        (4, .round 1 [(372649725281, 1)])]),
      (4, .split 1381 [
        (2, .abundant [(3, 6), (5, 2), (7, 2)]),
        (4, .abundant [(3, 4), (5, 4), (31, 2), (79, 2), (101, 4), (127, 2), (139, 52)])]),
      (6, .abundant [(3, 4), (5, 2), (31, 2), (71, 2), (79, 2), (101, 6), (127, 2)]),
      (10, .abundant [(3, 4), (5, 2), (23, 2), (31, 2)])]),
    (58, .round 1 [(47682069791867902967386858011341296462295349043894418472377790169064511950986550170307383, 1)]),
    (60, .round 1 [(72708615738488268430074452751689371867759303932801560701171051347377032971601020152219875452252512595689, 1)])]

private theorem checked127_1 : replayAbundance bank 127 1 (10^300) 8 state127_1 tree127_1 = true := by
  decide +kernel

theorem reject127_1 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_1 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree127_1 checked127_1

@[expose] noncomputable def state127_2 : State := ⟨50250441838545078706293761929, 51153930082875870694698848550, 1009⟩

private noncomputable def tree127_2 : AbundanceTree :=
  .abundant [(3, 4), (5, 2), (11, 2)]

private theorem checked127_2 : replayAbundance bank 127 1 (10^300) 3 state127_2 tree127_2 = true := by
  decide +kernel

theorem reject127_2 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_2 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_2 checked127_2

@[expose] noncomputable def state127_3 : State := ⟨1646254725072575323496889934555969, 1675853903453722808411718264210570, 1009⟩

private noncomputable def tree127_3 : AbundanceTree :=
  .abundant [(3, 4), (5, 2), (29, 2), (31, 2), (101, 2)]

private theorem checked127_3 : replayAbundance bank 127 1 (10^300) 3 state127_3 tree127_3 = true := by
  decide +kernel

theorem reject127_3 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_3 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_3 checked127_3

@[expose] noncomputable def state127_4 : State := ⟨1766897409286890594710326662753716157499249, 1798665707838844577499412017651039409812210, 1009⟩

private noncomputable def tree127_4 : AbundanceTree :=
  .split 52198426022458982993 [
    (2, .split 727 [
      (2, .split 176419 [
        (2, .abundant [(3, 6), (5, 2), (13, 2)]),
        (4, .abundant [(3, 4), (5, 2), (31, 2), (41, 2), (101, 2), (127, 2), (181, 10)]),
        (6, .split 683395002335722741 [
          (2, .split 354615587864421026051925379772419 [])]),
        (10, .abundant [(3, 4), (5, 2), (11, 2)]),
        (12, .split 157 [
          (2, .split 8269 [
            (2, .abundant [(3, 6), (5, 2), (7, 2)]),
            (4, .abundant [(3, 6), (5, 2), (31, 2), (61, 2), (101, 2), (127, 2), (157, 2)])]),
          (4, .abundant [(3, 4), (5, 2), (11, 2)]),
          (6, .round 1 [(5, 1), (31, 1), (101, 1), (12503, 1), (1205476469, 1)])])]),
      (4, .split 19587401 [
        (2, .split 383666297522203 [
          (2, .abundant [(3, 4), (5, 2), (19, 2), (31, 2)]),
          (4, .abundant [(3, 4), (5, 2), (11, 2)])]),
        (4, .abundant [(3, 4), (5, 2), (11, 2)]),
        (6, .abundant [(3, 4), (5, 2), (7, 2)]),
        (10, .abundant [(3, 4), (5, 2), (23, 2), (31, 2)])]),
      (6, .split 19481464031 [
        (2, .abundant [(3, 4), (5, 2), (13, 2)]),
        (4, .split 281 [
          (2, .abundant [(3, 4), (5, 2), (31, 2), (101, 2), (109, 2), (113, 2), (127, 2), (181, 10), (239, 2)]),
          (4, .abundant [(3, 4), (5, 4), (31, 2), (101, 2), (113, 2), (127, 2), (181, 10), (239, 2)]),
          (6, .abundant [(3, 4), (5, 2), (7, 2)]),
          (10, .round 1 [(201637702531, 1), (15277058694481, 1)]),
          (12, .abundant [(3, 4), (5, 2), (31, 2), (53, 2), (101, 2), (113, 2), (127, 2)])]),
        (6, .abundant [(3, 4), (5, 2), (7, 2)])]),
      (10, .abundant [(3, 4), (5, 2), (11, 2)]),
      (12, .split 19724193952362728947 [
        (2, .round 1 [(1895333441, 1), (18972457177, 1), (6835238813839638524068041847, 1)])]),
      (16, .split 84125767053887121808615743694069169 []),
      (18, .split 7647356463442445534257848274391889469297 []),
      (22, .round 1 [(13537641593297, 1), (2004878177703857376031383952494249216760523, 1)]),
      (28, .round 1 [(2018711290335734514212882701542320715926903683136203927568188228445833, 1)]),
      (30, .round 1 [(1861, 1)])]),
    (4, .split 2311 [
      (2, .split 2017 [
        (2, .split 4099 [
          (2, .abundant [(3, 6), (5, 2), (7, 2)]),
          (4, .split 369023021 [
            (2, .abundant [(3, 6), (5, 2), (13, 2)])]),
          (6, .round 1 [(101, 1), (281, 1), (331, 1), (727, 1), (883, 1), (16883681631285687821, 1)]),
          (10, .round 1 [(1339322446256468156596004408950229501, 1)])]),
        (4, .abundant [(3, 4), (5, 2), (11, 2)]),
        (6, .abundant [(3, 4), (5, 2), (7, 2)]),
        (10, .abundant [(3, 4), (5, 2), (23, 2), (31, 2)]),
        (12, .round 1 [(620920889070785392502066473873, 1)])]),
      (4, .split 550531 [
        (2, .abundant [(3, 4), (5, 2), (7, 2)]),
        (4, .abundant [(3, 4), (5, 4), (11, 2)]),
        (6, .abundant [(3, 4), (5, 2), (29, 2), (31, 2), (101, 2)])]),
      (6, .abundant [(3, 4), (5, 2), (7, 2)]),
      (10, .abundant [(3, 4), (5, 2), (11, 2)]),
      (12, .round 1 [(4187718109848600809, 1)])]),
    (6, .split 727 [
      (2, .round 1 [(176419, 1)])])]

private theorem checked127_4 : replayAbundance bank 127 1 (10^300) 8 state127_4 tree127_4 = true := by
  decide +kernel

theorem reject127_4 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_4 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree127_4 checked127_4

@[expose] noncomputable def state127_5 : State := ⟨57885326025647822773305011798474495035832896489, 58926087254508387203458245736674284794144675830, 1009⟩

private noncomputable def tree127_5 : AbundanceTree :=
  .split 152943249629 [
    (2, .abundant [(3, 4), (5, 2), (7, 2)]),
    (4, .abundant [(3, 4), (5, 2), (11, 2)]),
    (6, .abundant [(3, 4), (5, 2), (31, 2), (43, 2), (101, 2), (127, 2), (181, 12)]),
    (10, .round 1 [(26991238223, 1)])]

private theorem checked127_5 : replayAbundance bank 127 1 (10^300) 4 state127_5 tree127_5 = true := by
  decide +kernel

theorem reject127_5 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_5 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree127_5 checked127_5

@[expose] noncomputable def state127_6 : State := ⟨62127343376909821272987678548008529070957737978183862169, 63244374836837083138404127977725338942288506616594688670, 1009⟩

private noncomputable def tree127_6 : AbundanceTree :=
  .split 1334330052880007782765169510725896497 [
    (2, .abundant [(3, 4), (5, 2), (31, 2), (43, 2), (101, 2), (127, 2), (181, 16)])]

private theorem checked127_6 : replayAbundance bank 127 1 (10^300) 4 state127_6 tree127_6 = true := by
  decide +kernel

theorem reject127_6 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_6 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree127_6 checked127_6

@[expose] noncomputable def state127_7 : State := ⟨2035353896370942654724349336911307420893646453903281508518609, 2071948964029619680697257636678259829096940173848947882381890, 1009⟩

private noncomputable def tree127_7 : AbundanceTree :=
  .split 43713986862401934971169718340891095138399 [
    (2, .split 9769 [
      (2, .abundant [(3, 6), (5, 2), (7, 2)]),
      (4, .split 6151 [
        (2, .split 10099 [
          (2, .round 1 [(101, 1), (461, 1), (1061, 1), (1249, 1), (1601, 1), (33999967, 1)]),
          (4, .round 1 [(72849277001, 1)])]),
        (4, .abundant [(3, 4), (5, 2), (31, 2), (61, 2), (101, 2), (127, 2), (181, 18), (191, 2)]),
        (6, .abundant [(3, 4), (5, 2), (31, 2), (61, 2), (71, 2), (101, 2), (113, 2)])]),
      (6, .abundant [(3, 4), (5, 2), (29, 2), (31, 2), (101, 2)])])]

private theorem checked127_7 : replayAbundance bank 127 1 (10^300) 7 state127_7 tree127_7 = true := by
  decide +kernel

theorem reject127_7 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_7 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree127_7 checked127_7

@[expose] noncomputable def state127_8 : State := ⟨2184510982236515906174575051014448528887193475115896609604440754098689, 2223787850666426947341776132435126782222090843957279351835592052101930, 1009⟩

private noncomputable def tree127_8 : AbundanceTree :=
  .split 101773284709396412846629241478530447963663365783 [
    (2, .split 10993 [
      (2, .abundant [(3, 6), (5, 2), (19, 2), (31, 2)]),
      (4, .abundant [(3, 4), (5, 2), (11, 2)])])]

private theorem checked127_8 : replayAbundance bank 127 1 (10^300) 5 state127_8 tree127_8 = true := by
  decide +kernel

theorem reject127_8 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_8 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree127_8 checked127_8

@[expose] noncomputable def state127_9 : State := ⟨76811400136023464193076405024347446948441367651699565687077072797838483934845296809, 78192446640981343680822181946684628247700319111584400508446804739842830217518595990, 1009⟩

private noncomputable def tree127_9 : AbundanceTree :=
  .split 433125703643523100943 [
    (2, .abundant [(3, 4), (5, 2), (31, 2), (59, 2), (61, 2), (101, 2), (127, 2)]),
    (4, .round 1 [(31, 1), (59, 1), (101, 1)])]

private theorem checked127_9 : replayAbundance bank 127 1 (10^300) 4 state127_9 tree127_9 = true := by
  decide +kernel

theorem reject127_9 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_9 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree127_9 checked127_9

@[expose] noncomputable def state127_10 : State := ⟨2516418279856264710429376105002646709477887645637329471474331981929986572189466768759649, 2561662744405189800327415502755335106022910154414616545057225770090617369338816010092410, 1009⟩

private noncomputable def tree127_10 : AbundanceTree :=
  .split 2288137482121 [
    (2, .split 1089255527411244283 [
      (2, .split 8866387528741985070004921 [])]),
    (4, .abundant [(3, 4), (5, 2), (31, 2), (41, 2), (101, 2), (127, 2), (181, 30)]),
    (6, .abundant [(3, 4), (5, 2), (7, 2)])]

private theorem checked127_10 : replayAbundance bank 127 1 (10^300) 5 state127_10 tree127_10 = true := by
  decide +kernel

theorem reject127_10 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_10 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree127_10 checked127_10

@[expose] noncomputable def state127_11 : State := ⟨88481867555434451864254446503363768943798143581961698278014728422817274875277551953145531671046754569, 90072745650654458169260812673308009137057092722059663859343616858956303720374487099155309018442784870, 1009⟩

private noncomputable def tree127_11 : AbundanceTree :=
  .split 29329992429771407547965836658825936796349350460952815690332827729 []

private theorem checked127_11 : replayAbundance bank 127 1 (10^300) 3 state127_11 tree127_11 = true := by
  decide +kernel

theorem reject127_11 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_11 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_11 checked127_11

@[expose] noncomputable def state127_12 : State := ⟨94966094961805329007791280681257802930322545137653970830287973405608732390852776701511681999105406080737329849, 96673557568973592556468191289004373440917153231918581575167222113808838459627440802838264925019785121444202510, 1009⟩

private noncomputable def tree127_12 : AbundanceTree :=
  .round 1 [(5, 1), (31, 1), (101, 1), (170034833900341, 1), (37650509807897356627, 1), (44648353204272936138890839, 1), (7135671635146131189359629522817, 1)]

private theorem checked127_12 : replayAbundance bank 127 1 (10^300) 3 state127_12 tree127_12 = true := by
  decide +kernel

theorem reject127_12 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_12 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_12 checked127_12

@[expose] noncomputable def state127_13 : State := ⟨3111184237043704383624250146398686881800296901254681738371064296741147681856727817518224213972692208611035663183089, 3167122419517143865742454414819072278297886857030884650984053363670491356775854588141784397217199588946322805294130, 1009⟩

private noncomputable def tree127_13 : AbundanceTree :=
  .round 1 [(33764507556152726691424640975421842486881674115491343187088665764481222263483447508926673477, 1)]

private theorem checked127_13 : replayAbundance bank 127 1 (10^300) 3 state127_13 tree127_13 = true := by
  decide +kernel

theorem reject127_13 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_13 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_13 checked127_13

@[expose] noncomputable def state127_14 : State := ⟨3339181527940270854257616488411489566800380756905253632020601344498009113105103906833478158750382902430435431623450556340769, 3399219035008431481230066456537242545176136573618988671599160515390812979003913709802983948354379972322624428005975408402970, 1009⟩

private noncomputable def tree127_14 : AbundanceTree :=
  .split 290863564648029112125527 []

private theorem checked127_14 : replayAbundance bank 127 1 (10^300) 3 state127_14 tree127_14 = true := by
  decide +kernel

theorem reject127_14 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_14 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_14 checked127_14

@[expose] noncomputable def state127_15 : State := ⟨117411727638395831391051109936924248017747917507447678854810940146738051137187528217737274610738528191633742721698780639388260384227065289, 119522756155112407482389602485543364638423372824856143840590600681888139282445725176513535594867384445151845632262155867047873480939060230, 1009⟩

private noncomputable def tree127_15 : AbundanceTree :=
  .round 1 [(4379034542442173295482261595095265759057403835682359241076218227, 1)]

private theorem checked127_15 : replayAbundance bank 127 1 (10^300) 3 state127_15 tree127_15 = true := by
  decide +kernel

theorem reject127_15 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_15 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_15 checked127_15

@[expose] noncomputable def state127_16 : State := ⟨4128411010807265706983286794027609347108513188648070609145593497468315229276220774939658516037280598202345240024380595807858907161157577369961033791409, 4202638633105626398532017583332521844531534075747621061392878503117447730322054492633468814717828390575123601708863996761525259597473950753025126318290, 1009⟩

private noncomputable def tree127_16 : AbundanceTree :=
  .round 1 [(430665984440049279337871263622506185143255003526430144762992966425698730419751, 1)]

private theorem checked127_16 : replayAbundance bank 127 1 (10^300) 3 state127_16 tree127_16 = true := by
  decide +kernel

theorem reject127_16 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_16 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_16 checked127_16

@[expose] noncomputable def state127_17 : State := ⟨135250873125056831826479458659138509820622000573299441226218788570559475226318268807798152643897349677707032408438732699261265657506683392217293428040350249, 137682644259173426442307428047556748148697587855567813592292092640630705093080827233165071838970775903631624315584093397904329029672852727028438852600362710, 1009⟩

private noncomputable def tree127_17 : AbundanceTree :=
  .round 1 [(357940579107085761224235257559640464240043045386207158127877228758973672658088220966701989244373694924978567812281494809, 1)]

private theorem checked127_17 : replayAbundance bank 127 1 (10^300) 3 state127_17 tree127_17 = true := by
  decide +kernel

theorem reject127_17 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_17 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_17 checked127_17

@[expose] noncomputable def state127_18 : State := ⟨46819372125898809049, 47397849355435642110, 1009⟩

private theorem checked127_18 : checkChildren bank 127 1 (10^300) state127_18 181 [state127_1, state127_2, state127_3, state127_4, state127_5, state127_6, state127_7, state127_8, state127_9, state127_10, state127_11, state127_12, state127_13, state127_14, state127_15, state127_16, state127_17] = true := by
  decide +kernel

theorem reject127_18 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_18 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state127_1, state127_2, state127_3, state127_4, state127_5, state127_6, state127_7, state127_8, state127_9, state127_10, state127_11, state127_12, state127_13, state127_14, state127_15, state127_16, state127_17] ?_ checked127_18
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject127_1 ho hN hs hav hx hvalid
  · exact reject127_2 ho hN hs hav hx hvalid
  · exact reject127_3 ho hN hs hav hx hvalid
  · exact reject127_4 ho hN hs hav hx hvalid
  · exact reject127_5 ho hN hs hav hx hvalid
  · exact reject127_6 ho hN hs hav hx hvalid
  · exact reject127_7 ho hN hs hav hx hvalid
  · exact reject127_8 ho hN hs hav hx hvalid
  · exact reject127_9 ho hN hs hav hx hvalid
  · exact reject127_10 ho hN hs hav hx hvalid
  · exact reject127_11 ho hN hs hav hx hvalid
  · exact reject127_12 ho hN hs hav hx hvalid
  · exact reject127_13 ho hN hs hav hx hvalid
  · exact reject127_14 ho hN hs hav hx hvalid
  · exact reject127_15 ho hN hs hav hx hvalid
  · exact reject127_16 ho hN hs hav hx hvalid
  · exact reject127_17 ho hN hs hav hx hvalid

@[expose] noncomputable def state127_19 : State := ⟨4586847067802180423721481, 4643520054931962270299970, 1009⟩

private noncomputable def tree127_19 : AbundanceTree :=
  .abundant [(3, 2), (5, 2), (11, 2), (31, 2)]

private theorem checked127_19 : replayAbundance bank 127 1 (10^300) 3 state127_19 tree127_19 = true := by
  decide +kernel

theorem reject127_19 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_19 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_19 checked127_19

@[expose] noncomputable def state127_20 : State := ⟨449368820385511813931569772089, 454921016261780840946866186310, 1009⟩

private noncomputable def tree127_20 : AbundanceTree :=
  .split 32528030679467 [
    (2, .split 7059783720349647901 [
      (2, .abundant [(3, 4), (5, 2), (13, 2)]),
      (4, .abundant [(3, 2), (5, 2), (11, 2), (29, 2)]),
      (6, .round 1 [(149873257, 1)])]),
    (4, .abundant [(3, 2), (5, 2), (11, 2), (29, 2)]),
    (6, .abundant [(3, 2), (5, 2), (7, 2)])]

private theorem checked127_20 : replayAbundance bank 127 1 (10^300) 5 state127_20 tree127_20 = true := by
  decide +kernel

theorem reject127_20 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_20 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree127_20 checked127_20

@[expose] noncomputable def state127_21 : State := ⟨4313008217873229481694201061446094213529, 4366297777262433258471025174821859962510, 1009⟩

private noncomputable def tree127_21 : AbundanceTree :=
  .split 4805923863681403 [
    (2, .split 292938126094387 [
      (2, .abundant [(3, 4), (5, 2), (7, 2)]),
      (4, .abundant [(3, 4), (5, 2), (11, 2)]),
      (6, .round 1 [(199, 1), (307, 1), (2833, 1), (12241, 1), (79633, 1), (9466799, 1)])]),
    (4, .split 9466799 [
      (2, .split 87914143 [
        (2, .abundant [(3, 4), (5, 2), (7, 2)]),
        (4, .abundant [(3, 2), (5, 2), (11, 2), (19, 2)]),
        (6, .abundant [(3, 2), (5, 2), (19, 2), (31, 2), (43, 2), (101, 2)])]),
      (4, .split 199 [
        (2, .split 13267 [
          (2, .abundant [(3, 4), (5, 2), (7, 2)]),
          (4, .split 9352230341 [
            (2, .round 1 [(161671372200505003, 1)])]),
          (6, .round 1 [(1509388891523556998809, 1)])]),
        (4, .split 22199431 [
          (2, .abundant [(3, 4), (5, 2), (7, 2)]),
          (4, .round 1 [(6990719698304425251911, 1)])]),
        (6, .split 11552213 [
          (2, .split 219857721169 [])]),
        (10, .abundant [(3, 2), (5, 2), (11, 2), (31, 2)]),
        (12, .round 1 [(3501822143, 1), (309047089313, 1)]),
        (16, .round 1 [(101, 1)])]),
      (6, .split 199 [
        (2, .split 13267 [
          (2, .abundant [(3, 4), (5, 2), (7, 2)]),
          (4, .round 1 [(9352230341, 1)])]),
        (4, .split 22199431 [
          (2, .abundant [(3, 4), (5, 2), (7, 2)])]),
        (6, .split 11552213 []),
        (10, .abundant [(3, 2), (5, 2), (11, 2), (31, 2)])])]),
    (6, .abundant [(3, 2), (5, 2), (7, 2)])]

private theorem checked127_21 : replayAbundance bank 127 1 (10^300) 8 state127_21 tree127_21 = true := by
  decide +kernel

theorem reject127_21 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_21 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree127_21 checked127_21

@[expose] noncomputable def state127_22 : State := ⟨422541102096822419092099183788812404005222601, 427761826940623323899147865503552086515567570, 1009⟩

private noncomputable def tree127_22 : AbundanceTree :=
  .abundant [(3, 2), (5, 2), (13, 2), (31, 2)]

private theorem checked127_22 : replayAbundance bank 127 1 (10^300) 3 state127_22 tree127_22 = true := by
  decide +kernel

theorem reject127_22 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_22 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_22 checked127_22

@[expose] noncomputable def state127_23 : State := ⟨4055517790863541334988461713974369124948142376499243561, 4105625916156370865350419144946428240858728005419593370, 1009⟩

private noncomputable def tree127_23 : AbundanceTree :=
  .split 13246565380514038381666341431 [
    (2, .split 642681586231 [
      (2, .abundant [(3, 4), (5, 2), (13, 2)]),
      (4, .abundant [(3, 2), (5, 2), (11, 2), (19, 2)])]),
    (4, .round 1 [(642681586231, 1)])]

private theorem checked127_23 : replayAbundance bank 127 1 (10^300) 5 state127_23 tree127_23 = true := by
  decide +kernel

theorem reject127_23 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_23 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree127_23 checked127_23

@[expose] noncomputable def state127_24 : State := ⟨397315022453110281047484605656354968802044560483254392427609, 402224065379923497307515213211256628328688875392239991290910, 1009⟩

private noncomputable def tree127_24 : AbundanceTree :=
  .split 2581031347226487302682209 [
    (2, .split 1266189052768483 [
      (2, .abundant [(3, 4), (5, 2), (7, 2)]),
      (4, .round 1 [(101, 1), (673, 1), (1153, 1), (255209, 1)])]),
    (4, .abundant [(3, 2), (5, 2), (11, 2), (31, 2)])]

private theorem checked127_24 : replayAbundance bank 127 1 (10^300) 5 state127_24 tree127_24 = true := by
  decide +kernel

theorem reject127_24 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_24 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree127_24 checked127_24

@[expose] noncomputable def state127_25 : State := ⟨3813399771382982618551377722892371143341519754896501555593837806648249, 3860516397024863683078216557767556959212622669545034405443957935883110, 1009⟩

private noncomputable def tree127_25 : AbundanceTree :=
  .split 2995183555466410410776093988201797 [
    (2, .abundant [(3, 2), (5, 2), (7, 2)])]

private theorem checked127_25 : replayAbundance bank 127 1 (10^300) 4 state127_25 tree127_25 = true := by
  decide +kernel

theorem reject127_25 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_25 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree127_25 checked127_25

@[expose] noncomputable def state127_26 : State := ⟨3585736413028372510698572245226694822155553013389682888935111363920113984410696980041, 3630040134209393081097278582437281887997357523786657219948418476300012170375269398770, 1009⟩

private noncomputable def tree127_26 : AbundanceTree :=
  .split 3340270099229405074670185272299950407130423112103637 []

private theorem checked127_26 : replayAbundance bank 127 1 (10^300) 3 state127_26 tree127_26 = true := by
  decide +kernel

theorem reject127_26 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_26 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_26 checked127_26

@[expose] noncomputable def state127_27 : State := ⟨351291010647976626500628424292614065031757373168773842946083925211889646938731572437636729, 355631401908360030762019285442798069285213119247855021181126609704635892470924055576523510, 1009⟩

private noncomputable def tree127_27 : AbundanceTree :=
  .split 19305207276618397993460983952637983129 [
    (2, .round 1 [(202269050122553469545410099, 1)])]

private theorem checked127_27 : replayAbundance bank 127 1 (10^300) 4 state127_27 tree127_27 = true := by
  decide +kernel

theorem reject127_27 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_27 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree127_27 checked127_27

@[expose] noncomputable def state127_28 : State := ⟨330318624840417034387148968674302742106998224842133277681536783440048426281865189085341254189219567492361, 334399890881795792009911658655185962352432003905309967468486232277301159317031802464844934671708924842370, 1009⟩

private noncomputable def tree127_28 : AbundanceTree :=
  .split 163072747762875039437002169213 [
    (2, .round 1 [(496001166067871682287399843, 1)])]

private theorem checked127_28 : replayAbundance bank 127 1 (10^300) 4 state127_28 tree127_28 = true := by
  decide +kernel

theorem reject127_28 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_28 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree127_28 checked127_28

@[expose] noncomputable def state127_29 : State := ⟨3170373374439033295994012424064497367739503994995001270348366102618892237659482319959181582785756303944555818722921, 3209545059650064132636695468011521040159213409338024017207881989659152670723177249308156523494844957601566247876170, 1009⟩

private noncomputable def tree127_29 : AbundanceTree :=
  .round 1 [(7368657321755381452803984662866303, 1), (80949558969318552139575933139372374001531091453, 1)]

private theorem checked127_29 : replayAbundance bank 127 1 (10^300) 3 state127_29 tree127_29 = true := by
  decide +kernel

theorem reject127_29 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_29 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_29 checked127_29

@[expose] noncomputable def state127_30 : State := ⟨310598309120417652975237403173174742620071466885665279454759078707470253631261823404081060483937759341144189004465847449, 314435919948857133010284418305620704783357978499436874941838990644917527998078951937470786450266465651419273026028924110, 1009⟩

private noncomputable def tree127_30 : AbundanceTree :=
  .split 15363127765469921 [
    (2, .round 1 [(509774718656917544953049073901, 1)])]

private theorem checked127_30 : replayAbundance bank 127 1 (10^300) 4 state127_30 tree127_30 = true := by
  decide +kernel

theorem reject127_30 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_30 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree127_30 checked127_30

@[expose] noncomputable def state127_31 : State := ⟨2981099263951250546236066986816634467807934471625811718769872631767792364492488744776403599686136959950778725946064497702775274489, 3017932364712133720342305888164882289038603639238246506448111871553899429759178332849370172479313095777006180488524343933578188310, 1009⟩

private noncomputable def tree127_31 : AbundanceTree :=
  .round 1 [(2978097191205427408503368567192618347328225257518159337726830406283334141483248991221, 1)]

private theorem checked127_31 : replayAbundance bank 127 1 (10^300) 3 state127_31 tree127_31 = true := by
  decide +kernel

theorem reject127_31 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_31 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_31 checked127_31

@[expose] noncomputable def state127_32 : State := ⟨2803124986218113050790383724271204222630952882987041844190860431373851596788089588706662711300636545373970310253840545823055869454231023164824201, 2837759118100683403117999352989272059203488891692349570310445886772261989476382978288992085270492682666085646686487316525437617707897378331985570, 1009⟩

private noncomputable def tree127_32 : AbundanceTree :=
  .round 1 [(107, 1), (218149, 1), (1119754280001961, 1)]

private theorem checked127_32 : replayAbundance bank 127 1 (10^300) 3 state127_32 tree127_32 = true := by
  decide +kernel

theorem reject127_32 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_32 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_32 checked127_32

@[expose] noncomputable def state127_33 : State := ⟨477899867569321, 482258878498170, 1009⟩

private theorem checked127_33 : checkChildren bank 127 1 (10^300) state127_33 313 [state127_18, state127_19, state127_20, state127_21, state127_22, state127_23, state127_24, state127_25, state127_26, state127_27, state127_28, state127_29, state127_30, state127_31, state127_32] = true := by
  decide +kernel

theorem reject127_33 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_33 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state127_18, state127_19, state127_20, state127_21, state127_22, state127_23, state127_24, state127_25, state127_26, state127_27, state127_28, state127_29, state127_30, state127_31, state127_32] ?_ checked127_33
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject127_18 ho hN hs hav hx hvalid
  · exact reject127_19 ho hN hs hav hx hvalid
  · exact reject127_20 ho hN hs hav hx hvalid
  · exact reject127_21 ho hN hs hav hx hvalid
  · exact reject127_22 ho hN hs hav hx hvalid
  · exact reject127_23 ho hN hs hav hx hvalid
  · exact reject127_24 ho hN hs hav hx hvalid
  · exact reject127_25 ho hN hs hav hx hvalid
  · exact reject127_26 ho hN hs hav hx hvalid
  · exact reject127_27 ho hN hs hav hx hvalid
  · exact reject127_28 ho hN hs hav hx hvalid
  · exact reject127_29 ho hN hs hav hx hvalid
  · exact reject127_30 ho hN hs hav hx hvalid
  · exact reject127_31 ho hN hs hav hx hvalid
  · exact reject127_32 ho hN hs hav hx hvalid

@[expose] noncomputable def state127_34 : State := ⟨4427087072311321525909, 4467958315829966702754, 9181⟩

private noncomputable def tree127_34 : AbundanceTree :=
  .split 4591 [
    (2, .split 55333 [
      (2, .split 2780923 [
        (2, .split 135676061629 [
          (2, .split 201858430533847 [
            (2, .split 147033322138041055009 [
              (2, .split 7206265939649651266639461995378601681697 []),
              (4, .round 1 [(23011, 1), (7105807, 1)])]),
            (4, .split 473250449073027883507026458058252666083581891 []),
            (6, .split 23011 [
              (2, .abundant [(3, 8), (7, 2), (19, 2), (31, 2), (37, 2), (43, 2)]),
              (4, .abundant [(3, 8), (5, 2), (19, 2), (31, 2)])])]),
          (4, .split 577849383685113804256051 [
            (2, .split 69910810187626468050097 [
              (2, .abundant [(3, 8), (7, 2), (11, 2), (13, 2)])])]),
          (6, .split 40856552998479279475931725979 [
            (2, .round 1 [(22822493, 1), (14957593125707, 1)])]),
          (10, .round 1 [(23, 1), (31, 1), (37, 1), (67, 1), (313, 1), (367, 1), (2311, 1)])]),
        (4, .split 155062027558931 [
          (2, .split 358869140159504955234409279 [
            (2, .split 6079671002005370845171 [
              (2, .round 1 [(707236734824410577063252238741697, 1)])])]),
          (4, .abundant [(3, 6), (5, 2), (11, 2)]),
          (6, .round 1 [(209951121133205324945080506392389202469290191023356297779, 1)])]),
        (6, .split 87381383025387109 [
          (2, .split 2021584039267631893027 [
            (2, .round 1 [(323101, 1), (3641611, 1), (10275301, 1), (762566461, 1), (2232385011981583, 1), (8951019226419165463, 1)])]),
          (4, .round 1 [(10275301, 1), (18480001, 1), (5704849278662661579705432216684455217934495561, 1)])]),
        (10, .split 1202712875227062586821012072493425230706822336789153751809863971 []),
        (12, .split 4382675087186034703486274233187 [
          (2, .round 1 [(4077232205442818274168554694838249983858340318719399517387, 1)])]),
        (16, .split 949277008987 [
          (2, .round 1 [(5554122337, 1)])]),
        (18, .split 367 [
          (2, .round 1 [(31, 1), (37, 1), (191, 1), (313, 1), (3463, 1)]),
          (4, .round 1 [(5885051, 1)])])]),
      (4, .split 22926121 [
        (2, .split 250590853 [
          (2, .abundant [(3, 6), (7, 2), (11, 2), (31, 2), (37, 2)]),
          (4, .split 3943309449854352684895457937015821 [
            (2, .round 1 [(11, 1), (31, 1), (37, 1), (157, 1), (251, 1), (313, 1), (3191, 1), (8599, 1), (46411, 1), (699157, 1), (5876179, 1), (577515739, 1)])]),
          (6, .split 2139109153695913932952690972108490041 [
            (2, .round 1 [(699157, 1)])]),
          (10, .round 1 [(503450465371484911300970576103124443951582890130884789, 1)]),
          (12, .round 1 [(46411, 1), (699157, 1)])]),
        (4, .abundant [(3, 4), (5, 2), (11, 4)]),
        (6, .abundant [(3, 4), (7, 2), (11, 2), (31, 2), (37, 2)]),
        (10, .round 1 [(251, 1), (313, 1), (661, 1), (3191, 1), (46411, 1), (11235533, 1), (5401453999912054294903561906118030238109101698398612191623375347, 1)]),
        (12, .round 1 [(6453697706997278141, 1), (69261021890097562799, 1), (272155755642134533917570413267, 1)])]),
      (6, .split 56186222638043 [
        (2, .split 18046347790267 [
          (2, .split 109162124431 [
            (2, .split 33565630407553129 [
              (2, .abundant [(3, 8), (7, 2), (13, 2), (19, 2), (31, 2)])]),
            (4, .abundant [(3, 6), (5, 2), (19, 2), (31, 2)]),
            (6, .round 1 [(49722523, 1)])]),
          (4, .round 1 [(135913, 1), (141667, 1), (185167, 1), (4665461, 1), (49722523, 1), (74584300382201, 1), (454247752900804647037593007411, 1)]),
          (6, .round 1 [(13378770390594513113189533947074191247524887689017724425653077018711297899, 1)])]),
        (4, .split 903716551382580990289363207931 [
          (2, .round 1 [(1588537271, 1), (900282886291, 1)])]),
        (6, .split 587959 [
          (2, .split 115232124547 [
            (2, .abundant [(3, 6), (7, 2), (19, 2), (31, 2), (37, 2), (43, 2)])]),
          (4, .abundant [(3, 4), (7, 2), (11, 2), (31, 2), (37, 2)])])]),
      (10, .split 970423624929375339921944970770789 [
        (2, .split 440089295235970403642553674737477 [])]),
      (12, .split 17344455173293941941 [
        (2, .split 7478888882073296068963969 [
          (2, .round 1 [(58192157113793467526100876693478568161711, 1)])]),
        (4, .split 313 [
          (2, .abundant [(3, 6), (5, 2), (31, 2), (37, 2), (127, 2), (181, 2)])])]),
      (16, .split 1043731261579594321911248548626099228857 []),
      (18, .split 23644152743289183546829748843947141789260327256216116509553642884199217662715680573103 []),
      (22, .round 1 [(2476987249829175456439603640381372893411232326350669875712975479817233107747, 1)])]),
    (4, .abundant [(3, 4), (5, 2), (11, 2)]),
    (6, .split 36825984292217 [
      (2, .split 11283786030043965307 [
        (2, .abundant [(3, 4), (7, 2), (13, 2), (19, 2), (31, 2)]),
        (4, .round 1 [(164515848457564094102875791641, 1), (6272420103770092126179818941244106672451, 1)])]),
      (4, .split 3874101370963826934970957668931 [
        (2, .round 1 [(191674155939156908411641168172542199346549023624878898131, 1)])]),
      (6, .round 1 [(3080393, 1), (83926109, 1), (254322041, 1), (176526355054622623, 1), (22676213039515291859, 1), (831634130554243836667, 1)])]),
    (10, .split 72777851643949 [
      (2, .split 13274726039871486064461049 [
        (2, .abundant [(3, 6), (7, 2), (19, 2), (31, 2), (37, 2), (61, 2), (127, 2)])]),
      (4, .split 427387421986058585403402593524941313464176846023061 []),
      (6, .round 1 [(19653367822322188670397594393132545889744061865696458081255130190017, 1)])]),
    (12, .split 168323362076580637193136639975988773259673 [
      (2, .round 1 [(298725361897414193827497940520915232637901061972206004293803539865150686271, 1)])]),
    (16, .split 2348383615023098252823547325797 [
      (2, .round 1 [(955801233000296205155233, 1), (66398616087174002265335853628774815585259904511103, 1)])]),
    (18, .split 47425797106677360529764391 [
      (2, .round 1 [(20939, 1), (2334037, 1), (442078452317, 1), (1053085325072189, 1), (13645449103592241758355441043, 1)])]),
    (22, .split 326298558974471585266378160226439826060191 []),
    (28, .round 1 [(149015844837106590107, 1), (40322565183251362647536689892189735357504392997, 1)]),
    (30, .round 1 [(2319142991665190623724414102455143650147751230287060093236923024588248666906381, 1)]),
    (36, .round 1 [(15528266980739275031103490772205716227193065976300259527153692990461050087829777977790076921081035733, 1)])]

private theorem checked127_34 : replayAbundance bank 127 1 (10^300) 9 state127_34 tree127_34 = true := by
  decide +kernel

theorem reject127_34 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_34 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 9 h tree127_34 checked127_34

@[expose] noncomputable def state127_35 : State := ⟨40645086410890242929370529, 41020325784234610186676121, 0⟩

private noncomputable def tree127_35 : AbundanceTree :=
  .abundant [(3, 4), (7, 2), (13, 1), (31, 2), (37, 1), (127, 2)]

private theorem checked127_35 : replayAbundance bank 127 1 (10^300) 3 state127_35 tree127_35 = true := by
  decide +kernel

theorem reject127_35 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_35 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_35 checked127_35

@[expose] noncomputable def state127_36 : State := ⟨3426005264484697263991511140382569, 3457634476825525053489112266320835, 0⟩

private noncomputable def tree127_36 : AbundanceTree :=
  .split 125642407351 [
    (2, .split 7178724204220218847 [
      (2, .split 5385571182634843 [
        (2, .abundant [(3, 6), (5, 1), (7, 2)]),
        (4, .round 20812477983356377161743056612833664065402101 [(733, 1), (11311, 1), (34807, 1), (2729983, 1), (53543431, 1), (70414451, 1), (33567189193, 1), (20812477983356377161743056612833664065402101, 1)])]),
      (4, .split 27027804317000496719976756880243090104708391449142128121 [
        (1, .abundant [(3, 4), (5, 2), (7, 2)])]),
      (6, .abundant [(3, 4), (5, 1), (7, 2)])]),
    (4, .split 3448779827100966326231 [
      (2, .abundant [(3, 4), (5, 2), (7, 2)]),
      (4, .abundant [(3, 4), (5, 3), (31, 2), (37, 1), (127, 2), (181, 1)])]),
    (6, .split 5872649716518454235362120201146737504621684775030100774043923 []),
    (10, .abundant [(3, 4), (5, 1), (23, 2), (31, 2), (37, 1), (67, 2)])]

private theorem checked127_36 : replayAbundance bank 127 1 (10^300) 6 state127_36 tree127_36 = true := by
  decide +kernel

theorem reject127_36 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_36 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree127_36 checked127_36

@[expose] noncomputable def state127_37 : State := ⟨288780590933421405236462371562824572145009, 291446641311460370987630936458447819008189, 0⟩

private noncomputable def tree127_37 : AbundanceTree :=
  .split 19937168287 [
    (2, .split 204245563 [
      (2, .split 15251867 [
        (2, .split 232619462237557 [
          (1, .abundant [(3, 6), (7, 2), (11, 2), (31, 2), (37, 2)]),
          (2, .abundant [(3, 6), (7, 2), (19, 2), (31, 2), (37, 1), (43, 2), (97, 1)]),
          (4, .split 46153 [
            (1, .split 38431 [
              (2, .abundant [(3, 6), (7, 2), (13, 2), (31, 2), (37, 2)]),
              (4, .abundant [(3, 6), (5, 2), (7, 2)])]),
            (2, .abundant [(3, 6), (7, 2), (13, 1), (31, 2), (37, 1), (97, 1)]),
            (4, .round 4537421804830318421 [(1117, 1), (1279, 1), (17431, 1), (25981, 1), (38431, 1), (4537421804830318421, 1)])])]),
        (4, .abundant [(3, 6), (7, 2), (11, 2), (31, 2), (37, 1)]),
        (6, .split 1546180993982253931724756630608282852337 [
          (1, .round 1 [(6257, 1), (17431, 1), (25981, 1), (38431, 1), (46153, 1), (2579964631, 1), (15963538828617788246719669, 1)])]),
        (10, .round 46153 [(37, 1), (97, 1), (113, 1), (313, 1), (373, 1), (541, 1), (1117, 1), (1279, 1), (2069, 1), (17431, 1), (25981, 1), (38431, 1), (46153, 1)]),
        (12, .round 46153 [(25981, 1), (38431, 1), (46153, 1)])]),
      (4, .split 2228227302196697569006171908461 [
        (1, .split 2339017532969207 [
          (2, .round 1 [(71, 1), (113, 1), (313, 1), (379, 1), (541, 1), (17431, 1), (25981, 1), (46153, 1), (167107, 1), (1136203, 1), (15251867, 1), (560286943, 1), (51428739319, 1)]),
          (4, .round 1 [(15251867, 1)])]),
        (2, .round 1 [(1087954603, 1), (71236231446169373910345431380445176092220191547, 1)])]),
      (6, .split 71650091253163948244059977808135802039931877 [
        (1, .round 1 [(17431, 1), (23563, 1), (25981, 1), (46153, 1), (15251867, 1), (67917427, 1), (182279221603978079972592179543, 1)])]),
      (10, .round 11300690413 [(113, 1), (313, 1), (541, 1), (17431, 1), (25981, 1), (46153, 1), (61909, 1), (15251867, 1), (33453179, 1), (11300690413, 1)]),
      (12, .round 1 [(15251867, 1)])]),
    (4, .split 42617437942164780762375495251 [
      (2, .split 363365502979690803374404817362406101 [
        (1, .round 1 [(164277469, 1), (8220344521, 1), (268852715768861340109967, 1)])])]),
    (6, .split 473828723763234979442057307167894204197761329 [
      (1, .abundant [(3, 4), (5, 2), (7, 2)])]),
    (10, .split 15251867 [
      (2, .round 232619462237557 [(313, 1), (17431, 1), (708599, 1), (232619462237557, 1)])])]

private theorem checked127_37 : replayAbundance bank 127 1 (10^300) 9 state127_37 tree127_37 = true := by
  decide +kernel

theorem reject127_37 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_37 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 9 h tree127_37 checked127_37

@[expose] noncomputable def state127_38 : State := ⟨2051766574114401013807089779108265877233849515256794177089, 2070708681798592820781264141680662044370199368758236400417, 0⟩

private noncomputable def tree127_38 : AbundanceTree :=
  .split 103487890442126237477849 [
    (1, .abundant [(3, 4), (5, 2), (7, 2)]),
    (2, .split 306369066800970422402344104226042618159543 [
      (2, .round 1 [(2813416783, 1)])]),
    (4, .round 1 [(4314194581938681498027662837439961873986735211718067797654538417221055221386539765871, 1)])]

private theorem checked127_38 : replayAbundance bank 127 1 (10^300) 5 state127_38 tree127_38 = true := by
  decide +kernel

theorem reject127_38 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_38 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree127_38 checked127_38

@[expose] noncomputable def state127_39 : State := ⟨172944965926465762512971104676357632182373750600476291607200574729, 174541610598110237592789369044274822703779874982309687039016350091, 0⟩

private noncomputable def tree127_39 : AbundanceTree :=
  .split 8300232987522702063607043 [
    (2, .split 3985908625189819904247611107302801645958249 [
      (1, .abundant [(3, 4), (5, 4), (19, 2), (31, 2)])]),
    (4, .round 1 [(2190130430567, 1)])]

private theorem checked127_39 : replayAbundance bank 127 1 (10^300) 5 state127_39 tree127_39 = true := by
  decide +kernel

theorem reject127_39 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_39 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree127_39 checked127_39

@[expose] noncomputable def state127_40 : State := ⟨1228762290091323137042348202843366062328188824081122697116287650294076820015653209, 1240106342534145613363964670167775895272432098714655331552479647349213207876788559, 0⟩

private noncomputable def tree127_40 : AbundanceTree :=
  .split 2717635850124854249 [
    (1, .abundant [(3, 4), (5, 4), (17, 2), (31, 2)]),
    (2, .split 156509735616657751 [
      (2, .round 1 [(73603473319847, 1), (628084547251182254517653525257327, 1)])]),
    (4, .round 1 [(2283461629543, 1), (73603473319847, 1)])]

private theorem checked127_40 : replayAbundance bank 127 1 (10^300) 5 state127_40 tree127_40 = true := by
  decide +kernel

theorem reject127_40 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_40 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree127_40 checked127_40

@[expose] noncomputable def state127_41 : State := ⟨103573308519900386718206819244649689195216467733492957874304391538189608951579440898702049, 104529507333129802235260352025555827889969603921485419749265820912081282001501531840906153, 0⟩

private noncomputable def tree127_41 : AbundanceTree :=
  .split 854469555558683086335526541841674893 [
    (1, .split 118085024551805774505651739081667 [
      (2, .round 1 [(13802692086536369, 1)])]),
    (2, .round 1 [(118085024551805774505651739081667, 1)])]

private theorem checked127_41 : replayAbundance bank 127 1 (10^300) 5 state127_41 tree127_41 = true := by
  decide +kernel

theorem reject127_41 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_41 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree127_41 checked127_41

@[expose] noncomputable def state127_42 : State := ⟨735881354438269243888728424861533334402624480016472750253573361533981585379821058274947280934969068938929, 742675082357623390245324662003598501398257698328918708250598007244255405312503899095156616835681029530061, 0⟩

private noncomputable def tree127_42 : AbundanceTree :=
  .split 1790930171154308638447128742686546115997197736844515325484208339295730577 [
    (1, .round 1 [(47, 1), (313, 1), (395803, 1), (1535719, 1), (18132200719277, 1)])]

private theorem checked127_42 : replayAbundance bank 127 1 (10^300) 4 state127_42 tree127_42 = true := by
  decide +kernel

theorem reject127_42 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_42 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree127_42 checked127_42

@[expose] noncomputable def state127_43 : State := ⟨440704741817601764030897952346032777182544112991336039708948705621839578979292298293285610111690447967004773768481397618916402249, 444773370667375347231262090496234101740375036264169806407591413767238835142381153439252894983002320981694106076188683432449053723, 0⟩

private noncomputable def tree127_43 : AbundanceTree :=
  .round 18476667209739417836226575582820864051602717104805244317 [(7309, 1), (5509073, 1), (28460541731811529127, 1), (731663943395682064763777, 1), (18476667209739417836226575582820864051602717104805244317, 1)]

private theorem checked127_43 : replayAbundance bank 127 1 (10^300) 3 state127_43 tree127_43 = true := by
  decide +kernel

theorem reject127_43 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_43 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_43 checked127_43

@[expose] noncomputable def state127_44 : State := ⟨37147338064114175885106815916588838119660079200109701193793504906829836332084151064580045266663682855569735271578134819642051540950321489, 37490285886088145890762324598378440069847636232109470015318556443506438282904850775452393789570347700313263270376672574067538662008255957, 0⟩

private noncomputable def tree127_44 : AbundanceTree :=
  .split 3750683983908057292314007326713033856419814387917689363755371701839033835232666649248479223758262724481 []

private theorem checked127_44 : replayAbundance bank 127 1 (10^300) 3 state127_44 tree127_44 = true := by
  decide +kernel

theorem reject127_44 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_44 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_44 checked127_44

@[expose] noncomputable def state127_45 : State := ⟨482200966377444889, 486599685888691647, 0⟩

private theorem checked127_45 : checkChildren bank 127 1 (10^300) state127_45 9181 [state127_34, state127_35, state127_36, state127_37, state127_38, state127_39, state127_40, state127_41, state127_42, state127_43, state127_44] = true := by
  decide +kernel

theorem reject127_45 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_45 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state127_34, state127_35, state127_36, state127_37, state127_38, state127_39, state127_40, state127_41, state127_42, state127_43, state127_44] ?_ checked127_45
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject127_34 ho hN hs hav hx hvalid
  · exact reject127_35 ho hN hs hav hx hvalid
  · exact reject127_36 ho hN hs hav hx hvalid
  · exact reject127_37 ho hN hs hav hx hvalid
  · exact reject127_38 ho hN hs hav hx hvalid
  · exact reject127_39 ho hN hs hav hx hvalid
  · exact reject127_40 ho hN hs hav hx hvalid
  · exact reject127_41 ho hN hs hav hx hvalid
  · exact reject127_42 ho hN hs hav hx hvalid
  · exact reject127_43 ho hN hs hav hx hvalid
  · exact reject127_44 ho hN hs hav hx hvalid

@[expose] noncomputable def state127_46 : State := ⟨490919642050515470038009, 495397895291503959167577, 0⟩

private noncomputable def tree127_46 : AbundanceTree :=
  .split 1037517185381 [
    (1, .split 172919530897 [
      (2, .split 4590514719337 [
        (2, .split 1993800800670793 [
          (2, .split 28139916843675431872408729 [
            (2, .round 1 [(167017549, 1), (3523057633, 1), (308846848564964968060926540995921881897, 1)])]),
          (4, .round 1 [(167017549, 1), (3523057633, 1), (1252177447598024861, 1), (1735669540278444531735657542800443238271, 1)]),
          (6, .round 1 [(62818938916943713724293329489477630385792505500459422757805502240535452147851295164091552943, 1)])]),
        (4, .split 559987787876927662781 [
          (2, .abundant [(3, 4), (7, 2), (13, 2), (31, 2), (71, 2), (127, 2), (191, 2), (211, 2)])]),
        (6, .round 1 [(167017549, 1), (870686926998627797564934955733034184907573178618434553658334182039297, 1)])]),
      (4, .split 31583933249065988831 [
        (2, .split 768822705457273759 [
          (2, .round 1 [(15069283300651, 1), (34062268434687011, 1), (10934538587539854646349560392313, 1)])]),
        (4, .abundant [(3, 4), (5, 2), (11, 2)])]),
      (6, .split 15246374721662814592971018530162180783660880447517 []),
      (10, .round 1 [(12463658802959333368374299982523524813284113818387501263913421042493126668972110109693800550692795369129449, 1)])]),
    (2, .split 127992782604139 [
      (2, .split 9383676751 [
        (2, .split 6305373793 [
          (1, .split 50062963 [
            (2, .split 835433438134111 [
              (2, .split 1849863004983048103 [
                (2, .round 1 [(20116013061026119723051496443, 1)])]),
              (4, .abundant [(3, 6), (5, 2), (11, 2)])]),
            (4, .split 67307521443843128668351 [
              (2, .round 1 [(24755751054171598929498710980184837014632391, 1)])]),
            (6, .split 4429057 [
              (2, .round 1 [(109, 3), (313, 1), (373, 1), (727, 1), (1051, 1), (1399, 1), (2087, 1), (8269, 1), (13859, 1), (16225434523, 1)]),
              (4, .round 1 [(384808960292493267874730501, 1)])])]),
          (2, .split 50062963 [
            (2, .split 835433438134111 [
              (2, .round 4429057 [(1051, 1), (1399, 1), (8269, 1), (33457, 1), (87931, 1), (4429057, 1), (5513779, 1), (1877102911, 1), (1849863004983048103, 1)])]),
            (4, .round 8484181 [(19, 1), (31, 1), (61, 1), (313, 1), (373, 1), (727, 1), (1051, 1), (1399, 1), (8269, 1), (33457, 1), (87931, 1), (4429057, 1), (5513779, 1), (8484181, 1), (67307521443843128668351, 1)]),
            (6, .round 4429057 [(43, 3), (61, 1), (313, 1), (373, 1), (727, 1), (1051, 1), (1399, 1), (8269, 1), (33457, 1), (87931, 1), (4429057, 1), (5513779, 1)])]),
          (4, .split 22077202402189461431 [
            (2, .abundant [(3, 4), (7, 2), (11, 2), (31, 2), (43, 2)])]),
          (6, .round 4429057 [(31, 1), (43, 1), (61, 1), (281, 1), (313, 1), (373, 1), (727, 1), (1051, 1), (1399, 1), (8269, 1), (4429057, 1), (50062963, 1), (52778228147, 1)])]),
        (4, .abundant [(3, 4), (5, 1), (11, 2), (31, 2)]),
        (6, .split 36817013819668573173929 [
          (1, .abundant [(3, 4), (5, 2), (7, 2)]),
          (2, .round 1 [(50062963, 1)])])]),
      (4, .split 268374917215885156055938146567048670991350618006189678121 [
        (1, .round 1 [(31, 1), (313, 1), (727, 1), (1399, 1), (8269, 1), (40961, 1), (2133942222269565329, 1), (511725979422393004299244585171223, 1)])]),
      (6, .round 94529 [(1399, 1), (8269, 1), (94529, 1), (215725987, 1), (85174239230104911305393397366771392235065528974694071, 1)])]),
    (4, .split 81894380096869093891 [
      (2, .abundant [(3, 4), (5, 1), (7, 2)]),
      (4, .abundant [(3, 2), (5, 2), (11, 2), (31, 2)])]),
    (6, .split 53749796710026252467472921924601285997088061429877 [
      (1, .split 11124772385569 [
        (2, .round 1 [(3259149331, 1), (116680380199, 1), (31695515609568566461, 1)])])]),
    (10, .round 1 [(178776808715465708332382791517567063496502884116193022374924358597233798334388469886474399, 1)])]

private theorem checked127_46 : replayAbundance bank 127 1 (10^300) 10 state127_46 tree127_46 = true := by
  decide +kernel

theorem reject127_46 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_46 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 10 h tree127_46 checked127_46

@[expose] noncomputable def state127_47 : State := ⟨499795960098430840251766240729, 504355184636270124512164457907, 0⟩

private noncomputable def tree127_47 : AbundanceTree :=
  .split 1024823381 [
    (1, .abundant [(3, 4), (7, 2), (11, 2), (29, 2), (31, 2)]),
    (2, .split 27647957545189 [
      (1, .abundant [(3, 2), (5, 2), (7, 2)]),
      (2, .split 36441801894643 [
        (2, .split 7256857515455970416797771 [
          (2, .split 37935858347491087933 [
            (1, .round 1 [(5077297, 1), (8845231, 1), (35909757982597, 1), (1905290008503743683, 1)]),
            (2, .round 1 [(392888111144272273695943, 1)])])]),
        (4, .split 173453031169722671664927133411811799441856621 [
          (1, .abundant [(3, 4), (7, 2), (13, 2), (29, 2), (31, 2)])]),
        (6, .split 48658209768512811411948644203422805445580520258841696128953119421440350582321 [])]),
      (4, .abundant [(3, 2), (7, 2), (11, 2), (29, 1), (31, 2), (41, 1)]),
      (6, .round 1 [(47079202116283, 1), (4172286104965247278170778891, 1), (78411028446588445142726280221341972463, 1)])]),
    (4, .abundant [(3, 2), (5, 1), (7, 2)]),
    (6, .split 29796246480057232066027150958735863 [
      (2, .round 8861968484509756514131152583092244419181 [(4271, 1), (5077297, 1), (7731517, 1), (132342307, 1), (18366263737, 1), (884081512427, 1), (8861968484509756514131152583092244419181, 1)])]),
    (10, .round 1 [(964754322902390744864555579994083, 1), (19769637942300353366302567885660611743451476641184822351, 1)]),
    (12, .split 1074548107532322743221172315841634086094472396726615577470984506555558138379359739562795407847241597844197 [])]

private theorem checked127_47 : replayAbundance bank 127 1 (10^300) 8 state127_47 tree127_47 = true := by
  decide +kernel

theorem reject127_47 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_47 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree127_47 checked127_47

@[expose] noncomputable def state127_48 : State := ⟨518032976182763129119327100830434565186969, 522758561911701842037857633797604241049767, 0⟩

private noncomputable def tree127_48 : AbundanceTree :=
  .split 23223849323621 [
    (1, .split 16441151 [
      (2, .split 583826053231 [
        (2, .split 2642270235905971097617 [
          (2, .split 122484070167624493961943560700758907266251 []),
          (4, .round 1 [(4647193, 1)])]),
        (4, .abundant [(3, 4), (5, 2), (11, 2)]),
        (6, .split 4647193 [
          (2, .split 3654361 [
            (2, .abundant [(3, 6), (7, 2), (13, 2), (19, 2), (31, 2)])]),
          (4, .round 1 [(463, 1), (617, 1), (10987, 1), (431203, 1)])])]),
      (4, .abundant [(3, 4), (5, 2), (19, 2), (31, 2)]),
      (6, .split 158594524402445937838461492730549 [
        (2, .round 1 [(43, 1), (109, 1), (313, 1), (617, 1), (10987, 1), (23339, 1), (184003, 1), (431203, 1), (4647193, 1)])]),
      (10, .split 4647193 [
        (2, .split 3654361 [
          (2, .abundant [(3, 6), (7, 2), (11, 2), (13, 2)]),
          (4, .abundant [(3, 4), (5, 2), (11, 2)])]),
        (4, .split 431203 [
          (2, .round 1 [(61978819471, 1)])])]),
      (12, .split 4647193 [
        (2, .round 1 [(10987, 1), (11779, 1), (431203, 1), (1969921, 1), (3654361, 1)])])]),
    (2, .split 14198034740741233771 [
      (2, .split 2941185658598897653784418433 [
        (1, .split 68850965932542701 [
          (2, .round 1 [(4647193, 1), (5426779, 1), (16441151, 1), (123460400377, 1), (314960887193504371, 1)])]),
        (2, .round 569953323701169877317689682008525521213 [(313, 1), (617, 1), (465649, 1), (1195189, 1), (4647193, 1), (5426779, 1), (16441151, 1), (19506889, 1), (569953323701169877317689682008525521213, 1)])]),
      (4, .abundant [(3, 2), (5, 1), (7, 2)])]),
    (4, .split 1191850517219227015813600550636941 [
      (1, .split 2176489158895909531613711 [
        (2, .abundant [(3, 2), (5, 2), (7, 2)])]),
      (2, .round 4647193 [(4357, 1), (4647193, 1), (16441151, 1), (45119171, 1), (1081892014831, 1)])]),
    (6, .split 12933736453792298698115580808289801474315830097094889 [
      (1, .abundant [(3, 2), (5, 2), (17, 2), (29, 2), (31, 2)])])]

private theorem checked127_48 : replayAbundance bank 127 1 (10^300) 8 state127_48 tree127_48 = true := by
  decide +kernel

theorem reject127_48 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_48 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree127_48 checked127_48

end OddPerfect.IndexComponent.Size300
