module

public import OddPerfect.SizeIndex300.Seed3

public section

namespace OddPerfect.IndexComponent.Size300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def state5_1 : State := ⟨15625, 19531, 0⟩

private noncomputable def tree5_1 : AbundanceTree :=
  .split 19531 [
    (4, .split 32009891 [
      (6, .split 48354147450197362090513183675650958992851 [
        (2, .split 2338123575635428053751468411037490625854313922146971562881145410608899239228101053 [])]),
      (12, .split 4760281 [
        (1, .split 2380141 [])]),
      (16, .round 1 [(580378093713237611789992922436247791988453286018775834675335571683987642599, 1)])]),
    (10, .split 116301562592326723759559809 [
      (4, .split 31567260539 [])]),
    (12, .split 542484773057617547 [
      (2, .split 8424404688958143112702264814929 [
        (1, .split 22468639757 [])])]),
    (16, .split 4352879976166398326610980128472731265540049676664742316696650089399 []),
    (18, .split 5751121849207819585780202063999542303315009 []),
    (22, .split 138364619824953525297520160494079932676629423304297 []),
    (28, .round 1 [(11028723756586598750754952481589981746437696424375893070113012395419614425407963845549415707098187, 1)])]

private theorem checked5_1 : replayAbundance bank 5 224633409 (10^300) 6 state5_1 tree5_1 = true := by
  decide +kernel

theorem reject5_1 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_1 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree5_1 checked5_1

@[expose] noncomputable def state5_2 : State := ⟨9765625, 12207031, 0⟩

private noncomputable def tree5_2 : AbundanceTree :=
  .split 12207031 [
    (4, .split 33899939683211028917156831 [
      (2, .split 346895893309557449642507136763460222413699 []),
      (4, .split 2102184759694012771 [])]),
    (6, .split 87368232016235494292855682382769680247 []),
    (12, .split 6723474387225189124132237042213 [
      (1, .split 23773994335181800316133670391 [
        (2, .round 1 [(105007244872456434743, 1)])])]),
    (16, .round 1 [(27407390005963591968584993238900863877065178542962821241284765134221793297740520717960839008743, 1)]),
    (18, .split 229132119504958635358235114934920106892674298469415168019284435364613377792641957972541533920989 [])]

private theorem checked5_2 : replayAbundance bank 5 224633409 (10^300) 6 state5_2 tree5_2 = true := by
  decide +kernel

theorem reject5_2 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_2 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree5_2 checked5_2

@[expose] noncomputable def state5_3 : State := ⟨244140625, 305175781, 0⟩

private noncomputable def tree5_3 : AbundanceTree :=
  .split 305175781 [
    (1, .split 43609 [
      (6, .split 5968930061879 [
        (2, .split 51193000249429 [
          (6, .round 1 [(691, 1), (3499, 1), (4243, 1), (17137, 1), (237373, 1), (4930927, 1), (67241197577, 1)])])]),
      (10, .split 371275623291490722517947874992277163647292753 []),
      (12, .split 47306791574323349111302419726723197703462364929251918941 []),
      (16, .split 472707741919638729693156241187809665627111328388540297 []),
      (18, .split 538910623579515210492433674427269161124617093 []),
      (22, .round 1 [(1519020031315566821, 1), (32037751288956970936520890597770723392621306053105937504577103, 1)]),
      (28, .round 1 [(154174929623944042559388140908580603054684586916028287144545058904961195117893187186283286847403, 1)]),
      (30, .round 1 [(3499, 1)])]),
    (10, .split 69578974582861797141313609380633155003252180631220112754924473709869 []),
    (16, .split 11673312666179581 [])]

private theorem checked5_3 : replayAbundance bank 5 224633409 (10^300) 7 state5_3 tree5_3 = true := by
  decide +kernel

theorem reject5_3 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_3 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree5_3 checked5_3

@[expose] noncomputable def state5_4 : State := ⟨152587890625, 190734863281, 0⟩

private noncomputable def tree5_4 : AbundanceTree :=
  .split 466344409 [
    (6, .split 29354039466588511642445029969284062115196649353 [
      (1, .split 10628180594237383 [
        (4, .round 1 [(469823, 1), (4069279, 1), (9143240020375133, 1)])])]),
    (10, .split 86998871734374017298662359233117366205253656643041741 [
      (1, .round 1 [(2742909003061789, 1), (331684566686138521272550493847047077726725188693, 1)])]),
    (12, .split 101575129733962903176164717219488895595781584956747683545056554733469676083500321620734233 []),
    (16, .split 409 [
      (1, .split 103 [])])]

private theorem checked5_4 : replayAbundance bank 5 224633409 (10^300) 6 state5_4 tree5_4 = true := by
  decide +kernel

theorem reject5_4 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_4 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree5_4 checked5_4

@[expose] noncomputable def state5_5 : State := ⟨3814697265625, 4768371582031, 0⟩

private noncomputable def tree5_5 : AbundanceTree :=
  .split 3981071 [
    (4, .split 5378193516362980863601 [
      (4, .split 3484065879573259416731334721061 [])]),
    (10, .split 4901156681547845876139300137066778853806068993 []),
    (12, .split 593474976333784889038624098178709707712846986651 []),
    (16, .split 2859575807666797790108207773083532042940642404247030230421 [])]

private theorem checked5_5 : replayAbundance bank 5 224633409 (10^300) 5 state5_5 tree5_5 = true := by
  decide +kernel

theorem reject5_5 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_5 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree5_5 checked5_5

@[expose] noncomputable def state5_6 : State := ⟨2384185791015625, 2980232238769531, 0⟩

private noncomputable def tree5_6 : AbundanceTree :=
  .split 332207361361 [
    (1, .split 612928711 [
      (4, .split 95124481208472781904103458681 [
        (2, .split 2285125789427381455409651943311414400780523582543 [])]),
      (6, .split 251752038744740852369452390820730866386141 []),
      (10, .round 1 [(271, 1), (8971, 1), (1012397, 1), (321381569252585866953628783126948367071187906389518216907098417372109834635071531, 1)]),
      (12, .round 1 [(10277630575180896943289, 1), (5630767482817854807971038887428864688709, 1)])]),
    (10, .split 2254789917297327037 [
      (1, .round 1 [(8713, 1), (8971, 1), (250088941, 1), (4507976059, 1), (5274951023, 1)])]),
    (12, .round 1 [(357516255917731, 1)])]

private theorem checked5_6 : replayAbundance bank 5 224633409 (10^300) 6 state5_6 tree5_6 = true := by
  decide +kernel

theorem reject5_6 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_6 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree5_6 checked5_6

@[expose] noncomputable def state5_7 : State := ⟨37252902984619140625, 46566128730773925781, 0⟩

private noncomputable def tree5_7 : AbundanceTree :=
  .split 22125996444329 [
    (4, .split 558763069523746264444684871 [
      (2, .split 2938344312511812575066069630259275742025111 [])]),
    (10, .round 1 [(81580408065626825240466042210031375580237805282340863747415866008331366451900439998253353131256863245175059168877576954369487, 1)])]

private theorem checked5_7 : replayAbundance bank 5 224633409 (10^300) 5 state5_7 tree5_7 = true := by
  decide +kernel

theorem reject5_7 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_7 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree5_7 checked5_7

@[expose] noncomputable def state5_8 : State := ⟨931322574615478515625, 1164153218269348144531, 0⟩

private noncomputable def tree5_8 : AbundanceTree :=
  .split 625552508473588471 [
    (4, .split 41851214104513068170325155787681691 [])]

private theorem checked5_8 : replayAbundance bank 5 224633409 (10^300) 4 state5_8 tree5_8 = true := by
  decide +kernel

theorem reject5_8 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_8 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree5_8 checked5_8

@[expose] noncomputable def state5_9 : State := ⟨14551915228366851806640625, 18189894035458564758300781, 0⟩

private noncomputable def tree5_9 : AbundanceTree :=
  .split 8737481256739 [
    (6, .split 2150759895428788587887456760442174819295013690914412569 []),
    (10, .round 1 [(13971969971, 1)])]

private theorem checked5_9 : replayAbundance bank 5 224633409 (10^300) 4 state5_9 tree5_9 = true := by
  decide +kernel

theorem reject5_9 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_9 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree5_9 checked5_9

@[expose] noncomputable def state5_10 : State := ⟨9094947017729282379150390625, 11368683772161602973937988281, 0⟩

private noncomputable def tree5_10 : AbundanceTree :=
  .split 5079304643216687969 [
    (2, .split 4123060561523612941 [
      (1, .split 9726539312579 [
        (2, .split 288848538414427 [
          (4, .round 1 [(211949, 1), (265837681, 1), (2238236249, 1), (4486665151, 1)])]),
        (4, .split 990961692269187430092571 []),
        (6, .round 1 [(9649, 1), (211949, 1), (265837681, 1), (2238236249, 1)])]),
      (4, .split 57797473106759796223875185436086094171363020317320218785184172624274489081 [])]),
    (4, .split 528111989772321909941364227078092606399563643801 [])]

private theorem checked5_10 : replayAbundance bank 5 224633409 (10^300) 7 state5_10 tree5_10 = true := by
  decide +kernel

theorem reject5_10 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_10 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree5_10 checked5_10

@[expose] noncomputable def state5_11 : State := ⟨227373675443232059478759765625, 284217094304040074348449707031, 0⟩

private noncomputable def tree5_11 : AbundanceTree :=
  .split 172827552198815888791 [
    (4, .split 5003658779709479183772406627624630957349864991253211731 []),
    (6, .split 1644512641 [
      (1, .round 1 [(113, 1), (311, 1), (313, 1), (8447, 1)])])]

private theorem checked5_11 : replayAbundance bank 5 224633409 (10^300) 5 state5_11 tree5_11 = true := by
  decide +kernel

theorem reject5_11 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_11 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree5_11 checked5_11

@[expose] noncomputable def state5_12 : State := ⟨142108547152020037174224853515625, 177635683940025046467781066894531, 0⟩

private noncomputable def tree5_12 : AbundanceTree :=
  .split 177635683940025046467781066894531 [
    (4, .split 431 [])]

private theorem checked5_12 : replayAbundance bank 5 224633409 (10^300) 4 state5_12 tree5_12 = true := by
  decide +kernel

theorem reject5_12 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_12 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree5_12 checked5_12

@[expose] noncomputable def state5_13 : State := ⟨2220446049250313080847263336181640625, 2775557561562891351059079170227050781, 0⟩

private noncomputable def tree5_13 : AbundanceTree :=
  .split 27145365052629449 [
    (6, .split 158201441681836806055052932808241583569381031120968150592534440235704442953500859210235261 [])]

private theorem checked5_13 : replayAbundance bank 5 224633409 (10^300) 4 state5_13 tree5_13 = true := by
  decide +kernel

theorem reject5_13 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_13 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree5_13 checked5_13

@[expose] noncomputable def state5_14 : State := ⟨34694469519536141888238489627838134765625, 43368086899420177360298112034797668457031, 0⟩

private noncomputable def tree5_14 : AbundanceTree :=
  .split 2047572230657338751575051 [
    (4, .split 9151 [
      (4, .split 1446260951 []),
      (6, .round 1 [(1397534182102156463, 1)])])]

private theorem checked5_14 : replayAbundance bank 5 224633409 (10^300) 5 state5_14 tree5_14 = true := by
  decide +kernel

theorem reject5_14 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_14 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree5_14 checked5_14

@[expose] noncomputable def state5_15 : State := ⟨867361737988403547205962240695953369140625, 1084202172485504434007452800869941711425781, 0⟩

private noncomputable def tree5_15 : AbundanceTree :=
  .split 140194179307171898833699259 [
    (4, .split 918585913061 [])]

private theorem checked5_15 : replayAbundance bank 5 224633409 (10^300) 4 state5_15 tree5_15 = true := by
  decide +kernel

theorem reject5_15 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_15 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree5_15 checked5_15

@[expose] noncomputable def state5_16 : State := ⟨13552527156068805425093160010874271392822265625, 16940658945086006781366450013592839241027832031, 0⟩

private noncomputable def tree5_16 : AbundanceTree :=
  .split 604088623657497125653141 []

private theorem checked5_16 : replayAbundance bank 5 224633409 (10^300) 3 state5_16 tree5_16 = true := by
  decide +kernel

theorem reject5_16 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_16 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree5_16 checked5_16

@[expose] noncomputable def state5_17 : State := ⟨8470329472543003390683225006796419620513916015625, 10587911840678754238354031258495524525642395019531, 0⟩

private noncomputable def tree5_17 : AbundanceTree :=
  .split 18607929421228039083223253529869111644362732899 []

private theorem checked5_17 : replayAbundance bank 5 224633409 (10^300) 3 state5_17 tree5_17 = true := by
  decide +kernel

theorem reject5_17 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_17 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree5_17 checked5_17

@[expose] noncomputable def state5_18 : State := ⟨211758236813575084767080625169910490512847900390625, 264697796016968855958850781462388113141059875488281, 0⟩

private noncomputable def tree5_18 : AbundanceTree :=
  .split 9519524151770349914726200576714027279 []

private theorem checked5_18 : replayAbundance bank 5 224633409 (10^300) 3 state5_18 tree5_18 = true := by
  decide +kernel

theorem reject5_18 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_18 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree5_18 checked5_18

@[expose] noncomputable def state5_19 : State := ⟨3308722450212110699485634768279851414263248443603515625, 4135903062765138374357043460349814267829060554504394531, 0⟩

private noncomputable def tree5_19 : AbundanceTree :=
  .split 344120456368919234899 []

private theorem checked5_19 : replayAbundance bank 5 224633409 (10^300) 3 state5_19 tree5_19 = true := by
  decide +kernel

theorem reject5_19 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_19 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree5_19 checked5_19

@[expose] noncomputable def state5_20 : State := ⟨2067951531382569187178521730174907133914530277252197265625, 2584939414228211483973152162718633917393162846565246582031, 0⟩

private noncomputable def tree5_20 : AbundanceTree :=
  .split 88040095945103834627376781 [
    (1, .split 44020047972551917313688391 [])]

private theorem checked5_20 : replayAbundance bank 5 224633409 (10^300) 4 state5_20 tree5_20 = true := by
  decide +kernel

theorem reject5_20 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_20 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree5_20 checked5_20

@[expose] noncomputable def state5_21 : State := ⟨32311742677852643549664402033982923967414535582065582275390625, 40389678347315804437080502542478654959268169477581977844238281, 0⟩

private noncomputable def tree5_21 : AbundanceTree :=
  .split 231669654363683130095909 [
    (4, .round 8157179360521 [(14597959, 1), (834019001, 1), (8157179360521, 1)])]

private theorem checked5_21 : replayAbundance bank 5 224633409 (10^300) 4 state5_21 tree5_21 = true := by
  decide +kernel

theorem reject5_21 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_21 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree5_21 checked5_21

@[expose] noncomputable def state5_22 : State := ⟨12621774483536188886587657044524579674771302961744368076324462890625, 15777218104420236108234571305655724593464128702180460095405578613281, 0⟩

private noncomputable def tree5_22 : AbundanceTree :=
  .split 153159805660301568024613754993807288151489686913246436306439 []

private theorem checked5_22 : replayAbundance bank 5 224633409 (10^300) 3 state5_22 tree5_22 = true := by
  decide +kernel

theorem reject5_22 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_22 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree5_22 checked5_22

@[expose] noncomputable def state5_23 : State := ⟨7888609052210118054117285652827862296732064351090230047702789306640625, 9860761315262647567646607066034827870915080438862787559628486633300781, 0⟩

private noncomputable def tree5_23 : AbundanceTree :=
  .split 483593153887747265029536907421 [
    (2, .round 3434487311396589821473854121 [(37, 1), (2333282713, 1), (5937018283241, 1), (6646873767712671024673, 1), (407543311034792056887515251, 1), (3434487311396589821473854121, 1)])]

private theorem checked5_23 : replayAbundance bank 5 224633409 (10^300) 4 state5_23 tree5_23 = true := by
  decide +kernel

theorem reject5_23 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_23 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree5_23 checked5_23

@[expose] noncomputable def state5_24 : State := ⟨197215226305252951352932141320696557418301608777255751192569732666015625, 246519032881566189191165176650870696772877010971569688990712165832519531, 0⟩

private noncomputable def tree5_24 : AbundanceTree :=
  .split 39546955636451768643571562540114219 []

private theorem checked5_24 : replayAbundance bank 5 224633409 (10^300) 3 state5_24 tree5_24 = true := by
  decide +kernel

theorem reject5_24 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_24 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree5_24 checked5_24

@[expose] noncomputable def state5_25 : State := ⟨123259516440783094595582588325435348386438505485784844495356082916259765625, 154074395550978868244478235406794185483048131857231055619195103645324707031, 0⟩

private noncomputable def tree5_25 : AbundanceTree :=
  .split 717433171088016374418821 []

private theorem checked5_25 : replayAbundance bank 5 224633409 (10^300) 3 state5_25 tree5_25 = true := by
  decide +kernel

theorem reject5_25 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_25 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree5_25 checked5_25

@[expose] noncomputable def state5_26 : State := ⟨3081487911019577364889564708135883709660962637144621112383902072906494140625, 3851859888774471706111955885169854637076203296430776390479877591133117675781, 0⟩

private noncomputable def tree5_26 : AbundanceTree :=
  .split 2293559892404294400692399012979688850301546383400890423075969 []

private theorem checked5_26 : replayAbundance bank 5 224633409 (10^300) 3 state5_26 tree5_26 = true := by
  decide +kernel

theorem reject5_26 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_26 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree5_26 checked5_26

@[expose] noncomputable def state5_27 : State := ⟨1925929944387235853055977942584927318538101648215388195239938795566558837890625, 2407412430484044816319972428231159148172627060269235244049923494458198547363281, 0⟩

private noncomputable def tree5_27 : AbundanceTree :=
  .split 8237123176890810696379 []

private theorem checked5_27 : replayAbundance bank 5 224633409 (10^300) 3 state5_27 tree5_27 = true := by
  decide +kernel

theorem reject5_27 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_27 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree5_27 checked5_27

@[expose] noncomputable def state5_28 : State := ⟨11754943508222875079687365372222456778186655567720875215087517062784172594547271728515625, 14693679385278593849609206715278070972733319459651094018859396328480215743184089660644531, 0⟩

private noncomputable def tree5_28 : AbundanceTree :=
  .split 14693679385278593849609206715278070972733319459651094018859396328480215743184089660644531 []

private theorem checked5_28 : replayAbundance bank 5 224633409 (10^300) 3 state5_28 tree5_28 = true := by
  decide +kernel

theorem reject5_28 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_28 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree5_28 checked5_28

@[expose] noncomputable def state5_29 : State := ⟨7346839692639296924804603357639035486366659729825547009429698164240107871592044830322265625, 9183549615799121156005754197048794357958324662281933761787122705300134839490056037902832031, 0⟩

private noncomputable def tree5_29 : AbundanceTree :=
  .split 250805666433416532678429525124977090318975999001796354124089 []

private theorem checked5_29 : replayAbundance bank 5 224633409 (10^300) 3 state5_29 tree5_29 = true := by
  decide +kernel

theorem reject5_29 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_29 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree5_29 checked5_29

@[expose] noncomputable def state5_30 : State := ⟨114794370197489014450071927463109929474479058278524172022339033816251685493625700473785400390625, 143492962746861268062589909328887411843098822848155215027923792270314606867032125592231750488281, 0⟩

private noncomputable def tree5_30 : AbundanceTree :=
  .split 251755028858658462627642052961230751431 []

private theorem checked5_30 : replayAbundance bank 5 224633409 (10^300) 3 state5_30 tree5_30 = true := by
  decide +kernel

theorem reject5_30 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_30 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree5_30 checked5_30

@[expose] noncomputable def state5_31 : State := ⟨2869859254937225361251798186577748236861976456963104300558475845406292137340642511844635009765625, 3587324068671531701564747733222185296077470571203880375698094806757865171675803139805793762207031, 0⟩

private noncomputable def tree5_31 : AbundanceTree :=
  .split 24550591546653776667941845268908441565415743319193209001 []

private theorem checked5_31 : replayAbundance bank 5 224633409 (10^300) 3 state5_31 tree5_31 = true := by
  decide +kernel

theorem reject5_31 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_31 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree5_31 checked5_31

@[expose] noncomputable def state5_32 : State := ⟨28025969286496341418474591665798322625605238837530315435141365677795821653717212029732763767242431640625, 35032461608120426773093239582247903282006548546912894293926707097244777067146515037165954709053039550781, 0⟩

private noncomputable def tree5_32 : AbundanceTree :=
  .split 35032461608120426773093239582247903282006548546912894293926707097244777067146515037165954709053039550781 []

private theorem checked5_32 : replayAbundance bank 5 224633409 (10^300) 3 state5_32 tree5_32 = true := by
  decide +kernel

theorem reject5_32 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_32 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree5_32 checked5_32

@[expose] noncomputable def state5_33 : State := ⟨700649232162408535461864791644958065640130970938257885878534141944895541342930300743319094181060791015625, 875811540203010669327330989556197582050163713672822357348167677431119426678662875929148867726325988769531, 0⟩

private noncomputable def tree5_33 : AbundanceTree :=
  .split 23480835068319558820315540345862729 []

private theorem checked5_33 : replayAbundance bank 5 224633409 (10^300) 3 state5_33 tree5_33 = true := by
  decide +kernel

theorem reject5_33 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_33 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree5_33 checked5_33

@[expose] noncomputable def state5_34 : State := ⟨10947644252537633366591637369452469775627046420910279466852095967888992833483285949114360846579074859619140625, 13684555315672041708239546711815587219533808026137849333565119959861241041854107436392951058223843574523925781, 0⟩

private noncomputable def tree5_34 : AbundanceTree :=
  .split 4587548699755676969742331799602074877905422766102260881 [
    (1, .round 1 [(8616314452100494153901371725720169, 1)])]

private theorem checked5_34 : replayAbundance bank 5 224633409 (10^300) 4 state5_34 tree5_34 = true := by
  decide +kernel

theorem reject5_34 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_34 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree5_34 checked5_34

@[expose] noncomputable def state5_35 : State := ⟨171056941445900521352994333897694840244172600326723116669563999498265513023176342954911888227798044681549072265625, 213821176807375651691242917372118550305215750408403895836954999372831891278970428693639860284747555851936340332031, 0⟩

private noncomputable def tree5_35 : AbundanceTree :=
  .round 1 [(6582151087844246659, 1), (102556399583828574447011133455059, 1), (2541462766396986870745222882425433052891, 1)]

private theorem checked5_35 : replayAbundance bank 5 224633409 (10^300) 3 state5_35 tree5_35 = true := by
  decide +kernel

theorem reject5_35 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_35 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree5_35 checked5_35

@[expose] noncomputable def state5_36 : State := ⟨106910588403687825845621458686059275152607875204201947918477499686415945639485214346819930142373777925968170166015625, 133638235504609782307026823357574093940759844005252434898096874608019932049356517933524912677967222407460212707519531, 0⟩

private noncomputable def tree5_36 : AbundanceTree :=
  .split 136120444765766549215152778976644223266629687067883561040373326929809178107924810841979832452900690680385721 []

private theorem checked5_36 : replayAbundance bank 5 224633409 (10^300) 3 state5_36 tree5_36 = true := by
  decide +kernel

theorem reject5_36 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_36 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree5_36 checked5_36

@[expose] noncomputable def state5_37 : State := ⟨1670477943807622278837835291969676174259498050065655436226210932600249150616956474169061408474590280093252658843994140625, 2088097429759527848547294114962095217824372562582069295282763665750311438271195592711326760593237850116565823554992675781, 0⟩

private noncomputable def tree5_37 : AbundanceTree :=
  .split 339919831020187630960347957199421099342434386629129924807724899548171905079254114627192212342747249 []

private theorem checked5_37 : replayAbundance bank 5 224633409 (10^300) 3 state5_37 tree5_37 = true := by
  decide +kernel

theorem reject5_37 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_37 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree5_37 checked5_37

@[expose] noncomputable def state5_38 : State := ⟨26101217871994098106841176437026190222804657032275866191034545821878892978389944908891584507415473126457072794437408447265625, 32626522339992622633551470546282737778505821290344832738793182277348616222987431136114480634269341408071340993046760559082031, 0⟩

private noncomputable def tree5_38 : AbundanceTree :=
  .round 1 [(192314444462213728810818160511138304152610629589418566747969452950500442408719960811, 1)]

private theorem checked5_38 : replayAbundance bank 5 224633409 (10^300) 3 state5_38 tree5_38 = true := by
  decide +kernel

theorem reject5_38 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_38 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree5_38 checked5_38

@[expose] noncomputable def state5_39 : State := ⟨652530446799852452671029410925654755570116425806896654775863645546972324459748622722289612685386828161426819860935211181640625, 815663058499815565838786763657068444462645532258620818469829556933715405574685778402862015856733535201783524826169013977050781, 0⟩

private noncomputable def tree5_39 : AbundanceTree :=
  .split 815663058499815565838786763657068444462645532258620818469829556933715405574685778402862015856733535201783524826169013977050781 []

private theorem checked5_39 : replayAbundance bank 5 224633409 (10^300) 3 state5_39 tree5_39 = true := by
  decide +kernel

theorem reject5_39 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_39 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree5_39 checked5_39

@[expose] noncomputable def state5_40 : State := ⟨6372367644529809108115521591070847222364418220770475144295543413544651606052232643772359498880730743763933787704445421695709228515625, 7965459555662261385144401988838559027955522775963093930369429266930814507565290804715449373600913429704917234630556777119636535644531, 0⟩

private noncomputable def tree5_40 : AbundanceTree :=
  .round 1 [(1169749680244912326138211518173648104342708417321462088878770777077018070874770315901989031997671838650855091818008950671, 1)]

private theorem checked5_40 : replayAbundance bank 5 224633409 (10^300) 3 state5_40 tree5_40 = true := by
  decide +kernel

theorem reject5_40 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_40 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree5_40 checked5_40

@[expose] noncomputable def state5_41 : State := ⟨159309191113245227702888039776771180559110455519261878607388585338616290151305816094308987472018268594098344692611135542392730712890625, 199136488891556534628610049720963975698888069399077348259235731673270362689132270117886234340022835742622930865763919427990913391113281, 0⟩

private noncomputable def tree5_41 : AbundanceTree :=
  .round 653307895929756357032069541177270095642284909406860982228674482418078001190973372748580182250689 [(749154725101, 1), (406875383561091922623241829, 1), (653307895929756357032069541177270095642284909406860982228674482418078001190973372748580182250689, 1)]

private theorem checked5_41 : replayAbundance bank 5 224633409 (10^300) 3 state5_41 tree5_41 = true := by
  decide +kernel

theorem reject5_41 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_41 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree5_41 checked5_41

@[expose] noncomputable def state5_42 : State := ⟨99568244445778267314305024860481987849444034699538674129617865836635181344566135058943117170011417871311465432881959713995456695556640625, 124460305557222834142881281075602484811805043374423342662022332295793976680707668823678896462514272339139331791102449642494320869445800781, 0⟩

private noncomputable def tree5_42 : AbundanceTree :=
  .round 1 [(470323176131, 1), (362204827770839, 1)]

private theorem checked5_42 : replayAbundance bank 5 224633409 (10^300) 3 state5_42 tree5_42 = true := by
  decide +kernel

theorem reject5_42 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_42 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree5_42 checked5_42

@[expose] noncomputable def state5_43 : State := ⟨2489206111144456682857625621512049696236100867488466853240446645915879533614153376473577929250285446782786635822048992849886417388916015625, 3111507638930570853572032026890062120295126084360583566550558307394849417017691720591972411562856808478483294777561241062358021736145019531, 0⟩

private noncomputable def tree5_43 : AbundanceTree :=
  .split 57908984365274624584914333008692600552662821915850878758083011806868463587457738002121166767096402607032872918381590535488973250751801 []

private theorem checked5_43 : replayAbundance bank 5 224633409 (10^300) 3 state5_43 tree5_43 = true := by
  decide +kernel

theorem reject5_43 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_43 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree5_43 checked5_43

@[expose] noncomputable def state5_44 : State := ⟨607716335728627119838287505251965257870141813351676477841905919413056526761267914178119611633370470405953768511242429894991801120340824127197265625, 759645419660783899797859381564956572337677266689595597302382399266320658451584892722649514541713088007442210639053037368739751400426030158996582031, 0⟩

private noncomputable def tree5_44 : AbundanceTree :=
  .round 1 [(5594292675731, 1)]

private theorem checked5_44 : replayAbundance bank 5 224633409 (10^300) 3 state5_44 tree5_44 = true := by
  decide +kernel

theorem reject5_44 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_44 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree5_44 checked5_44

@[expose] noncomputable def state5_45 : State := ⟨1, 1, 0⟩

private theorem checked5_45 : checkChildren bank 5 224633409 (10^300) state5_45 5 [state5_1, state5_2, state5_3, state5_4, state5_5, state5_6, state5_7, state5_8, state5_9, state5_10, state5_11, state5_12, state5_13, state5_14, state5_15, state5_16, state5_17, state5_18, state5_19, state5_20, state5_21, state5_22, state5_23, state5_24, state5_25, state5_26, state5_27, state5_28, state5_29, state5_30, state5_31, state5_32, state5_33, state5_34, state5_35, state5_36, state5_37, state5_38, state5_39, state5_40, state5_41, state5_42, state5_43, state5_44] = true := by
  decide +kernel

theorem reject5_45 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) (h : Valid state5_45 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state5_1, state5_2, state5_3, state5_4, state5_5, state5_6, state5_7, state5_8, state5_9, state5_10, state5_11, state5_12, state5_13, state5_14, state5_15, state5_16, state5_17, state5_18, state5_19, state5_20, state5_21, state5_22, state5_23, state5_24, state5_25, state5_26, state5_27, state5_28, state5_29, state5_30, state5_31, state5_32, state5_33, state5_34, state5_35, state5_36, state5_37, state5_38, state5_39, state5_40, state5_41, state5_42, state5_43, state5_44] ?_ checked5_45
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject5_1 ho hN hs hav hx hvalid
  · exact reject5_2 ho hN hs hav hx hvalid
  · exact reject5_3 ho hN hs hav hx hvalid
  · exact reject5_4 ho hN hs hav hx hvalid
  · exact reject5_5 ho hN hs hav hx hvalid
  · exact reject5_6 ho hN hs hav hx hvalid
  · exact reject5_7 ho hN hs hav hx hvalid
  · exact reject5_8 ho hN hs hav hx hvalid
  · exact reject5_9 ho hN hs hav hx hvalid
  · exact reject5_10 ho hN hs hav hx hvalid
  · exact reject5_11 ho hN hs hav hx hvalid
  · exact reject5_12 ho hN hs hav hx hvalid
  · exact reject5_13 ho hN hs hav hx hvalid
  · exact reject5_14 ho hN hs hav hx hvalid
  · exact reject5_15 ho hN hs hav hx hvalid
  · exact reject5_16 ho hN hs hav hx hvalid
  · exact reject5_17 ho hN hs hav hx hvalid
  · exact reject5_18 ho hN hs hav hx hvalid
  · exact reject5_19 ho hN hs hav hx hvalid
  · exact reject5_20 ho hN hs hav hx hvalid
  · exact reject5_21 ho hN hs hav hx hvalid
  · exact reject5_22 ho hN hs hav hx hvalid
  · exact reject5_23 ho hN hs hav hx hvalid
  · exact reject5_24 ho hN hs hav hx hvalid
  · exact reject5_25 ho hN hs hav hx hvalid
  · exact reject5_26 ho hN hs hav hx hvalid
  · exact reject5_27 ho hN hs hav hx hvalid
  · exact reject5_28 ho hN hs hav hx hvalid
  · exact reject5_29 ho hN hs hav hx hvalid
  · exact reject5_30 ho hN hs hav hx hvalid
  · exact reject5_31 ho hN hs hav hx hvalid
  · exact reject5_32 ho hN hs hav hx hvalid
  · exact reject5_33 ho hN hs hav hx hvalid
  · exact reject5_34 ho hN hs hav hx hvalid
  · exact reject5_35 ho hN hs hav hx hvalid
  · exact reject5_36 ho hN hs hav hx hvalid
  · exact reject5_37 ho hN hs hav hx hvalid
  · exact reject5_38 ho hN hs hav hx hvalid
  · exact reject5_39 ho hN hs hav hx hvalid
  · exact reject5_40 ho hN hs hav hx hvalid
  · exact reject5_41 ho hN hs hav hx hvalid
  · exact reject5_42 ho hN hs hav hx hvalid
  · exact reject5_43 ho hN hs hav hx hvalid
  · exact reject5_44 ho hN hs hav hx hvalid

theorem exclude_5 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 5 ∣ N)
    (hav : Nat.Coprime 224633409 N) (hx : N ≤ 10^300) : False :=
  reject5_45 ho hN hs hav hx (root_valid N)

end OddPerfect.IndexComponent.Size300
