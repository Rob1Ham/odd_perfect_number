module

public import OddPerfect.SizeIndex300.Seed31

public section

namespace OddPerfect.IndexComponent.Size300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def state13_1 : State := ⟨5916840241, 6581591523, 0⟩

private noncomputable def tree13_1 : AbundanceTree :=
  .split 3169 [
    (1, .abundant [(3, 4), (5, 2), (13, 2)]),
    (2, .split 3348577 [
      (1, .split 1674289 [
        (2, .split 934415109937 [
          (4, .split 44322667326129398950847171430005295122621 [])]),
        (4, .split 7858179685661558917710821 [
          (2, .split 82818872912127113607949 [
            (2, .split 10026390870440555999563332259 [])])]),
        (12, .split 22585646008360298988057561180592547 []),
        (16, .round 1 [(3956451899480991413, 1), (227852513819803851204263653623117987276133170184156001598484507703001831869, 1)]),
        (18, .split 4031434050653 []),
        (22, .round 1 [(3083, 1)])]),
      (2, .split 3737657091169 [
        (1, .abundant [(3, 6), (5, 2), (13, 2)]),
        (2, .split 987900542491 []),
        (4, .split 195163150047313020008802835877656364030813707064261 [
          (1, .split 487028384784201229 []),
          (2, .round 1 [(79924458878744271170965015597634065318826198630367553697609183317747, 1)])])]),
      (4, .split 1453121857811448551 [
        (2, .split 16694867096928847 [
          (2, .split 9868152717977503 [
            (2, .split 1036950426156829 [
              (1, .abundant [(3, 6), (5, 2), (13, 2)])])]),
          (4, .round 3478781116501 [(4051, 1), (8111, 1), (182701, 1), (5076551, 1), (86524531, 1), (1092087791, 1), (3478781116501, 1), (357469226115736660590839311, 1)])]),
        (6, .round 240711967217525643596748113663485582667815117067436722301154726681228109040584676913 [(47183809, 1), (86524531, 1), (28584035037615149, 1), (240711967217525643596748113663485582667815117067436722301154726681228109040584676913, 1)])]),
      (12, .split 33201824164356132292811808428606053 [
        (1, .split 357803268795732159787447 [])]),
      (16, .round 1 [(3288879759133313860651, 1), (170538912879859159955597960914444809962698959129912919637023, 1)]),
      (18, .split 173445569142927798078586246740083460690702262828047923934305020980200733358121968681944228901 [])]),
    (4, .split 1653850268201 [
      (2, .split 22216443433 [
        (1, .split 1577431459 [
          (4, .split 78049 [
            (2, .split 20933761 [
              (4, .abundant [(3, 4), (5, 2), (13, 2)]),
              (6, .split 71999 [
                (6, .round 1 [(7160899293871, 1)])])]),
            (6, .split 71999 [
              (6, .split 7160899293871 [
                (2, .round 1 [(883304544071268449821, 1)])]),
              (10, .round 1 [(372041144312772337140436187016023, 1)])]),
            (10, .round 1 [(41, 1), (53, 1), (71, 1), (2113, 1), (2861, 1), (71999, 1), (1387591529606790846687628155738329013116407, 1)]),
            (12, .split 71999 [])]),
          (6, .split 78049 [
            (2, .split 20933761 [
              (4, .abundant [(3, 4), (5, 2), (13, 2)]),
              (6, .split 71999 [])]),
            (6, .split 71999 [
              (6, .round 1 [(7160899293871, 1)])]),
            (10, .round 1 [(1387591529606790846687628155738329013116407, 1)]),
            (12, .round 1 [(71999, 1)])]),
          (10, .split 78049 [
            (2, .split 20933761 [])]),
          (12, .round 1 [(78049, 1)])]),
        (4, .split 203041357551189509282939887095491 [
          (2, .round 1 [(1577431459, 1), (383648610470176460447108648593863136411719282871, 1)])]),
        (6, .split 161829762772126598475261977967276884867047561861641665090201 []),
        (10, .split 1577431459 [])]),
      (4, .split 231095599827244820769014303866257168079151 []),
      (6, .split 736858006219516642679807 [
        (2, .round 209117839979303977 [(1986459091, 1), (12533290309, 1), (2928547481506417, 1), (209117839979303977, 1), (60382080575877306305795178187, 1)])]),
      (10, .split 107787831922278736427 [])]),
    (6, .split 3447899565839 [
      (2, .split 5031807024001464757 [
        (1, .split 10810256869463 [
          (6, .round 1 [(211, 1), (491, 1), (1103, 1), (8429, 1), (2362573, 1), (712782407, 1), (4106087021, 1), (1344698476591, 1)])]),
        (2, .split 488554350635617461823 [
          (2, .split 72049819577336069191 []),
          (4, .round 6149624869 [(2362573, 1), (2809087, 1), (6149624869, 1)])]),
        (4, .split 31784737314210171707627237048461 [])]),
      (10, .round 87345721 [(8429, 1), (13693571, 1), (87345721, 1)])]),
    (12, .split 27495050288861117 [
      (1, .split 51206126365213 [
        (2, .split 25317725864513 [
          (2, .split 2575414718127728049109 [
            (2, .round 1 [(13751549137, 1), (2210920323449641639724126880590439614580997, 1)])]),
          (6, .round 1 [(9081344704322615789277838261768252776769371879193688469868494611205400648812467, 1)])]),
        (4, .split 6875237331259208010170719604369680500308152268076585341 [])]),
      (4, .split 2611803034283209601 []),
      (6, .round 51206126365213 [(12251, 1), (13751549137, 1), (28552914124561, 1), (51206126365213, 1)])]),
    (16, .split 184065236096494092094574928338134239077340652559 [
      (2, .split 985996607929 [
        (1, .abundant [(3, 4), (5, 2), (13, 2)])])]),
    (18, .split 546104277626159357953084111141441465332047 [
      (2, .split 427951609310474819 [])]),
    (22, .split 350629641953301517546168193 []),
    (28, .split 383179201994636300160466770424505293943259810893365588712563747 []),
    (30, .split 1018931726790243197488050343793 []),
    (36, .round 36799120636249118806979649347305792642377421012261 [(924347763164985110217631744828987973503604101, 1), (36799120636249118806979649347305792642377421012261, 1)]),
    (40, .round 1 [(2865992221934153623365676749832089310906879977602687375509000649303, 1)])]

private theorem checked13_1 : replayAbundance bank 13 5759831 (10^300) 10 state13_1 tree13_1 = true := by
  decide +kernel

theorem reject13_1 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_1 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 10 h tree13_1 checked13_1

@[expose] noncomputable def state13_2 : State := ⟨523813612327596721, 582664203781954983, 0⟩

private noncomputable def tree13_2 : AbundanceTree :=
  .split 20241187 [
    (2, .split 1890771811 [
      (2, .split 567661 [
        (1, .split 283831 [
          (6, .split 184993393445546792221665593 []),
          (10, .split 152407 [
            (2, .split 7742682019 [
              (4, .round 1 [(1276321491857688434021838745571, 1)])]),
            (4, .split 49236515971 [
              (2, .round 1 [(967, 1), (2017, 1), (6829, 1), (8329, 1), (72229, 1), (267270691, 1), (2256275128193893, 1)])]),
            (6, .split 3565344072087523181 []),
            (10, .round 1 [(5986246439669, 1)])]),
          (12, .split 152407 [
            (2, .split 7742682019 [
              (4, .round 1 [(1276321491857688434021838745571, 1)])]),
            (4, .split 49236515971 [
              (2, .round 1 [(267270691, 1), (2256275128193893, 1)])]),
            (6, .round 1 [(72229, 1), (3515044995197, 1), (3565344072087523181, 1)])]),
          (16, .split 152407 [
            (2, .round 1 [(103, 1), (647, 1), (967, 1), (2017, 1), (6829, 1), (72229, 1), (7742682019, 1)]),
            (4, .round 1 [(49236515971, 1)])]),
          (18, .round 1 [(748247121288929365959985028508922739525728453611963160381752724749855114993473473631012250059639, 1)])]),
        (2, .split 152407 [
          (2, .split 7742682019 [
            (4, .split 1276321491857688434021838745571 [
              (2, .round 10338645830280210505291045928631768697 [(68678651, 1), (32308354513, 1), (131807445409, 1), (10338645830280210505291045928631768697, 1)])]),
            (6, .round 1113617 [(43, 1), (67, 1), (71, 1), (967, 1), (2017, 1), (6829, 1), (9967, 1), (12373, 1), (72229, 1), (1113617, 1), (2724923672940169033618938566817620036616759093492163, 1)]),
            (10, .round 24646174878469594587079476374463830585060659299310589761851497891088902719703759116991490224453 [(72229, 1), (24646174878469594587079476374463830585060659299310589761851497891088902719703759116991490224453, 1)])]),
          (4, .split 49236515971 [
            (2, .split 2256275128193893 [
              (1, .split 5126569771 [
                (2, .split 278658727003 [
                  (2, .round 1 [(9967, 1), (12373, 1), (72229, 1), (220057, 1), (31438357, 1), (267270691, 1), (1472381413, 1), (17579386575067, 1)]),
                  (4, .round 1 [(31438357, 1), (267270691, 1)])])])]),
            (6, .round 1 [(14567641413739, 1), (5081182890168706668061757604902797557199636391, 1)])]),
          (6, .split 3565344072087523181 [
            (2, .split 3333121151155141 [
              (1, .round 1 [(29, 1), (43, 1), (59, 1), (67, 1), (853, 1), (967, 1), (2017, 1), (3209, 1), (3559, 1), (6829, 1), (9967, 1), (12373, 1), (72229, 1), (927973, 1), (303529829, 1), (1353753013, 1), (3515044995197, 1)])])]),
          (10, .split 5986246439669 [
            (2, .round 10561409 [(6829, 1), (9967, 1), (12373, 1), (34607, 1), (72229, 1), (10561409, 1), (757905469663, 1), (1991951243371, 1), (490892416937750201414647, 1)]),
            (4, .round 1 [(757905469663, 1), (1991951243371, 1)])]),
          (12, .split 1094806272682068880388122066127 []),
          (16, .round 1 [(497102328408781619399, 1), (14490209233961187767063, 1)]),
          (18, .round 1484584028339793856008105113792703546864239156391400019767302456075713 [(72229, 1), (2508541843, 1), (2767144311853, 1), (1484584028339793856008105113792703546864239156391400019767302456075713, 1)])]),
        (4, .abundant [(3, 4), (5, 1), (13, 2), (41, 1), (43, 2)]),
        (6, .split 10773631832991133 [
          (1, .split 48774625069 [
            (6, .round 1 [(72229, 1), (152407, 1), (356693, 1), (44198972119, 1)])]),
          (4, .split 44198972119 [])]),
        (10, .split 152407 [
          (2, .split 7742682019 [
            (4, .round 1 [(1276321491857688434021838745571, 1)])]),
          (4, .split 49236515971 [
            (2, .split 2256275128193893 [
              (1, .round 1 [(72229, 1), (220057, 1), (267270691, 1), (5126569771, 1)])])]),
          (6, .split 3565344072087523181 []),
          (10, .round 1 [(1991951243371, 1)])]),
        (12, .split 14172366309174962723703137142485835775763949973243219070451445522267 []),
        (16, .split 152407 [
          (2, .round 72229 [(43, 1), (239, 1), (967, 1), (1361, 1), (2017, 1), (6829, 1), (72229, 1), (7742682019, 1)]),
          (4, .round 1 [(49236515971, 1)])]),
        (18, .split 152407 [
          (2, .round 1 [(7742682019, 1)])])]),
      (10, .round 1 [(19823173807011977458638629445607312130902615244849600898559294504168175330118124663243279, 1)]),
      (12, .split 8284176020070048102993789409669511672115610936155717253730881859266645789710400908174069890242334161 [])]),
    (10, .split 261228918910252692663296926361697980081554367 []),
    (12, .split 502481311241792961238607042480751391292386751875040294179 []),
    (16, .split 11896771 []),
    (18, .round 1 [(967, 1), (79100676007, 1)])]

private theorem checked13_2 : replayAbundance bank 13 5759831 (10^300) 11 state13_2 tree13_2 = true := by
  decide +kernel

theorem reject13_2 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_2 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 11 h tree13_2 checked13_2

@[expose] noncomputable def state13_3 : State := ⟨46372842477374874168087601, 51582843025254593834427243, 0⟩

private noncomputable def tree13_3 : AbundanceTree :=
  .split 837197335075000483 [
    (2, .split 233633125952227544941816005841744591 []),
    (4, .split 11031864047065746990161103141020284309974641961233117155302961154851 []),
    (6, .split 338984002897 [
      (1, .split 28537 [
        (2, .split 52783 [
          (2, .round 1 [(139, 1), (337, 1), (613, 1), (2063, 1), (2879, 1), (116539, 1)])])])])]

private theorem checked13_3 : replayAbundance bank 13 5759831 (10^300) 7 state13_3 tree13_3 = true := by
  decide +kernel

theorem reject13_3 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_3 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree13_3 checked13_3

@[expose] noncomputable def state13_4 : State := ⟨436322074869620191047536237809, 485342970024620473388193773709, 0⟩

private noncomputable def tree13_4 : AbundanceTree :=
  .split 8224356155341457 [
    (2, .split 50156791927903603 [
      (2, .split 253067024871751 [
        (2, .split 177774281582573821 [
          (2, .round 796057760833 [(112501, 1), (1079059, 1), (217555099, 1), (120082834831, 1), (796057760833, 1), (1308716624033283261323467, 1)])]),
        (4, .abundant [(3, 4), (5, 1), (13, 2), (37, 1), (43, 2)])]),
      (4, .split 12288381826278378235712063697684697601746915312568569241 []),
      (6, .round 10193 [(79, 3), (4657, 1), (10193, 1), (20359, 1), (1079059, 1)])]),
    (4, .split 869092273260863143524512939389109473193796045318392161 [
      (1, .split 46267174932838402716097 [
        (2, .round 1 [(45962958203714034570937, 1)])])]),
    (6, .split 17960270347143687413147814805014164622970434639677 [
      (1, .round 1 [(227099725441118785176010433, 1)])])]

private theorem checked13_4 : replayAbundance bank 13 5759831 (10^300) 7 state13_4 tree13_4 = true := by
  decide +kernel

theorem reject13_4 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_4 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree13_4 checked13_4

@[expose] noncomputable def state13_5 : State := ⟨38627279572635644256521019954675785329, 42967064174684202806936429313549543249, 0⟩

private noncomputable def tree13_5 : AbundanceTree :=
  .split 62065212901958868055012327674641 [
    (4, .split 101 [
      (1, .abundant [(3, 4), (5, 2), (13, 2)]),
      (2, .round 1 [(10303, 1)])])]

private theorem checked13_5 : replayAbundance bank 13 5759831 (10^300) 5 state13_5 tree13_5 = true := by
  decide +kernel

theorem reject13_5 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_5 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree13_5 checked13_5

@[expose] noncomputable def state13_6 : State := ⟨363444073498928776809606276753544464160561, 404277106819603664210464863411187720274163, 0⟩

private noncomputable def tree13_6 : AbundanceTree :=
  .split 97199158345481611029493 [
    (1, .split 586297360433 [
      (2, .split 13189649827 [
        (6, .round 1 [(66372257226728205287921, 1), (1844779867041222368032321820250310559, 1)])])]),
    (2, .split 435031625275171328059039580569 [])]

private theorem checked13_6 : replayAbundance bank 13 5759831 (10^300) 6 state13_6 tree13_6 = true := by
  decide +kernel

theorem reject13_6 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_6 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree13_6 checked13_6

@[expose] noncomputable def state13_7 : State := ⟨32175442510571318881163917574078305613664733886641, 35790361591499709097517887033555656232539188336823, 0⟩

private noncomputable def tree13_7 : AbundanceTree :=
  .split 685880385513120464179 [
    (4, .split 2781923674510938331025973708049795847846040376707422041 [])]

private theorem checked13_7 : replayAbundance bank 13 5759831 (10^300) 4 state13_7 tree13_7 = true := by
  decide +kernel

theorem reject13_7 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_7 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree13_7 checked13_7

@[expose] noncomputable def state13_8 : State := ⟨26801242857508368765686901514772104106257509084776600379253489, 29812369252005387970879735539780587271726462363492634729863069, 0⟩

private noncomputable def tree13_8 : AbundanceTree :=
  .split 1674947788493753179095247410947 []

private theorem checked13_8 : replayAbundance bank 13 5759831 (10^300) 3 state13_8 tree13_8 = true := by
  decide +kernel

theorem reject13_8 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_8 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_8 checked13_8

@[expose] noncomputable def state13_9 : State := ⟨252172894046296241716348056352490727535776902978663032968396078001, 280504582292118695418007431693795545639674284378102200173349460543, 0⟩

private noncomputable def tree13_9 : AbundanceTree :=
  .split 86560814174154135219046318815578701530065478419 []

private theorem checked13_9 : replayAbundance bank 13 5759831 (10^300) 3 state13_9 tree13_9 = true := by
  decide +kernel

theorem reject13_9 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_9 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_9 checked13_9

@[expose] noncomputable def state13_10 : State := ⟨210052961142491667809144048615926476058357954451787258679580907385873240466929, 233652464303637780077581536108202894061289012464951093582460997508710748678949, 0⟩

private noncomputable def tree13_10 : AbundanceTree :=
  .split 337507116686293990049793563249167463387817822419468016366663340756115941 []

private theorem checked13_10 : replayAbundance bank 13 5759831 (10^300) 3 state13_10 tree13_10 = true := by
  decide +kernel

theorem reject13_10 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_10 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_10 checked13_10

@[expose] noncomputable def state13_11 : State := ⟨18595837621865725899634367849397016074310143748247475175864307112198947535677328648049, 20685084668679218354704417610534740413365086206722158015018986319988953818157469875689, 0⟩

private noncomputable def tree13_11 : AbundanceTree :=
  .split 7256407013778292029505951038072042332543 []

private theorem checked13_11 : replayAbundance bank 13 5759831 (10^300) 3 state13_11 tree13_11 = true := by
  decide +kernel

theorem reject13_11 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_11 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_11 checked13_11

@[expose] noncomputable def state13_12 : State := ⟨174968236184134614989659767094976524243184142527260493929707265618679897363187985249493041, 194625961647602765499413865297521372549352096119048784763313642284776066475043634128202123, 0⟩

private noncomputable def tree13_12 : AbundanceTree :=
  .split 943803569044693240741742722138484804807832469632719164836978873986379071 []

private theorem checked13_12 : replayAbundance bank 13 5759831 (10^300) 3 state13_12 tree13_12 = true := by
  decide +kernel

theorem reject13_12 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_12 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_12 checked13_12

@[expose] noncomputable def state13_13 : State := ⟨15489812147219621072246401615545730403128161288539894427301848765697751482716828201976224534233521, 17230096448595848203274715416220418193927278085262279319019911928962422411043817372997434186933583, 0⟩

private noncomputable def tree13_13 : AbundanceTree :=
  .split 25192889033071001087753314994572377853269833154221501771 []

private theorem checked13_13 : replayAbundance bank 13 5759831 (10^300) 3 state13_13 tree13_13 = true := by
  decide +kernel

theorem reject13_13 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_13 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_13 checked13_13

@[expose] noncomputable def state13_14 : State := ⟨12902579880243106277436741911606871708379375921856359932111615202231600014185818879367785910270375183649025009, 14352187983906926264707082043621026470382433959104645011180428842740832818427770708855394581068800453533293109, 0⟩

private noncomputable def tree13_14 : AbundanceTree :=
  .split 5929582946741988252213566334740639595824689106555394557410995097068922733 [
    (1, .round 1 [(2608744640283223309289, 1)])]

private theorem checked13_14 : replayAbundance bank 13 5759831 (10^300) 4 state13_14 tree13_14 = true := by
  decide +kernel

theorem reject13_14 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_14 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree13_14 checked13_14

@[expose] noncomputable def state13_15 : State := ⟨10747487831602676951847308625080700022982456170982479764200874443611411658815946393506644621653551709197174940002792269361, 11954970800072854757242827102780301054095436252298331348679779434103850760300981984927177558930280741468657669903011396763, 0⟩

private noncomputable def tree13_15 : AbundanceTree :=
  .round 53489014811148111678694572505473146058642537147509 [(103745502061, 1), (53489014811148111678694572505473146058642537147509, 1), (3111911324351773762927252874434121580672856110951541483, 1)]

private theorem checked13_15 : replayAbundance bank 13 5759831 (10^300) 3 state13_15 tree13_15 = true := by
  decide +kernel

theorem reject13_15 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_15 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_15 checked13_15

@[expose] noncomputable def state13_16 : State := ⟨101123113007549587439931326853384306516241930112774152101366027639939772297799239616504019245138268031836219010486272462417649, 112484320257885490410897760210059852617983959697874999659728044695483131803671939496179813651975011496478600016117434299987389, 0⟩

private noncomputable def tree13_16 : AbundanceTree :=
  .split 2044059063516845982148029045618748106949759432857012674679539078697 []

private theorem checked13_16 : replayAbundance bank 13 5759831 (10^300) 3 state13_16 tree13_16 = true := by
  decide +kernel

theorem reject13_16 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_16 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_16 checked13_16

@[expose] noncomputable def state13_17 : State := ⟨84232722186560418963226393683138742627778319828454184550042858482929062247705565877691037988409624258301202150523494848251790890084591921, 93696289768286607269663911353009035630292348431501271567388862168885507568804579446310881513983230766829604078768390963177935902207502883, 0⟩

private noncomputable def tree13_17 : AbundanceTree :=
  .round 1 [(12861260416295775019945284556155730389536534070031, 1)]

private theorem checked13_17 : replayAbundance bank 13 5759831 (10^300) 3 state13_17 tree13_17 = true := by
  decide +kernel

theorem reject13_17 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_17 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_17 checked13_17

@[expose] noncomputable def state13_18 : State := ⟨7457062331848941753873198072991214708081265281801092299656602780678460654793617646850121533257590369067563707821498772522935154461538951944538801, 8294865165554069943512719183729627110853163426442285322446679015219534556386327447889280442909126865844503498608033017497040140486517181452487143, 0⟩

private noncomputable def tree13_18 : AbundanceTree :=
  .round 1 [(3152889469990230034438133899, 1)]

private theorem checked13_18 : replayAbundance bank 13 5759831 (10^300) 3 state13_18 tree13_18 = true := by
  decide +kernel

theorem reject13_18 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_18 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_18 checked13_18

@[expose] noncomputable def state13_19 : State := ⟨70163499480366692962192920668774339188336625036466477447468975563403636300953148439212793506420667782556706926892481950668296868328619998846165578609, 78046386342698244098511174799712061486017414679395462598900802854200600641038954957190239687331974680730933418402982661629650681837640160286519372809, 0⟩

private noncomputable def tree13_19 : AbundanceTree :=
  .round 1 [(406200032183433943894585200505966442183, 1)]

private theorem checked13_19 : replayAbundance bank 13 5759831 (10^300) 3 state13_19 tree13_19 = true := by
  decide +kernel

theorem reject13_19 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_19 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_19 checked13_19

@[expose] noncomputable def state13_20 : State := ⟨628849, 692289, 0⟩

private theorem checked13_20 : checkChildren bank 13 5759831 (10^300) state13_20 97 [state13_1, state13_2, state13_3, state13_4, state13_5, state13_6, state13_7, state13_8, state13_9, state13_10, state13_11, state13_12, state13_13, state13_14, state13_15, state13_16, state13_17, state13_18, state13_19] = true := by
  decide +kernel

theorem reject13_20 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_20 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state13_1, state13_2, state13_3, state13_4, state13_5, state13_6, state13_7, state13_8, state13_9, state13_10, state13_11, state13_12, state13_13, state13_14, state13_15, state13_16, state13_17, state13_18, state13_19] ?_ checked13_20
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject13_1 ho hN hs hav hx hvalid
  · exact reject13_2 ho hN hs hav hx hvalid
  · exact reject13_3 ho hN hs hav hx hvalid
  · exact reject13_4 ho hN hs hav hx hvalid
  · exact reject13_5 ho hN hs hav hx hvalid
  · exact reject13_6 ho hN hs hav hx hvalid
  · exact reject13_7 ho hN hs hav hx hvalid
  · exact reject13_8 ho hN hs hav hx hvalid
  · exact reject13_9 ho hN hs hav hx hvalid
  · exact reject13_10 ho hN hs hav hx hvalid
  · exact reject13_11 ho hN hs hav hx hvalid
  · exact reject13_12 ho hN hs hav hx hvalid
  · exact reject13_13 ho hN hs hav hx hvalid
  · exact reject13_14 ho hN hs hav hx hvalid
  · exact reject13_15 ho hN hs hav hx hvalid
  · exact reject13_16 ho hN hs hav hx hvalid
  · exact reject13_17 ho hN hs hav hx hvalid
  · exact reject13_18 ho hN hs hav hx hvalid
  · exact reject13_19 ho hN hs hav hx hvalid

@[expose] noncomputable def state13_21 : State := ⟨2339947129, 2576018715, 0⟩

private noncomputable def tree13_21 : AbundanceTree :=
  .split 21491 [
    (2, .split 1097113 [
      (1, .split 548557 [
        (6, .split 2203874382642540199649 [
          (4, .round 1 [(23377869537150461, 1), (3712767172624444257778315033753177656228041, 1)])]),
        (10, .split 2467279812034059839211825248502190841385239006113319093807 []),
        (12, .split 72113624030903550850231079202631276102987406200327171 []),
        (16, .abundant [(3, 2), (5, 2), (13, 2), (17, 2)]),
        (18, .round 1 [(86113795485607439604052118030456803715812887150635219024683636276590543192708133373765689324091, 1)]),
        (22, .abundant [(3, 2), (5, 2), (13, 2), (61, 4), (131, 2), (139, 2)])]),
      (2, .split 1888171 [
        (2, .abundant [(3, 4), (5, 1), (13, 2), (37, 1), (61, 4)]),
        (4, .abundant [(3, 2), (5, 2), (13, 2), (37, 1), (61, 4)]),
        (6, .abundant [(3, 2), (5, 1), (13, 2), (37, 1), (43, 2), (61, 4)]),
        (10, .abundant [(3, 2), (5, 1), (13, 2), (23, 2), (37, 1)]),
        (12, .abundant [(3, 2), (5, 1), (13, 2), (37, 1), (53, 1), (61, 4), (131, 2)]),
        (16, .split 314932115031930391453927992844361577110501639199958097399916506573843526444174467957 []),
        (18, .round 10291769043128655374740490724787519517494742647433109544467657857169143978218395874748554169 [(5, 1), (37, 1), (131, 1), (191, 1), (421, 1), (1597, 1), (5743, 1), (41611, 1), (712373208973, 1), (10291769043128655374740490724787519517494742647433109544467657857169143978218395874748554169, 1)])]),
      (4, .split 234895531489741 [
        (1, .abundant [(3, 2), (5, 2), (13, 2), (61, 4), (79, 2), (131, 2)]),
        (4, .split 22511 [
          (10, .split 1277 [
            (1, .abundant [(3, 4), (5, 2), (13, 2)]),
            (2, .split 125539 [
              (2, .split 5253388687 []),
              (4, .round 1 [(308378344871, 1)])]),
            (4, .split 9471036101 []),
            (6, .round 1 [(4339958797615285027, 1)])]),
          (12, .split 1301 [
            (2, .split 1699 [])])]),
        (6, .split 3402202720441747385273789895721708318379585190642722567830953267477833 [
          (1, .abundant [(3, 4), (5, 2), (13, 2)])])]),
      (6, .split 278822975484684541 [
        (1, .abundant [(3, 2), (5, 2), (13, 2), (43, 2), (61, 4)]),
        (2, .abundant [(3, 2), (5, 1), (13, 2), (37, 1), (43, 2), (61, 4)])]),
      (10, .abundant [(3, 2), (5, 1), (13, 2), (23, 2), (61, 4), (131, 2)]),
      (12, .split 1483264090910809022297249238099699996454992676757207 []),
      (16, .abundant [(3, 2), (5, 1), (13, 2), (17, 1), (61, 4)]),
      (18, .split 2243 [
        (2, .split 757 [
          (1, .abundant [(3, 2), (5, 2), (13, 2), (61, 4), (109, 2), (131, 2)]),
          (2, .split 14713 [
            (4, .round 26403131021 [(109, 1), (131, 1), (229, 1), (421, 1), (1774921, 1), (26403131021, 1)])])]),
        (4, .split 25322743716601 [
          (1, .split 271895803 [])]),
        (6, .round 4817 [(131, 1), (229, 1), (421, 1), (4817, 1), (6791, 1), (3894564762019, 1)])]),
      (22, .split 39791 [])]),
    (10, .abundant [(3, 2), (5, 1), (13, 2), (23, 2), (61, 4), (131, 2)]),
    (12, .split 195670722635262862398353040119397303469387 []),
    (16, .split 2621988021283204163582551346961647 [
      (2, .round 1 [(1166875779450778753574983, 1), (6068330598049957467183824807623, 1)])]),
    (18, .split 21329396889910742705842661 [
      (1, .split 283355944507855047853 [
        (2, .abundant [(3, 4), (5, 2), (13, 2)])]),
      (2, .round 1 [(10543542704374903, 1), (454943171687334063595189264919405759653528793403583, 1)])]),
    (22, .split 1604538047664286104952452485159370737260147 []),
    (28, .round 1 [(48122841333164549609122206833993119998744983191288478316291910299593321907823249799, 1)]),
    (30, .round 1 [(267372856258531148328842650781528800153927024741939503245536881597054218381813852256579422282259507435379953102455507, 1)])]

private theorem checked13_21 : replayAbundance bank 13 5759831 (10^300) 9 state13_21 tree13_21 = true := by
  decide +kernel

theorem reject13_21 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_21 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 9 h tree13_21 checked13_21

@[expose] noncomputable def state13_22 : State := ⟨8706943267009, 9585365649861, 0⟩

private noncomputable def tree13_22 : AbundanceTree :=
  .split 52379047267 [
    (2, .split 138161295607249 [
      (1, .abundant [(3, 2), (5, 4), (13, 2), (53, 2), (61, 6)]),
      (2, .split 528515019661 [
        (2, .split 10822630597 [
          (1, .split 549568273 [
            (4, .split 904442220513171631 []),
            (6, .round 1 [(8627893, 1), (27763969, 1), (416255023, 1), (7415508040487, 1), (194087695949273788167239329, 1)])]),
          (6, .split 549568273 [])]),
        (4, .abundant [(3, 4), (5, 1), (13, 2), (61, 6), (67, 2)]),
        (6, .round 1 [(6619231, 1), (452424840239577650219849039468623, 1), (76342820716020144503424651166936459, 1)])]),
      (4, .split 767768580936922371851320382865396497486741497741 [
        (1, .split 383884290468461185925660191432698248743370748871 []),
        (2, .round 1 [(6619231, 1)])]),
      (6, .split 161752099894238111149476439477896799106456558561838193105041160044183078886579113157 [
        (1, .round 1 [(6619231, 1)])])]),
    (4, .split 25332490598403837286469216576711 [
      (2, .split 24203101971249059783773 [
        (1, .split 373760264642068615009 [])])]),
    (10, .split 2898485987 [
      (2, .split 8401221019733850157 [
        (1, .round 1 [(23, 1), (67, 1), (24509, 1), (14252401, 1), (294730025479, 1)])]),
      (4, .round 24509 [(23, 1), (67, 1), (761, 1), (24509, 1)])]),
    (12, .split 578267 [])]

private theorem checked13_22 : replayAbundance bank 13 5759831 (10^300) 8 state13_22 tree13_22 = true := by
  decide +kernel

theorem reject13_22 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_22 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree13_22 checked13_22

@[expose] noncomputable def state13_23 : State := ⟨120554952071027159569, 132717448714879307913, 0⟩

private noncomputable def tree13_23 : AbundanceTree :=
  .split 4242586390571 [
    (4, .split 15008538895398688503343773594490169791961 [
      (1, .abundant [(3, 2), (5, 2), (13, 2), (17, 2)]),
      (2, .round 1 [(159804204906166690032650023, 1), (232073096028124516795385004906427, 1)])]),
    (6, .split 7789463501052688646527444606920201876722583734323 [])]

private theorem checked13_23 : replayAbundance bank 13 5759831 (10^300) 5 state13_23 tree13_23 = true := by
  decide +kernel

theorem reject13_23 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_23 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree13_23 checked13_23

@[expose] noncomputable def state13_24 : State := ⟨448584976656292060756249, 493841626668065904755619, 0⟩

private noncomputable def tree13_24 : AbundanceTree :=
  .split 14421466756460791 [
    (2, .split 2283523948634855486611 [
      (4, .split 5438163721383629312009508093830403446564040848379147163263659250398048437431242820421 [])]),
    (6, .split 187123 [
      (4, .split 97298466526008161 [
        (1, .round 1 [(113, 1), (197, 1), (12601, 1), (21893, 1), (246904049813, 1)])]),
      (6, .split 432756417615425605965733 [])])]

private theorem checked13_24 : replayAbundance bank 13 5759831 (10^300) 6 state13_24 tree13_24 = true := by
  decide +kernel

theorem reject13_24 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_24 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree13_24 checked13_24

@[expose] noncomputable def state13_25 : State := ⟨6211036261771731522793363410409, 6837652642027400294767486760391, 0⟩

private noncomputable def tree13_25 : AbundanceTree :=
  .split 362759437743508955104646759 [
    (2, .split 895444957565791173447100919955113823637 [
      (1, .split 192889342066209507897492313 [
        (2, .round 1 [(5221123, 1), (4103358316718614771, 1), (37482435530620244167, 1)])])]),
    (4, .split 103 [
      (2, .split 3571 [
        (2, .split 181 [
          (2, .split 139 [
            (2, .split 499 []),
            (4, .split 9170881 []),
            (6, .split 87683177 [])]),
          (6, .split 4338835663 [])]),
        (4, .split 322099207841 [
          (1, .abundant [(3, 4), (5, 2), (13, 2)])])]),
      (6, .split 585604027 []),
      (10, .round 1 [(3, 1), (199, 1), (24837228904511, 1)]),
      (12, .round 1 [(400500370843, 1)])])]

private theorem checked13_25 : replayAbundance bank 13 5759831 (10^300) 8 state13_25 tree13_25 = true := by
  decide +kernel

theorem reject13_25 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_25 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree13_25 checked13_25

@[expose] noncomputable def state13_26 : State := ⟨23111265930052612996314105250131889, 25442905480983956496829818235426257, 0⟩

private noncomputable def tree13_26 : AbundanceTree :=
  .split 607127818287731321660577427051 [
    (2, .split 5819214590069067382417 [
      (1, .split 44562864398954114497 []),
      (2, .split 51308969484858146797 [
        (2, .round 1 [(25100776701304901375513304345283, 1)])])]),
    (4, .split 27173809443719126257339868549348079099288331082311717024187031097884640122734116803386833064845134988810864430052134101 [])]

private theorem checked13_26 : replayAbundance bank 13 5759831 (10^300) 6 state13_26 tree13_26 = true := by
  decide +kernel

theorem reject13_26 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_26 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree13_26 checked13_26

@[expose] noncomputable def state13_27 : State := ⟨319994913376225601181498687350591364123649, 352278423867732385206022667346612563876949, 0⟩

private noncomputable def tree13_27 : AbundanceTree :=
  .split 40957844886377442763169709027626155549 [
    (1, .abundant [(3, 2), (5, 2), (13, 2), (47, 2), (61, 22)]),
    (2, .split 602412622974719759892728119770418230345437465443056727166483222655841 [
      (1, .round 1 [(178137130626632223577706933544126507968420645362333, 1)])])]

private theorem checked13_27 : replayAbundance bank 13 5759831 (10^300) 5 state13_27 tree13_27 = true := by
  decide +kernel

theorem reject13_27 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_27 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree13_27 checked13_27

@[expose] noncomputable def state13_28 : State := ⟨16486257730758909410063096279332562334384061173363289, 18149516276968610033977745933549249836166595155646387, 0⟩

private noncomputable def tree13_28 : AbundanceTree :=
  .split 26582256519936794775401 [
    (1, .split 129924628343 [
      (2, .split 7215061951 [
        (2, .split 1580015219 [
          (2, .split 192034468757817937 [
            (2, .round 1 [(828561571, 1), (613388130561469, 1), (3049792463518831, 1)])]),
          (4, .round 1 [(59503651, 1), (62144713, 1), (828561571, 1), (81148072047903370096556788254361, 1)]),
          (6, .round 1 [(17620041127398282365478588843751349904938701468548727, 1)])]),
        (6, .round 1 [(18451, 1), (22571, 1), (37991, 1), (17559739, 1), (59503651, 1), (1580015219, 1)])]),
      (6, .split 1580015219 [
        (2, .round 1 [(37991, 1), (59503651, 1), (192034468757817937, 1)])])]),
    (4, .split 129924628343 [
      (2, .round 1 [(7215061951, 1)])])]

private theorem checked13_28 : replayAbundance bank 13 5759831 (10^300) 8 state13_28 tree13_28 = true := by
  decide +kernel

theorem reject13_28 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_28 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree13_28 checked13_28

@[expose] noncomputable def state13_29 : State := ⟨61345365016153901914844781255396464446243091626084798369, 67534350066600197936431192618736758640375900574160217373, 0⟩

private noncomputable def tree13_29 : AbundanceTree :=
  .split 247844301073446432073571189153011918514923282850779 [
    (2, .split 2048215633 [
      (1, .split 19322789 [
        (2, .round 1 [(22717, 1), (11373751, 1)])])])]

private theorem checked13_29 : replayAbundance bank 13 5759831 (10^300) 6 state13_29 tree13_29 = true := by
  decide +kernel

theorem reject13_29 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_29 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree13_29 checked13_29

@[expose] noncomputable def state13_30 : State := ⟨3160536170944441839043677873485181399746270640585913044702082217209, 3479394997658067480201634724035017748063867767343249242407233115451, 0⟩

private noncomputable def tree13_30 : AbundanceTree :=
  .split 19013087418896543607659206142267856546797091624826498592389251997 [
    (1, .split 118470123710219891706333708505740644829333323791367 [])]

private theorem checked13_30 : replayAbundance bank 13 5759831 (10^300) 4 state13_30 tree13_30 = true := by
  decide +kernel

theorem reject13_30 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_30 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree13_30 checked13_30

@[expose] noncomputable def state13_31 : State := ⟨43760281297645561537146355891493937517044303632520698856770922748403277769, 48175149913768974698142482329067734171870370951659621433741006966511419103, 0⟩

private noncomputable def tree13_31 : AbundanceTree :=
  .split 21804100501191050418513591293754946574976697774374305117 [
    (1, .split 1592255129780302797374357727435107 [
      (2, .round 1 [(94301495279, 1)])])]

private theorem checked13_31 : replayAbundance bank 13 5759831 (10^300) 5 state13_31 tree13_31 = true := by
  decide +kernel

theorem reject13_31 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_31 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree13_31 checked13_31

@[expose] noncomputable def state13_32 : State := ⟨162832006708539134479721590272248941500921853816609520446044603546808596578449, 179259732829134354851788176746461038853529650311125451354950286922388990493609, 0⟩

private noncomputable def tree13_32 : AbundanceTree :=
  .split 164446796105869041894952007169259881366870041 [
    (1, .split 11015699879053969868640461796866126821 [])]

private theorem checked13_32 : replayAbundance bank 13 5759831 (10^300) 4 state13_32 tree13_32 = true := by
  decide +kernel

theorem reject13_32 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_32 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree13_32 checked13_32

@[expose] noncomputable def state13_33 : State := ⟨2254546074597366198283842863176705556440065341370018579182182659617147885658348880609, 2482001758454674444915437660911396856660793826993443530513876235631777302525063959981, 0⟩

private noncomputable def tree13_33 : AbundanceTree :=
  .split 28583991118304278404388234765612493959 []

private theorem checked13_33 : replayAbundance bank 13 5759831 (10^300) 3 state13_33 tree13_33 = true := by
  decide +kernel

theorem reject13_33 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_33 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_33 checked13_33

@[expose] noncomputable def state13_34 : State := ⟨116155057777379338880190940048561971962460980846684617820991371844558096004217757274120973665849, 127873659760245124252423221278313342506602754358140077784588430364970613973874045803847379588939, 0⟩

private noncomputable def tree13_34 : AbundanceTree :=
  .split 2799184268335147360617347079224746490992349612030418707511487619441500331513883799676243 []

private theorem checked13_34 : replayAbundance bank 13 5759831 (10^300) 3 state13_34 tree13_34 = true := by
  decide +kernel

theorem reject13_34 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_34 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_34 checked13_34

@[expose] noncomputable def state13_35 : State := ⟨5984352060614168136614119758462420315214375572076442255837687561582588206750677089726543460466363000897489, 6588098821758970306609804621668244376601388018845101075139655448712665892698008713275878170531164711934777, 0⟩

private noncomputable def tree13_35 : AbundanceTree :=
  .split 45765542239805727756249259984195022727099019288437016468311336590418178576565571345601 [
    (1, .round 1 [(1657268111, 1)])]

private theorem checked13_35 : replayAbundance bank 13 5759831 (10^300) 4 state13_35 tree13_35 = true := by
  decide +kernel

theorem reject13_35 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_35 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree13_35 checked13_35

@[expose] noncomputable def state13_36 : State := ⟨22267774017545319636341139621238665992912691503696441633972035416648810717319269450872468216395336726339556569, 24514315715765128510895082997227537325333764818122621100594657924659829786729290422099542672546463893109316563, 0⟩

private noncomputable def tree13_36 : AbundanceTree :=
  .round 1 [(398853286456071792609917995907, 1), (1000403244183535565720394723140528028235711874491322863, 1)]

private theorem checked13_36 : replayAbundance bank 13 5759831 (10^300) 3 state13_36 tree13_36 = true := by
  decide +kernel

theorem reject13_36 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_36 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_36 checked13_36

@[expose] noncomputable def state13_37 : State := ⟨1147244053570083849947699893591585818483101639058544688285825800070897340221717708467980460576761706115666163637616727409, 1262986722879965090430589143211328648099296212703208516305194615995209764190831832310460146096488256939761477779754983041, 0⟩

private noncomputable def tree13_37 : AbundanceTree :=
  .round 7525224795311420974568704601033981 [(5672941282190938732295369523461, 1), (7525224795311420974568704601033981, 1), (600990558184559183777724051749697130888724712684563, 1)]

private theorem checked13_37 : replayAbundance bank 13 5759831 (10^300) 3 state13_37 tree13_37 = true := by
  decide +kernel

theorem reject13_37 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_37 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_37 checked13_37

@[expose] noncomputable def state13_38 : State := ⟨15884558753926863343043711042386016180571886481243999445400106581479433300032808138332011048252610877766241310806422826645355969, 17487113350107058727652558813230285860327807572990805306607632127125731156633751207909293819688747063955083999263520514185612293, 0⟩

private noncomputable def tree13_38 : AbundanceTree :=
  .split 293456387082165744658275731198291921555349530889701149644553301446693162048276102157778796572509 []

private theorem checked13_38 : replayAbundance bank 13 5759831 (10^300) 3 state13_38 tree13_38 = true := by
  decide +kernel

theorem reject13_38 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_38 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_38 checked13_38

@[expose] noncomputable def state13_39 : State := ⟨59106443123361858499465648788718366207907989596708921936333796589684971309422079082733413110547965076168183917510699337947369560649, 65069548775748365525595171344029893686279771979098786545886999145034845633834188244630482303061827824976867561259559833284663353599, 0⟩

private noncomputable def tree13_39 : AbundanceTree :=
  .round 8373573793950147412813487438357 [(25183243286549632313, 1), (8373573793950147412813487438357, 1), (4807557298497810374791931204229711982139, 1)]

private theorem checked13_39 : replayAbundance bank 13 5759831 (10^300) 3 state13_39 tree13_39 = true := by
  decide +kernel

theorem reject13_39 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_39 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_39 checked13_39

@[expose] noncomputable def state13_40 : State := ⟨3045186076862757054761179944054516420427711582665337071708642208156994832916969880901372934618696638570938714827650773113963333079852574120289, 3352407512427905029812529754978359645092164141744887350244928300755082181444983706163907896365730826071734602921209623300904604257435333817037, 0⟩

private noncomputable def tree13_40 : AbundanceTree :=
  .round 1 [(558852593312647853822479983606911173523573367961068091845598154543, 1)]

private theorem checked13_40 : replayAbundance bank 13 5759831 (10^300) 3 state13_40 tree13_40 = true := by
  decide +kernel

theorem reject13_40 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_40 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_40 checked13_40

@[expose] noncomputable def state13_41 : State := ⟨42163162235655513001851590477767729689131246567442613306283458340030653494389931172749346334433869284887684666247995008063011189653679044710236368049, 46416901384282297005884546795199326086762535052501172814402588308655047826220394643136188671724386866587891906245203971894220306716372699812659622929, 0⟩

private noncomputable def tree13_41 : AbundanceTree :=
  .round 1 [(112558099261012009195559934112878460530409982687138540328308072080847191, 1)]

private theorem checked13_41 : replayAbundance bank 13 5759831 (10^300) 3 state13_41 tree13_41 = true := by
  decide +kernel

theorem reject13_41 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_41 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_41 checked13_41

@[expose] noncomputable def state13_42 : State := ⟨169, 183, 0⟩

private theorem checked13_42 : checkChildren bank 13 5759831 (10^300) state13_42 61 [state13_20, state13_21, state13_22, state13_23, state13_24, state13_25, state13_26, state13_27, state13_28, state13_29, state13_30, state13_31, state13_32, state13_33, state13_34, state13_35, state13_36, state13_37, state13_38, state13_39, state13_40, state13_41] = true := by
  decide +kernel

theorem reject13_42 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_42 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state13_20, state13_21, state13_22, state13_23, state13_24, state13_25, state13_26, state13_27, state13_28, state13_29, state13_30, state13_31, state13_32, state13_33, state13_34, state13_35, state13_36, state13_37, state13_38, state13_39, state13_40, state13_41] ?_ checked13_42
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject13_20 ho hN hs hav hx hvalid
  · exact reject13_21 ho hN hs hav hx hvalid
  · exact reject13_22 ho hN hs hav hx hvalid
  · exact reject13_23 ho hN hs hav hx hvalid
  · exact reject13_24 ho hN hs hav hx hvalid
  · exact reject13_25 ho hN hs hav hx hvalid
  · exact reject13_26 ho hN hs hav hx hvalid
  · exact reject13_27 ho hN hs hav hx hvalid
  · exact reject13_28 ho hN hs hav hx hvalid
  · exact reject13_29 ho hN hs hav hx hvalid
  · exact reject13_30 ho hN hs hav hx hvalid
  · exact reject13_31 ho hN hs hav hx hvalid
  · exact reject13_32 ho hN hs hav hx hvalid
  · exact reject13_33 ho hN hs hav hx hvalid
  · exact reject13_34 ho hN hs hav hx hvalid
  · exact reject13_35 ho hN hs hav hx hvalid
  · exact reject13_36 ho hN hs hav hx hvalid
  · exact reject13_37 ho hN hs hav hx hvalid
  · exact reject13_38 ho hN hs hav hx hvalid
  · exact reject13_39 ho hN hs hav hx hvalid
  · exact reject13_40 ho hN hs hav hx hvalid
  · exact reject13_41 ho hN hs hav hx hvalid

@[expose] noncomputable def state13_43 : State := ⟨28561, 30941, 0⟩

private noncomputable def tree13_43 : AbundanceTree :=
  .split 30941 [
    (1, .split 191 [
      (10, .split 1900421426047 [
        (6, .split 1095547099641958489507506167316839141886595074112338348965965156459230979 [])]),
      (12, .split 48552947 [
        (6, .split 715922848963684943005366120516304577581903 []),
        (10, .round 1 [(9049, 1), (19163, 1), (92041, 1), (301627, 1), (7998827, 1), (36314543, 1), (568666623058430693389293915009126543755004788259311248333, 1)]),
        (12, .round 1 [(246847105841685728835149098355964544683232858131764102182366031361452490304679361466439, 1)])]),
      (16, .split 3153651086937051299292748168322873857 [
        (2, .split 1745535544184727081740825307430561100072908388829261675774868582261 [])]),
      (22, .split 709691990009063207 [
        (2, .split 12196726415046495775567 [])]),
      (28, .split 6937262398479723944960192269796773 []),
      (30, .split 508375662001573857302831322631066310940308723 [
        (2, .round 1 [(62683, 1), (8510327225640925409, 1)])]),
      (36, .split 247083378176222619030563834191940715419265911223308036537 []),
      (40, .split 53817680879343932139042949972070052863773269539980203371 []),
      (42, .split 115818625571197592034031211634645997677055792367221 []),
      (46, .round 1 [(5730395978260105084320676489373993, 1), (148467031893746524227485026611653806025492334017387237830406481156482009, 1)]),
      (52, .round 1 [(244797638979090330792744428374308875307086167784283401115144024498759277250936541488346219559, 1)]),
      (58, .round 1 [(309230803668597407783342504083862087212680638905258601497392523, 1)]),
      (60, .round 1 [(574955521536424328969894806814092993366644832673239429849749437816790017462473549408456349821958837352445007711886661058712680471663, 1)])]),
    (2, .split 14083 [
      (2, .split 14401 [
        (4, .split 2235195191 [
          (2, .split 154545688753 [
            (1, .abundant [(3, 2), (5, 2), (13, 4), (41, 2), (157, 2)])]),
          (6, .abundant [(3, 2), (5, 1), (13, 4), (29, 1), (41, 1), (157, 1)]),
          (10, .split 21313122575103426339142536782748035552885009391211094980352486742992727902464000349 []),
          (12, .round 7986227195062460109131861565304887264200477092835262118674682173814627482140406487720250871265720775025517 [(41, 1), (157, 1), (433, 1), (599, 1), (3251, 1), (4591, 1), (93871, 1), (7986227195062460109131861565304887264200477092835262118674682173814627482140406487720250871265720775025517, 1)])]),
        (6, .split 853390763 [
          (2, .split 475686345674143 [
            (4, .split 25809494423403483277404013696925751121 [
              (1, .round 1 [(1010981, 1), (8045221, 1), (47462563, 1), (2544698614445093, 1), (220488179834417489299, 1)])]),
            (6, .round 1 [(1715933306741158453490758428846972721604166119798305693451985869778581107, 1)])]),
          (10, .round 10079447284694915407581873184207422316723510453 [(34721, 1), (47462563, 1), (877398919, 1), (363063988082203, 1), (192767758756217503, 1), (10079447284694915407581873184207422316723510453, 1)]),
          (12, .round 1 [(4591, 1), (6343, 1), (47462563, 1)])]),
        (10, .split 83043705950602621825261 [
          (1, .split 171102215257 [
            (4, .split 17504442856512010512735312327385737601 [])]),
          (2, .split 480330434889939121 [
            (2, .split 141703510716693878434717429 [
              (1, .abundant [(3, 4), (5, 2), (13, 4)])])]),
          (4, .round 1 [(679486068990446580710834938122055909620993859442745254622708586361638871027552831, 1)])]),
        (12, .split 6748447329627331021015103435872211423 [
          (2, .split 5215482418601884555571969387072746710022501 [
            (1, .round 1 [(30762911079533110898866150285320970579, 1)])])]),
        (16, .split 232826755072522951415683 []),
        (18, .split 3955651156092694836805161806316602227205569 [
          (1, .round 1 [(211, 1), (229, 1), (433, 1), (1013, 1), (3877, 1), (4591, 1), (1081646128183, 1), (9558458371001354772407, 1), (202091755830016292540433547, 1)])]),
        (22, .split 86955759522758784026938639388725025838814508360983494849135689173 []),
        (28, .round 1 [(2878319791561117685582532984481924989856693782709674033037185004142735435821967737094116024989323, 1)]),
        (30, .round 1 [(4591, 1), (18137543, 1), (5556696991, 1)])]),
      (6, .split 7801927585025353459681093 [
        (1, .split 25125200742702138527 [])]),
      (10, .split 64852170705457741955185923109 [
        (1, .split 8819227394713997 [
          (4, .round 1 [(4732145777657, 1), (530468431681571, 1), (104631953847582332778178389617029701971, 1)])])]),
      (12, .split 770452554484090197386587479931326064708100638279 []),
      (16, .split 39142161322463429947510947236016017221408300438307 [
        (2, .round 1 [(61165834505641003, 1)])]),
      (18, .split 1435130102620557966393278537760156017252441420078670131 []),
      (22, .split 599038420461060696413181332715356424078575978745199 []),
      (28, .split 929 [
        (2, .split 5503 [
          (2, .split 165511 [
            (2, .split 246793303 [])])]),
        (6, .split 172110179118949 [
          (1, .round 1 [(3442203582379, 1)])])]),
      (30, .split 9280684146823 [])]),
    (10, .split 8682564712362839769429759610849611323291 []),
    (12, .split 587062252516880486410662191647 []),
    (16, .split 254315833448083019814973207753737859223 [
      (2, .round 1 [(1436162282970486151637648797548860940964159294865554226167, 1)])]),
    (18, .split 12574229158179939996937343 [
      (2, .round 547366799984016650988905202217 [(9600433, 1), (45712301287, 1), (2314462327501, 1), (46434088032473231, 1), (10736056226838183421, 1), (547366799984016650988905202217, 1)])]),
    (22, .split 911193301 [
      (1, .split 331937 [
        (4, .split 306949194545171771 []),
        (6, .round 1 [(357750155087247998348897464933, 1)])]),
      (4, .split 2956596702431 [])]),
    (28, .round 1 [(19680915995838469586276407353067388962488704313299562261457737772505606167395508436792406664425712169883467, 1)]),
    (30, .split 81760848073 [
      (1, .split 692888543 [])])]

private theorem checked13_43 : replayAbundance bank 13 5759831 (10^300) 9 state13_43 tree13_43 = true := by
  decide +kernel

theorem reject13_43 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_43 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 9 h tree13_43 checked13_43

@[expose] noncomputable def state13_44 : State := ⟨4826809, 5229043, 0⟩

private noncomputable def tree13_44 : AbundanceTree :=
  .split 5229043 [
    (4, .split 32607907713428723311 [
      (2, .split 70996104180895725120735321697 [
        (1, .split 178043084228769642541931 [
          (2, .split 7439834553159901014667 [
            (2, .round 1 [(4373226763450139295773022706687441, 1)])])]),
        (2, .split 6662904114579970644590941 [
          (1, .split 4483784733903075803897 []),
          (2, .round 1 [(4992178363, 1), (440546526996272557867, 1)])])]),
      (6, .round 267233 [(491, 1), (33937, 1), (151841, 1), (267233, 1), (223957037756467, 1)])]),
    (10, .split 1677917555538661023466032373392973155985961563 [
      (2, .round 467629 [(27457, 1), (38611, 1), (129529, 1), (467629, 1), (373559364091, 1)])]),
    (12, .split 2810563613697654668266333727 []),
    (16, .split 8807 [
      (2, .split 77572057 [
        (1, .split 38786029 [
          (4, .round 1 [(743579344231162833521, 1)])]),
        (2, .split 5732075647 []),
        (4, .split 883155911952273463293383790061 [])]),
      (4, .split 3664781 [
        (2, .split 4511462359 [
          (2, .round 1 [(72598579, 1)])]),
        (4, .round 1 [(1333691, 1)])]),
      (10, .round 1 [(542943628346324860024620276188509667, 1)])]),
    (18, .round 1 [(3640027656499981435791423265686003853682834538332462603519434638613263300679556521958816067063444672485047090591, 1)])]

private theorem checked13_44 : replayAbundance bank 13 5759831 (10^300) 8 state13_44 tree13_44 = true := by
  decide +kernel

theorem reject13_44 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_44 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree13_44 checked13_44

@[expose] noncomputable def state13_45 : State := ⟨137858491849, 149346699503, 0⟩

private noncomputable def tree13_45 : AbundanceTree :=
  .split 18041 [
    (4, .split 790579404481 [
      (2, .split 493975465285722559 [
        (2, .split 13946830486961377 [
          (1, .abundant [(3, 2), (5, 2), (13, 10), (23, 2)]),
          (2, .abundant [(3, 4), (5, 1), (13, 10), (23, 2)])]),
        (4, .split 5091091801969160161417843420837771079275273568507161 [
          (1, .abundant [(3, 2), (5, 2), (13, 10), (23, 2)])])]),
      (6, .split 232135472986202362799296691 [
        (2, .round 23954198376965473 [(859, 1), (1327, 1), (26801, 1), (111327371, 1), (3249191191, 1), (121387119169, 1), (23954198376965473, 1)])]),
      (10, .split 26801 [
        (1, .abundant [(3, 2), (5, 2), (13, 10), (23, 2)])])]),
    (6, .split 9108709959749 [
      (1, .abundant [(3, 2), (5, 4), (13, 10), (23, 2)]),
      (2, .split 117967608271 [
        (4, .split 11360243651129135071 [
          (2, .abundant [(3, 2), (5, 1), (13, 10), (23, 2), (61, 1), (181, 1)])]),
        (6, .split 3392420147482768839966377445286704923659241 [
          (1, .round 1 [(236773, 1), (10723561, 1), (25384507, 1), (12467742253891, 1)])])])]),
    (12, .split 18332526062277636790838217843221 [
      (1, .split 2542396357125397 [
        (2, .split 2154593078908163914456513177669 [])]),
      (2, .split 4220664214690363448000050143108419891813994478063 [])]),
    (16, .split 4373020399515950003899137643344017725037 [
      (1, .split 93815349051618588433552823 [])]),
    (18, .split 1026463775022809327511730559391500791573 [
      (2, .split 18936535212031693 [])]),
    (22, .split 2473918340499187090562261581208120911 []),
    (28, .round 1 [(428810647, 1), (800672808675011, 1), (276815509957929740767, 1)]),
    (30, .split 106092913 [
      (1, .round 1 [(46687, 1), (3047921, 1), (53046457, 1)]),
      (2, .round 463140612061 [(3047921, 1), (463140612061, 1)])])]

private theorem checked13_45 : replayAbundance bank 13 5759831 (10^300) 7 state13_45 tree13_45 = true := by
  decide +kernel

theorem reject13_45 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_45 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree13_45 checked13_45

end OddPerfect.IndexComponent.Size300
