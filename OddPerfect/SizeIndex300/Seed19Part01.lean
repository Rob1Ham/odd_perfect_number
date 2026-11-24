module

public import OddPerfect.SizeIndex300.Seed127

public section

namespace OddPerfect.IndexComponent.Size300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def state19_1 : State := ⟨64280950465195205312190877849, 67926810270325613558543423598, 861001⟩

private noncomputable def tree19_1 : AbundanceTree :=
  .split 2851 [
    (2, .split 5779 [
      (2, .abundant [(3, 4), (7, 2), (13, 2), (19, 4), (61, 2)]),
      (4, .abundant [(3, 2), (7, 2), (11, 2), (13, 2), (19, 4)]),
      (10, .abundant [(3, 2), (7, 2), (13, 2), (19, 4), (23, 2)]),
      (12, .split 83361611358661224033981134561 [
        (2, .split 4933442879 [
          (2, .split 20999878037350519 []),
          (4, .round 1 [(1106443776670315658834562891569951, 1)])])]),
      (16, .split 9320924080054019661443653796384897173 [
        (2, .abundant [(3, 4), (7, 2), (13, 2), (19, 4), (61, 2)])]),
      (18, .split 83194434912745262406561921388251499906829 []),
      (22, .abundant [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (67, 2), (139, 2), (151, 2)]),
      (28, .split 337 [
        (2, .abundant [(3, 4), (7, 2), (13, 2), (19, 4), (43, 2)]),
        (4, .split 12936304421 []),
        (6, .abundant [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (67, 2), (151, 2), (239, 2)])]),
      (30, .round 1 [(9494219754101766840536714797849310944061977669021960566301314538974316798167363222414455178643, 1)])]),
    (4, .abundant [(3, 2), (5, 2), (13, 2), (19, 4)]),
    (6, .split 28971231269 [
      (2, .split 363190065456882121 [
        (2, .split 523988383861462873 [
          (2, .split 1020392150510893 [
            (2, .round 1 [(1125114715117, 1), (1252948424577913278018125353, 1)])]),
          (4, .round 1 [(1125114715117, 1)])]),
        (4, .abundant [(3, 2), (5, 2), (13, 2), (19, 4)])]),
      (4, .split 312076885622591 [
        (2, .split 47361822949683247927 [
          (2, .round 1 [(5281, 1), (58031, 1), (66333529, 1), (226818061, 1), (18542517953, 1), (32475238801, 1)])]),
        (4, .abundant [(3, 2), (5, 2), (13, 2), (19, 4)])]),
      (10, .round 1 [(722224466327578569573582916933905512211079625644958827873892307683470856171152818763542037, 1)])]),
    (10, .split 1475685122474626705890337 [
      (2, .split 1629103649054388987619177 [
        (2, .round 1 [(61, 1), (223, 1), (337, 1), (25903, 1), (13351537, 1), (24050872253, 1), (1498933666303391083, 1)])]),
      (4, .round 1 [(24050872253, 1), (23919669339506365080611, 1)])]),
    (12, .split 475547629160366607077789777948273 [
      (2, .round 1 [(3, 1), (13, 1), (53, 1), (61, 1), (313, 1), (337, 1), (18493, 1), (11445877, 1), (99752055211293601, 1), (391664745994421369991855543234103738913767, 1)])]),
    (16, .split 1053642488759991945893094661008259128533669236780153 []),
    (18, .split 634592051620271588327313467944021 [
      (2, .round 1 [(7042709062791925662796369379741925596765609493721, 1)])]),
    (22, .split 117095878222117993421317 [
      (2, .round 1 [(5369801401451, 1), (68633947703159, 1), (153348667863557, 1)])]),
    (28, .round 1 [(245733022013211511, 1), (8975702163823010500332303258451344307619211676537997401195681, 1)]),
    (30, .round 1 [(745906374085257932557448440539987714614476312034118845516920489329618013921183734534570871788911, 1)]),
    (36, .round 1 [(13515909822310892207971748423538338754117939588605145949207, 1)])]

private theorem checked19_1 : replayAbundance bank 19 127 (10^300) 8 state19_1 tree19_1 = true := by
  decide +kernel

theorem reject19_1 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_1 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree19_1 checked19_1

@[expose] noncomputable def state19_2 : State := ⟨55345962631483536969001658018866849, 58485051569639516343404275348293897, 0⟩

private noncomputable def tree19_2 : AbundanceTree :=
  .split 217081 [
    (1, .split 108541 [
      (2, .split 3927085741 [
        (2, .split 137476732909837 [
          (2, .split 2168798562241 [
            (2, .split 198041655652411 [
              (2, .abundant [(3, 8), (7, 2), (13, 2), (19, 4), (31, 2)]),
              (4, .abundant [(3, 6), (5, 2), (13, 2)])]),
            (4, .abundant [(3, 6), (5, 2), (11, 2)]),
            (6, .round 1 [(151, 1), (337, 1), (613, 1), (18661, 1), (5196805069, 1)])]),
          (4, .split 7667241785020539262163120730869333821 []),
          (6, .round 1 [(3205372870184002819915411302451432731108548941760904872958355381, 1)])]),
        (4, .abundant [(3, 4), (5, 2), (13, 2)]),
        (6, .split 3086476300362699201278645915793496455762857967332917 []),
        (10, .round 1 [(872376251565413458447512751375430083268293187776480839125193096165114831718571582824789235909711, 1)]),
        (12, .round 1 [(337, 1), (18661, 1)])]),
      (4, .abundant [(3, 2), (5, 2), (11, 2), (13, 2)]),
      (6, .split 27282710017315537 [
        (2, .split 1785003035704867089959419277971 [
          (2, .round 1 [(5502997992185822133325044025114218231630382402194049024447, 1)])]),
        (4, .round 1 [(137117, 1), (50368305776617547793954081216371152117495674623682719844521812111, 1)]),
        (6, .abundant [(3, 2), (7, 2), (13, 2), (19, 4), (29, 2), (61, 2)])]),
      (10, .split 5858329822057687753549 [
        (2, .round 1 [(23, 1), (151, 1), (337, 1), (18661, 1), (76873, 1), (2542879, 1), (3733049, 1), (588744487, 1), (3037086319, 1), (766390278611, 1), (19269467882879558659429, 1)])]),
      (12, .split 78502102067780881464335234231178888128258220373507 []),
      (16, .round 1 [(18661, 1), (312971, 1), (13688084491799, 1), (86628006773587143889896572224721096068997342530859346491996933, 1)]),
      (18, .round 1 [(647, 1), (18661, 1), (2270159, 1), (2738928731663661112961658341486626467776989204065017, 1)]),
      (22, .round 1 [(151, 1), (337, 1), (18661, 1), (5957090827287409, 1)])]),
    (2, .abundant [(3, 4), (7, 2), (13, 1), (19, 4), (61, 2)]),
    (4, .abundant [(3, 2), (5, 1), (13, 1), (19, 4), (61, 2)]),
    (6, .split 31045189810031713 [
      (1, .split 15522594905015857 [
        (2, .split 375628121880369543406597 [
          (2, .round 1 [(116235975405131, 1), (76255772534144976481153, 1), (616768546425759064075573, 1)])]),
        (4, .round 1 [(120691, 1), (998125094891, 1), (116235975405131, 1), (29735806818490958012011042351, 1)])]),
      (2, .split 1974702993887119 [
        (2, .split 99544270401529168129 [
          (1, .abundant [(3, 4), (5, 2), (13, 2)]),
          (2, .round 80761 [(18661, 1), (80761, 1), (161683, 1), (233017007827, 1), (116235975405131, 1)])]),
        (4, .round 1 [(5023, 1), (27611, 1), (233017007827, 1), (116235975405131, 1)])]),
      (4, .round 1 [(116235975405131, 1), (282833999975199879418122527387051, 1), (3284321492144095749319975883891791, 1)]),
      (6, .abundant [(3, 2), (7, 2), (13, 1), (19, 4), (29, 2), (61, 2)])]),
    (10, .split 6134603577177962917566611229463 [
      (2, .round 1 [(45286836400872032286867207663175848670999530560063945909143, 1)])]),
    (12, .split 1845345910866732954516060109015374162747512913478950637 [
      (1, .abundant [(3, 2), (7, 2), (13, 2), (19, 4), (43, 2), (53, 2)])]),
    (16, .round 1 [(469071595771, 1), (378435016196184360737733930679849755379451134490811986496010608290744011, 1)]),
    (18, .split 8111291 [
      (2, .split 2787959227 [
        (2, .abundant [(3, 4), (7, 2), (13, 1), (19, 4), (61, 2)])]),
      (4, .abundant [(3, 2), (5, 1), (13, 1), (19, 4), (61, 2)])]),
    (22, .round 57627421 [(13, 1), (151, 1), (337, 1), (1151, 1), (1289, 1), (18661, 1), (57627421, 1)])]

private theorem checked19_2 : replayAbundance bank 19 127 (10^300) 9 state19_2 tree19_2 = true := by
  decide +kernel

theorem reject19_2 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_2 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 9 h tree19_2 checked19_2

@[expose] noncomputable def state19_3 : State := ⟨41029219669737004486679422282028501514261844849, 43356297625974023933952393934303747613919351495, 0⟩

private noncomputable def tree19_3 : AbundanceTree :=
  .abundant [(3, 2), (5, 1), (11, 2), (13, 1)]

private theorem checked19_3 : replayAbundance bank 19 127 (10^300) 3 state19_3 tree19_3 = true := by
  decide +kernel

theorem reject19_3 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_3 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_3 checked19_3

@[expose] noncomputable def state19_4 : State := ⟨30415892807146406409861139071987499846415741145716620822849, 32141008571972557621636710913796222560156328099920632165093, 0⟩

private noncomputable def tree19_4 : AbundanceTree :=
  .abundant [(3, 2), (7, 2), (13, 1), (19, 4), (29, 1), (61, 1)]

private theorem checked19_4 : replayAbundance bank 19 127 (10^300) 3 state19_4 tree19_4 = true := by
  decide +kernel

theorem reject19_4 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_4 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_4 checked19_4

@[expose] noncomputable def state19_5 : State := ⟨16715339137123662655623891063792904575879258557636806564291554928639802167686778849, 17663392684086861112290592728404744472999804214541372293342167418539133261811060289, 0⟩

private noncomputable def tree19_5 : AbundanceTree :=
  .split 93405926305602818503366746111204285215950653747431 [
    (2, .round 671128236077515738032837904111506686388860348391579216895155547781469320228005072453696196476372861 [(2396970181, 1), (671128236077515738032837904111506686388860348391579216895155547781469320228005072453696196476372861, 1)])]

private theorem checked19_5 : replayAbundance bank 19 127 (10^300) 4 state19_5 tree19_5 = true := by
  decide +kernel

theorem reject19_5 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_5 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_5 checked19_5

@[expose] noncomputable def state19_6 : State := ⟨12391460708302360189613975194298055555540860401864990588185720307876065455419703141920393756849, 13094274344339821356883296717526702483167075110263881894330339400452412510855378609967941141887, 0⟩

private noncomputable def tree19_6 : AbundanceTree :=
  .split 359489271368256328030150289666093123281 [
    (1, .split 6986029164423431842177 [
      (2, .round 1 [(337, 1), (2341, 1), (12196359822028671563, 1)])]),
    (2, .round 1 [(12196359822028671563, 1)])]

private theorem checked19_6 : replayAbundance bank 19 127 (10^300) 5 state19_6 tree19_6 = true := by
  decide +kernel

theorem reject19_6 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_6 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree19_6 checked19_6

@[expose] noncomputable def state19_7 : State := ⟨6809843441286413076331362287670108285479793766668619007131628949184782405278814546592353157311587479576243240155712849, 7196081266065995005331323813026243257512375086379965438067789039666341423142529336187635915513688971575430910442573083, 0⟩

private noncomputable def tree19_7 : AbundanceTree :=
  .split 541275423929242862808856008001028521982577712499 []

private theorem checked19_7 : replayAbundance bank 19 127 (10^300) 3 state19_7 tree19_7 = true := by
  decide +kernel

theorem reject19_7 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_7 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_7 checked19_7

@[expose] noncomputable def state19_8 : State := ⟨5048291676295100766803645678140083074514303899390893308114425203910794202608182751018317881510112585657891632805908996311210690849, 5334618551900445730256687475941365032906247090977693479900715756845285984625039982890613888969757572653119570094127547042477922681, 0⟩

private noncomputable def tree19_8 : AbundanceTree :=
  .split 7070053 [
    (1, .split 3535027 [
      (2, .split 306758461 [
        (2, .abundant [(3, 4), (7, 2), (13, 2), (19, 4), (37, 2)])]),
      (4, .round 1 [(8761, 1)])]),
    (2, .abundant [(3, 2), (7, 2), (13, 2), (19, 4), (43, 2), (61, 1), (139, 2)]),
    (4, .round 2053 [(13, 1), (61, 1), (151, 1), (337, 1), (2053, 1)])]

private theorem checked19_8 : replayAbundance bank 19 127 (10^300) 6 state19_8 tree19_8 = true := by
  decide +kernel

theorem reject19_8 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_8 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree19_8 checked19_8

@[expose] noncomputable def state19_9 : State := ⟨2774336034369656423323476458658693421833875794069841343819979974513879075743745916821759090431046359351822384631172441290974184304185337279466035668646849, 2931689654076385803278395612058768859931380609680082244503751122278818140031061156571567021170568840249288811713479411553911817739166306218558647277889877, 0⟩

private noncomputable def tree19_9 : AbundanceTree :=
  .round 1289 [(47, 1), (61, 1), (151, 1), (337, 1), (1289, 1)]

private theorem checked19_9 : replayAbundance bank 19 127 (10^300) 3 state19_9 tree19_9 = true := by
  decide +kernel

theorem reject19_9 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_9 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_9 checked19_9

@[expose] noncomputable def state19_10 : State := ⟨74658392342395891888849, 78892743884829086992299, 0⟩

private theorem checked19_10 : checkChildren bank 19 127 (10^300) state19_10 861001 [state19_1, state19_2, state19_3, state19_4, state19_5, state19_6, state19_7, state19_8, state19_9] = true := by
  decide +kernel

theorem reject19_10 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_10 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state19_1, state19_2, state19_3, state19_4, state19_5, state19_6, state19_7, state19_8, state19_9] ?_ checked19_10
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject19_1 ho hN hs hav hx hvalid
  · exact reject19_2 ho hN hs hav hx hvalid
  · exact reject19_3 ho hN hs hav hx hvalid
  · exact reject19_4 ho hN hs hav hx hvalid
  · exact reject19_5 ho hN hs hav hx hvalid
  · exact reject19_6 ho hN hs hav hx hvalid
  · exact reject19_7 ho hN hs hav hx hvalid
  · exact reject19_8 ho hN hs hav hx hvalid
  · exact reject19_9 ho hN hs hav hx hvalid

@[expose] noncomputable def state19_11 : State := ⟨51535454421076952186357165581763761, 54458357313454983589032535552443853, 0⟩

private noncomputable def tree19_11 : AbundanceTree :=
  .split 2249049650927341 [
    (1, .split 131500009 [
      (2, .abundant [(3, 2), (7, 2), (11, 2), (19, 4), (31, 2)]),
      (4, .split 382870671188157827422430098601 [
        (2, .split 679962044928252649182431611563359904446618797 [])]),
      (6, .split 87898016264279260245126586891 [
        (2, .round 1 [(229144693012555309178923, 1), (303756349794538078858327221241441, 1)])]),
      (10, .round 1 [(621301, 1), (975899, 1), (714219756551929, 1), (779246529699754723197032970319616880707346707, 1)]),
      (12, .round 1 [(11, 1), (31, 1), (53, 1), (59, 1), (131, 1), (151, 1), (144941, 1), (621301, 1), (161934001082889361, 1)])]),
    (2, .split 1631164874282493956886307 [
      (2, .abundant [(3, 2), (7, 2), (11, 2), (13, 1), (19, 4)]),
      (4, .round 1 [(21857819592558272327563854981168792289687791616901741825111, 1)])]),
    (4, .split 114805118873129581017471121 [
      (1, .split 27192117212962951448951 [
        (2, .round 1 [(2974952422915511, 1), (786539924244310894788466228441457484313, 1)])]),
      (2, .abundant [(3, 2), (5, 1), (7, 2)])]),
    (6, .round 1 [(150767034618663479416896464250963327749559821774318213288564997447087659, 1)])]

private theorem checked19_11 : replayAbundance bank 19 127 (10^300) 6 state19_11 tree19_11 = true := by
  decide +kernel

theorem reject19_11 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_11 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree19_11 checked19_11

@[expose] noncomputable def state19_12 : State := ⟨35574072506229221935790977969887474610809936529, 37591704068620135352656863761881796791705917359, 0⟩

private noncomputable def tree19_12 : AbundanceTree :=
  .split 2082791208222878694249997667 [
    (2, .split 211385809189542242314813187779978264040809 [
      (1, .split 1707892132096164194189328494626955353 []),
      (2, .round 1999981393 [(7723, 1), (157920029, 1), (1999981393, 1)])]),
    (4, .split 157920029 [
      (1, .abundant [(3, 4), (5, 2), (11, 2)])])]

private theorem checked19_12 : replayAbundance bank 19 127 (10^300) 5 state19_12 tree19_12 = true := by
  decide +kernel

theorem reject19_12 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_12 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree19_12 checked19_12

@[expose] noncomputable def state19_13 : State := ⟨16950735141396988012457644698286207691742168011837856431394022804361809, 17912118975677493633762806469057683475073554461725930493291174267901619, 0⟩

private noncomputable def tree19_13 : AbundanceTree :=
  .split 11043961981033833615628648328570335560660927963857564693 [
    (1, .split 69106810541612119451056863643153 [
      (2, .round 1 [(4585127602420298137, 1)])]),
    (2, .round 1 [(23, 1), (151, 1)])]

private theorem checked19_13 : replayAbundance bank 19 127 (10^300) 5 state19_13 tree19_13 = true := by
  decide +kernel

theorem reject19_13 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_13 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree19_13 checked19_13

@[expose] noncomputable def state19_14 : State := ⟨11700812338375862497680552590807886730231535793719728012861906660345355338160305201, 12364439711243736602826471948103139737500762713635210791539987182526172109049189333, 0⟩

private noncomputable def tree19_14 : AbundanceTree :=
  .split 202288034832782429143265224498632631807007915883251181123517081 [
    (1, .split 2196398878510367961182820571671822575493067387 [])]

private theorem checked19_14 : replayAbundance bank 19 127 (10^300) 4 state19_14 tree19_14 = true := by
  decide +kernel

theorem reject19_14 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_14 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_14 checked19_14

@[expose] noncomputable def state19_15 : State := ⟨5575334981741806439853650187517428147568474445547403174337144807491402172314010080874968475450563279553521, 5891547634316084430208502753094884102134019301916590945280153198782191299307927986042454652608625341821273, 0⟩

private noncomputable def tree19_15 : AbundanceTree :=
  .split 50645362436196135834421642283706575039296966047049 [
    (1, .round 1 [(219437, 1), (22812947, 1), (7801857533, 1), (616949907001, 1), (307940520066469, 1)])]

private theorem checked19_15 : replayAbundance bank 19 127 (10^300) 4 state19_15 tree19_15 = true := by
  decide +kernel

theorem reject19_15 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_15 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_15 checked19_15

@[expose] noncomputable def state19_16 : State := ⟨3848561599291598537364409188196526566434516668772584631404310212604803243004515856370539079897377035092025120781513169, 4066837967598226587152550452991757044054909521973163113432186458381486574354027091724029102639432596972224599842103739, 0⟩

private noncomputable def tree19_16 : AbundanceTree :=
  .round 1 [(183195940346164522720034039821182810727710514546819743139533127780231919503386084611711578219479628319, 1)]

private theorem checked19_16 : replayAbundance bank 19 127 (10^300) 3 state19_16 tree19_16 = true := by
  decide +kernel

theorem reject19_16 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_16 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_16 checked19_16

@[expose] noncomputable def state19_17 : State := ⟨1833806020761887977907931691126836506970401969253826755283090452768940322363308039982083196129423848117737746658007373341906769948059926223249, 1937812805651185949133384056643530714619182611678377375274611814353700117591889791049243329307713423021534046799282727224107772029722825649599, 0⟩

private noncomputable def tree19_17 : AbundanceTree :=
  .round 1 [(737163345907282629899470538990260446480100782275538685666168734927866521735632043641781499080704810735676126351, 1)]

private theorem checked19_17 : replayAbundance bank 19 127 (10^300) 3 state19_17 tree19_17 = true := by
  decide +kernel

theorem reject19_17 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_17 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_17 checked19_17

@[expose] noncomputable def state19_18 : State := ⟨108156134641, 114290218313, 0⟩

private theorem checked19_18 : checkChildren bank 19 127 (10^300) state19_18 830833 [state19_10, state19_11, state19_12, state19_13, state19_14, state19_15, state19_16, state19_17] = true := by
  decide +kernel

theorem reject19_18 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_18 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state19_10, state19_11, state19_12, state19_13, state19_14, state19_15, state19_16, state19_17] ?_ checked19_18
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject19_10 ho hN hs hav hx hvalid
  · exact reject19_11 ho hN hs hav hx hvalid
  · exact reject19_12 ho hN hs hav hx hvalid
  · exact reject19_13 ho hN hs hav hx hvalid
  · exact reject19_14 ho hN hs hav hx hvalid
  · exact reject19_15 ho hN hs hav hx hvalid
  · exact reject19_16 ho hN hs hav hx hvalid
  · exact reject19_17 ho hN hs hav hx hvalid

@[expose] noncomputable def state19_19 : State := ⟨89761047417393361, 94851852397998905, 0⟩

private noncomputable def tree19_19 : AbundanceTree :=
  .split 17884211 [
    (2, .split 45692145853819 [
      (2, .abundant [(3, 2), (5, 1), (7, 2)]),
      (4, .split 777223234256745831445688101300524172301 [
        (1, .abundant [(3, 2), (5, 2), (7, 2)]),
        (2, .split 3622746821 [
          (1, .abundant [(3, 2), (5, 2), (7, 2)]),
          (2, .round 1 [(976278071191, 1)])])]),
      (6, .split 254050636991997895906733798914269897988345735660515865883 [])]),
    (4, .split 781190727528010465434731 [
      (2, .split 6489279550305425562991591 [
        (2, .abundant [(3, 2), (5, 2), (7, 4)])]),
      (4, .round 1 [(188088558675259524374171, 1), (43899987687514715838099526814665751606971, 1)])]),
    (6, .split 24547825537410184611649747322405623 [
      (2, .abundant [(3, 2), (5, 1), (11, 2), (13, 1)])]),
    (10, .split 30732368782787916073467973909139899894719155870877415153189616863 []),
    (12, .split 1163762748420082000147218073246967844916182060168850374263 []),
    (16, .split 26465963820993187250427507375539662524523800297209689600092297319617543795725909381 []),
    (18, .round 1 [(368139992306044105118439310198196765470544649873523224829636021961998500309535615525499476452965718750427392251, 1)])]

private theorem checked19_19 : replayAbundance bank 19 127 (10^300) 7 state19_19 tree19_19 = true := by
  decide +kernel

theorem reject19_19 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_19 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree19_19 checked19_19

@[expose] noncomputable def state19_20 : State := ⟨74494578233690515554481, 78719544193999774692137, 0⟩

private noncomputable def tree19_20 : AbundanceTree :=
  .split 81750272028928231 [
    (2, .split 72211650019 [
      (2, .split 1100806923905162413 [
        (1, .split 25297495897 [
          (2, .split 30474442794477587167 [
            (2, .round 1 [(397, 1), (619, 1), (1279, 1), (1579, 1), (3919, 1), (35149, 1), (218527, 1), (14632890871, 1), (78990530206165427580716388661440901, 1)])]),
          (4, .split 92427500083358281 [
            (2, .abundant [(3, 4), (7, 2), (11, 4), (19, 4)])]),
          (6, .round 1 [(8185687548210551, 1), (145192550189071421664275960059577431605193, 1)])]),
        (2, .split 12704596693303 [
          (2, .split 491340344348448039871 [
            (2, .round 259858993 [(218527, 1), (39773329, 1), (259858993, 1), (14632890871, 1)])]),
          (4, .abundant [(3, 4), (7, 4), (11, 2), (19, 4)])]),
        (4, .split 326437931963948663648330930282169451620521011997231546134541 [])]),
      (4, .abundant [(3, 2), (7, 2), (11, 2), (19, 4), (31, 2)]),
      (6, .split 60167782489199647234151559619 [
        (2, .round 1 [(5431646152811794979666891, 1)])]),
      (10, .round 1 [(14632890871, 1)])]),
    (4, .split 782209595746475328977396664324121 [
      (1, .split 26767634247106306288401281 [
        (2, .round 1 [(690841, 1), (1251121, 1), (152524929943, 1), (4680594500779, 1)])]),
      (2, .abundant [(3, 2), (5, 1), (7, 2)])]),
    (6, .round 1 [(151750761447588720293053268145870171261507182101461829972687726842643168048810677709881038430743111, 1)])]

private theorem checked19_20 : replayAbundance bank 19 127 (10^300) 8 state19_20 tree19_20 = true := by
  decide +kernel

theorem reject19_20 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_20 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree19_20 checked19_20

@[expose] noncomputable def state19_21 : State := ⟨51309546191120492747734653837175921, 54219571205509518969816764696467721, 0⟩

private noncomputable def tree19_21 : AbundanceTree :=
  .split 247174661801 [
    (1, .split 50390258557 [
      (2, .split 17273320799263278781 [
        (2, .split 472319 [
          (2, .abundant [(3, 4), (7, 2), (13, 2), (19, 4), (67, 2)]),
          (4, .split 249329489131 [
            (2, .split 332142098321281 [
              (2, .round 1 [(366990261165935892257881, 1)])]),
            (4, .abundant [(3, 4), (5, 2), (7, 2)])]),
          (6, .split 308599047587209 [
            (2, .abundant [(3, 4), (7, 4), (19, 4), (29, 2), (31, 2), (43, 2)])]),
          (10, .abundant [(3, 4), (7, 2), (11, 2), (19, 4)]),
          (12, .round 1 [(291439, 1)])]),
        (4, .abundant [(3, 2), (5, 2), (7, 2)])]),
      (4, .split 30641495417399415391 [
        (2, .split 36373907685853466410249 [
          (2, .round 1 [(29270617029246916574037205073963831947051, 1)])]),
        (4, .round 1 [(507431, 1), (2044111, 1)])]),
      (6, .split 472319 [
        (2, .split 291439 [
          (2, .split 28312327387 [
            (2, .split 204296477131 [
              (2, .round 1 [(139394845309, 1)])])]),
          (4, .split 21156205819894285981 []),
          (6, .round 1 [(247087, 1), (37104826542068462501209607, 1)])]),
        (4, .split 249329489131 [
          (2, .round 1 [(287503, 1), (291439, 1), (61397681, 1), (332142098321281, 1)])]),
        (6, .round 1 [(673, 1), (1597, 1), (12097, 1), (141353, 1), (291439, 1), (13630919, 1), (308599047587209, 1)])]),
      (10, .round 1 [(10253, 1), (141353, 1), (291439, 1), (472319, 1)])]),
    (2, .split 459363258922450400191 [
      (2, .split 10733454434853919253303195449 [
        (1, .abundant [(3, 2), (5, 2), (7, 2)]),
        (2, .round 1 [(3308013439, 1), (7291972282900672203291015439286344574790522479491, 1)])]),
      (4, .round 4334148639238921 [(101153235616801, 1), (4334148639238921, 1), (1846625187349652327838164941696849027714651089055151, 1)])]),
    (4, .split 57710745113383297226474977257232621 [
      (1, .split 1779229148211379844573081 [
        (2, .round 1 [(2316843833, 1), (50390258557, 1), (3853148671712462588766392074111711, 1)])]),
      (2, .round 63854322413437693 [(50390258557, 1), (275036918797, 1), (63854322413437693, 1), (352112173455709225340181883434843763, 1)])]),
    (6, .split 20922295111122818557878561478088089 [
      (1, .round 1 [(472319, 1), (1724059, 1), (2170939, 1), (50390258557, 1), (396157790380625113, 1), (5555707680513559420665539399, 1)]),
      (2, .round 396157790380625113 [(50390258557, 1), (396157790380625113, 1)])]),
    (10, .round 50390258557 [(11, 1), (23, 1), (67, 1), (89, 1), (151, 1), (1277, 1), (472319, 1), (50390258557, 1)])]

private theorem checked19_21 : replayAbundance bank 19 127 (10^300) 9 state19_21 tree19_21 = true := by
  decide +kernel

theorem reject19_21 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_21 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 9 h tree19_21 checked19_21

@[expose] noncomputable def state19_22 : State := ⟨42582869884480910461692691647202877532241, 44997960754447665492949299173657312935673, 0⟩

private noncomputable def tree19_22 : AbundanceTree :=
  .split 1943777054011345723 [
    (2, .split 3571291902874676735926716043 [
      (2, .split 20092166804684214160509997457809566379 [])]),
    (4, .split 208101841737306154960647550795063137569172079150924556201 [
      (1, .abundant [(3, 2), (7, 2), (11, 2), (13, 2), (19, 4)])]),
    (6, .round 10165373 [(13, 1), (43, 1), (53, 1), (151, 1), (937, 1), (10165373, 1), (260670715787, 1)])]

private theorem checked19_22 : replayAbundance bank 19 127 (10^300) 5 state19_22 tree19_22 = true := by
  decide +kernel

theorem reject19_22 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_22 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree19_22 checked19_22

@[expose] noncomputable def state19_23 : State := ⟨29329755011621939339507511087599536716794405493976081, 30993194411997931559747907171135465604266153963335897, 0⟩

private noncomputable def tree19_23 : AbundanceTree :=
  .split 165543788931117927824524680022311579852222257 [
    (1, .split 88436838986645913478839283 [
      (2, .split 652799986546651832491665664009 [])]),
    (2, .round 1 [(621577855103779232020354854430799478674267898455633513341518743986760647186871128363, 1)])]

private theorem checked19_23 : replayAbundance bank 19 127 (10^300) 5 state19_23 tree19_23 = true := by
  decide +kernel

theorem reject19_23 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_23 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree19_23 checked19_23

@[expose] noncomputable def state19_24 : State := ⟨24341379609000291518583413109331695111538729801966123119601, 25721902899599735357997542867375916749758170763405816429769, 0⟩

private noncomputable def tree19_24 : AbundanceTree :=
  .split 101521630894179215518143149824759 [
    (2, .split 1065486730700418111449543508776899 [])]

private theorem checked19_24 : replayAbundance bank 19 127 (10^300) 4 state19_24 tree19_24 = true := by
  decide +kernel

theorem reject19_24 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_24 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_24 checked19_24

@[expose] noncomputable def state19_25 : State := ⟨16765584436032926668693185629702528219181212962661445073777798814289841, 17716445897718400175231607852826306406478936987637097634221082920549033, 0⟩

private noncomputable def tree19_25 : AbundanceTree :=
  .split 30757554438787917441772961957630399 [
    (2, .split 83219137714974604167614481212311786693 [
      (1, .round 1 [(15416661303255762165174968731439753, 1)])])]

private theorem checked19_25 : replayAbundance bank 19 127 (10^300) 5 state19_25 tree19_25 = true := by
  decide +kernel

theorem reject19_25 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_25 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree19_25 checked19_25

@[expose] noncomputable def state19_26 : State := ⟨9583606183221422001964087820078669164604671101872853896993600441404298627337635276773201, 10127141174104931358107193614202950668096206906818257450989536375240606100067705335428729, 0⟩

private noncomputable def tree19_26 : AbundanceTree :=
  .split 26127114714858722169201773992968871882310961393104909921297867 []

private theorem checked19_26 : replayAbundance bank 19 127 (10^300) 3 state19_26 tree19_26 = true := by
  decide +kernel

theorem reject19_26 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_26 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_26 checked19_26

@[expose] noncomputable def state19_27 : State := ⟨7953636027185305769292037727727509191757873245537420779046825871930696921098677606534891747121, 8404727130354338737651680231492927021417072132313515041982687018076059055174290079684471656041, 0⟩

private noncomputable def tree19_27 : AbundanceTree :=
  .split 505721798544031140740638061509529267073352657243267449823387256782461164389882661 [
    (1, .round 1 [(218633757381137623379043199093904270591, 1)])]

private theorem checked19_27 : replayAbundance bank 19 127 (10^300) 4 state19_27 tree19_27 = true := by
  decide +kernel

theorem reject19_27 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_27 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_27 checked19_27

@[expose] noncomputable def state19_28 : State := ⟨4546487222085889341011839020075066232502924468052030926350957744760613182039862714001088835838304538340172099281, 4804341608374724495036515111826052976496530807951571511145598923705045814181124194716167414568237234798638031417, 0⟩

private noncomputable def tree19_28 : AbundanceTree :=
  .split 2993975309016712531997471601605501121783934731157674241358537 [
    (1, .round 1 [(126918638983, 1), (4373689633189, 1)])]

private theorem checked19_28 : replayAbundance bank 19 127 (10^300) 4 state19_28 tree19_28 = true := by
  decide +kernel

theorem reject19_28 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_28 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_28 checked19_28

@[expose] noncomputable def state19_29 : State := ⟨3131478849335291576532910985615507807674022589577055366940218137123265799345555585189819194299871585672245252806595261272721, 3309080922634721421127031745468093839827518944862531617365989265757234264524495671417468752924912986742178828934149617714201, 0⟩

private noncomputable def tree19_29 : AbundanceTree :=
  .round 1 [(327078975744855777578480425202706797392129480442141810100414255440867674469321760645736634839, 1)]

private theorem checked19_29 : replayAbundance bank 19 127 (10^300) 3 state19_29 tree19_29 = true := by
  decide +kernel

theorem reject19_29 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_29 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_29 checked19_29

@[expose] noncomputable def state19_30 : State := ⟨2598880058119194520487770018093007855252632501564379367186392776579477875458662836816319935552543726252695452454502345830717885041, 2746275748393930636543167313230625907643494350239257102415999177426509618048433972118457084896196710870055795887858384883112863753, 0⟩

private noncomputable def tree19_30 : AbundanceTree :=
  .round 110837018922348171125729904495435656295404797717841256878004178442107081754189 [(208121, 1), (2641061, 1), (327694871751043121635724957386987097, 1), (110837018922348171125729904495435656295404797717841256878004178442107081754189, 1)]

private theorem checked19_30 : replayAbundance bank 19 127 (10^300) 3 state19_30 tree19_30 = true := by
  decide +kernel

theorem reject19_30 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_30 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_30 checked19_30

@[expose] noncomputable def state19_31 : State := ⟨1790027671127101796716501001668273077351862724733125235607784790847158994307406599975857475976451730214646514257344101373698450990810943800881, 1891549233606441381177432793789028325366411179633782081521174575375245629721101818001577891314167293718881611210091129733507060578114903283177, 0⟩

private noncomputable def tree19_31 : AbundanceTree :=
  .split 13750621423269977545797375664534485249208795949678921216923216430349049728637490407903242134865022017278746237742464286632890576385130257 []

private theorem checked19_31 : replayAbundance bank 19 127 (10^300) 3 state19_31 tree19_31 = true := by
  decide +kernel

theorem reject19_31 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_31 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_31 checked19_31

@[expose] noncomputable def state19_32 : State := ⟨130321, 137561, 0⟩

private theorem checked19_32 : checkChildren bank 19 127 (10^300) state19_32 911 [state19_18, state19_19, state19_20, state19_21, state19_22, state19_23, state19_24, state19_25, state19_26, state19_27, state19_28, state19_29, state19_30, state19_31] = true := by
  decide +kernel

theorem reject19_32 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_32 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state19_18, state19_19, state19_20, state19_21, state19_22, state19_23, state19_24, state19_25, state19_26, state19_27, state19_28, state19_29, state19_30, state19_31] ?_ checked19_32
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject19_18 ho hN hs hav hx hvalid
  · exact reject19_19 ho hN hs hav hx hvalid
  · exact reject19_20 ho hN hs hav hx hvalid
  · exact reject19_21 ho hN hs hav hx hvalid
  · exact reject19_22 ho hN hs hav hx hvalid
  · exact reject19_23 ho hN hs hav hx hvalid
  · exact reject19_24 ho hN hs hav hx hvalid
  · exact reject19_25 ho hN hs hav hx hvalid
  · exact reject19_26 ho hN hs hav hx hvalid
  · exact reject19_27 ho hN hs hav hx hvalid
  · exact reject19_28 ho hN hs hav hx hvalid
  · exact reject19_29 ho hN hs hav hx hvalid
  · exact reject19_30 ho hN hs hav hx hvalid
  · exact reject19_31 ho hN hs hav hx hvalid

@[expose] noncomputable def state19_33 : State := ⟨31757992979518465193623383215493881, 33550453372043855480390261512449678, 70841⟩

private noncomputable def tree19_33 : AbundanceTree :=
  .split 800281 [
    (2, .split 48071041 [
      (2, .split 1166323 [
        (2, .abundant [(3, 6), (7, 4), (13, 2), (19, 6), (163, 2)]),
        (4, .abundant [(3, 6), (7, 2), (11, 2), (13, 2)]),
        (6, .split 124633 [
          (2, .split 7493251 [
            (2, .split 2402910859 [
              (2, .abundant [(3, 8), (7, 2), (13, 2), (19, 6), (73, 2)]),
              (4, .abundant [(3, 8), (7, 2), (13, 2), (19, 6), (31, 2)]),
              (6, .round 1 [(7789, 1)])]),
            (4, .abundant [(3, 6), (5, 2), (7, 2)]),
            (6, .round 1 [(701, 1), (757, 1), (4441, 1), (177019756853596029005378891254877455170757, 1)])]),
          (4, .abundant [(3, 6), (7, 2), (11, 2), (13, 2)]),
          (6, .abundant [(3, 6), (7, 2), (13, 2), (19, 6), (29, 2)]),
          (10, .split 4441 [
            (2, .split 6575641 [
              (2, .abundant [(3, 8), (7, 4), (13, 2), (19, 6)])]),
            (4, .abundant [(3, 6), (5, 2), (7, 2)]),
            (6, .round 1 [(24750362743, 1)])]),
          (12, .abundant [(3, 6), (7, 2), (13, 2), (19, 6), (131, 2)])]),
        (10, .abundant [(3, 6), (7, 2), (13, 2), (19, 6), (23, 2)]),
        (12, .abundant [(3, 6), (7, 2), (13, 2), (19, 6), (79, 2)]),
        (16, .round 1 [(331, 1), (409, 1), (701, 1), (757, 1), (4441, 1), (124633, 1)])]),
      (4, .abundant [(3, 4), (5, 2), (7, 2)]),
      (6, .split 10845764513284237703204276099 [
        (2, .split 2255287399003668517 [
          (2, .abundant [(3, 6), (7, 2), (13, 2), (19, 6), (241, 2)])])]),
      (10, .abundant [(3, 4), (7, 2), (13, 2), (19, 6), (23, 2)]),
      (12, .split 4441 [
        (2, .abundant [(3, 6), (7, 2), (13, 2), (19, 6), (157, 2)]),
        (4, .abundant [(3, 4), (5, 2), (7, 2)]),
        (6, .round 1 [(119655719, 1), (24750362743, 1)])])]),
    (4, .abundant [(3, 4), (5, 2), (7, 2)]),
    (6, .split 596163019671514709 [
      (2, .split 163817803706156453053477 [
        (2, .abundant [(3, 4), (7, 2), (13, 2), (19, 6), (31, 2)])]),
      (4, .split 470149013261 [
        (2, .round 1 [(52051, 1), (31577156381537443266769, 1)])])]),
    (10, .split 7364813913742192593615769880129 [
      (2, .round 1 [(2445285268520744649835470098281930626599903916423099769, 1)])]),
    (12, .split 701 [
      (2, .split 492103 [
        (2, .split 163417 [
          (2, .split 2746609 [
            (4, .round 1 [(17471, 1), (1854991, 1), (16585171, 1), (105878551, 1)])]),
          (4, .abundant [(3, 4), (7, 2), (13, 4), (19, 6), (31, 2)]),
          (6, .round 1 [(4649, 1), (33048947, 1), (629220204475261337, 1)])]),
        (4, .split 13462149171001 [
          (2, .split 4356227321 [])]),
        (6, .abundant [(3, 4), (7, 2), (13, 4), (19, 6), (43, 2)])]),
      (4, .abundant [(3, 4), (5, 2), (7, 2)]),
      (6, .split 16975792017452101 [
        (2, .round 1 [(409, 1), (2018659771, 1), (8575358941, 1), (20032891183, 1)])]),
      (10, .abundant [(3, 4), (7, 2), (13, 4), (19, 6), (89, 2)]),
      (12, .split 62966051321959646638153131367 []),
      (16, .abundant [(3, 4), (7, 2), (13, 4), (19, 6), (137, 2)]),
      (18, .round 1 [(154225215596708939, 1)])]),
    (16, .split 25953493 [
      (2, .split 11549197141 [
        (2, .abundant [(3, 6), (7, 2), (13, 2), (19, 6), (37, 2)])]),
      (4, .abundant [(3, 4), (7, 2), (11, 2), (13, 2)])]),
    (18, .round 1 [(701, 1), (1747013, 1), (3091090109851, 1), (19783967018464547728931, 1)])]

private theorem checked19_33 : replayAbundance bank 19 127 (10^300) 9 state19_33 tree19_33 = true := by
  decide +kernel

theorem reject19_33 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_33 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 9 h tree19_33 checked19_33

@[expose] noncomputable def state19_34 : State := ⟨533591478201266328008686553733468305279681, 563708041025044856324755785178342843129878, 70841⟩

private noncomputable def tree19_34 : AbundanceTree :=
  .split 369023021 [
    (2, .split 794191 [
      (2, .split 684842713 [
        (2, .abundant [(3, 4), (7, 2), (13, 4), (19, 6), (73, 2)]),
        (4, .split 19731582134141 [
          (2, .split 1170911630593 [
            (4, .round 1 [(499796425710423124246308781673755341004789141, 1)])]),
          (4, .abundant [(3, 4), (5, 2), (11, 2)])]),
        (6, .split 3051934557618205300007 [
          (2, .round 1 [(31448020871, 1), (242965299753278998099, 1)])]),
        (10, .round 1 [(1149986550472855579648408239822856912298581122489969299470029337872846236797481461, 1)])]),
      (4, .abundant [(3, 2), (5, 2), (13, 4), (19, 6)]),
      (6, .split 558861218182531732008656297142353 [
        (2, .round 1 [(11836657945248868823719972077308659037688015473418294247, 1)])]),
      (10, .split 1489962562289489012597493331592337055839049922263678324283 []),
      (12, .round 1 [(51949, 1), (56629, 1), (101323, 1), (765181, 1), (4589566181929, 1), (1478845714767861414511012765881554982553, 1)]),
      (16, .round 1 [(103, 1), (331, 1), (409, 1), (487, 1), (577, 1), (643, 1), (701, 1), (765181, 1)]),
      (18, .round 1 [(765181, 1)])]),
    (4, .abundant [(3, 2), (5, 2), (11, 2), (13, 2)]),
    (6, .split 2525345248777555834735270389700098944681903308737427 []),
    (10, .round 1 [(4370521, 1), (7457254718534088640217, 1), (407224223745777739427669509897906954434418411219, 1)]),
    (12, .round 1 [(79, 1), (157, 1), (331, 1), (409, 1), (521, 1), (701, 1), (1847, 1), (765181, 1), (6500993481529, 1)])]

private theorem checked19_34 : replayAbundance bank 19 127 (10^300) 8 state19_34 tree19_34 = true := by
  decide +kernel

theorem reject19_34 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_34 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree19_34 checked19_34

@[expose] noncomputable def state19_35 : State := ⟨8965297832033514791202677747205541505116449505481, 9471310327402639700227171346644474868246758170078, 70841⟩

private noncomputable def tree19_35 : AbundanceTree :=
  .split 16883681631285687821 [
    (2, .split 6275014246887639436149602673397 [
      (2, .round 1 [(701, 1), (9391, 1), (10541359, 1), (25902229, 1), (45427579, 1), (457088476683403, 1), (861427970872444305124839871, 1)])]),
    (4, .abundant [(3, 2), (5, 2), (11, 2), (13, 2)]),
    (6, .round 1 [(89891479350266864602383095145463762293575043317013438194085498298938853040210282487615587060188415556052921, 1)])]

private theorem checked19_35 : replayAbundance bank 19 127 (10^300) 5 state19_35 tree19_35 = true := by
  decide +kernel

theorem reject19_35 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_35 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree19_35 checked19_35

@[expose] noncomputable def state19_36 : State := ⟨2530908211639876771251453299991212075174132354742973047469277081, 2673755800611900990643410179652800473059830682353411248133330478, 70841⟩

private noncomputable def tree19_36 : AbundanceTree :=
  .split 1339322446256468156596004408950229501 [
    (2, .split 6540509344391624373706394495239741 [])]

private theorem checked19_36 : replayAbundance bank 19 127 (10^300) 4 state19_36 tree19_36 = true := by
  decide +kernel

theorem reject19_36 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_36 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_36 checked19_36

@[expose] noncomputable def state19_37 : State := ⟨42523816121239093175089439307245647035872812172052839291942347128822881, 44923912884476838676493439799900602641065321251866706671206044489450678, 70841⟩

private noncomputable def tree19_37 : AbundanceTree :=
  .split 26715048700768676096790397 [
    (2, .split 208406906275196481119886147216353300372753167 [])]

private theorem checked19_37 : replayAbundance bank 19 127 (10^300) 4 state19_37 tree19_37 = true := by
  decide +kernel

theorem reject19_37 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_37 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_37 checked19_37

@[expose] noncomputable def state19_38 : State := ⟨12004495269188048366393247304184754786012500471650937532536346516239673759128707234481, 12682043825924717781680400710455419182919651267850606638272118429419258635943778771078, 70841⟩

private noncomputable def tree19_38 : AbundanceTree :=
  .split 23209434928687323399695305315125991 [
    (2, .split 2005553791141 [
      (2, .round 1 [(1340748669720681134624341, 1)])])]

private theorem checked19_38 : replayAbundance bank 19 127 (10^300) 5 state19_38 tree19_38 = true := by
  decide +kernel

theorem reject19_38 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_38 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree19_38 checked19_38

@[expose] noncomputable def state19_39 : State := ⟨201697140618339020230514428948698717148379616437085193885106719432902266805802472341010100281, 213081176636465749148955538337330572482998579591823590465527125884568199647867726304007971278, 70841⟩

private noncomputable def tree19_39 : AbundanceTree :=
  .split 1315793702897003456684038437256526454475356179683 []

private theorem checked19_39 : replayAbundance bank 19 127 (10^300) 3 state19_39 tree19_39 = true := by
  decide +kernel

theorem reject19_39 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_39 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_39 checked19_39

@[expose] noncomputable def state19_40 : State := ⟨56939207042433573996780078043145188155076800769161424575667178257645450917163494915584650739886506603151881, 60152926294116919092775851781494243771436308523268953711632960589519845644440069230622277223022656875451678, 70841⟩

private noncomputable def tree19_40 : AbundanceTree :=
  .split 30131459415734311915773538164664219704704072363381540078544825047249013708964901 []

private theorem checked19_40 : replayAbundance bank 19 127 (10^300) 3 state19_40 tree19_40 = true := by
  decide +kernel

theorem reject19_40 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_40 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_40 checked19_40

@[expose] noncomputable def state19_41 : State := ⟨270071604504901620022389854085704573386346921630392092525939835279151081249041633785536084512815925541729156955556278809341029281, 285314779810865933142199346244125252290203743424244854813054799906542822531522203905622098087673531087445735918999091452919372278, 70841⟩

private noncomputable def tree19_41 : AbundanceTree :=
  .round 1 [(2422343149966398363656897666702471278107242490941797790578985742543137777648730987956589111118401739, 1)]

private theorem checked19_41 : replayAbundance bank 19 127 (10^300) 3 state19_41 tree19_41 = true := by
  decide +kernel

theorem reject19_41 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_41 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_41 checked19_41

@[expose] noncomputable def state19_42 : State := ⟨4537689354642060544193809872767045186827297094196443490594428450333075916081228971579453970303515130582950491065022440855064915114535081, 4793802152740987046334538117923889908054797546469220625842838950124551102152952297103685273271571222298585038242845332981660366390732478, 70841⟩

private noncomputable def tree19_42 : AbundanceTree :=
  .round 1 [(13118744817454561559022413109165078253672629509672489016560293, 1)]

private theorem checked19_42 : replayAbundance bank 19 127 (10^300) 3 state19_42 tree19_42 = true := by
  decide +kernel

theorem reject19_42 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_42 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_42 checked19_42

@[expose] noncomputable def state19_43 : State := ⟨21522973508213701577563958555269016312020412493899213748427441625363653587893187962146840544596418568127901212704044077872973541205615038317499653367705692481, 22737756746506244066744329861236375286542914528485165476446575498577455975961479996158164880262662453914731351189862974511916801329712415964452378004246973078, 70841⟩

private noncomputable def tree19_43 : AbundanceTree :=
  .round 1 [(1111967065035291754495968792865341702722332441, 1)]

private theorem checked19_43 : replayAbundance bank 19 127 (10^300) 3 state19_43 tree19_43 = true := by
  decide +kernel

theorem reject19_43 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_43 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_43 checked19_43

@[expose] noncomputable def state19_44 : State := ⟨1890154095951884276788148081, 1996349578165660709318129478, 70841⟩

private theorem checked19_44 : checkChildren bank 19 127 (10^300) state19_44 4099 [state19_33, state19_34, state19_35, state19_36, state19_37, state19_38, state19_39, state19_40, state19_41, state19_42, state19_43] = true := by
  decide +kernel

theorem reject19_44 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_44 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state19_33, state19_34, state19_35, state19_36, state19_37, state19_38, state19_39, state19_40, state19_41, state19_42, state19_43] ?_ checked19_44
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject19_33 ho hN hs hav hx hvalid
  · exact reject19_34 ho hN hs hav hx hvalid
  · exact reject19_35 ho hN hs hav hx hvalid
  · exact reject19_36 ho hN hs hav hx hvalid
  · exact reject19_37 ho hN hs hav hx hvalid
  · exact reject19_38 ho hN hs hav hx hvalid
  · exact reject19_39 ho hN hs hav hx hvalid
  · exact reject19_40 ho hN hs hav hx hvalid
  · exact reject19_41 ho hN hs hav hx hvalid
  · exact reject19_42 ho hN hs hav hx hvalid
  · exact reject19_43 ho hN hs hav hx hvalid

@[expose] noncomputable def state19_45 : State := ⟨7689693116865995332530178168303409, 8121727029995759211951428600376714, 70841⟩

private noncomputable def tree19_45 : AbundanceTree :=
  .split 617341 [
    (2, .abundant [(3, 2), (7, 2), (11, 2), (13, 2), (19, 6)]),
    (4, .abundant [(3, 2), (5, 2), (11, 2), (13, 2)]),
    (6, .split 75936731906816833044936424699 [
      (2, .split 24330747901636175766781709209550533062052386631957104073 [])]),
    (10, .split 936010009756428524564143157 [
      (2, .round 1 [(42168367, 1), (45175567, 1), (1346733637, 1), (3033826866533, 1), (1882271111361815343907831, 1)])]),
    (12, .split 216367925343300049320216818660636098604857033 []),
    (16, .split 451811287665190564204675720224179 []),
    (18, .round 1 [(55605260707481080611167213932854509241832150277687435597331270169278275138249829868221460100854619, 1)])]

private theorem checked19_45 : replayAbundance bank 19 127 (10^300) 5 state19_45 tree19_45 = true := by
  decide +kernel

theorem reject19_45 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_45 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree19_45 checked19_45

@[expose] noncomputable def state19_46 : State := ⟨31283893920721643285383866010148907497201, 33041532737134418238392236009482925875918, 70841⟩

private noncomputable def tree19_46 : AbundanceTree :=
  .split 1727870509 [
    (2, .split 192062921 [
      (2, .split 1781434578409 [
        (2, .abundant [(3, 4), (7, 2), (13, 2), (19, 6), (29, 2)]),
        (4, .abundant [(3, 2), (7, 2), (13, 2), (19, 6), (29, 2), (101, 2)]),
        (6, .split 49936897 [
          (2, .abundant [(3, 4), (7, 2), (13, 2), (19, 6), (29, 2)])])]),
      (4, .abundant [(3, 2), (5, 2), (7, 2)]),
      (6, .split 33984484323298183190021365274475669834016030051 []),
      (10, .abundant [(3, 2), (7, 2), (13, 2), (19, 6), (23, 2)]),
      (12, .round 1 [(925669, 1), (49936897, 1)])]),
    (4, .abundant [(3, 2), (7, 2), (13, 2), (19, 6), (29, 2), (71, 2)]),
    (6, .abundant [(3, 2), (7, 2), (13, 2), (19, 6), (29, 2), (43, 2)]),
    (10, .round 1 [(1593338139722132805740923010892188253377430022436070734856393560918068943504583129583, 1)]),
    (12, .abundant [(3, 2), (7, 2), (13, 4), (19, 6), (29, 2), (157, 2)])]

private theorem checked19_46 : replayAbundance bank 19 127 (10^300) 7 state19_46 tree19_46 = true := by
  decide +kernel

theorem reject19_46 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_46 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree19_46 checked19_46

@[expose] noncomputable def state19_47 : State := ⟨517778958307681756027278159332565454382401103197828721, 546869595098281135730244855184149010334241509434051158, 70841⟩

private noncomputable def tree19_47 : AbundanceTree :=
  .split 4419297420801248089593523 [
    (2, .split 97908418174954417469206813 [
      (2, .round 1 [(66491353374067371278827, 1), (571204451690878910471369512289401, 1)])]),
    (4, .split 903518491 [
      (2, .round 1 [(1144863931, 1)])])]

private theorem checked19_47 : replayAbundance bank 19 127 (10^300) 5 state19_47 tree19_47 = true := by
  decide +kernel

theorem reject19_47 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_47 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree19_47 checked19_47

@[expose] noncomputable def state19_48 : State := ⟨2106474440514600303546459435552923379843924201727591409528369, 2224823558172791063398862111652266394093442626674231495982234, 70841⟩

private noncomputable def tree19_48 : AbundanceTree :=
  .split 620920889070785392502066473873 [
    (2, .split 23415065069707640204392947799864167443670942372487 [])]

private theorem checked19_48 : replayAbundance bank 19 127 (10^300) 4 state19_48 tree19_48 = true := by
  decide +kernel

theorem reject19_48 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_48 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_48 checked19_48

@[expose] noncomputable def state19_49 : State := ⟨34864206619399218421648285686978052961616714445185672806996747721618083249, 36822999952894760657216147517794314151578645910141618416243655603703733794, 70841⟩

private noncomputable def tree19_49 : AbundanceTree :=
  .split 7201784514979903734932941 [
    (2, .split 72008214963608854098577 [
      (2, .round 1 [(67412764337119, 1), (2654131923811478107, 1)])])]

private theorem checked19_49 : replayAbundance bank 19 127 (10^300) 5 state19_49 tree19_49 = true := by
  decide +kernel

theorem reject19_49 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_49 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree19_49 checked19_49

@[expose] noncomputable def state19_50 : State := ⟨141837668283429026913389082529190256105162701593489975638303991791633910282990961, 149806605655362272939385223569019912525411737791124134645991246982836544397512038, 70841⟩

private noncomputable def tree19_50 : AbundanceTree :=
  .split 4892384286715651501694143544939 [
    (2, .round 1 [(544807, 1), (12570541, 1), (389916367, 1), (8056011857, 1), (3247924032880777432414313552509, 1)])]

private theorem checked19_50 : replayAbundance bank 19 127 (10^300) 4 state19_50 tree19_50 = true := by
  decide +kernel

theorem reject19_50 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_50 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_50 checked19_50

@[expose] noncomputable def state19_51 : State := ⟨2347551756782401789580529808717015349834482481135068033751007259874739261331790867511915197681, 2479445443089965225534584722403760569400442058647532814976650765207564197096016561276334909678, 70841⟩

private noncomputable def tree19_51 : AbundanceTree :=
  .split 30507407889862761518086187727811537 [
    (2, .round 1 [(113332236855837843555161, 1)])]

private theorem checked19_51 : replayAbundance bank 19 127 (10^300) 4 state19_51 tree19_51 = true := by
  decide +kernel

theorem reject19_51 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_51 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_51 checked19_51

@[expose] noncomputable def state19_52 : State := ⟨158070404725794007295515502451434809449288336139818148074321348419974463290674311773406202952217208004779253181489, 166951354129861159624621994574535346837422336473257996592869135664413715069973528904366700502831656784835169151674, 70841⟩

private noncomputable def tree19_52 : AbundanceTree :=
  .round 1 [(6607709210461, 1), (358339387953089, 1), (2826174187466546475451998889679877975135327618860939618711867, 1)]

private theorem checked19_52 : replayAbundance bank 19 127 (10^300) 3 state19_52 tree19_52 = true := by
  decide +kernel

theorem reject19_52 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_52 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_52 checked19_52

@[expose] noncomputable def state19_53 : State := ⟨643076088771495776146265467952645269499635795745924633811132724242149489286354105170318948002272792936555383146466702321, 679206357541618727228093789685641831649870079828454301700806983063042008468307537932817099621965487911090785757839119358, 70841⟩

private noncomputable def tree19_53 : AbundanceTree :=
  .round 1 [(1112190585151, 1), (2739084071010530819900447, 1), (742284670612540681657676750660567614709418373, 1)]

private theorem checked19_53 : replayAbundance bank 19 127 (10^300) 3 state19_53 tree19_53 = true := by
  decide +kernel

theorem reject19_53 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_53 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_53 checked19_53

@[expose] noncomputable def state19_54 : State := ⟨43300982535488860275744469879627699650477671327214413286411341332553724356949792574202635102219236214472537435259641734462148272636592761649, 45733783512440621557572444910322043930827849559869749638579204289907640844402177818467011541226539744832859180220439428871677909040299739594, 70841⟩

private noncomputable def tree19_54 : AbundanceTree :=
  .round 1 [(625808471269831187227606816830703048065254931755625985748026113024771874870254225971245310897335049050089162240175889, 1)]

private theorem checked19_54 : replayAbundance bank 19 127 (10^300) 3 state19_54 tree19_54 = true := by
  decide +kernel

theorem reject19_54 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_54 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_54 checked19_54

@[expose] noncomputable def state19_55 : State := ⟨716673496200352792337518450282743778445770472447700244336518601274972782521318909680354026658532380551930242346158628305291279087207591643638621361982129, 756938725292618436908344703011648815140942253487504318814668695414005941553978222682578396733706708120884939927723409854478353833459420575969470559638354, 70841⟩

private noncomputable def tree19_55 : AbundanceTree :=
  .round 1 [(163731241329494411911333, 1)]

private theorem checked19_55 : replayAbundance bank 19 127 (10^300) 3 state19_55 tree19_55 = true := by
  decide +kernel

theorem reject19_55 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_55 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_55 checked19_55

end OddPerfect.IndexComponent.Size300
