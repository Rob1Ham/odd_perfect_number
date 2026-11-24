module

public import OddPerfect.SizeIndex300.Seed13Part01

public section

namespace OddPerfect.IndexComponent.Size300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def state13_46 : State := ⟨23298085122481, 25239592216021, 0⟩

private noncomputable def tree13_46 : AbundanceTree :=
  .split 1803647 [
    (4, .split 4803254465101 [
      (1, .split 53738676221 [
        (4, .split 519211189523980856872429785652927511 []),
        (6, .split 642661823 [
          (2, .split 2401511401 []),
          (4, .round 1 [(3001, 1), (23321, 1), (42061, 1), (264031, 1), (403331, 1), (1096741684364621, 1)]),
          (6, .round 1 [(36388491333260552829602617, 1)])]),
        (10, .round 1 [(264031, 1), (642661823, 1)])]),
      (2, .split 53738676221 [
        (4, .split 519211189523980856872429785652927511 []),
        (6, .split 22095845017 [
          (1, .split 849840193 [
            (2, .round 1 [(151, 1), (281, 1), (1753, 1), (2719, 1), (9697, 1), (87421, 1), (264031, 1), (4690303, 1), (29279959, 1)])]),
          (2, .split 6341188605733 [
            (1, .round 1 [(7411, 1), (9697, 1), (87421, 1), (264031, 1), (1586699, 1), (1998233, 1)])])])])]),
    (6, .split 5826213364117301 [
      (1, .split 327668647153 [
        (2, .split 4771219052011060021 [
          (4, .abundant [(3, 4), (5, 2), (13, 12)])]),
        (4, .split 1117871311 [
          (4, .abundant [(3, 2), (5, 2), (13, 12), (41, 2), (53, 2)]),
          (6, .round 1 [(763296630708601148561021866841513592130942007993, 1)])])]),
      (2, .split 4686878224900426723549 [
        (1, .split 327668647153 [
          (2, .abundant [(3, 2), (5, 2), (13, 12), (53, 2), (97, 2), (191, 2)]),
          (4, .round 1 [(53, 1), (71, 1), (97, 1), (191, 1), (787, 1), (881, 1), (4201, 1), (8737, 1), (94873, 1), (264031, 1), (2064077, 1), (48797669, 1), (10057295749, 1)])]),
        (4, .round 327668647153 [(2064077, 1), (327668647153, 1)])])]),
    (10, .split 67608625137565252245903509 [
      (2, .split 1133381153729685128482914690160658458857506566927 [])]),
    (12, .split 7951186635606231688370736884287359758076217547543 []),
    (16, .split 4560798544018227994993268812202073557 []),
    (18, .round 1 [(668736191098237671448882782357037347132625069457269951930516188304389730146500305497599663, 1)]),
    (22, .round 1 [(264031, 1)])]

private theorem checked13_46 : replayAbundance bank 13 5759831 (10^300) 8 state13_46 tree13_46 = true := by
  decide +kernel

theorem reject13_46 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_46 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree13_46 checked13_46

@[expose] noncomputable def state13_47 : State := ⟨665416609183179841, 720867993281778161, 0⟩

private noncomputable def tree13_47 : AbundanceTree :=
  .split 15798461357509 [
    (1, .split 77477 [
      (2, .split 114769 [
        (4, .split 43268024731 [
          (2, .abundant [(3, 2), (5, 2), (13, 16), (41, 2), (73, 2)]),
          (10, .round 1 [(97802791, 1)])]),
        (6, .split 950274111010589 [
          (2, .split 1493913401 [
            (2, .split 60476569 [
              (2, .abundant [(3, 2), (5, 2), (13, 16), (29, 2)]),
              (6, .round 1 [(231867787946768243547410811561457056731425381, 1)])]),
            (4, .split 235247028860563935891219211 [])]),
          (4, .split 1493913401 [
            (2, .split 60476569 [
              (2, .abundant [(3, 2), (5, 2), (13, 16), (29, 2)])]),
            (4, .round 1 [(235247028860563935891219211, 1)])])]),
        (10, .split 2228968720571955116349765042113017788551 [
          (2, .round 1 [(277, 1), (337, 1), (443, 1), (727, 1), (21487, 1), (228251, 1), (779351, 1)])]),
        (12, .split 21487 [
          (6, .split 1386170227401701013826247 [
            (2, .round 1 [(44122422037773592008054341724037300181623, 1)])]),
          (10, .round 1 [(4754461695327763, 1), (4412418511423122567342488459, 1)]),
          (12, .round 1 [(46569218204428000087788199869629073416951, 1)])]),
        (16, .split 21487 [
          (6, .round 1 [(103, 1), (193, 1), (271, 1), (443, 1), (1386170227401701013826247, 1)])]),
        (18, .split 21487 [
          (6, .round 1 [(1386170227401701013826247, 1)])]),
        (22, .round 1 [(271, 1), (443, 1), (461, 1), (12007, 1), (20149, 1), (21487, 1)])]),
      (10, .split 21487 [
        (6, .split 1386170227401701013826247 [
          (2, .round 1 [(44122422037773592008054341724037300181623, 1)])]),
        (10, .split 4412418511423122567342488459 []),
        (12, .split 46569218204428000087788199869629073416951 []),
        (16, .round 1 [(150909918630184620367911994983897007674067181267502653410621, 1)]),
        (18, .round 1 [(100079192780973336580578975342295627, 1)])]),
      (12, .split 46419313456592907636857201777405071452546406811377 []),
      (16, .split 21487 [
        (6, .split 1386170227401701013826247 []),
        (10, .round 1 [(4412418511423122567342488459, 1)]),
        (12, .round 1 [(46569218204428000087788199869629073416951, 1)])]),
      (18, .split 21487 [
        (6, .split 1386170227401701013826247 [])]),
      (22, .split 21487 [])]),
    (2, .split 83197127088240304524014197 [
      (1, .split 150019243780639 [
        (4, .split 943524951901650772200785844845092320491 []),
        (6, .round 1 [(7062035822770696632302912966443667681160568837137517421989447, 1)])]),
      (4, .split 1535874355681 [
        (1, .split 11461748923 []),
        (2, .round 1 [(15167446089487, 1)])])]),
    (4, .split 571751846490414760931925846757021 [
      (1, .split 43424993500692386209987 [
        (2, .round 1 [(373, 1), (443, 1), (547, 1), (661, 1), (9221, 1), (26701, 1), (3287587, 1), (288197171658101, 1), (26887494615082083112320450168555667, 1)])])]),
    (6, .split 8013701793031740679104448685874912251261320627440757702964056013 [
      (1, .round 1 [(37721054831691908297617861, 1), (1220956244111245455703580956465386301, 1)])]),
    (10, .round 1 [(103, 1), (443, 1), (1094522287, 1)])]

private theorem checked13_47 : replayAbundance bank 13 5759831 (10^300) 9 state13_47 tree13_47 = true := by
  decide +kernel

theorem reject13_47 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_47 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 9 h tree13_47 checked13_47

@[expose] noncomputable def state13_48 : State := ⟨112455406951957393129, 121826690864620509223, 0⟩

private noncomputable def tree13_48 : AbundanceTree :=
  .split 9468940004449 [
    (1, .split 12865927 [
      (4, .split 1250413 [
        (2, .abundant [(3, 2), (5, 2), (13, 18), (17, 2)]),
        (4, .split 4173935346453624551 [
          (4, .round 1 [(2387795576775944733610342335138191971, 1)])]),
        (6, .split 73340030785269557 [
          (2, .split 5378760115584286426921727936245807 []),
          (4, .round 1 [(7290745991057487777017992825429341709445011231, 1)])]),
        (10, .split 972702693318769601 [
          (2, .round 1 [(78229527050009149, 1), (399923780800757489841199, 1)])]),
        (12, .round 1 [(39294891169, 1), (237479082467754559684099752568103065896607562707, 1)]),
        (16, .round 1 [(644065671719077187141459312861, 1)])]),
      (6, .split 1250413 [
        (2, .abundant [(3, 2), (5, 2), (13, 18), (17, 2)]),
        (4, .split 4173935346453624551 []),
        (6, .split 73340030785269557 [
          (2, .round 1 [(1933, 1), (7048567, 1), (83513081, 1), (5378760115584286426921727936245807, 1)])]),
        (10, .round 1 [(28653090269, 1), (2781059109643, 1), (78229527050009149, 1), (972702693318769601, 1)]),
        (12, .round 1 [(237479082467754559684099752568103065896607562707, 1)])]),
      (10, .split 1250413 [
        (2, .abundant [(3, 2), (5, 2), (13, 18), (17, 2)]),
        (4, .split 4173935346453624551 []),
        (6, .round 1 [(71, 1), (151, 1), (683, 1), (1783, 1), (2113, 1), (7048567, 1), (83513081, 1), (73340030785269557, 1)])]),
      (12, .split 1250413 [
        (2, .abundant [(3, 2), (5, 2), (13, 18), (17, 2)]),
        (4, .split 4173935346453624551 []),
        (6, .round 1 [(73340030785269557, 1)])]),
      (16, .split 1250413 [
        (2, .abundant [(3, 2), (5, 2), (13, 18), (17, 2)])])]),
    (4, .split 12024735984722311807613551 [
      (2, .split 2763176737607744574249063619094427721429447657 [
        (1, .round 1 [(733857154621666697260741, 1), (3209464745430699310951969687, 1)])])]),
    (6, .split 94991159353457389383372467776842251186731 []),
    (10, .round 1814693 [(353, 1), (26951, 1), (1814693, 1), (12865927, 1)])]

private theorem checked13_48 : replayAbundance bank 13 5759831 (10^300) 7 state13_48 tree13_48 = true := by
  decide +kernel

theorem reject13_48 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_48 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree13_48 checked13_48

@[expose] noncomputable def state13_49 : State := ⟨3211838877954855105157369, 3479492117784426363920483, 0⟩

private noncomputable def tree13_49 : AbundanceTree :=
  .split 2519545342349331183143 [
    (6, .split 637337 [
      (1, .round 1 [(1381, 1), (8171, 1), (12517, 1)])])]

private theorem checked13_49 : replayAbundance bank 13 5759831 (10^300) 5 state13_49 tree13_49 = true := by
  decide +kernel

theorem reject13_49 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_49 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree13_49 checked13_49

@[expose] noncomputable def state13_50 : State := ⟨15502932802662396215269535105521, 16794843869550929233208663030981, 0⟩

private noncomputable def tree13_50 : AbundanceTree :=
  .split 846041103974872866961 [
    (2, .split 2959025653654433029 [
      (1, .split 79236309623407 [
        (2, .split 56562096961590090040287487 [
          (2, .abundant [(3, 4), (5, 2), (13, 28)])]),
        (4, .split 20305777 []),
        (6, .round 1 [(5755419536401637361591771958576685291587629097065062981939719805409899032578218899, 1)])]),
      (4, .round 1 [(110938526418773344364482949384423460298063454771, 1)])]),
    (4, .split 65314594964594366010664953641121076145251 []),
    (6, .round 1973 [(1709, 1), (1973, 1), (2843, 1), (3539, 1)])]

private theorem checked13_50 : replayAbundance bank 13 5759831 (10^300) 7 state13_50 tree13_50 = true := by
  decide +kernel

theorem reject13_50 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_50 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree13_50 checked13_50

@[expose] noncomputable def state13_51 : State := ⟨2619995643649944960380551432833049, 2838328613954107040412264052235803, 0⟩

private noncomputable def tree13_51 : AbundanceTree :=
  .split 8170509011431363408568150369 [
    (1, .split 10601825698977984621911 [
      (4, .split 331841 [
        (2, .split 322459 [])])]),
    (2, .split 1117 [
      (1, .split 311 [
        (6, .split 232096537 [
          (2, .split 17956267573162969 [])]),
        (10, .split 369211100186859029135807 [
          (2, .round 1 [(136316836501190855419243369696076556180278677057, 1)])]),
        (12, .split 195006165968459 []),
        (16, .split 1960979995560857679344089 []),
        (18, .split 2045700044378558987157448951 []),
        (22, .round 1 [(205368060708076529554328672621790229394318528413, 1)]),
        (28, .round 1 [(77232161282416184921572788668498253578610346849, 1)])]),
      (4, .split 457421 [
        (2, .split 1909021 [
          (1, .split 8447 [
            (4, .split 3180314445761 [
              (2, .round 1 [(251, 1), (271, 1), (311, 1), (331, 1), (1601, 1), (8431, 1), (61051, 1), (399451777, 1), (414746743129, 1)])]),
            (6, .split 2356264653172291 []),
            (10, .round 1 [(171007, 1), (269282504108399, 1), (610391728348403, 1)]),
            (12, .round 1 [(14750021001352890739789577, 1)])]),
          (6, .round 1 [(331, 1), (8431, 1), (48402128744050308842922221506363743427, 1)])]),
        (6, .split 402459644582699528483 [
          (2, .round 1 [(53995274886780071575086215090971, 1)])]),
        (10, .round 7431137157045977 [(140084304076289, 1), (7431137157045977, 1), (122575031587791311, 1)])]),
      (6, .split 1944052625982187267 [
        (2, .split 253514958703 [
          (2, .round 1 [(584398351, 1), (9023174851, 1), (323602414939, 1)])])]),
      (10, .split 2713299004769 [
        (1, .abundant [(3, 2), (5, 2), (13, 30), (17, 2)]),
        (2, .split 229424148128117397979 []),
        (4, .round 1 [(352536911, 1)])]),
      (12, .split 19613956318561686222919207 [
        (2, .round 1 [(7909103848783, 1)])]),
      (16, .split 105096236484133465538099023002928838982262531 []),
      (18, .round 1 [(412116160123267, 1), (3332206185083623, 1), (5340655735545636352071067, 1)]),
      (22, .round 1 [(129473674248554602393735504326838249522076852921265394727, 1)])]),
    (4, .split 1117 [
      (1, .split 311 [
        (6, .round 1 [(19853, 1), (232096537, 1)])]),
      (4, .split 457421 [
        (2, .round 1 [(8431, 1)])]),
      (6, .round 1 [(1944052625982187267, 1)])])]

private theorem checked13_51 : replayAbundance bank 13 5759831 (10^300) 9 state13_51 tree13_51 = true := by
  decide +kernel

theorem reject13_51 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_51 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 9 h tree13_51 checked13_51

@[expose] noncomputable def state13_52 : State := ⟨12646218552730347184269489080961456410641, 13700070098791209449625279837708244444861, 0⟩

private noncomputable def tree13_52 : AbundanceTree :=
  .split 31964044249933 [
    (1, .split 4287755796749 [
      (2, .split 189396382956961 [
        (2, .split 29440087660920247 [
          (2, .round 1 [(463, 1), (827, 1), (1481, 1), (181123, 1), (2242381, 1), (16127389, 1), (217138189, 1), (67495678093, 1), (288906253827556203246212851820419, 1)])]),
        (6, .round 1 [(217138189, 1), (67495678093, 1)])]),
      (4, .split 67495678093 [
        (4, .round 1 [(585061, 1), (8136281, 1), (29718701, 1), (217138189, 1), (11424786747881443421, 1)])]),
      (6, .split 67495678093 [])]),
    (2, .split 2589447375480485612221 [
      (1, .split 4287755796749 [
        (2, .split 189396382956961 [
          (2, .split 29440087660920247 [
            (2, .round 1 [(288906253827556203246212851820419, 1)])])]),
        (4, .split 67495678093 []),
        (6, .round 1 [(56836159529, 1), (67495678093, 1)])]),
      (2, .split 37228460788097252101 []),
      (4, .round 10109399487240966566165404578297904544256598573003131834172351523160807416981 [(1481, 1), (2687231, 1), (67495678093, 1), (4287755796749, 1), (10109399487240966566165404578297904544256598573003131834172351523160807416981, 1)])]),
    (6, .round 4473173789623477 [(2549488493329, 1), (4287755796749, 1), (4473173789623477, 1), (93519356885558614543291294309785410185094174903565271, 1)])]

private theorem checked13_52 : replayAbundance bank 13 5759831 (10^300) 8 state13_52 tree13_52 = true := by
  decide +kernel

theorem reject13_52 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_52 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree13_52 checked13_52

@[expose] noncomputable def state13_53 : State := ⟨361188648084531445929920877641340156544317601, 391287702091575733090747617444785169589677401, 0⟩

private noncomputable def tree13_53 : AbundanceTree :=
  .split 58047259977349384372529747126587 [
    (2, .split 68618354130992261250361621925551563109288767034369 [])]

private theorem checked13_53 : replayAbundance bank 13 5759831 (10^300) 4 state13_53 tree13_53 = true := by
  decide +kernel

theorem reject13_53 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_53 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree13_53 checked13_53

@[expose] noncomputable def state13_54 : State := ⟨61040881526285814362156628321386486455989674569, 66127621653476298892336347348168693660655480783, 0⟩

private noncomputable def tree13_54 : AbundanceTree :=
  .split 552781743698966779174737704265497702530829 [
    (1, .split 17247278064503276490215629 [])]

private theorem checked13_54 : replayAbundance bank 13 5759831 (10^300) 4 state13_54 tree13_54 = true := by
  decide +kernel

theorem reject13_54 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_54 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree13_54 checked13_54

@[expose] noncomputable def state13_55 : State := ⟨1743388617272249143997555461487119439669521095365209, 1888671002044936572664018416611046059641981186645643, 0⟩

private noncomputable def tree13_55 : AbundanceTree :=
  .split 534280344481909234853671069326391741 [
    (1, .split 16917208542442398371 [
      (2, .split 43162983777352599889 [])])]

private theorem checked13_55 : replayAbundance bank 13 5759831 (10^300) 5 state13_55 tree13_55 = true := by
  decide +kernel

theorem reject13_55 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_55 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree13_55 checked13_55

@[expose] noncomputable def state13_56 : State := ⟨8415003868347247618489696679505181495471801448798649088081, 9116254190709518253363838069463946620094451569531869845421, 0⟩

private noncomputable def tree13_56 : AbundanceTree :=
  .split 274690322498001718403 [
    (4, .round 1 [(945703914200715901032957574928753384673504013979356531, 1)])]

private theorem checked13_56 : replayAbundance bank 13 5759831 (10^300) 4 state13_56 tree13_56 = true := by
  decide +kernel

theorem reject13_56 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_56 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree13_56 checked13_56

@[expose] noncomputable def state13_57 : State := ⟨40617616406773309930154634339905725588976750479274358606191163529, 44002417774004419091000853868231202721391479685880555156707093823, 0⟩

private noncomputable def tree13_57 : AbundanceTree :=
  .split 30233706222041559662776806806113588758534692993333729 [
    (1, .split 52994926300350223824875516968726113151 [])]

private theorem checked13_57 : replayAbundance bank 13 5759831 (10^300) 4 state13_57 tree13_57 = true := by
  decide +kernel

theorem reject13_57 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_57 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree13_57 checked13_57

@[expose] noncomputable def state13_58 : State := ⟨6864377172744689378196133203444067624537070830997366604446306636401, 7436408603806746826379144303731073259915160066913813821483498856101, 0⟩

private noncomputable def tree13_58 : AbundanceTree :=
  .split 87103671046409436847 [
    (2, .split 48401662036451 [
      (2, .round 316089035473 [(4027, 1), (4759, 1), (7687, 1), (9283, 1), (27817, 1), (44533, 1), (92110001, 1), (4672993939, 1), (316089035473, 1), (14863108179151, 1), (26185818869971, 1)])]),
    (4, .round 92110001 [(27817, 1), (92110001, 1), (4672993939, 1), (48401662036451, 1)])]

private theorem checked13_58 : replayAbundance bank 13 5759831 (10^300) 5 state13_58 tree13_58 = true := by
  decide +kernel

theorem reject13_58 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_58 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree13_58 checked13_58

@[expose] noncomputable def state13_59 : State := ⟨33133037516798621392881499511582656606724154320695568102640872889340074409, 35894123976531839842288291137547877990617833847420198777860945630118413943, 0⟩

private noncomputable def tree13_59 : AbundanceTree :=
  .split 46832111174371450604616850217838043873 [
    (2, .round 1 [(800597722837718677177305324190218478736081107099, 1)])]

private theorem checked13_59 : replayAbundance bank 13 5759831 (10^300) 4 state13_59 tree13_59 = true := by
  decide +kernel

theorem reject13_59 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_59 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree13_59 checked13_59

@[expose] noncomputable def state13_60 : State := ⟨946312684517285425602088507550312255344648571553386120579525970592441865195449, 1025172074893725877735595883179504943290035952516168297294486468141812020628403, 0⟩

private noncomputable def tree13_60 : AbundanceTree :=
  .split 56573583882629131201397586942443243853379490390398336588076200421 []

private theorem checked13_60 : replayAbundance bank 13 5759831 (10^300) 3 state13_60 tree13_60 = true := by
  decide +kernel

theorem reject13_60 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_60 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_60 checked13_60

@[expose] noncomputable def state13_61 : State := ⟨159926843683421236926752957776002771153245608592522254377939889030122675218030881, 173254080657039673337315704257336335416016075975232442242768213115966231486200121, 0⟩

private noncomputable def tree13_61 : AbundanceTree :=
  .split 1194776740722409996051132396456283691052300333 [
    (1, .split 140808500332277052134234597144822699113 []),
    (2, .round 290751325679130827322454369115535898102478892669035583663447191523347847901 [(145009586102490829218552548223336637, 1), (290751325679130827322454369115535898102478892669035583663447191523347847901, 1)])]

private theorem checked13_61 : replayAbundance bank 13 5759831 (10^300) 4 state13_61 tree13_61 = true := by
  decide +kernel

theorem reject13_61 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_61 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree13_61 checked13_61

@[expose] noncomputable def state13_62 : State := ⟨771936328432730777189183517369830159827426282764863750131729657829597399846468418688729, 836264355802125008621615477150649339813045139661935729309373795982063849833674120246123, 0⟩

private noncomputable def tree13_62 : AbundanceTree :=
  .split 1999561631486182208460037804951465687912381337222920142652723329 [
    (1, .round 1 [(6709792556882923, 1), (6647910023442789120989346350302983626987758848799, 1)])]

private theorem checked13_62 : replayAbundance bank 13 5759831 (10^300) 4 state13_62 tree13_62 = true := by
  decide +kernel

theorem reject13_62 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_62 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree13_62 checked13_62

@[expose] noncomputable def state13_63 : State := ⟨22047273476367223727300270439599719194831122062047273567512330757271131337014984506168788969, 23884546266064492371241959642899695794400382233884546364805024987043725615099566548349521383, 0⟩

private noncomputable def tree13_63 : AbundanceTree :=
  .split 1386931777883518057046869588983880892136291513972206972463883515737484028199438341 []

private theorem checked13_63 : replayAbundance bank 13 5759831 (10^300) 3 state13_63 tree13_63 = true := by
  decide +kernel

theorem reject13_63 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_63 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_63 checked13_63

@[expose] noncomputable def state13_64 : State := ⟨106417978041190602791946491060293881007083613449188338481130625710173112177685960349236066114669921, 115286142877956486357942031981985037757673914569954033354558177852687538192493123711672404957559081, 0⟩

private noncomputable def tree13_64 : AbundanceTree :=
  .split 97149593605438945916118967283170626506454157662777835870622857 []

private theorem checked13_64 : replayAbundance bank 13 5759831 (10^300) 3 state13_64 tree13_64 = true := by
  decide +kernel

theorem reject13_64 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_64 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_64 checked13_64

@[expose] noncomputable def state13_65 : State := ⟨86808413954902578113899124146033582025796522106191700214004730205740649831517648547259748010923363334343041, 94042448451144459623390717824869713861279565615041008565171791056219037317477452592864727011833643612204961, 0⟩

private noncomputable def tree13_65 : AbundanceTree :=
  .split 2649670037989481306648479727588559059666394088223938940478532104361128850279248331066898797 []

private theorem checked13_65 : replayAbundance bank 13 5759831 (10^300) 3 state13_65 tree13_65 = true := by
  decide +kernel

theorem reject13_65 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_65 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_65 checked13_65

@[expose] noncomputable def state13_66 : State := ⟨2479335110965972533511072884734865136238774467874941149812189099406158699837975560158285662939982180192171594001, 2685946370213136911303662291796103897592005673531186245629871524356671924824473523504809468184980695208185893501, 0⟩

private noncomputable def tree13_66 : AbundanceTree :=
  .split 2214300387644795475106069490351281036761752410165858405300800926922235717085303811628037484076653499759427777 []

private theorem checked13_66 : replayAbundance bank 13 5759831 (10^300) 3 state13_66 tree13_66 = true := by
  decide +kernel

theorem reject13_66 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_66 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_66 checked13_66

@[expose] noncomputable def state13_67 : State := ⟨419007633753249358163371317520192208024352885070865054318259957799640820272617869666750277036856988452476999386169, 453924936566020138010318927313541558693048958826770475511448287616277555295336025472312800123261737490183416001683, 0⟩

private noncomputable def tree13_67 : AbundanceTree :=
  .round 1 [(1493185475735966076741431, 1), (19026442010188172700578868793469892827183847475034770559, 1)]

private theorem checked13_67 : replayAbundance bank 13 5759831 (10^300) 3 state13_67 tree13_67 = true := by
  decide +kernel

theorem reject13_67 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_67 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_67 checked13_67

@[expose] noncomputable def state13_68 : State := ⟨11967277027626554918504048199694209653383542750508976816383822654715541467806238975552054662449672447191195579468372809, 12964550113262101161712718883002060457832171313051391551082474542608503256790092223514725884320478484457128544424070543, 0⟩

private noncomputable def tree13_68 : AbundanceTree :=
  .round 1 [(1842708018885404721657218228344276394838382971121554990878798778219059086476647798269311913985066291, 1)]

private theorem checked13_68 : replayAbundance bank 13 5759831 (10^300) 3 state13_68 tree13_68 = true := by
  decide +kernel

theorem reject13_68 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_68 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_68 checked13_68

@[expose] noncomputable def state13_69 : State := ⟨2022469817668887781227184145748321431421818724836017081968866028646926508059254386868297237953994643575312052930155004721, 2191008969141295096329449491227348217373636951905685172132938197700837050397525585773988674450160863873254724007667921781, 0⟩

private noncomputable def tree13_69 : AbundanceTree :=
  .split 125025942261588947866880499769668751057693669636754394291266568468102904285433551663774528443041 []

private theorem checked13_69 : replayAbundance bank 13 5759831 (10^300) 3 state13_69 tree13_69 = true := by
  decide +kernel

theorem reject13_69 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_69 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_69 checked13_69

@[expose] noncomputable def state13_70 : State := ⟨57763760462441103919629606386717808402838564600041483878112782644184867996680364543345437413204041015154487543738157089836481, 62577407167644529246265406918944292436408444983378274201288847864533606996403728255290890530971044433084028172383003513989521, 0⟩

private noncomputable def tree13_70 : AbundanceTree :=
  .round 1 [(61349337746986017722692725938501380826299213257649660983422349704788968522764032871952828460266300559135616999, 1)]

private theorem checked13_70 : replayAbundance bank 13 5759831 (10^300) 3 state13_70 tree13_70 = true := by
  decide +kernel

theorem reject13_70 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_70 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_70 checked13_70

@[expose] noncomputable def state13_71 : State := ⟨227437666394005844316500527252761744284852640743712885642637897969492966486940917902690249609396565862882747018937640788915595934095847962009, 246390805260172998009542237857158556308590360805688959446191056133617380360852661061247770410179613018122975937182444187991895595270501958843, 0⟩

private noncomputable def tree13_71 : AbundanceTree :=
  .round 1889628004829682891131446914841122715904737697796281271846268890798899576955033713387489540044285157 [(115806724907473978817, 1), (1889628004829682891131446914841122715904737697796281271846268890798899576955033713387489540044285157, 1)]

private theorem checked13_71 : replayAbundance bank 13 5759831 (10^300) 3 state13_71 tree13_71 = true := by
  decide +kernel

theorem reject13_71 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_71 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_71 checked13_71

@[expose] noncomputable def state13_72 : State := ⟨6495847189879200919523571558866128178519676272281183726839381003906688615833519556218736219093975317609794137607877958572218335473711513642939049, 7037167789035800996150535855438305526729649294971282370742662754232246000486312852570297570685139927410610315741867788453236530096520806446517303, 0⟩

private noncomputable def tree13_72 : AbundanceTree :=
  .round 1 [(490892172446892018395299483401013733502108754948584834868805508270451316700696057763430117315431878622536780964504820752843410079, 1)]

private theorem checked13_72 : replayAbundance bank 13 5759831 (10^300) 3 state13_72 tree13_72 = true := by
  decide +kernel

theorem reject13_72 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_72 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree13_72 checked13_72

@[expose] noncomputable def state13_73 : State := ⟨1, 1, 0⟩

private theorem checked13_73 : checkChildren bank 13 5759831 (10^300) state13_73 13 [state13_42, state13_43, state13_44, state13_45, state13_46, state13_47, state13_48, state13_49, state13_50, state13_51, state13_52, state13_53, state13_54, state13_55, state13_56, state13_57, state13_58, state13_59, state13_60, state13_61, state13_62, state13_63, state13_64, state13_65, state13_66, state13_67, state13_68, state13_69, state13_70, state13_71, state13_72] = true := by
  decide +kernel

theorem reject13_73 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) (h : Valid state13_73 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state13_42, state13_43, state13_44, state13_45, state13_46, state13_47, state13_48, state13_49, state13_50, state13_51, state13_52, state13_53, state13_54, state13_55, state13_56, state13_57, state13_58, state13_59, state13_60, state13_61, state13_62, state13_63, state13_64, state13_65, state13_66, state13_67, state13_68, state13_69, state13_70, state13_71, state13_72] ?_ checked13_73
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject13_42 ho hN hs hav hx hvalid
  · exact reject13_43 ho hN hs hav hx hvalid
  · exact reject13_44 ho hN hs hav hx hvalid
  · exact reject13_45 ho hN hs hav hx hvalid
  · exact reject13_46 ho hN hs hav hx hvalid
  · exact reject13_47 ho hN hs hav hx hvalid
  · exact reject13_48 ho hN hs hav hx hvalid
  · exact reject13_49 ho hN hs hav hx hvalid
  · exact reject13_50 ho hN hs hav hx hvalid
  · exact reject13_51 ho hN hs hav hx hvalid
  · exact reject13_52 ho hN hs hav hx hvalid
  · exact reject13_53 ho hN hs hav hx hvalid
  · exact reject13_54 ho hN hs hav hx hvalid
  · exact reject13_55 ho hN hs hav hx hvalid
  · exact reject13_56 ho hN hs hav hx hvalid
  · exact reject13_57 ho hN hs hav hx hvalid
  · exact reject13_58 ho hN hs hav hx hvalid
  · exact reject13_59 ho hN hs hav hx hvalid
  · exact reject13_60 ho hN hs hav hx hvalid
  · exact reject13_61 ho hN hs hav hx hvalid
  · exact reject13_62 ho hN hs hav hx hvalid
  · exact reject13_63 ho hN hs hav hx hvalid
  · exact reject13_64 ho hN hs hav hx hvalid
  · exact reject13_65 ho hN hs hav hx hvalid
  · exact reject13_66 ho hN hs hav hx hvalid
  · exact reject13_67 ho hN hs hav hx hvalid
  · exact reject13_68 ho hN hs hav hx hvalid
  · exact reject13_69 ho hN hs hav hx hvalid
  · exact reject13_70 ho hN hs hav hx hvalid
  · exact reject13_71 ho hN hs hav hx hvalid
  · exact reject13_72 ho hN hs hav hx hvalid

theorem exclude_13 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 13 ∣ N)
    (hav : Nat.Coprime 5759831 N) (hx : N ≤ 10^300) : False :=
  reject13_73 ho hN hs hav hx (root_valid N)

end OddPerfect.IndexComponent.Size300
