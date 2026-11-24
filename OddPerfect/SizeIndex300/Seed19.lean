module

public import OddPerfect.SizeIndex300.Seed19Part02

public section

namespace OddPerfect.IndexComponent.Size300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def state19_105 : State := ⟨489304320748405446649619952702464909001298875933101, 516492855340819179268758129566261518333470826674114, 62060021⟩

private noncomputable def tree19_105 : AbundanceTree :=
  .split 1285983178319318482443211013887 [
    (2, .split 673 [
      (2, .split 151201 [
        (2, .split 8933917 [
          (2, .split 320083 [
            (2, .split 34151148991 [
              (2, .round 1 [(853, 1), (189337, 1), (2124921121, 1), (182955964171, 1)])]),
            (4, .split 750781489374165101 []),
            (6, .round 1 [(16371158815890691, 1)])]),
          (4, .split 52648055034228427507830821 []),
          (6, .round 1 [(34274188585995312993828606751747, 1)])]),
        (4, .abundant [(3, 4), (5, 2), (19, 10), (47, 2), (109, 2)]),
        (6, .split 4645408650446387216815339 []),
        (10, .round 1 [(4372817884287224443197838610260477113578606863, 1)])]),
      (4, .split 192811 [
        (2, .split 609757 [
          (2, .split 596899 [
            (2, .split 20323 [
              (2, .abundant [(3, 8), (7, 4), (19, 10), (31, 2), (37, 2), (47, 2)]),
              (4, .round 1 [(10357, 1), (170597490652383161, 1)]),
              (6, .abundant [(3, 6), (7, 2), (19, 10), (29, 2), (31, 2), (47, 2)])]),
            (4, .round 1 [(109, 1), (397, 1), (421, 1), (523, 1), (2531, 1), (20323, 1), (630133915661, 1)]),
            (6, .round 1 [(50465659297530123886919, 1)])]),
          (4, .split 117925236645991 [
            (2, .round 1 [(1362395539, 1)])]),
          (6, .round 1 [(8005847844291616347967786961, 1)])]),
        (4, .abundant [(3, 4), (5, 2), (11, 2)]),
        (6, .split 2992419337579673 []),
        (10, .round 1 [(50552551219222009, 1)])]),
      (6, .split 149854447 [
        (2, .split 1690099754311 [
          (2, .round 1 [(1327, 1), (20731, 1), (88709167, 1), (34610848633461703, 1)])]),
        (4, .round 1 [(38351, 1), (88709167, 1), (1350760001, 1), (2307145143731, 1)]),
        (6, .round 1 [(185042019984940188192193, 1)])]),
      (10, .split 41832052827966414311 [
        (2, .abundant [(3, 4), (7, 2), (19, 10), (23, 2), (31, 2), (47, 2)])]),
      (12, .split 6908555180220756335677 []),
      (16, .round 1 [(10808131541058781762828515811979771, 1)]),
      (18, .round 1 [(803372473647509302428002115170516353259089422238963, 1)])]),
    (4, .round 1 [(2861, 1)])]

private theorem checked19_105 : replayAbundance bank 19 127 (10^300) 9 state19_105 tree19_105 = true := by
  decide +kernel

theorem reject19_105 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_105 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 9 h tree19_105 checked19_105

@[expose] noncomputable def state19_106 : State := ⟨57862847162422087933014335672965109671150024627916412408400346501540621, 61078036473002457498382043500619269923042216196220188438903954042186842, 62060021⟩

private noncomputable def tree19_106 : AbundanceTree :=
  .split 13824943058809258349425668327816336867664962977401 [
    (2, .split 1483 [
      (2, .split 733591 []),
      (4, .round 1 [(6804911, 1)])])]

private theorem checked19_106 : replayAbundance bank 19 127 (10^300) 5 state19_106 tree19_106 = true := by
  decide +kernel

theorem reject19_106 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_106 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree19_106 checked19_106

@[expose] noncomputable def state19_107 : State := ⟨629231091507981341289477155275163163931242786692091019989544510912745511101182781, 664194754350606572685412145925759070974258975166987305513244607440455159784440966, 62060021⟩

private noncomputable def tree19_107 : AbundanceTree :=
  .split 673 [
    (2, .split 151201 [
      (2, .split 8933917 [
        (2, .split 320083 [
          (2, .split 34151148991 [
            (2, .split 182955964171 [
              (2, .round 1 [(2163289, 1), (2124921121, 1), (217230976273, 1)])]),
            (4, .abundant [(3, 6), (5, 2), (11, 2)])]),
          (4, .split 750781489374165101 [
            (2, .round 1 [(563672844786889585212011790180505303, 1)])]),
          (6, .round 1 [(47, 1), (109, 1), (439, 1), (853, 1), (10753, 1), (13679, 1), (189337, 1), (63799247, 1), (16371158815890691, 1)]),
          (10, .round 1 [(1737474188904574571323973, 1)])]),
        (4, .split 52648055034228427507830821 [
          (2, .abundant [(3, 4), (7, 2), (11, 2), (19, 10)])]),
        (6, .split 34274188585995312993828606751747 [])]),
      (4, .abundant [(3, 4), (5, 2), (19, 10), (47, 2), (109, 2)]),
      (6, .split 4645408650446387216815339 [
        (2, .abundant [(3, 4), (7, 2), (19, 10), (29, 2), (43, 2), (47, 2), (109, 2)])]),
      (10, .round 1 [(4372817884287224443197838610260477113578606863, 1)]),
      (12, .round 1 [(11489302824370776504884773, 1)])]),
    (4, .split 192811 [
      (2, .split 609757 [
        (2, .split 596899 [
          (2, .split 20323 [
            (2, .abundant [(3, 6), (7, 4), (19, 10), (31, 2), (37, 2), (47, 2)]),
            (4, .split 170597490652383161 [
              (2, .abundant [(3, 6), (7, 2), (13, 2), (19, 10), (31, 2)])]),
            (6, .abundant [(3, 6), (7, 2), (19, 10), (29, 2), (31, 2), (47, 2)])]),
          (4, .split 630133915661 [
            (2, .round 1 [(20323, 1), (4752411720588555433, 1)])]),
          (6, .round 1 [(2531, 1), (20323, 1), (8267393, 1), (50465659297530123886919, 1)])]),
        (4, .split 117925236645991 [
          (2, .round 1 [(20323, 1), (705751, 1), (52758703, 1), (109491307, 1), (1362395539, 1)])]),
        (6, .split 8005847844291616347967786961 []),
        (10, .round 1 [(1684932020575452819641795797727, 1)])]),
      (4, .abundant [(3, 2), (5, 2), (11, 2), (19, 10)]),
      (6, .split 2992419337579673 [
        (2, .round 1 [(8954573491920771950428960366603, 1)])]),
      (10, .round 1 [(7133771425679713, 1), (50552551219222009, 1)]),
      (12, .round 1 [(1301073676566448167206786457750427589549905276882964549926717, 1)])]),
    (6, .split 149854447 [
      (2, .split 1690099754311 [
        (2, .split 34610848633461703 [
          (2, .round 1 [(5136947906380039, 1)])]),
        (4, .abundant [(3, 4), (5, 2), (7, 2)])]),
      (4, .split 2307145143731 [
        (2, .round 1 [(1350760001, 1), (354932778402196909, 1)])]),
      (6, .round 1 [(88709167, 1), (362764543, 1), (185042019984940188192193, 1)])]),
    (10, .split 41832052827966414311 [
      (2, .round 1 [(20021, 1), (871752897817, 1), (9250500287937185644221097, 1)])]),
    (12, .split 6908555180220756335677 [
      (2, .round 1 [(174738080895730792395069136612351669, 1)])]),
    (16, .split 10808131541058781762828515811979771 []),
    (18, .round 1 [(109, 1), (803372473647509302428002115170516353259089422238963, 1)]),
    (22, .round 1 [(4542626403850880777, 1), (2011472309968638229211, 1)])]

private theorem checked19_107 : replayAbundance bank 19 127 (10^300) 9 state19_107 tree19_107 = true := by
  decide +kernel

theorem reject19_107 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_107 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 9 h tree19_107 checked19_107

@[expose] noncomputable def state19_108 : State := ⟨74409934541517129890189041277034628081327452293692610699621198281744633898238065233798610099520223901, 78544574260632818624692116737795826264830359321540340712153158427270604505276395874115725531151256734, 62060021⟩

private noncomputable def tree19_108 : AbundanceTree :=
  .split 195563210996935540523583770995894853917345964174681742857298704837702198458534097 []

private theorem checked19_108 : replayAbundance bank 19 127 (10^300) 3 state19_108 tree19_108 = true := by
  decide +kernel

theorem reject19_108 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_108 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_108 checked19_108

@[expose] noncomputable def state19_109 : State := ⟨809172839337973202834199698753854933201003080637201585299507793201958895443464370781419753971559567976181094861, 854135090437518227055637363789320080430169668533408103123435461678658546335396233690022502380499576137971799178, 62060021⟩

private noncomputable def tree19_109 : AbundanceTree :=
  .split 185441 [
    (2, .split 1567 [
      (2, .abundant [(3, 4), (7, 2), (13, 2), (19, 10), (47, 2)]),
      (4, .abundant [(3, 2), (7, 2), (11, 2), (13, 2), (19, 10)]),
      (6, .split 14814643926095565217 []),
      (10, .abundant [(3, 2), (7, 2), (13, 2), (19, 10), (23, 2)]),
      (12, .round 1 [(148762334008975733281, 1)])]),
    (4, .abundant [(3, 2), (5, 2), (11, 2), (19, 10)]),
    (6, .split 673 [
      (2, .split 151201 [
        (2, .round 1 [(853, 1), (8933917, 1)])]),
      (4, .round 1 [(47, 1), (109, 1), (421, 1), (2531, 1), (192811, 1)]),
      (6, .round 1 [(149854447, 1)])])]

private theorem checked19_109 : replayAbundance bank 19 127 (10^300) 6 state19_109 tree19_109 = true := by
  decide +kernel

theorem reject19_109 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_109 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree19_109 checked19_109

@[expose] noncomputable def state19_110 : State := ⟨95689006504136511889917002419170896272308171129936444649584879655738651304097542665535997878940675108357714897252219445648666017581, 101006032643354180937523224642527496024920946775412129578631014326538540440138028853113578803552248581675577358534477836831544625186, 62060021⟩

private noncomputable def tree19_110 : AbundanceTree :=
  .split 28429 [
    (2, .split 5701 [
      (2, .split 10835701 [
        (2, .round 1 [(32292739, 1)])]),
      (4, .abundant [(3, 4), (5, 2), (7, 2)])]),
    (4, .round 1 [(31, 1), (47, 1), (109, 1), (673, 1), (10211, 1), (111601811, 1)]),
    (6, .round 1 [(527940254843336209169517811, 1)])]

private theorem checked19_110 : replayAbundance bank 19 127 (10^300) 6 state19_110 tree19_110 = true := by
  decide +kernel

theorem reject19_110 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_110 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree19_110 checked19_110

@[expose] noncomputable def state19_111 : State := ⟨380494100711521473821, 401632668333839157822, 62060021⟩

private theorem checked19_111 : checkChildren bank 19 127 (10^300) state19_111 104281 [state19_103, state19_104, state19_105, state19_106, state19_107, state19_108, state19_109, state19_110] = true := by
  decide +kernel

theorem reject19_111 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_111 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state19_103, state19_104, state19_105, state19_106, state19_107, state19_108, state19_109, state19_110] ?_ checked19_111
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject19_103 ho hN hs hav hx hvalid
  · exact reject19_104 ho hN hs hav hx hvalid
  · exact reject19_105 ho hN hs hav hx hvalid
  · exact reject19_106 ho hN hs hav hx hvalid
  · exact reject19_107 ho hN hs hav hx hvalid
  · exact reject19_108 ho hN hs hav hx hvalid
  · exact reject19_109 ho hN hs hav hx hvalid
  · exact reject19_110 ho hN hs hav hx hvalid

@[expose] noncomputable def state19_112 : State := ⟨23613471880533137607282210241, 24925331831084099616736684163, 0⟩

private noncomputable def tree19_112 : AbundanceTree :=
  .split 17748600316039 [
    (2, .split 105004271059505813093655187 [
      (2, .split 7628654724064665238414519372668238801 [
        (1, .split 34960613997972077237 [
          (2, .round 1 [(751, 1), (1699, 1), (1753, 1), (104281, 1), (283564158181, 1), (292502835310001, 1)])]),
        (2, .round 283564158181 [(1699, 1), (4723, 1), (104281, 1), (283564158181, 1), (1096259005867, 1)])]),
      (4, .abundant [(3, 2), (7, 2), (11, 2), (19, 10), (31, 2)])]),
    (4, .split 1974411424507417425755276131904734921 [
      (1, .split 5279174931838014507367048481028703 [
        (2, .abundant [(3, 2), (7, 2), (11, 2), (17, 2), (19, 10)])]),
      (2, .round 1144430876288986402314739685500413679747878481 [(31, 1), (1171, 1), (104281, 1), (124771, 1), (145381, 1), (295225751, 1), (9100197832105955096371, 1), (1144430876288986402314739685500413679747878481, 1)])]),
    (6, .split 5158568022412358951621235813834337785958866750186553335421344366923371321 [
      (1, .round 1 [(48105532969151269777790678536224865597, 1)])])]

private theorem checked19_112 : replayAbundance bank 19 127 (10^300) 7 state19_112 tree19_112 = true := by
  decide +kernel

theorem reject19_112 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_112 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree19_112 checked19_112

@[expose] noncomputable def state19_113 : State := ⟨90946016697056457013819533273465356426036281, 95998574727092052959308197841909026059633705, 0⟩

private noncomputable def tree19_113 : AbundanceTree :=
  .split 116856733421 [
    (1, .abundant [(3, 2), (5, 2), (11, 2), (13, 2)]),
    (2, .split 575428601657895373 [
      (1, .split 738389740637 [
        (2, .split 110659510671547497241 [
          (2, .abundant [(3, 2), (5, 2), (13, 2), (19, 10)])]),
        (4, .split 1368186226749564413251 [
          (2, .abundant [(3, 2), (5, 2), (7, 2)])]),
        (6, .round 1 [(1249, 1), (11173, 1), (104281, 1), (389651, 1), (23159681, 1), (29037121, 1), (61511921, 1)])]),
      (2, .split 559016688150211 [
        (2, .abundant [(3, 2), (5, 1), (7, 2)]),
        (4, .abundant [(3, 2), (5, 2), (11, 2), (19, 10)])]),
      (4, .round 124744666201 [(61511921, 1), (124744666201, 1), (1948799913186274801163476159014724224101694439062599765111, 1)])]),
    (4, .split 636865925135816416129802831 [
      (2, .split 515335281372167025562710000343177170584029 [
        (1, .round 1 [(39061354749701320139643310061584099, 1)])])]),
    (6, .split 1286628677048226457522103729965407324742932243211542616199 []),
    (10, .round 61511921 [(104281, 1), (23159681, 1), (61511921, 1)])]

private theorem checked19_113 : replayAbundance bank 19 127 (10^300) 7 state19_113 tree19_113 = true := by
  decide +kernel

theorem reject19_113 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_113 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree19_113 checked19_113

@[expose] noncomputable def state19_114 : State := ⟨350273691006022778609510090539508159195870737639522634119921, 369733346464027767012421146097113224007973970971808894221727, 0⟩

private noncomputable def tree19_114 : AbundanceTree :=
  .split 2041648288605040221889024691 [
    (2, .split 914171474762788693668656274889106858671 [])]

private theorem checked19_114 : replayAbundance bank 19 127 (10^300) 4 state19_114 tree19_114 = true := by
  decide +kernel

theorem reject19_114 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_114 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_114 checked19_114

@[expose] noncomputable def state19_115 : State := ⟨5195833091877069148920641440166362378845657890018420829952444397186045167177114143575796001, 5484490574244164835040791050105235993074441267373387061567251544417964457218629379198166011, 0⟩

private noncomputable def tree19_115 : AbundanceTree :=
  .split 13227046155712782636741137653875891345779 [
    (2, .round 1 [(271, 1), (10111, 1)])]

private theorem checked19_115 : replayAbundance bank 19 127 (10^300) 4 state19_115 tree19_115 = true := by
  decide +kernel

theorem reject19_115 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_115 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_115 checked19_115

@[expose] noncomputable def state19_116 : State := ⟨20011471651423311962179647214748519944587865542894225213570790089129430849784834531154763243478153052556441, 21123220416869803730506677936080031401169018220266718471275752310305331648025969275112634130631710822088673, 0⟩

private noncomputable def tree19_116 : AbundanceTree :=
  .split 7484591086350246919092708017291837 [
    (1, .round 1 [(104281, 1), (404197, 1), (40325668900104021637477, 1), (1247431847725041153182118002881973, 1)])]

private theorem checked19_116 : replayAbundance bank 19 127 (10^300) 4 state19_116 tree19_116 = true := by
  decide +kernel

theorem reject19_116 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_116 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_116 checked19_116

@[expose] noncomputable def state19_117 : State := ⟨296842923957532644777128524824048472502406855643631659812533302370633490190063603847274417172377626958479710443097508698231661716901442121, 313334202559615941244999192121824741632040265697404812375042166984907030279914600745702776902444565462249570874391718853283897411835131037, 0⟩

private noncomputable def tree19_117 : AbundanceTree :=
  .split 104281 [
    (1, .split 40529 [
      (2, .round 1 [(2267, 1), (29989, 1), (1642640371, 1)])]),
    (2, .split 179743 [
      (2, .round 1 [(49627843, 1)])])]

private theorem checked19_117 : replayAbundance bank 19 127 (10^300) 5 state19_117 tree19_117 = true := by
  decide +kernel

theorem reject19_117 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_117 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree19_117 checked19_117

@[expose] noncomputable def state19_118 : State := ⟨1143274553408674838035399619688411853567442821114679970604491363328521806028133550204278949509294404296129384865944617746572442953051889588459946364895361, 1206789825821340271439500135048155615502726319719222376587821061081317961462096206791950765631278852688784898063042717050738237879427961415547716893185139, 0⟩

private noncomputable def tree19_118 : AbundanceTree :=
  .round 1 [(65219432427202213218611042380245134951516556220905814475152737256300473009279433432471898046319778085284772450023, 1)]

private theorem checked19_118 : replayAbundance bank 19 127 (10^300) 3 state19_118 tree19_118 = true := by
  decide +kernel

theorem reject19_118 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_118 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_118 checked19_118

@[expose] noncomputable def state19_119 : State := ⟨6131066257801, 6471681049901, 0⟩

private theorem checked19_119 : checkChildren bank 19 127 (10^300) state19_119 62060021 [state19_111, state19_112, state19_113, state19_114, state19_115, state19_116, state19_117, state19_118] = true := by
  decide +kernel

theorem reject19_119 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_119 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state19_111, state19_112, state19_113, state19_114, state19_115, state19_116, state19_117, state19_118] ?_ checked19_119
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject19_111 ho hN hs hav hx hvalid
  · exact reject19_112 ho hN hs hav hx hvalid
  · exact reject19_113 ho hN hs hav hx hvalid
  · exact reject19_114 ho hN hs hav hx hvalid
  · exact reject19_115 ho hN hs hav hx hvalid
  · exact reject19_116 ho hN hs hav hx hvalid
  · exact reject19_117 ho hN hs hav hx hvalid
  · exact reject19_118 ho hN hs hav hx hvalid

@[expose] noncomputable def state19_120 : State := ⟨2213314919066161, 2336276859014281, 0⟩

private noncomputable def tree19_120 : AbundanceTree :=
  .split 133338869 [
    (1, .abundant [(3, 2), (5, 2), (7, 2)]),
    (2, .split 316950847 [
      (2, .split 33485946576989419 [
        (2, .split 3977922110084642993062668607 [
          (2, .split 5274621437966752855709432191676310205338603949788663019 [])]),
        (4, .split 76574672959050740219756384533876186628666339913941 [
          (1, .round 1 [(7927, 1), (29251, 1), (56094673, 1), (12091081603, 1), (2717852329690688043093572894629, 1)])]),
        (6, .round 1 [(2225647600931082732306305439409191196187821442910144610243861763322509263, 1)])]),
      (4, .split 290770486991 [
        (2, .split 6367921363 [
          (2, .split 41442572371 [
            (2, .abundant [(3, 2), (7, 2), (11, 2), (19, 12), (31, 2)]),
            (4, .abundant [(3, 2), (5, 1), (11, 2), (19, 12)]),
            (6, .round 1 [(2395275511, 1)])]),
          (4, .split 590385607384351 [
            (2, .round 7905387587089 [(9901391, 1), (22431271, 1), (56094673, 1), (2395275511, 1), (109449185539, 1), (7905387587089, 1)])]),
          (6, .round 56094673 [(71, 1), (571, 1), (599, 1), (1951, 1), (29251, 1), (591901, 1), (1182431, 1), (22431271, 1), (56094673, 1), (2395275511, 1)])]),
        (4, .split 18133834148123055907452160021 [
          (1, .round 1 [(571, 1), (599, 1), (1951, 1), (3181, 1), (29251, 1), (1182431, 1), (40489321, 1), (56094673, 1), (501178511, 1), (1947157841, 1), (2395275511, 1), (4344740942669, 1)]),
          (2, .abundant [(3, 2), (5, 1), (11, 2), (19, 12)])]),
        (6, .round 14027349673 [(64050113, 1), (2395275511, 1), (14027349673, 1), (74175564031330658180302227052116705369911023, 1)])]),
      (6, .split 133321199956302288761960977 [
        (1, .split 178809055095947 [
          (2, .split 303759912394367965087 [
            (2, .round 1 [(19225510331591154038435765646529, 1)])]),
          (4, .round 1 [(759273457, 1), (12244884163, 1), (21414089265143, 1)])]),
        (2, .split 20977832244420473277393404703290341 [
          (1, .round 1 [(12244884163, 1), (21414089265143, 1), (22336571194934180343253, 1)])])]),
      (10, .split 901587609162625343111346092627481367099696294946383571623960494387521287 []),
      (12, .split 56094673 [
        (1, .split 31981 [
          (2, .round 1 [(599, 1), (859, 1), (877, 1), (2081, 1), (8317, 1), (29251, 1), (31253, 1), (40993, 1)]),
          (4, .round 1 [(31253, 1), (16520191511, 1)])]),
        (2, .split 1048870798357201 [
          (1, .round 1 [(31253, 1), (170203097, 1)])])])]),
    (4, .split 28736534061494944742276637557351 [
      (2, .split 31760490959072695223529283 [
        (2, .round 661 [(97, 1), (599, 1), (661, 1), (29251, 1), (41325067365823, 1), (135977951957568402271, 1)])])]),
    (6, .split 83805125413969394807266869009652300225171631 [
      (2, .split 3874647592440350471397670127556814092997439024014257871899409 [])]),
    (10, .split 1455348248764276069690512860868005199229003 []),
    (12, .split 1024629021395998244971958696557093043058573256266282635925428861 [
      (1, .round 1 [(38647753, 1), (1316180923115132621, 1)])]),
    (16, .split 29251 [
      (2, .round 1 [(1477807, 1)])])]

private theorem checked19_120 : replayAbundance bank 19 127 (10^300) 8 state19_120 tree19_120 = true := by
  decide +kernel

theorem reject19_120 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_120 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree19_120 checked19_120

@[expose] noncomputable def state19_121 : State := ⟨288441413567621167681, 304465936543600121441, 0⟩

private noncomputable def tree19_121 : AbundanceTree :=
  .split 99995282631947 [
    (2, .split 129574807 [
      (2, .split 5596543579554019 [
        (2, .split 9612063923644045579 [
          (2, .split 118908330594876916973454248990313373 [
            (1, .abundant [(3, 4), (7, 2), (13, 2), (19, 16), (37, 2)])]),
          (4, .round 14879180581 [(3044803, 1), (10050613, 1), (14879180581, 1)])]),
        (4, .split 1536153963224241878311859680676309891 []),
        (6, .round 10050613 [(29, 1), (67, 1), (87403, 1), (1311127, 1), (3044803, 1), (10050613, 1)])]),
      (4, .split 537919877835868006051 [
        (2, .split 7828258473822109303 [
          (2, .split 37344077229108872621199190017002593 [
            (1, .round 1 [(3044803, 1), (10050613, 1)])])]),
        (4, .round 1 [(87403, 1), (1311127, 1), (3044803, 1)])]),
      (6, .split 282510594090638575830851732813 [
        (1, .split 281946700689260055719412907 [
          (2, .round 1 [(1311127, 1), (3044803, 1), (10050613, 1)])]),
        (2, .round 10050613 [(29, 1), (67, 1), (71, 1), (199, 1), (1499, 1), (8191, 1), (9157, 1), (72367, 1), (87403, 1), (1311127, 1), (3044803, 1), (10050613, 1)])]),
      (10, .round 1 [(1311127, 1), (3044803, 1), (2051911628894931110311811615696081848001217968792167, 1)]),
      (12, .round 1 [(44604207284711557453102149250212199279132866082055230912453669537416701733960164663, 1)])]),
    (4, .split 836611965227956085219418549834729037351 [
      (2, .split 17219916093251301116052729581099566497810811153 [])]),
    (6, .split 4652385632270610217303236066567347711621 [
      (1, .round 1 [(16857692111586805864708941403112365837, 1), (775397605378435036217206011094557951937, 1)])])]

private theorem checked19_121 : replayAbundance bank 19 127 (10^300) 8 state19_121 tree19_121 = true := by
  decide +kernel

theorem reject19_121 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_121 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree19_121 checked19_121

@[expose] noncomputable def state19_122 : State := ⟨104127350297911241532841, 109912203092239643840221, 0⟩

private noncomputable def tree19_122 : AbundanceTree :=
  .split 109912203092239643840221 [
    (1, .split 16842464147039939 [
      (2, .split 16804815986052307 [
        (2, .split 103786049366070998904953372317 [
          (2, .round 1 [(41267859317595241, 1), (12429301572625457913698663439867217685587, 1)])]),
        (4, .round 1 [(18982297, 1), (55067041, 1), (131659020401219202550655891832780288667108075297709311051, 1)]),
        (6, .round 1 [(18982297, 1)])]),
      (4, .split 1319145472132817553886313329747888026461175713980985963030890861 []),
      (6, .round 1 [(3204380343919654981319275346519952548867642854842486945501278105196317, 1)])]),
    (2, .split 10760206295810970254814774980512127221 [
      (1, .split 439552815560351 [
        (2, .split 11327411057072547258673 [
          (2, .round 1 [(1623337777304049828432228200687238771283, 1)])]),
        (4, .abundant [(3, 2), (5, 2), (11, 2), (13, 2)])]),
      (2, .split 9338793885988865663044338444054341113 [
        (1, .split 183361 [
          (2, .abundant [(3, 4), (7, 2), (13, 2), (19, 18), (37, 2)]),
          (4, .abundant [(3, 2), (5, 2), (7, 2)])])])]),
    (4, .split 3519965848655194762931969528014081 [
      (1, .round 1 [(114118662694961, 1), (22580796951639782467655033, 1), (657067724021324845960747798585621, 1)])]),
    (6, .round 1 [(7, 1)])]

private theorem checked19_122 : replayAbundance bank 19 127 (10^300) 7 state19_122 tree19_122 = true := by
  decide +kernel

theorem reject19_122 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_122 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree19_122 checked19_122

@[expose] noncomputable def state19_123 : State := ⟨13569980418174090907801371961, 14323868219183762624901448181, 0⟩

private noncomputable def tree19_123 : AbundanceTree :=
  .split 1335495402823 [
    (2, .split 3381863410579 [
      (2, .split 5666151340567 [
        (2, .abundant [(3, 4), (7, 2), (13, 1), (19, 22), (31, 2)]),
        (4, .split 15728947510785623941 [
          (1, .round 1 [(499159, 1), (1347919, 1), (379687663, 1), (16497763013, 1), (4068532723948687, 1), (2364392891748676771, 1)]),
          (2, .round 1 [(379687663, 1), (2364392891748676771, 1)])]),
        (6, .round 16497763013 [(239, 1), (277, 1), (463, 1), (2347, 1), (499159, 1), (1347919, 1), (379687663, 1), (16497763013, 1)])]),
      (4, .split 794932978346037131 [
        (2, .round 16497763013 [(463, 1), (2347, 1), (4861, 1), (539947, 1), (716351, 1), (939931, 1), (25979311, 1), (175924351, 1), (379687663, 1), (16497763013, 1), (1146504157422163, 1)])]),
      (6, .round 1 [(379687663, 1), (736780645245109284585700948378143836767280313662007029396357032327, 1)])]),
    (4, .split 9235379541700294893241592533312191410548921 [
      (1, .split 158037228202544489771066643850100814719 [
        (2, .round 1 [(16497763013, 1)])]),
      (2, .split 16497763013 [
        (1, .round 1 [(2131, 1), (2347, 1), (4951, 1), (746167, 1), (1290299, 1)])])]),
    (10, .round 16497763013 [(45673, 1), (796625303, 1), (16497763013, 1)])]

private theorem checked19_123 : replayAbundance bank 19 127 (10^300) 7 state19_123 tree19_123 = true := by
  decide +kernel

theorem reject19_123 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_123 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree19_123 checked19_123

@[expose] noncomputable def state19_124 : State := ⟨638411683925748518131605316913942641, 673878999699401213583361167853606121, 0⟩

private noncomputable def tree19_124 : AbundanceTree :=
  .split 165049085515149863 [
    (2, .split 210760197502242391 [
      (2, .split 5529489944354911 [
        (2, .split 119119141275549171391 [
          (2, .round 1 [(2161188870894566657019607264162507, 1)])]),
        (4, .abundant [(3, 2), (5, 1), (13, 1), (19, 28), (59, 2)])]),
      (4, .split 53699356071124407937717710072242399831889360212253450208505201 [])]),
    (4, .split 462332852147235946389022227567721 [
      (1, .round 1 [(19949, 1), (47563, 1), (83742643, 1), (2046537721, 1), (374474805409, 1), (297003021451861, 1), (544269503440038940542961, 1)]),
      (2, .abundant [(3, 2), (7, 2), (11, 2), (19, 28), (59, 2), (131, 2), (233, 1)])]),
    (6, .split 297003021451861 [
      (1, .split 1227285212611 [])])]

private theorem checked19_124 : replayAbundance bank 19 127 (10^300) 7 state19_124 tree19_124 = true := by
  decide +kernel

theorem reject19_124 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_124 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree19_124 checked19_124

@[expose] noncomputable def state19_125 : State := ⟨230466617897195215045509519405933293401, 243270318891483838103593381595151809701, 0⟩

private noncomputable def tree19_125 : AbundanceTree :=
  .split 243270318891483838103593381595151809701 [
    (1, .split 48837672001 [
      (2, .split 10857851 [
        (2, .split 16841848456579 [
          (2, .split 80882782483 [
            (2, .abundant [(3, 4), (7, 2), (13, 2), (19, 30), (103, 2)]),
            (4, .round 1 [(919630957793653936389727100981, 1)])]),
          (4, .round 1 [(163, 1), (283, 1), (691, 1), (24229, 1), (32579, 1), (327689, 1), (886799, 1), (3731137, 1), (6684907, 1)])]),
        (4, .abundant [(3, 2), (5, 2), (11, 2), (19, 30)]),
        (6, .split 6684907 [
          (2, .split 4728697 [
            (2, .round 1 [(24229, 1), (32579, 1), (327689, 1), (886799, 1), (3731137, 1), (22518207499, 1)]),
            (4, .round 1 [(320683080755221, 1)])]),
          (4, .round 1 [(3731137, 1), (181546908917839756944254491, 1)])]),
        (10, .round 1 [(327689, 1), (886799, 1), (3731137, 1), (6684907, 1)])]),
      (4, .split 9914944534833970091 [
        (2, .round 1 [(19543, 1), (24229, 1), (32579, 1), (64453, 1), (327689, 1), (886799, 1), (10857851, 1), (3653236254381775601, 1)])]),
      (6, .round 1 [(10857851, 1), (6307582352219676571, 1), (2151130674591536410408271989953606683289509317, 1)])]),
    (2, .split 1517447385988826624856071573502814124388188817307601190223067900871037679977 [
      (1, .round 1 [(1368002308501049720943852205382042557991811143693371561411789, 1)])])]

private theorem checked19_125 : replayAbundance bank 19 127 (10^300) 8 state19_125 tree19_125 = true := by
  decide +kernel

theorem reject19_125 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_125 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree19_125 checked19_125

@[expose] noncomputable def state19_126 : State := ⟨10842505080063916320800450434338728415281531281, 11444866473400800560844919902913102216130505241, 0⟩

private noncomputable def tree19_126 : AbundanceTree :=
  .split 21406757809476033811281103559 [
    (2, .split 1879593499986749153862319 [
      (2, .round 1 [(3588174588084451, 1), (64148371425431627832601436220662527, 1)])]),
    (4, .round 1 [(3588174588084451, 1)])]

private theorem checked19_126 : replayAbundance bank 19 127 (10^300) 5 state19_126 tree19_126 = true := by
  decide +kernel

theorem reject19_126 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_126 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree19_126 checked19_126

@[expose] noncomputable def state19_127 : State := ⟨1413006104539009638843035501053457425807904438071201, 1491506443680065729889870806667538393908343573519601, 0⟩

private noncomputable def tree19_127 : AbundanceTree :=
  .split 11951068054199383402102234839038071 [
    (2, .split 325220800093458627477824778607 [
      (2, .round 1 [(1122827308399, 1)])])]

private theorem checked19_127 : replayAbundance bank 19 127 (10^300) 5 state19_127 tree19_127 = true := by
  decide +kernel

theorem reject19_127 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_127 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree19_127 checked19_127

@[expose] noncomputable def state19_128 : State := ⟨510095203738582479622335815880298130716653502143703561, 538433826168503728490243361206981360200912030040575981, 0⟩

private noncomputable def tree19_128 : AbundanceTree :=
  .split 28461948730641665973894996037 [
    (1, .split 18917672548149688895557513 [
      (2, .split 119122047354131617 [
        (2, .round 1 [(1637, 1), (10939, 1), (46751, 1), (71839132231230571116884209, 1)])])]),
    (2, .split 1524523113963417599654286922906303801 [
      (1, .round 1 [(125887, 1), (1259413, 1), (363272734884668341, 1), (2098317555331289161, 1), (18917672548149688895557513, 1)])])]

private theorem checked19_128 : replayAbundance bank 19 127 (10^300) 6 state19_128 tree19_128 = true := by
  decide +kernel

theorem reject19_128 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_128 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree19_128 checked19_128

@[expose] noncomputable def state19_129 : State := ⟨66476117046415807326862425861336332693125001052869591773081, 70169234660105574400577005075855017842743056666917902427141, 0⟩

private noncomputable def tree19_129 : AbundanceTree :=
  .split 70169234660105574400577005075855017842743056666917902427141 [
    (1, .split 66569719867813794343 [
      (2, .split 735189538004593929463 [
        (2, .round 1 [(4869402313436110466304246936161401922503, 1)])])]),
    (2, .round 1 [(9043, 1), (89119, 1)])]

private theorem checked19_129 : replayAbundance bank 19 127 (10^300) 6 state19_129 tree19_129 = true := by
  decide +kernel

theorem reject19_129 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_129 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree19_129 checked19_129

@[expose] noncomputable def state19_130 : State := ⟨3127427491907749548018497790443751608857168317658177523074947729361, 3301173463680402300686192112135071142682566557528076274356889269881, 0⟩

private noncomputable def tree19_130 : AbundanceTree :=
  .split 37334173314913678536474517 [
    (1, .split 2551089855701675251204783 [
      (2, .split 2037684451226282489 [
        (2, .round 1 [(938444395204832616319117, 1)])])]),
    (2, .split 19662850693470066560369007324997054554511235161 [
      (1, .round 1 [(2551089855701675251204783, 1), (183651679276988647753432530635281551141457, 1)])])]

private theorem checked19_130 : replayAbundance bank 19 127 (10^300) 6 state19_130 tree19_130 = true := by
  decide +kernel

theorem reject19_130 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_130 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree19_130 checked19_130

@[expose] noncomputable def state19_131 : State := ⟨147132581620420448213882032847979675383852886669516818427458744956737812041, 155306613932666028670208812450645212905178047040045530562317564121001023821, 0⟩

private noncomputable def tree19_131 : AbundanceTree :=
  .split 155306613932666028670208812450645212905178047040045530562317564121001023821 [
    (1, .split 25884435655444338111701468741774202150863007840007588427052927353500170637 [])]

private theorem checked19_131 : replayAbundance bank 19 127 (10^300) 4 state19_131 tree19_131 = true := by
  decide +kernel

theorem reject19_131 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_131 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_131 checked19_131

@[expose] noncomputable def state19_132 : State := ⟨53114861964971781805211413858120662813570892087695571452312606929382350146801, 56065687629692436349945381294682921858769274981456436532996640647681369599401, 0⟩

private noncomputable def tree19_132 : AbundanceTree :=
  .split 56065687629692436349945381294682921858769274981456436532996640647681369599401 [
    (1, .round 1 [(9701103752872552262464583, 1), (4012501458145349117003681108099144759239934369, 1)])]

private theorem checked19_132 : replayAbundance bank 19 127 (10^300) 4 state19_132 tree19_132 = true := by
  decide +kernel

theorem reject19_132 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_132 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_132 checked19_132

@[expose] noncomputable def state19_133 : State := ⟨2498835475335488615165941356210895586368381374221567418772496080399497448506732376681, 2637659668409682427119604764889278674499958117233876719815412529310580640090439730941, 0⟩

private noncomputable def tree19_133 : AbundanceTree :=
  .split 111718923317519780739416742825495315326353 [
    (1, .split 24299939580826833879511 [
      (2, .round 1 [(1650922227287, 1), (600691521094362857, 1)])]),
    (2, .round 1 [(24299939580826833879511, 1)])]

private theorem checked19_133 : replayAbundance bank 19 127 (10^300) 5 state19_133 tree19_133 = true := by
  decide +kernel

theorem reject19_133 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_133 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree19_133 checked19_133

@[expose] noncomputable def state19_134 : State := ⟨325650737981196211817040643482760123711113829069928887581850461693742906986845870061444601, 343742445646818223584654012565135686139509041796036048003064376232284179597226196175969301, 0⟩

private noncomputable def tree19_134 : AbundanceTree :=
  .split 15039779687938609372385845398208131004523 [
    (2, .round 1 [(19840332702980239, 1)])]

private theorem checked19_134 : replayAbundance bank 19 127 (10^300) 4 state19_134 tree19_134 = true := by
  decide +kernel

theorem reject19_134 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_134 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_134 checked19_134

@[expose] noncomputable def state19_135 : State := ⟨117559916411211832465951672297276404659712092294244328417048016671441189422251359092181500961, 124091022878501378714060098536013982696362764088369013329106239819854588834598656819524917681, 0⟩

private noncomputable def tree19_135 : AbundanceTree :=
  .split 3226690707486553756833988409595477959 [
    (2, .round 1 [(391818505243975817655620850033223, 1)])]

private theorem checked19_135 : replayAbundance bank 19 127 (10^300) 4 state19_135 tree19_135 = true := by
  decide +kernel

theorem reject19_135 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_135 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_135 checked19_135

@[expose] noncomputable def state19_136 : State := ⟨5530709837851818935985098926648662357728660588336035659633359363610638296057696191939038924612591641, 5837971495510253321317604422573588044269141732132482085168545994922340423616457091491207753757735621, 0⟩

private noncomputable def tree19_136 : AbundanceTree :=
  .split 12577647923565067982570531255067267090413921105116610018487966576192735681081030635731 []

private theorem checked19_136 : replayAbundance bank 19 127 (10^300) 3 state19_136 tree19_136 = true := by
  decide +kernel

theorem reject19_136 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_136 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_136 checked19_136

@[expose] noncomputable def state19_137 : State := ⟨720767636778686895556514077219780327121556776532540503199079025625101993380535025429687491694437555246761, 760810283266391723087431525954212567517198819673237197821250082604274326346120304620225685677461863871581, 0⟩

private noncomputable def tree19_137 : AbundanceTree :=
  .round 1 [(4555750199199950437649290574576123158785621674690043100726048398827989978120480865989375363338094993243, 1)]

private theorem checked19_137 : replayAbundance bank 19 127 (10^300) 3 state19_137 tree19_137 = true := by
  decide +kernel

theorem reject19_137 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_137 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_137 checked19_137

@[expose] noncomputable def state19_138 : State := ⟨33909148468541327024611190051706596115901832643493493141183991149154498993443438522697051601444997586070043641441, 35792990050126956303756256165690295900118601123687576093471990657440860048634740662846887801525275229740601621521, 0⟩

private noncomputable def tree19_138 : AbundanceTree :=
  .split 1991511641305906595444902842736305161490856691155674104014444795547589309174118116074569 []

private theorem checked19_138 : replayAbundance bank 19 127 (10^300) 3 state19_138 tree19_138 = true := by
  decide +kernel

theorem reject19_138 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_138 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_138 checked19_138

@[expose] noncomputable def state19_139 : State := ⟨575898160682100232836281104757191024769944517268203419236599427061651467503917683818033285217971123197113409626034423582081, 607892502942216912438296721688146081701608101560881386971966061898409882365246444030146245507858407819175265716369669336641, 0⟩

private noncomputable def tree19_139 : AbundanceTree :=
  .round 1 [(62468771853453988907994855172682616050526469382576404972295431, 1)]

private theorem checked19_139 : replayAbundance bank 19 127 (10^300) 3 state19_139 tree19_139 = true := by
  decide +kernel

theorem reject19_139 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_139 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_139 checked19_139

@[expose] noncomputable def state19_140 : State := ⟨75051624198251984443456989853061891539043939434909537798332873934101480896578056472849915762891214746171016655874432115640378001, 79221158875932650245871267067120885513435269403515623231573589152662674279721281832452688860829615565402739803423011677620399001, 0⟩

private noncomputable def tree19_140 : AbundanceTree :=
  .round 35416527816324755373904207002690632171176351357357426751388073 [(832072847051039530081, 1), (5245647644316863182854571, 1), (35416527816324755373904207002690632171176351357357426751388073, 1)]

private theorem checked19_140 : replayAbundance bank 19 127 (10^300) 3 state19_140 tree19_140 = true := by
  decide +kernel

theorem reject19_140 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_140 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_140 checked19_140

@[expose] noncomputable def state19_141 : State := ⟨27093636335568966384087973336955342845594862136002343145198167490210634603664678386698819590403728523367737012770669993746176458361, 28598838354211686738759527411230639670350132254669139986598065684111225414979382741515420678759491219110389069035707215620964039381, 0⟩

private noncomputable def tree19_141 : AbundanceTree :=
  .split 2781054154752782883032125779881884379761516802550397017190960448523488191754317061752510502291353191102716115805637 []

private theorem checked19_141 : replayAbundance bank 19 127 (10^300) 3 state19_141 tree19_141 = true := by
  decide +kernel

theorem reject19_141 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_141 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_141 checked19_141

@[expose] noncomputable def state19_142 : State := ⟨3530869780887683268140728773245357234980768028425961361025370385491740112184184552032976867841004304893806855241286484254995462230063881, 3727029213159221227481880371758988192479699585560736992193446518019059007305528138257031138276615655165685013865802400046939654576178541, 0⟩

private noncomputable def tree19_142 : AbundanceTree :=
  .split 3727029213159221227481880371758988192479699585560736992193446518019059007305528138257031138276615655165685013865802400046939654576178541 []

private theorem checked19_142 : replayAbundance bank 19 127 (10^300) 3 state19_142 tree19_142 = true := by
  decide +kernel

theorem reject19_142 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_142 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_142 checked19_142

@[expose] noncomputable def state19_143 : State := ⟨1274643990900453659798803087141573961828057258261772051330158709162518180498490623283904649290602554066664274742104420816053361865053061041, 1345457545950478863120958814204994737485171550387426054181834193004880301637295657910788240917858251514812290005554666416945215302000453321, 0⟩

private noncomputable def tree19_143 : AbundanceTree :=
  .round 1 [(3961530772257172751242715595128137716110841782476968116923, 1)]

private theorem checked19_143 : replayAbundance bank 19 127 (10^300) 3 state19_143 tree19_143 = true := by
  decide +kernel

theorem reject19_143 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_143 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_143 checked19_143

@[expose] noncomputable def state19_144 : State := ⟨166112879538138021398639817119377060279394249953932395501397613136768531800743796516981737800200615448521754948665790225168890171615579967924161, 175341372845812355920786473626009119183805041618039750807030813866589005789674007434591834344656205195661852445813889682122717403372001077253281, 0⟩

private noncomputable def tree19_144 : AbundanceTree :=
  .round 1 [(45105455053019926096989967321192491775615103323415239629606365036266780745382993922176956968187479923972573050518012187, 1)]

private theorem checked19_144 : replayAbundance bank 19 127 (10^300) 3 state19_144 tree19_144 = true := by
  decide +kernel

theorem reject19_144 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_144 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_144 checked19_144

@[expose] noncomputable def state19_145 : State := ⟨1, 1, 0⟩

private theorem checked19_145 : checkChildren bank 19 127 (10^300) state19_145 19 [state19_32, state19_94, state19_119, state19_120, state19_121, state19_122, state19_123, state19_124, state19_125, state19_126, state19_127, state19_128, state19_129, state19_130, state19_131, state19_132, state19_133, state19_134, state19_135, state19_136, state19_137, state19_138, state19_139, state19_140, state19_141, state19_142, state19_143, state19_144] = true := by
  decide +kernel

theorem reject19_145 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_145 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state19_32, state19_94, state19_119, state19_120, state19_121, state19_122, state19_123, state19_124, state19_125, state19_126, state19_127, state19_128, state19_129, state19_130, state19_131, state19_132, state19_133, state19_134, state19_135, state19_136, state19_137, state19_138, state19_139, state19_140, state19_141, state19_142, state19_143, state19_144] ?_ checked19_145
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject19_32 ho hN hs hav hx hvalid
  · exact reject19_94 ho hN hs hav hx hvalid
  · exact reject19_119 ho hN hs hav hx hvalid
  · exact reject19_120 ho hN hs hav hx hvalid
  · exact reject19_121 ho hN hs hav hx hvalid
  · exact reject19_122 ho hN hs hav hx hvalid
  · exact reject19_123 ho hN hs hav hx hvalid
  · exact reject19_124 ho hN hs hav hx hvalid
  · exact reject19_125 ho hN hs hav hx hvalid
  · exact reject19_126 ho hN hs hav hx hvalid
  · exact reject19_127 ho hN hs hav hx hvalid
  · exact reject19_128 ho hN hs hav hx hvalid
  · exact reject19_129 ho hN hs hav hx hvalid
  · exact reject19_130 ho hN hs hav hx hvalid
  · exact reject19_131 ho hN hs hav hx hvalid
  · exact reject19_132 ho hN hs hav hx hvalid
  · exact reject19_133 ho hN hs hav hx hvalid
  · exact reject19_134 ho hN hs hav hx hvalid
  · exact reject19_135 ho hN hs hav hx hvalid
  · exact reject19_136 ho hN hs hav hx hvalid
  · exact reject19_137 ho hN hs hav hx hvalid
  · exact reject19_138 ho hN hs hav hx hvalid
  · exact reject19_139 ho hN hs hav hx hvalid
  · exact reject19_140 ho hN hs hav hx hvalid
  · exact reject19_141 ho hN hs hav hx hvalid
  · exact reject19_142 ho hN hs hav hx hvalid
  · exact reject19_143 ho hN hs hav hx hvalid
  · exact reject19_144 ho hN hs hav hx hvalid

theorem exclude_19 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) : False :=
  reject19_145 ho hN hs hav hx (root_valid N)

end OddPerfect.IndexComponent.Size300
