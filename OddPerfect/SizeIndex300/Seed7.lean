module

public import OddPerfect.SizeIndex300.Seed7Part05

public section

namespace OddPerfect.IndexComponent.Size300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def state7_229 : State := ⟨33232930569601, 38771752331201, 0⟩

private theorem checked7_229 : checkChildren bank 7 2413 (10^300) state7_229 2767631689 [state7_209, state7_225, state7_226, state7_227, state7_228] = true := by
  decide +kernel

theorem reject7_229 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_229 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state7_209, state7_225, state7_226, state7_227, state7_228] ?_ checked7_229
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact reject7_209 ho hN hs hav hx hvalid
  · exact reject7_225 ho hN hs hav hx hvalid
  · exact reject7_226 ho hN hs hav hx hvalid
  · exact reject7_227 ho hN hs hav hx hvalid
  · exact reject7_228 ho hN hs hav hx hvalid

@[expose] noncomputable def state7_230 : State := ⟨1628413597910449, 1899815864228857, 0⟩

private noncomputable def tree7_230 : AbundanceTree :=
  .split 4534166740403 [
    (2, .split 4721697244987 [
      (2, .split 1139535451 [
        (2, .split 248875867 [
          (2, .split 1226758987 [
            (2, .split 501645871137341719 [
              (2, .abundant [(3, 6), (7, 18), (13, 1), (31, 2), (37, 1), (73, 1)])]),
            (4, .abundant [(3, 4), (7, 18), (11, 2), (31, 2), (37, 1)]),
            (6, .round 3408438715471425110881037183620384923644227021787901037 [(37, 1), (199, 1), (229, 1), (373, 1), (419, 1), (8263, 1), (95239, 1), (101173, 1), (877543, 1), (2404291, 1), (5179063, 1), (3408438715471425110881037183620384923644227021787901037, 1)])]),
          (4, .split 5179063 [
            (2, .abundant [(3, 4), (7, 18), (11, 2), (31, 2), (37, 1)]),
            (4, .split 234784582614581 [
              (1, .abundant [(3, 4), (7, 18), (11, 2), (13, 2)]),
              (2, .round 3064328247661 [(7522609, 1), (3064328247661, 1), (27542445616645459, 1)])]),
            (6, .round 1 [(877543, 1), (238722443, 1), (4887651221531780302199887, 1)])]),
          (6, .split 5179063 [
            (2, .split 3459751 [
              (2, .abundant [(3, 4), (7, 18), (13, 1), (31, 2), (37, 1), (199, 2)]),
              (4, .abundant [(3, 4), (5, 1), (7, 18)])]),
            (4, .round 234784582614581 [(95239, 1), (101173, 1), (877543, 1), (3064328247661, 1), (234784582614581, 1)]),
            (6, .round 1 [(4887651221531780302199887, 1)])]),
          (10, .round 1 [(877543, 1), (5179063, 1)])]),
        (4, .abundant [(3, 2), (5, 1), (7, 18)]),
        (6, .split 1656969594837977353739690486991588347 []),
        (10, .round 3692142095149370820436844005262745777186535626584358433534998783587078595894875429239112261 [(373, 1), (419, 1), (8263, 1), (101173, 1), (248875867, 1), (3692142095149370820436844005262745777186535626584358433534998783587078595894875429239112261, 1)])]),
      (4, .split 183607193268389509183043452655120523611903731 [
        (2, .round 1 [(8263, 1), (2707091, 1)])]),
      (6, .split 3589712147808168668843143777455132584426344389825537023022971 [])]),
    (4, .split 877121779867765511 [
      (2, .split 47003508337164397314469 [
        (1, .split 893736880630277 [
          (2, .round 1 [(19199332631, 1), (75427511821, 1), (388940209901, 1), (798765611798738893165649727007, 1)]),
          (4, .round 1 [(388940209901, 1)])]),
        (2, .round 4189921463676841 [(436801, 1), (4071031, 1), (19199332631, 1), (75427511821, 1), (388940209901, 1), (4189921463676841, 1), (116069233674969187, 1)])]),
      (4, .round 40758660922013695077399221 [(19199332631, 1), (388940209901, 1), (40758660922013695077399221, 1), (315682126203561725019670945027448942251, 1)])]),
    (6, .split 47104141373523161143798381165060954748808467 []),
    (10, .split 84253511 [
      (2, .round 1 [(1119131988031, 1)])])]

private theorem checked7_230 : replayAbundance bank 7 2413 (10^300) 9 state7_230 tree7_230 = true := by
  decide +kernel

theorem reject7_230 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_230 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 9 h tree7_230 checked7_230

@[expose] noncomputable def state7_231 : State := ⟨3909821048582988049, 4561457890013486057, 0⟩

private noncomputable def tree7_231 : AbundanceTree :=
  .split 31479823396757 [
    (1, .split 826632619 [
      (2, .split 401173 [
        (4, .split 2158316902961 [
          (2, .split 1357374612378654607 [
            (2, .abundant [(3, 4), (7, 22), (11, 2), (31, 2), (47, 2)]),
            (4, .round 1 [(3769, 1), (12301, 1), (13441, 1), (22621, 1), (490267, 1)])]),
          (4, .abundant [(3, 2), (5, 2), (7, 22)]),
          (6, .round 1 [(9996504077737561082317365827678627769339126419173, 1)])]),
        (6, .split 15164592286444030129805625073 [
          (2, .abundant [(3, 4), (7, 22), (11, 2), (29, 2), (47, 2)])]),
        (10, .split 113043638752963230361299370354961 [
          (2, .round 1 [(4799752453764001671697, 1)])]),
        (12, .split 1820053456181618552109638593 [
          (2, .abundant [(3, 4), (7, 22), (11, 2), (47, 2), (53, 2), (157, 2)])]),
        (16, .split 54367 [
          (2, .split 3769 [
            (4, .round 1 [(154871, 1), (1303315891, 1)])]),
          (4, .round 1 [(3769, 1), (238441665492001, 1)])]),
        (18, .round 1 [(1230095007558537223828797189886518258819976457625095517104182465314204934271519803519, 1)])]),
      (4, .split 466928254880310715095332431984168361 [
        (2, .split 14794188357930067072624401691 [])]),
      (6, .split 44976791391364736346199 [
        (2, .abundant [(3, 2), (7, 22), (11, 2), (13, 2)])]),
      (10, .round 1 [(2277528080279, 1), (5711068840955501, 1), (3613702003599716627831, 1), (133391206340605613860938179157138409, 1)]),
      (12, .split 5365931799413693 [])]),
    (2, .split 1331399425301563 [
      (2, .split 121201077839481372013 [
        (1, .split 12486437381123 [
          (2, .split 247544928465283 [
            (2, .split 20426163869627441743554911791 []),
            (4, .round 1 [(37514419, 1), (696451621, 1), (708196039, 1)])]),
          (4, .round 1 [(434312371, 1), (696451621, 1), (708196039, 1), (259926373051, 1), (857882691919987983203298851291, 1)]),
          (6, .round 1 [(696451621, 1), (708196039, 1)])]),
        (2, .split 454606544407886068259731100073294991 [
          (2, .round 1 [(10771, 1), (708196039, 1)])]),
        (4, .round 951716390919185678954611825747846674581 [(22980733022201, 1), (318267877505493406716408431, 1), (951716390919185678954611825747846674581, 1)])]),
      (4, .split 522004282403474532166404858744420830406647584961 [
        (1, .round 1 [(1471, 1), (3083, 1), (1439561, 1), (708196039, 1), (6019485806281, 1), (3734972299323400624695812828229917447, 1)])]),
      (6, .split 43940971011446293476010702228598703850875254833527867376821033127867289 [])]),
    (4, .split 120333284591555577359492463316200337575802653745741 [
      (1, .split 88489220524308233511967788264940751 [
        (2, .round 1 [(3437837653671171376635518701439750553902734388489707799281, 1)])]),
      (2, .round 412278083230693196852698258682491046814473355122719676427000595206768103560645733 [(8161, 1), (23594437, 1), (1648480921, 1), (412278083230693196852698258682491046814473355122719676427000595206768103560645733, 1)])]),
    (6, .split 2718959017808956940251287413909769221 [
      (1, .split 52741816378628561218873 [
        (2, .round 1 [(128561120018635149779535020551263223711, 1)])]),
      (2, .round 1 [(24969491, 1)])]),
    (10, .round 30757 [(67, 1), (89, 1), (3083, 1), (30757, 1)])]

private theorem checked7_231 : replayAbundance bank 7 2413 (10^300) 8 state7_231 tree7_231 = true := by
  decide +kernel

theorem reject7_231 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_231 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree7_231 checked7_231

@[expose] noncomputable def state7_232 : State := ⟨459986536544739960976801, 536650959302196621139601, 0⟩

private noncomputable def tree7_232 : AbundanceTree :=
  .split 71316922984999 [
    (4, .split 5082029097175123831385067530894378368541 [
      (1, .split 150515643112410865207507164811 [
        (2, .round 1 [(59, 1), (71, 1), (241, 1), (1931, 1), (51349, 1), (127540261, 1), (154054921, 1)])]),
      (2, .split 502919711681105506251085291328090911734842611233504425078904654133 [])])]

private theorem checked7_232 : replayAbundance bank 7 2413 (10^300) 6 state7_232 tree7_232 = true := by
  decide +kernel

theorem reject7_232 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_232 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree7_232 checked7_232

@[expose] noncomputable def state7_233 : State := ⟨22539340290692258087863249, 26295897005807634435840457, 0⟩

private noncomputable def tree7_233 : AbundanceTree :=
  .split 3999088279399464409 [
    (1, .split 26677735199 [
      (2, .split 46476951307688977 [
        (4, .round 1 [(43, 1), (89, 1), (101, 1), (151, 1), (311, 1), (3917, 1), (15313, 1), (21143, 1), (342241, 1), (411751, 1), (60709918541, 1), (236267520345733871, 1), (13760339565944651953121, 1)]),
        (6, .round 1 [(89, 1), (311, 1), (3917, 1), (15313, 1), (21143, 1)])]),
      (4, .split 38263971129192598399331 [
        (2, .split 3112550548953157693796388858421 [])]),
      (6, .split 43281965600502126982204296288233923002754831903 []),
      (10, .split 51437 [
        (2, .round 1 [(463, 1), (1657, 1), (3917, 1), (21143, 1), (122827, 1)])])]),
    (2, .split 12037386527585149 [
      (1, .abundant [(3, 2), (5, 2), (7, 30)]),
      (2, .split 47678602188292803517 [
        (1, .split 2240060022926953 [
          (2, .split 1820210818824647 [
            (2, .round 1 [(3483038983, 1), (6061190089, 1), (1997660229043, 1), (16165035796957, 1)])]),
          (4, .round 1 [(2513706667, 1), (1820210818824647, 1)])]),
        (2, .split 2208197807420673686085939242339773 [
          (1, .abundant [(3, 4), (7, 30), (13, 2), (31, 2), (61, 2), (83, 2)])]),
        (4, .abundant [(3, 2), (7, 30), (11, 2), (13, 1), (31, 2)])]),
      (4, .split 8380246217855931047127282526496243095412104081458859924231 []),
      (6, .split 2240060022926953 [
        (1, .round 1 [(16630193, 1)])])]),
    (4, .split 1472453695215602977826232022345919614707716196165585951754831019880881 [
      (1, .abundant [(3, 2), (7, 30), (11, 2), (13, 2)])]),
    (6, .split 2574587 [])]

private theorem checked7_233 : replayAbundance bank 7 2413 (10^300) 8 state7_233 tree7_233 = true := by
  decide +kernel

theorem reject7_233 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_233 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree7_233 checked7_233

@[expose] noncomputable def state7_234 : State := ⟨2651730845859653471779023381601, 3093685986836262383742193945201, 0⟩

private noncomputable def tree7_234 : AbundanceTree :=
  .split 4805345109492315767981401 [
    (1, .split 9370586851 [
      (2, .split 87650274787 [
        (2, .split 3808888831208287 [
          (2, .split 4555794473090863 [
            (2, .round 1 [(2887, 1), (4003, 1), (7321, 1), (45613, 1), (330427, 1), (6726821, 1), (265170755671, 1), (427302451730624181446257, 1)])]),
          (4, .round 1 [(18432461, 1), (72185651, 1), (11113661736463671697902708582393451, 1)])]),
        (4, .split 1484842073045503012000416271 [
          (2, .round 1 [(223, 1), (619, 1), (2269, 1), (2887, 1), (7321, 1), (45613, 1), (6726821, 1)])]),
        (6, .round 1 [(3587347, 1), (6726821, 1), (5608387541, 1), (386440989010965584038116180607519355112049, 1)])]),
      (4, .split 28802062877524711 [
        (2, .abundant [(3, 2), (5, 2), (7, 36)]),
        (4, .round 1 [(3691, 1), (2147081, 1), (6726821, 1), (11556431, 1), (2157751381, 1)])]),
      (6, .split 15745321441036702429466089296024992027 []),
      (10, .round 1 [(1052779270758222602886840306171671658582991699955152398722618140489511108023729, 1)])]),
    (2, .split 194307774563247050351722816730060368686862477 [
      (1, .split 118679039172455534915143 [
        (2, .round 1 [(238339, 1), (4143205906183, 1), (58364886340039271526342759525564007, 1)])]),
      (2, .split 6103062888262009 [
        (1, .abundant [(3, 2), (5, 2), (7, 36)])])]),
    (4, .round 1 [(2268500435671871, 1), (18937002577126532099173623699263783311238456422353508197844826911, 1)])]

private theorem checked7_234 : replayAbundance bank 7 2413 (10^300) 8 state7_234 tree7_234 = true := by
  decide +kernel

theorem reject7_234 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_234 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree7_234 checked7_234

@[expose] noncomputable def state7_235 : State := ⟨6366805760909027985741435139224001, 7427940054393865983365007662428001, 0⟩

private noncomputable def tree7_235 : AbundanceTree :=
  .split 4362139336229068656094783 [
    (2, .split 41983564756831 [
      (2, .split 21350651564197 [
        (1, .abundant [(3, 2), (7, 40), (11, 2), (13, 2)]),
        (2, .split 26086289746843232323 []),
        (4, .round 786631291189 [(29845969, 1), (522541321, 1), (72381100807, 1), (786631291189, 1)])]),
      (4, .abundant [(3, 2), (5, 1), (7, 40)]),
      (6, .round 1 [(72381100807, 1)])]),
    (4, .split 20515909 [
      (1, .split 996311 [
        (2, .split 992636605033 []),
        (4, .round 1 [(6871, 1), (15661, 1), (160681, 1)])]),
      (2, .split 140300847537397 [
        (1, .round 1 [(160681, 1), (996311, 1), (70150423768699, 1)])]),
      (4, .round 1 [(5714804572329308953256996051, 1)])])]

private theorem checked7_235 : replayAbundance bank 7 2413 (10^300) 6 state7_235 tree7_235 = true := by
  decide +kernel

theorem reject7_235 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_235 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree7_235 checked7_235

@[expose] noncomputable def state7_236 : State := ⟨311973482284542371301330321821976049, 363969062665299433184885375458972057, 0⟩

private noncomputable def tree7_236 : AbundanceTree :=
  .split 2192537062271178641 [
    (1, .split 166003607842448777 [
      (4, .split 272977983247258853313096765919753230104153145571 []),
      (6, .round 1 [(3435095312634990101694422917052410155542761242440302019827342368859237724357909837, 1)])]),
    (4, .split 166003607842448777 [
      (1, .abundant [(3, 2), (5, 2), (7, 42)])]),
    (6, .split 166003607842448777 [
      (1, .round 1 [(1697041, 1), (5434413581, 1)])])]

private theorem checked7_236 : replayAbundance bank 7 2413 (10^300) 5 state7_236 tree7_236 = true := by
  decide +kernel

theorem reject7_236 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_236 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree7_236 checked7_236

@[expose] noncomputable def state7_237 : State := ⟨749048330965186233494494102694564493649, 873889719459383939076909786476991909257, 0⟩

private noncomputable def tree7_237 : AbundanceTree :=
  .split 63681511996418550459487 [
    (2, .split 701941337793204512881 [
      (1, .split 13722816749522711 [
        (2, .split 188315699540981077255463054312233 []),
        (4, .abundant [(3, 2), (5, 2), (7, 46)])]),
      (4, .abundant [(3, 2), (5, 1), (7, 46)])]),
    (4, .split 75006313962995199466290696763540465726269266306912771649378970081 [])]

private theorem checked7_237 : replayAbundance bank 7 2413 (10^300) 6 state7_237 tree7_237 = true := by
  decide +kernel

theorem reject7_237 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_237 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree7_237 checked7_237

@[expose] noncomputable def state7_238 : State := ⟨88124787089723195184393736687912818113311201, 102812251604677061048459359469231621132196401, 0⟩

private noncomputable def tree7_238 : AbundanceTree :=
  .split 38904276017035188056372051839841219 [
    (2, .split 24695054790253283552629 [
      (1, .split 2469505479025328355263 [
        (2, .round 1 [(4120717024194879943, 1), (187115016600310232389, 1)])]),
      (2, .round 1 [(4120717024194879943, 1), (100913820647592380852971721378050891087, 1)])])]

private theorem checked7_238 : replayAbundance bank 7 2413 (10^300) 6 state7_238 tree7_238 = true := by
  decide +kernel

theorem reject7_238 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_238 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree7_238 checked7_238

@[expose] noncomputable def state7_239 : State := ⟨10367793076318844190248738727596255138212949486449, 12095758589038651555290195182195630994581774400857, 0⟩

private noncomputable def tree7_239 : AbundanceTree :=
  .split 354639323684545612988577649 [
    (1, .split 3660120919867 [
      (2, .abundant [(3, 2), (5, 2), (7, 58)]),
      (4, .split 5952234231764158082931689063328193260384466991 []),
      (6, .split 459257 [
        (2, .split 16453 [
          (2, .abundant [(3, 2), (5, 2), (7, 58)])])])]),
    (2, .split 617737193026586407 [
      (2, .split 138629752232561610678949 [
        (1, .abundant [(3, 2), (5, 2), (7, 58)]),
        (2, .round 1 [(58379697387568483, 1)])])]),
    (4, .split 459257 [
      (1, .round 1 [(101, 1), (151, 1), (241, 1), (76543, 1)])])]

private theorem checked7_239 : replayAbundance bank 7 2413 (10^300) 7 state7_239 tree7_239 = true := by
  decide +kernel

theorem reject7_239 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_239 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree7_239 checked7_239

@[expose] noncomputable def state7_240 : State := ⟨508021860739623365322188197652216501772434524836001, 592692170862893926209219563927585918734506945642001, 0⟩

private noncomputable def tree7_240 : AbundanceTree :=
  .split 1914662449813727660680530326064591907 [
    (2, .split 2013142392491326300328063210982871195846973763417574233794643495065617 [
      (1, .round 1 [(2884158155431699570670577666164571913820879317217155062743042256541, 1)])])]

private theorem checked7_240 : replayAbundance bank 7 2413 (10^300) 5 state7_240 tree7_240 = true := by
  decide +kernel

theorem reject7_240 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_240 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree7_240 checked7_240

@[expose] noncomputable def state7_241 : State := ⟨59768263894155949306790119265585619217025149412430681649, 69729641209848607524588472476516555753196007647835795257, 0⟩

private noncomputable def tree7_241 : AbundanceTree :=
  .split 10052011757370829033540932021825161 [
    (1, .split 530319574500328599169 [
      (2, .split 166344512921281831 [
        (2, .round 1 [(1795966537, 1), (37470919266199, 1), (136541081076043110339637441, 1)])]),
      (4, .round 1 [(206244761, 1), (1795966537, 1)])]),
    (2, .split 2333446723349033463365937692074786415652363449384803 [])]

private theorem checked7_241 : replayAbundance bank 7 2413 (10^300) 6 state7_241 tree7_241 = true := by
  decide +kernel

theorem reject7_241 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_241 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree7_241 checked7_241

@[expose] noncomputable def state7_242 : State := ⟨143503601609868434285603076356671071740077383739246066639249, 167420868544846506666536922416116250363423614362453744412457, 0⟩

private noncomputable def tree7_242 : AbundanceTree :=
  .split 169002145064468556765676975247413756542145739 [
    (2, .split 990643452963163 [])]

private theorem checked7_242 : replayAbundance bank 7 2413 (10^300) 4 state7_242 tree7_242 = true := by
  decide +kernel

theorem reject7_242 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_242 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_242 checked7_242

@[expose] noncomputable def state7_243 : State := ⟨7031676478883553279994550741476882515263791803223057265323201, 8203622558697478826660309198389696267807757103760233476210401, 0⟩

private noncomputable def tree7_243 : AbundanceTree :=
  .split 7222605228105536202757606969 [
    (1, .split 1958423494433591 [
      (2, .split 1512597319 [
        (2, .abundant [(3, 2), (5, 2), (7, 72)]),
        (4, .round 1 [(23469599, 1), (5234718177761065196295179434515790961, 1)]),
        (6, .round 1 [(23469599, 1)])]),
      (4, .round 1 [(215279145262078789936455744164015584347037002891877271, 1)])]),
    (2, .split 10465170479478397824116797 [
      (1, .round 1 [(439, 1), (1789, 1), (11317, 1), (3675989, 1), (6766399, 1), (13475851, 1), (24756481, 1), (35142721, 1), (2343895350169, 1), (1958423494433591, 1)])])]

private theorem checked7_243 : replayAbundance bank 7 2413 (10^300) 6 state7_243 tree7_243 = true := by
  decide +kernel

theorem reject7_243 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_243 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree7_243 checked7_243

@[expose] noncomputable def state7_244 : State := ⟨827269706064171159838078900184013751038269841857389464208009274449, 965147990408199686477758716881349376211314815500287708242677486857, 0⟩

private noncomputable def tree7_244 : AbundanceTree :=
  .split 1056836588644853738704557482552056406147 [
    (2, .split 913242407367610843676812931 [])]

private theorem checked7_244 : replayAbundance bank 7 2413 (10^300) 4 state7_244 tree7_244 = true := by
  decide +kernel

theorem reject7_244 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_244 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_244 checked7_244

@[expose] noncomputable def state7_245 : State := ⟨1986274564260074954771227439341817016242885890299592103563430267952049, 2317320324970087447233098679232119852283366872016190787490668645944057, 0⟩

private noncomputable def tree7_245 : AbundanceTree :=
  .split 18624275418445601 [
    (1, .split 303567967057423 [
      (2, .split 10113283283692423 [
        (2, .round 1 [(7685542369, 1), (274427186197, 1), (62911130477521, 1), (126611896219018562707, 1)])]),
      (4, .round 1 [(66733, 1), (76066181, 1), (7685542369, 1), (274427186197, 1), (62911130477521, 1)])]),
    (2, .split 51242965705734537575645799187 [
      (2, .round 62911130477521 [(76066181, 1), (7685542369, 1), (62911130477521, 1), (303567967057423, 1)])]),
    (4, .round 62911130477521 [(66733, 1), (121921, 1), (2748401, 1), (76066181, 1), (7685542369, 1), (62911130477521, 1), (303567967057423, 1)])]

private theorem checked7_245 : replayAbundance bank 7 2413 (10^300) 6 state7_245 tree7_245 = true := by
  decide +kernel

theorem reject7_245 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_245 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree7_245 checked7_245

@[expose] noncomputable def state7_246 : State := ⟨233683216210633558353880137011125430143959282107856711392134007594290612801, 272630418912405818079526826512979668501285829125832829957489675526672381601, 0⟩

private noncomputable def tree7_246 : AbundanceTree :=
  .split 8166146875847876762859119015147004762656450569 [
    (1, .split 790214414220108085265284027441894231873 []),
    (2, .round 1 [(22621381401823741299545786610202403920654214219713584092893551450591633838028394716743, 1)])]

private theorem checked7_246 : replayAbundance bank 7 2413 (10^300) 4 state7_246 tree7_246 = true := by
  decide +kernel

theorem reject7_246 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_246 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_246 checked7_246

@[expose] noncomputable def state7_247 : State := ⟨1347137238494276547832006567721872890819326613454654477690085519113574118965817601, 1571660111576655972470674329008851705955881049030430223971766438965836472126787201, 0⟩

private noncomputable def tree7_247 : AbundanceTree :=
  .split 4160924156784953821413999107825795646911807584554735726748631757909547764679 []

private theorem checked7_247 : replayAbundance bank 7 2413 (10^300) 3 state7_247 tree7_247 = true := by
  decide +kernel

theorem reject7_247 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_247 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_247 checked7_247

@[expose] noncomputable def state7_248 : State := ⟨3234476509624757991344647769100216810857203198904625400933895331391691459636928060001, 3773555927895550989902089063950252946000070398722062967756211219956973369576416070001, 0⟩

private noncomputable def tree7_248 : AbundanceTree :=
  .split 1226962153072980952980067096888460031879516017670288348423584305043494594529 [
    (1, .abundant [(3, 2), (5, 2), (7, 100)])]

private theorem checked7_248 : replayAbundance bank 7 2413 (10^300) 4 state7_248 tree7_248 = true := by
  decide +kernel

theorem reject7_248 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_248 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_248 checked7_248

@[expose] noncomputable def state7_249 : State := ⟨158489348971613141575887740685910623732002956746326644645760871238192881522209474940049, 184904240466881998505202364133562394354003449537381085420054349777891695109244387430057, 0⟩

private noncomputable def tree7_249 : AbundanceTree :=
  .split 10316589882658148664018432412741304154103858145253645339510927287724805842171756259 []

private theorem checked7_249 : replayAbundance bank 7 2413 (10^300) 3 state7_249 tree7_249 = true := by
  decide +kernel

theorem reject7_249 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_249 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_249 checked7_249

@[expose] noncomputable def state7_250 : State := ⟨380532926880843152923706465386871407580539099147930273794471851842901108534824949331057649, 443955081360983678410990876284683308843962282339251986093550493816717959957295774219567257, 0⟩

private noncomputable def tree7_250 : AbundanceTree :=
  .split 1206506689449517154664984054683391885701717268373 [
    (1, .round 1 [(3467398618193, 1), (227109283745807808529, 1), (1620221568881364582821, 1), (7344605686536566602699, 1)])]

private theorem checked7_250 : replayAbundance bank 7 2413 (10^300) 4 state7_250 tree7_250 = true := by
  decide +kernel

theorem reject7_250 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_250 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_250 checked7_250

@[expose] noncomputable def state7_251 : State := ⟨18646113417161314493261616803956698971446415858248583415929120740302154318206422517221824801, 21753798986688200242138552937949482133354151834623347318583974197019180037907492936758795601, 0⟩

private noncomputable def tree7_251 : AbundanceTree :=
  .split 23540782932240399632107200158745339309941271547 []

private theorem checked7_251 : replayAbundance bank 7 2413 (10^300) 3 state7_251 tree7_251 = true := by
  decide +kernel

theorem reject7_251 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_251 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_251 checked7_251

@[expose] noncomputable def state7_252 : State := ⟨44769318314604316098321141946300034230442844475654848781645818897465472518013620463849601347201, 52230871367038368781374665604016706602183318554930656911920122047043051271015890541157868238401, 0⟩

private noncomputable def tree7_252 : AbundanceTree :=
  .split 230091944348186646613985311030910601771732680858725360845463092718251327185092028815673428363 []

private theorem checked7_252 : replayAbundance bank 7 2413 (10^300) 3 state7_252 tree7_252 = true := by
  decide +kernel

theorem reject7_252 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_252 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_252 checked7_252

@[expose] noncomputable def state7_253 : State := ⟨30363584636685952977761483300842317761884830962342835712214251124211986029046959176627705345482312365245649, 35424182076133611807388397184316037388865636122733308330916626311580650367221452372732322903062697759453257, 0⟩

private noncomputable def tree7_253 : AbundanceTree :=
  .split 245341643198368582843352144598480744468850041775022125500767047213117 [
    (1, .round 1 [(554351226505275380676162672703, 1)])]

private theorem checked7_253 : replayAbundance bank 7 2413 (10^300) 4 state7_253 tree7_253 = true := by
  decide +kernel

theorem reject7_253 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_253 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_253 checked7_253

@[expose] noncomputable def state7_254 : State := ⟨72902966712682973099605321405322404946285479140585148545026416949232978455741748983083120534503031988954803249, 85053461164796801949539541639542805770666392330682673302530819774105141531698707146930307290253537320447270457, 0⟩

private noncomputable def tree7_254 : AbundanceTree :=
  .split 85053461164796801949539541639542805770666392330682673302530819774105141531698707146930307290253537320447270457 []

private theorem checked7_254 : replayAbundance bank 7 2413 (10^300) 3 state7_254 tree7_254 = true := by
  decide +kernel

theorem reject7_254 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_254 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_254 checked7_254

@[expose] noncomputable def state7_255 : State := ⟨8576961130780439102195466458014775619525540335410702141173812927660310682339561026110746047763747210468543647441601, 10006454652577178952561377534350571556113130391312485831369448415603695796062821197129203722391038412213300922015201, 0⟩

private noncomputable def tree7_255 : AbundanceTree :=
  .round 18142811321510255442702751468712154533804561 [(2741, 1), (213721, 1), (251533, 1), (57162922399254002352124124899, 1), (65480203458464902965944539043, 1), (18142811321510255442702751468712154533804561, 1)]

private theorem checked7_255 : replayAbundance bank 7 2413 (10^300) 3 state7_255 tree7_255 = true := by
  decide +kernel

theorem reject7_255 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_255 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_255 checked7_255

@[expose] noncomputable def state7_256 : State := ⟨420271095408241516007577856442724005356751476435124404917516833455355223434638490279426556340423613312958638724638449, 490316277976281768675507499183178006249543389174311805737102972364581094007078238659330982397160882198451745178744857, 0⟩

private noncomputable def tree7_256 : AbundanceTree :=
  .split 36907186032510520494090542644478414425042667765511537140671634321685208913758955545681985719375774106220917 []

private theorem checked7_256 : replayAbundance bank 7 2413 (10^300) 3 state7_256 tree7_256 = true := by
  decide +kernel

theorem reject7_256 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_256 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_256 checked7_256

@[expose] noncomputable def state7_257 : State := ⟨118716182322945778886378040885544717651425707137129398625052391991992997123150142766665096079473688936057706400443288316248801, 138502212710103408700774381033135503926663324993317631729227790657325163310341833227775945426052637092067324133850503035623601, 0⟩

private noncomputable def tree7_257 : AbundanceTree :=
  .split 138502212710103408700774381033135503926663324993317631729227790657325163310341833227775945426052637092067324133850503035623601 []

private theorem checked7_257 : replayAbundance bank 7 2413 (10^300) 3 state7_257 tree7_257 = true := by
  decide +kernel

theorem reject7_257 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_257 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_257 checked7_257

@[expose] noncomputable def state7_258 : State := ⟨5817092933824343165432524003391691164919859649719340532627567207607656859034356995566589707894210757866827613621721127496191249, 6786608422795067026337944670623639692406502924672563954732161742208933002206749828161021325876579217511298882558674648745556457, 0⟩

private noncomputable def tree7_258 : AbundanceTree :=
  .round 1 [(2765290231620224523441852435124159094999555183731339173137659, 1)]

private theorem checked7_258 : replayAbundance bank 7 2413 (10^300) 3 state7_258 tree7_258 = true := by
  decide +kernel

theorem reject7_258 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_258 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_258 checked7_258

@[expose] noncomputable def state7_259 : State := ⟨684375166571500149069971016475029073861656567929830694323100654407833221808533066171413712544046001452274401914981868928799404253601, 798437694333416840581632852554200586171932662584802476710284096809138758776621910533315997968053668360986802234145513750265971629201, 0⟩

private noncomputable def tree7_259 : AbundanceTree :=
  .split 30888375309332174699747764157798083891019286829175554176515308211775675085491164240495874534303554491469173279661 []

private theorem checked7_259 : replayAbundance bank 7 2413 (10^300) 3 state7_259 tree7_259 = true := by
  decide +kernel

theorem reject7_259 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_259 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_259 checked7_259

@[expose] noncomputable def state7_260 : State := ⟨80516053971970421037933020117270695510750033560376651356418468890427170712552106702000651867094468024858631110895701897604321111031904049, 93935396300632157877588523470149144762541705820439426582488213705498365831310791152334093844943546029001736296044985547205041296203888057, 0⟩

private noncomputable def tree7_260 : AbundanceTree :=
  .round 1 [(7354840357696348186997141461981606470291584313584199443, 1)]

private theorem checked7_260 : replayAbundance bank 7 2413 (10^300) 3 state7_260 tree7_260 = true := by
  decide +kernel

theorem reject7_260 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_260 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_260 checked7_260

@[expose] noncomputable def state7_261 : State := ⟨193319045586700980912077181301566939921310830578464339906760743805915636880837608191503565132893817727685573297260580256147974987587601621649, 225538886517817811064090044851828096574862635674875063224554201106901576360977209556754159321709454015633168846804010298839304152185535225257, 0⟩

private noncomputable def tree7_261 : AbundanceTree :=
  .round 1 [(494816894793945434195756741367539, 1)]

private theorem checked7_261 : replayAbundance bank 7 2413 (10^300) 3 state7_261 tree7_261 = true := by
  decide +kernel

theorem reject7_261 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_261 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_261 checked7_261

@[expose] noncomputable def state7_262 : State := ⟨22743792394229783703324968302948048914802297906725751125690494748022168763393663766122202934319824761844480012849410006555553109314693743185383201, 26534424459934747653879129686772723733936014224513376313305577206025863557292607727142570090039795555485226681657645007648145294200476033716280401, 0⟩

private noncomputable def tree7_262 : AbundanceTree :=
  .round 2795470346154518601095703317279482175240316831812233463788382148771684556965122038863701628739457 [(9491935586594867440367391646466925926211879363793, 1), (2795470346154518601095703317279482175240316831812233463788382148771684556965122038863701628739457, 1)]

private theorem checked7_262 : replayAbundance bank 7 2413 (10^300) 3 state7_262 tree7_262 = true := by
  decide +kernel

theorem reject7_262 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_262 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_262 checked7_262

@[expose] noncomputable def state7_263 : State := ⟨1, 1, 0⟩

private theorem checked7_263 : checkChildren bank 7 2413 (10^300) state7_263 7 [state7_26, state7_79, state7_170, state7_208, state7_229, state7_230, state7_231, state7_232, state7_233, state7_234, state7_235, state7_236, state7_237, state7_238, state7_239, state7_240, state7_241, state7_242, state7_243, state7_244, state7_245, state7_246, state7_247, state7_248, state7_249, state7_250, state7_251, state7_252, state7_253, state7_254, state7_255, state7_256, state7_257, state7_258, state7_259, state7_260, state7_261, state7_262] = true := by
  decide +kernel

theorem reject7_263 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_263 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state7_26, state7_79, state7_170, state7_208, state7_229, state7_230, state7_231, state7_232, state7_233, state7_234, state7_235, state7_236, state7_237, state7_238, state7_239, state7_240, state7_241, state7_242, state7_243, state7_244, state7_245, state7_246, state7_247, state7_248, state7_249, state7_250, state7_251, state7_252, state7_253, state7_254, state7_255, state7_256, state7_257, state7_258, state7_259, state7_260, state7_261, state7_262] ?_ checked7_263
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject7_26 ho hN hs hav hx hvalid
  · exact reject7_79 ho hN hs hav hx hvalid
  · exact reject7_170 ho hN hs hav hx hvalid
  · exact reject7_208 ho hN hs hav hx hvalid
  · exact reject7_229 ho hN hs hav hx hvalid
  · exact reject7_230 ho hN hs hav hx hvalid
  · exact reject7_231 ho hN hs hav hx hvalid
  · exact reject7_232 ho hN hs hav hx hvalid
  · exact reject7_233 ho hN hs hav hx hvalid
  · exact reject7_234 ho hN hs hav hx hvalid
  · exact reject7_235 ho hN hs hav hx hvalid
  · exact reject7_236 ho hN hs hav hx hvalid
  · exact reject7_237 ho hN hs hav hx hvalid
  · exact reject7_238 ho hN hs hav hx hvalid
  · exact reject7_239 ho hN hs hav hx hvalid
  · exact reject7_240 ho hN hs hav hx hvalid
  · exact reject7_241 ho hN hs hav hx hvalid
  · exact reject7_242 ho hN hs hav hx hvalid
  · exact reject7_243 ho hN hs hav hx hvalid
  · exact reject7_244 ho hN hs hav hx hvalid
  · exact reject7_245 ho hN hs hav hx hvalid
  · exact reject7_246 ho hN hs hav hx hvalid
  · exact reject7_247 ho hN hs hav hx hvalid
  · exact reject7_248 ho hN hs hav hx hvalid
  · exact reject7_249 ho hN hs hav hx hvalid
  · exact reject7_250 ho hN hs hav hx hvalid
  · exact reject7_251 ho hN hs hav hx hvalid
  · exact reject7_252 ho hN hs hav hx hvalid
  · exact reject7_253 ho hN hs hav hx hvalid
  · exact reject7_254 ho hN hs hav hx hvalid
  · exact reject7_255 ho hN hs hav hx hvalid
  · exact reject7_256 ho hN hs hav hx hvalid
  · exact reject7_257 ho hN hs hav hx hvalid
  · exact reject7_258 ho hN hs hav hx hvalid
  · exact reject7_259 ho hN hs hav hx hvalid
  · exact reject7_260 ho hN hs hav hx hvalid
  · exact reject7_261 ho hN hs hav hx hvalid
  · exact reject7_262 ho hN hs hav hx hvalid

theorem exclude_7 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) : False :=
  reject7_263 ho hN hs hav hx (root_valid N)

end OddPerfect.IndexComponent.Size300
