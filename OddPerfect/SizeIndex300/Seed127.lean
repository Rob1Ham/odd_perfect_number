module

public import OddPerfect.SizeIndex300.Seed127Part02

public section

namespace OddPerfect.IndexComponent.Size300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def state127_103 : State := ⟨37961522478248568780507757313529223381, 38263482669061467385132342009800561070, 162709⟩

private noncomputable def tree127_103 : AbundanceTree :=
  .split 8970971 [
    (2, .split 1501489387 [
      (2, .abundant [(3, 2), (5, 2), (7, 2)]),
      (4, .split 6926451032919380680600528880321 [
        (2, .split 1964041 [
          (2, .abundant [(3, 2), (5, 2), (7, 4)]),
          (4, .abundant [(5, 2), (7, 2), (11, 2), (13, 2), (19, 2), (31, 2), (41, 2), (43, 2), (53, 2)])])]),
      (6, .split 1964041 [
        (2, .abundant [(3, 2), (5, 2), (7, 4)]),
        (4, .abundant [(5, 2), (7, 2), (11, 2), (13, 2), (19, 2), (31, 2), (41, 2), (43, 2), (53, 2)]),
        (6, .abundant [(5, 2), (7, 2), (11, 2), (13, 2), (19, 2), (29, 2), (31, 2), (43, 4), (53, 2)])]),
      (10, .abundant [(5, 2), (7, 2), (11, 2), (13, 2), (19, 2), (23, 2), (31, 2), (43, 2)]),
      (12, .round 1 [(1964041, 1)])]),
    (4, .split 11232875364041 [
      (2, .split 43208760870154528381 [
        (2, .abundant [(3, 2), (5, 2), (7, 2)]),
        (4, .round 1 [(5405967912750465340092257739308075946643484287840514164962968461618901, 1)])]),
      (4, .split 73844708644354283096117087296721 []),
      (6, .split 12926572181 [
        (2, .round 1 [(347393489321267503, 1)])])]),
    (6, .split 18877888966421647 [
      (2, .abundant [(3, 2), (5, 2), (7, 2)]),
      (4, .round 1 [(7, 1), (11, 1), (29, 1), (43, 1), (53, 1), (281, 1), (307, 1), (617, 1), (1021, 1), (1124131, 1), (1964041, 1), (16141189, 1), (85044793, 1)])]),
    (10, .split 1964041 [
      (2, .abundant [(3, 2), (5, 2), (7, 2)]),
      (4, .split 79028782411 [
        (2, .abundant [(3, 2), (5, 2), (7, 2)])]),
      (6, .round 1 [(1021, 1), (1583, 1), (26209, 1), (154267, 1), (343253, 1), (487247779146731, 1)])]),
    (12, .split 1964041 [
      (2, .abundant [(3, 2), (5, 2), (7, 2)]),
      (4, .round 1 [(281, 1), (307, 1), (431, 1), (1021, 1), (65287, 1), (16267271, 1), (79028782411, 1)]),
      (6, .round 1 [(487247779146731, 1)])]),
    (16, .round 1 [(53, 1), (137, 1), (281, 1), (307, 1), (647, 1), (1021, 1), (1964041, 1)])]

private theorem checked127_103 : replayAbundance bank 127 1 (10^300) 7 state127_103 tree127_103 = true := by
  decide +kernel

theorem reject127_103 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_103 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree127_103 checked127_103

@[expose] noncomputable def state127_104 : State := ⟨283073022395270246878619852375041458015673079029, 285324691408425257914583950160633544975733682810, 162709⟩

private noncomputable def tree127_104 : AbundanceTree :=
  .split 95281244588123623 [
    (2, .abundant [(3, 2), (5, 2), (7, 2)]),
    (4, .split 316037 [
      (2, .split 41808163 [
        (2, .abundant [(3, 2), (5, 2), (7, 2)]),
        (4, .round 1 [(916053560831, 1), (18426587368747531, 1)])]),
      (4, .split 74451297871 [
        (2, .abundant [(3, 2), (5, 2), (7, 2)])]),
      (6, .round 1 [(307, 1), (1499, 1), (2339, 1), (269389, 1), (12154901079250302052639, 1)])]),
    (6, .round 1 [(5, 1), (7, 3), (43, 1), (53, 1), (307, 1), (2339, 1), (11789, 1), (11887, 1), (55147, 1), (316037, 1)])]

private theorem checked127_104 : replayAbundance bank 127 1 (10^300) 6 state127_104 tree127_104 = true := by
  decide +kernel

theorem reject127_104 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_104 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree127_104 checked127_104

@[expose] noncomputable def state127_105 : State := ⟨15740125910376452637682192182361600976781576823877409313238605834549, 15865328776674548677795632045825644947104738639024561148055379275410, 162709⟩

private noncomputable def tree127_105 : AbundanceTree :=
  .split 331 [
    (2, .abundant [(3, 2), (5, 2), (7, 2)]),
    (4, .split 63601 [
      (2, .abundant [(3, 2), (5, 2), (7, 2)]),
      (4, .split 50408381 [
        (2, .split 11709700117279 [
          (2, .abundant [(3, 2), (5, 4), (7, 2)]),
          (4, .round 1 [(1381, 1), (4231, 1), (37861, 1)])]),
        (4, .split 5358262160224805504778924521 []),
        (6, .round 1 [(105585173, 1), (155386601264650814573919871784675632919, 1)])]),
      (6, .split 1539295634290340976189184549 [
        (2, .abundant [(3, 2), (5, 2), (7, 2)])]),
      (10, .split 16087764908674140456316746782137183300115891 []),
      (12, .round 1 [(30963286783037373883, 1), (4703101461919824644415984264263, 1)]),
      (16, .round 1 [(317931101264175933944784154075254966609795081849052168303, 1)])]),
    (6, .split 604842197 [
      (2, .split 365834083876629007 [
        (2, .abundant [(3, 2), (5, 2), (7, 2)])]),
      (4, .split 2291041 [
        (2, .abundant [(3, 2), (5, 2), (7, 2)]),
        (4, .split 45538241939667589005961 []),
        (6, .round 1 [(39355378835534062769123938241, 1)])]),
      (6, .split 2180921 [
        (2, .split 1478526139 [
          (2, .abundant [(3, 2), (5, 2), (7, 2)])]),
        (4, .round 1 [(969550980294955841, 1)])])]),
    (10, .split 703207451121161180833 [
      (2, .abundant [(3, 2), (5, 2), (7, 2)])]),
    (12, .split 80037421623539251 [
      (2, .abundant [(3, 2), (5, 2), (7, 2)])]),
    (16, .split 65687724032159167 [
      (2, .abundant [(3, 2), (5, 2), (7, 2)])]),
    (18, .split 8080363351283173500917653281271 []),
    (22, .split 4230633157300118626197785006849 []),
    (28, .round 1 [(55360151897245468424405269776668510649162316699, 1)]),
    (30, .round 1 [(35166923403152020033228542959565452947, 1)])]

private theorem checked127_105 : replayAbundance bank 127 1 (10^300) 7 state127_105 tree127_105 = true := by
  decide +kernel

theorem reject127_105 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_105 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree127_105 checked127_105

@[expose] noncomputable def state127_106 : State := ⟨117371610079268226506033734301576319685918928183342306604672437293609318400341, 118305227897043066557333725642134418175186272059809739776645689606972256315870, 162709⟩

private noncomputable def tree127_106 : AbundanceTree :=
  .split 14327 [
    (2, .split 6621847 [
      (2, .abundant [(3, 2), (5, 2), (7, 2)]),
      (4, .split 356027162308028801 [
        (2, .round 1 [(307, 1), (6481, 1), (833281, 1), (17263699, 1), (10183501824554455211643457, 1)])]),
      (6, .split 6105161248358627141 [
        (2, .round 1 [(332785674209261096199764636756341, 1)])]),
      (10, .split 307 [
        (2, .abundant [(3, 2), (5, 2), (7, 2)])])]),
    (4, .split 372221190881 [
      (2, .split 2885970942193 [
        (2, .abundant [(3, 2), (5, 2), (7, 2)]),
        (4, .round 1 [(317931301, 1)])]),
      (4, .round 1 [(251, 1), (307, 1), (1801, 1), (1268098376312517998382609230156218760681, 1)])]),
    (6, .split 10777903506787327 [
      (2, .abundant [(3, 2), (5, 2), (7, 2)])]),
    (10, .split 307 [
      (2, .abundant [(3, 2), (5, 2), (7, 2)]),
      (4, .split 5231 [
        (2, .split 3909799 [
          (2, .abundant [(3, 2), (5, 2), (7, 2)]),
          (4, .round 1 [(26456251, 1)])]),
        (4, .split 249216868661 []),
        (6, .round 1 [(288624373085970303047, 1)])]),
      (6, .split 1274564409623 [
        (2, .round 1 [(1220002291, 1), (332144352187, 1)])]),
      (10, .split 12135499643725165489 []),
      (12, .round 1 [(20390887542170848365521, 1)]),
      (16, .round 1 [(598357843411082684037656428789, 1)])]),
    (12, .split 307 [
      (2, .abundant [(3, 2), (5, 2), (7, 2)]),
      (4, .split 5231 [
        (2, .split 3909799 [
          (2, .abundant [(3, 2), (5, 2), (7, 2)])]),
        (4, .round 1 [(1051, 1), (1621, 1), (249216868661, 1)]),
        (6, .round 1 [(288624373085970303047, 1)])]),
      (6, .split 1274564409623 []),
      (10, .round 1 [(12135499643725165489, 1)]),
      (12, .round 1 [(20390887542170848365521, 1)])]),
    (16, .split 2687 [
      (2, .split 555589 []),
      (4, .round 1 [(13493071, 1)])]),
    (18, .split 1597 [
      (2, .abundant [(3, 2), (5, 2), (7, 2)])])]

private theorem checked127_106 : replayAbundance bank 127 1 (10^300) 7 state127_106 tree127_106 = true := by
  decide +kernel

theorem reject127_106 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_106 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree127_106 checked127_106

@[expose] noncomputable def state127_107 : State := ⟨6526386390758231486186789347518969650139530195895016864156808315607046654941208909213224248790421, 6578299716442185530625098420016525566928176063958244116889164944995401542851561279020786878401270, 162709⟩

private noncomputable def tree127_107 : AbundanceTree :=
  .split 204511 [
    (2, .abundant [(3, 2), (5, 2), (7, 2)]),
    (4, .split 111741820038178391 [
      (2, .round 1 [(2647, 1), (185414358274917436447104799, 1)])]),
    (6, .split 307 [
      (2, .abundant [(3, 2), (5, 2), (7, 2)]),
      (4, .split 5231 [
        (2, .split 3909799 [
          (2, .abundant [(3, 2), (5, 2), (7, 2)])]),
        (4, .round 1 [(1051, 1), (1621, 1), (249216868661, 1)]),
        (6, .round 1 [(288624373085970303047, 1)])]),
      (6, .split 1274564409623 []),
      (10, .round 1 [(12135499643725165489, 1)]),
      (12, .round 1 [(20390887542170848365521, 1)])]),
    (10, .split 307 [
      (2, .abundant [(3, 2), (5, 2), (7, 2)])])]

private theorem checked127_107 : replayAbundance bank 127 1 (10^300) 7 state127_107 tree127_107 = true := by
  decide +kernel

theorem reject127_107 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_107 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree127_107 checked127_107

@[expose] noncomputable def state127_108 : State := ⟨48666223068630922847220073365908066284998971280931686853384324791647513983123217101773764818203930443006389, 49053332463739274065477447053000966298556770660025616011154467913940961542996775804513606026042133106364610, 162709⟩

private noncomputable def tree127_108 : AbundanceTree :=
  .split 307 [
    (2, .abundant [(3, 2), (5, 2), (7, 2)]),
    (4, .split 5231 [
      (2, .split 3909799 [
        (2, .abundant [(3, 2), (5, 2), (7, 2)]),
        (4, .round 1 [(11551, 1), (5396621, 1), (12881171, 1), (26456251, 1)])]),
      (4, .split 249216868661 [
        (2, .round 1 [(62109047625443340801583, 1)])]),
      (6, .split 288624373085970303047 []),
      (10, .round 1 [(206370597455266282853, 1)])]),
    (6, .split 1274564409623 [
      (2, .split 332144352187 [])]),
    (10, .split 12135499643725165489 []),
    (12, .split 20390887542170848365521 []),
    (16, .round 1 [(598357843411082684037656428789, 1)]),
    (18, .round 1 [(468689304524295510900907073656841, 1)])]

private theorem checked127_108 : replayAbundance bank 127 1 (10^300) 6 state127_108 tree127_108 = true := by
  decide +kernel

theorem reject127_108 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_108 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree127_108 checked127_108

@[expose] noncomputable def state127_109 : State := ⟨2706059631543033324972500742703833130529681649371826921158524365789168342865990673770024167972357707121989581102077643478238709, 2727584645013186327515851744941674072018245897288915019388208143453997801152130325697755961548981788349698090652411850593941210, 162709⟩

private noncomputable def tree127_109 : AbundanceTree :=
  .split 307 [
    (2, .abundant [(3, 2), (5, 2), (7, 2)]),
    (4, .split 5231 [
      (2, .split 3909799 [
        (2, .abundant [(3, 2), (5, 2), (7, 2)])]),
      (4, .round 1 [(1621, 1), (249216868661, 1)])]),
    (6, .split 1274564409623 []),
    (10, .round 1 [(12135499643725165489, 1)]),
    (12, .round 1 [(20390887542170848365521, 1)])]

private theorem checked127_109 : replayAbundance bank 127 1 (10^300) 6 state127_109 tree127_109 = true := by
  decide +kernel

theorem reject127_109 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_109 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree127_109 checked127_109

@[expose] noncomputable def state127_110 : State := ⟨682706286076132501, 688128819107371670, 162709⟩

private theorem checked127_110 : checkChildren bank 127 1 (10^300) state127_110 86353 [state127_102, state127_103, state127_104, state127_105, state127_106, state127_107, state127_108, state127_109] = true := by
  decide +kernel

theorem reject127_110 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_110 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state127_102, state127_103, state127_104, state127_105, state127_106, state127_107, state127_108, state127_109] ?_ checked127_110
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject127_102 ho hN hs hav hx hvalid
  · exact reject127_103 ho hN hs hav hx hvalid
  · exact reject127_104 ho hN hs hav hx hvalid
  · exact reject127_105 ho hN hs hav hx hvalid
  · exact reject127_106 ho hN hs hav hx hvalid
  · exact reject127_107 ho hN hs hav hx hvalid
  · exact reject127_108 ho hN hs hav hx hvalid
  · exact reject127_109 ho hN hs hav hx hvalid

@[expose] noncomputable def state127_111 : State := ⟨980279778381848104610416801588573, 988065849329871176716850878581786, 8824793797⟩

private noncomputable def tree127_111 : AbundanceTree :=
  .split 2409829 [
    (2, .split 4252519 [
      (2, .split 360541 [
        (2, .split 249541 [
          (2, .split 1246591 [
            (2, .split 517996789291 [
              (2, .split 1155775441150339 [
                (2, .split 4893102089253706537901248957 []),
                (4, .abundant [(3, 8), (7, 4), (11, 2), (31, 2), (43, 2)])]),
              (4, .abundant [(3, 6), (5, 2), (7, 2)]),
              (6, .round 1 [(67, 1), (71, 1), (661, 1), (1831, 1), (2287, 1), (16651, 1), (28663, 1), (65029, 1), (86353, 1)])]),
            (4, .abundant [(3, 6), (5, 2), (7, 2)]),
            (6, .split 3087134292609393841154205419 [
              (2, .round 1 [(1831, 1), (2287, 1), (16651, 1), (18859, 1), (28663, 1), (65029, 1), (86353, 1)])]),
            (10, .split 86353 [
              (2, .split 2485642321 [
                (2, .round 1 [(28663, 1), (65029, 1), (2202194614231, 1)])]),
              (4, .abundant [(3, 6), (7, 2), (11, 2), (43, 2), (67, 2), (127, 6)]),
              (6, .round 1 [(95281244588123623, 1)])]),
            (12, .split 86353 [
              (2, .round 1 [(16651, 1), (28663, 1), (65029, 1), (2485642321, 1)]),
              (4, .abundant [(3, 6), (7, 2), (11, 2), (43, 2), (67, 2), (127, 6)])])]),
          (4, .abundant [(3, 4), (5, 2), (7, 2)]),
          (6, .split 287115878622190273284170790067 [
            (2, .split 86353 [
              (2, .round 1 [(661, 1), (1831, 1), (2287, 1), (19927, 1), (28663, 1), (65029, 1), (2485642321, 1)]),
              (4, .abundant [(3, 6), (7, 2), (11, 2), (29, 2), (43, 2)])])]),
          (10, .split 86353 [
            (2, .split 2485642321 [
              (2, .split 2202194614231 [
                (2, .round 1 [(15783728797, 1), (15995470741, 1)])]),
              (4, .abundant [(3, 6), (5, 2), (7, 2)])]),
            (4, .abundant [(3, 4), (7, 2), (11, 2), (43, 2), (67, 2), (127, 6)]),
            (6, .round 1 [(2287, 1), (2339, 1), (28663, 1), (65029, 1), (316037, 1), (95281244588123623, 1)])]),
          (12, .split 86353 [
            (2, .split 2485642321 [
              (2, .round 1 [(2287, 1), (15331, 1), (28663, 1), (65029, 1), (2202194614231, 1)])]),
            (4, .abundant [(3, 4), (7, 2), (11, 2), (43, 2), (67, 2), (127, 6)]),
            (6, .round 1 [(95281244588123623, 1)])]),
          (16, .round 1 [(661, 1), (1831, 1), (2287, 1), (6869, 1), (28663, 1), (65029, 1), (86353, 1)]),
          (18, .round 1 [(86353, 1)])]),
        (4, .abundant [(3, 4), (5, 2), (7, 2)]),
        (6, .split 2196489635605284233153321431577347 [
          (2, .round 1 [(1608188906440478104688918927823338449446448661601620750367291711919, 1)])]),
        (10, .split 49162886861911435505377 [
          (2, .round 1 [(77470452376495553, 1), (290468889020380554520783, 1)])]),
        (12, .split 255993901725306580903054781 [
          (2, .round 1 [(27127124677943042741, 1)])]),
        (16, .round 1 [(251325168039445907021783288121079116720005283804546444134547613023813788622867421, 1)]),
        (18, .round 1 [(1831, 1), (65029, 1), (86353, 1), (249541, 1)])]),
      (4, .split 54864211481 [
        (2, .split 6961384333116919 [
          (2, .split 596162293003363 [
            (2, .round 1 [(19441, 1), (65029, 1), (86353, 1), (128351, 1), (140071, 1), (193444878199, 1), (1350244511299, 1), (12534219388905427, 1)]),
            (4, .round 1 [(193444878199, 1)])]),
          (4, .round 1 [(125780949003797147138988024305924223352656026179070341409791, 1)])]),
        (4, .abundant [(3, 2), (5, 2), (7, 2)]),
        (6, .round 1 [(128351, 1), (28618176002311938089940627899672310291470210791337120597146679, 1)])]),
      (6, .split 73924958544343117020996103 [
        (2, .round 1 [(19, 1), (43, 1), (71, 1), (73, 1), (1831, 1), (65029, 1), (84449, 1), (86353, 1), (13342393, 1), (1313362051377757371555364861075742333220393021433, 1)])]),
      (10, .split 4424511226328588514967 [
        (2, .abundant [(3, 4), (7, 2), (13, 2), (23, 2), (37, 2)])]),
      (12, .round 1 [(10065936397983470907963763, 1), (266006663113266106863268763, 1), (13061966247138294279496504049, 1)]),
      (16, .round 1 [(1361, 1), (1831, 1), (7481, 1), (65029, 1), (86353, 1), (3142757, 1)])]),
    (4, .split 3065860574467561346058631 [
      (2, .abundant [(3, 2), (7, 2), (11, 2), (13, 2), (43, 2)]),
      (4, .abundant [(3, 2), (5, 2), (7, 2)])]),
    (6, .split 5807144135935585705699122518981 [
      (2, .split 727338853179362377 [
        (2, .round 1 [(9157, 1), (18307, 1), (86353, 1), (50241311287, 1), (15511794835249, 1)])])]),
    (10, .split 1583330397709302767840785182434201286717675016979587310473 []),
    (12, .split 3089499562831010954009785359657939152416385828337707929706654959741421 []),
    (16, .round 1 [(651891825899083982461147449130249216983075792259279984700670906409196480618403831136237, 1)]),
    (18, .round 1 [(43, 1), (457, 1), (1483, 1), (1831, 1), (86353, 1), (231877, 1), (672943, 1)])]

private theorem checked127_111 : replayAbundance bank 127 1 (10^300) 10 state127_111 tree127_111 = true := by
  decide +kernel

theorem reject127_111 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_111 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 10 h tree127_111 checked127_111

@[expose] noncomputable def state127_112 : State := ⟨8650766907588667850962213292243418756481681, 8719477378193783767211921210714915760528849, 0⟩

private noncomputable def tree127_112 : AbundanceTree :=
  .split 425557298187947929 [
    (1, .abundant [(3, 2), (5, 2), (7, 2)]),
    (2, .abundant [(3, 4), (7, 2), (13, 1), (31, 2), (43, 2), (61, 1)]),
    (4, .split 5286850352369751070321343689283274611098901 [
      (1, .abundant [(3, 4), (7, 2), (11, 2), (43, 2), (61, 2), (127, 6)])]),
    (6, .split 1554379 [
      (2, .split 11929039 [])])]

private theorem checked127_112 : replayAbundance bank 127 1 (10^300) 5 state127_112 tree127_112 = true := by
  decide +kernel

theorem reject127_112 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_112 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree127_112 checked127_112

@[expose] noncomputable def state127_113 : State := ⟨673695649541485918489056522036082750844101541030855413691708329, 679046613868591767479479478018134149584784521057736628940884227, 0⟩

private noncomputable def tree127_113 : AbundanceTree :=
  .split 18330959975152002601481 [
    (1, .split 492466462994279 [
      (2, .split 19141890667 [
        (2, .abundant [(3, 4), (7, 4), (13, 2), (17, 2)]),
        (4, .abundant [(3, 4), (7, 2), (11, 2), (17, 2)]),
        (6, .round 1 [(786645889, 1), (2300865181, 1)])]),
      (4, .abundant [(3, 4), (7, 2), (11, 2), (17, 2)]),
      (6, .round 1 [(2437, 1), (86353, 1)])]),
    (2, .split 3073245339798516301 [
      (1, .split 219517524271322593 [
        (2, .round 1 [(1582381, 1), (70331254588753, 1), (14933535113363089, 1), (12020296265496759883, 1)])]),
      (2, .split 58179035597570809 [
        (1, .abundant [(3, 2), (5, 2), (7, 2)]),
        (2, .round 1 [(3349603, 1), (14723179, 1), (284841523, 1)])])]),
    (4, .abundant [(3, 2), (5, 1), (7, 2)])]

private theorem checked127_113 : replayAbundance bank 127 1 (10^300) 6 state127_113 tree127_113 = true := by
  decide +kernel

theorem reject127_113 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_113 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree127_113 checked127_113

@[expose] noncomputable def state127_114 : State := ⟨52465386370887212902920341693896428880931853389983483185493197110527453698306773761, 52882103342519007579435269189313177941149157506264123477926485412578706296308064229, 0⟩

private noncomputable def tree127_114 : AbundanceTree :=
  .split 25124140376188542344573 [
    (1, .split 116446518124847 [
      (2, .split 18900693735838111 [
        (2, .round 1 [(1114998887, 1), (592057347953, 1), (36789257224117727908561, 1)])]),
      (4, .abundant [(3, 4), (7, 2), (11, 2), (17, 2)])]),
    (2, .split 1211800402195384488981591200041 [
      (1, .round 1 [(239, 1), (3851, 1), (42323, 1), (86353, 1), (592057347953, 1), (3195683246341, 1), (116446518124847, 1)])])]

private theorem checked127_114 : replayAbundance bank 127 1 (10^300) 6 state127_114 tree127_114 = true := by
  decide +kernel

theorem reject127_114 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_114 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree127_114 checked127_114

@[expose] noncomputable def state127_115 : State := ⟨318193380592859788499803212416222430921873897760602296376961916214773907776868684107374394029256945128279871064354846000241, 320720696050266136622893090082343969625742592583760449892768276172732510245645406475062470394160222961135286971310225678009, 0⟩

private noncomputable def tree127_115 : AbundanceTree :=
  .split 13123633564523508229711104727040647987676748268852654085893327407611483861 []

private theorem checked127_115 : replayAbundance bank 127 1 (10^300) 3 state127_115 tree127_115 = true := by
  decide +kernel

theorem reject127_115 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_115 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_115 checked127_115

@[expose] noncomputable def state127_116 : State := ⟨24779941305580800124489384177320861941333156333892235893217112435709934034717724550817678435944610640364160282233688925531258795574761106207369, 24976761014961711530882219141562129864478185810091106868909998893856710070823770321033428280073264837711343288413430407518439126026290178378667, 0⟩

private noncomputable def tree127_116 : AbundanceTree :=
  .round 1 [(388082329425685017842219750182204396614739644658604750424173368397824326295782997258127448877364218219, 1)]

private theorem checked127_116 : replayAbundance bank 127 1 (10^300) 3 state127_116 tree127_116 = true := by
  decide +kernel

theorem reject127_116 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_116 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_116 checked127_116

@[expose] noncomputable def state127_117 : State := ⟨111082457101161443105209, 111964752032370510547407, 0⟩

private theorem checked127_117 : checkChildren bank 127 1 (10^300) state127_117 8824793797 [state127_111, state127_112, state127_113, state127_114, state127_115, state127_116] = true := by
  decide +kernel

theorem reject127_117 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_117 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state127_111, state127_112, state127_113, state127_114, state127_115, state127_116] ?_ checked127_117
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject127_111 ho hN hs hav hx hvalid
  · exact reject127_112 ho hN hs hav hx hvalid
  · exact reject127_113 ho hN hs hav hx hvalid
  · exact reject127_114 ho hN hs hav hx hvalid
  · exact reject127_115 ho hN hs hav hx hvalid
  · exact reject127_116 ho hN hs hav hx hvalid

@[expose] noncomputable def state127_118 : State := ⟨2940821260918949383852842756209329, 2964179329868916775176489042881837, 0⟩

private noncomputable def tree127_118 : AbundanceTree :=
  .split 700888562389531127981 [
    (1, .split 639334696481669 [
      (2, .split 155042347 [
        (2, .split 62478139 [
          (2, .split 13483794013 [
            (2, .split 8657747666595163723 [
              (2, .abundant [(3, 6), (7, 2), (13, 2), (31, 2), (37, 2)])]),
            (4, .abundant [(3, 4), (7, 2), (13, 2), (37, 2), (43, 2), (127, 6), (251, 2)]),
            (6, .abundant [(3, 4), (7, 2), (13, 2), (29, 2), (37, 2)])]),
          (4, .split 678630265991908471 [
            (2, .abundant [(3, 4), (7, 2), (11, 2), (37, 2), (43, 2)])]),
          (6, .split 14374663 [
            (2, .round 1 [(829, 1), (1009, 1), (3541, 1), (19309, 1), (80173, 1), (86353, 1), (139891, 1), (182713, 1), (5203368103, 1)]),
            (4, .round 1 [(157551095323747542085059071, 1)])]),
          (10, .round 1 [(14374663, 1)])]),
        (4, .split 346966287560533152124421 [
          (2, .abundant [(3, 2), (7, 2), (11, 2), (13, 2), (43, 2)])]),
        (6, .round 1 [(7, 1), (29, 1), (43, 1), (829, 1), (1597, 1), (3541, 1), (25453, 1), (86353, 1), (182713, 1), (14374663, 1), (62478139, 1), (1076307159383, 1), (10947725165856805261838158831, 1)]),
        (10, .round 1 [(182713, 1), (14374663, 1), (62478139, 1)])]),
      (4, .split 61764271043090776571 [
        (2, .round 1 [(182713, 1), (1425091, 1), (30048643, 1), (37369771, 1), (1476372844561, 1), (1780037409229846318483, 1)])]),
      (6, .round 1 [(232837138842672543995677079, 1), (993689231862312864705878648101955521, 1)])]),
    (2, .split 293551836782650742688643681 [
      (1, .split 248554705490239 [
        (2, .split 57655894847019692911 [
          (2, .round 1 [(25674676553, 1), (4873161253641367, 1), (1709636399771096215801, 1)])]),
        (4, .round 1 [(19087279, 1), (25674676553, 1), (8786466984029986813849371013861441, 1)])]),
      (2, .split 30819948109494959190359952134419 [
        (2, .round 1 [(19087279, 1)])])]),
    (4, .split 345682503476776101923218570637351124413539535890981 [
      (1, .round 1 [(1091, 1), (1721, 1), (86353, 1), (1021193837, 1), (2398728935615388940981841, 1)])]),
    (6, .round 1 [(43, 1), (6287, 1), (10711, 1)])]

private theorem checked127_118 : replayAbundance bank 127 1 (10^300) 9 state127_118 tree127_118 = true := by
  decide +kernel

theorem reject127_118 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_118 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 9 h tree127_118 checked127_118

@[expose] noncomputable def state127_119 : State := ⟨77855945163302425004890369451392546558275049, 78474331788649737770611683979182958288368667, 0⟩

private noncomputable def tree127_119 : AbundanceTree :=
  .split 6473630500798343 [
    (2, .split 2511282478463599 [
      (2, .split 32302134217542367 [
        (2, .split 14053393855402663843 [
          (2, .abundant [(3, 4), (7, 4), (13, 3), (43, 2), (71, 2), (73, 1), (79, 2)])]),
        (4, .round 5767237398301 [(9196436593, 1), (5767237398301, 1)])]),
      (4, .round 5767237398301 [(9196436593, 1), (5767237398301, 1), (361673794672711, 1), (39828946269617282691472403638450635724153631, 1)]),
      (6, .round 5767237398301 [(9196436593, 1), (5767237398301, 1)])]),
    (4, .split 515380651092796114239414194849764516701117416486401 [
      (1, .round 1 [(14061661, 1), (5264187869, 1), (5767237398301, 1), (310020314521271495193453336959, 1)])]),
    (6, .round 1 [(15683582525946463789968936371101953625229875427469522885258065117732981081554343, 1)])]

private theorem checked127_119 : replayAbundance bank 127 1 (10^300) 7 state127_119 tree127_119 = true := by
  decide +kernel

theorem reject127_119 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_119 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree127_119 checked127_119

@[expose] noncomputable def state127_120 : State := ⟨54568006105149222804746479626203570807054956330319166693131883289, 55001423554215144073314713727195029931676963257899265886807887527, 0⟩

private noncomputable def tree127_120 : AbundanceTree :=
  .split 13005241719297839159406513466506959012287519723718951 [
    (2, .round 43505945101 [(241, 1), (86353, 1), (11509789, 1), (19087279, 1), (43505945101, 1)])]

private theorem checked127_120 : replayAbundance bank 127 1 (10^300) 4 state127_120 tree127_120 = true := by
  decide +kernel

theorem reject127_120 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_120 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree127_120 checked127_120

@[expose] noncomputable def state127_121 : State := ⟨1444645326613863604670050466389024471369040571473774889559665098966355521809, 1456119714940595983518854827748673799147556414339627365757403536244557663557, 0⟩

private noncomputable def tree127_121 : AbundanceTree :=
  .split 87384992395494220450351208993992934681932223997184523 []

private theorem checked127_121 : replayAbundance bank 127 1 (10^300) 3 state127_121 tree127_121 = true := by
  decide +kernel

theorem reject127_121 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_121 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_121 checked127_121

@[expose] noncomputable def state127_122 : State := ⟨1012529163149867803341519299690458722800182455487034802668240388832308459200463979727680198707649, 1020571381261184436954216941519857606471988513179777500162672740369013122070682561584820514608817, 0⟩

private noncomputable def tree127_122 : AbundanceTree :=
  .split 15700972139726169437800493108807954150757911460094624738156837043809908331 []

private theorem checked127_122 : replayAbundance bank 127 1 (10^300) 3 state127_122 tree127_122 = true := by
  decide +kernel

theorem reject127_122 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_122 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_122 checked127_122

@[expose] noncomputable def state127_123 : State := ⟨26805918486119527001904484466787179836615990993263307726096678347423004386919249815974156409419833213390969, 27018829927078822360999796894911698777720664798841480206230111201966790029857797674329788922017595536082047, 0⟩

private noncomputable def tree127_123 : AbundanceTree :=
  .split 93438208632439763568896789701993 [
    (1, .round 1 [(338220607644037, 1), (14297636212139963, 1), (46719104316219881784448394850997, 1)])]

private theorem checked127_123 : replayAbundance bank 127 1 (10^300) 4 state127_123 tree127_123 = true := by
  decide +kernel

theorem reject127_123 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_123 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree127_123 checked127_123

@[expose] noncomputable def state127_124 : State := ⟨18787846201553419153891830533004741575905623574261147408438790662306849812977678043551405960795627447548868768469339017888778409, 18937072478182055985749522912176853758456443821348989426788566758962205190798846369248575838221277806253875410968365708108789707, 0⟩

private noncomputable def tree127_124 : AbundanceTree :=
  .round 1 [(5509922221711822886530615800648931096090120135423171783365725252877651593735512414971817213338831173471, 1)]

private theorem checked127_124 : replayAbundance bank 127 1 (10^300) 3 state127_124 tree127_124 = true := by
  decide +kernel

theorem reject127_124 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_124 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_124 checked127_124

@[expose] noncomputable def state127_125 : State := ⟨4195872914689, 4229173493377, 0⟩

private theorem checked127_125 : checkChildren bank 127 1 (10^300) state127_125 162709 [state127_110, state127_117, state127_118, state127_119, state127_120, state127_121, state127_122, state127_123, state127_124] = true := by
  decide +kernel

theorem reject127_125 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_125 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state127_110, state127_117, state127_118, state127_119, state127_120, state127_121, state127_122, state127_123, state127_124] ?_ checked127_125
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject127_110 ho hN hs hav hx hvalid
  · exact reject127_117 ho hN hs hav hx hvalid
  · exact reject127_118 ho hN hs hav hx hvalid
  · exact reject127_119 ho hN hs hav hx hvalid
  · exact reject127_120 ho hN hs hav hx hvalid
  · exact reject127_121 ho hN hs hav hx hvalid
  · exact reject127_122 ho hN hs hav hx hvalid
  · exact reject127_123 ho hN hs hav hx hvalid
  · exact reject127_124 ho hN hs hav hx hvalid

@[expose] noncomputable def state127_126 : State := ⟨1091533853073393531649, 1100196820161277607297, 0⟩

private noncomputable def tree127_126 : AbundanceTree :=
  .split 47834644354838156839 [
    (2, .split 135940431627182851348747 [
      (2, .split 38676837149795180081395279974646356487 [
        (2, .split 220897 [
          (1, .abundant [(3, 4), (7, 2), (17, 2), (23, 2), (37, 2), (73, 2)]),
          (2, .round 1 [(3470287, 1)])])]),
      (4, .round 5966767972298043917865932006761 [(6399129590496313895171, 1), (9252646445749049400601, 1), (5966767972298043917865932006761, 1)])]),
    (4, .split 5661441363368178618635736738445094781572639593766742448510907471 []),
    (6, .split 33038978287897 [
      (1, .split 4404022699 []),
      (2, .round 1 [(163065499816327, 1)])])]

private theorem checked127_126 : replayAbundance bank 127 1 (10^300) 7 state127_126 tree127_126 = true := by
  decide +kernel

theorem reject127_126 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_126 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree127_126 checked127_126

@[expose] noncomputable def state127_127 : State := ⟨17605349516220764271966721, 17745074512381246528093441, 0⟩

private noncomputable def tree127_127 : AbundanceTree :=
  .split 1437263292796553 [
    (1, .split 12346432697 [
      (2, .split 22299994021 [
        (2, .split 429593155185361 [
          (2, .split 14398676411790827539 [
            (2, .split 2366169307 [
              (2, .round 1 [(3, 5), (61, 1), (67, 1), (103, 1), (199, 1), (277, 1), (523, 1), (1511, 1), (5683, 1), (1867147, 1), (137819029, 1), (1686024841, 1)]),
              (4, .round 1 [(60165224719733315498728669512290881, 1)])])]),
          (4, .abundant [(3, 2), (5, 2), (7, 2)]),
          (6, .round 1 [(1867147, 1), (2366169307, 1)])]),
        (4, .abundant [(3, 2), (5, 2), (7, 2)]),
        (6, .split 2366169307 [
          (2, .split 1686024841 [
            (2, .round 1 [(31, 1), (61, 1), (67, 1), (103, 1), (523, 1), (607, 1), (1511, 1), (5683, 1), (1867147, 1), (1755966521167, 1)])]),
          (4, .round 1 [(60165224719733315498728669512290881, 1)])]),
        (10, .round 1 [(30412173964575017022598119890960982461056027566451722865570205265225620604435769972430323077031195097111, 1)])]),
      (4, .split 2112386037215470122004643590499058284351 [
        (2, .split 2366169307 [
          (2, .round 1 [(1511, 1), (5683, 1), (11071, 1), (1686024841, 1)])])]),
      (6, .split 2366169307 [
        (2, .split 1686024841 [
          (2, .split 1755966521167 [
            (2, .round 1 [(163, 1), (607, 1), (1511, 1), (5683, 1), (364393, 1), (17304281773201441, 1)])]),
          (4, .round 1 [(5231, 1), (5683, 1), (69401, 1), (528391, 1), (32238400926181, 1)])]),
        (4, .split 60165224719733315498728669512290881 []),
        (6, .round 1 [(2631040024238690470140817205578773053, 1)])]),
      (10, .split 2366169307 [
        (2, .round 1 [(1511, 1), (5683, 1), (1686024841, 1)])]),
      (12, .round 1 [(2366169307, 1)])]),
    (2, .split 925370433206515418719 [
      (2, .split 198488309390337614088710294281 [
        (1, .split 7524255812664343 [
          (2, .round 1 [(161009, 1), (891859, 1), (81920243, 1), (3234361159, 1), (12346432697, 1), (205436217781, 1), (240694854209331349, 1)]),
          (4, .round 1 [(205436217781, 1)])]),
        (2, .round 1 [(144313585951041710884574423363082546479951007302235646891, 1)])]),
      (4, .split 10715493248775349833771443475881080309655119944086365563208534081 [])]),
    (4, .split 4928208474260412556728730034100462485663463851 [
      (2, .round 1 [(184976953991, 1)])]),
    (6, .round 1409655816661 [(12346432697, 1), (1409655816661, 1), (21642230062111, 1), (504905072680378839073907, 1), (572259713187727786563539547465881684370719, 1)])]

private theorem checked127_127 : replayAbundance bank 127 1 (10^300) 9 state127_127 tree127_127 = true := by
  decide +kernel

theorem reject127_127 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_127 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 9 h tree127_127 checked127_127

@[expose] noncomputable def state127_128 : State := ⟨4579937329576774398276408998492161, 4616286038541669433183364625464321, 0⟩

private noncomputable def tree127_128 : AbundanceTree :=
  .split 115512048133057 [
    (1, .split 75755912653 [
      (2, .split 12668782123542431371 [
        (2, .split 75888778595259718177 [
          (2, .round 1 [(179947, 1), (712093, 1), (527532101, 1), (834669361, 1), (3564746191, 1), (6159328577, 1), (4886312332487955587473, 1)])]),
        (4, .split 6159328577 [
          (2, .round 1 [(568237, 1), (527532101, 1), (76126812043, 1)])])]),
      (4, .split 13226713467278341206763906871 [
        (2, .split 6159328577 [
          (2, .round 1 [(4238761, 1), (53405081, 1), (527532101, 1), (76126812043, 1)])])]),
      (6, .split 27002325475619891805372216513157401751768981566290446929532834549 []),
      (10, .round 1 [(527532101, 1), (6159328577, 1)])]),
    (2, .split 115370386473455611 [
      (2, .split 127226661266447868259133561407 [
        (2, .round 240972368394352849 [(527532101, 1), (75755912653, 1), (240972368394352849, 1), (22390704578651042491068531271252322766331, 1)])]),
      (4, .abundant [(3, 2), (5, 1), (7, 2)]),
      (6, .round 75755912653 [(527532101, 1), (75755912653, 1)])]),
    (4, .split 59150752990166536513524713615381067397793501 [
      (1, .split 30335745201236437168165916669 [
        (2, .round 1 [(273625252091, 1)])]),
      (2, .round 1 [(273625252091, 1)])]),
    (6, .round 75755912653 [(527532101, 1), (75755912653, 1), (31270714267899191, 1), (503354853910630094320855979, 1), (64941238353142879388943982194275831, 1)])]

private theorem checked127_128 : replayAbundance bank 127 1 (10^300) 7 state127_128 tree127_128 = true := by
  decide +kernel

theorem reject127_128 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_128 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree127_128 checked127_128

@[expose] noncomputable def state127_129 : State := ⟨73869809188743794269800200736680064769, 74456077515638586287814488044114033537, 0⟩

private noncomputable def tree127_129 : AbundanceTree :=
  .split 149861247689324730312041 [
    (1, .split 496833428679257 [
      (2, .split 6806961201874898689 [
        (2, .split 379186880811283999085739117313 [
          (2, .round 1 [(8836616628937, 1)])]),
        (4, .round 1 [(109, 1), (631, 1), (2371, 1), (140317, 1), (8836616628937, 1)])]),
      (4, .split 8836616628937 [
        (2, .split 143872038649231 [
          (2, .abundant [(3, 4), (7, 2), (13, 2), (31, 2), (61, 2), (127, 18), (157, 2)])]),
        (4, .round 1 [(56416924405507042950911201, 1)])]),
      (6, .split 8836616628937 [
        (2, .round 1 [(143872038649231, 1)])])]),
    (2, .split 35656206228074199833528635038646710571 [
      (2, .round 1 [(55195025662906767408798868272163518868979908778358722851, 1)])]),
    (4, .split 19451240820651356618624250225315807279766251445373288953577458478347096680245577541 [])]

private theorem checked127_129 : replayAbundance bank 127 1 (10^300) 7 state127_129 tree127_129 = true := by
  decide +kernel

theorem reject127_129 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_129 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree127_129 checked127_129

@[expose] noncomputable def state127_130 : State := ⟨19216834992144255601295030362371570981188252929, 19369349555573971915591022666834837417546889857, 0⟩

private noncomputable def tree127_130 : AbundanceTree :=
  .split 19369349555573971915591022666834837417546889857 [
    (1, .split 73901225118855710546258209795045590947 [
      (2, .abundant [(3, 2), (7, 2), (11, 2), (13, 2), (19, 2)])]),
    (2, .split 384344893835589375381417855515555077 [
      (1, .round 1 [(119618327526605583793309, 1), (24225812900759759059658617, 1)])])]

private theorem checked127_130 : replayAbundance bank 127 1 (10^300) 5 state127_130 tree127_130 = true := by
  decide +kernel

theorem reject127_130 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_130 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree127_130 checked127_130

@[expose] noncomputable def state127_131 : State := ⟨80631397449585884167753993329574755403270206405810971374081, 81271329175376248327815532959174555049327906456650740988161, 0⟩

private noncomputable def tree127_131 : AbundanceTree :=
  .split 26199309335023419242579777392551093827273 [
    (1, .split 160006125892973 [
      (2, .split 1832934561331 [
        (2, .round 1 [(59, 1), (8233, 1), (164653, 1), (1454119, 1), (4418831, 1), (8566849, 1), (36157263917, 1), (61071495271, 1), (1528366755967, 1)]),
        (4, .abundant [(3, 2), (5, 2), (11, 2), (13, 2)])]),
      (4, .split 36157263917 [
        (2, .round 1 [(19981303, 1), (5846533159, 1)])])]),
    (2, .split 10461718456238211247907797947092631942893046596585474901183118090074575212273 [])]

private theorem checked127_131 : replayAbundance bank 127 1 (10^300) 6 state127_131 tree127_131 = true := by
  decide +kernel

theorem reject127_131 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_131 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree127_131 checked127_131

@[expose] noncomputable def state127_132 : State := ⟨1300503809464370725741704158412711229899345159119325157292552449, 1310825268269643509279336731098526398390609803239319801398048897, 0⟩

private noncomputable def tree127_132 : AbundanceTree :=
  .split 1310825268269643509279336731098526398390609803239319801398048897 [
    (1, .split 257125395894398491423957773852202118162143939434939152883101 [])]

private theorem checked127_132 : replayAbundance bank 127 1 (10^300) 4 state127_132 tree127_132 = true := by
  decide +kernel

theorem reject127_132 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_132 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree127_132 checked127_132

@[expose] noncomputable def state127_133 : State := ⟨5456748709581417100915090468521094447984647336886445336075825428058035023361, 5500056239022539458858861027795071388048017553845861568901824042566432126721, 0⟩

private noncomputable def tree127_133 : AbundanceTree :=
  .split 194203343722276362479760868906423630163997146074681519296949 [
    (1, .split 1964806536597022356534606613 [
      (2, .abundant [(3, 2), (5, 2), (7, 2)])])]

private theorem checked127_133 : replayAbundance bank 127 1 (10^300) 5 state127_133 tree127_133 = true := by
  decide +kernel

theorem reject127_133 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_133 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree127_133 checked127_133

@[expose] noncomputable def state127_134 : State := ⟨1419543934081271011988816981415941916098059254965930379719569954760828848317673958401, 1430810155780328718433172671744639867813123217306929827177661779798613204256703116801, 0⟩

private noncomputable def tree127_134 : AbundanceTree :=
  .split 173516236731585386728283399492820062514514695084429889016980953179741605063 []

private theorem checked127_134 : replayAbundance bank 127 1 (10^300) 3 state127_134 tree127_134 = true := by
  decide +kernel

theorem reject127_134 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_134 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_134 checked127_134

@[expose] noncomputable def state127_135 : State := ⟨22895824112796820152367629093257727164745597723345491094496943800337408494515763275049729, 23077537002580921899608642022569296427957864371943471182548506846371832371456364570883457, 0⟩

private noncomputable def tree127_135 : AbundanceTree :=
  .split 27276795789402785335062769556423455997027986936940419 []

private theorem checked127_135 : replayAbundance bank 127 1 (10^300) 3 state127_135 tree127_135 = true := by
  decide +kernel

theorem reject127_135 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_135 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_135 checked127_135

@[expose] noncomputable def state127_136 : State := ⟨5956225944222672284479242170486686953748691376070130099746604520535950811676153706028796007852289, 6003497578700630001022728219458803516873680990165924783077926778635442484784694608457595976168577, 0⟩

private noncomputable def tree127_136 : AbundanceTree :=
  .split 127876091543425749918009800415499747563439592773 [
    (1, .split 332545242174719239866237860155585866066917 [])]

private theorem checked127_136 : replayAbundance bank 127 1 (10^300) 4 state127_136 tree127_136 = true := by
  decide +kernel

theorem reject127_136 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_136 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree127_136 checked127_136

@[expose] noncomputable def state127_137 : State := ⟨24991567113131825098714376022397857842296632218930895008095215809912163288597558384071813576832591177410373121, 25189912883870966567751791705115301158505335649239870365302320697292418552792777101405716859188405393104106241, 0⟩

private noncomputable def tree127_137 : AbundanceTree :=
  .round 10385386208583037 [(2889382663, 1), (4216187737, 1), (2104305482273, 1), (10385386208583037, 1), (217171599055284644648798525834594580991825499758079, 1)]

private theorem checked127_137 : replayAbundance bank 127 1 (10^300) 3 state127_137 tree127_137 = true := by
  decide +kernel

theorem reject127_137 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_137 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_137 checked127_137

@[expose] noncomputable def state127_138 : State := ⟨104861439545622188384028854067804434131547046734174240001087913410372622354801140776104249344514806788169208562273291674369, 105693673192809666069616384655644151862749801073334353016969563516804151103648768877501902117090321127757853074672286052737, 0⟩

private noncomputable def tree127_138 : AbundanceTree :=
  .round 1 [(30007489448321593870497921019180748632826641477294435650454214930059796978711887605126240779302636268911, 1)]

private theorem checked127_138 : replayAbundance bank 127 1 (10^300) 3 state127_138 tree127_138 = true := by
  decide +kernel

theorem reject127_138 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_138 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_138 checked127_138

@[expose] noncomputable def state127_139 : State := ⟨1691310158431340276446001387259617718107722316775496316977546955395900025960587599577785437677679318686381164900905921415897601, 1704733254926827104036842668110884525394291541511809779810702089962534153150750993225228179246549789469606412241389301744595201, 0⟩

private noncomputable def tree127_139 : AbundanceTree :=
  .round 484659285270119194936449216246169915874829114597769 [(4561764611500668699638496177119953507590109034017, 1), (484659285270119194936449216246169915874829114597769, 1)]

private theorem checked127_139 : replayAbundance bank 127 1 (10^300) 3 state127_139 tree127_139 = true := by
  decide +kernel

theorem reject127_139 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_139 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_139 checked127_139

@[expose] noncomputable def state127_140 : State := ⟨7096522484100422093816242854880349625224556010967853491571164578706352917847701458479552610164503882214081841062395272347901452889032761089, 7152844091117092110433832083887336527012052487245376138329665884886562067989349882753199853102317405088796776308922218953837178705612386177, 0⟩

private noncomputable def tree127_140 : AbundanceTree :=
  .round 1 [(69424288611600259592456975282398999769690869870796439136061807316258152016274559865148749784783580277524394670036888840787372050403, 1)]

private theorem checked127_140 : replayAbundance bank 127 1 (10^300) 3 state127_140 tree127_140 = true := by
  decide +kernel

theorem reject127_140 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_140 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_140 checked127_140

@[expose] noncomputable def state127_141 : State := ⟨1846122293974732513544294817451663651208526667857624309105377135279480424232792788591339619611857813381688605687795876725042050565195840470736674049, 1860774058212627216032741601717153045265737196967605454415737271273762014901307017072223267386555097614876610494841875746669368426824378887171092097, 0⟩

private noncomputable def tree127_141 : AbundanceTree :=
  .round 48246109851768796889318028776693997239250192734594011318276897701653896086992636122848240035346352054393 [(63979665542255612936629, 1), (48246109851768796889318028776693997239250192734594011318276897701653896086992636122848240035346352054393, 1)]

private theorem checked127_141 : replayAbundance bank 127 1 (10^300) 3 state127_141 tree127_141 = true := by
  decide +kernel

theorem reject127_141 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_141 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_141 checked127_141

@[expose] noncomputable def state127_142 : State := ⟨1, 1, 0⟩

private theorem checked127_142 : checkChildren bank 127 1 (10^300) state127_142 127 [state127_70, state127_101, state127_125, state127_126, state127_127, state127_128, state127_129, state127_130, state127_131, state127_132, state127_133, state127_134, state127_135, state127_136, state127_137, state127_138, state127_139, state127_140, state127_141] = true := by
  decide +kernel

theorem reject127_142 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_142 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state127_70, state127_101, state127_125, state127_126, state127_127, state127_128, state127_129, state127_130, state127_131, state127_132, state127_133, state127_134, state127_135, state127_136, state127_137, state127_138, state127_139, state127_140, state127_141] ?_ checked127_142
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject127_70 ho hN hs hav hx hvalid
  · exact reject127_101 ho hN hs hav hx hvalid
  · exact reject127_125 ho hN hs hav hx hvalid
  · exact reject127_126 ho hN hs hav hx hvalid
  · exact reject127_127 ho hN hs hav hx hvalid
  · exact reject127_128 ho hN hs hav hx hvalid
  · exact reject127_129 ho hN hs hav hx hvalid
  · exact reject127_130 ho hN hs hav hx hvalid
  · exact reject127_131 ho hN hs hav hx hvalid
  · exact reject127_132 ho hN hs hav hx hvalid
  · exact reject127_133 ho hN hs hav hx hvalid
  · exact reject127_134 ho hN hs hav hx hvalid
  · exact reject127_135 ho hN hs hav hx hvalid
  · exact reject127_136 ho hN hs hav hx hvalid
  · exact reject127_137 ho hN hs hav hx hvalid
  · exact reject127_138 ho hN hs hav hx hvalid
  · exact reject127_139 ho hN hs hav hx hvalid
  · exact reject127_140 ho hN hs hav hx hvalid
  · exact reject127_141 ho hN hs hav hx hvalid

theorem exclude_127 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) : False :=
  reject127_142 ho hN hs hav hx (root_valid N)

end OddPerfect.IndexComponent.Size300
