module

public import OddPerfect.SizeIndex300.Seed7Part02

public section

namespace OddPerfect.IndexComponent.Size300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def state7_96 : State := ⟨7562960709064500129904591777, 8823484251672462814993219858, 310897033⟩

private theorem checked7_96 : checkChildren bank 7 2413 (10^300) state7_96 84437 [state7_89, state7_90, state7_91, state7_92, state7_93, state7_94, state7_95] = true := by
  decide +kernel

theorem reject7_96 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_96 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state7_89, state7_90, state7_91, state7_92, state7_93, state7_94, state7_95] ?_ checked7_96
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject7_89 ho hN hs hav hx hvalid
  · exact reject7_90 ho hN hs hav hx hvalid
  · exact reject7_91 ho hN hs hav hx hvalid
  · exact reject7_92 ho hN hs hav hx hvalid
  · exact reject7_93 ho hN hs hav hx hvalid
  · exact reject7_94 ho hN hs hav hx hvalid
  · exact reject7_95 ho hN hs hav hx hvalid

@[expose] noncomputable def state7_97 : State := ⟨45440961654877187930734465034980496821964972279507089, 53014636443405233445881619925509158206285935562627803, 0⟩

private noncomputable def tree7_97 : AbundanceTree :=
  .split 6315307 [
    (4, .split 16047680282064438060281 [
      (1, .abundant [(3, 4), (7, 10), (11, 2), (17, 2)]),
      (2, .split 38280237973898212158647494954229824123 []),
      (4, .abundant [(3, 2), (5, 1), (7, 10)])]),
    (6, .split 1950391 [
      (2, .split 17299603 [
        (2, .split 6553160377 [
          (1, .split 3276580189 [
            (2, .split 11433416121644149 [
              (2, .round 1 [(1931049842714676159979417, 1)])]),
            (4, .abundant [(3, 4), (7, 10), (11, 2), (13, 2)])]),
          (2, .split 87840993949 [
            (1, .abundant [(3, 6), (5, 2), (7, 10)]),
            (2, .round 162960781 [(139, 1), (277, 1), (283, 1), (523, 1), (1123, 1), (1171, 1), (1667353, 1), (162960781, 1), (367430486573147409931, 1)])]),
          (4, .abundant [(3, 4), (7, 10), (11, 2), (13, 1)])]),
        (4, .split 9270912674235100802554061 [
          (1, .split 58530379 [
            (2, .round 1 [(15331, 1), (343583, 1), (556859, 1), (1667353, 1), (22205857, 1)])])]),
        (6, .split 69383149738662734304241891729 [
          (1, .abundant [(3, 4), (5, 2), (7, 10)])])]),
      (4, .abundant [(3, 2), (5, 1), (7, 10)]),
      (6, .split 31083109736130061 [
        (1, .split 3401266261 [
          (2, .abundant [(3, 4), (7, 10), (13, 4), (29, 2), (31, 2)])]),
        (2, .round 3401266261 [(277, 1), (523, 1), (631, 1), (659, 1), (1123, 1), (43177, 1), (1667353, 1), (3401266261, 1)])]),
      (10, .round 1 [(3536184476549094462412470479077934353311416537826160187579, 1)])]),
    (10, .split 1950391 [
      (2, .split 17299603 [
        (2, .abundant [(3, 4), (7, 10), (13, 1), (23, 2), (37, 1)]),
        (4, .round 9270912674235100802554061 [(523, 1), (1123, 1), (8053, 1), (9661, 1), (1667353, 1), (9270912674235100802554061, 1)])]),
      (4, .abundant [(3, 2), (5, 1), (7, 10)]),
      (6, .round 31083109736130061 [(43177, 1), (1667353, 1), (3401266261, 1), (31083109736130061, 1)])]),
    (12, .split 4024701512640176939233477381284023898711327395588894172584912288902466004225339001 []),
    (16, .round 1 [(1950391, 1)])]

private theorem checked7_97 : replayAbundance bank 7 2413 (10^300) 9 state7_97 tree7_97 = true := by
  decide +kernel

theorem reject7_97 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_97 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 9 h tree7_97 checked7_97

@[expose] noncomputable def state7_98 : State := ⟨878186194914740466020773621333509312727460724997802406479697138145081, 1024554062183352338874128544074638644394719133927959960958017722053311, 0⟩

private noncomputable def tree7_98 : AbundanceTree :=
  .split 73286203525352337924791 [
    (2, .split 38903141 [
      (1, .split 6483857 [
        (2, .split 1667353 [
          (2, .split 759631 [
            (4, .abundant [(3, 4), (5, 2), (7, 10)]),
            (6, .round 1 [(119827, 1), (214741, 1)])]),
          (4, .split 759631 [
            (4, .abundant [(3, 2), (5, 2), (7, 10)])]),
          (6, .split 759631 [])]),
        (4, .split 514864412568431 [
          (2, .round 1 [(155390881, 1), (8890665898135561, 1)])]),
        (6, .round 1 [(16244999, 1), (941312979435266779381780565827, 1)])]),
      (2, .split 216207774081289 [
        (1, .abundant [(3, 2), (5, 2), (7, 10)]),
        (2, .split 1069395493 [
          (1, .split 534697747 [
            (2, .round 1 [(63810001, 1), (95300560393857919, 1)])]),
          (2, .round 63810001 [(769, 1), (1033, 1), (1123, 1), (466153, 1), (1667353, 1), (63810001, 1), (117145891, 1)])])]),
      (4, .abundant [(3, 2), (5, 1), (7, 10)]),
      (6, .split 1667353 [
        (1, .split 4933 [
          (4, .abundant [(3, 2), (7, 10), (11, 2), (13, 2)])]),
        (2, .split 214741 [
          (1, .round 1 [(227, 1), (277, 1), (1123, 1), (88069, 1)]),
          (2, .round 1 [(95803, 1)])])])]),
    (4, .abundant [(3, 2), (5, 1), (7, 10)])]

private theorem checked7_98 : replayAbundance bank 7 2413 (10^300) 8 state7_98 tree7_98 = true := by
  decide +kernel

theorem reject7_98 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_98 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree7_98 checked7_98

@[expose] noncomputable def state7_99 : State := ⟨16971713732560417681247841629994225048278620789450415981174080922958119632636839202849, 19800400356550735701678662402993731693433206745693300067609758710183542482997569087043, 0⟩

private noncomputable def tree7_99 : AbundanceTree :=
  .split 1123839041232277367115712206901 [
    (1, .split 49918102555193 [
      (2, .split 39528435584068569451 []),
      (4, .round 1 [(1667353, 1), (2368451, 1), (26099221, 1), (80556323, 1)])]),
    (2, .split 26099221 [
      (1, .split 13049611 [
        (4, .abundant [(3, 2), (5, 2), (7, 10)])]),
      (2, .split 1446219454153 [
        (1, .round 1 [(281, 1), (1123, 1), (6911, 1), (60761, 1), (1667353, 1), (104631707, 1)]),
        (2, .round 1 [(90523341079, 1)])]),
      (4, .abundant [(3, 2), (5, 1), (7, 10)])])]

private theorem checked7_99 : replayAbundance bank 7 2413 (10^300) 6 state7_99 tree7_99 = true := by
  decide +kernel

theorem reject7_99 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_99 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree7_99 checked7_99

@[expose] noncomputable def state7_100 : State := ⟨6338753770389552734134352157774003266011446507641218152217708186392020204968712241496739387407586406743974307014777009, 7395238005606739754650978054674450355578198841980559146887684054652304334293285773153851638469165820850316751224867883, 0⟩

private noncomputable def tree7_100 : AbundanceTree :=
  .split 1667353 [
    (1, .split 4933 [
      (4, .abundant [(3, 2), (7, 10), (11, 2), (13, 2)]),
      (6, .split 12400411646533 []),
      (10, .round 1 [(159091297108374907, 1)])]),
    (2, .split 214741 [
      (1, .abundant [(3, 2), (7, 10), (11, 2), (23, 2), (43, 2), (139, 2), (199, 2)]),
      (2, .split 95803 [
        (2, .split 1046677 [
          (1, .split 88069 [
            (2, .round 1 [(577, 1), (907, 1), (1123, 1), (3331, 1), (22921, 1), (110881, 1)])]),
          (2, .round 88069 [(199, 1), (277, 1), (1123, 1), (2833, 1), (22921, 1), (88069, 1), (18414499, 1)])]),
        (4, .abundant [(3, 4), (7, 10), (11, 2), (23, 2)]),
        (6, .round 1 [(3808755976674263215090504631, 1)])]),
      (4, .abundant [(3, 2), (5, 1), (7, 10)]),
      (6, .round 47625056392739259250409976433 [(199, 1), (277, 1), (1123, 1), (88069, 1), (47625056392739259250409976433, 1)])]),
    (4, .split 1123 [
      (4, .split 1983851 [
        (2, .round 1 [(19571, 1)])]),
      (6, .round 1 [(431, 1), (3823, 1), (293147, 1)])]),
    (6, .split 1123 [])]

private theorem checked7_100 : replayAbundance bank 7 2413 (10^300) 8 state7_100 tree7_100 = true := by
  decide +kernel

theorem reject7_100 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_100 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree7_100 checked7_100

@[expose] noncomputable def state7_101 : State := ⟨122501942111130493588770214571666643313061221831457047762234526233244073689307217988315821232930422332249004477788050936352745861532761, 142919420895125621330494356570641005054996118046577960612489733966101431936429043165078899146093382041206808821726753484460902331455631, 0⟩

private noncomputable def tree7_101 : AbundanceTree :=
  .split 1667353 [
    (1, .split 4933 [
      (4, .abundant [(3, 2), (7, 10), (11, 2), (13, 2)]),
      (6, .round 1 [(12400411646533, 1)])]),
    (2, .split 214741 [
      (1, .split 88069 [
        (2, .abundant [(3, 4), (7, 10), (11, 2), (43, 2), (79, 2), (139, 2)])]),
      (2, .split 95803 [
        (2, .round 1046677 [(22921, 1), (88069, 1), (1046677, 1)])])]),
    (4, .split 1123 [])]

private theorem checked7_101 : replayAbundance bank 7 2413 (10^300) 6 state7_101 tree7_101 = true := by
  decide +kernel

theorem reject7_101 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_101 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree7_101 checked7_101

@[expose] noncomputable def state7_102 : State := ⟨2351302045143729296015452156545497641, 2743195074567194005364948270392505751, 0⟩

private theorem checked7_102 : checkChildren bank 7 2413 (10^300) state7_102 139017523 [state7_97, state7_98, state7_99, state7_100, state7_101] = true := by
  decide +kernel

theorem reject7_102 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_102 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state7_97, state7_98, state7_99, state7_100, state7_101] ?_ checked7_102
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact reject7_97 ho hN hs hav hx hvalid
  · exact reject7_98 ho hN hs hav hx hvalid
  · exact reject7_99 ho hN hs hav hx hvalid
  · exact reject7_100 ho hN hs hav hx hvalid
  · exact reject7_101 ho hN hs hav hx hvalid

@[expose] noncomputable def state7_103 : State := ⟨20277618254581841647551668955732794538516443896174113565425349, 23657302241646992641292117472380888950709509041284976658391294, 89222701⟩

private noncomputable def tree7_103 : AbundanceTree :=
  .split 44611351 [
    (2, .split 1511140989109 [
      (2, .split 7290111030129830569 [
        (2, .split 2457437452187506198939 [
          (2, .round 1 [(7795811, 1), (12533041, 1), (15221321, 1)])]),
        (4, .round 1 [(7795811, 1), (15221321, 1)])]),
      (4, .split 15221321 [
        (2, .split 7795811 [
          (2, .split 5492801 [
            (2, .round 1 [(1123, 1), (83443, 1), (107599, 1), (160651, 1), (2064583, 1), (14613541, 1)]),
            (4, .abundant [(3, 2), (5, 2), (7, 10)])]),
          (4, .abundant [(3, 2), (5, 2), (7, 10)])]),
        (4, .abundant [(3, 2), (5, 2), (7, 10)]),
        (6, .round 1 [(5492801, 1), (7795811, 1)])]),
      (6, .split 15221321 [
        (2, .round 1 [(1123, 1), (160651, 1), (5492801, 1), (7795811, 1)])])]),
    (4, .split 1631830528533060342008861 [
      (2, .round 1 [(160651, 1), (2431489, 1), (5492801, 1), (7795811, 1), (15221321, 1), (1095160567805360033706307292638522482495847, 1)])]),
    (6, .split 60226780120174584708613854132734173 [
      (2, .round 1 [(15221321, 1), (22608881, 1)])]),
    (10, .split 15221321 [
      (2, .split 7795811 [
        (2, .round 1 [(107599, 1), (160651, 1), (5492801, 1)])]),
      (4, .round 1 [(2826807791, 1)])]),
    (12, .round 1 [(160651, 1), (5492801, 1), (7795811, 1), (15221321, 1)])]

private theorem checked7_103 : replayAbundance bank 7 2413 (10^300) 8 state7_103 tree7_103 = true := by
  decide +kernel

theorem reject7_103 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_103 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree7_103 checked7_103

@[expose] noncomputable def state7_104 : State := ⟨1809223870520697537348849941288329363004485657331617978587989851647649, 2110768404373099637132117513194859226832593834739523026878635287249791, 0⟩

private noncomputable def tree7_104 : AbundanceTree :=
  .split 204120268280977 [
    (1, .split 15221321 [
      (2, .split 7795811 [
        (2, .split 6142993 [
          (2, .split 1112084671 [
            (2, .abundant [(3, 4), (7, 10), (13, 2), (23, 2), (37, 2)]),
            (4, .abundant [(3, 2), (5, 2), (7, 10)]),
            (6, .round 1 [(160651, 1), (5492801, 1)])]),
          (4, .abundant [(3, 2), (7, 10), (13, 2), (23, 2), (31, 2), (37, 2)]),
          (6, .split 5492801 [
            (2, .round 1 [(2143, 1), (2789, 1), (83443, 1), (107599, 1), (160651, 1), (2064583, 1), (14613541, 1)]),
            (4, .abundant [(3, 2), (5, 2), (7, 10)])])]),
        (4, .abundant [(3, 2), (5, 2), (7, 10)]),
        (6, .split 6142993 [
          (2, .split 1112084671 [
            (2, .abundant [(3, 4), (7, 10), (13, 2), (23, 2), (37, 2)])]),
          (4, .abundant [(3, 2), (7, 10), (13, 2), (23, 2), (31, 2), (37, 2)])]),
        (10, .abundant [(3, 2), (7, 10), (11, 2), (13, 2)])]),
      (4, .abundant [(3, 2), (5, 2), (7, 10)]),
      (6, .split 7795811 [
        (2, .split 6142993 [
          (2, .round 1 [(277, 1), (967, 1), (1123, 1), (2789, 1), (11311, 1), (83443, 1), (92051, 1), (107599, 1), (160651, 1), (5492801, 1), (1112084671, 1)]),
          (4, .abundant [(3, 2), (7, 10), (13, 2), (23, 2), (31, 2), (37, 2)])]),
        (4, .abundant [(3, 2), (5, 2), (7, 10)]),
        (6, .round 1 [(160651, 1), (5492801, 1), (6142993, 1)])]),
      (10, .round 1 [(277, 1), (1123, 1), (2789, 1), (160651, 1), (5492801, 1), (6142993, 1), (7795811, 1)]),
      (12, .round 1 [(7795811, 1)])]),
    (2, .split 26264382337 [
      (1, .split 15221321 [
        (2, .split 7795811 [
          (2, .split 5492801 [
            (2, .split 14613541 [
              (2, .round 1 [(19429, 1), (20143, 1), (22171, 1), (30937, 1), (83443, 1), (107599, 1), (160651, 1), (227431, 1), (602477, 1), (2064583, 1)]),
              (4, .abundant [(3, 2), (5, 2), (7, 10)])]),
            (4, .abundant [(3, 2), (5, 2), (7, 10)]),
            (6, .round 1 [(160651, 1), (227431, 1), (602477, 1)])]),
          (4, .abundant [(3, 2), (5, 2), (7, 10)]),
          (6, .round 1 [(1123, 1), (19429, 1), (20143, 1), (160651, 1), (227431, 1), (602477, 1), (5492801, 1)])]),
        (4, .abundant [(3, 2), (5, 2), (7, 10)]),
        (6, .round 1 [(307, 1), (457, 1), (1123, 1), (19429, 1), (20143, 1), (92051, 1), (160651, 1), (227431, 1), (602477, 1), (5492801, 1), (7795811, 1)])]),
      (2, .split 25294999 [
        (2, .split 44093239591 [
          (4, .abundant [(3, 4), (5, 1), (7, 10)])]),
        (4, .abundant [(3, 4), (7, 10), (11, 2), (13, 2)]),
        (6, .round 264042040895666103514361 [(7795811, 1), (11794063, 1), (15221321, 1), (71497889, 1), (264042040895666103514361, 1)])]),
      (4, .round 15221321 [(19429, 1), (20143, 1), (160651, 1), (227431, 1), (5492801, 1), (7795811, 1), (15221321, 1), (1001173110774860964055954504873182431, 1)]),
      (6, .round 15221321 [(20143, 1), (160651, 1), (227431, 1), (5492801, 1), (7795811, 1), (15221321, 1)])]),
    (4, .split 15221321 [
      (1, .abundant [(3, 4), (7, 10), (11, 2), (13, 2)]),
      (2, .split 7795811 [
        (2, .split 5492801 [
          (1, .abundant [(3, 2), (7, 10), (11, 2), (13, 2)]),
          (2, .round 1 [(1123, 1), (83443, 1), (107599, 1), (160651, 1), (2064583, 1)])]),
        (4, .abundant [(3, 2), (5, 1), (7, 10)])]),
      (4, .abundant [(3, 2), (5, 1), (7, 10)]),
      (6, .round 1 [(7795811, 1)])]),
    (6, .round 15221321 [(1123, 1), (25537, 1), (160651, 1), (5492801, 1), (7795811, 1), (15221321, 1)])]

private theorem checked7_104 : replayAbundance bank 7 2413 (10^300) 9 state7_104 tree7_104 = true := by
  decide +kernel

theorem reject7_104 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_104 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 9 h tree7_104 checked7_104

@[expose] noncomputable def state7_105 : State := ⟨14402671049986420426422589159899500372996410030019249867546460138504723907274609722249, 16803173717877766576831846719943854318450106985219462642234802853586117413817484942485, 0⟩

private noncomputable def tree7_105 : AbundanceTree :=
  .split 30944468620811041861 [
    (1, .split 502128718657 [
      (2, .abundant [(3, 2), (5, 2), (7, 10)]),
      (4, .round 1 [(29, 1), (41, 1), (71, 1), (277, 1), (307, 1), (1123, 1), (3461, 1), (160651, 1), (5492801, 1), (7795811, 1), (15221321, 1), (140703931, 1)]),
      (6, .round 1 [(140703931, 1)])]),
    (4, .round 15221321 [(5492801, 1), (7795811, 1), (15221321, 1), (140703931, 1)])]

private theorem checked7_105 : replayAbundance bank 7 2413 (10^300) 5 state7_105 tree7_105 = true := by
  decide +kernel

theorem reject7_105 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_105 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree7_105 checked7_105

@[expose] noncomputable def state7_106 : State := ⟨114655204783704437562183923922957708757601682963336816357744816726666336555980442749373473473228636849, 133764863264113225134227474441637385083117330669940803667950408446130430564905303401992875417751802779, 0⟩

private noncomputable def tree7_106 : AbundanceTree :=
  .split 15221321 [
    (1, .split 7795811 [
      (2, .split 5492801 [
        (2, .split 14613541 [
          (2, .round 1 [(67, 1), (277, 1), (463, 1), (647, 1), (967, 1), (1123, 1), (1307, 1), (1549, 1), (22171, 1), (30937, 1), (83443, 1), (107599, 1), (160651, 1), (2064583, 1)]),
          (4, .abundant [(3, 2), (5, 2), (7, 10)])]),
        (4, .abundant [(3, 2), (5, 2), (7, 10)]),
        (6, .round 1 [(1123, 1), (1307, 1), (83443, 1), (107599, 1), (160651, 1)])]),
      (4, .abundant [(3, 2), (5, 2), (7, 10)]),
      (6, .split 5492801 [
        (2, .round 1 [(160651, 1), (2064583, 1), (14613541, 1)])])]),
    (2, .split 7795811 [
      (2, .split 5492801 [
        (1, .split 160651 [
          (2, .split 8602968151 [
            (2, .round 1 [(1123, 1), (83443, 1), (107599, 1), (404432027408324191, 1)])]),
          (4, .abundant [(3, 2), (5, 2), (7, 10)]),
          (6, .round 1 [(277, 1), (463, 1), (967, 1), (1123, 1), (83443, 1), (107599, 1)])]),
        (2, .split 14613541 [
          (1, .split 7306771 [
            (2, .round 1 [(83443, 1), (107599, 1), (160651, 1), (2064583, 1), (117856312921, 1)]),
            (4, .round 1 [(570075058907226260253494341, 1)])]),
          (2, .round 30937 [(463, 1), (967, 1), (1123, 1), (1549, 1), (22171, 1), (30937, 1), (83443, 1), (107599, 1), (160651, 1), (2064583, 1)]),
          (4, .round 1 [(1670658319616551, 1)])]),
        (4, .round 1 [(1123, 1), (2251, 1), (8431, 1), (83443, 1), (107599, 1), (160651, 1), (47343671, 1)]),
        (6, .round 1 [(160651, 1)])]),
      (4, .split 5492801 [
        (1, .abundant [(3, 2), (5, 2), (7, 10)]),
        (2, .split 14613541 [
          (1, .round 1 [(463, 1), (1123, 1), (160651, 1), (2064583, 1), (7306771, 1)]),
          (2, .abundant [(3, 2), (5, 1), (7, 10)])]),
        (4, .round 1 [(47343671, 1)])]),
      (6, .split 5492801 [
        (1, .split 160651 [
          (2, .round 1 [(8602968151, 1)])]),
        (2, .round 1 [(2064583, 1)])])]),
    (4, .split 2826807791 [
      (2, .round 82379817423557809 [(277, 1), (463, 1), (1123, 1), (3541, 1), (6271, 1), (160651, 1), (5492801, 1), (7795811, 1), (218992561, 1), (82379817423557809, 1)]),
      (4, .round 1 [(16559331332345565026531, 1)])]),
    (6, .split 7795811 [
      (2, .round 1 [(1123, 1), (83443, 1), (92051, 1), (107599, 1), (160651, 1)])])]

private theorem checked7_106 : replayAbundance bank 7 2413 (10^300) 8 state7_106 tree7_106 = true := by
  decide +kernel

theorem reject7_106 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_106 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree7_106 checked7_106

@[expose] noncomputable def state7_107 : State := ⟨7265997424746454388499197722764461930192423121919218866008523853310376240254154333152723028992493286932681090936004729669593392986049, 8477026000103103920771957096379218122074651283437022603796781910316402693097716087939941141706227583162542319702912305340360721186167, 0⟩

private noncomputable def tree7_107 : AbundanceTree :=
  .round 1 [(31970812095470591499730311240922035939158187006230932744620190004004638720098511, 1)]

private theorem checked7_107 : replayAbundance bank 7 2413 (10^300) 3 state7_107 tree7_107 = true := by
  decide +kernel

theorem reject7_107 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_107 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_107 checked7_107

@[expose] noncomputable def state7_108 : State := ⟨57842355754765313188565132533591273538726528852130369066596548248270310767047485470644262306390786866796229615396971017518628408572194648401610420649, 67482979276925489787009696311954692882301188645581020822319304861691093516562854866457488015056757017973650301666851374527038203262704677367977789261, 0⟩

private noncomputable def tree7_108 : AbundanceTree :=
  .round 15900000636532709350944313908819383949541632023358496888153281405166246186914398574010913 [(160651, 1), (5492801, 1), (7795811, 1), (15221321, 1), (15900000636532709350944313908819383949541632023358496888153281405166246186914398574010913, 1)]

private theorem checked7_108 : replayAbundance bank 7 2413 (10^300) 3 state7_108 tree7_108 = true := by
  decide +kernel

theorem reject7_108 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_108 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_108 checked7_108

@[expose] noncomputable def state7_109 : State := ⟨227269719783330047893883743283369044594563931618413049, 265148910662299743413869235571692156898695009721684697, 0⟩

private theorem checked7_109 : checkChildren bank 7 2413 (10^300) state7_109 89222701 [state7_103, state7_104, state7_105, state7_106, state7_107, state7_108] = true := by
  decide +kernel

theorem reject7_109 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_109 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state7_103, state7_104, state7_105, state7_106, state7_107, state7_108] ?_ checked7_109
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject7_103 ho hN hs hav hx hvalid
  · exact reject7_104 ho hN hs hav hx hvalid
  · exact reject7_105 ho hN hs hav hx hvalid
  · exact reject7_106 ho hN hs hav hx hvalid
  · exact reject7_107 ho hN hs hav hx hvalid
  · exact reject7_108 ho hN hs hav hx hvalid

@[expose] noncomputable def state7_110 : State := ⟨64159187693137594386047134359251825663845053032319573092471224200824175513841, 74896465631294367790363927815422923539449382163995590241389229159717225218381, 0⟩

private noncomputable def tree7_110 : AbundanceTree :=
  .split 2922391 [
    (2, .split 287347 [
      (2, .split 273253 [
        (1, .split 125407 [
          (4, .split 8503518281771 [
            (2, .round 1 [(79, 1), (197, 1), (241, 1), (277, 1), (317, 1), (431, 1), (1123, 1), (3307, 1), (14389, 1), (120691, 1), (2445609913, 1), (1277255785249, 1)])]),
          (6, .split 13728939001314480265826029 []),
          (10, .round 1 [(71, 1), (79, 1), (197, 1), (277, 1), (317, 1), (431, 1), (1123, 1), (2927, 1), (5171, 1), (14389, 1)]),
          (12, .round 1 [(14389, 1), (126127, 1)])]),
        (2, .split 158563 [
          (2, .split 300247 [
            (4, .split 53819443905840141911 []),
            (6, .split 156967 [
              (2, .round 95089 [(277, 1), (1123, 1), (2423, 1), (14389, 1), (86371, 1), (95089, 1), (125407, 1)]),
              (4, .round 1 [(230706970592411, 1)])])]),
          (4, .abundant [(3, 4), (7, 10), (11, 2), (41, 1), (71, 2), (79, 2)]),
          (6, .split 41865594655627 [
            (2, .round 1 [(584242671956435296772472919, 1)])]),
          (10, .round 14389 [(277, 1), (1123, 1), (14389, 1), (125407, 1), (156967, 1)])]),
        (4, .split 168940682372183621 [
          (1, .split 8381161 [
            (2, .abundant [(3, 4), (7, 10), (13, 2), (31, 2), (61, 2), (71, 2)]),
            (4, .abundant [(3, 4), (5, 2), (7, 10)])]),
          (2, .split 125407 [
            (4, .round 1 [(8503518281771, 1)])])]),
        (6, .split 766327959061576842471367583 []),
        (10, .round 37584772487800093147106735073830996898204481 [(197, 1), (277, 1), (881, 1), (1123, 1), (14389, 1), (125407, 1), (3047441, 1), (37584772487800093147106735073830996898204481, 1)]),
        (12, .round 1 [(125407, 1)])]),
      (4, .split 45198750015791 [
        (2, .split 36374954029 [
          (1, .abundant [(3, 2), (5, 2), (7, 10)]),
          (2, .round 1015015789 [(823, 1), (1123, 1), (1327, 1), (4603, 1), (20029, 1), (125407, 1), (199033, 1), (11172199, 1), (1015015789, 1)])]),
        (4, .abundant [(3, 2), (5, 1), (7, 10)])]),
      (6, .split 2119910228171 [
        (2, .round 56197 [(277, 1), (281, 1), (1123, 1), (21407, 1), (22543, 1), (56197, 1), (125407, 1), (18267551, 1), (199353208335454074091, 1)])]),
      (10, .split 125407 [
        (4, .round 1 [(8503518281771, 1)])]),
      (12, .round 1249 [(79, 1), (197, 1), (277, 1), (1123, 1), (1249, 1), (10271, 1), (125407, 1)])]),
    (4, .split 44071256975293525020151 [
      (2, .abundant [(3, 2), (5, 1), (7, 10)])]),
    (6, .split 1123 [
      (4, .split 1983851 [
        (2, .split 1831394497 [
          (1, .split 190097 [
            (2, .round 1 [(31, 1), (41, 1), (71, 1), (79, 1), (197, 1), (277, 1), (307, 1), (3463, 1), (4261, 1), (4817, 1), (19571, 1)]),
            (4, .round 1 [(2860942796115511, 1)])]),
          (2, .split 17257690903 [])]),
        (4, .round 99581 [(71, 1), (197, 1), (277, 1), (751, 1), (19571, 1), (99581, 1), (679078783976611, 1)]),
        (6, .round 1 [(2369223120158284605160807, 1)])]),
      (6, .split 15852481 [
        (1, .split 7926241 [
          (4, .round 1 [(55160622800223990491671, 1)])]),
        (2, .split 127584187 [
          (2, .round 1 [(3823, 1), (293147, 1), (1949359, 1)])]),
        (4, .round 1 [(2259069000636123729760871, 1)])]),
      (10, .split 1091743984775080451267993 [
        (1, .round 1 [(299764960124953446257, 1)])]),
      (12, .round 1 [(22917277423, 1), (2937027106191751, 1)])]),
    (10, .split 1123 [
      (4, .split 1983851 [
        (2, .round 1 [(19571, 1)])]),
      (6, .round 1 [(3823, 1), (293147, 1)])]),
    (12, .split 1123 [])]

private theorem checked7_110 : replayAbundance bank 7 2413 (10^300) 9 state7_110 tree7_110 = true := by
  decide +kernel

theorem reject7_110 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_110 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 9 h tree7_110 checked7_110

@[expose] noncomputable def state7_111 : State := ⟨187388520470780802309034530427513981431704633335488163059291947570087353763940645721, 218748684180299181622278378748926635451342430312780921337796420833573517687875841071, 0⟩

private noncomputable def tree7_111 : AbundanceTree :=
  .split 22171 [
    (2, .split 23408353 [
      (1, .abundant [(3, 2), (7, 10), (11, 2), (17, 2), (31, 2)]),
      (4, .split 15901 [
        (1, .split 7951 [
          (2, .split 21075451 [
            (2, .abundant [(3, 4), (7, 10), (11, 2), (31, 2), (41, 2)]),
            (4, .abundant [(3, 2), (5, 2), (7, 10)])]),
          (4, .abundant [(3, 2), (5, 2), (7, 10)]),
          (6, .abundant [(3, 2), (7, 10), (11, 2), (31, 2), (41, 2), (71, 2), (197, 2), (211, 2)]),
          (10, .abundant [(3, 2), (7, 10), (11, 2), (23, 2), (31, 2)])]),
        (2, .split 12040843 [
          (4, .split 138977745037897031941 [
            (1, .abundant [(3, 2), (7, 10), (11, 2), (13, 2)])])]),
        (4, .abundant [(3, 2), (5, 1), (7, 10)]),
        (6, .split 1123 [
          (4, .split 1983851 [
            (2, .round 1 [(19571, 1)])]),
          (6, .abundant [(3, 2), (7, 10), (11, 2), (31, 2), (41, 1), (71, 2), (113, 1)])]),
        (10, .abundant [(3, 2), (7, 10), (11, 2), (23, 2), (31, 2)])]),
      (6, .split 31584267505367688706299721376758347163327 [])]),
    (4, .split 110681491 [
      (2, .abundant [(3, 2), (5, 1), (7, 10)]),
      (4, .split 15901 [
        (1, .split 7951 [
          (2, .abundant [(3, 2), (5, 2), (7, 10)]),
          (4, .split 42595031 [
            (2, .round 1 [(685519, 1), (1182073, 1)])]),
          (6, .round 1 [(822067, 1), (1456785048372361, 1)])]),
        (2, .abundant [(3, 2), (5, 2), (7, 10)]),
        (4, .split 15631591 [
          (2, .abundant [(3, 2), (5, 3), (7, 10)])]),
        (6, .round 1381 [(11, 1), (31, 1), (197, 1), (277, 1), (281, 1), (421, 1), (751, 1), (1123, 1), (1381, 1)])]),
      (6, .split 15901 [
        (1, .split 7951 [
          (2, .abundant [(3, 2), (5, 2), (7, 10)]),
          (4, .round 1 [(42595031, 1)])]),
        (2, .abundant [(3, 2), (5, 1), (7, 10)]),
        (4, .round 1 [(15631591, 1)])])]),
    (6, .split 1256510774467663610813 [
      (1, .abundant [(3, 2), (7, 10), (11, 2), (23, 2), (31, 2)]),
      (2, .round 1 [(1578819326353327807408520562177120794131783, 1)])]),
    (10, .split 15901 [
      (1, .split 7951 [
        (2, .split 21075451 [
          (2, .split 12877987183 [
            (2, .abundant [(3, 4), (7, 10), (11, 2), (13, 2)])]),
          (4, .abundant [(3, 2), (5, 2), (7, 10)])]),
        (4, .split 42595031 [
          (2, .round 1 [(3701, 1), (685519, 1), (1182073, 1)])]),
        (6, .round 1 [(1123, 1), (822067, 1), (1456785048372361, 1)])]),
      (2, .split 12040843 [
        (4, .round 138977745037897031941 [(1901, 1), (79561, 1), (138977745037897031941, 1)])]),
      (4, .split 15631591 [
        (2, .abundant [(3, 2), (5, 1), (7, 10)])]),
      (6, .split 1123 [
        (4, .round 1 [(1983851, 1)])])]),
    (12, .split 2358680789697807356834136943635824066434739708333 [
      (1, .abundant [(3, 4), (7, 10), (11, 2), (31, 2), (43, 2)])]),
    (16, .split 15901 [
      (1, .round 1 [(277, 1), (1123, 1), (4931, 1), (7951, 1)]),
      (2, .round 1 [(12040843, 1)])])]

private theorem checked7_111 : replayAbundance bank 7 2413 (10^300) 8 state7_111 tree7_111 = true := by
  decide +kernel

theorem reject7_111 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_111 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree7_111 checked7_111

@[expose] noncomputable def state7_112 : State := ⟨547302091357120544468753281363561962801932520194926903572175864720950302478619929085056001, 638895125660400437904453847473265487606057965928232658773913424182107957355595519204692961, 0⟩

private noncomputable def tree7_112 : AbundanceTree :=
  .split 699906607 [
    (2, .split 17259425773 [
      (1, .split 220021 [
        (2, .split 177324031 [
          (2, .split 52669702089469 [
            (2, .round 1 [(924699172731155938060930477, 1)])]),
          (4, .abundant [(3, 2), (5, 2), (7, 10)])]),
        (4, .abundant [(3, 2), (5, 2), (7, 10)]),
        (6, .round 1 [(66083, 1), (99709, 1), (130589, 1), (113445370872765991132307482674427, 1)]),
        (10, .round 1 [(130589, 1)])]),
      (2, .split 14185132287188384443 [
        (2, .round 1 [(11428294315047104383072428197168899, 1)])]),
      (4, .split 220021 [
        (1, .split 99709 [
          (2, .round 1 [(229, 1), (277, 1), (1123, 1), (2621, 1), (51031, 1), (198241, 1)]),
          (4, .round 1 [(9151031, 1)])]),
        (2, .round 99709 [(71, 1), (197, 1), (277, 1), (1123, 1), (2621, 1), (51031, 1), (99709, 1), (177324031, 1)]),
        (4, .abundant [(3, 2), (5, 1), (7, 10)])])]),
    (4, .split 99709 [
      (1, .split 51031 [
        (2, .abundant [(3, 2), (5, 2), (7, 10)]),
        (4, .split 48439681604861 []),
        (6, .round 1 [(2999984063027871171351751, 1)])]),
      (2, .split 198241 [
        (1, .split 51031 [
          (2, .abundant [(3, 2), (7, 10), (11, 2), (31, 2), (71, 2), (73, 2), (103, 2), (197, 2), (229, 2)]),
          (4, .abundant [(3, 2), (5, 2), (7, 10)]),
          (6, .round 1 [(2999984063027871171351751, 1)])]),
        (2, .split 2352289 [
          (1, .abundant [(3, 2), (5, 2), (7, 10)]),
          (2, .round 5569 [(73, 1), (197, 1), (229, 1), (277, 1), (601, 1), (1123, 1), (5569, 1), (51031, 1), (438417391, 1)]),
          (4, .round 1 [(271082465131, 1)])]),
        (4, .abundant [(3, 2), (5, 1), (7, 10)]),
        (6, .round 1 [(73498848746217019903, 1)])]),
      (4, .split 9151031 [
        (2, .round 1 [(51031, 1), (4547831, 1), (11466709231, 1)])]),
      (6, .round 942060617 [(701, 1), (1123, 1), (14029, 1), (46187, 1), (51031, 1), (263089, 1), (942060617, 1)])]),
    (6, .split 99709 [
      (1, .split 51031 [
        (2, .abundant [(3, 2), (5, 2), (7, 10)]),
        (4, .round 1 [(48439681604861, 1)])]),
      (2, .split 198241 [
        (1, .round 1 [(73, 1), (197, 1), (229, 1), (277, 1), (701, 1), (1123, 1), (9011, 1), (51031, 1)]),
        (2, .round 2352289 [(1123, 1), (5569, 1), (51031, 1), (2352289, 1)])]),
      (4, .round 1 [(4547831, 1), (9151031, 1)])])]

private theorem checked7_112 : replayAbundance bank 7 2413 (10^300) 8 state7_112 tree7_112 = true := by
  decide +kernel

theorem reject7_112 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_112 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree7_112 checked7_112

@[expose] noncomputable def state7_113 : State := ⟨4668693447874128722918132812141879378549798668887168280829878706793591666097307761740846850459273119761, 5450016607196037104099194295292816197911762634031493610004747404479058770106157391081046065817958588341, 0⟩

private noncomputable def tree7_113 : AbundanceTree :=
  .split 1308609482390357027 [
    (2, .round 277 [(71, 1), (197, 1), (277, 1), (1123, 1), (675863, 1), (240439651, 1), (302313163, 1), (5664519402358798843489484839, 1)])]

private theorem checked7_113 : replayAbundance bank 7 2413 (10^300) 4 state7_113 tree7_113 = true := by
  decide +kernel

theorem reject7_113 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_113 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_113 checked7_113

@[expose] noncomputable def state7_114 : State := ⟨13635764248030458152581255059899356405222204526044043541622490971236614100928750930869018320046240274696677241, 15917759954321928845237538893570117749557841011676208481411671359281171212392538711125466326700713727583983831, 0⟩

private noncomputable def tree7_114 : AbundanceTree :=
  .split 259696329409947921881443 [
    (2, .round 1 [(475800499, 1), (29652370262363097578145283, 1)])]

private theorem checked7_114 : replayAbundance bank 7 2413 (10^300) 4 state7_114 tree7_114 = true := by
  decide +kernel

theorem reject7_114 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_114 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_114 checked7_114

@[expose] noncomputable def state7_115 : State := ⟨116318216587987548876313258196584722423869855429404984258928458235032148645566251677382161575408624900560264534522680603401, 135784501424615504766220058320023810901896182768726795670621075098090962179076014033311376482598414317787049950935896550411, 0⟩

private noncomputable def tree7_115 : AbundanceTree :=
  .split 1383604064465335251153235520216235169 [
    (1, .round 1 [(2939, 1), (4217, 1), (83267, 1), (680963417, 1), (42387177726703337089, 1)])]

private theorem checked7_115 : replayAbundance bank 7 2413 (10^300) 4 state7_115 tree7_115 = true := by
  decide +kernel

theorem reject7_115 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_115 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_115 checked7_115

@[expose] noncomputable def state7_116 : State := ⟨339728405142420062239619483262859263673670633225409978830351428326351930938281085515348209052226037983193253980954237307421836081, 396583213405347437076108366154185464048761044985147746349889948448517881201195307448045773741232136164074084459890857892580553501, 0⟩

private noncomputable def tree7_116 : AbundanceTree :=
  .round 1 [(1123, 1), (15474311155246395463946610910558907452312779495655085512711, 1)]

private theorem checked7_116 : replayAbundance bank 7 2413 (10^300) 3 state7_116 tree7_116 = true := by
  decide +kernel

theorem reject7_116 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_116 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_116 checked7_116

@[expose] noncomputable def state7_117 : State := ⟨2898011544615502926218091502670330125060061002753464963250673071668926890692876472814577429787629933571399240765707282679260700027264103000641, 3383004522002223622534212305046668778454501651305182459827949145741392727771788740356982785717376087365967303282595376123558207645638420079281, 0⟩

private noncomputable def tree7_117 : AbundanceTree :=
  .round 1 [(57852552859732474830844372402730122391, 1)]

private theorem checked7_117 : replayAbundance bank 7 2413 (10^300) 3 state7_117 tree7_117 = true := by
  decide +kernel

theorem reject7_117 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_117 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_117 checked7_117

@[expose] noncomputable def state7_118 : State := ⟨21967201379793820135114767535123426921271118972705192074201607159708361, 25628489011666942510555202166795245242491296395313149486632428432648891, 0⟩

private theorem checked7_118 : checkChildren bank 7 2413 (10^300) state7_118 1709 [state7_110, state7_111, state7_112, state7_113, state7_114, state7_115, state7_116, state7_117] = true := by
  decide +kernel

theorem reject7_118 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_118 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state7_110, state7_111, state7_112, state7_113, state7_114, state7_115, state7_116, state7_117] ?_ checked7_118
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject7_110 ho hN hs hav hx hvalid
  · exact reject7_111 ho hN hs hav hx hvalid
  · exact reject7_112 ho hN hs hav hx hvalid
  · exact reject7_113 ho hN hs hav hx hvalid
  · exact reject7_114 ho hN hs hav hx hvalid
  · exact reject7_115 ho hN hs hav hx hvalid
  · exact reject7_116 ho hN hs hav hx hvalid
  · exact reject7_117 ho hN hs hav hx hvalid

@[expose] noncomputable def state7_119 : State := ⟨205230092602125873813154752894915541530378114922390706460050379432053081549167510648859368591777439301481, 239435924594156877167128773295217604346815671616386539713993842349019383694750259002200880088074647220831, 0⟩

private noncomputable def tree7_119 : AbundanceTree :=
  .split 1123 [
    (4, .split 1983851 [
      (2, .split 1831394497 [
        (1, .split 190097 [
          (2, .split 19571 [
            (2, .round 1 [(67, 1), (79, 1), (89, 1), (277, 1), (283, 1), (307, 1), (3463, 1), (4261, 1), (4817, 1), (31477, 1)]),
            (4, .round 1 [(29342982506103941, 1)])]),
          (4, .round 1 [(456451, 1), (2860942796115511, 1)])]),
        (2, .split 17257690903 [
          (2, .round 166062471846877 [(597823, 1), (9254689, 1), (166062471846877, 1)])]),
        (4, .round 1 [(1305391, 1)])]),
      (4, .split 679078783976611 []),
      (6, .round 1 [(2369223120158284605160807, 1)])]),
    (6, .split 15852481 [
      (1, .split 7926241 [
        (4, .round 1 [(55160622800223990491671, 1)])]),
      (2, .split 127584187 [
        (2, .round 5786761 [(89, 1), (113, 1), (277, 1), (367, 1), (1789, 1), (3823, 1), (293147, 1), (1949359, 1), (5786761, 1)])]),
      (4, .round 1 [(2259069000636123729760871, 1)])]),
    (10, .split 1091743984775080451267993 [
      (1, .round 1 [(265871, 1), (299764960124953446257, 1)])]),
    (12, .split 2937027106191751 []),
    (16, .round 1 [(3330387172446132796579, 1)])]

private theorem checked7_119 : replayAbundance bank 7 2413 (10^300) 8 state7_119 tree7_119 = true := by
  decide +kernel

theorem reject7_119 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_119 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree7_119 checked7_119

@[expose] noncomputable def state7_120 : State := ⟨19836917903901571338101100479818148331817668709121757901681847256071388320251300522496107523521696618408321184124866474809, 23143149813936485631394447994308260647961616037318163610436990239499871470228347578659881677283262203872643537025792566817, 0⟩

private noncomputable def tree7_120 : AbundanceTree :=
  .split 1123 [
    (4, .split 1983851 [
      (2, .split 1831394497 [
        (1, .round 1 [(41, 1), (79, 1), (277, 1), (307, 1), (599, 1), (4817, 1), (19571, 1), (190097, 1)]),
        (2, .round 1 [(17257690903, 1)])]),
      (4, .round 1 [(679078783976611, 1)])]),
    (6, .split 15852481 [
      (1, .split 7926241 []),
      (2, .round 1 [(3823, 1), (293147, 1), (127584187, 1)])]),
    (10, .round 1091743984775080451267993 [(11, 1), (79, 1), (277, 1), (599, 1), (265871, 1), (1091743984775080451267993, 1)]),
    (12, .round 1 [(2937027106191751, 1)])]

private theorem checked7_120 : replayAbundance bank 7 2413 (10^300) 6 state7_120 tree7_120 = true := by
  decide +kernel

theorem reject7_120 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_120 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree7_120 checked7_120

@[expose] noncomputable def state7_121 : State := ⟨185327772435466198033726283954809236986122715868178382982815008648192286398903078675366485335402679911390381767948273110032129638785699990750594762432368089, 216216471880116966258321845294366630915858121409009142899466373036218576627884377161500484354395415565678814256380182901744325965894384525186854263413196677, 0⟩

private noncomputable def tree7_121 : AbundanceTree :=
  .round 3877 [(277, 1), (1123, 1), (3877, 1)]

private theorem checked7_121 : replayAbundance bank 7 2413 (10^300) 3 state7_121 tree7_121 = true := by
  decide +kernel

theorem reject7_121 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_121 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_121 checked7_121

@[expose] noncomputable def state7_122 : State := ⟨24326255661193460569, 28380728301423624437, 0⟩

private theorem checked7_122 : checkChildren bank 7 2413 (10^300) state7_122 310897033 [state7_96, state7_102, state7_109, state7_118, state7_119, state7_120, state7_121] = true := by
  decide +kernel

theorem reject7_122 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_122 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state7_96, state7_102, state7_109, state7_118, state7_119, state7_120, state7_121] ?_ checked7_122
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject7_96 ho hN hs hav hx hvalid
  · exact reject7_102 ho hN hs hav hx hvalid
  · exact reject7_109 ho hN hs hav hx hvalid
  · exact reject7_118 ho hN hs hav hx hvalid
  · exact reject7_119 ho hN hs hav hx hvalid
  · exact reject7_120 ho hN hs hav hx hvalid
  · exact reject7_121 ho hN hs hav hx hvalid

@[expose] noncomputable def state7_123 : State := ⟨588911924725291963766244814482095770126166579726000004048047338773164417987774449, 687593953755555756003197808173328077939545496688778990873968753159677743958193801, 0⟩

private noncomputable def tree7_123 : AbundanceTree :=
  .split 15326501 [
    (2, .split 23615827 [
      (2, .split 301471069 [
        (1, .abundant [(3, 2), (5, 2), (7, 10)]),
        (4, .split 28031060066997623719607731 []),
        (6, .split 17458438261823805936789744207109210876552864352137 [])]),
      (4, .split 9946789 [
        (1, .abundant [(3, 2), (5, 2), (7, 10)]),
        (2, .split 34317940117 [
          (1, .split 3777013 [
            (2, .abundant [(3, 4), (7, 10), (11, 4), (31, 2), (59, 2)]),
            (4, .round 1 [(172440016272121496741, 1)])])]),
        (4, .split 34835764455386714637920341 [
          (1, .round 1 [(17417882227693357318960171, 1)])]),
        (6, .split 1291 [
          (2, .round 1 [(751, 1), (907, 1), (1123, 1)])])]),
      (6, .split 9946789 [
        (1, .abundant [(3, 2), (5, 2), (7, 10)]),
        (2, .abundant [(3, 2), (7, 10), (11, 2), (29, 1), (31, 2), (71, 2)]),
        (4, .round 34835764455386714637920341 [(241, 1), (281, 1), (631, 1), (751, 1), (1123, 1), (2549, 1), (34835764455386714637920341, 1)])]),
      (10, .round 1 [(751, 1), (1123, 1)])]),
    (4, .abundant [(3, 2), (5, 1), (7, 10)]),
    (6, .split 1123 [
      (4, .split 1983851 [
        (2, .split 1831394497 [
          (1, .split 190097 [
            (2, .abundant [(3, 2), (7, 10), (11, 2), (31, 2), (41, 2), (43, 2)]),
            (4, .round 1 [(2860942796115511, 1)])]),
          (2, .round 9254689 [(71, 1), (241, 1), (307, 1), (751, 1), (19571, 1), (9254689, 1), (17257690903, 1)])]),
        (4, .abundant [(3, 2), (5, 1), (7, 10)])]),
      (6, .split 15852481 [
        (1, .split 7926241 []),
        (2, .split 127584187 [
          (2, .abundant [(3, 4), (7, 10), (11, 2), (13, 1)])]),
        (4, .abundant [(3, 2), (5, 1), (7, 10)])]),
      (10, .split 1091743984775080451267993 [
        (1, .round 1 [(299764960124953446257, 1)])]),
      (12, .round 1 [(22917277423, 1), (2937027106191751, 1)])]),
    (10, .split 1123 [
      (4, .round 1 [(19571, 1), (1983851, 1)])]),
    (12, .round 1 [(1123, 1)])]

private theorem checked7_123 : replayAbundance bank 7 2413 (10^300) 8 state7_123 tree7_123 = true := by
  decide +kernel

theorem reject7_123 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_123 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree7_123 checked7_123

@[expose] noncomputable def state7_124 : State := ⟨999859966005923223710004342231032537382136754558020340872811204195127507339405349482241, 1167403203031766673356583095102459010109785513183233394553073708068580465195962884901233, 0⟩

private noncomputable def tree7_124 : AbundanceTree :=
  .split 1123 [
    (4, .split 1983851 [
      (2, .split 1831394497 [
        (1, .split 190097 [
          (2, .split 19571 [
            (2, .split 31477 [
              (2, .split 294103 [
                (2, .split 3198967 [
                  (2, .round 1 [(151, 1), (283, 1), (307, 1), (751, 1), (1117, 1), (3463, 1), (4261, 1), (4817, 1), (9013, 1), (2889151, 1)]),
                  (4, .round 1 [(2249142005286109349681, 1)])]),
                (4, .round 1 [(3463, 1), (4261, 1), (4817, 1), (111191, 1), (1973011, 1), (831794981, 1)]),
                (6, .round 1 [(19156241955924193663870069, 1)])]),
              (4, .split 187673266740451 []),
              (6, .round 1 [(4817, 1), (972688545870895998743279227, 1)])]),
            (4, .abundant [(3, 2), (5, 2), (7, 10)]),
            (6, .round 1 [(41, 1), (79, 1), (307, 1), (743, 1), (751, 1), (3463, 1), (4261, 1), (4817, 1), (550789, 1), (585271, 1), (8090422789, 1)]),
            (10, .round 1 [(3463, 1), (4261, 1), (4817, 1)])]),
          (4, .split 2860942796115511 [
            (2, .round 1 [(456451, 1), (1567696597, 1), (1812511449097, 1)])]),
          (6, .split 70100353947691380349 []),
          (10, .round 1 [(21872661262105931506286746335805995179871106877, 1)])]),
        (2, .split 17257690903 [
          (2, .split 166062471846877 [
            (1, .split 83031235923439 [
              (2, .round 1 [(19752813250054781829007, 1)])]),
            (2, .round 187596901740782192420452381 [(751, 1), (19571, 1), (597823, 1), (9254689, 1), (187596901740782192420452381, 1)])]),
          (4, .round 1 [(821538522595690918631, 1)])]),
        (4, .split 378510836590119752613221 [
          (1, .round 1 [(1305391, 1), (80835531031, 1), (780413496727, 1)])]),
        (6, .round 1093208355208482471225341744517042144744723375133 [(673, 1), (751, 1), (19571, 1), (51283, 1), (1093208355208482471225341744517042144744723375133, 1)])]),
      (4, .abundant [(3, 2), (5, 1), (7, 10)]),
      (6, .split 2369223120158284605160807 []),
      (10, .round 29513949537333245294691327574113530231096889670837359841 [(23, 1), (41, 1), (751, 1), (19571, 1), (126457, 1), (29513949537333245294691327574113530231096889670837359841, 1)])]),
    (6, .split 15852481 [
      (1, .split 7926241 [
        (4, .abundant [(3, 2), (5, 2), (7, 10)]),
        (6, .round 1 [(293147, 1), (1202447, 1), (397036059341206702173346083943, 1)])]),
      (2, .split 127584187 [
        (2, .split 5786761 [
          (1, .split 1949359 [
            (2, .split 97435960519 []),
            (4, .abundant [(3, 4), (7, 10), (11, 2), (13, 2)]),
            (6, .round 1 [(2109226992584967454458432923, 1)])]),
          (4, .abundant [(3, 4), (5, 1), (7, 10)]),
          (6, .round 1 [(78739190424682001507709151, 1)])]),
        (4, .round 1 [(151, 1), (367, 1), (751, 1), (3823, 1), (4651, 1), (6271, 1), (41351, 1), (293147, 1), (3226002944164951, 1)]),
        (6, .round 4313016370613880652773372788298434532293960014237 [(1789, 1), (3823, 1), (293147, 1), (4313016370613880652773372788298434532293960014237, 1)])]),
      (4, .abundant [(3, 2), (5, 1), (7, 10)]),
      (6, .round 1 [(3823, 1), (293147, 1), (385267, 1), (120161935554310741570451765250151, 1)])]),
    (10, .split 1091743984775080451267993 [
      (1, .split 299764960124953446257 [
        (2, .round 1 [(10295124177825558793, 1)])]),
      (2, .round 1 [(273818481499, 1), (234644065482067, 1)])]),
    (12, .split 2937027106191751 [
      (2, .round 106442138516353 [(79, 1), (751, 1), (3163, 1), (24697, 1), (4377343, 1), (1128748349, 1), (22917277423, 1), (106442138516353, 1)])]),
    (16, .split 3330387172446132796579 []),
    (18, .split 10612992450021439543353331638426864955619439336698933 []),
    (22, .round 402363029321257669799797253 [(33658073731, 1), (41292578210753, 1), (402363029321257669799797253, 1)])]

private theorem checked7_124 : replayAbundance bank 7 2413 (10^300) 11 state7_124 tree7_124 = true := by
  decide +kernel

theorem reject7_124 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_124 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 11 h tree7_124 checked7_124

@[expose] noncomputable def state7_125 : State := ⟨2882151744735123064139530121326022976819706815870503925835170433792989639187598853969174971752357921, 3365104407438036336482862196876046048524201844626620603752346935943450735692775034563929332582392513, 0⟩

private noncomputable def tree7_125 : AbundanceTree :=
  .split 435647383171675304477 [
    (1, .split 6267119 [
      (4, .split 23565541864751 [
        (2, .round 1 [(6397, 1), (1937891, 1), (1166355026258533, 1)])]),
      (6, .round 1 [(652271327, 1), (1049191168112126929333553159, 1)])]),
    (2, .split 573067982664279603907380297685333 [
      (1, .split 6267119 [])])]

private theorem checked7_125 : replayAbundance bank 7 2413 (10^300) 6 state7_125 tree7_125 = true := by
  decide +kernel

theorem reject7_125 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_125 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree7_125 checked7_125

@[expose] noncomputable def state7_126 : State := ⟨4893343171576994554403671495758413744251289609346284399818284879027641946319458022658550989615899049495089, 5713304548887965034407631783615923176411376437229187140067492111962768374952146381893251450626425075923241, 0⟩

private noncomputable def tree7_126 : AbundanceTree :=
  .split 201000007517992361490787 [
    (2, .split 109106389471 [
      (2, .round 1 [(1123, 1), (18074731, 1), (279131659, 1)])])]

private theorem checked7_126 : replayAbundance bank 7 2413 (10^300) 5 state7_126 tree7_126 = true := by
  decide +kernel

theorem reject7_126 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_126 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree7_126 checked7_126

@[expose] noncomputable def state7_127 : State := ⟨14105332785636090234095431430592658623385570831369892868727518893092071068441959624467387820191416756982183513237737809, 16468916881989667092958015980623781766069552519076849301428647003063859445003544352441148694078341891782302325707178361, 0⟩

private noncomputable def tree7_127 : AbundanceTree :=
  .split 35922462993765878557295703991437520493 [
    (1, .round 1 [(67, 1), (751, 1), (1123, 1), (6317, 1), (1923437047717, 1), (14145854152447308556668810448091, 1)])]

private theorem checked7_127 : replayAbundance bank 7 2413 (10^300) 4 state7_127 tree7_127 = true := by
  decide +kernel

theorem reject7_127 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_127 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_127 checked7_127

@[expose] noncomputable def state7_128 : State := ⟨23948160951448024724259330341743091144711632627637286441561400124361756088640375028057351247611369092755164008426650391760481, 27961075302493994697427956154046882296468780892861346746421819567230357179893346346469308447980787262180320083710624611730273, 0⟩

private noncomputable def tree7_128 : AbundanceTree :=
  .split 33402117805176599431254583 [
    (2, .round 1 [(212237107, 1)])]

private theorem checked7_128 : replayAbundance bank 7 2413 (10^300) 4 state7_128 tree7_128 = true := by
  decide +kernel

theorem reject7_128 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_128 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_128 checked7_128

@[expose] noncomputable def state7_129 : State := ⟨69031900682184706905893743569344130686259124914218344567363133138430685026611196373787889736994475029815567423991120478734508851584191361, 80599348616459975103141932572273919326947035678735780124637482157029647151577440975509788754626293251700168195963899930913855752003160753, 0⟩

private noncomputable def tree7_129 : AbundanceTree :=
  .split 1044922546780909920647393 [
    (1, .round 1 [(235170205927, 1), (450857606831, 1), (288503080269369527, 1)])]

private theorem checked7_129 : replayAbundance bank 7 2413 (10^300) 4 state7_129 tree7_129 = true := by
  decide +kernel

theorem reject7_129 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_129 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_129 checked7_129

@[expose] noncomputable def state7_130 : State := ⟨337844089481375116434301212302692336414168587694697718516663851813551900938218057804982165098140315819053122612521863811077647889998887743932330348970491569, 394455509366370264673992730055578671740851725707382288085007695944744394273396932623028215511051015695082126336540046492973640309763256482856014484373321321, 0⟩

private noncomputable def tree7_130 : AbundanceTree :=
  .split 1223601162034160415425106618141008313973 []

private theorem checked7_130 : replayAbundance bank 7 2413 (10^300) 3 state7_130 tree7_130 = true := by
  decide +kernel

theorem reject7_130 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_130 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_130 checked7_130

@[expose] noncomputable def state7_131 : State := ⟨573594735718284005058204506958421772995003155705347038777058537583714739380015062503818964743108511460430763049643133075221930286471121601638005857455241320272321, 669710113901807732695886923022931969089663727571525015151318831244250535296921772779770911859414563733857198872746043509184637505515176419136588250103430124504913, 0⟩

private noncomputable def tree7_131 : AbundanceTree :=
  .round 143691831909885691760575432292450544282827896784201 [(24084691605091313324674217015697893, 1), (143691831909885691760575432292450544282827896784201, 1)]

private theorem checked7_131 : replayAbundance bank 7 2413 (10^300) 3 state7_131 tree7_131 = true := by
  decide +kernel

theorem reject7_131 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_131 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_131 checked7_131

@[expose] noncomputable def state7_132 : State := ⟨204302031671975042190698162882964869913501220929736828919521867320529, 238353182383133059079318499779904566123340745163524003952763838823481, 0⟩

private theorem checked7_132 : checkChildren bank 7 2413 (10^300) state7_132 1303 [state7_123, state7_124, state7_125, state7_126, state7_127, state7_128, state7_129, state7_130, state7_131] = true := by
  decide +kernel

theorem reject7_132 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_132 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state7_123, state7_124, state7_125, state7_126, state7_127, state7_128, state7_129, state7_130, state7_131] ?_ checked7_132
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject7_123 ho hN hs hav hx hvalid
  · exact reject7_124 ho hN hs hav hx hvalid
  · exact reject7_125 ho hN hs hav hx hvalid
  · exact reject7_126 ho hN hs hav hx hvalid
  · exact reject7_127 ho hN hs hav hx hvalid
  · exact reject7_128 ho hN hs hav hx hvalid
  · exact reject7_129 ho hN hs hav hx hvalid
  · exact reject7_130 ho hN hs hav hx hvalid
  · exact reject7_131 ho hN hs hav hx hvalid

@[expose] noncomputable def state7_133 : State := ⟨19923940570432313844993647770138324063558343137168500194196499472744661833510254383254170095323681017591969, 23244676529696931541952895300555831164702735978122005522136913299045377919396673853550787728085237538101185, 0⟩

private noncomputable def tree7_133 : AbundanceTree :=
  .split 172918880358232491224830637233905569874719873338729915557207194422824133751 []

private theorem checked7_133 : replayAbundance bank 7 2413 (10^300) 3 state7_133 tree7_133 = true := by
  decide +kernel

theorem reject7_133 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_133 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_133 checked7_133

@[expose] noncomputable def state7_134 : State := ⟨1943022321439654259647522529664977245222916707075503082139554051649256140820766885442487779880217650355183506624034918526934928625203322231741809, 2266867098513212457859967917926628108245696760463552130521325985966289916101059401736478310938516456816995216602094849081737206574355026665808329, 0⟩

private noncomputable def tree7_134 : AbundanceTree :=
  .round 1 [(743774360151624041075673590061627066616453777374105767207030502752698292162536397044908712056989445919018046471, 1)]

private theorem checked7_134 : replayAbundance bank 7 2413 (10^300) 3 state7_134 tree7_134 = true := by
  decide +kernel

theorem reject7_134 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_134 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_134 checked7_134

@[expose] noncomputable def state7_135 : State := ⟨2094932977627880202150633343489, 2444096801243283221193001600817, 0⟩

private theorem checked7_135 : checkChildren bank 7 2413 (10^300) state7_135 9875322243666178231 [state7_132, state7_133, state7_134] = true := by
  decide +kernel

theorem reject7_135 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_135 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state7_132, state7_133, state7_134] ?_ checked7_135
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact reject7_132 ho hN hs hav hx hvalid
  · exact reject7_133 ho hN hs hav hx hvalid
  · exact reject7_134 ho hN hs hav hx hvalid

@[expose] noncomputable def state7_136 : State := ⟨1520691273444858815591912791321913935608743861, 1774356344935998797214899499398041961382082710, 8429⟩

private noncomputable def tree7_136 : AbundanceTree :=
  .abundant [(3, 2), (5, 2), (7, 10)]

private theorem checked7_136 : replayAbundance bank 7 2413 (10^300) 3 state7_136 tree7_136 = true := by
  decide +kernel

theorem reject7_136 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_136 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_136 checked7_136

end OddPerfect.IndexComponent.Size300
