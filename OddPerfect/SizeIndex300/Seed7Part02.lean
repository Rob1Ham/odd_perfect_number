module

public import OddPerfect.SizeIndex300.Seed7Part01

public section

namespace OddPerfect.IndexComponent.Size300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def state7_47 : State := ⟨184271951629196787969053, 215849826580451085443934, 4733⟩

private noncomputable def tree7_47 : AbundanceTree :=
  .split 192750517 [
    (2, .split 78785754721 [
      (2, .split 680310719936857 [
        (2, .abundant [(3, 6), (7, 6), (13, 2), (29, 2), (73, 2), (97, 2)]),
        (4, .split 3240013750326687956657499283744699755129884738233781 []),
        (6, .round 1 [(7211, 1), (63659, 1), (157189, 1), (434479, 1), (46101931, 1), (17354266853252267, 1)])]),
      (4, .abundant [(3, 4), (5, 2), (7, 6)]),
      (6, .split 1743472668312840089541755093310371 [
        (2, .round 1 [(57620388685963446617, 1)])]),
      (10, .split 157189 [
        (2, .round 1 [(239, 1), (7211, 1), (1176597091, 1)])])]),
    (4, .split 4844027097467060229431 [
      (2, .abundant [(3, 2), (7, 6), (11, 2), (13, 2)]),
      (4, .abundant [(3, 2), (5, 2), (7, 6)])]),
    (6, .split 493020374806711829071 [
      (2, .split 36313138890414869617 [
        (2, .round 1 [(64525231, 1), (557597259471113, 1), (1666539090921748667841027474289981, 1)])]),
      (4, .abundant [(3, 2), (5, 2), (7, 6)])]),
    (10, .split 243432201843957984755042149137416484613647544400935419182889216793489291 []),
    (12, .round 1 [(438997499172919904984298559699300058736178987500419568679184679163115245097, 1)]),
    (16, .round 1 [(7211, 1)])]

private theorem checked7_47 : replayAbundance bank 7 2413 (10^300) 6 state7_47 tree7_47 = true := by
  decide +kernel

theorem reject7_47 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_47 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree7_47 checked7_47

@[expose] noncomputable def state7_48 : State := ⟨881621615153712516499136771188733, 1032701238891933874142201258508414, 4733⟩

private noncomputable def tree7_48 : AbundanceTree :=
  .split 3124914562747294549 [
    (4, .split 478843754680778393547386148766246292646357256397616780775018111 []),
    (6, .split 307977209 [
      (2, .round 1 [(629567, 1), (6653904277, 1)])])]

private theorem checked7_48 : replayAbundance bank 7 2413 (10^300) 5 state7_48 tree7_48 = true := by
  decide +kernel

theorem reject7_48 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_48 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree7_48 checked7_48

@[expose] noncomputable def state7_49 : State := ⟨60980885498567141053728791326353472877, 71430911992916174140541919021308992398, 4733⟩

private noncomputable def tree7_49 : AbundanceTree :=
  .split 539093310059453790343 [
    (2, .split 17301541349415751184286073 [
      (2, .split 4897992001279902468859 [
        (2, .round 1 [(92649771797757775770073883289709, 1)])])]),
    (4, .round 1 [(301211, 1), (644739790948604408912946243964751555483005423397828932600903479211584446023944571, 1)]),
    (6, .round 1 [(301211, 1)])]

private theorem checked7_49 : replayAbundance bank 7 2413 (10^300) 6 state7_49 tree7_49 = true := by
  decide +kernel

theorem reject7_49 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_49 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree7_49 checked7_49

@[expose] noncomputable def state7_50 : State := ⟨291753933745346465996573473924091172043373233997, 341750523866050125775275423113628114190407596718, 4733⟩

private noncomputable def tree7_50 : AbundanceTree :=
  .split 481003352262457 [
    (4, .split 938437344329450506846644744944508774142306782882282661 []),
    (6, .round 1 [(383780125176082672784933259554837783992839964968595483988765164423343706948461779, 1)])]

private theorem checked7_50 : replayAbundance bank 7 2413 (10^300) 4 state7_50 tree7_50 = true := by
  decide +kernel

theorem reject7_50 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_50 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_50 checked7_50

@[expose] noncomputable def state7_51 : State := ⟨20180327843231869706516990617855462279068083222338493, 23638541985290821149750025741346543030436474597891774, 4733⟩

private noncomputable def tree7_51 : AbundanceTree :=
  .split 36379600869079813407167833690281003289076473 [
    (2, .round 1 [(6043266481249099155043506469751380212900667829056909046598424996930850347630358589937, 1)])]

private theorem checked7_51 : replayAbundance bank 7 2413 (10^300) 4 state7_51 tree7_51 = true := by
  decide +kernel

theorem reject7_51 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_51 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_51 checked7_51

@[expose] noncomputable def state7_52 : State := ⟨96549762837930315883453469418568517571773722521989856716444573, 113095071608548193915957200665375774043079387329151215045746654, 4733⟩

private noncomputable def tree7_52 : AbundanceTree :=
  .split 2660939892939529745485461033791647 [
    (2, .round 1 [(1321, 1), (5107, 1), (1647035419, 1), (272509811686691, 1), (1084783618177512525019860906248081411183171284249447081, 1)])]

private theorem checked7_52 : replayAbundance bank 7 2413 (10^300) 4 state7_52 tree7_52 = true := by
  decide +kernel

theorem reject7_52 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_52 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_52 checked7_52

@[expose] noncomputable def state7_53 : State := ⟨31951091744994424899587667796156690592055909451248815646899733216917020728557, 37426409994782939023405708348776790136169691162301646201862740750314646052878, 4733⟩

private noncomputable def tree7_53 : AbundanceTree :=
  .split 3263407034245679124330139904752352597834225347 [
    (2, .abundant [(3, 4), (7, 6), (13, 2), (29, 2), (59, 2), (109, 2)])]

private theorem checked7_53 : replayAbundance bank 7 2413 (10^300) 4 state7_53 tree7_53 = true := by
  decide +kernel

theorem reject7_53 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_53 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_53 checked7_53

@[expose] noncomputable def state7_54 : State := ⟨2210025064909519375879579393792362131561915200833429329480407646880933406773559133, 2588747352929141109309949440776541796928721368005242566136643914958513924372022814, 4733⟩

private noncomputable def tree7_54 : AbundanceTree :=
  .split 290966192645581900300968995258848794450391 [
    (2, .round 1 [(236710809243580736963, 1)])]

private theorem checked7_54 : replayAbundance bank 7 2413 (10^300) 4 state7_54 tree7_54 = true := by
  decide +kernel

theorem reject7_54 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_54 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_54 checked7_54

@[expose] noncomputable def state7_55 : State := ⟨731360818836942452930257494544734145212284356427338096176016541032273300234137821301141482087597, 856690909918588559323558318159547486902215577698002139117406343780046106023916503669767663946318, 4733⟩

private noncomputable def tree7_55 : AbundanceTree :=
  .split 436999576289754237796902293505941268479 []

private theorem checked7_55 : replayAbundance bank 7 2413 (10^300) 3 state7_55 tree7_55 = true := by
  decide +kernel

theorem reject7_55 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_55 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_55 checked7_55

@[expose] noncomputable def state7_56 : State := ⟨3499086543895944992201593537899553247242248124764658976176396692833036283080518716693433999766166158091917, 4098709635472599638127848020002847506466755251302375622865563085729022447961390403749611493606682688745838, 4733⟩

private noncomputable def tree7_56 : AbundanceTree :=
  .round 1 [(45025709, 1), (392376151, 1), (181627957627, 1), (1965796395871967711901639812168202247638752123911666233267819054341657, 1)]

private theorem checked7_56 : replayAbundance bank 7 2413 (10^300) 3 state7_56 tree7_56 = true := by
  decide +kernel

theorem reject7_56 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_56 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_56 checked7_56

@[expose] noncomputable def state7_57 : State := ⟨242028317154738619165592023422974198558499060541846696723145182846568286664396399114968136329825946989059806973, 283503646776004244369665119695576959174798993977334019457988133076790753703041412836956877401280635069401373054, 4733⟩

private noncomputable def tree7_57 : AbundanceTree :=
  .round 1 [(150244794430249657, 1), (44526645292767619795851584398018381457427136775197089212581942491500603597, 1)]

private theorem checked7_57 : replayAbundance bank 7 2413 (10^300) 3 state7_57 tree7_57 = true := by
  decide +kernel

theorem reject7_57 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_57 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_57 checked7_57

@[expose] noncomputable def state7_58 : State := ⟨1157948314957159636413265549160831747161880371621357207443376517236426559227613730832077706546727250509464548353824261853, 1356380831498321747888388406797665773846623663897693637278210440417286498558759010912727237927625228512738598561766744734, 4733⟩

private noncomputable def tree7_58 : AbundanceTree :=
  .round 1 [(366824236426951613048418029470643784174609262985099501022265244787667370413787704633126552604522339479, 1)]

private theorem checked7_58 : replayAbundance bank 7 2413 (10^300) 3 state7_58 tree7_58 = true := by
  decide +kernel

theorem reject7_58 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_58 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_58 checked7_58

@[expose] noncomputable def state7_59 : State := ⟨383198381432202461669552472356699155102318656825754567989021931199127987585768042864130844497044524978570584670975653618728906152748077, 448865404890762667148850047789000047772460237974592506222171392815461638402893049025103480988908395927318635492134587371398736543739598, 4733⟩

private noncomputable def tree7_59 : AbundanceTree :=
  .round 1 [(631172722633094599282215430260850529796246854551094582836527975364552271665451, 1)]

private theorem checked7_59 : replayAbundance bank 7 2413 (10^300) 3 state7_59 tree7_59 = true := by
  decide +kernel

theorem reject7_59 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_59 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_59 checked7_59

@[expose] noncomputable def state7_60 : State := ⟨126811359052491365357278278812118873133243213917782784959431204230200926802986889825790771353129188525072006847226472430087975373320086365923701575293, 148542464644818004724349789000881230267858563136215291143630961522243024971312574140739886606168778504923603614927145785758056683155088963583189976574, 4733⟩

private noncomputable def tree7_60 : AbundanceTree :=
  .round 1 [(462910106379718736683354511448413225253159633545128098281364110024091275400569751303369305754589541, 1)]

private theorem checked7_60 : replayAbundance bank 7 2413 (10^300) 3 state7_60 tree7_60 = true := by
  decide +kernel

theorem reject7_60 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_60 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_60 checked7_60

@[expose] noncomputable def state7_61 : State := ⟨556832717, 649774638, 4733⟩

private theorem checked7_61 : checkChildren bank 7 2413 (10^300) state7_61 263 [state7_45, state7_46, state7_47, state7_48, state7_49, state7_50, state7_51, state7_52, state7_53, state7_54, state7_55, state7_56, state7_57, state7_58, state7_59, state7_60] = true := by
  decide +kernel

theorem reject7_61 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_61 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state7_45, state7_46, state7_47, state7_48, state7_49, state7_50, state7_51, state7_52, state7_53, state7_54, state7_55, state7_56, state7_57, state7_58, state7_59, state7_60] ?_ checked7_61
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject7_45 ho hN hs hav hx hvalid
  · exact reject7_46 ho hN hs hav hx hvalid
  · exact reject7_47 ho hN hs hav hx hvalid
  · exact reject7_48 ho hN hs hav hx hvalid
  · exact reject7_49 ho hN hs hav hx hvalid
  · exact reject7_50 ho hN hs hav hx hvalid
  · exact reject7_51 ho hN hs hav hx hvalid
  · exact reject7_52 ho hN hs hav hx hvalid
  · exact reject7_53 ho hN hs hav hx hvalid
  · exact reject7_54 ho hN hs hav hx hvalid
  · exact reject7_55 ho hN hs hav hx hvalid
  · exact reject7_56 ho hN hs hav hx hvalid
  · exact reject7_57 ho hN hs hav hx hvalid
  · exact reject7_58 ho hN hs hav hx hvalid
  · exact reject7_59 ho hN hs hav hx hvalid
  · exact reject7_60 ho hN hs hav hx hvalid

@[expose] noncomputable def state7_62 : State := ⟨2635489249561, 3075383498911, 0⟩

private noncomputable def tree7_62 : AbundanceTree :=
  .split 22406023 [
    (4, .split 829007553280001 [
      (1, .split 304018940824561 [
        (2, .split 69867248717034037 [
          (2, .split 125164934443279342539625921373113 [
            (2, .round 1 [(62995328779, 1), (138167925546667, 1)])]),
          (4, .split 138167925546667 [
            (2, .abundant [(3, 4), (7, 6), (11, 2), (13, 2)])])]),
        (4, .abundant [(3, 2), (5, 2), (7, 6)]),
        (6, .split 138167925546667 [
          (2, .round 1 [(4839650905501262512741, 1)])])]),
      (2, .split 687015720002749009 [
        (1, .split 304018940824561 [
          (2, .abundant [(3, 2), (5, 2), (7, 6)]),
          (4, .round 1 [(6199228913, 1), (1708569156838289884502224293573384003719946739712411044321, 1)]),
          (6, .round 1 [(6199228913, 1)])]),
        (4, .round 1 [(6256017851, 1), (54297214168168410671, 1), (93023780264561775745652559396701131, 1)])]),
      (4, .split 3050471924995169743725212337745231 [
        (2, .abundant [(3, 2), (5, 1), (7, 6)])]),
      (6, .split 304018940824561 [
        (1, .split 709140083 [
          (2, .round 1 [(2447, 1), (24019, 1), (49477, 1), (68001766309, 1)])]),
        (2, .round 69867248717034037 [(49477, 1), (709140083, 1), (62995328779, 1), (69867248717034037, 1)])])]),
    (6, .split 21431736905122215024105943 [
      (2, .split 26983767183403223367538633378897 [
        (1, .split 2563008738743291 [
          (2, .split 62316423268709 [
            (2, .round 1 [(275434440766579, 1)])])]),
        (2, .round 1 [(3415691950142456972644496836155892254480424753327207, 1)])]),
      (4, .split 62316423268709 [
        (1, .abundant [(3, 2), (5, 2), (7, 6)])])]),
    (10, .split 1340787806789879901977522152758742973024257 [
      (1, .split 88540242009401610494167 [
        (2, .round 1 [(60770344613049656874225196565535197391872233, 1)])]),
      (2, .round 108158618888829697 [(219900698580377, 1), (108158618888829697, 1)])]),
    (12, .split 4490783391790502545966925483301025475883971 []),
    (16, .split 912674556760523008721638426070617257480445566886461176721452026363041282663162968120416667203119994455437316575821 []),
    (18, .round 1 [(562313756666209162383347, 1)])]

private theorem checked7_62 : replayAbundance bank 7 2413 (10^300) 8 state7_62 tree7_62 = true := by
  decide +kernel

theorem reject7_62 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_62 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree7_62 checked7_62

@[expose] noncomputable def state7_63 : State := ⟨59038356335809084129, 68892554545586270917, 0⟩

private noncomputable def tree7_63 : AbundanceTree :=
  .split 11018941331 [
    (4, .split 1898020914628186894923984701 [
      (1, .abundant [(3, 2), (5, 2), (7, 6)]),
      (2, .split 212085782995955069974776546543157 [
        (1, .split 2924819713760751607121 [
          (2, .round 1 [(32608951138745046012109614999829, 1)])]),
        (2, .abundant [(3, 2), (5, 1), (7, 6)])]),
      (4, .round 1553418542761 [(4261, 1), (1553418542761, 1)])]),
    (6, .split 149181343123962969049064858742150382521746561 [
      (1, .abundant [(3, 2), (7, 6), (11, 2), (29, 2), (41, 2), (101, 2), (113, 2)]),
      (2, .split 1767059981 [
        (1, .abundant [(3, 4), (7, 6), (11, 2), (13, 2)])])]),
    (10, .round 1 [(20380157803085930484094212802107369098944232351326127794708543228480749907051, 1)]),
    (12, .round 1 [(720307623544626344225425894300241649500156280875883689166677713076874300844016848026010980378825925085519301427, 1)])]

private theorem checked7_63 : replayAbundance bank 7 2413 (10^300) 7 state7_63 tree7_63 = true := by
  decide +kernel

theorem reject7_63 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_63 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree7_63 checked7_63

@[expose] noncomputable def state7_64 : State := ⟨435672610579708106415558998807139457, 508391510914884781079706494494143998, 329422297⟩

private noncomputable def tree7_64 : AbundanceTree :=
  .split 69655517 [
    (2, .split 1942157131 [
      (4, .split 15866360800614491081 [
        (2, .split 1699421291 [
          (2, .split 105533191 [
            (2, .abundant [(3, 2), (5, 2), (7, 6)]),
            (4, .round 1 [(15637651, 1), (132274505201, 1)])]),
          (4, .round 1 [(1668146604311876914479540747971821781, 1)])]),
        (4, .round 1 [(70001, 1), (105533191, 1), (1699421291, 1)])]),
      (6, .split 70001 [
        (2, .split 376939231 [
          (2, .split 13240442106403 [
            (2, .round 1 [(113, 1), (4663, 1), (6199, 1), (35323, 1), (4088839, 1), (33319243, 1), (428932133323, 1)])]),
          (4, .round 1 [(4663, 1), (6199, 1), (35323, 1), (833101, 1), (7738781, 1), (56931478172288358271, 1)]),
          (6, .round 1 [(6199, 1), (35323, 1)])]),
        (4, .split 149467631 [
          (2, .split 70065607 [
            (2, .abundant [(3, 2), (5, 2), (7, 6)]),
            (4, .round 1 [(3375702307841, 1)])]),
          (4, .round 1 [(10455371551, 1), (2917511762964611, 1)])]),
        (6, .split 5141996917 [
          (2, .round 1 [(35323, 1), (50359, 1), (263621, 1), (8490763, 1), (128691691, 1), (420149893, 1)])]),
        (10, .split 96581 [
          (2, .round 1 [(6883, 1), (35323, 1), (193603, 1)])]),
        (12, .round 1 [(6199, 1), (35323, 1)])]),
      (10, .split 70001 [
        (2, .split 376939231 [
          (2, .abundant [(3, 2), (7, 6), (13, 2), (23, 2), (29, 2), (31, 2)])]),
        (4, .round 1 [(149467631, 1)])]),
      (12, .round 1 [(70001, 1)])]),
    (4, .split 123250508297577266744997386051 [
      (2, .split 70001 [
        (2, .split 376939231 [
          (2, .split 13240442106403 [
            (2, .round 1 [(4088839, 1), (33319243, 1), (428932133323, 1)])]),
          (4, .round 1 [(7738781, 1), (56931478172288358271, 1)])]),
        (4, .split 149467631 [
          (2, .round 1 [(61, 1), (181, 1), (191, 1), (571, 1), (1669, 1), (4663, 1), (35323, 1), (2910031, 1), (8617627, 1), (70065607, 1)]),
          (4, .round 1 [(2917511762964611, 1)])]),
        (6, .split 5141996917 [
          (2, .round 1 [(8490763, 1), (128691691, 1), (420149893, 1)])]),
        (10, .round 1 [(35323, 1), (96581, 1)])])]),
    (6, .split 70001 [
      (2, .split 376939231 [
        (2, .split 13240442106403 [
          (2, .split 428932133323 [
            (2, .abundant [(3, 4), (7, 6), (13, 2), (29, 2), (61, 2), (73, 2)])]),
          (4, .split 35323 [
            (2, .round 1 [(4663, 1), (11471, 1), (5697487, 1)])])]),
        (4, .split 56931478172288358271 [
          (2, .abundant [(3, 2), (5, 2), (7, 6)])]),
        (6, .split 35323 [
          (2, .split 5697487 [
            (2, .round 1 [(4663, 1), (832342661863, 1)])]),
          (4, .round 1 [(4663, 1), (367091516400121, 1)])])]),
      (4, .split 149467631 [
        (2, .split 70065607 [
          (2, .abundant [(3, 2), (5, 2), (7, 6)]),
          (4, .round 1 [(6101, 1), (27481, 1), (35323, 1), (1818871, 1), (2910031, 1), (8617627, 1), (3375702307841, 1)]),
          (6, .round 1 [(2910031, 1), (8617627, 1)])]),
        (4, .split 2917511762964611 [
          (2, .round 1 [(10455371551, 1), (5651119912551271, 1)])]),
        (6, .split 2910031 [
          (2, .abundant [(3, 2), (5, 2), (7, 6)])])]),
      (6, .split 5141996917 [
        (2, .split 420149893 [
          (2, .split 1205235307 [
            (2, .round 1 [(996367, 1), (1845751, 1), (8490763, 1), (128691691, 1)])]),
          (4, .round 1 [(8490763, 1), (128691691, 1)])]),
        (4, .split 8490763 [
          (2, .round 1 [(50359, 1), (263621, 1), (8007671311, 1)])])]),
      (10, .split 96581 [
        (2, .split 193603 [
          (2, .split 35323 [
            (2, .round 1 [(223, 1), (331, 1), (4663, 1), (6883, 1), (24181, 1), (5697487, 1)]),
            (4, .round 1 [(367091516400121, 1)])]),
          (4, .round 1 [(52230452374901, 1)])]),
        (4, .round 1 [(23, 1), (29, 1), (31, 1), (4663, 1), (35323, 1), (47431, 1), (11835246523601, 1)]),
        (6, .round 1 [(811623631030152257565326082187, 1)])]),
      (12, .split 35323 [
        (2, .split 5697487 [
          (2, .round 1 [(832342661863, 1)])]),
        (4, .round 1 [(367091516400121, 1)])]),
      (16, .round 1 [(4663, 1), (35323, 1)])]),
    (10, .split 70001 [
      (2, .split 376939231 [
        (2, .split 13240442106403 [
          (2, .round 1 [(33319243, 1), (428932133323, 1)])]),
        (4, .round 1 [(56931478172288358271, 1)])]),
      (4, .split 149467631 [
        (2, .round 1 [(37, 1), (61, 1), (181, 1), (4663, 1), (35323, 1), (2910031, 1), (8617627, 1), (70065607, 1)]),
        (4, .round 1 [(2917511762964611, 1)])]),
      (6, .split 5141996917 [
        (2, .round 1 [(128691691, 1), (420149893, 1)])]),
      (10, .round 1 [(96581, 1)])]),
    (12, .split 70001 [
      (2, .split 376939231 [
        (2, .round 1 [(521, 1), (4663, 1), (35323, 1), (13240442106403, 1)])]),
      (4, .round 1 [(181, 1), (521, 1), (4663, 1), (35323, 1), (2910031, 1), (149467631, 1)]),
      (6, .round 1 [(5141996917, 1)])])]

private theorem checked7_64 : replayAbundance bank 7 2413 (10^300) 8 state7_64 tree7_64 = true := by
  decide +kernel

theorem reject7_64 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_64 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree7_64 checked7_64

@[expose] noncomputable def state7_65 : State := ⟨143520272117153946004933881926068139924272729, 167475499300881917616901077826020498763710057, 0⟩

private noncomputable def tree7_65 : AbundanceTree :=
  .split 69655517 [
    (1, .split 2311333 [
      (2, .split 1780754182741 [
        (2, .split 3109622749 [
          (2, .split 460464459247997131 [
            (2, .abundant [(3, 8), (7, 6), (13, 2), (29, 2), (59, 2), (109, 2)]),
            (4, .abundant [(3, 8), (5, 2), (7, 6)])]),
          (4, .abundant [(3, 6), (7, 6), (13, 2), (29, 2), (31, 2)]),
          (6, .round 1 [(70001, 1), (1351093, 1), (35941459, 1), (535302210552974396501222601541769628629081, 1)])]),
        (4, .abundant [(3, 6), (5, 2), (7, 6)]),
        (6, .round 1 [(6561487608532081, 1), (2916507202643844355422876997343172799810986988337, 1)])]),
      (4, .abundant [(3, 4), (7, 6), (13, 2), (29, 2), (31, 2)]),
      (6, .split 46944033373404832267 [
        (2, .split 114251974235155791469 [
          (2, .round 1 [(3247842098220887329, 1), (6429479764984362451, 1)])]),
        (4, .abundant [(3, 4), (7, 6), (11, 2), (13, 2)])]),
      (10, .split 15070815500303596594228625800087723787 []),
      (12, .round 1 [(70001, 1), (739103, 1), (4581704497581995647813, 1), (2549561058117779520813143837022388797486293, 1)]),
      (16, .abundant [(3, 4), (7, 6), (13, 2), (29, 2), (59, 2), (103, 2)])]),
    (2, .split 1942157131 [
      (4, .abundant [(3, 2), (5, 1), (7, 6)]),
      (6, .split 2311333 [
        (1, .abundant [(3, 2), (7, 6), (13, 2), (29, 2), (31, 2), (41, 2)]),
        (2, .split 1780754182741 [
          (1, .split 890377091371 [
            (2, .abundant [(3, 4), (7, 6), (13, 2), (29, 2), (31, 2)])]),
          (2, .abundant [(3, 4), (7, 6), (13, 2), (29, 2), (31, 2)])]),
        (4, .split 107896304231 [
          (2, .round 1 [(38272603, 1), (84438671, 1), (378361939, 1)])]),
        (6, .round 3247842098220887329 [(2131, 1), (6199, 1), (70001, 1), (3247842098220887329, 1), (46944033373404832267, 1)])]),
      (10, .abundant [(3, 2), (7, 6), (13, 2), (23, 2), (29, 1), (31, 2)])]),
    (4, .split 123250508297577266744997386051 [
      (2, .split 2311333 [
        (1, .split 70001 [
          (2, .split 376939231 [
            (2, .abundant [(3, 2), (7, 6), (13, 2), (29, 2), (41, 2), (71, 2), (73, 2), (191, 2)]),
            (4, .abundant [(3, 2), (5, 2), (7, 6)])]),
          (4, .abundant [(3, 2), (5, 2), (7, 6)]),
          (6, .round 1 [(50359, 1), (263621, 1), (8490763, 1), (5141996917, 1)])]),
        (2, .split 1780754182741 [
          (1, .split 890377091371 [
            (2, .round 1 [(70001, 1), (3411739623785797, 1)])]),
          (2, .round 3109622749 [(1423, 1), (1669, 1), (2131, 1), (70001, 1), (1351093, 1), (35941459, 1), (3109622749, 1)])]),
        (4, .round 70001 [(397, 1), (571, 1), (1423, 1), (1669, 1), (2131, 1), (70001, 1), (101051, 1), (84438671, 1), (107896304231, 1)]),
        (6, .round 1 [(46944033373404832267, 1)])])]),
    (6, .split 2311333 [
      (1, .split 70001 [
        (2, .split 376939231 [
          (2, .split 13240442106403 [
            (2, .abundant [(3, 4), (7, 6), (13, 2), (29, 2), (41, 2)]),
            (4, .round 1 [(11471, 1)])]),
          (4, .abundant [(3, 2), (5, 2), (7, 6)]),
          (6, .split 2131 [
            (2, .split 4933 []),
            (4, .abundant [(3, 2), (5, 2), (7, 6)])])]),
        (4, .abundant [(3, 2), (5, 2), (7, 6)]),
        (6, .split 5141996917 [
          (2, .split 420149893 [
            (2, .abundant [(3, 4), (7, 6), (13, 2), (29, 2), (41, 2)])]),
          (4, .round 1 [(50359, 1), (263621, 1), (8490763, 1)])]),
        (10, .abundant [(3, 2), (7, 6), (13, 2), (23, 2), (29, 2), (41, 2)]),
        (12, .split 2131 [
          (2, .round 1 [(41, 1), (71, 1), (307, 1), (1423, 1), (4933, 1)])])]),
      (2, .split 1780754182741 [
        (1, .split 890377091371 [
          (2, .split 3411739623785797 [
            (2, .round 1 [(3879989086836685020808720903669, 1)])]),
          (4, .abundant [(3, 2), (5, 2), (7, 6)])]),
        (2, .split 3109622749 [
          (1, .abundant [(3, 4), (5, 4), (7, 6)]),
          (2, .split 460464459247997131 [
            (2, .round 1 [(5660874240871841199362777599, 1)])]),
          (4, .abundant [(3, 4), (7, 6), (13, 1), (29, 1), (31, 2)])]),
        (4, .abundant [(3, 2), (5, 1), (7, 6)])]),
      (4, .split 107896304231 [
        (2, .split 378361939 [
          (2, .round 1 [(101051, 1), (114847, 1), (796819, 1), (30885607, 1), (38272603, 1), (84438671, 1)]),
          (4, .round 1 [(84438671, 1)])]),
        (4, .abundant [(3, 2), (5, 1), (7, 6)])]),
      (6, .split 46944033373404832267 [
        (2, .round 1 [(6429479764984362451, 1)])]),
      (10, .round 1 [(15070815500303596594228625800087723787, 1)])]),
    (10, .split 2311333 [
      (1, .split 70001 [
        (2, .split 376939231 [
          (2, .split 13240442106403 [])]),
        (4, .abundant [(3, 2), (5, 2), (7, 6)]),
        (6, .round 1 [(263621, 1), (8490763, 1), (5141996917, 1)])]),
      (2, .split 1780754182741 [
        (1, .split 890377091371 [
          (2, .round 1 [(3411739623785797, 1)])]),
        (2, .round 3109622749 [(2131, 1), (70001, 1), (1351093, 1), (35941459, 1), (3109622749, 1)])]),
      (4, .round 70001 [(397, 1), (1423, 1), (2131, 1), (70001, 1), (101051, 1), (84438671, 1), (107896304231, 1)]),
      (6, .round 1 [(46944033373404832267, 1)])]),
    (12, .split 2311333 [
      (1, .split 70001 [
        (2, .split 376939231 []),
        (4, .abundant [(3, 2), (5, 2), (7, 6)])]),
      (2, .split 1780754182741 [
        (1, .round 1 [(70001, 1), (890377091371, 1)])])])]

private theorem checked7_65 : replayAbundance bank 7 2413 (10^300) 8 state7_65 tree7_65 = true := by
  decide +kernel

theorem reject7_65 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_65 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree7_65 checked7_65

@[expose] noncomputable def state7_66 : State := ⟨15574683551558700937547214006599398163510224972185989396124361, 18174282042339896509603529804030221190165588372851537232637911, 0⟩

private noncomputable def tree7_66 : AbundanceTree :=
  .split 1074666521961382602401 [
    (1, .split 77454079403707 [
      (2, .split 64506821680385229664137049 [
        (2, .round 1 [(69655517, 1), (187463623161013556106717947842041603097792112383, 1)])]),
      (4, .round 1 [(26711, 1), (70001, 1), (28015921, 1), (69655517, 1), (955359303471547448711, 1), (23120140348403327013509376221, 1)]),
      (6, .round 1 [(70001, 1), (28015921, 1), (69655517, 1)])]),
    (2, .split 55837223596838794957331299 [
      (2, .round 239183225509 [(28015921, 1), (69655517, 1), (219577381, 1), (557828389, 1), (239183225509, 1), (11036894813486155616588863, 1)])]),
    (4, .round 1 [(1467046983899039726186275590455021547723182191, 1)])]

private theorem checked7_66 : replayAbundance bank 7 2413 (10^300) 6 state7_66 tree7_66 = true := by
  decide +kernel

theorem reject7_66 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_66 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree7_66 checked7_66

@[expose] noncomputable def state7_67 : State := ⟨1690149859339629908476485422808810698848735244311275902968843677362457166907449, 1972255817318701211807871579474829397548962305200658246343752927697101736183397, 0⟩

private noncomputable def tree7_67 : AbundanceTree :=
  .split 6822398817447814798303 [
    (2, .split 1790825470352353574442601147 []),
    (4, .round 1 [(1675411861177363, 1)])]

private theorem checked7_67 : replayAbundance bank 7 2413 (10^300) 4 state7_67 tree7_67 = true := by
  decide +kernel

theorem reject7_67 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_67 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_67 checked7_67

@[expose] noncomputable def state7_68 : State := ⟨19903854033205537154127822352191916208351949322800129385317948098293485989200884716635620816876121701064811871769, 23226042168467651620778652237998199190970964176154877575130268874942556231473917229010675164161753981079010867937, 0⟩

private noncomputable def tree7_68 : AbundanceTree :=
  .split 654337900948810257477854320201534837021324442482839576784396053052379784395359753669 [
    (1, .round 1 [(69655517, 1)])]

private theorem checked7_68 : replayAbundance bank 7 2413 (10^300) 4 state7_68 tree7_68 = true := by
  decide +kernel

theorem reject7_68 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_68 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_68 checked7_68

@[expose] noncomputable def state7_69 : State := ⟨2159947326260259852290922269283740646497024412917947162545201986142150077359416049947012047045754004815977239612979370546178563721, 2520468025825363131307797966525559344625614184359333526890955690338282162320567537422377433185206874127721759466593575769045914831, 0⟩

private noncomputable def tree7_69 : AbundanceTree :=
  .round 3607069778576494174120970869037 [(669077968114506874691, 1), (23834338339946103562153003, 1), (28392361864610666302626481, 1), (3607069778576494174120970869037, 1)]

private theorem checked7_69 : replayAbundance bank 7 2413 (10^300) 3 state7_69 tree7_69 = true := by
  decide +kernel

theorem reject7_69 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_69 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_69 checked7_69

@[expose] noncomputable def state7_70 : State := ⟨1322535282363440342399042281, 1543282024323941729893786651, 0⟩

private theorem checked7_70 : checkChildren bank 7 2413 (10^300) state7_70 329422297 [state7_64, state7_65, state7_66, state7_67, state7_68, state7_69] = true := by
  decide +kernel

theorem reject7_70 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_70 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state7_64, state7_65, state7_66, state7_67, state7_68, state7_69] ?_ checked7_70
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject7_64 ho hN hs hav hx hvalid
  · exact reject7_65 ho hN hs hav hx hvalid
  · exact reject7_66 ho hN hs hav hx hvalid
  · exact reject7_67 ho hN hs hav hx hvalid
  · exact reject7_68 ho hN hs hav hx hvalid
  · exact reject7_69 ho hN hs hav hx hvalid

@[expose] noncomputable def state7_71 : State := ⟨663671678185557669152069802032168492969401, 774446311304691534256110914032897017839191, 0⟩

private noncomputable def tree7_71 : AbundanceTree :=
  .split 149756169433403613317161 [
    (2, .split 242980751471069070767002375553611 [
      (2, .round 1 [(3715817544877836253819, 1), (270506434242341701706091354122482600111, 1)])]),
    (4, .split 15393182494510496472439733415528529966085358071654101 [
      (1, .round 1 [(491751810355961017531, 1)])])]

private theorem checked7_71 : replayAbundance bank 7 2413 (10^300) 5 state7_71 tree7_71 = true := by
  decide +kernel

theorem reject7_71 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_71 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree7_71 checked7_71

@[expose] noncomputable def state7_72 : State := ⟨14867101064149672972841900583495393707702019957889, 17348595634520362114724540601305081603854522891837, 0⟩

private noncomputable def tree7_72 : AbundanceTree :=
  .split 5254721205635580646501 [
    (1, .split 34910890042656523169 [
      (2, .split 28343494036522194840123504160699775017 [
        (2, .round 1 [(10688807, 1), (40935743, 1)])]),
      (4, .split 40935743 [
        (2, .round 1 [(6004651, 1), (10688807, 1), (239390727985399, 1)])])]),
    (4, .round 1 [(651435268818511578018931, 1), (476808038041463635075919713613992478364491, 1)])]

private theorem checked7_72 : replayAbundance bank 7 2413 (10^300) 6 state7_72 tree7_72 = true := by
  decide +kernel

theorem reject7_72 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_72 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree7_72 checked7_72

@[expose] noncomputable def state7_73 : State := ⟨7460575188108312202055278120085271471365932992772064750112489169, 8705833207223818636203203494321082854779460005644999129474787097, 0⟩

private noncomputable def tree7_73 : AbundanceTree :=
  .split 16952580673293897376649 [
    (1, .abundant [(3, 2), (5, 2), (7, 6)]),
    (2, .split 206942259762718171661475733 [
      (1, .split 7816625987881598827 [
        (2, .round 1 [(7563524537, 1), (8209197757, 1), (52407378251, 1)])]),
      (2, .round 8209197757 [(63284371, 1), (7563524537, 1), (8209197757, 1), (7816625987881598827, 1)])]),
    (4, .round 1 [(63284371, 1), (7816625987881598827, 1)])]

private theorem checked7_73 : replayAbundance bank 7 2413 (10^300) 6 state7_73 tree7_73 = true := by
  decide +kernel

theorem reject7_73 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_73 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree7_73 checked7_73

@[expose] noncomputable def state7_74 : State := ⟨167126500895043664940466679143406870873523489725721933593982652384138841, 195021885660817648953173824202096435822859714850395256904113124623142671, 0⟩

private noncomputable def tree7_74 : AbundanceTree :=
  .split 20035625396161565456417195309021 [
    (1, .split 3339270899360260909402865884837 [
      (2, .round 1 [(397, 1), (1787, 1), (4513, 1), (58217, 1), (681665903475579942644606417, 1)])]),
    (2, .round 681665903475579942644606417 [(751, 1), (1787, 1), (58217, 1), (41985407811274723, 1), (681665903475579942644606417, 1), (13415327550378577131359762679792640404919, 1)])]

private theorem checked7_74 : replayAbundance bank 7 2413 (10^300) 5 state7_74 tree7_74 = true := by
  decide +kernel

theorem reject7_74 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_74 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree7_74 checked7_74

@[expose] noncomputable def state7_75 : State := ⟨83867044454253786479690456259958798871785381241091748782331606922296912774585746437161, 97865443641040454392729527657431196503868312512693429127130872258917261638169505545611, 0⟩

private noncomputable def tree7_75 : AbundanceTree :=
  .split 1427139255384884779689202115413130313129855577426008122495764105127925516389 [
    (1, .abundant [(3, 2), (5, 2), (7, 6)])]

private theorem checked7_75 : replayAbundance bank 7 2413 (10^300) 4 state7_75 tree7_75 = true := by
  decide +kernel

theorem reject7_75 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_75 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_75 checked7_75

@[expose] noncomputable def state7_76 : State := ⟨942780009335342713953666423643216533598042207166574872207960314853688894641653536591552676526598699839644609, 1100141115856716117175926718051783838734773829026580488964938571221653824005691789575783401469348690597740077, 0⟩

private noncomputable def tree7_76 : AbundanceTree :=
  .split 52305369616955074256575903512705464657373733771 []

private theorem checked7_76 : replayAbundance bank 7 2413 (10^300) 3 state7_76 tree7_76 = true := by
  decide +kernel

theorem reject7_76 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_76 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_76 checked7_76

@[expose] noncomputable def state7_77 : State := ⟨21119487452543710049320414165628126458707953316936314852468587113568477644958232311059446465595853662132132543501001, 24644579077088780331815798253899526737027062893661018215064899801183350369506639423214311377717904659851558861533891, 0⟩

private noncomputable def tree7_77 : AbundanceTree :=
  .split 3310833202399836978699693757735028040744145614488023758467761 [
    (1, .round 1 [(17123629703337280465370521249, 1)])]

private theorem checked7_77 : replayAbundance bank 7 2413 (10^300) 4 state7_77 tree7_77 = true := by
  decide +kernel

theorem reject7_77 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_77 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_77 checked7_77

@[expose] noncomputable def state7_78 : State := ⟨237411854766475116137399986857377099978919972878190476339934669406603527983755879659640648421399692288065040651909372753665778496504969569, 277038694323332489806385775086405384953009258928803940813431736222391487389609113661425313247709473622913455194578885666238504778167071397, 0⟩

private noncomputable def tree7_78 : AbundanceTree :=
  .round 1 [(20080265532927138143001626122389410757333134726368715392308318041362200648332766167528165891, 1)]

private theorem checked7_78 : replayAbundance bank 7 2413 (10^300) 3 state7_78 tree7_78 = true := by
  decide +kernel

theorem reject7_78 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_78 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_78 checked7_78

@[expose] noncomputable def state7_79 : State := ⟨117649, 137257, 0⟩

private theorem checked7_79 : checkChildren bank 7 2413 (10^300) state7_79 4733 [state7_61, state7_62, state7_63, state7_70, state7_71, state7_72, state7_73, state7_74, state7_75, state7_76, state7_77, state7_78] = true := by
  decide +kernel

theorem reject7_79 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_79 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state7_61, state7_62, state7_63, state7_70, state7_71, state7_72, state7_73, state7_74, state7_75, state7_76, state7_77, state7_78] ?_ checked7_79
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject7_61 ho hN hs hav hx hvalid
  · exact reject7_62 ho hN hs hav hx hvalid
  · exact reject7_63 ho hN hs hav hx hvalid
  · exact reject7_70 ho hN hs hav hx hvalid
  · exact reject7_71 ho hN hs hav hx hvalid
  · exact reject7_72 ho hN hs hav hx hvalid
  · exact reject7_73 ho hN hs hav hx hvalid
  · exact reject7_74 ho hN hs hav hx hvalid
  · exact reject7_75 ho hN hs hav hx hvalid
  · exact reject7_76 ho hN hs hav hx hvalid
  · exact reject7_77 ho hN hs hav hx hvalid
  · exact reject7_78 ho hN hs hav hx hvalid

@[expose] noncomputable def state7_80 : State := ⟨29195295324820929495368558768694948754163300593, 34063161323292781839301106162115423713173903986, 310897033⟩

private noncomputable def tree7_80 : AbundanceTree :=
  .split 6781 [
    (2, .split 414313 [
      (2, .abundant [(3, 4), (7, 10), (13, 2), (37, 2), (43, 2), (61, 2)]),
      (4, .split 21510233728457701 [
        (2, .abundant [(3, 4), (7, 10), (11, 2), (37, 2), (43, 2)]),
        (4, .abundant [(3, 2), (5, 2), (7, 10)]),
        (6, .round 1 [(11321, 1)])]),
      (6, .split 4563518292641213580000474037 [
        (2, .split 5023 [
          (4, .split 50368353121 [
            (2, .round 1 [(12641, 1), (1621781727656533, 1)])]),
          (6, .round 1 [(619, 1), (659, 1), (953, 1), (1123, 1), (1163, 1), (1583, 1), (3517, 1), (3447767, 1), (103870649, 1)]),
          (10, .round 1 [(195077772785631536672465584871, 1)])])]),
      (10, .split 5023 [
        (4, .split 50368353121 [
          (2, .split 1621781727656533 []),
          (4, .abundant [(3, 2), (5, 2), (7, 10)])]),
        (6, .split 103870649 [
          (2, .split 10789111827551851 []),
          (4, .round 1 [(36978006857728559191, 1)])]),
        (10, .round 1 [(263, 1), (277, 1), (619, 1), (1123, 1), (25609, 1), (195077772785631536672465584871, 1)]),
        (12, .round 1 [(992609563458650339114558026010082857, 1)])]),
      (12, .split 5023 [
        (4, .split 50368353121 [
          (2, .round 1 [(163, 1), (263, 1), (277, 1), (457, 1), (619, 1), (1123, 1), (12641, 1), (1621781727656533, 1)])]),
        (6, .split 103870649 [
          (2, .round 1 [(1123, 1), (1583, 1), (3447767, 1), (10789111827551851, 1)])]),
        (10, .round 1 [(195077772785631536672465584871, 1)]),
        (12, .round 1 [(992609563458650339114558026010082857, 1)])]),
      (16, .split 5023 [
        (4, .round 1 [(619, 1), (1123, 1), (12641, 1), (50368353121, 1)]),
        (6, .round 1 [(103870649, 1)])]),
      (18, .split 5023 [])]),
    (4, .abundant [(3, 2), (5, 2), (7, 10)]),
    (6, .split 3352961130596029024703 [
      (2, .split 20749 [
        (2, .split 5023 [
          (4, .split 50368353121 [
            (2, .split 1621781727656533 []),
            (4, .abundant [(3, 2), (5, 2), (7, 10)])]),
          (6, .split 103870649 [
            (2, .round 1 [(103, 1), (263, 1), (277, 1), (619, 1), (659, 1), (823, 1), (1123, 1), (1583, 1), (1693, 1), (3447767, 1), (10789111827551851, 1)]),
            (4, .abundant [(3, 2), (7, 10), (11, 2), (29, 2), (31, 2), (43, 2)])]),
          (10, .abundant [(3, 2), (7, 10), (23, 2), (29, 2), (31, 2), (43, 2), (61, 2), (89, 2), (103, 2)]),
          (12, .round 1 [(992609563458650339114558026010082857, 1)])]),
        (4, .abundant [(3, 2), (7, 10), (11, 2), (29, 2), (31, 2), (43, 2)]),
        (6, .split 9802259616049620107711 [
          (2, .round 1 [(96084293580437245811926475412657300861767233, 1)])]),
        (10, .round 1 [(5023, 1), (27959987069285335876609070209948992760319, 1)]),
        (12, .abundant [(3, 2), (7, 10), (13, 2), (29, 2), (31, 2), (43, 2), (61, 2)])]),
      (4, .split 42571 [
        (4, .abundant [(3, 2), (5, 2), (7, 10)])])]),
    (10, .split 52595417797518863702755409 [
      (2, .split 58341660037 [
        (2, .split 1134583098643741500469 []),
        (4, .round 1 [(5023, 1), (122131, 1)])])]),
    (12, .split 1314910344602155601 [
      (2, .split 259339259638042446931 [
        (2, .round 1 [(40606039, 1), (164184967, 1), (2406225921513077, 1)])]),
      (4, .abundant [(3, 2), (5, 2), (7, 10)])]),
    (16, .split 34276926782411 [
      (2, .split 1105275361850234041642291 [
        (2, .round 1 [(5023, 1)])]),
      (4, .abundant [(3, 2), (5, 2), (7, 10)])]),
    (18, .split 70775827084119857713229129468079547660774063688737072592057 []),
    (22, .round 1 [(2360658177374918510556565420453413187801345568825570475472424053628193350219, 1)]),
    (28, .round 1 [(5838857115082075330673028204096729494664991891581680491526300943764448483089, 1)]),
    (30, .round 1 [(148522457061512004102859422030755516521, 1)])]

private theorem checked7_80 : replayAbundance bank 7 2413 (10^300) 8 state7_80 tree7_80 = true := by
  decide +kernel

theorem reject7_80 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_80 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree7_80 checked7_80

@[expose] noncomputable def state7_81 : State := ⟨15807686411944605251904872499124520722023202705828992073, 18443374742654285150367355757598363525581373401645088566, 310897033⟩

private noncomputable def tree7_81 : AbundanceTree :=
  .split 39652448401 [
    (2, .split 185247563104753 [
      (2, .split 11940971871487 [
        (2, .abundant [(3, 4), (7, 10), (11, 2), (13, 2)]),
        (4, .split 5878200649 [
          (2, .abundant [(3, 4), (7, 10), (11, 2), (13, 2)])])]),
      (4, .split 2829217 [
        (2, .split 2668157220769 [
          (2, .abundant [(3, 4), (7, 10), (11, 2), (41, 2), (61, 2), (191, 2)])]),
        (4, .abundant [(3, 2), (7, 10), (11, 2), (31, 2), (41, 2), (61, 2), (191, 2)]),
        (6, .round 1 [(1123, 1), (5023, 1), (672151, 1)])]),
      (6, .round 1 [(277, 1), (1123, 1), (5023, 1), (12853, 1), (672151, 1), (2829217, 1)])]),
    (4, .split 38416308119563899871404070700771 []),
    (6, .split 672151 [
      (4, .split 23447646989174174161 []),
      (6, .round 1 [(92215036119737819985456413047777657, 1)])]),
    (10, .round 1 [(1123, 1), (5023, 1), (672151, 1)])]

private theorem checked7_81 : replayAbundance bank 7 2413 (10^300) 7 state7_81 tree7_81 = true := by
  decide +kernel

theorem reject7_81 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_81 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree7_81 checked7_81

@[expose] noncomputable def state7_82 : State := ⟨8559014283576553447225381532819947430808555662636461246223696353, 9986098138969474175724206474054917073327456331813179945845401946, 310897033⟩

private noncomputable def tree7_82 : AbundanceTree :=
  .split 1760751039974165471 [
    (4, .round 1 [(5573, 1), (9227157027250280470259819642125230360313655626433712049984353343111, 1)])]

private theorem checked7_82 : replayAbundance bank 7 2413 (10^300) 4 state7_82 tree7_82 = true := by
  decide +kernel

theorem reject7_82 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_82 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_82 checked7_82

@[expose] noncomputable def state7_83 : State := ⟨2509196248622526496303644549306536903710984082076104070323273890274933572208655313, 2927566090964390969544948140500367330423175287877343409589733609678639832506567106, 310897033⟩

private noncomputable def tree7_83 : AbundanceTree :=
  .split 5023 [
    (4, .split 50368353121 [
      (2, .split 1621781727656533 []),
      (4, .split 168287671584983640775584597264631 []),
      (6, .split 12641 [
        (2, .round 1 [(159807523, 1)])])]),
    (6, .split 103870649 [
      (2, .split 10789111827551851 []),
      (4, .split 36978006857728559191 [])]),
    (10, .split 195077772785631536672465584871 [
      (2, .round 1 [(25609, 1)])]),
    (12, .split 992609563458650339114558026010082857 []),
    (16, .round 1 [(39447306533, 1), (72906989466765413790451297855712614673, 1)]),
    (18, .round 1 [(39794905409392396139272403153242163, 1)]),
    (22, .round 1 [(3856318991340212017588480825802322293044120720988141071743513043952813, 1)])]

private theorem checked7_83 : replayAbundance bank 7 2413 (10^300) 6 state7_83 tree7_83 = true := by
  decide +kernel

theorem reject7_83 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_83 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree7_83 checked7_83

@[expose] noncomputable def state7_84 : State := ⟨1358595177851518234049688292259509480026519726969031873933824741495676072189107151927165993, 1585120006539664471041373996607640610220912849687778889380578808766185210850585596407994886, 310897033⟩

private noncomputable def tree7_84 : AbundanceTree :=
  .split 5023 [
    (4, .split 50368353121 [
      (2, .split 1621781727656533 []),
      (4, .round 1 [(12641, 1), (695370101, 1), (168287671584983640775584597264631, 1)]),
      (6, .round 1 [(12641, 1)])]),
    (6, .split 103870649 [
      (2, .split 10789111827551851 []),
      (4, .split 36978006857728559191 [])]),
    (10, .split 195077772785631536672465584871 []),
    (12, .split 992609563458650339114558026010082857 []),
    (16, .round 1 [(72906989466765413790451297855712614673, 1)]),
    (18, .round 1 [(39794905409392396139272403153242163, 1)])]

private theorem checked7_84 : replayAbundance bank 7 2413 (10^300) 5 state7_84 tree7_84 = true := by
  decide +kernel

theorem reject7_84 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_84 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree7_84 checked7_84

@[expose] noncomputable def state7_85 : State := ⟨398291416594899431680960823040108242168951542377808727272116233551364679558497338286947184983365733311289753, 464700378133241649232122091264633042223931248837690854334976493326151627879196558477789576000434960896380846, 310897033⟩

private noncomputable def tree7_85 : AbundanceTree :=
  .split 5023 [
    (4, .split 50368353121 [
      (2, .split 1621781727656533 []),
      (4, .round 1 [(168287671584983640775584597264631, 1)])]),
    (6, .split 103870649 [
      (2, .split 10789111827551851 []),
      (4, .round 1 [(36978006857728559191, 1)])]),
    (10, .round 1 [(1123, 1), (2789, 1), (25609, 1), (195077772785631536672465584871, 1)]),
    (12, .round 1 [(992609563458650339114558026010082857, 1)])]

private theorem checked7_85 : replayAbundance bank 7 2413 (10^300) 5 state7_85 tree7_85 = true := by
  decide +kernel

theorem reject7_85 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_85 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree7_85 checked7_85

@[expose] noncomputable def state7_86 : State := ⟨215653438132843308444624350618631564768485559805801822535528791425412512330879470443653527108437221833494316978438833, 251610328695567664110370950622945448712506921797353192722654097331985585050881010102407908095459738104778035398795026, 310897033⟩

private noncomputable def tree7_86 : AbundanceTree :=
  .split 5023 [
    (4, .split 50368353121 [
      (2, .split 1621781727656533 [])]),
    (6, .split 103870649 [
      (2, .round 1 [(1123, 1), (1583, 1), (3447767, 1), (10789111827551851, 1)])]),
    (10, .round 1 [(195077772785631536672465584871, 1)]),
    (12, .round 1 [(992609563458650339114558026010082857, 1)])]

private theorem checked7_86 : replayAbundance bank 7 2413 (10^300) 5 state7_86 tree7_86 = true := by
  decide +kernel

theorem reject7_86 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_86 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree7_86 checked7_86

@[expose] noncomputable def state7_87 : State := ⟨63221859438159995109189396195266555555325137049540500106129843280604317046855400836844182319217728144706109369235866572839421113151393, 73763131122358804205513830876383680447908407073125687772601997128314815118189950601487629079663752276179763160586178436599228163105786, 310897033⟩

private noncomputable def tree7_87 : AbundanceTree :=
  .split 5023 [
    (4, .split 50368353121 []),
    (6, .round 1 [(2347, 1), (3447767, 1), (103870649, 1)])]

private theorem checked7_87 : replayAbundance bank 7 2413 (10^300) 4 state7_87 tree7_87 = true := by
  decide +kernel

theorem reject7_87 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_87 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_87 checked7_87

@[expose] noncomputable def state7_88 : State := ⟨10035374462723599064138524863436539298779754735690611824958430026949323780945410709102836148009589866252064671165798210884543644343300132504171526411425703776233, 11708618647635837221892757478769379388002326764925478131861731380478054514392192031857169280876209559408647474545737660088402118920184354713892586903691170197926, 310897033⟩

private noncomputable def tree7_88 : AbundanceTree :=
  .round 1 [(4177, 1), (5023, 1)]

private theorem checked7_88 : replayAbundance bank 7 2413 (10^300) 3 state7_88 tree7_88 = true := by
  decide +kernel

theorem reject7_88 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_88 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_88 checked7_88

@[expose] noncomputable def state7_89 : State := ⟨53920937377619441596669182838399293913, 62908719848948983510584190384844360206, 310897033⟩

private theorem checked7_89 : checkChildren bank 7 2413 (10^300) state7_89 23269 [state7_80, state7_81, state7_82, state7_83, state7_84, state7_85, state7_86, state7_87, state7_88] = true := by
  decide +kernel

theorem reject7_89 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_89 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state7_80, state7_81, state7_82, state7_83, state7_84, state7_85, state7_86, state7_87, state7_88] ?_ checked7_89
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject7_80 ho hN hs hav hx hvalid
  · exact reject7_81 ho hN hs hav hx hvalid
  · exact reject7_82 ho hN hs hav hx hvalid
  · exact reject7_83 ho hN hs hav hx hvalid
  · exact reject7_84 ho hN hs hav hx hvalid
  · exact reject7_85 ho hN hs hav hx hvalid
  · exact reject7_86 ho hN hs hav hx hvalid
  · exact reject7_87 ho hN hs hav hx hvalid
  · exact reject7_88 ho hN hs hav hx hvalid

@[expose] noncomputable def state7_90 : State := ⟨384435090902488155437501093152186806686804079697, 448514447445936045199890371748424314902542245418, 310897033⟩

private noncomputable def tree7_90 : AbundanceTree :=
  .split 5144408211938741 [
    (2, .split 543296947597055507819731 [
      (4, .round 1 [(277, 1), (379, 1), (811, 1), (1123, 1), (3371, 1)])]),
    (4, .split 1123 [
      (4, .split 1983851 [
        (2, .split 1831394497 [
          (2, .abundant [(3, 2), (5, 2), (7, 10)]),
          (4, .round 1 [(378510836590119752613221, 1)])]),
        (4, .split 679078783976611 [
          (2, .abundant [(3, 2), (5, 2), (7, 10)])]),
        (6, .round 1 [(2369223120158284605160807, 1)])]),
      (6, .split 15852481 [
        (2, .abundant [(3, 2), (5, 2), (7, 10)]),
        (4, .round 1 [(5591, 1), (293147, 1), (2259069000636123729760871, 1)]),
        (6, .round 1 [(120161935554310741570451765250151, 1)])]),
      (10, .split 1091743984775080451267993 []),
      (12, .round 1 [(53, 1), (241, 1), (263, 1), (277, 1), (281, 1), (1128748349, 1), (22917277423, 1), (2937027106191751, 1)]),
      (16, .round 1 [(3330387172446132796579, 1)]),
      (18, .round 1 [(10612992450021439543353331638426864955619439336698933, 1)])]),
    (6, .split 1123 [
      (4, .split 1983851 [
        (2, .round 1 [(19571, 1), (1831394497, 1)])]),
      (6, .round 1 [(277, 1), (3823, 1), (293147, 1), (15852481, 1)])])]

private theorem checked7_90 : replayAbundance bank 7 2413 (10^300) 7 state7_90 tree7_90 = true := by
  decide +kernel

theorem reject7_90 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_90 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree7_90 checked7_90

@[expose] noncomputable def state7_91 : State := ⟨2740871103226528052447163037682949234544094166945362608393, 3197731730207729878585438137490929953017630921146579487846, 310897033⟩

private noncomputable def tree7_91 : AbundanceTree :=
  .split 43923080889124454137 [
    (2, .split 19963290423871127954420311408597 [
      (2, .split 18376499 [
        (4, .abundant [(3, 2), (7, 10), (11, 2), (13, 2)])])]),
    (4, .split 18376499 [
      (4, .round 1 [(3226441, 1), (34047782581661, 1)])])]

private theorem checked7_91 : replayAbundance bank 7 2413 (10^300) 6 state7_91 tree7_91 = true := by
  decide +kernel

theorem reject7_91 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_91 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree7_91 checked7_91

@[expose] noncomputable def state7_92 : State := ⟨139322029064359511734663607379070177456422563091837840870414997794550447503673, 162544846611564645856612125277124876264921776324760085278372176290426073389886, 310897033⟩

private noncomputable def tree7_92 : AbundanceTree :=
  .split 1123 [
    (4, .split 1983851 [
      (2, .split 1831394497 [
        (2, .split 17257690903 [
          (2, .split 166062471846877 [
            (2, .abundant [(3, 4), (7, 10), (11, 2), (23, 2)])]),
          (4, .round 1 [(23655641, 1), (821538522595690918631, 1)])]),
        (4, .split 378510836590119752613221 []),
        (6, .round 1 [(1093208355208482471225341744517042144744723375133, 1)])]),
      (4, .split 679078783976611 [
        (2, .abundant [(3, 2), (5, 2), (7, 10)])]),
      (6, .split 2369223120158284605160807 [
        (2, .round 1 [(358444762816845474395474502098503, 1)])]),
      (10, .round 1 [(29513949537333245294691327574113530231096889670837359841, 1)])]),
    (6, .split 15852481 [
      (2, .split 127584187 [
        (2, .abundant [(3, 2), (7, 10), (11, 2), (13, 2)]),
        (4, .abundant [(3, 2), (7, 10), (11, 2), (23, 2), (41, 2), (113, 2)]),
        (6, .round 1 [(4313016370613880652773372788298434532293960014237, 1)])]),
      (4, .split 2259069000636123729760871 [
        (2, .round 1 [(20190160335800936751198926476589330851, 1)])]),
      (6, .round 1 [(397, 1), (3823, 1), (48973, 1), (293147, 1), (385267, 1), (120161935554310741570451765250151, 1)])]),
    (10, .split 1091743984775080451267993 [
      (2, .round 1 [(85447, 1), (265871, 1), (273818481499, 1), (234644065482067, 1)])]),
    (12, .split 2937027106191751 [
      (2, .abundant [(3, 2), (7, 10), (11, 2), (23, 2), (53, 2), (79, 2), (199, 2)])]),
    (16, .split 3330387172446132796579 [
      (2, .abundant [(3, 2), (7, 10), (11, 2), (17, 2), (23, 2)])]),
    (18, .round 1 [(277, 1), (397, 1), (761, 1), (10612992450021439543353331638426864955619439336698933, 1)]),
    (22, .round 1 [(41292578210753, 1), (402363029321257669799797253, 1)])]

private theorem checked7_92 : replayAbundance bank 7 2413 (10^300) 8 state7_92 tree7_92 = true := by
  decide +kernel

theorem reject7_92 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_92 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree7_92 checked7_92

@[expose] noncomputable def state7_93 : State := ⟨993311309352478124384894934040498561933376999628409257287623794198146500744255673897137, 1158880871176847335093318783105690574101648986724868711998753936298637715992234178085338, 310897033⟩

private noncomputable def tree7_93 : AbundanceTree :=
  .split 1662538028940448492661741282705388761381133306649407119659 []

private theorem checked7_93 : replayAbundance bank 7 2413 (10^300) 3 state7_93 tree7_93 = true := by
  decide +kernel

theorem reject7_93 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_93 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_93 checked7_93

@[expose] noncomputable def state7_94 : State := ⟨50491300721384293174447614869078193271445107904354395475035523472870383896681895362078626221817750548290657, 58907416049650990590054527739200440199884282507162890220240044079659088678923007728474073691893203203651698, 310897033⟩

private noncomputable def tree7_94 : AbundanceTree :=
  .split 1123 [
    (4, .split 1983851 [
      (2, .split 1831394497 [
        (2, .split 17257690903 [
          (2, .round 1 [(166062471846877, 1)])]),
        (4, .round 1 [(378510836590119752613221, 1)])]),
      (4, .split 679078783976611 []),
      (6, .round 1 [(2369223120158284605160807, 1)])]),
    (6, .split 15852481 [
      (2, .split 127584187 [
        (2, .round 1 [(443, 1), (1789, 1), (3823, 1), (293147, 1), (1949359, 1), (5786761, 1)])]),
      (4, .round 1 [(2259069000636123729760871, 1)])]),
    (10, .split 1091743984775080451267993 []),
    (12, .round 1 [(443, 1), (1128748349, 1), (22917277423, 1), (2937027106191751, 1)]),
    (16, .round 1 [(3330387172446132796579, 1)])]

private theorem checked7_94 : replayAbundance bank 7 2413 (10^300) 7 state7_94 tree7_94 = true := by
  decide +kernel

theorem reject7_94 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_94 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree7_94 checked7_94

@[expose] noncomputable def state7_95 : State := ⟨18298408842147894542300861986327115684149861257982901377737468587409982332190638187845249243489098657914869819212416800604317350650554313, 21348469286997325392789112832701923406866015182763052316319876286624345824711938840847283425285380748890432029444582045053538947399582406, 310897033⟩

private noncomputable def tree7_95 : AbundanceTree :=
  .split 1123 [
    (4, .split 1983851 [
      (2, .round 1 [(1831394497, 1)])]),
    (6, .round 1 [(3823, 1), (293147, 1), (15852481, 1)])]

private theorem checked7_95 : replayAbundance bank 7 2413 (10^300) 5 state7_95 tree7_95 = true := by
  decide +kernel

theorem reject7_95 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_95 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree7_95 checked7_95

end OddPerfect.IndexComponent.Size300
