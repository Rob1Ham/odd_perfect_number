module

public import OddPerfect.SizeIndex300.Seed127Part01

public section

namespace OddPerfect.IndexComponent.Size300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def state127_49 : State := ⟨527399530425123669256933654140549652560114586489, 532210559469627323043744137674299205591066335297, 0⟩

private noncomputable def tree127_49 : AbundanceTree :=
  .split 7099454441103522204145488136066513 [
    (1, .split 15469507184813921 [
      (2, .split 239305652541009538839586580208163 [
        (2, .round 1 [(19089065112692795051048167029917288207982194530854987378330680911, 1)])]),
      (4, .round 1 [(491, 1), (4583, 1), (373861, 1), (1682207, 1), (29763857, 1), (30920646556590231333162780266099496298031, 1)])]),
    (2, .split 593908784114903953873113805266296003229807455843032095043 [])]

private theorem checked127_49 : replayAbundance bank 127 1 (10^300) 6 state127_49 tree127_49 = true := by
  decide +kernel

theorem reject127_49 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_49 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree127_49 checked127_49

@[expose] noncomputable def state127_50 : State := ⟨546643771049513770233298082658798925842356063032683657878329, 551630349360261039665817048329394431944313552122605467845557, 0⟩

private noncomputable def tree127_50 : AbundanceTree :=
  .split 3011913661965600461029 [
    (1, .abundant [(3, 2), (5, 2), (13, 2), (31, 2)]),
    (2, .split 7796189653827459075869274769999 [
      (2, .round 49276157093 [(67, 1), (137, 1), (313, 1), (443, 1), (1531, 1), (284131, 1), (7152367, 1), (83774233, 1), (49276157093, 1)])]),
    (4, .round 1215659822020580867661554768262393014202201476258450467299826070592486000412921 [(31, 1), (137, 1), (313, 1), (443, 1), (1531, 1), (6154111, 1), (83774233, 1), (49276157093, 1), (1215659822020580867661554768262393014202201476258450467299826070592486000412921, 1)])]

private theorem checked127_50 : replayAbundance bank 127 1 (10^300) 5 state127_50 tree127_50 = true := by
  decide +kernel

theorem reject127_50 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_50 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree127_50 checked127_50

@[expose] noncomputable def state127_51 : State := ⟨556527637073860028712886345291352669220511703008377611096427066649, 561604377707043919524014686380238212668298685458534779568551014287, 0⟩

private noncomputable def tree127_51 : AbundanceTree :=
  .split 319876154622823252591170110865566399 [
    (2, .round 1115761626186517425361 [(313, 1), (823, 1), (1434637, 1), (40260089, 1), (91330330501, 1), (1115761626186517425361, 1), (1273270316712826178403249504283877053231, 1)])]

private theorem checked127_51 : replayAbundance bank 127 1 (10^300) 4 state127_51 tree127_51 = true := by
  decide +kernel

theorem reject127_51 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_51 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree127_51 checked127_51

@[expose] noncomputable def state127_52 : State := ⟨576834730926104419937944091647483143750639602772244532481970768187739746768089, 582096716355114839847752374251393426211085285371849351917244056321835521538947, 0⟩

private noncomputable def tree127_52 : AbundanceTree :=
  .split 27945714132675033142899109225439212386442031501005140283 []

private theorem checked127_52 : replayAbundance bank 127 1 (10^300) 3 state127_52 tree127_52 = true := by
  decide +kernel

theorem reject127_52 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_52 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_52 checked127_52

@[expose] noncomputable def state127_53 : State := ⟨608693127818431859964798197301953130276283268005306031584418524297933227699127617494314439152249, 614245731012378027478293501096473720558916274910924390788136904525161462781567324695223157073937, 0⟩

private noncomputable def tree127_53 : AbundanceTree :=
  .split 22989758668864328087586403746084268421181779 []

private theorem checked127_53 : replayAbundance bank 127 1 (10^300) 3 state127_53 tree127_53 = true := by
  decide +kernel

theorem reject127_53 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_53 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_53 checked127_53

@[expose] noncomputable def state127_54 : State := ⟨619698908262516926424821713507369744824808745774109969941496395635764158389155543946229138526560814169, 625351908074812834593128525889799061900342040077588814697977207895880907190120843493037969235869353067, 0⟩

private noncomputable def tree127_54 : AbundanceTree :=
  .split 541967059114154224732799381256192501745719196265286977 [
    (1, .round 1 [(313, 1), (2401104071, 1), (57643774229, 1), (448918291337, 1), (17459400920798357, 1)])]

private theorem checked127_54 : replayAbundance bank 127 1 (10^300) 4 state127_54 tree127_54 = true := by
  decide +kernel

theorem reject127_54 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_54 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree127_54 checked127_54

@[expose] noncomputable def state127_55 : State := ⟨653924679899867261081224944606742955405611669774613784774166014397597225111142221934219739397600889236231476562969473529, 659889893075882155771858526770422550586594479269754249003717639830847053096974303921361700704360115060055408141472100857, 0⟩

private noncomputable def tree127_55 : AbundanceTree :=
  .round 1 [(1499025812676956770716461023567442851876812436145044297287136788018753991293665859895506372495976207, 1)]

private theorem checked127_55 : replayAbundance bank 127 1 (10^300) 3 state127_55 tree127_55 = true := by
  decide +kernel

theorem reject127_55 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_55 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_55 checked127_55

@[expose] noncomputable def state127_56 : State := ⟨677785686905460230804996930741519913703839310337857571490473678970309161322691175088634959104437548872757065346746353088806620387769, 683968564283114589850579611736796044460196830348538431625115004191744520356464854520555146435032770453538819794006504361252228644717, 0⟩

private noncomputable def tree127_56 : AbundanceTree :=
  .round 1235984635787783426003808201972989 [(583685047309400717017752889, 1), (1235984635787783426003808201972989, 1), (5698024531416050565147586354033062043, 1)]

private theorem checked127_56 : replayAbundance bank 127 1 (10^300) 3 state127_56 tree127_56 = true := by
  decide +kernel

theorem reject127_56 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_56 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_56 checked127_56

@[expose] noncomputable def state127_57 : State := ⟨690040729910397857238182080246257335263518428908076374240592933559771321268566754225412567800004884193925385845280873899005332891000251289, 696335399893917584749667941696609053740081649238070355007328708582535453029030095555141304037724597976109255194701935966608512449720626247, 0⟩

private noncomputable def tree127_57 : AbundanceTree :=
  .round 1 [(1165167952932192898134826517617019328133672097062322352048550076460346220839, 1)]

private theorem checked127_57 : replayAbundance bank 127 1 (10^300) 3 state127_57 tree127_57 = true := by
  decide +kernel

theorem reject127_57 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_57 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_57 checked127_57

@[expose] noncomputable def state127_58 : State := ⟨715219572668034281119646439504780906980027167388899556847731584295157635075204138803802766524735424548699302156001373234000544617785985712115861431129, 721743928377129711114514729791640884458294975958935468844260904417475725251643427596791285386169687454304363135576801885570871142792865667750380968507, 0⟩

private noncomputable def tree127_58 : AbundanceTree :=
  .round 1 [(8517104784989720539108480605094824391619892292091059180304914213169249723081486058810390185408695326334866356155272375247895068591327, 1)]

private theorem checked127_58 : replayAbundance bank 127 1 (10^300) 3 state127_58 tree127_58 = true := by
  decide +kernel

theorem reject127_58 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_58 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_58 checked127_58

@[expose] noncomputable def state127_59 : State := ⟨473637133369, 477484038117, 0⟩

private theorem checked127_59 : checkChildren bank 127 1 (10^300) state127_59 1009 [state127_33, state127_45, state127_46, state127_47, state127_48, state127_49, state127_50, state127_51, state127_52, state127_53, state127_54, state127_55, state127_56, state127_57, state127_58] = true := by
  decide +kernel

theorem reject127_59 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_59 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state127_33, state127_45, state127_46, state127_47, state127_48, state127_49, state127_50, state127_51, state127_52, state127_53, state127_54, state127_55, state127_56, state127_57, state127_58] ?_ checked127_59
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject127_33 ho hN hs hav hx hvalid
  · exact reject127_45 ho hN hs hav hx hvalid
  · exact reject127_46 ho hN hs hav hx hvalid
  · exact reject127_47 ho hN hs hav hx hvalid
  · exact reject127_48 ho hN hs hav hx hvalid
  · exact reject127_49 ho hN hs hav hx hvalid
  · exact reject127_50 ho hN hs hav hx hvalid
  · exact reject127_51 ho hN hs hav hx hvalid
  · exact reject127_52 ho hN hs hav hx hvalid
  · exact reject127_53 ho hN hs hav hx hvalid
  · exact reject127_54 ho hN hs hav hx hvalid
  · exact reject127_55 ho hN hs hav hx hvalid
  · exact reject127_56 ho hN hs hav hx hvalid
  · exact reject127_57 ho hN hs hav hx hvalid
  · exact reject127_58 ho hN hs hav hx hvalid

@[expose] noncomputable def state127_60 : State := ⟨13908620131812505009, 14021586647939201577, 0⟩

private noncomputable def tree127_60 : AbundanceTree :=
  .split 836561914831 [
    (2, .split 347568611538691 [
      (2, .split 281362890397573 [
        (1, .split 3325881113 [
          (2, .abundant [(3, 4), (7, 4), (13, 2), (19, 2), (61, 2)]),
          (4, .abundant [(3, 4), (7, 2), (11, 2), (31, 2), (61, 2)]),
          (6, .round 1 [(6157549, 1), (20143639, 1), (50132989313743981, 1), (26997075678373361428517399627207223712603, 1)])]),
        (2, .split 3406268064750955554962983 [
          (2, .split 2684177863931427575235522828887908895012821 [
            (1, .round 1 [(463797723241, 1), (17973257912769806741195766611, 1)])])]),
        (4, .split 15120866040945290672141262005762437021 [
          (1, .round 1 [(5583869, 1), (6157549, 1), (20143639, 1), (573663131, 1), (97598032277, 1), (5149146324851, 1)])]),
        (6, .round 1 [(577261367752481355962267550400295836359010006575077847181127, 1)])]),
      (4, .split 1553856171496325342304906710960367907213898244703511 []),
      (6, .round 96187110422490505321 [(4573633, 1), (6157549, 1), (175010608151, 1), (96187110422490505321, 1), (22898167557805240362824718730100007611882028955979, 1)])]),
    (4, .split 24775760241107316406238530697611 [
      (2, .split 1229641748503576110369888978709876411 [])]),
    (6, .split 288663488733680253672029344853020258410277627 [
      (2, .round 1 [(18839057791, 1)])]),
    (10, .split 758822726669866515154920409897327831678341383440090905799226092821328735152832649080380226209910157 [])]

private theorem checked127_60 : replayAbundance bank 127 1 (10^300) 8 state127_60 tree127_60 = true := by
  decide +kernel

theorem reject127_60 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_60 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree127_60 checked127_60

@[expose] noncomputable def state127_61 : State := ⟨408434432906568156404595049, 411751758026844148288802637, 0⟩

private noncomputable def tree127_61 : AbundanceTree :=
  .split 829621381 [
    (1, .split 414810691 [
      (2, .split 95359493521 [
        (2, .split 31029319 [
          (2, .split 427884607 [
            (2, .abundant [(3, 6), (7, 2), (13, 4), (29, 2), (103, 2), (127, 2), (211, 2)]),
            (4, .abundant [(3, 4), (7, 2), (13, 4), (29, 2), (31, 2)]),
            (6, .abundant [(3, 4), (7, 2), (13, 4), (29, 2), (43, 2), (103, 2)])]),
          (4, .abundant [(3, 4), (7, 2), (13, 2), (29, 2), (103, 2), (127, 2), (211, 2), (241, 2)]),
          (6, .split 182324105002490944624125858291443 [
            (2, .round 1 [(38748851, 1)])]),
          (10, .split 475483 [
            (2, .abundant [(3, 4), (7, 2), (13, 2), (29, 2), (31, 2)]),
            (4, .round 1 [(6380491850704250171, 1)])]),
          (12, .abundant [(3, 4), (7, 2), (13, 2), (29, 2), (103, 2), (127, 2), (157, 2), (211, 2)])]),
        (4, .abundant [(3, 2), (5, 2), (7, 2)]),
        (6, .split 110997250014986885992304442256975000490342960018363 []),
        (10, .round 1 [(3559, 1), (475483, 1)])]),
      (4, .abundant [(3, 2), (5, 2), (7, 2)]),
      (6, .split 58320489808015675283 [
        (2, .split 9201059666631735331095181 [
          (2, .round 1 [(213991755624069403, 1)])]),
        (4, .round 1 [(213991755624069403, 1)])]),
      (10, .round 1 [(180044256749103712547991089917917320449575398825781695596603515416271470773424701, 1)]),
      (12, .split 391771001205246406092493 [])]),
    (2, .split 154702548132607 [
      (2, .split 6266791934726823850590403 [
        (2, .split 16010700115729044644102887 [
          (2, .round 7655458506024501728976818904175060093 [(1499, 1), (1723, 1), (475483, 1), (67791564436340859853, 1), (7655458506024501728976818904175060093, 1)])]),
        (4, .abundant [(3, 4), (7, 2), (11, 2), (19, 2)])]),
      (4, .split 114291154039309381 [
        (1, .split 11623389313512671 [
          (2, .split 404573891 [
            (2, .abundant [(3, 2), (7, 2), (17, 2), (19, 2), (29, 2), (43, 2), (127, 2)])])]),
        (2, .split 698785124190250897823681113 [
          (1, .round 1 [(475483, 1), (6231037, 1), (55849049, 1), (164853258892057, 1), (11623389313512671, 1)])]),
        (4, .abundant [(3, 2), (5, 1), (7, 2)])]),
      (6, .round 1 [(7228570959808507, 1), (1529490731111602564658371813263226399358287058043237202570351, 1)])]),
    (4, .abundant [(3, 2), (5, 1), (7, 2)]),
    (6, .split 27395631932423126416280468114484772969719691 [
      (2, .split 459182826388161937576413177755847569554864778530680145963289411449 [])]),
    (10, .split 56809265962192046283734033196289431057897325583 []),
    (12, .round 1 [(5948538021402454432929226539826423913602238804222863077260622056212123803954970953695423, 1)])]

private theorem checked127_61 : replayAbundance bank 127 1 (10^300) 8 state127_61 tree127_61 = true := by
  decide +kernel

theorem reject127_61 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_61 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree127_61 checked127_61

@[expose] noncomputable def state127_62 : State := ⟨352207785730653960250304937411058362386329, 355068435178954412868160234828237218901557, 0⟩

private noncomputable def tree127_62 : AbundanceTree :=
  .split 830088529041623897 [
    (1, .split 27121758120683 [
      (2, .split 22987759093064683 [
        (2, .split 82619968102045394968069609 [
          (2, .round 1 [(848715199059453874962956479489684884692749, 1)])]),
        (4, .split 43038337 [
          (2, .abundant [(3, 4), (7, 2), (11, 2), (67, 2), (79, 2), (127, 2), (139, 2), (211, 2)])])]),
      (4, .split 433471463064816310331 [
        (2, .round 1 [(9438197072471, 1), (13812946356800147815593309862088459431, 1)])]),
      (6, .round 1 [(388651149984019343, 1), (1291448434929120875763970555997348809534162621, 1)])]),
    (2, .split 27924055055589429150074083 [
      (2, .split 586175292554936619690474283243 [
        (2, .round 24675748729 [(43038337, 1), (24675748729, 1)])])]),
    (4, .split 6774953864043126592402408864370354018322956829078992011 []),
    (6, .round 43038337 [(43, 1), (67, 1), (5783, 1), (33287, 1), (274121, 1), (8368123, 1), (43038337, 1)])]

private theorem checked127_62 : replayAbundance bank 127 1 (10^300) 7 state127_62 tree127_62 = true := by
  decide +kernel

theorem reject127_62 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_62 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree127_62 checked127_62

@[expose] noncomputable def state127_63 : State := ⟨10342779216548448439621904908145616415215849815569, 10426783792422131727299144333622924574124113191417, 0⟩

private noncomputable def tree127_63 : AbundanceTree :=
  .split 997095307634462220855658215075433 [
    (1, .split 498547653817231110427829107537717 [
      (2, .split 41714048449068420177806463620463823 [])]),
    (2, .split 348447070076681960207943110309920506978127 [])]

private theorem checked127_63 : replayAbundance bank 127 1 (10^300) 5 state127_63 tree127_63 = true := by
  decide +kernel

theorem reject127_63 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_63 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree127_63 checked127_63

@[expose] noncomputable def state127_64 : State := ⟨8918952646176310882544948520204157613991271727562225333925261249, 8991392830636666913717507558347744169337208491562521540893531937, 0⟩

private noncomputable def tree127_64 : AbundanceTree :=
  .split 124817696072779678581316616209791886786018319 [
    (2, .round 1 [(2132840385459670115313391072326679294901556140093088243974767, 1)])]

private theorem checked127_64 : replayAbundance bank 127 1 (10^300) 4 state127_64 tree127_64 = true := by
  decide +kernel

theorem reject127_64 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_64 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree127_64 checked127_64

@[expose] noncomputable def state127_65 : State := ⟨261910047987401873976337521011914922867275143383303909339127628648445689, 264037294643023711091453204972621740617066125528697211622923006689534597, 0⟩

private noncomputable def tree127_65 : AbundanceTree :=
  .split 475616555301816168614994177768361558520855212259287915469003 []

private theorem checked127_65 : replayAbundance bank 127 1 (10^300) 3 state127_65 tree127_65 = true := by
  decide +kernel

theorem reject127_65 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_65 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_65 checked127_65

@[expose] noncomputable def state127_66 : State := ⟨225854508411033353876347414836550088061747096775276948286026230708995418801706198857769, 227688910150739021095987330950105439365375729915076944240711970338710804559819040884717, 0⟩

private noncomputable def tree127_66 : AbundanceTree :=
  .split 50108770334077047291351366118996698593241671 []

private theorem checked127_66 : replayAbundance bank 127 1 (10^300) 3 state127_66 tree127_66 = true := by
  decide +kernel

theorem reject127_66 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_66 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_66 checked127_66

@[expose] noncomputable def state127_67 : State := ⟨5719310438480509376241401710524111097589623248908938033858872101128438253500947995898924599498839941374343889, 5765762967110896023975606990342334968854207995202769698599846808091672654447614664745748345306764108054911897, 0⟩

private noncomputable def tree127_67 : AbundanceTree :=
  .split 354663404509497202680421171823973363403715814430877142068022809134014434055952184581764676465938617706521 []

private theorem checked127_67 : replayAbundance bank 127 1 (10^300) 3 state127_67 tree127_67 = true := by
  decide +kernel

theorem reject127_67 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_67 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_67 checked127_67

@[expose] noncomputable def state127_68 : State := ⟨167950759559136145399088832655900126407045034482853603278502774076885322367915551931397620160983753727664719307406729, 169314864122236010956713149586924248410321344989814640953185416033671306926213349742085822524754845127697106749092157, 0⟩

private noncomputable def tree127_68 : AbundanceTree :=
  .split 6056742050613547620601509870890807474528726692309512243313892198595289428485734539635914899197 []

private theorem checked127_68 : replayAbundance bank 127 1 (10^300) 3 state127_68 tree127_68 = true := by
  decide +kernel

theorem reject127_68 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_68 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_68 checked127_68

@[expose] noncomputable def state127_69 : State := ⟨4253014646708608867073205701790028757161452686353348583114278799334220260681716344713682944113095405087975190472059101526113411573761273649, 4287557846761616214535366522056798109682092672049593142954706336476382740170829322906693659378895185835609789149932652673255037423817010537, 0⟩

private noncomputable def tree127_69 : AbundanceTree :=
  .split 263736104248115655688956543154136563307011913148157294885569682996640385075403169275185683667275338982322063674105471653641818135192041 []

private theorem checked127_69 : replayAbundance bank 127 1 (10^300) 3 state127_69 tree127_69 = true := by
  decide +kernel

theorem reject127_69 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_69 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_69 checked127_69

@[expose] noncomputable def state127_70 : State := ⟨16129, 16257, 0⟩

private theorem checked127_70 : checkChildren bank 127 1 (10^300) state127_70 5419 [state127_59, state127_60, state127_61, state127_62, state127_63, state127_64, state127_65, state127_66, state127_67, state127_68, state127_69] = true := by
  decide +kernel

theorem reject127_70 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_70 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state127_59, state127_60, state127_61, state127_62, state127_63, state127_64, state127_65, state127_66, state127_67, state127_68, state127_69] ?_ checked127_70
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject127_59 ho hN hs hav hx hvalid
  · exact reject127_60 ho hN hs hav hx hvalid
  · exact reject127_61 ho hN hs hav hx hvalid
  · exact reject127_62 ho hN hs hav hx hvalid
  · exact reject127_63 ho hN hs hav hx hvalid
  · exact reject127_64 ho hN hs hav hx hvalid
  · exact reject127_65 ho hN hs hav hx hvalid
  · exact reject127_66 ho hN hs hav hx hvalid
  · exact reject127_67 ho hN hs hav hx hvalid
  · exact reject127_68 ho hN hs hav hx hvalid
  · exact reject127_69 ho hN hs hav hx hvalid

@[expose] noncomputable def state127_71 : State := ⟨950061131819315529165821977489159738987210700600288201, 957670745726300648794639796776425811865509955231187306, 262209281⟩

private noncomputable def tree127_71 : AbundanceTree :=
  .split 2773167361 [
    (2, .split 727642843683307 [
      (2, .split 740989 [
        (2, .split 776467 [
          (2, .split 325597 [
            (2, .split 35337910669 [
              (2, .split 612415423 [
                (2, .abundant [(3, 10), (7, 2), (13, 6), (43, 2), (79, 2), (127, 4), (151, 2), (223, 2), (229, 2)]),
                (4, .abundant [(3, 10), (7, 2), (11, 2), (13, 4)])]),
              (4, .round 1 [(1559421344165064403643738302020721661495261, 1)])]),
            (4, .abundant [(3, 8), (7, 2), (13, 2), (31, 2), (41, 2)]),
            (6, .round 1 [(223, 1), (229, 1), (271, 1), (601, 1), (3137, 1), (12277, 1), (1229576892433, 1), (969009443060272914259, 1)]),
            (10, .abundant [(3, 8), (7, 2), (13, 2), (23, 2), (79, 2)])]),
          (4, .split 1136796912795881 [
            (2, .round 1 [(3137, 1), (12277, 1), (25759, 1), (174631, 1), (30687997, 1), (1634813550790560841, 1)])]),
          (6, .split 336423368757297801862701509531 []),
          (10, .round 1 [(31855995609962377124403031307, 1)])]),
        (4, .split 858576981721 [
          (2, .split 35102592073428616433503 [
            (2, .round 1 [(1161684238842332536085964194997877, 1)])]),
          (4, .abundant [(3, 6), (5, 2), (13, 2)])]),
        (6, .split 5005107915858278965988749 [
          (2, .round 1 [(767541166372278134742774626497, 1)])]),
        (10, .round 1 [(167676893338405384303641648007444400587092642212543, 1)]),
        (12, .round 1 [(7405390173088189633256732503, 1)])]),
      (4, .split 619407888580423076012074149709822126167996555718776821 []),
      (6, .split 740989 [
        (2, .abundant [(3, 6), (7, 2), (13, 2), (29, 2), (127, 4), (151, 2), (211, 2), (223, 2)])])]),
    (4, .split 740989 [
      (2, .abundant [(3, 4), (5, 2), (7, 2)]),
      (4, .split 858576981721 [
        (2, .abundant [(3, 4), (5, 2), (7, 2)]),
        (4, .round 1 [(2128693124521, 1), (90082468738068954601, 1)])]),
      (6, .split 5005107915858278965988749 [
        (2, .round 1 [(767541166372278134742774626497, 1)])]),
      (10, .round 1 [(167676893338405384303641648007444400587092642212543, 1)]),
      (12, .round 1 [(7405390173088189633256732503, 1)])]),
    (6, .split 740989 [
      (2, .split 776467 [
        (2, .split 325597 [
          (2, .split 35337910669 [
            (2, .round 1 [(223, 1), (229, 1), (601, 1), (1831, 1), (3137, 1), (12277, 1), (2196541, 1), (612415423, 1)])]),
          (4, .abundant [(3, 6), (7, 2), (13, 2), (31, 2), (41, 2)]),
          (6, .round 1 [(969009443060272914259, 1)])]),
        (4, .split 1136796912795881 [
          (2, .round 1 [(1634813550790560841, 1)])]),
        (6, .round 1 [(15149, 1), (336423368757297801862701509531, 1)])]),
      (4, .split 858576981721 [
        (2, .round 1 [(229, 1), (1531, 1), (3137, 1), (12277, 1), (42701, 1), (35102592073428616433503, 1)])]),
      (6, .split 5005107915858278965988749 []),
      (10, .round 1 [(167676893338405384303641648007444400587092642212543, 1)])]),
    (10, .split 740989 [
      (2, .split 776467 [
        (2, .round 1 [(325597, 1)])])]),
    (12, .round 1 [(740989, 1)])]

private theorem checked127_71 : replayAbundance bank 127 1 (10^300) 10 state127_71 tree127_71 = true := by
  decide +kernel

theorem reject127_71 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_71 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 10 h tree127_71 checked127_71

@[expose] noncomputable def state127_72 : State := ⟨1810022833070443580216010465512940330096632173297701628679341894529, 1824520400080808276463676029079416808626687094308974324702640636798, 262209281⟩

private noncomputable def tree127_72 : AbundanceTree :=
  .split 493295840179661 [
    (2, .split 83250354409359610382688421 [
      (2, .split 740989 [
        (2, .split 776467 [
          (2, .abundant [(3, 6), (7, 2), (13, 2), (31, 2), (37, 2)]),
          (4, .round 1 [(1136796912795881, 1)])]),
        (4, .round 1 [(131, 3), (1531, 1), (3137, 1), (12277, 1), (13831, 1), (42701, 1), (858576981721, 1)]),
        (6, .round 1 [(5005107915858278965988749, 1)])])]),
    (4, .split 740989 [
      (2, .abundant [(3, 4), (5, 2), (7, 2)]),
      (4, .split 858576981721 [
        (2, .abundant [(3, 4), (5, 2), (7, 2)])]),
      (6, .round 1 [(34702823, 1), (5005107915858278965988749, 1)])]),
    (6, .split 740989 [
      (2, .round 1 [(3137, 1), (12277, 1), (13831, 1), (776467, 1)])])]

private theorem checked127_72 : replayAbundance bank 127 1 (10^300) 7 state127_72 tree127_72 = true := by
  decide +kernel

theorem reject127_72 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_72 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree127_72 checked127_72

@[expose] noncomputable def state127_73 : State := ⟨3448391420836933728351382541238204526119590376041762565465444901343457136395641, 3476011672243786839041284884158685026362483529349015806644988466163572714548466, 262209281⟩

private noncomputable def tree127_73 : AbundanceTree :=
  .split 97395630516874503993254933258403437 [
    (2, .split 740989 [
      (2, .split 776467 [
        (2, .split 325597 [
          (2, .round 1 [(12277, 1), (35337910669, 1)])]),
        (4, .round 1 [(1136796912795881, 1)])]),
      (4, .round 1 [(3137, 1), (3163, 1), (12277, 1), (42701, 1), (858576981721, 1)]),
      (6, .round 1 [(5005107915858278965988749, 1)])])]

private theorem checked127_73 : replayAbundance bank 127 1 (10^300) 7 state127_73 tree127_73 = true := by
  decide +kernel

theorem reject127_73 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_73 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree127_73 checked127_73

@[expose] noncomputable def state127_74 : State := ⟨12516461302369431911194723155413415772066520714150918849218281183069043947141487413686686336892852336681, 12616713207013043285069935017375078487707722431059467773027498072050091131091841461092689339908615660026, 262209281⟩

private noncomputable def tree127_74 : AbundanceTree :=
  .split 740989 [
    (2, .split 776467 [
      (2, .split 325597 [
        (2, .split 35337910669 [
          (2, .split 612415423 [
            (2, .round 1 [(31949284516627, 1)])])]),
        (4, .abundant [(3, 4), (7, 2), (13, 2), (31, 2), (41, 2), (79, 2)]),
        (6, .round 1 [(1229576892433, 1), (969009443060272914259, 1)])]),
      (4, .split 1136796912795881 [
        (2, .round 1 [(1634813550790560841, 1)])]),
      (6, .round 1 [(3137, 1), (12277, 1), (15149, 1), (336423368757297801862701509531, 1)])]),
    (4, .split 858576981721 [
      (2, .split 35102592073428616433503 [])]),
    (6, .split 5005107915858278965988749 []),
    (10, .round 1 [(167676893338405384303641648007444400587092642212543, 1)])]

private theorem checked127_74 : replayAbundance bank 127 1 (10^300) 8 state127_74 tree127_74 = true := by
  decide +kernel

theorem reject127_74 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_74 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree127_74 checked127_74

@[expose] noncomputable def state127_75 : State := ⟨23845918949602792879268118480975998652665521119337460393015751427036264134119390260801624970182785256895402699316449, 24036915329084452904843284133939627015168406188988478424017305067865830681095004653697245576354341974162991742369678, 262209281⟩

private noncomputable def tree127_75 : AbundanceTree :=
  .split 740989 [
    (2, .split 776467 [
      (2, .split 325597 [
        (2, .split 35337910669 [
          (2, .round 1 [(2196541, 1), (612415423, 1)])]),
        (4, .abundant [(3, 4), (7, 2), (13, 2), (31, 2), (41, 2), (79, 2)]),
        (6, .round 1 [(969009443060272914259, 1)])]),
      (4, .split 1136796912795881 []),
      (6, .round 1 [(336423368757297801862701509531, 1)])]),
    (4, .split 858576981721 [
      (2, .round 1 [(35102592073428616433503, 1)])]),
    (6, .round 1 [(34702823, 1), (5005107915858278965988749, 1)])]

private theorem checked127_75 : replayAbundance bank 127 1 (10^300) 7 state127_75 tree127_75 = true := by
  decide +kernel

theorem reject127_75 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_75 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree127_75 checked127_75

@[expose] noncomputable def state127_76 : State := ⟨86552390760705080764626229677486315648941916949301866943533087215705053625436404829938176290093647905368878329016891073551043331166759605009, 87245641178343186368548669748553405245839399840317357380957025249620748551984362355810718098935974850648785197427591671163139561837433602518, 262209281⟩

private noncomputable def tree127_76 : AbundanceTree :=
  .split 740989 [
    (2, .split 776467 [
      (2, .round 1 [(3137, 1), (12277, 1), (325597, 1)])]),
    (4, .round 1 [(858576981721, 1)])]

private theorem checked127_76 : replayAbundance bank 127 1 (10^300) 5 state127_76 tree127_76 = true := by
  decide +kernel

theorem reject127_76 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_76 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree127_76 checked127_76

@[expose] noncomputable def state127_77 : State := ⟨164896550639549520734640505831923948283732429140260901273563029919777103925711867624464753457717974029276614635688532661171193346019524359926658813415561, 166217306791901233026200916370512150136309333301877605170069962633773183975232398400322335156815258050327472679711599377381791908094826962114422435678346, 262209281⟩

private noncomputable def tree127_77 : AbundanceTree :=
  .split 740989 [
    (2, .round 1 [(776467, 1)])]

private theorem checked127_77 : replayAbundance bank 127 1 (10^300) 4 state127_77 tree127_77 = true := by
  decide +kernel

theorem reject127_77 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_77 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree127_77 checked127_77

@[expose] noncomputable def state127_78 : State := ⟨498676667333881234206717621448211392729169, 502670506026353395902815517792078492088758, 262209281⟩

private theorem checked127_78 : checkChildren bank 127 1 (10^300) state127_78 1380277 [state127_71, state127_72, state127_73, state127_74, state127_75, state127_76, state127_77] = true := by
  decide +kernel

theorem reject127_78 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_78 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state127_71, state127_72, state127_73, state127_74, state127_75, state127_76, state127_77] ?_ checked127_78
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject127_71 ho hN hs hav hx hvalid
  · exact reject127_72 ho hN hs hav hx hvalid
  · exact reject127_73 ho hN hs hav hx hvalid
  · exact reject127_74 ho hN hs hav hx hvalid
  · exact reject127_75 ho hN hs hav hx hvalid
  · exact reject127_76 ho hN hs hav hx hvalid
  · exact reject127_77 ho hN hs hav hx hvalid

@[expose] noncomputable def state127_79 : State := ⟨18784972728882955094674157507712277143475061850896138807081, 18935419212218049373394942165680256180564993044630185872706, 262209281⟩

private noncomputable def tree127_79 : AbundanceTree :=
  .split 187039475551 [
    (2, .split 1861441475983 [
      (2, .split 78372732118311223 [
        (2, .split 1226739592508202843601507810279 []),
        (4, .round 1 [(14737117, 1), (817170061, 1)])]),
      (4, .split 189807767334990199796008528480002671 []),
      (6, .round 1 [(3137, 1), (4219, 1), (8681, 1), (91411, 1), (297841, 1), (321679, 1), (817170061, 1)])]),
    (4, .abundant [(3, 2), (5, 2), (11, 2), (31, 2)]),
    (6, .round 1 [(91411, 1), (297841, 1), (11725981, 1), (817170061, 1), (84914530903304553545666061499881394732390301127632672185279, 1)])]

private theorem checked127_79 : replayAbundance bank 127 1 (10^300) 6 state127_79 tree127_79 = true := by
  decide +kernel

theorem reject127_79 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_79 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree127_79 checked127_79

@[expose] noncomputable def state127_80 : State := ⟨707623242754636873931595261590255884341674002753786175446491996161468719169, 713290508283051694252055486437055148501706920388697007661515769307138923758, 262209281⟩

private noncomputable def tree127_80 : AbundanceTree :=
  .split 102638746262804858777501321 [
    (2, .split 10534712234400438364326051101268091387747998934246363 [])]

private theorem checked127_80 : replayAbundance bank 127 1 (10^300) 4 state127_80 tree127_80 = true := by
  decide +kernel

theorem reject127_80 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_80 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree127_80 checked127_80

@[expose] noncomputable def state127_81 : State := ⟨1004118873986400687484099262932941308697328642721989473280231040996118598718183437033238534606001924444709169, 1012160735724606776632526905492657628535771320367647627939370948077342605728050671241810410049501478635758758, 262209281⟩

private noncomputable def tree127_81 : AbundanceTree :=
  .split 13381309681257009556475149527135960619812344958842911830265029943 []

private theorem checked127_81 : replayAbundance bank 127 1 (10^300) 3 state127_81 tree127_81 = true := by
  decide +kernel

theorem reject127_81 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_81 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_81 checked127_81

@[expose] noncomputable def state127_82 : State := ⟨37824800918071039843869578680012335524225194519639922673599718050201661314186731494558275973062238590730634128608604561827081, 38127734990060625555225940834799262459709644918071678908239262086571360370934084144913242428507627454092687353986716879702706, 262209281⟩

private noncomputable def tree127_82 : AbundanceTree :=
  .round 1 [(596900628921541048878197250999695160956137589518479887723814165311483148211728883016437, 1)]

private theorem checked127_82 : replayAbundance bank 127 1 (10^300) 3 state127_82 tree127_82 = true := by
  decide +kernel

theorem reject127_82 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_82 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_82 checked127_82

@[expose] noncomputable def state127_83 : State := ⟨53673472282739529003483745765097002095508483238619222280473621371528202089153118820833932181324785257037106999783642417248865979353164987791932402176923337081, 54103336369840708133763706003571792984206361812438010946359091789769465281315751509277272501074455760415825579795675345694665785481226103913254255314701617706, 262209281⟩

private noncomputable def tree127_83 : AbundanceTree :=
  .round 1 [(239, 1), (3137, 1)]

private theorem checked127_83 : replayAbundance bank 127 1 (10^300) 3 state127_83 tree127_83 = true := by
  decide +kernel

theorem reject127_83 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_83 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_83 checked127_83

@[expose] noncomputable def state127_84 : State := ⟨13238157016904760077297081, 13344179682268141313957706, 262209281⟩

private theorem checked127_84 : checkChildren bank 127 1 (10^300) state127_84 194086693 [state127_78, state127_79, state127_80, state127_81, state127_82, state127_83] = true := by
  decide +kernel

theorem reject127_84 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_84 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state127_78, state127_79, state127_80, state127_81, state127_82, state127_83] ?_ checked127_84
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject127_78 ho hN hs hav hx hvalid
  · exact reject127_79 ho hN hs hav hx hvalid
  · exact reject127_80 ho hN hs hav hx hvalid
  · exact reject127_81 ho hN hs hav hx hvalid
  · exact reject127_82 ho hN hs hav hx hvalid
  · exact reject127_83 ho hN hs hav hx hvalid

@[expose] noncomputable def state127_85 : State := ⟨2569165682822230462243617926910641, 2589741794218838803788109565289810, 262209281⟩

private noncomputable def tree127_85 : AbundanceTree :=
  .split 1394813567261 [
    (2, .abundant [(3, 2), (5, 2), (7, 2)]),
    (4, .split 47876387198627901679361 [
      (2, .split 1792141087719266316693639952577872550394877 []),
      (4, .abundant [(3, 2), (5, 4), (11, 2), (127, 4), (151, 2)])]),
    (6, .split 185395279782594286095686284641569841922664265843885045360762592543493 []),
    (10, .abundant [(3, 2), (5, 2), (11, 2), (23, 2)])]

private theorem checked127_85 : replayAbundance bank 127 1 (10^300) 5 state127_85 tree127_85 = true := by
  decide +kernel

theorem reject127_85 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_85 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree127_85 checked127_85

@[expose] noncomputable def state127_86 : State := ⟨498605077531760537985925185704644299149801, 502598340281143884866053558956472916508954, 262209281⟩

private noncomputable def tree127_86 : AbundanceTree :=
  .split 285472521588928549 [
    (2, .split 40338149992917567492211 [
      (2, .split 678332774652339154360193101922265800521 []),
      (4, .abundant [(3, 2), (5, 2), (7, 2)])]),
    (4, .split 169279177204032117446993967365464606391 []),
    (6, .split 3658159 [
      (2, .round 1 [(2269, 1), (2503, 1), (2857, 1), (3137, 1), (33829, 1)])])]

private theorem checked127_86 : replayAbundance bank 127 1 (10^300) 5 state127_86 tree127_86 = true := by
  decide +kernel

theorem reject127_86 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_86 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree127_86 checked127_86

@[expose] noncomputable def state127_87 : State := ⟨18779579591251912929890331531530305647460127621945776688921, 18929982784099561211419733399727743078283603696142054633962, 262209281⟩

private noncomputable def tree127_87 : AbundanceTree :=
  .split 249789449906249446733 [
    (2, .split 76410695565565800992671 [
      (2, .round 1 [(36023763577, 1), (200822829241, 1), (1946198132271192388009371231955701018265568971, 1)])]),
    (4, .round 1 [(278556835167700751, 1), (8939778539101733037651771620430771999970530403008551, 1)])]

private theorem checked127_87 : replayAbundance bank 127 1 (10^300) 5 state127_87 tree127_87 = true := by
  decide +kernel

theorem reject127_87 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_87 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree127_87 checked127_87

@[expose] noncomputable def state127_88 : State := ⟨3644604861693510188835416067529444972176479605003381074308336580881, 3673794024592668743188732390769079747501138111297970241195574352626, 262209281⟩

private noncomputable def tree127_88 : AbundanceTree :=
  .split 407894065567398422895591407413946559138619063763 [
    (2, .round 1 [(2165983622449672584328017946055161138981, 1)])]

private theorem checked127_88 : replayAbundance bank 127 1 (10^300) 4 state127_88 tree127_88 = true := by
  decide +kernel

theorem reject127_88 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_88 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree127_88 checked127_88

@[expose] noncomputable def state127_89 : State := ⟨137271259686434171282098709126637804236967906448522063122230646035242480542531889601, 138370647222919594189449223696896133941240737245652769370577113482225963547836254274, 262209281⟩

private noncomputable def tree127_89 : AbundanceTree :=
  .split 4920673432019850720282700666497718306083875473095857318070217033 []

private theorem checked127_89 : replayAbundance bank 127 1 (10^300) 3 state127_89 tree127_89 = true := by
  decide +kernel

theorem reject127_89 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_89 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_89 checked127_89

@[expose] noncomputable def state127_90 : State := ⟨26640612373294273865463806354742497315245859872854381159547581954873211503377941745413258361, 26853973547908988125345967912163259844202401642939368199044132576905918129490587612577874058, 262209281⟩

private noncomputable def tree127_90 : AbundanceTree :=
  .split 1217725963038029317159302248647 [
    (2, .round 1 [(3137, 1), (61637, 1), (2278747, 1), (6393083, 1), (209267118578121698317, 1)])]

private theorem checked127_90 : replayAbundance bank 127 1 (10^300) 4 state127_90 tree127_90 = true := by
  decide +kernel

theorem reject127_90 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_90 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree127_90 checked127_90

@[expose] noncomputable def state127_91 : State := ⟨1003398326588645425439787099641188631032461906346850874079635871152553607895947333125542654595381950999104681, 1011434412342515016218187905588572815568914502797251960830016024334671436397015696561487643055736576039763546, 262209281⟩

private noncomputable def tree127_91 : AbundanceTree :=
  .split 33552166761756203169531862795676299 []

private theorem checked127_91 : replayAbundance bank 127 1 (10^300) 3 state127_91 tree127_91 = true := by
  decide +kernel

theorem reject127_91 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_91 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_91 checked127_91

@[expose] noncomputable def state127_92 : State := ⟨7334442796698482836574714944883062268128448719258160871252487686571308767516504358023392855298380576668296795951597508847529936286161, 7393183388255482042364475997658345376040795351868883259395754370965307878498179223147718789059254095409294150229618908640895405398578, 262209281⟩

private noncomputable def tree127_92 : AbundanceTree :=
  .split 3137 [
    (2, .split 9843907 [
      (2, .round 1 [(59, 1), (233, 1), (1700044120501, 1)])]),
    (4, .split 10908731 [
      (2, .round 1 [(299749176169, 1)])]),
    (6, .round 1 [(42137940881, 1)])]

private theorem checked127_92 : replayAbundance bank 127 1 (10^300) 5 state127_92 tree127_92 = true := by
  decide +kernel

theorem reject127_92 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_92 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree127_92 checked127_92

@[expose] noncomputable def state127_93 : State := ⟨1423415563951836248605166712141418716510610345593345152066135813451396515895435113830132354015430197342788540357780150902762062765209351360521, 1434815512738076373347592825183784621819820402573160684137613242451055535195194175309112896244306034896639140796210925578703205488086062577402, 262209281⟩

private noncomputable def tree127_93 : AbundanceTree :=
  .round 1 [(3137, 1), (4960807, 1), (536701327, 1), (1319008032883, 1)]

private theorem checked127_93 : replayAbundance bank 127 1 (10^300) 3 state127_93 tree127_93 = true := by
  decide +kernel

theorem reject127_93 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_93 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_93 checked127_93

@[expose] noncomputable def state127_94 : State := ⟨68212339272613121, 68753707304746242, 262209281⟩

private theorem checked127_94 : checkChildren bank 127 1 (10^300) state127_94 13931 [state127_84, state127_85, state127_86, state127_87, state127_88, state127_89, state127_90, state127_91, state127_92, state127_93] = true := by
  decide +kernel

theorem reject127_94 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_94 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state127_84, state127_85, state127_86, state127_87, state127_88, state127_89, state127_90, state127_91, state127_92, state127_93] ?_ checked127_94
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject127_84 ho hN hs hav hx hvalid
  · exact reject127_85 ho hN hs hav hx hvalid
  · exact reject127_86 ho hN hs hav hx hvalid
  · exact reject127_87 ho hN hs hav hx hvalid
  · exact reject127_88 ho hN hs hav hx hvalid
  · exact reject127_89 ho hN hs hav hx hvalid
  · exact reject127_90 ho hN hs hav hx hvalid
  · exact reject127_91 ho hN hs hav hx hvalid
  · exact reject127_92 ho hN hs hav hx hvalid
  · exact reject127_93 ho hN hs hav hx hvalid

@[expose] noncomputable def state127_95 : State := ⟨17885908435999949448576001, 18027860158461960264481283, 0⟩

private noncomputable def tree127_95 : AbundanceTree :=
  .split 4296301150081 [
    (1, .split 123152587 [
      (2, .split 13339102733461 [
        (2, .split 839108393120143 [
          (2, .split 1567624160569 [
            (2, .split 50738998441 [
              (2, .round 1 [(151, 1), (379, 1), (397, 1), (571, 1), (1231, 1), (4363, 1), (4549, 1), (9433, 1), (17443, 1), (17491, 1), (17791, 1), (93979, 1), (96199, 1), (42232441, 1), (344461909346017, 1)]),
              (4, .abundant [(3, 4), (5, 2), (13, 2)])]),
            (4, .split 42232441 [
              (2, .round 1 [(1231, 1), (4549, 1), (17443, 1), (17491, 1), (93979, 1), (110557, 1), (472669, 1)])]),
            (6, .round 1 [(42232441, 1)])]),
          (4, .round 1 [(379, 1), (1231, 1), (3121, 1), (17443, 1), (17491, 1), (93979, 1), (185186707990152041, 1), (77978700807883897938537676040065740731, 1)]),
          (6, .round 1 [(1231, 1), (2017, 1), (17443, 1), (17491, 1), (93979, 1)])]),
        (4, .abundant [(3, 2), (5, 2), (13, 2), (31, 2)]),
        (6, .round 1 [(1159201, 1), (1597289, 1), (3464011840184281, 1), (125470043458596098806451717206806024172874202481709, 1)])]),
      (4, .split 2239675079541472691 [
        (2, .split 27874747639211916597758319853741 [
          (2, .round 1 [(215418943537314001084160888574073363257578983, 1)])]),
        (4, .round 1 [(102704422012531, 1), (36805908914339368365177508331329628145229111570447371537821, 1)])]),
      (6, .split 988979118833915893022329386772515511 [
        (2, .round 1 [(709741781675884596598513, 1), (670285567037496982972109475457, 1)])]),
      (10, .split 9137478695055695198006344538060368675414463416006549 []),
      (12, .split 1221324894479 [
        (2, .round 1 [(1231, 1), (17443, 1), (2472995956150534609, 1)])])]),
    (2, .split 4635303278743 [
      (2, .split 207837725713 [
        (1, .split 947239753 [
          (2, .split 33425173 [
            (2, .split 575709019 [
              (2, .split 9034453 [
                (2, .split 52461511 [
                  (2, .abundant [(3, 8), (7, 4), (13, 2), (31, 2), (43, 2)]),
                  (4, .abundant [(3, 6), (5, 2), (7, 2)])]),
                (4, .round 1 [(646879, 1), (666019, 1), (887143, 1), (4015513, 1), (8252681, 1), (91123391, 1), (8858956488251, 1)]),
                (6, .abundant [(3, 6), (7, 4), (13, 2), (29, 2), (43, 2)])]),
              (4, .round 1 [(5197, 1), (5419, 1), (14737, 1), (93251, 1), (108421, 1), (646879, 1), (887143, 1), (4015513, 1), (5459407361, 1), (6569400520481, 1)]),
              (6, .round 1 [(2038811844077614752925769002050361, 1)])]),
            (4, .split 2707657589237767474139138401 [
              (2, .round 1 [(2732491, 1), (4015513, 1)])]),
            (6, .round 1 [(14737, 1), (108421, 1), (845041, 1), (887143, 1), (1926611, 1), (4015513, 1), (5567751651967, 1), (32993235595486433, 1)]),
            (10, .abundant [(3, 4), (7, 2), (11, 2), (13, 2)])]),
          (4, .abundant [(3, 2), (7, 2), (11, 2), (13, 2), (31, 2)]),
          (6, .split 33425173 [
            (2, .split 575709019 [
              (2, .round 1 [(646879, 1), (666019, 1), (4015513, 1), (9034453, 1)])]),
            (4, .round 1 [(2707657589237767474139138401, 1)])]),
          (10, .round 1 [(33425173, 1)])]),
        (2, .split 258316859700878821 [
          (1, .split 129158429850439411 [
            (2, .split 794376190544327543871250458688873 []),
            (4, .abundant [(3, 4), (5, 2), (7, 2)])]),
          (2, .split 465891236282611963 [
            (2, .round 292717313533 [(947239753, 1), (292717313533, 1), (72351548014980190015557764637775111, 1)])]),
          (4, .abundant [(3, 4), (5, 1), (7, 2)])]),
        (4, .split 1888399622712722283356441 [
          (1, .split 3691810561801213 [
            (2, .round 1 [(18198601, 1), (85251739, 1), (947239753, 1), (174584317091, 1)])]),
          (2, .round 1 [(4945982156812138509667871141363447556725297563, 1)])]),
        (6, .split 1096768712002926313862195776597306199108123009 [
          (1, .abundant [(3, 6), (5, 2), (7, 2)])])]),
      (4, .split 13050343269427265004626386141 [
        (1, .split 103737625617657751921 [
          (2, .round 1 [(348764834786503, 1), (3587164989596440625284097127907078980721, 1)])]),
        (2, .round 2505420882950293453666143785857 [(5419, 1), (27583, 1), (4015513, 1), (493616224077391, 1), (103737625617657751921, 1), (2505420882950293453666143785857, 1)])]),
      (6, .round 141483161 [(1231, 1), (5419, 1), (937049, 1), (2183063, 1), (4015513, 1), (141483161, 1), (34271696399635948697289219651778674636533566057881693599, 1)])]),
    (4, .split 68141055822477632778023162393161554769187099016961 [
      (1, .split 1149738429074614562932019 [
        (2, .round 1 [(866896609414818462553, 1), (1524862873997493314386400677, 1)])]),
      (2, .split 1231 [
        (2, .split 1051 [
          (2, .abundant [(3, 4), (5, 1), (13, 2), (37, 1), (127, 4)])])])]),
    (6, .split 941639820430438197714216879705853971799668206593563558454132592107 []),
    (10, .round 1 [(4140821200993783967, 1)])]

private theorem checked127_95 : replayAbundance bank 127 1 (10^300) 11 state127_95 tree127_95 = true := by
  decide +kernel

theorem reject127_95 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_95 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 11 h tree127_95 checked127_95

@[expose] noncomputable def state127_96 : State := ⟨1229722508798380965993906785681755860072961, 1239482215938717571143738930873578324947205, 0⟩

private noncomputable def tree127_96 : AbundanceTree :=
  .split 4440731591 [
    (2, .split 477869921 [
      (1, .abundant [(3, 4), (5, 2), (7, 2)]),
      (2, .split 14073559 [
        (2, .abundant [(3, 2), (5, 1), (7, 4)]),
        (4, .split 197102915665228520161 [
          (1, .split 98551457832614260081 [
            (2, .abundant [(3, 2), (5, 2), (7, 4)])]),
          (2, .abundant [(3, 2), (5, 1), (7, 4)])]),
        (6, .split 6579701 [
          (1, .abundant [(3, 2), (5, 2), (7, 4)]),
          (2, .split 883519833247 [
            (2, .abundant [(3, 2), (5, 1), (7, 6)])]),
          (4, .round 2468269 [(421, 1), (6199, 1), (14621, 1), (37501, 1), (75181, 1), (688453, 1), (2468269, 1), (17996831, 1), (32402584631, 1)]),
          (6, .round 2468269 [(6199, 1), (14621, 1), (75181, 1), (688453, 1), (2468269, 1)])]),
        (10, .round 6579701 [(31, 1), (37, 1), (79, 1), (89, 1), (421, 1), (6199, 1), (14621, 1), (75181, 1), (688453, 1), (2468269, 1), (6579701, 1)]),
        (12, .round 6579701 [(2468269, 1), (6579701, 1)])]),
      (4, .split 550849106399739158982391 [
        (2, .abundant [(3, 2), (5, 2), (7, 2)])]),
      (6, .split 6579701 [
        (1, .abundant [(3, 2), (5, 2), (7, 2)]),
        (2, .split 883519833247 [
          (2, .abundant [(3, 2), (5, 1), (7, 4)])]),
        (4, .split 32402584631 [
          (2, .round 1 [(17996831, 1), (177416611, 1), (304213471, 1)])]),
        (6, .round 2468269 [(29, 1), (31, 1), (79, 1), (421, 1), (6199, 1), (14621, 1), (42967, 1), (75181, 1), (2468269, 1)])]),
      (10, .round 36635458309076176921649139249926118446272625716270376530382325392129725625129007661 [(79, 1), (421, 1), (6199, 1), (14621, 1), (75181, 1), (2468269, 1), (6579701, 1), (36635458309076176921649139249926118446272625716270376530382325392129725625129007661, 1)])]),
    (4, .split 67925926254055524975061780331 [
      (2, .split 22997058678794290833044141354201238337 [
        (1, .round 1 [(54495399712782679699156733066827579, 1)])])]),
    (6, .split 2608856049206359191163303 [
      (2, .round 18035954329 [(3, 1), (5, 1), (11, 1), (29, 1), (421, 1), (547, 1), (1531, 1), (14621, 1), (20749, 1), (6579701, 1), (477869921, 1), (723397193, 1), (18035954329, 1)])]),
    (10, .split 518332453 [
      (1, .round 1 [(251483, 1), (302411, 1), (6579701, 1), (36565673, 1), (477869921, 1)]),
      (2, .abundant [(3, 2), (5, 1), (7, 2)])]),
    (12, .round 477869921 [(6579701, 1), (477869921, 1)])]

private theorem checked127_96 : replayAbundance bank 127 1 (10^300) 8 state127_96 tree127_96 = true := by
  decide +kernel

theorem reject127_96 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_96 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree127_96 checked127_96

@[expose] noncomputable def state127_97 : State := ⟨84547981113537465407900918941700376829169566647871999211521, 85218997159085124521747089051531206491722088931366890890247, 0⟩

private noncomputable def tree127_97 : AbundanceTree :=
  .split 2345859770241123348845770103 [
    (2, .split 269913320447578842973414950122681611 [
      (2, .round 1 [(4360138339, 1)])])]

private theorem checked127_97 : replayAbundance bank 127 1 (10^300) 5 state127_97 tree127_97 = true := by
  decide +kernel

theorem reject127_97 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_97 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree127_97 checked127_97

@[expose] noncomputable def state127_98 : State := ⟨399664413801156963089728953505309268585243415467973907913055937073372321036168124695485117441, 402836355117352809836576686076631043449595407201664187835303908129108426792248047221444820491, 0⟩

private noncomputable def tree127_98 : AbundanceTree :=
  .split 6865379200955135391524384965083073728767674853 [
    (1, .round 1 [(947, 1), (4481, 1), (153342821665045555262919920768081, 1), (956372488104878858958714149864983227667, 1)])]

private theorem checked127_98 : replayAbundance bank 127 1 (10^300) 4 state127_98 tree127_98 = true := by
  decide +kernel

theorem reject127_98 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_98 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree127_98 checked127_98

@[expose] noncomputable def state127_99 : State := ⟨27478410021812011684228714672546896392520283961513370287567232242068329848539132206447811097014091103668236801, 27696492745821860030139698252802549177588649601893654784737757848510635710140640225218591591759320537182414093, 0⟩

private noncomputable def tree127_99 : AbundanceTree :=
  .round 1 [(4593499, 1), (1447553814182867, 1), (593087897109832382475448398803149004845356606680283725024270560517684419, 1)]

private theorem checked127_99 : replayAbundance bank 127 1 (10^300) 3 state127_99 tree127_99 = true := by
  decide +kernel

theorem reject127_99 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_99 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_99 checked127_99

@[expose] noncomputable def state127_100 : State := ⟨129892428996118514123248697520588510396091389198465156254418855981880708943257950651187354073613467722303471420226434178407372106694782234488321, 130923321785084232700149428542005996954392086584730271950599544602860387419247425368814446688441549009333894263552584660329159794594146717034257, 0⟩

private noncomputable def tree127_100 : AbundanceTree :=
  .split 17342847747419 []

private theorem checked127_100 : replayAbundance bank 127 1 (10^300) 3 state127_100 tree127_100 = true := by
  decide +kernel

theorem reject127_100 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_100 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_100 checked127_100

@[expose] noncomputable def state127_101 : State := ⟨260144641, 262209281, 0⟩

private theorem checked127_101 : checkChildren bank 127 1 (10^300) state127_101 262209281 [state127_94, state127_95, state127_96, state127_97, state127_98, state127_99, state127_100] = true := by
  decide +kernel

theorem reject127_101 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_101 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state127_94, state127_95, state127_96, state127_97, state127_98, state127_99, state127_100] ?_ checked127_101
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject127_94 ho hN hs hav hx hvalid
  · exact reject127_95 ho hN hs hav hx hvalid
  · exact reject127_96 ho hN hs hav hx hvalid
  · exact reject127_97 ho hN hs hav hx hvalid
  · exact reject127_98 ho hN hs hav hx hvalid
  · exact reject127_99 ho hN hs hav hx hvalid
  · exact reject127_100 ho hN hs hav hx hvalid

@[expose] noncomputable def state127_102 : State := ⟨5090831958032076099121533109, 5131326345219109398085338210, 162709⟩

private noncomputable def tree127_102 : AbundanceTree :=
  .abundant [(3, 2), (5, 2), (7, 2)]

private theorem checked127_102 : replayAbundance bank 127 1 (10^300) 3 state127_102 tree127_102 = true := by
  decide +kernel

theorem reject127_102 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 127 ∣ N)
    (hav : Nat.Coprime 1 N) (hx : N ≤ 10^300) (h : Valid state127_102 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree127_102 checked127_102

end OddPerfect.IndexComponent.Size300
