module

public import OddPerfect.SizeIndex300.Seed19Part01

public section

namespace OddPerfect.IndexComponent.Size300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def state19_56 : State := ⟨464606643223203729329, 490466585976355274754, 70841⟩

private theorem checked19_56 : checkChildren bank 19 127 (10^300) state19_56 2017 [state19_44, state19_45, state19_46, state19_47, state19_48, state19_49, state19_50, state19_51, state19_52, state19_53, state19_54, state19_55] = true := by
  decide +kernel

theorem reject19_56 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_56 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state19_44, state19_45, state19_46, state19_47, state19_48, state19_49, state19_50, state19_51, state19_52, state19_53, state19_54, state19_55] ?_ checked19_56
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject19_44 ho hN hs hav hx hvalid
  · exact reject19_45 ho hN hs hav hx hvalid
  · exact reject19_46 ho hN hs hav hx hvalid
  · exact reject19_47 ho hN hs hav hx hvalid
  · exact reject19_48 ho hN hs hav hx hvalid
  · exact reject19_49 ho hN hs hav hx hvalid
  · exact reject19_50 ho hN hs hav hx hvalid
  · exact reject19_51 ho hN hs hav hx hvalid
  · exact reject19_52 ho hN hs hav hx hvalid
  · exact reject19_53 ho hN hs hav hx hvalid
  · exact reject19_54 ho hN hs hav hx hvalid
  · exact reject19_55 ho hN hs hav hx hvalid

@[expose] noncomputable def state19_57 : State := ⟨64768604785584878464837847921, 68373616544255255511595971522, 70841⟩

private noncomputable def tree19_57 : AbundanceTree :=
  .split 280257881 [
    (2, .split 596514349 [
      (2, .abundant [(3, 2), (7, 2), (11, 2), (19, 6), (31, 2)]),
      (4, .split 319854035341896419960919632951 [
        (2, .round 1 [(61, 1), (181, 1), (409, 1), (571, 1), (701, 1), (49549, 1), (98779, 1), (395851, 1), (257057869, 1), (710955781, 1), (642397020588227167280642461914079, 1)])]),
      (6, .split 45053171728033434141365744307266184678000360677634451 []),
      (10, .round 1 [(701, 1), (65033, 1), (98779, 1), (1631059, 1), (106608324854155984606237242150032611343213, 1)]),
      (12, .round 1 [(147288896259554653048339534170155737073204055434490859640563886368888452651719199716458668895512099521, 1)])]),
    (4, .abundant [(3, 2), (5, 2), (11, 2), (19, 6)]),
    (6, .abundant [(3, 2), (7, 2), (11, 2), (19, 6), (29, 2)]),
    (10, .round 1 [(61, 1), (181, 1), (571, 1), (701, 1), (129972210670960788621478188842492467460230683912546368216972096715362723243437714757, 1)]),
    (12, .round 1 [(838117896007137349517259370544309861801488999872938932803232282743330127, 1)])]

private theorem checked19_57 : replayAbundance bank 19 127 (10^300) 6 state19_57 tree19_57 = true := by
  decide +kernel

theorem reject19_57 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_57 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree19_57 checked19_57

@[expose] noncomputable def state19_58 : State := ⟨9029083477517051593025457934051137329, 9531641039382423414194199119472506754, 70841⟩

private noncomputable def tree19_58 : AbundanceTree :=
  .split 1807475964966137691443 [
    (2, .split 239826076678847259343 [
      (2, .split 6326341150922616224464390009 [
        (2, .round 1 [(8941, 1), (8454841, 1), (480960559, 1), (938710207, 1)])]),
      (4, .round 1 [(375511, 1), (400381, 1), (649751, 1), (8454841, 1), (938710207, 1)])]),
    (4, .round 1 [(701, 1), (1499, 1), (2281, 1), (184651, 1), (182074271, 1), (17285840628244303181230651, 1), (23611289773416034859924489088435186558811, 1)]),
    (6, .round 1 [(1499, 1)])]

private theorem checked19_58 : replayAbundance bank 19 127 (10^300) 6 state19_58 tree19_58 = true := by
  decide +kernel

theorem reject19_58 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_58 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree19_58 checked19_58

@[expose] noncomputable def state19_59 : State := ⟨175469614206110137872540197974707367647252679714545329, 185236229136237035179088064669274146059892357053738754, 70841⟩

private noncomputable def tree19_59 : AbundanceTree :=
  .split 190101462739418057644741 [
    (2, .split 53319233962462469854970452063 [
      (2, .round 1 [(3086797731100772306448748493711271174961111253708524873, 1)])]),
    (4, .abundant [(3, 2), (5, 2), (19, 6), (23, 2), (67, 2)])]

private theorem checked19_59 : replayAbundance bank 19 127 (10^300) 5 state19_59 tree19_59 = true := by
  decide +kernel

theorem reject19_59 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_59 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree19_59 checked19_59

@[expose] noncomputable def state19_60 : State := ⟨24461385260336721091545796561173376288999803981523440511031921, 25822902646558178812162531248148264980741662989813679433507522, 70841⟩

private noncomputable def tree19_60 : AbundanceTree :=
  .split 1546114155153779517885983 [
    (2, .split 29136536642507203532659 [
      (2, .split 420262176997681 [
        (2, .round 1 [(43780498807753, 1)])])]),
    (4, .round 1 [(1091, 1), (8831, 1), (90793, 1), (653641, 1)])]

private theorem checked19_60 : replayAbundance bank 19 127 (10^300) 6 state19_60 tree19_60 = true := by
  decide +kernel

theorem reject19_60 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_60 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree19_60 checked19_60

@[expose] noncomputable def state19_61 : State := ⟨475378242461288340901477330373932457078290555226238138558834857794020123623921, 501837730967522440509095384382221494224393342055737585626995695301997656275522, 70841⟩

private noncomputable def tree19_61 : AbundanceTree :=
  .split 352543136592931780159519873787602252895251257440951 [
    (2, .round 1 [(343965353, 1)])]

private theorem checked19_61 : replayAbundance bank 19 127 (10^300) 4 state19_61 tree19_61 = true := by
  decide +kernel

theorem reject19_61 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_61 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_61 checked19_61

@[expose] noncomputable def state19_62 : State := ⟨66270222259498274024167331708633317288180907345661979039090874500654966044803489361329, 69958813843122476732258128824554298575503615723222270002990156025503155010827608202754, 70841⟩

private noncomputable def tree19_62 : AbundanceTree :=
  .split 12755656264103554794811153642420149904161519647432859138990530954362823 []

private theorem checked19_62 : replayAbundance bank 19 127 (10^300) 3 state19_62 tree19_62 = true := by
  decide +kernel

theorem reject19_62 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_62 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_62 checked19_62

@[expose] noncomputable def state19_63 : State := ⟨1287883799300644371855757371199279923161297853674070539836813899373029147194512905223072333445600769329, 1359567236911349679824034387564362850940008822733815723427375994546120300168740455186715821916581434754, 70841⟩

private noncomputable def tree19_63 : AbundanceTree :=
  .split 1697474577624273168331956029356714648678408423967478930313 []

private theorem checked19_63 : replayAbundance bank 19 127 (10^300) 3 state19_63 tree19_63 = true := by
  decide +kernel

theorem reject19_63 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_63 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_63 checked19_63

@[expose] noncomputable def state19_64 : State := ⟨3489105163739443717378559811112653595451164482226595486051638150063936432080785167397640746475357984125292253996858542065399921, 3683308283972746742716162389011518386650718539858406808040754791077787256022743623812744589073364975914503105130720753540579522, 70841⟩

private noncomputable def tree19_64 : AbundanceTree :=
  .split 20402696773 [
    (2, .round 1 [(31, 1), (457, 1), (701, 1), (9281, 1), (1399194088311829, 1)])]

private theorem checked19_64 : replayAbundance bank 19 127 (10^300) 4 state19_64 tree19_64 = true := by
  decide +kernel

theorem reject19_64 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_64 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_64 checked19_64

@[expose] noncomputable def state19_65 : State := ⟨486399574138282922542643757729552441524614851984754618155304643167562424234393444376574790274943152141124413866203310274404050271585329, 513472508470983468882285554164585584559121694077877625818216623798141910794877324540777988813175123735240308082021304238332441919898754, 70841⟩

private noncomputable def tree19_65 : AbundanceTree :=
  .round 1 [(453578945704073255060439503299622412782317125815866187787849198937069695723869237369269, 1)]

private theorem checked19_65 : replayAbundance bank 19 127 (10^300) 3 state19_65 tree19_65 = true := by
  decide +kernel

theorem reject19_65 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_65 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_65 checked19_65

@[expose] noncomputable def state19_66 : State := ⟨3332777255921, 3517981203522, 70841⟩

private theorem checked19_66 : checkChildren bank 19 127 (10^300) state19_66 11807 [state19_56, state19_57, state19_58, state19_59, state19_60, state19_61, state19_62, state19_63, state19_64, state19_65] = true := by
  decide +kernel

theorem reject19_66 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_66 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state19_56, state19_57, state19_58, state19_59, state19_60, state19_61, state19_62, state19_63, state19_64, state19_65] ?_ checked19_66
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject19_56 ho hN hs hav hx hvalid
  · exact reject19_57 ho hN hs hav hx hvalid
  · exact reject19_58 ho hN hs hav hx hvalid
  · exact reject19_59 ho hN hs hav hx hvalid
  · exact reject19_60 ho hN hs hav hx hvalid
  · exact reject19_61 ho hN hs hav hx hvalid
  · exact reject19_62 ho hN hs hav hx hvalid
  · exact reject19_63 ho hN hs hav hx hvalid
  · exact reject19_64 ho hN hs hav hx hvalid
  · exact reject19_65 ho hN hs hav hx hvalid

@[expose] noncomputable def state19_67 : State := ⟨124776846382746211442126393367541, 131713831302059246287079149240578, 128341⟩

private noncomputable def tree19_67 : AbundanceTree :=
  .split 39103 [
    (2, .split 67411 [
      (2, .abundant [(3, 4), (7, 2), (13, 2), (19, 6), (79, 2)]),
      (4, .abundant [(3, 2), (5, 2), (7, 2)]),
      (6, .split 27277 [
        (2, .abundant [(3, 4), (7, 4), (13, 2), (19, 6), (71, 2)]),
        (4, .split 8918947233611 [
          (2, .abundant [(3, 2), (7, 4), (13, 2), (19, 6), (43, 2), (71, 2)]),
          (4, .abundant [(3, 2), (5, 2), (7, 4)]),
          (6, .round 1 [(42362353770389877187899271101754177324032608526730349, 1)])]),
        (6, .split 121349509999094498311 [
          (2, .abundant [(3, 4), (7, 4), (13, 2), (19, 6), (71, 2)])]),
        (10, .split 4589655430599728676532379 [
          (2, .round 1 [(1471133529570171633367870213603, 1)])]),
        (12, .split 884968348782172298523512989642578078956651 []),
        (16, .round 1 [(18693457687, 1), (224625253963538101, 1), (526376017872581956222386959, 1)]),
        (18, .round 1 [(181795253734611692015167058232443407812079, 1)])]),
      (10, .split 27277 [
        (2, .abundant [(3, 4), (7, 2), (13, 2), (19, 6), (67, 2)]),
        (4, .split 8918947233611 [
          (2, .abundant [(3, 2), (7, 4), (13, 2), (19, 6), (43, 2), (67, 2)]),
          (4, .abundant [(3, 2), (5, 2), (7, 2)])]),
        (6, .split 121349509999094498311 [
          (2, .abundant [(3, 4), (7, 2), (13, 2), (19, 6), (67, 2)])]),
        (10, .split 4589655430599728676532379 []),
        (12, .round 1 [(2426723729, 1), (884968348782172298523512989642578078956651, 1)]),
        (16, .round 1 [(526376017872581956222386959, 1)])]),
      (12, .split 553380199816018621947567695412291830484243594791355361 []),
      (16, .split 27277 [
        (2, .abundant [(3, 4), (7, 2), (13, 2), (19, 6), (79, 2)]),
        (4, .split 8918947233611 [
          (2, .round 1 [(62071, 1), (172676809976347, 1)])]),
        (6, .split 121349509999094498311 []),
        (10, .round 1 [(4589655430599728676532379, 1)])]),
      (18, .split 27277 [
        (2, .abundant [(3, 4), (7, 2), (13, 2), (19, 6), (79, 2)]),
        (4, .split 8918947233611 []),
        (6, .round 1 [(121349509999094498311, 1)])]),
      (22, .split 27277 [
        (2, .abundant [(3, 4), (7, 2), (13, 2), (19, 6), (79, 2)])])]),
    (4, .abundant [(3, 2), (7, 2), (11, 2), (13, 2), (19, 6)]),
    (6, .split 121012813720289 [
      (2, .split 1407376241059 [
        (2, .split 817018003 [
          (2, .abundant [(3, 4), (7, 4), (13, 4), (19, 6), (43, 2)]),
          (4, .round 1 [(670297, 1), (1733647, 1), (13004671, 1), (45058231, 1), (258785941, 1), (9888999811852866003635214191, 1)]),
          (6, .round 1 [(670297, 1), (1733647, 1), (13004671, 1), (258785941, 1)])]),
        (4, .split 817018003 [
          (2, .abundant [(3, 2), (7, 4), (13, 2), (19, 6), (43, 2), (67, 2)]),
          (4, .round 1 [(9888999811852866003635214191, 1)])])]),
      (4, .split 13004671 [
        (2, .split 2967043523209 []),
        (4, .abundant [(3, 2), (5, 2), (7, 4)]),
        (6, .split 27277 [
          (2, .round 1 [(4441, 1), (5119, 1), (7547, 1)])])]),
      (6, .abundant [(3, 2), (7, 4), (13, 2), (19, 6), (43, 2), (79, 2), (197, 2)])]),
    (10, .abundant [(3, 2), (7, 2), (13, 2), (19, 6), (23, 2)]),
    (12, .split 877334426527063012842694533180319245729116085571 [
      (2, .round 1 [(274847, 1)])]),
    (16, .split 34511 [
      (2, .split 4822039 [
        (2, .split 23415976777 [
          (2, .abundant [(3, 4), (7, 4), (13, 2), (19, 6), (79, 2)]),
          (4, .round 1 [(27277, 1)])]),
        (4, .split 27277 [
          (2, .split 5119 [
            (2, .abundant [(3, 4), (7, 4), (13, 4), (19, 6), (79, 2)]),
            (4, .abundant [(3, 2), (7, 2), (11, 2), (13, 4)])]),
          (4, .round 1 [(701, 1), (62071, 1), (8918947233611, 1)]),
          (6, .round 1 [(121349509999094498311, 1)])]),
        (6, .split 27277 [
          (2, .round 1 [(701, 1), (3727, 1), (5119, 1)])])]),
      (4, .abundant [(3, 2), (5, 2), (7, 2)]),
      (6, .split 27277 [
        (2, .split 5119 [
          (2, .abundant [(3, 4), (7, 4), (13, 2), (19, 6), (79, 2)]),
          (4, .abundant [(3, 2), (7, 4), (11, 2), (13, 2)]),
          (6, .round 1 [(1405482289, 1)])]),
        (4, .round 1 [(79, 1), (103, 1), (197, 1), (307, 1), (701, 1), (62071, 1), (8918947233611, 1)]),
        (6, .round 1 [(121349509999094498311, 1)])]),
      (10, .round 1 [(27366139512868075584678334572556999, 1)]),
      (12, .round 1 [(36130670207925603488253282309763898358848207860461967, 1)])]),
    (18, .split 27277 [
      (2, .split 5119 [
        (2, .abundant [(3, 4), (7, 4), (13, 2), (19, 6), (79, 2)]),
        (4, .abundant [(3, 2), (7, 2), (11, 2), (13, 2), (19, 6)]),
        (6, .split 1405482289 [
          (2, .abundant [(3, 4), (7, 2), (13, 4), (19, 6), (79, 2)])]),
        (10, .abundant [(3, 2), (7, 2), (13, 2), (19, 6), (23, 2)])]),
      (4, .split 8918947233611 [
        (2, .round 1 [(1741, 1), (62071, 1), (172676809976347, 1)])]),
      (6, .split 121349509999094498311 []),
      (10, .round 1 [(4589655430599728676532379, 1)])]),
    (22, .split 27277 [
      (2, .split 5119 [
        (2, .abundant [(3, 4), (7, 4), (13, 2), (19, 6), (79, 2)]),
        (4, .abundant [(3, 2), (7, 2), (11, 2), (13, 2), (19, 6)])]),
      (4, .round 1 [(139, 1), (701, 1), (62071, 1), (8918947233611, 1)]),
      (6, .round 1 [(121349509999094498311, 1)])])]

private theorem checked19_67 : replayAbundance bank 19 127 (10^300) 8 state19_67 tree19_67 = true := by
  decide +kernel

theorem reject19_67 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_67 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree19_67 checked19_67

@[expose] noncomputable def state19_68 : State := ⟨513820726997119109024963748949345133674381, 542386656796917301633499799749045022282730, 128341⟩

private noncomputable def tree19_68 : AbundanceTree :=
  .split 33579221106357041 [
    (2, .split 59345478426821800746377014559617 [
      (2, .abundant [(3, 2), (5, 2), (7, 2)])]),
    (4, .split 7383065400567475772932193100590063422106453615472619425193241 []),
    (6, .split 143352274829 [
      (2, .round 1 [(853837, 1), (134945578333, 1)])])]

private theorem checked19_68 : replayAbundance bank 19 127 (10^300) 5 state19_68 tree19_68 = true := by
  decide +kernel

theorem reject19_68 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_68 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree19_68 checked19_68

@[expose] noncomputable def state19_69 : State := ⟨2115871230484590936384456921198503961617183199902821, 2233503365312375592047788341101111306102939862825362, 128341⟩

private noncomputable def tree19_69 : AbundanceTree :=
  .split 7017607616783 [
    (2, .split 877730348497296141139 [
      (2, .split 112288378468617538885026141245334135601 []),
      (4, .round 1 [(7589, 1), (16091, 1), (39103, 1), (105337, 1), (429227, 1), (7616881, 1)])]),
    (4, .split 27606403754114712629388977399531 [
      (2, .round 1 [(7589, 1), (39103, 1), (105337, 1), (429227, 1), (1220411, 1), (3666121, 1)])]),
    (6, .round 1 [(39103, 1), (105337, 1), (429227, 1), (22010861183683, 1), (1542114541984432614958230365243821648687170241, 1)])]

private theorem checked19_69 : replayAbundance bank 19 127 (10^300) 5 state19_69 tree19_69 = true := by
  decide +kernel

theorem reject19_69 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_69 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree19_69 checked19_69

@[expose] noncomputable def state19_70 : State := ⟨35879341350395208503358871711133390064868211722268624544966642363820501, 37874057975137620993075227198156656790642651593239674973689684471960866, 128341⟩

private noncomputable def tree19_70 : AbundanceTree :=
  .split 45672782274591962977167539 [
    (2, .split 109789633721172726495643902619680352783757802762319 [])]

private theorem checked19_70 : replayAbundance bank 19 127 (10^300) 4 state19_70 tree19_70 = true := by
  decide +kernel

theorem reject19_70 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_70 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_70 checked19_70

@[expose] noncomputable def state19_71 : State := ⟨147748158342516651259771304229583358598898917443968272647073916359857435697157741, 155962236322452758835108019689281420417107102465757778671937444406497287997968138, 128341⟩

private noncomputable def tree19_71 : AbundanceTree :=
  .split 91973239755129316333429234761782941 [
    (2, .round 1 [(59265571, 1), (168873373403798311, 1), (113006934901830598686638027127937, 1)])]

private theorem checked19_71 : replayAbundance bank 19 127 (10^300) 4 state19_71 tree19_71 = true := by
  decide +kernel

theorem reject19_71 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_71 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_71 checked19_71

@[expose] noncomputable def state19_72 : State := ⟨2505401335718006666145916536937552631172146907906756073919023265353386237256223690880439528897309021, 2644689447146883447086034756378027992432540971792873052665544575573544909596876834656044151442877722, 128341⟩

private noncomputable def tree19_72 : AbundanceTree :=
  .split 4705611764574585791723551736089 [
    (2, .split 39103 [
      (2, .round 1 [(701, 1), (7561, 1), (67411, 1)])])]

private theorem checked19_72 : replayAbundance bank 19 127 (10^300) 5 state19_72 tree19_72 = true := by
  decide +kernel

theorem reject19_72 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_72 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree19_72 checked19_72

@[expose] noncomputable def state19_73 : State := ⟨10317035355977608764675200729202161320248697791054070057172616342278827144129520071229216405704146536080731061, 10890612271496909606173093733614316183618577997184766624495747014408328046716765479236174987419400854897882434, 128341⟩

private noncomputable def tree19_73 : AbundanceTree :=
  .split 13769463149220753216723577478298988256791 []

private theorem checked19_73 : replayAbundance bank 19 127 (10^300) 3 state19_73 tree19_73 = true := by
  decide +kernel

theorem reject19_73 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_73 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_73 checked19_73

@[expose] noncomputable def state19_74 : State := ⟨174948469419114094817496903351995003876768425222938536610163980808214083752724362178978044228445616297508873895142655222779387941, 184674752212755804948069386912362960894471204392748967317678086948475539258565995749512938584957614955121883532886243018479327698, 128341⟩

private noncomputable def tree19_74 : AbundanceTree :=
  .split 173743 [
    (2, .split 39103 [
      (2, .split 67411 [
        (2, .round 1 [(1741, 1), (7561, 1), (1514770111, 1)])]),
      (4, .round 1 [(57344741, 1), (3706509671, 1)])]),
    (4, .round 1 [(39103, 1), (82839807132821922691, 1)]),
    (6, .round 1 [(39103, 1)])]

private theorem checked19_74 : replayAbundance bank 19 127 (10^300) 6 state19_74 tree19_74 = true := by
  decide +kernel

theorem reject19_74 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_74 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree19_74 checked19_74

@[expose] noncomputable def state19_75 : State := ⟨12216392845228226928285448853375308919373315041918213031346207693743928412150251973091424334282573733962917397412431252677077268404240158670577352846928265261, 12895564786117063546497014300979328875076994603412463593743121818776085008132320441093671362154690925447693013459118606395718042101992369983161148213721893194, 128341⟩

private noncomputable def tree19_75 : AbundanceTree :=
  .round 1 [(39103, 1)]

private theorem checked19_75 : replayAbundance bank 19 127 (10^300) 3 state19_75 tree19_75 = true := by
  decide +kernel

theorem reject19_75 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_75 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_75 checked19_75

@[expose] noncomputable def state19_76 : State := ⟨30300960189390608358301, 31985047549329297151706, 128341⟩

private theorem checked19_76 : checkChildren bank 19 127 (10^300) state19_76 64171 [state19_67, state19_68, state19_69, state19_70, state19_71, state19_72, state19_73, state19_74, state19_75] = true := by
  decide +kernel

theorem reject19_76 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_76 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state19_67, state19_68, state19_69, state19_70, state19_71, state19_72, state19_73, state19_74, state19_75] ?_ checked19_76
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject19_67 ho hN hs hav hx hvalid
  · exact reject19_68 ho hN hs hav hx hvalid
  · exact reject19_69 ho hN hs hav hx hvalid
  · exact reject19_70 ho hN hs hav hx hvalid
  · exact reject19_71 ho hN hs hav hx hvalid
  · exact reject19_72 ho hN hs hav hx hvalid
  · exact reject19_73 ho hN hs hav hx hvalid
  · exact reject19_74 ho hN hs hav hx hvalid
  · exact reject19_75 ho hN hs hav hx hvalid

@[expose] noncomputable def state19_77 : State := ⟨3888855531666580067312708641, 4104992987777688632235461289, 0⟩

private noncomputable def tree19_77 : AbundanceTree :=
  .split 5490513541 [
    (1, .split 2745256771 [
      (2, .split 68659639549 [
        (2, .split 3133157107 [
          (2, .split 5927871379 [
            (2, .split 52852004066809 [
              (2, .split 127667386809148129 [
                (2, .round 1 [(552006661, 1), (7293259993, 1), (5991538509580918739491, 1)])]),
              (4, .round 1 [(3491, 1), (10111, 1), (39103, 1), (221623, 1), (7086103, 1), (552006661, 1)])]),
            (4, .split 1857452689266357897063071 [
              (2, .round 1 [(7086103, 1), (552006661, 1)])]),
            (6, .round 1 [(54195680769082441770899127173, 1), (800622803253666012651085842257, 1)])]),
          (4, .abundant [(3, 4), (7, 2), (11, 2), (19, 6)]),
          (6, .round 1 [(157, 1), (241, 1), (701, 1), (967, 1), (10111, 1), (39103, 1), (7086103, 1), (35595178037371, 1), (916439642411793208145115058726184189900123, 1)]),
          (10, .round 1 [(7086103, 1)])]),
        (4, .split 17122617603104335390299006901 []),
        (10, .round 1 [(967, 1), (5171, 1), (39103, 1)])]),
      (4, .abundant [(3, 2), (5, 2), (11, 2), (19, 6)]),
      (6, .split 54743819808326539187333 [
        (2, .split 171054751070533961653023553 [])]),
      (10, .split 232814414999 [
        (2, .split 6262743919971841 [])]),
      (12, .round 1 [(233801765289458094897451789799188342687083748952237658115157781600991586400921572644427, 1)])]),
    (2, .split 1435511378542612963 [
      (2, .split 56782082406079903 [
        (2, .split 126975359699835793 [
          (1, .split 107136718849 [
            (2, .split 2685198483619 [
              (2, .round 1 [(33136801, 1), (64124773, 1), (141437827, 1), (3189353977226971, 1)])]),
            (4, .round 1 [(199, 1), (397, 1), (701, 1), (39103, 1), (64124773, 1), (141437827, 1)])]),
          (2, .abundant [(3, 6), (7, 4), (13, 1), (19, 6), (181, 1), (199, 2)]),
          (4, .abundant [(3, 4), (7, 4), (11, 2), (19, 6)])]),
        (4, .abundant [(3, 4), (7, 4), (11, 2), (19, 6)])]),
      (4, .split 1561195444634042088697554799320312080678946229621044036491 []),
      (6, .split 15884363386091243 [])]),
    (4, .split 1053652258497518268871 [
      (2, .abundant [(3, 2), (5, 1), (7, 2)]),
      (4, .round 1 [(99050698428155838565346333372651506987329311, 1)])]),
    (6, .split 90040246158974357316584918623066359649537 [
      (1, .split 902432211596656089315877927061 [
        (2, .round 1 [(814383896527231869131880879166129254176662569751670314024783, 1)])]),
      (2, .split 2250137643177545519352555700705792240511315864350676648459995802880047665785169 [])]),
    (10, .round 1 [(87159826556284461329412347433428697278867573176552783269981500618746640945911, 1)]),
    (12, .split 124861049 [
      (1, .split 1363259 [
        (2, .abundant [(3, 4), (5, 2), (7, 2)])]),
      (2, .round 1 [(39103, 1), (1363259, 1)])])]

private theorem checked19_77 : replayAbundance bank 19 127 (10^300) 10 state19_77 tree19_77 = true := by
  decide +kernel

theorem reject19_77 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_77 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 10 h tree19_77 checked19_77

@[expose] noncomputable def state19_78 : State := ⟨64054942763327691318004355776742220121, 67615031912300335419844818888631841915, 0⟩

private noncomputable def tree19_78 : AbundanceTree :=
  .split 12833941 [
    (1, .split 1058821 [
      (2, .abundant [(3, 2), (5, 2), (11, 4), (19, 6)]),
      (4, .split 38160408950501 [
        (2, .split 471161 [
          (2, .split 39103 [
            (2, .abundant [(3, 2), (5, 2), (11, 4), (19, 6)]),
            (4, .split 3706509671 [
              (2, .split 4642673454589 [
                (2, .abundant [(3, 2), (5, 2), (7, 2)])]),
              (4, .round 1 [(57344741, 1), (1670214331, 1), (195924904331007941, 1)])]),
            (6, .split 121012813720289 [
              (2, .round 1 [(7547, 1), (670297, 1), (13004671, 1), (817018003, 1), (1407376241059, 1)])]),
            (10, .split 5659 [
              (2, .abundant [(3, 2), (5, 2), (11, 4), (19, 6)]),
              (4, .round 1 [(3259, 1), (4801, 1), (30300731, 1)])]),
            (12, .round 1 [(877334426527063012842694533180319245729116085571, 1)])]),
          (4, .split 295127290051981 [
            (2, .abundant [(3, 2), (5, 4), (7, 2)]),
            (4, .round 1 [(39103, 1)])]),
          (6, .split 39103 [
            (2, .abundant [(3, 2), (5, 2), (11, 4), (19, 6)]),
            (4, .split 3706509671 [
              (2, .round 1 [(3259, 1), (57344741, 1), (4642673454589, 1)])]),
            (6, .round 1 [(2017, 1), (3259, 1), (7547, 1), (13004671, 1), (121012813720289, 1)])]),
          (10, .round 1 [(5789201388813725928081754950461682939389717971051093, 1)]),
          (12, .round 1 [(179, 1), (541, 1), (701, 1), (3259, 1), (39103, 1)])]),
        (4, .split 471161 [
          (2, .split 39103 [
            (2, .abundant [(3, 2), (5, 4), (11, 4), (19, 6)]),
            (4, .round 1 [(179, 1), (487, 1), (541, 1), (701, 1), (739, 1), (3259, 1), (5659, 1), (21061, 1), (57344741, 1), (3706509671, 1)]),
            (6, .round 1 [(21061, 1), (13004671, 1), (121012813720289, 1)])]),
          (4, .split 295127290051981 [
            (2, .abundant [(3, 2), (5, 4), (7, 2)])]),
          (6, .split 39103 [
            (2, .abundant [(3, 2), (5, 4), (11, 4), (19, 6)])])]),
        (6, .split 471161 [
          (2, .round 1 [(541, 1), (701, 1), (739, 1), (3259, 1), (5659, 1), (39103, 1)])])]),
      (6, .split 201297159962369701073783342415458461 [
        (2, .abundant [(3, 2), (5, 2), (7, 2)])]),
      (10, .split 112739818910406031721670884578906123322097049590443218979 []),
      (12, .round 1 [(61, 1), (179, 1), (541, 1), (701, 1), (3259, 1), (27847, 1), (39103, 1), (71300495875015113140464746764669763517377188589020620018920284886259, 1)]),
      (16, .split 39103 [
        (2, .abundant [(3, 2), (5, 2), (11, 4), (19, 6)]),
        (4, .round 1 [(3706509671, 1)])]),
      (18, .round 1 [(61, 1), (179, 1), (541, 1), (701, 1), (3259, 1), (39103, 1)])]),
    (2, .abundant [(3, 2), (5, 1), (11, 2), (13, 1)]),
    (4, .split 108338860041712068491 [
      (2, .split 1676758370733953699851708005405655297939 [
        (2, .abundant [(3, 2), (5, 2), (7, 2)])]),
      (4, .round 63775539770303645654075312606109783509341 [(102001, 1), (1058821, 1), (8515321, 1), (187215837026251747885188892751, 1), (63775539770303645654075312606109783509341, 1)])]),
    (6, .split 343632680481721 [
      (1, .split 2521087073569 [
        (2, .abundant [(3, 2), (5, 2), (7, 2)]),
        (4, .round 1 [(754451, 1), (1058821, 1), (333861247832731961503629158161923897180522538541, 1)]),
        (6, .round 1 [(1058821, 1)])]),
      (2, .abundant [(3, 2), (5, 1), (7, 2)]),
      (4, .round 533946024525561895721 [(39103, 1), (1058821, 1), (2521087073569, 1), (294211030224641, 1), (533946024525561895721, 1), (1613833928517310528571, 1)])]),
    (10, .split 1809362626344622614704298487540261001958948518369343217015529067795533 [
      (1, .abundant [(3, 4), (5, 2), (11, 2)])]),
    (12, .round 1058821 [(541, 1), (701, 1), (39103, 1), (399647, 1), (1058821, 1), (14794651, 1), (4254105860607520571447, 1), (63944320293455736741868122811, 1)]),
    (16, .round 1058821 [(701, 1), (1361, 1), (15607, 1), (39103, 1), (1058821, 1)])]

private theorem checked19_78 : replayAbundance bank 19 127 (10^300) 10 state19_78 tree19_78 = true := by
  decide +kernel

theorem reject19_78 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_78 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 10 h tree19_78 checked19_78

@[expose] noncomputable def state19_79 : State := ⟨1055075370890627811202754022152525098672244706001, 1113715067020470659794851272941478841535678709821, 0⟩

private noncomputable def tree19_79 : AbundanceTree :=
  .split 3957838446627983 [
    (2, .split 38934969278521 [
      (1, .split 19467484639261 [
        (2, .split 76682225834119 [
          (2, .split 7935443669196901548623941 []),
          (4, .round 1 [(151677497137, 1), (4454269239481, 1)])]),
        (4, .split 4454269239481 [
          (2, .abundant [(3, 2), (5, 2), (13, 2), (19, 6)])]),
        (6, .round 1 [(4454269239481, 1)])]),
      (2, .split 20343393309397 [
        (1, .split 4454269239481 [
          (2, .round 1 [(13, 1), (29, 1), (43, 1), (103, 1), (163, 1), (701, 1), (1381, 1), (5011, 1), (39103, 1), (307873, 1), (47206363, 1), (80679541, 1), (151677497137, 1), (26775323154913765719823, 1)]),
          (4, .abundant [(3, 2), (5, 2), (19, 6), (29, 2), (43, 2)])]),
        (2, .split 19707316730516141293419667 [
          (2, .abundant [(3, 4), (7, 2), (13, 1), (19, 6), (29, 1)])]),
        (4, .round 1 [(19414490044065495254374573533441787771624348151, 1)])]),
      (4, .split 4454269239481 [
        (1, .split 151677497137 [
          (2, .round 1 [(1381, 1), (2011, 1), (3061, 1), (39103, 1), (737873, 1), (3018317, 1)])]),
        (2, .abundant [(3, 2), (5, 1), (13, 1), (19, 6), (29, 1)])]),
      (6, .round 4454269239481 [(2927, 1), (39103, 1), (151677497137, 1), (4454269239481, 1)])]),
    (4, .split 24547641483321526177159987273613081 [
      (1, .abundant [(3, 4), (7, 2), (11, 2), (19, 6)]),
      (2, .round 1 [(22163887550817200253654851, 1)])])]

private theorem checked19_79 : replayAbundance bank 19 127 (10^300) 7 state19_79 tree19_79 = true := by
  decide +kernel

theorem reject19_79 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_79 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree19_79 checked19_79

@[expose] noncomputable def state19_80 : State := ⟨286249779451934965287855733412368266203746290085558037228726972088961, 302159164266904780357854322202545967322539426912428150028661391453073, 0⟩

private noncomputable def tree19_80 : AbundanceTree :=
  .split 30908111996862789061026989478061704758093309893 [
    (1, .split 142967427661194991 [
      (2, .round 1 [(3, 1), (23, 1), (53, 1), (701, 1), (787, 1), (31051, 1), (39103, 1), (39227, 1), (224317, 1), (23083783, 1), (35703589963, 1), (16176671303467, 1), (8266736264028679, 1)]),
      (4, .round 1 [(16176671303467, 1)])]),
    (2, .round 13818703441 [(701, 1), (9733, 1), (39103, 1), (39227, 1), (56441899, 1), (13818703441, 1), (460724037139, 1)])]

private theorem checked19_80 : replayAbundance bank 19 127 (10^300) 5 state19_80 tree19_80 = true := by
  decide +kernel

theorem reject19_80 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_80 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree19_80 checked19_80

@[expose] noncomputable def state19_81 : State := ⟨4714938132698143036455695627484744697243063890723449195147508654062056439930041, 4976988169122591761043969257535946615623500604552070941944188792720024344541219, 0⟩

private noncomputable def tree19_81 : AbundanceTree :=
  .split 214640238454835499563255504039 [
    (2, .round 1 [(359071851818193370015783391, 1), (172439727359826603994880069764875285250771, 1)])]

private theorem checked19_81 : replayAbundance bank 19 127 (10^300) 4 state19_81 tree19_81 = true := by
  decide +kernel

theorem reject19_81 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_81 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_81 checked19_81

@[expose] noncomputable def state19_82 : State := ⟨1279197712173939252076473333834641750120511826796367471657217760160194869034745852589798243015271401, 1350293832130326623742275780663748274007973057626535877773428992855471352047841136960571212830982551, 0⟩

private noncomputable def tree19_82 : AbundanceTree :=
  .split 1285176912984348749212222162725641090192120756270017840573379 []

private theorem checked19_82 : replayAbundance bank 19 127 (10^300) 3 state19_82 tree19_82 = true := by
  decide +kernel

theorem reject19_82 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_82 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_82 checked19_82

@[expose] noncomputable def state19_83 : State := ⟨21070192906128926204800377622092930946170331733899432058843616036993946293172099452061418435313963824979475681, 22241246409510014342849787472513725651987480513306843768644373248401072086164485002869387672846860097135260537, 0⟩

private noncomputable def tree19_83 : AbundanceTree :=
  .split 17248436354894858410930075517693 [
    (1, .round 1 [(44353590379237, 1), (541484157559328762821939961, 1), (1862495562111452164042656011, 1)])]

private theorem checked19_83 : replayAbundance bank 19 127 (10^300) 4 state19_83 tree19_83 = true := by
  decide +kernel

theorem reject19_83 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_83 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_83 checked19_83

@[expose] noncomputable def state19_84 : State := ⟨5716499729586006855006857643843370803436947627964233209915589956569732635348704963473862983054149392586839012294655971005186711441, 6034215237233850050830250368604136468853612566783322561960653321587051510542587222735934449220121455167309406088653208510414043149, 0⟩

private noncomputable def tree19_84 : AbundanceTree :=
  .split 153960714674185577520610506774325322207427089046534534693027836048511238032283917337697 []

private theorem checked19_84 : replayAbundance bank 19 127 (10^300) 3 state19_84 tree19_84 = true := by
  decide +kernel

theorem reject19_84 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_84 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_84 checked19_84

@[expose] noncomputable def state19_85 : State := ⟨236097273586699561, 249217306488361543, 0⟩

private theorem checked19_85 : checkChildren bank 19 127 (10^300) state19_85 128341 [state19_76, state19_77, state19_78, state19_79, state19_80, state19_81, state19_82, state19_83, state19_84] = true := by
  decide +kernel

theorem reject19_85 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_85 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state19_76, state19_77, state19_78, state19_79, state19_80, state19_81, state19_82, state19_83, state19_84] ?_ checked19_85
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject19_76 ho hN hs hav hx hvalid
  · exact reject19_77 ho hN hs hav hx hvalid
  · exact reject19_78 ho hN hs hav hx hvalid
  · exact reject19_79 ho hN hs hav hx hvalid
  · exact reject19_80 ho hN hs hav hx hvalid
  · exact reject19_81 ho hN hs hav hx hvalid
  · exact reject19_82 ho hN hs hav hx hvalid
  · exact reject19_83 ho hN hs hav hx hvalid
  · exact reject19_84 ho hN hs hav hx hvalid

@[expose] noncomputable def state19_86 : State := ⟨1184841720682685529664343641, 1250683914124665161594518105, 0⟩

private noncomputable def tree19_86 : AbundanceTree :=
  .split 1163018639068051 [
    (2, .split 28110903730899737033240809 [
      (1, .abundant [(3, 2), (5, 2), (19, 6), (43, 2), (61, 2), (71, 2), (131, 2)]),
      (2, .split 558084438947608033606711 [
        (2, .abundant [(3, 4), (5, 1), (19, 6), (37, 1), (43, 2), (61, 1)])]),
      (4, .split 624452245225531802049697454845415244231210841614453118233335006590876782422183657322321353993088229781 [])]),
    (4, .split 2526989019842017283015059353315938671 [
      (2, .round 49561513777377607582916647355821 [(2039459061440951452061, 1), (54793570689682138623829369, 1), (49561513777377607582916647355821, 1)])]),
    (6, .split 20276385188276232432000779343436361287895363664748433633164068318856801 [
      (1, .split 701 [
        (2, .round 1 [(463, 1), (492103, 1)])])])]

private theorem checked19_86 : replayAbundance bank 19 127 (10^300) 6 state19_86 tree19_86 = true := by
  decide +kernel

theorem reject19_86 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_86 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree19_86 checked19_86

@[expose] noncomputable def state19_87 : State := ⟨5946065711575384660122070187826090121, 6276491288229363375239438526523726027, 0⟩

private noncomputable def tree19_87 : AbundanceTree :=
  .split 98811777493935291929249 [
    (1, .abundant [(3, 2), (5, 4), (7, 2)]),
    (2, .split 89575847445054835606035553724366295887281039 [
      (2, .round 1 [(26709055260152757281874387159818964785556211761057739, 1)])]),
    (4, .round 1 [(1211899615033956827429653677327467379597163771478816509608214094097038376180211, 1)])]

private theorem checked19_87 : replayAbundance bank 19 127 (10^300) 5 state19_87 tree19_87 = true := by
  decide +kernel

theorem reject19_87 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_87 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree19_87 checked19_87

@[expose] noncomputable def state19_88 : State := ⟨149750553698745607295280173323393715629916154132483938281, 158072260094259143230035446458878627380506819664122323151, 0⟩

private noncomputable def tree19_88 : AbundanceTree :=
  .split 16085976346319087113900064804280632383 [
    (2, .abundant [(3, 2), (7, 2), (11, 2), (19, 6), (37, 2)])]

private theorem checked19_88 : replayAbundance bank 19 127 (10^300) 4 state19_88 tree19_88 = true := by
  decide +kernel

theorem reject19_88 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_88 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_88 checked19_88

@[expose] noncomputable def state19_89 : State := ⟨751515259037714386041692549947993925895439925964140933842456263961, 793277303871559601052160943815180525886716601545372009386520505953, 0⟩

private noncomputable def tree19_89 : AbundanceTree :=
  .split 10345788322745407432628729 [
    (1, .split 11891710715799318888079 [
      (2, .split 136538727326737803627866081161 [])]),
    (2, .split 63631190731905536767 [
      (2, .split 262349354591659 [])])]

private theorem checked19_89 : replayAbundance bank 19 127 (10^300) 5 state19_89 tree19_89 = true := by
  decide +kernel

theorem reject19_89 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_89 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree19_89 checked19_89

@[expose] noncomputable def state19_90 : State := ⟨18926771349813592622346288990390539392069804033636127513397256243939917578918682278521, 19978540644136311809261565939488317981232568504886070865169719539418061158159742224037, 0⟩

private noncomputable def tree19_90 : AbundanceTree :=
  .split 43735025361072370380426595117563610040954202688378153 [
    (1, .split 124798758143302088808354823309030120841 [])]

private theorem checked19_90 : replayAbundance bank 19 127 (10^300) 4 state19_90 tree19_90 = true := by
  decide +kernel

theorem reject19_90 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_90 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_90 checked19_90

@[expose] noncomputable def state19_91 : State := ⟨94983004218580723752455393824265637540256101014804056662977751670260552101288564000746597151401, 100261252973913862592556896206827359904179992441991737548084296626125141341458469331397356696919, 0⟩

private noncomputable def tree19_91 : AbundanceTree :=
  .split 5862583086383669779277913015596925602816779597239284613977 [
    (1, .round 1 [(2052890293, 1), (1610473313497, 1), (5659156943529101, 1), (6339943009721562811120106797, 1)])]

private theorem checked19_91 : replayAbundance bank 19 127 (10^300) 4 state19_91 tree19_91 = true := by
  decide +kernel

theorem reject19_91 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_91 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_91 checked19_91

@[expose] noncomputable def state19_92 : State := ⟨2392129210078007960649657531588332444492582183568158217102767957213385979935964307113085010591115377792406647588361, 2525060918540650193739934563791117749428406600954454978341212468300820481939038438744455247857321174690543099814363, 0⟩

private noncomputable def tree19_92 : AbundanceTree :=
  .split 204687535116921117846119509136894569549812455155694774917799411072169317483729774730409478257 []

private theorem checked19_92 : replayAbundance bank 19 127 (10^300) 3 state19_92 tree19_92 = true := by
  decide +kernel

theorem reject19_92 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_92 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_92 checked19_92

@[expose] noncomputable def state19_93 : State := ⟨302337997957839353088377211564270175294209369596553021416430231472762689087681778088658297252581820021309185562280226532100343164131717433051801, 319139058047900210329668736135362639072057675784862328431811007777034801163445038004710047393339171774831937150741293719370266619162977774831729, 0⟩

private noncomputable def tree19_93 : AbundanceTree :=
  .split 399096635432401608542709213838689320970341226898033111133793958374441217504279593849731817411052363248685854206164349087377 []

private theorem checked19_93 : replayAbundance bank 19 127 (10^300) 3 state19_93 tree19_93 = true := by
  decide +kernel

theorem reject19_93 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_93 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_93 checked19_93

@[expose] noncomputable def state19_94 : State := ⟨47045881, 49659541, 0⟩

private theorem checked19_94 : checkChildren bank 19 127 (10^300) state19_94 70841 [state19_66, state19_85, state19_86, state19_87, state19_88, state19_89, state19_90, state19_91, state19_92, state19_93] = true := by
  decide +kernel

theorem reject19_94 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_94 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state19_66, state19_85, state19_86, state19_87, state19_88, state19_89, state19_90, state19_91, state19_92, state19_93] ?_ checked19_94
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject19_66 ho hN hs hav hx hvalid
  · exact reject19_85 ho hN hs hav hx hvalid
  · exact reject19_86 ho hN hs hav hx hvalid
  · exact reject19_87 ho hN hs hav hx hvalid
  · exact reject19_88 ho hN hs hav hx hvalid
  · exact reject19_89 ho hN hs hav hx hvalid
  · exact reject19_90 ho hN hs hav hx hvalid
  · exact reject19_91 ho hN hs hav hx hvalid
  · exact reject19_92 ho hN hs hav hx hvalid
  · exact reject19_93 ho hN hs hav hx hvalid

@[expose] noncomputable def state19_95 : State := ⟨133678718657867681316123405200973893837069, 141107454602554518627202848921301485817578, 62060021⟩

private noncomputable def tree19_95 : AbundanceTree :=
  .abundant [(3, 4), (7, 2), (19, 10), (31, 2), (43, 2), (47, 2), (67, 2)]

private theorem checked19_95 : replayAbundance bank 19 127 (10^300) 3 state19_95 tree19_95 = true := by
  decide +kernel

theorem reject19_95 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_95 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_95 checked19_95

@[expose] noncomputable def state19_96 : State := ⟨4318831358810375590269513839697150174787944020690381, 4558835587429207888632566260863476732585037710546346, 62060021⟩

private noncomputable def tree19_96 : AbundanceTree :=
  .abundant [(3, 4), (7, 2), (11, 2), (19, 10)]

private theorem checked19_96 : replayAbundance bank 19 127 (10^300) 3 state19_96 tree19_96 = true := by
  decide +kernel

theorem reject19_96 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_96 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_96 checked19_96

@[expose] noncomputable def state19_97 : State := ⟨139530843002631451241617874696858483486029900258488692928854669, 147284790670689099389590698898941702995505703644399122405583978, 62060021⟩

private noncomputable def tree19_97 : AbundanceTree :=
  .split 2436545047787131898016233 [
    (2, .split 13840121 [
      (2, .abundant [(3, 4), (7, 2), (13, 2), (19, 10), (43, 2)]),
      (4, .abundant [(3, 4), (5, 2), (7, 2)]),
      (6, .abundant [(3, 4), (7, 2), (19, 10), (29, 2), (43, 2), (47, 2), (67, 2)])]),
    (4, .abundant [(3, 4), (7, 2), (11, 2), (19, 10)])]

private theorem checked19_97 : replayAbundance bank 19 127 (10^300) 5 state19_97 tree19_97 = true := by
  decide +kernel

theorem reject19_97 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_97 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree19_97 checked19_97

@[expose] noncomputable def state19_98 : State := ⟨145639158906458771107433327581781734365880930656646526457420116109855562172946912269, 153732555264418966820253937995863367286099589232821621916054256360607226024095910378, 62060021⟩

private noncomputable def tree19_98 : AbundanceTree :=
  .split 673 [
    (2, .split 151201 [
      (2, .split 8933917 [
        (2, .split 320083 [
          (2, .split 34151148991 [
            (2, .split 182955964171 [
              (2, .round 1 [(2163289, 1), (2124921121, 1), (217230976273, 1)])]),
            (4, .abundant [(3, 8), (5, 2), (7, 2)])]),
          (4, .abundant [(3, 6), (7, 2), (11, 2), (19, 10)]),
          (6, .round 1 [(109, 1), (439, 1), (661, 1), (853, 1), (10753, 1), (13679, 1), (189337, 1), (63799247, 1), (16371158815890691, 1)]),
          (10, .round 1 [(1737474188904574571323973, 1)])]),
        (4, .abundant [(3, 6), (7, 2), (11, 2), (19, 10)]),
        (6, .round 1 [(47, 1), (67, 1), (109, 1), (197, 1), (661, 1), (853, 1), (1429, 1), (52697, 1), (34274188585995312993828606751747, 1)])]),
      (4, .abundant [(3, 4), (5, 2), (7, 2)]),
      (6, .abundant [(3, 4), (7, 2), (19, 10), (29, 2), (43, 2), (47, 2), (67, 2)]),
      (10, .round 1 [(4372817884287224443197838610260477113578606863, 1)]),
      (12, .round 1 [(11489302824370776504884773, 1)])]),
    (4, .split 192811 [
      (2, .split 609757 [
        (2, .split 596899 [
          (2, .abundant [(3, 6), (7, 4), (19, 10), (31, 2), (43, 2), (47, 2), (67, 2)]),
          (4, .split 630133915661 [
            (2, .abundant [(3, 6), (7, 2), (13, 2), (19, 10), (43, 2)])]),
          (6, .round 1 [(2531, 1), (20323, 1), (8267393, 1), (50465659297530123886919, 1)])]),
        (4, .abundant [(3, 4), (7, 2), (11, 2), (19, 10)]),
        (6, .round 1 [(43, 1), (47, 1), (67, 1), (109, 1), (421, 1), (661, 1), (2531, 1), (20323, 1), (917141, 1), (8005847844291616347967786961, 1)]),
        (10, .abundant [(3, 4), (7, 2), (19, 10), (23, 2), (43, 2), (47, 2)])]),
      (4, .abundant [(3, 4), (5, 2), (7, 2)]),
      (6, .split 2992419337579673 [
        (2, .round 1 [(8954573491920771950428960366603, 1)])]),
      (10, .abundant [(3, 4), (7, 2), (19, 10), (23, 2), (43, 2), (47, 2)]),
      (12, .round 1 [(1301073676566448167206786457750427589549905276882964549926717, 1)])]),
    (6, .split 149854447 [
      (2, .split 1690099754311 [
        (2, .split 34610848633461703 [
          (2, .abundant [(3, 6), (7, 2), (19, 10), (43, 2), (47, 2), (61, 2), (67, 2), (103, 2)])]),
        (4, .abundant [(3, 4), (5, 2), (7, 2)])]),
      (4, .split 2307145143731 [
        (2, .round 1 [(1350760001, 1), (354932778402196909, 1)])]),
      (6, .round 1 [(88709167, 1), (362764543, 1), (185042019984940188192193, 1)])]),
    (10, .abundant [(3, 4), (7, 2), (19, 10), (23, 2), (43, 2), (47, 2)]),
    (12, .split 6908555180220756335677 [
      (2, .round 1 [(174738080895730792395069136612351669, 1)])]),
    (16, .split 10808131541058781762828515811979771 []),
    (18, .round 1 [(661, 1), (803372473647509302428002115170516353259089422238963, 1)]),
    (22, .round 1 [(4542626403850880777, 1), (2011472309968638229211, 1)])]

private theorem checked19_98 : replayAbundance bank 19 127 (10^300) 9 state19_98 tree19_98 = true := by
  decide +kernel

theorem reject19_98 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_98 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 9 h tree19_98 checked19_98

@[expose] noncomputable def state19_99 : State := ⟨4705243832908045231073352957045715196492783981640583461438997238958085317641264870163080575181, 4966721608435653141774357207674946510107862636739369132256575550934724378914632329645873893546, 62060021⟩

private noncomputable def tree19_99 : AbundanceTree :=
  .split 673 [
    (2, .split 151201 [
      (2, .split 8933917 [
        (2, .split 320083 [
          (2, .split 34151148991 [
            (2, .round 1 [(47, 1), (67, 1), (79, 1), (109, 1), (439, 1), (853, 1), (189337, 1), (2124921121, 1), (182955964171, 1)])]),
          (4, .abundant [(3, 6), (7, 2), (11, 2), (19, 10)]),
          (6, .round 1 [(189337, 1), (63799247, 1), (16371158815890691, 1)])]),
        (4, .abundant [(3, 6), (7, 2), (11, 2), (19, 10)]),
        (6, .abundant [(3, 6), (7, 2), (19, 10), (43, 2), (47, 2), (67, 2), (79, 2), (109, 2), (197, 2)])]),
      (4, .abundant [(3, 4), (5, 2), (7, 2)]),
      (6, .abundant [(3, 4), (7, 2), (19, 10), (29, 2), (43, 2), (47, 2), (67, 2)]),
      (10, .round 1 [(4372817884287224443197838610260477113578606863, 1)]),
      (12, .round 1 [(11489302824370776504884773, 1)])]),
    (4, .split 192811 [
      (2, .split 609757 [
        (2, .split 596899 [
          (2, .abundant [(3, 6), (7, 4), (19, 10), (31, 2), (43, 2), (47, 2), (67, 2)]),
          (4, .round 1 [(3, 5), (7, 1), (43, 1), (47, 1), (67, 1), (79, 1), (109, 1), (397, 1), (421, 1), (523, 1), (2531, 1), (20323, 1), (630133915661, 1)]),
          (6, .round 1 [(50465659297530123886919, 1)])]),
        (4, .abundant [(3, 4), (7, 2), (11, 2), (19, 10)]),
        (6, .round 1 [(917141, 1), (8005847844291616347967786961, 1)])]),
      (4, .abundant [(3, 4), (5, 2), (7, 2)]),
      (6, .split 2992419337579673 [
        (2, .round 1 [(8954573491920771950428960366603, 1)])]),
      (10, .abundant [(3, 4), (7, 2), (19, 10), (23, 2), (43, 2), (47, 2)])]),
    (6, .split 149854447 [
      (2, .abundant [(3, 4), (7, 2), (19, 10), (43, 2), (47, 2), (67, 2), (79, 2), (103, 2), (109, 2)]),
      (4, .abundant [(3, 4), (7, 2), (19, 10), (43, 2), (47, 2), (67, 2), (79, 2), (109, 2), (191, 2)]),
      (6, .round 1 [(185042019984940188192193, 1)])]),
    (10, .abundant [(3, 4), (7, 2), (19, 10), (23, 2), (43, 2), (47, 2)]),
    (12, .split 6908555180220756335677 [
      (2, .round 1 [(174738080895730792395069136612351669, 1)])]),
    (16, .round 1 [(243101, 1), (675071, 1), (10808131541058781762828515811979771, 1)]),
    (18, .round 1 [(803372473647509302428002115170516353259089422238963, 1)]),
    (22, .round 1 [(2011472309968638229211, 1)])]

private theorem checked19_99 : replayAbundance bank 19 127 (10^300) 8 state19_99 tree19_99 = true := by
  decide +kernel

theorem reject19_99 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_99 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 8 h tree19_99 checked19_99

@[expose] noncomputable def state19_100 : State := ⟨4911227793998250873763513964629777245587253569255236258810518698012403596738838667987574070153067686992307807957581, 5184152421135022756495900708432206497772963801679786560711420426246762107181927007394198216468341098535856607727146, 62060021⟩

private noncomputable def tree19_100 : AbundanceTree :=
  .round 1 [(67, 1), (103, 1), (109, 1), (673, 1), (3877, 1), (5441, 1), (546288981094405014938321037911675818236580327442713712514228872304704856331, 1)]

private theorem checked19_100 : replayAbundance bank 19 127 (10^300) 3 state19_100 tree19_100 = true := by
  decide +kernel

theorem reject19_100 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_100 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree19_100 checked19_100

@[expose] noncomputable def state19_101 : State := ⟨158669718111727175929569213348331085598422576736153156065895314801611253974813256492790371431268590776117902814371796796147469, 167487243070854588552154226017405234021477043969979807862675549621166475014928380411944823159035782146860972834327214684243178, 62060021⟩

private noncomputable def tree19_101 : AbundanceTree :=
  .split 2357 [
    (2, .abundant [(3, 4), (7, 2), (19, 10), (37, 2), (43, 2), (47, 2), (67, 2)]),
    (4, .abundant [(3, 4), (7, 2), (11, 2), (19, 10)]),
    (6, .round 1 [(7, 1), (47, 1), (67, 1), (109, 1), (281, 1), (673, 1), (2129, 1), (14196033517635929, 1)]),
    (10, .round 1 [(39385385020517637711809, 1)])]

private theorem checked19_101 : replayAbundance bank 19 127 (10^300) 4 state19_101 tree19_101 = true := by
  decide +kernel

theorem reject19_101 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_101 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_101 checked19_101

@[expose] noncomputable def state19_102 : State := ⟨165615886727503276023772508333992628324549469872365182283063627246851244869494265789231456169064637572897223015542331355063126802753921207059325069, 174819421165117223325792869985922041149440967459694035543620640377092312945457597002896644588292260418820075917346355253206590932352424840030249578, 62060021⟩

private noncomputable def tree19_102 : AbundanceTree :=
  .split 673 [
    (2, .split 151201 [
      (2, .round 1 [(8933917, 1)])]),
    (4, .round 1 [(2531, 1), (192811, 1)])]

private theorem checked19_102 : replayAbundance bank 19 127 (10^300) 5 state19_102 tree19_102 = true := by
  decide +kernel

theorem reject19_102 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_102 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree19_102 checked19_102

@[expose] noncomputable def state19_103 : State := ⟨4137693356688889550396920187981, 4367607163272624059787929032746, 62060021⟩

private theorem checked19_103 : checkChildren bank 19 127 (10^300) state19_103 179743 [state19_95, state19_96, state19_97, state19_98, state19_99, state19_100, state19_101, state19_102] = true := by
  decide +kernel

theorem reject19_103 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_103 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state19_95, state19_96, state19_97, state19_98, state19_99, state19_100, state19_101, state19_102] ?_ checked19_103
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject19_95 ho hN hs hav hx hvalid
  · exact reject19_96 ho hN hs hav hx hvalid
  · exact reject19_97 ho hN hs hav hx hvalid
  · exact reject19_98 ho hN hs hav hx hvalid
  · exact reject19_99 ho hN hs hav hx hvalid
  · exact reject19_100 ho hN hs hav hx hvalid
  · exact reject19_101 ho hN hs hav hx hvalid
  · exact reject19_102 ho hN hs hav hx hvalid

@[expose] noncomputable def state19_104 : State := ⟨44995457963663919104942476835564572655741, 47495661852064921214439029398366084858710, 62060021⟩

private noncomputable def tree19_104 : AbundanceTree :=
  .split 181345750520141 [
    (2, .abundant [(3, 2), (5, 2), (7, 2)]),
    (4, .abundant [(3, 2), (5, 2), (11, 2), (19, 10)]),
    (6, .abundant [(3, 2), (5, 2), (19, 10), (29, 2), (41, 2)])]

private theorem checked19_104 : replayAbundance bank 19 127 (10^300) 4 state19_104 tree19_104 = true := by
  decide +kernel

theorem reject19_104 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 19 ∣ N)
    (hav : Nat.Coprime 127 N) (hx : N ≤ 10^300) (h : Valid state19_104 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree19_104 checked19_104

end OddPerfect.IndexComponent.Size300
