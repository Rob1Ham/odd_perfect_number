module

public import OddPerfect.SizeIndex300.Seed3Part01

public section

namespace OddPerfect.IndexComponent.Size300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def state3_36 : State := ⟨36617224686027166686507654208332321703081294595578774154446776505122737474164425830693599527213129, 54925987923383134004097758335309457078728638135494469281412045674259933069517695592793927737318973, 0⟩

private noncomputable def tree3_36 : AbundanceTree :=
  .split 37513900517964857745873832181533 []

private theorem checked3_36 : replayAbundance bank 3 74877803 (10^300) 3 state3_36 tree3_36 = true := by
  decide +kernel

theorem reject3_36 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_36 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_36 checked3_36

@[expose] noncomputable def state3_37 : State := ⟨85015671585174062657061495967230989137122013482751398684549855872981504885627329769328031623696070375738291293607401460616449985769, 127523857715176509086112389093030985784513005291978717470059169257212382826797265636986729616075113425600751303094261243605056155963, 0⟩

private noncomputable def tree3_37 : AbundanceTree :=
  .split 550271635685454468899 []

private theorem checked3_37 : replayAbundance bank 3 74877803 (10^300) 3 state3_37 tree3_37 = true := by
  decide +kernel

theorem reject3_37 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_37 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_37 checked3_37

@[expose] noncomputable def state3_38 : State := ⟨387420489, 581130733, 0⟩

private theorem checked3_38 : checkChildren bank 3 74877803 (10^300) state3_38 363889 [state3_17, state3_33, state3_34, state3_35, state3_36, state3_37] = true := by
  decide +kernel

theorem reject3_38 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_38 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state3_17, state3_33, state3_34, state3_35, state3_36, state3_37] ?_ checked3_38
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject3_17 ho hN hs hav hx hvalid
  · exact reject3_33 ho hN hs hav hx hvalid
  · exact reject3_34 ho hN hs hav hx hvalid
  · exact reject3_35 ho hN hs hav hx hvalid
  · exact reject3_36 ho hN hs hav hx hvalid
  · exact reject3_37 ho hN hs hav hx hvalid

@[expose] noncomputable def state3_39 : State := ⟨31381059609, 47071589413, 0⟩

private noncomputable def tree3_39 : AbundanceTree :=
  .split 1001523179 [
    (2, .split 16443420968455561 [
      (1, .split 6578839 [
        (2, .split 1377020431 [
          (2, .split 39987067 [
            (4, .split 11967024851 [
              (2, .split 29965357699 [
                (4, .round 1 [(27031, 1), (53719, 1), (294247, 1), (709981, 1), (3701917, 1), (5505377, 1)])]),
              (4, .round 1 [(10477, 1), (27031, 1), (53719, 1), (294247, 1), (709981, 1), (5505377, 1), (6883571, 1), (20732854330327246265843829691, 1)]),
              (6, .round 1 [(27031, 1), (53719, 1), (294247, 1), (709981, 1), (5505377, 1)])]),
            (10, .round 1 [(98938128133287512521, 1), (600229740804722632086003222339942900047, 1)]),
            (12, .round 1 [(53719, 1), (294247, 1), (5505377, 1)])]),
          (4, .split 459205587830170903741 [
            (2, .split 883052524857912767084599404256447 []),
            (4, .round 1 [(405313411, 1)])]),
          (6, .split 37739778286868040700788332179475370591684041 []),
          (10, .round 1 [(47, 1), (61, 1), (227, 1), (397, 1), (10477, 1), (5505377, 1), (5489122519, 1), (288389032776263, 1)]),
          (12, .round 1 [(5505377, 1)])]),
        (10, .split 4291781120435989548176400752477438787720901695229962129583 []),
        (12, .round 1 [(62563099, 1), (105068592059321620374590733663233962595671030748270079636282316848006922339, 1)]),
        (16, .split 5505377 [])]),
      (2, .split 222480985260063443458219 [
        (2, .split 963679483334691401409591346561 [
          (2, .split 12324695712070413962149132119929881485488646554140791733 [])])]),
      (6, .split 199233900527411473995441244722968579880601584578702335152371614370609881 [
        (1, .round 1 [(99217850582830248547065607, 1)])])]),
    (4, .split 5056496574263951471 [
      (4, .split 111391001351022179008522138454295055950575820180161 [
        (1, .round 1 [(37501, 1), (1099298734488491, 1), (31299392497173527281, 1)])])]),
    (6, .split 972678647809046615985593294428943 [
      (2, .split 223441003826648731011397 [
        (1, .round 1 [(6050130041152489, 1), (2464419019796363687, 1), (10988965838620369927, 1), (182252042272959813223, 1)])])]),
    (10, .split 25528437114044074401130674498507857367195217 [
      (1, .round 1 [(187051793464801, 1), (439409519511359, 1), (3349309513781694358584449553727087033219, 1)])]),
    (12, .split 807813012557149 [
      (1, .split 91551857004271 [
        (2, .round 1 [(367792309, 1), (11738616277, 1)])])])]

private theorem checked3_39 : replayAbundance bank 3 74877803 (10^300) 10 state3_39 tree3_39 = true := by
  decide +kernel

theorem reject3_39 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_39 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 10 h tree3_39 checked3_39

@[expose] noncomputable def state3_40 : State := ⟨22876792454961, 34315188682441, 0⟩

private noncomputable def tree3_40 : AbundanceTree :=
  .split 20381027 [
    (4, .split 172545754771028210096747645881 [
      (1, .split 107331526897849 [
        (4, .split 4571623436397678892966894111 [
          (2, .round 1 [(248531574771551, 1)])]),
        (6, .round 1 [(59, 1), (617, 1), (28537, 1), (3329761, 1), (8599579, 1), (93469471, 1), (534239119, 1)])]),
      (4, .round 1 [(2940027031, 1), (10564674611, 1)])]),
    (6, .split 7190721950928797 [
      (1, .split 1158061627 [
        (4, .split 33849546552896078971 [
          (2, .round 1 [(1034879, 1), (367735663, 1), (478880543, 1), (176771523631, 1), (38897454303286936901887117, 1)])]),
        (6, .round 1 [(351023, 1), (837313, 1), (1034879, 1), (3511271, 1), (478880543, 1), (42887513411, 1), (552327686467108635431317436231991773, 1)]),
        (10, .round 1 [(478880543, 1)])]),
      (2, .split 258381756584713 [
        (2, .split 3408217147 [
          (2, .round 5738555624149 [(59, 1), (61, 1), (109, 1), (463, 1), (3557, 1), (28537, 1), (351023, 1), (674731, 1), (837313, 1), (19295839, 1), (170015941, 1), (186978817, 1), (320373271, 1), (478880543, 1), (5738555624149, 1)])])]),
      (4, .round 238465861 [(3557, 1), (5641, 1), (28537, 1), (351023, 1), (837313, 1), (7857781, 1), (238465861, 1), (478880543, 1), (18988763011, 1), (13320210099994714496864024274091471, 1)])]),
    (10, .split 2807849912914984403871286297334902334993724876898138933757 [
      (1, .round 1 [(59, 1), (673, 1), (28537, 1), (29482223, 1), (149391727, 1), (50540611901193618743003, 1), (13758373008567670793204508857647, 1)])]),
    (12, .split 704847552277661849298060724597152201677 []),
    (16, .round 1 [(246108135761943990164188661738499036408301251385768607117673154202778547, 1)]),
    (18, .round 1 [(79990016500027733254471047490588619566178305451377426908634996145666614562178152746698083, 1)])]

private theorem checked3_40 : replayAbundance bank 3 74877803 (10^300) 7 state3_40 tree3_40 = true := by
  decide +kernel

theorem reject3_40 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_40 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree3_40 checked3_40

@[expose] noncomputable def state3_41 : State := ⟨205891132094649, 308836698141973, 0⟩

private noncomputable def tree3_41 : AbundanceTree :=
  .split 4404047 [
    (4, .split 10654978292191 [
      (4, .split 11223161238600714411950128963557385268950335901 [
        (1, .abundant [(3, 30), (5, 2), (17, 2), (131, 2), (167, 2)])]),
      (6, .round 1 [(2770771, 1), (20609007000172100024081236134386936882121097608895960705878495204941921194007, 1)])]),
    (6, .split 1512757364755397741 [
      (1, .split 21392848667 [
        (2, .split 21293987317453 [
          (6, .round 1 [(268088311, 1)])])]),
      (2, .split 100777575268488582781 [
        (1, .split 50388787634244291391 [])]),
      (4, .split 8765716444041539021859890323032867141143304266621 [
        (1, .round 1 [(21392848667, 1), (159103504064765648611, 1)])])]),
    (10, .split 301611165423161143291264069569349889 [
      (1, .split 48873043253 [
        (4, .round 1 [(173977, 1), (900217, 1), (6266459, 1), (518386877, 1), (1065192899, 1)])])]),
    (12, .split 639918356281764655715372870672321746473013822504099 []),
    (16, .split 53981569322490647470007930577931563651187110915148203187401567944945124061 []),
    (18, .split 32615913256463 [])]

private theorem checked3_41 : replayAbundance bank 3 74877803 (10^300) 7 state3_41 tree3_41 = true := by
  decide +kernel

theorem reject3_41 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_41 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree3_41 checked3_41

@[expose] noncomputable def state3_42 : State := ⟨150094635296999121, 225141952945498681, 0⟩

private noncomputable def tree3_42 : AbundanceTree :=
  .split 17189128703 [
    (4, .split 120422267411267440976637389628164071 [
      (2, .split 4833840829490268113510548333147842703698650330426092900442909241152371 [])]),
    (6, .split 32782724856476414222948063085617 [
      (1, .split 3729028273377384104094212939 [])]),
    (10, .split 66163334257012730378508537760704662266671664609573541447323022441211497 [
      (1, .round 1 [(74906490019115723, 1)])]),
    (12, .round 1 [(13097927, 1), (179452162007, 1), (3038776685491, 1)])]

private theorem checked3_42 : replayAbundance bank 3 74877803 (10^300) 5 state3_42 tree3_42 = true := by
  decide +kernel

theorem reject3_42 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_42 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree3_42 checked3_42

@[expose] noncomputable def state3_43 : State := ⟨12157665459056928801, 18236498188585393201, 0⟩

private noncomputable def tree3_43 : AbundanceTree :=
  .split 86950696619 [
    (2, .split 7560423642616328727781 [
      (2, .split 114707673343018436243948659 [
        (2, .split 2526913 [
          (6, .round 6228104212690837 [(156577, 1), (2064379, 1), (848697683, 1), (6228104212690837, 1)])])]),
      (4, .split 2526913 [
        (6, .round 1 [(848697683, 1)])])]),
    (6, .split 2526913 [
      (6, .split 6228104212690837 [
        (1, .split 22730307345587 [])]),
      (10, .round 1 [(336905609838849202956933661947604825994271802453137393931, 1)])]),
    (10, .split 2526913 []),
    (12, .split 2526913 [])]

private theorem checked3_43 : replayAbundance bank 3 74877803 (10^300) 7 state3_43 tree3_43 = true := by
  decide +kernel

theorem reject3_43 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_43 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree3_43 checked3_43

@[expose] noncomputable def state3_44 : State := ⟨109418989131512359209, 164128483697268538813, 0⟩

private noncomputable def tree3_44 : AbundanceTree :=
  .split 380808546861411923 [
    (4, .split 26431239645132182318301507785895061 [
      (1, .split 161143736783433929267521 [])]),
    (6, .split 1208923608657985963 [
      (2, .round 1 [(2127359958618118186970157415084459, 1)])])]

private theorem checked3_44 : replayAbundance bank 3 74877803 (10^300) 5 state3_44 tree3_44 = true := by
  decide +kernel

theorem reject3_44 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_44 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree3_44 checked3_44

@[expose] noncomputable def state3_45 : State := ⟨8862938119652501095929, 13294407179478751643893, 0⟩

private noncomputable def tree3_45 : AbundanceTree :=
  .split 96656723 [
    (6, .split 349842127708427058287633 [
      (1, .split 4261210359825834719543 []),
      (2, .split 1000266157066423203744583 []),
      (4, .round 1 [(4261210359825834719543, 1)])]),
    (10, .split 21725473066772863950504173513098364324584931693593 [
      (1, .round 1 [(130769, 1), (258809, 1), (5112661, 1), (320694229, 1), (94129832004310937469012032249717, 1)])]),
    (12, .split 5112661 [
      (1, .split 2556331 [
        (2, .split 26610109 [
          (2, .round 1 [(2003, 1), (21269, 1), (21997, 1), (236032642533997, 1)])]),
        (4, .round 1 [(8540799213542848201829461, 1)])]),
      (2, .split 10214657137 [])]),
    (16, .round 5112661 [(953, 1), (1223, 1), (21997, 1), (5112661, 1)])]

private theorem checked3_45 : replayAbundance bank 3 74877803 (10^300) 7 state3_45 tree3_45 = true := by
  decide +kernel

theorem reject3_45 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_45 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree3_45 checked3_45

@[expose] noncomputable def state3_46 : State := ⟨6461081889226673298932241, 9691622833840009948398361, 0⟩

private noncomputable def tree3_46 : AbundanceTree :=
  .split 3747607031112307667 [
    (4, .split 9765578657333421967770993073534901 [
      (1, .split 76372709981818363434801791580961 [])]),
    (6, .split 55147 [
      (2, .split 6713569 [
        (1, .split 671357 [])])])]

private theorem checked3_46 : replayAbundance bank 3 74877803 (10^300) 6 state3_46 tree3_46 = true := by
  decide +kernel

theorem reject3_46 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_46 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree3_46 checked3_46

@[expose] noncomputable def state3_47 : State := ⟨4710128697246244834921603689, 7065193045869367252382405533, 0⟩

private noncomputable def tree3_47 : AbundanceTree :=
  .split 489769993189671059 [
    (2, .split 8598509368780937491 [
      (4, .split 1093258017237971729095577456688681214669241886637747557079936451002105626181 [])]),
    (4, .split 14838719937203868848850500506716523518922675219564546603981 [
      (1, .split 2198635888517939077611274043 [])]),
    (6, .split 2505051879696101784446736308957057983399568618014258494724914460625463048799405009853287874873101 [])]

private theorem checked3_47 : replayAbundance bank 3 74877803 (10^300) 5 state3_47 tree3_47 = true := by
  decide +kernel

theorem reject3_47 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_47 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree3_47 checked3_47

@[expose] noncomputable def state3_48 : State := ⟨42391158275216203514294433201, 63586737412824305271441649801, 0⟩

private noncomputable def tree3_48 : AbundanceTree :=
  .split 105293313660391861035901 [
    (4, .round 1 [(3467554724111, 1), (411802087918509031, 1), (143248443570926491474211, 1), (120179775845388603258928272133182896251, 1)])]

private theorem checked3_48 : replayAbundance bank 3 74877803 (10^300) 4 state3_48 tree3_48 = true := by
  decide +kernel

theorem reject3_48 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_48 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree3_48 checked3_48

@[expose] noncomputable def state3_49 : State := ⟨30903154382632612361920641803529, 46354731573948918542880962705293, 0⟩

private noncomputable def tree3_49 : AbundanceTree :=
  .split 475384700124973 [
    (1, .split 441019876741 [
      (6, .split 2343435803 []),
      (10, .round 1 [(2343435803, 1)])]),
    (4, .split 38837477199485305775994962307001 [
      (1, .split 33792725390932884587831 []),
      (2, .round 441019876741 [(1321, 1), (2141, 1), (9319, 1), (69439, 1), (221101, 1), (4281922861, 1), (441019876741, 1), (2020300327691, 1)])]),
    (6, .split 883264137303032970769744643 [])]

private theorem checked3_49 : replayAbundance bank 3 74877803 (10^300) 5 state3_49 tree3_49 = true := by
  decide +kernel

theorem reject3_49 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_49 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree3_49 checked3_49

@[expose] noncomputable def state3_50 : State := ⟨2503155504993241601315571986085849, 3754733257489862401973357979128773, 0⟩

private noncomputable def tree3_50 : AbundanceTree :=
  .split 3754733257489862401973357979128773 [
    (1, .split 4052490063499 [
      (2, .split 55966233918334582459 [
        (2, .split 8540432484382583143 []),
        (4, .round 1 [(853, 1), (2131, 1), (82219, 1), (97813, 1), (3099719989, 1)])]),
      (6, .round 1 [(399259605875035119828589166705947916681231082949734535510971181006799, 1)])])]

private theorem checked3_50 : replayAbundance bank 3 74877803 (10^300) 6 state3_50 tree3_50 = true := by
  decide +kernel

theorem reject3_50 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_50 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree3_50 checked3_50

@[expose] noncomputable def state3_51 : State := ⟨22528399544939174411840147874772641, 33792599317408761617760221812158961, 0⟩

private noncomputable def tree3_51 : AbundanceTree :=
  .split 9460375336977361 [
    (2, .split 29832900505496508718289054500561 [
      (1, .split 9255235542077137267048253 [
        (2, .split 41413832311099 [
          (2, .round 1 [(15768033143, 1), (1959224382721, 1), (901870204247557319581, 1)])])]),
      (2, .split 2281074882720528877 [
        (1, .round 1 [(8269, 1), (11243, 1), (13681, 1), (20149, 1), (23887, 1), (75709, 1), (109695889, 1), (15768033143, 1), (134633676459019, 1), (39043567624569589, 1)]),
        (2, .round 39043567624569589 [(20149, 1), (23887, 1), (75709, 1), (15768033143, 1), (134633676459019, 1), (39043567624569589, 1)])])]),
    (6, .split 65415293913810879186763765258759024743242170438623241990848261877725852093371788013473 [])]

private theorem checked3_51 : replayAbundance bank 3 74877803 (10^300) 7 state3_51 tree3_51 = true := by
  decide +kernel

theorem reject3_51 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_51 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree3_51 checked3_51

@[expose] noncomputable def state3_52 : State := ⟨16423203268260658146231467800709255289, 24634804902390987219347201701063882933, 0⟩

private noncomputable def tree3_52 : AbundanceTree :=
  .split 145171177264407947 [
    (6, .round 1 [(3076218487405306438204266595835208734518020024512316564608733745279668911, 1)])]

private theorem checked3_52 : replayAbundance bank 3 74877803 (10^300) 4 state3_52 tree3_52 = true := by
  decide +kernel

theorem reject3_52 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_52 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree3_52 checked3_52

@[expose] noncomputable def state3_53 : State := ⟨1330279464729113309844748891857449678409, 1995419197093669964767123337786174517613, 0⟩

private noncomputable def tree3_53 : AbundanceTree :=
  .split 950996059627210897943351 []

private theorem checked3_53 : replayAbundance bank 3 74877803 (10^300) 3 state3_53 tree3_53 = true := by
  decide +kernel

theorem reject3_53 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_53 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_53 checked3_53

@[expose] noncomputable def state3_54 : State := ⟨969773729787523602876821942164080815560161, 1454660594681285404315232913246121223340241, 0⟩

private noncomputable def tree3_54 : AbundanceTree :=
  .split 5042939439565996049162197 []

private theorem checked3_54 : replayAbundance bank 3 74877803 (10^300) 3 state3_54 tree3_54 = true := by
  decide +kernel

theorem reject3_54 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_54 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_54 checked3_54

@[expose] noncomputable def state3_55 : State := ⟨6362685441135942358474828762538534230890216321, 9544028161703913537712243143807801346335324481, 0⟩

private noncomputable def tree3_55 : AbundanceTree :=
  .split 48845962828028421155731228333 [
    (2, .split 7956390695593152787478995941367927117 [
      (1, .split 20692716021225254452457974058309 []),
      (2, .round 1 [(2549755542947, 1)])]),
    (4, .round 1 [(2549755542947, 1)])]

private theorem checked3_55 : replayAbundance bank 3 74877803 (10^300) 5 state3_55 tree3_55 = true := by
  decide +kernel

theorem reject3_55 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_55 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree3_55 checked3_55

@[expose] noncomputable def state3_56 : State := ⟨515377520732011331036461129765621272702107522001, 773066281098016996554691694648431909053161283001, 0⟩

private noncomputable def tree3_56 : AbundanceTree :=
  .split 50316775668019759306202964023 [
    (2, .split 942937138947191062678148648111573147677187129521 [
      (1, .round 1 [(10687, 1), (7794023, 1), (33034273, 1), (465092326319, 1), (3377651878597, 1), (17909199576426970731064974131, 1)])]),
    (4, .round 1 [(465092326319, 1)])]

private theorem checked3_56 : replayAbundance bank 3 74877803 (10^300) 5 state3_56 tree3_56 = true := by
  decide +kernel

theorem reject3_56 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_56 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree3_56 checked3_56

@[expose] noncomputable def state3_57 : State := ⟨4638397686588101979328150167890591454318967698009, 6957596529882152968992225251835887181478451547013, 0⟩

private noncomputable def tree3_57 : AbundanceTree :=
  .split 6957596529882152968992225251835887181478451547013 [
    (1, .split 1535090713229126909942383374434289901 [
      (2, .round 1 [(308890468603, 1), (3348533057527736197527567125205923290762027, 1)])]),
    (2, .split 3689786190483514868858729011531953642827230621 [])]

private theorem checked3_57 : replayAbundance bank 3 74877803 (10^300) 5 state3_57 tree3_57 = true := by
  decide +kernel

theorem reject3_57 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_57 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree3_57 checked3_57

@[expose] noncomputable def state3_58 : State := ⟨375710212613636260325580163599137907799836383538729, 563565318920454390488370245398706861699754575308093, 0⟩

private noncomputable def tree3_58 : AbundanceTree :=
  .split 48965028505045123993421250406516036571557 []

private theorem checked3_58 : replayAbundance bank 3 74877803 (10^300) 3 state3_58 tree3_58 = true := by
  decide +kernel

theorem reject3_58 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_58 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_58 checked3_58

@[expose] noncomputable def state3_59 : State := ⟨3381391913522726342930221472392241170198527451848561, 5072087870284089514395332208588361755297791177772841, 0⟩

private noncomputable def tree3_59 : AbundanceTree :=
  .split 10624346875389299603 [
    (2, .split 112163735142315646497529 [
      (1, .split 8017422097377816047 [
        (2, .round 1 [(521402591, 1), (3499901929, 1), (12117963973, 1), (239789806103, 1), (5720193000792603980011, 1)])])]),
    (4, .round 1 [(3605874131348838205807751841903426251404678964385635713963631089271, 1)])]

private theorem checked3_59 : replayAbundance bank 3 74877803 (10^300) 6 state3_59 tree3_59 = true := by
  decide +kernel

theorem reject3_59 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_59 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree3_59 checked3_59

@[expose] noncomputable def state3_60 : State := ⟨273892744995340833777347939263771534786080723599733441, 410839117493011250666021908895657302179121085399600161, 0⟩

private noncomputable def tree3_60 : AbundanceTree :=
  .split 526256453012063980796131127321354599535039 []

private theorem checked3_60 : replayAbundance bank 3 74877803 (10^300) 3 state3_60 tree3_60 = true := by
  decide +kernel

theorem reject3_60 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_60 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_60 checked3_60

@[expose] noncomputable def state3_61 : State := ⟨1310020508637620352391208095712502073964245732475093456566329, 1965030762956430528586812143568753110946368598712640184849493, 0⟩

private noncomputable def tree3_61 : AbundanceTree :=
  .split 301515315752300874236564235591357673 []

private theorem checked3_61 : replayAbundance bank 3 74877803 (10^300) 3 state3_61 tree3_61 = true := by
  decide +kernel

theorem reject3_61 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_61 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_61 checked3_61

@[expose] noncomputable def state3_62 : State := ⟨106111661199647248543687855752712667991103904330482569981872649, 159167491799470872815531783629069001986655856495723854972808973, 0⟩

private noncomputable def tree3_62 : AbundanceTree :=
  .split 605199588591144003100881306574406851660288427740394885828171 []

private theorem checked3_62 : replayAbundance bank 3 74877803 (10^300) 3 state3_62 tree3_62 = true := by
  decide +kernel

theorem reject3_62 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_62 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_62 checked3_62

@[expose] noncomputable def state3_63 : State := ⟨77355401014542844188348446843727534965514746256921793516785161121, 116033101521814266282522670265591302448272119385382690275177741681, 0⟩

private noncomputable def tree3_63 : AbundanceTree :=
  .split 108081809773839995188256800499141543684393035450350551 [
    (2, .round 1 [(217629707, 1), (262878787, 1)])]

private theorem checked3_63 : replayAbundance bank 3 74877803 (10^300) 4 state3_63 tree3_63 = true := by
  decide +kernel

theorem reject3_63 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_63 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree3_63 checked3_63

@[expose] noncomputable def state3_64 : State := ⟨696198609130885597695136021593547814689632716312296141651066450089, 1044297913696328396542704032390321722034449074468444212476599675133, 0⟩

private noncomputable def tree3_64 : AbundanceTree :=
  .split 115215201111546538317696820901417129607616709798043944747 []

private theorem checked3_64 : replayAbundance bank 3 74877803 (10^300) 3 state3_64 tree3_64 = true := by
  decide +kernel

theorem reject3_64 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_64 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_64 checked3_64

@[expose] noncomputable def state3_65 : State := ⟨41109831670569663658300086939077404909608122265524774868353822811305361, 61664747505854495487450130408616107364412183398287162302530734216958041, 0⟩

private noncomputable def tree3_65 : AbundanceTree :=
  .split 46509804063632583432467217805311362636553293639540930405531 []

private theorem checked3_65 : replayAbundance bank 3 74877803 (10^300) 3 state3_65 tree3_65 = true := by
  decide +kernel

theorem reject3_65 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_65 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_65 checked3_65

@[expose] noncomputable def state3_66 : State := ⟨369988485035126972924700782451696644186473100389722973815184405301748249, 554982727552690459387051173677544966279709650584584460722776607952622373, 0⟩

private noncomputable def tree3_66 : AbundanceTree :=
  .split 905673230703550690601003473107008473103084254587061 [
    (1, .split 17039118605046803898613358569 []),
    (2, .round 2508391439795128297693169687171969161162527720152116219190299168647106394762124638801067614384963929 [(64745079361, 1), (2508391439795128297693169687171969161162527720152116219190299168647106394762124638801067614384963929, 1)])]

private theorem checked3_66 : replayAbundance bank 3 74877803 (10^300) 4 state3_66 tree3_66 = true := by
  decide +kernel

theorem reject3_66 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_66 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree3_66 checked3_66

@[expose] noncomputable def state3_67 : State := ⟨269721605590607563262106870407286853611938890184108047911269431464974473521, 404582408385911344893160305610930280417908335276162071866904147197461710281, 0⟩

private noncomputable def tree3_67 : AbundanceTree :=
  .split 1283810768507270931382867729773882314783 []

private theorem checked3_67 : replayAbundance bank 3 74877803 (10^300) 3 state3_67 tree3_67 = true := by
  decide +kernel

theorem reject3_67 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_67 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_67 checked3_67

@[expose] noncomputable def state3_68 : State := ⟨196627050475552913618075908526912116283103450944214766927315415537966391196809, 294940575713329370427113862790368174424655176416322150390973123306949586795213, 0⟩

private noncomputable def tree3_68 : AbundanceTree :=
  .split 6351885141964057411259499526611848626072045955243 []

private theorem checked3_68 : replayAbundance bank 3 74877803 (10^300) 3 state3_68 tree3_68 = true := by
  decide +kernel

theorem reject3_68 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_68 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_68 checked3_68

@[expose] noncomputable def state3_69 : State := ⟨15926791088519786003064148590679881418931379526481396121112548658575277686941529, 23890186632779679004596222886019822128397069289722094181668822987862916530412293, 0⟩

private noncomputable def tree3_69 : AbundanceTree :=
  .split 260551495718621260054268273374657473120059796409 [
    (1, .split 719933342870241613 [])]

private theorem checked3_69 : replayAbundance bank 3 74877803 (10^300) 4 state3_69 tree3_69 = true := by
  decide +kernel

theorem reject3_69 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_69 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree3_69 checked3_69

@[expose] noncomputable def state3_70 : State := ⟨11610630703530923996233764322605633554400975674804937772291047972101377433780374641, 17415946055296385994350646483908450331601463512207406658436571958152066150670561961, 0⟩

private noncomputable def tree3_70 : AbundanceTree :=
  .split 30985428700388045508959018054392810762033149280306907746766819 []

private theorem checked3_70 : replayAbundance bank 3 74877803 (10^300) 3 state3_70 tree3_70 = true := by
  decide +kernel

theorem reject3_70 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_70 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_70 checked3_70

@[expose] noncomputable def state3_71 : State := ⟨8464149782874043593254414191179506861158311266932799636000173971661904149225893113289, 12696224674311065389881621286769260291737466900399199454000260957492856223838839669933, 0⟩

private noncomputable def tree3_71 : AbundanceTree :=
  .split 161868664744491655705858963594331 []

private theorem checked3_71 : replayAbundance bank 3 74877803 (10^300) 3 state3_71 tree3_71 = true := by
  decide +kernel

theorem reject3_71 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_71 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_71 checked3_71

@[expose] noncomputable def state3_72 : State := ⟨76177348045866392339289727720615561750424801402395196724001565744957137343033038019601, 114266022068799588508934591580923342625637202103592795086002348617435706014549557029401, 0⟩

private noncomputable def tree3_72 : AbundanceTree :=
  .split 1412740676235815729693013611798695493926336144083867368022228212267580445753 [
    (1, .round 1 [(109493990707136573602303883584030263567622474391347175253666777311, 1)])]

private theorem checked3_72 : replayAbundance bank 3 74877803 (10^300) 4 state3_72 tree3_72 = true := by
  decide +kernel

theorem reject3_72 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_72 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree3_72 checked3_72

@[expose] noncomputable def state3_73 : State := ⟨4498196224760364601242719132174628305800834098010033971355568455673974002968757862019419449, 6747294337140546901864078698261942458701251147015050957033352683510961004453136793029129173, 0⟩

private noncomputable def tree3_73 : AbundanceTree :=
  .split 5890868591760365434332005074929710400548909181468214858888800348369500317 []

private theorem checked3_73 : replayAbundance bank 3 74877803 (10^300) 3 state3_73 tree3_73 = true := by
  decide +kernel

theorem reject3_73 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_73 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_73 checked3_73

@[expose] noncomputable def state3_74 : State := ⟨40483766022843281411184472189571654752207506882090305742200116101065766026718820758174775041, 60725649034264922116776708284357482128311260323135458613300174151598649040078231137262162561, 0⟩

private noncomputable def tree3_74 : AbundanceTree :=
  .split 607981469094652492202396647678317419649770543 []

private theorem checked3_74 : replayAbundance bank 3 74877803 (10^300) 3 state3_74 tree3_74 = true := by
  decide +kernel

theorem reject3_74 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_74 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_74 checked3_74

@[expose] noncomputable def state3_75 : State := ⟨3279185047850305794305942247355304034928808057449314765118209404186327048164224481412156778321, 4918777571775458691458913371032956052393212086173972147677314106279490572246336722118235167481, 0⟩

private noncomputable def tree3_75 : AbundanceTree :=
  .split 58733573000937067164211172290216978734891718609 []

private theorem checked3_75 : replayAbundance bank 3 74877803 (10^300) 3 state3_75 tree3_75 = true := by
  decide +kernel

theorem reject3_75 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_75 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_75 checked3_75

@[expose] noncomputable def state3_76 : State := ⟨29512665430652752148753480226197736314359272517043832886063884637676943433478020332709411004889, 44268998145979128223130220339296604471538908775565749329095826956515415150217030499064116507333, 0⟩

private noncomputable def tree3_76 : AbundanceTree :=
  .split 110902970953020998760372036298330712066931713186888935429 [
    (1, .round 1 [(293366430131930353811221418233, 1), (65746047949771080612445556717533662593, 1)])]

private theorem checked3_76 : replayAbundance bank 3 74877803 (10^300) 4 state3_76 tree3_76 = true := by
  decide +kernel

theorem reject3_76 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_76 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree3_76 checked3_76

@[expose] noncomputable def state3_77 : State := ⟨15684240429131529254685698284890751184639406145730291592802676915731672495230992603635422093849215049, 23526360643697293882028547427336126776959109218595437389204015373597508742846488905453133140773822573, 0⟩

private noncomputable def tree3_77 : AbundanceTree :=
  .split 22260233052088235975354234411 [
    (2, .round 1 [(1695949409060064182746451, 1)])]

private theorem checked3_77 : replayAbundance bank 3 74877803 (10^300) 4 state3_77 tree3_77 = true := by
  decide +kernel

theorem reject3_77 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_77 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree3_77 checked3_77

@[expose] noncomputable def state3_78 : State := ⟨8335248417898089038639422182220625700315950641493051894370647422773355762538053940268612352977320694855609, 12502872626847133557959133273330938550473925962239577841555971134160033643807080910402918529465981042283413, 0⟩

private noncomputable def tree3_78 : AbundanceTree :=
  .split 229523806583019160757328140035039965995090154366780957756461054952218263816107757 [
    (1, .round 1 [(54473097204950819531444809, 1)])]

private theorem checked3_78 : replayAbundance bank 3 74877803 (10^300) 4 state3_78 tree3_78 = true := by
  decide +kernel

theorem reject3_78 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_78 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree3_78 checked3_78

@[expose] noncomputable def state3_79 : State := ⟨675155121849745212129793196759870681725592001960937203444022441244641816765582369161757600591162976283304329, 1012732682774617818194689795139806022588388002941405805166033661866962725148373553742636400886744464424956493, 0⟩

private noncomputable def tree3_79 : AbundanceTree :=
  .round 1 [(86695423725589885803695742296342497463, 1), (586802158643368690388409871761484798763798234696414454735059, 1)]

private theorem checked3_79 : replayAbundance bank 3 74877803 (10^300) 3 state3_79 tree3_79 = true := by
  decide +kernel

theorem reject3_79 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_79 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_79 checked3_79

@[expose] noncomputable def state3_80 : State := ⟨6076396096647706909168138770838836135530328017648434830996201971201776350890241322455818405320466786549738961, 9114594144971560363752208156258254203295492026472652246494302956802664526335361983683727607980700179824608441, 0⟩

private noncomputable def tree3_80 : AbundanceTree :=
  .split 193795952251956993033428990650021813 [
    (1, .round 1 [(32356561399076305309, 1), (284663996630519253661, 1), (634538541879036040523, 1)])]

private theorem checked3_80 : replayAbundance bank 3 74877803 (10^300) 4 state3_80 tree3_80 = true := by
  decide +kernel

theorem reject3_80 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_80 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree3_80 checked3_80

@[expose] noncomputable def state3_81 : State := ⟨492188083828464259642619240437945726977956569429523221310692359667343884422109547118921290830957809710528855841, 738282125742696389463928860656918590466934854144284831966038539501015826633164320678381936246436714565793283761, 0⟩

private noncomputable def tree3_81 : AbundanceTree :=
  .round 1 [(6354979252162209284471, 1), (38247482016765032274959, 1), (235663554277284144371286817356030779989411991, 1)]

private theorem checked3_81 : replayAbundance bank 3 74877803 (10^300) 3 state3_81 tree3_81 = true := by
  decide +kernel

theorem reject3_81 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_81 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_81 checked3_81

@[expose] noncomputable def state3_82 : State := ⟨358805113110950445279469426279262434966930339114122428335494730197493691743717859849693621015768243278975535908089, 538207669666425667919204139418893652450395508671183642503242095296240537615576789774540431523652364918463303862133, 0⟩

private noncomputable def tree3_82 : AbundanceTree :=
  .split 1507825692437133671959981388935564985777556063472074560073441273431 []

private theorem checked3_82 : replayAbundance bank 3 74877803 (10^300) 3 state3_82 tree3_82 = true := by
  decide +kernel

theorem reject3_82 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_82 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_82 checked3_82

@[expose] noncomputable def state3_83 : State := ⟨3229246017998554007515224836513361914702373052027101855019452571777443225693460738647242589141914189510779823172801, 4843869026997831011272837254770042872053559578040652782529178857666164838540191107970863883712871284266169734759201, 0⟩

private noncomputable def tree3_83 : AbundanceTree :=
  .round 1 [(8746781693759220836960579574321515651597080180989131549946798109975686695403479, 1)]

private theorem checked3_83 : replayAbundance bank 3 74877803 (10^300) 3 state3_83 tree3_83 = true := by
  decide +kernel

theorem reject3_83 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_83 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_83 checked3_83

@[expose] noncomputable def state3_84 : State := ⟨190683748116796615589766511371277507701260426349148337437043654910886245033973163156381027646240890976422037778530726249, 286025622175194923384649767056916261551890639523722506155565482366329367550959744734571541469361336464633056667796089373, 0⟩

private noncomputable def tree3_84 : AbundanceTree :=
  .split 96461370326140480137275742594590102875331031471807256393566286296975030226677613 []

private theorem checked3_84 : replayAbundance bank 3 74877803 (10^300) 3 state3_84 tree3_84 = true := by
  decide +kernel

theorem reject3_84 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_84 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_84 checked3_84

@[expose] noncomputable def state3_85 : State := ⟨139008452377144732764939786789661303114218850808529137991604824430036072629766435941001769154109609521811665540548899435521, 208512678565717099147409680184491954671328276212793706987407236645054108944649653911502653731164414282717498310823349153281, 0⟩

private noncomputable def tree3_85 : AbundanceTree :=
  .split 1303684432177220040931228503924522275783855152532699243445654450720942101263148269 []

private theorem checked3_85 : replayAbundance bank 3 74877803 (10^300) 3 state3_85 tree3_85 = true := by
  decide +kernel

theorem reject3_85 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_85 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_85 checked3_85

@[expose] noncomputable def state3_86 : State := ⟨101337161782938510185641104569663089970265542239417741595879917009496296947099731800990289713345905341400704179060147688494809, 152005742674407765278461656854494634955398313359126612393819875514244445420649597701485434570018858012101056268590221532742213, 0⟩

private noncomputable def tree3_86 : AbundanceTree :=
  .split 3688200234744568182050401066389522755138234431221709 []

private theorem checked3_86 : replayAbundance bank 3 74877803 (10^300) 3 state3_86 tree3_86 = true := by
  decide +kernel

theorem reject3_86 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_86 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_86 checked3_86

@[expose] noncomputable def state3_87 : State := ⟨73874790939762173925332365231284392588323580292535533623396459499922800474435704482921921201029164993881113346534847664912715761, 110812186409643260887998547846926588882485370438803300435094689249884200711653556724382881801543747490821670019802271497369073641, 0⟩

private noncomputable def tree3_87 : AbundanceTree :=
  .round 1 [(15597165786807676691920291625641910938974071907958316973148155921390236953578833891, 1)]

private theorem checked3_87 : replayAbundance bank 3 74877803 (10^300) 3 state3_87 tree3_87 = true := by
  decide +kernel

theorem reject3_87 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_87 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_87 checked3_87

@[expose] noncomputable def state3_88 : State := ⟨664873118457859565327991287081559533294912222632819802610568135499305204269921340346297290809262484944930020118813628984214441849, 997309677686789347991986930622339299942368333949229703915852203248957806404882010519445936213893727417395030178220443476321662773, 0⟩

private noncomputable def tree3_88 : AbundanceTree :=
  .round 1 [(25868527977712808361978066658579889576559130208360024345084977414463027844372456066131, 1)]

private theorem checked3_88 : replayAbundance bank 3 74877803 (10^300) 3 state3_88 tree3_88 = true := by
  decide +kernel

theorem reject3_88 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_88 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_88 checked3_88

@[expose] noncomputable def state3_89 : State := ⟨484692503355779623124105648282456899771991010299325636103104170778993493912772657112450724999952351524853984666615135529492328107921, 727038755033669434686158472423685349657986515448988454154656256168490240869158985668676087499928527287280976999922703294238492161881, 0⟩

private noncomputable def tree3_89 : AbundanceTree :=
  .round 1 [(96093835737198987630852488215668046851137095982583744906497662037435603571748141245792156421257518028298294596143, 1)]

private theorem checked3_89 : replayAbundance bank 3 74877803 (10^300) 3 state3_89 tree3_89 = true := by
  decide +kernel

theorem reject3_89 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_89 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_89 checked3_89

@[expose] noncomputable def state3_90 : State := ⟨39260092771818149473052557510879008881531271834245376524351437833098473006934585226108508724996140473513172757995825977888878576741601, 58890139157727224209578836266318513322296907751368064786527156749647709510401877839162763087494210710269759136993738966833317865112401, 0⟩

private noncomputable def tree3_90 : AbundanceTree :=
  .round 1 [(543615007915184215523, 1), (2397212236344676495763, 1)]

private theorem checked3_90 : replayAbundance bank 3 74877803 (10^300) 3 state3_90 tree3_90 = true := by
  decide +kernel

theorem reject3_90 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_90 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_90 checked3_90

@[expose] noncomputable def state3_91 : State := ⟨353340834946363345257473017597911079933781446508208388719162940497886257062411267034976578524965264261618554821962433800999907190674409, 530011252419545017886209526396866619900672169762312583078744410746829385593616900552464867787447896392427832232943650701499860786011613, 0⟩

private noncomputable def tree3_91 : AbundanceTree :=
  .round 5637503043463711302785197075523227977754476479417792282366672851461413293171897240803829 [(1830824353, 1), (306487563493, 1), (1257602943398454563, 1), (5637503043463711302785197075523227977754476479417792282366672851461413293171897240803829, 1)]

private theorem checked3_91 : replayAbundance bank 3 74877803 (10^300) 3 state3_91 tree3_91 = true := by
  decide +kernel

theorem reject3_91 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_91 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_91 checked3_91

@[expose] noncomputable def state3_92 : State := ⟨20864422962747809174108524216139051359009860634863197145477852473459685593278322907148331985320673889384314043682059753515243519702133177041, 31296634444121713761162786324208577038514790952294795718216778710189528389917484360722497977981010834076471065523089630272865279553199765561, 0⟩

private noncomputable def tree3_92 : AbundanceTree :=
  .round 1 [(587, 1), (64911612051881874971, 1)]

private theorem checked3_92 : replayAbundance bank 3 74877803 (10^300) 3 state3_92 tree3_92 = true := by
  decide +kernel

theorem reject3_92 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_92 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_92 checked3_92

@[expose] noncomputable def state3_93 : State := ⟨99793888233710926097676673961542382339552034110870991187709058567130998942396826836880350287497238272034603157195937657211050782186192219658614729, 149690832350566389146515010942313573509328051166306486781563587850696498413595240255320525431245857408051904735793906485816576173279288329487922093, 0⟩

private noncomputable def tree3_93 : AbundanceTree :=
  .round 11665479581585055349598973071696589607991946673408334574649356416413027107729461307877711679909644074637 [(1209358403350153553775181, 1), (11665479581585055349598973071696589607991946673408334574649356416413027107729461307877711679909644074637, 1)]

private theorem checked3_93 : replayAbundance bank 3 74877803 (10^300) 3 state3_93 tree3_93 = true := by
  decide +kernel

theorem reject3_93 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_93 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_93 checked3_93

@[expose] noncomputable def state3_94 : State := ⟨8083304946930585013911810590884932969503714762980550286204433743937610914334142973787308373287276300034802855732870950234095113357081569792347793049, 12124957420395877520867715886327399454255572144470825429306650615906416371501214460680962559930914450052204283599306425351142670035622354688521689573, 0⟩

private noncomputable def tree3_94 : AbundanceTree :=
  .round 1 [(873069502041694941443, 1)]

private theorem checked3_94 : replayAbundance bank 3 74877803 (10^300) 3 state3_94 tree3_94 = true := by
  decide +kernel

theorem reject3_94 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_94 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_94 checked3_94

@[expose] noncomputable def state3_95 : State := ⟨72749744522375265125206295317964396725533432866824952575839903695438498229007286764085775359585486700313225701595838552106856020213734128131130137441, 109124616783562897687809442976946595088300149300237428863759855543157747343510930146128663039378230050469838552393757828160284030320601192196695206161, 0⟩

private noncomputable def tree3_95 : AbundanceTree :=
  .round 1 [(3759897752153653302941126019779, 1)]

private theorem checked3_95 : replayAbundance bank 3 74877803 (10^300) 3 state3_95 tree3_95 = true := by
  decide +kernel

theorem reject3_95 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_95 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree3_95 checked3_95

@[expose] noncomputable def state3_96 : State := ⟨1, 1, 0⟩

private theorem checked3_96 : checkChildren bank 3 74877803 (10^300) state3_96 3 [state3_13, state3_14, state3_15, state3_16, state3_38, state3_39, state3_40, state3_41, state3_42, state3_43, state3_44, state3_45, state3_46, state3_47, state3_48, state3_49, state3_50, state3_51, state3_52, state3_53, state3_54, state3_55, state3_56, state3_57, state3_58, state3_59, state3_60, state3_61, state3_62, state3_63, state3_64, state3_65, state3_66, state3_67, state3_68, state3_69, state3_70, state3_71, state3_72, state3_73, state3_74, state3_75, state3_76, state3_77, state3_78, state3_79, state3_80, state3_81, state3_82, state3_83, state3_84, state3_85, state3_86, state3_87, state3_88, state3_89, state3_90, state3_91, state3_92, state3_93, state3_94, state3_95] = true := by
  decide +kernel

theorem reject3_96 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) (h : Valid state3_96 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state3_13, state3_14, state3_15, state3_16, state3_38, state3_39, state3_40, state3_41, state3_42, state3_43, state3_44, state3_45, state3_46, state3_47, state3_48, state3_49, state3_50, state3_51, state3_52, state3_53, state3_54, state3_55, state3_56, state3_57, state3_58, state3_59, state3_60, state3_61, state3_62, state3_63, state3_64, state3_65, state3_66, state3_67, state3_68, state3_69, state3_70, state3_71, state3_72, state3_73, state3_74, state3_75, state3_76, state3_77, state3_78, state3_79, state3_80, state3_81, state3_82, state3_83, state3_84, state3_85, state3_86, state3_87, state3_88, state3_89, state3_90, state3_91, state3_92, state3_93, state3_94, state3_95] ?_ checked3_96
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject3_13 ho hN hs hav hx hvalid
  · exact reject3_14 ho hN hs hav hx hvalid
  · exact reject3_15 ho hN hs hav hx hvalid
  · exact reject3_16 ho hN hs hav hx hvalid
  · exact reject3_38 ho hN hs hav hx hvalid
  · exact reject3_39 ho hN hs hav hx hvalid
  · exact reject3_40 ho hN hs hav hx hvalid
  · exact reject3_41 ho hN hs hav hx hvalid
  · exact reject3_42 ho hN hs hav hx hvalid
  · exact reject3_43 ho hN hs hav hx hvalid
  · exact reject3_44 ho hN hs hav hx hvalid
  · exact reject3_45 ho hN hs hav hx hvalid
  · exact reject3_46 ho hN hs hav hx hvalid
  · exact reject3_47 ho hN hs hav hx hvalid
  · exact reject3_48 ho hN hs hav hx hvalid
  · exact reject3_49 ho hN hs hav hx hvalid
  · exact reject3_50 ho hN hs hav hx hvalid
  · exact reject3_51 ho hN hs hav hx hvalid
  · exact reject3_52 ho hN hs hav hx hvalid
  · exact reject3_53 ho hN hs hav hx hvalid
  · exact reject3_54 ho hN hs hav hx hvalid
  · exact reject3_55 ho hN hs hav hx hvalid
  · exact reject3_56 ho hN hs hav hx hvalid
  · exact reject3_57 ho hN hs hav hx hvalid
  · exact reject3_58 ho hN hs hav hx hvalid
  · exact reject3_59 ho hN hs hav hx hvalid
  · exact reject3_60 ho hN hs hav hx hvalid
  · exact reject3_61 ho hN hs hav hx hvalid
  · exact reject3_62 ho hN hs hav hx hvalid
  · exact reject3_63 ho hN hs hav hx hvalid
  · exact reject3_64 ho hN hs hav hx hvalid
  · exact reject3_65 ho hN hs hav hx hvalid
  · exact reject3_66 ho hN hs hav hx hvalid
  · exact reject3_67 ho hN hs hav hx hvalid
  · exact reject3_68 ho hN hs hav hx hvalid
  · exact reject3_69 ho hN hs hav hx hvalid
  · exact reject3_70 ho hN hs hav hx hvalid
  · exact reject3_71 ho hN hs hav hx hvalid
  · exact reject3_72 ho hN hs hav hx hvalid
  · exact reject3_73 ho hN hs hav hx hvalid
  · exact reject3_74 ho hN hs hav hx hvalid
  · exact reject3_75 ho hN hs hav hx hvalid
  · exact reject3_76 ho hN hs hav hx hvalid
  · exact reject3_77 ho hN hs hav hx hvalid
  · exact reject3_78 ho hN hs hav hx hvalid
  · exact reject3_79 ho hN hs hav hx hvalid
  · exact reject3_80 ho hN hs hav hx hvalid
  · exact reject3_81 ho hN hs hav hx hvalid
  · exact reject3_82 ho hN hs hav hx hvalid
  · exact reject3_83 ho hN hs hav hx hvalid
  · exact reject3_84 ho hN hs hav hx hvalid
  · exact reject3_85 ho hN hs hav hx hvalid
  · exact reject3_86 ho hN hs hav hx hvalid
  · exact reject3_87 ho hN hs hav hx hvalid
  · exact reject3_88 ho hN hs hav hx hvalid
  · exact reject3_89 ho hN hs hav hx hvalid
  · exact reject3_90 ho hN hs hav hx hvalid
  · exact reject3_91 ho hN hs hav hx hvalid
  · exact reject3_92 ho hN hs hav hx hvalid
  · exact reject3_93 ho hN hs hav hx hvalid
  · exact reject3_94 ho hN hs hav hx hvalid
  · exact reject3_95 ho hN hs hav hx hvalid

theorem exclude_3 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 3 ∣ N)
    (hav : Nat.Coprime 74877803 N) (hx : N ≤ 10^300) : False :=
  reject3_96 ho hN hs hav hx (root_valid N)

end OddPerfect.IndexComponent.Size300
