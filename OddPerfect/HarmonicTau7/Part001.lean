module

public import OddPerfect.HarmonicTau7.Primes02
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau7_0 : Closed 7 ⟨6334284299201037,9581963583474702,11,4⟩ := by
  exact closed_size (c:=76047330027577) [(67,1),(19,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl
    · exact htauPrime7_67
    · exact (by norm_num)) (by decide +kernel)

theorem htau7_1 : Closed 7 ⟨168295599545472352053,254583249232193047254,13,4⟩ := by
  exact closed_size (c:=42430541538698841209) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_2 : Closed 7 ⟨4471445784323654921696157,6764022348908919926181342,15,4⟩ := by
  exact closed_size (c:=1127337058151486654363557) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_3 : Closed 7 ⟨238408833573,358432034694,9,3⟩ := by
  apply closed_split (c:=59738672449) (p:=163) (by decide +kernel) (by decide +kernel) htauPrime7_163 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=163) (r:=1) (E:=7) [2, 4, 6] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau7_0
  · exact htau7_1
  · exact htau7_2

theorem htau7_4 : Closed 7 ⟨71334068684543757,107246091324023662,11,3⟩ := by
  exact closed_size (c:=53623045662011831) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_5 : Closed 7 ⟨796797,1195742,7,2⟩ := by
  apply closed_split (c:=597871) (p:=547) (by decide +kernel) (by decide +kernel) htauPrime7_547 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=547) (r:=1) (E:=6) [2, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau7_3
  · exact htau7_4

theorem htau7_6 : Closed 7 ⟨214175410851684717,321932013763215924,10,4⟩ := by
  exact closed_size (c:=8942555937867109) [(103,1),(19,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl
    · exact htauPrime7_103
    · exact (by norm_num)) (by decide +kernel)

theorem htau7_7 : Closed 7 ⟨132146228495489470389,198632573417492838726,11,4⟩ := by
  exact closed_size (c:=33105428902915473121) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_8 : Closed 7 ⟨81534222981717003230013,122556298319518670107560,12,4⟩ := by
  exact closed_size (c:=340434161998662972521) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_9 : Closed 7 ⟨50306615579719390992918021,75617236063663945044978138,13,4⟩ := by
  exact closed_size (c:=12602872677277324174163023) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_10 : Closed 7 ⟨31039181812686864242630418957,46655834651281175018340124764,14,4⟩ := by
  exact closed_size (c:=431998468993344213132778933) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_11 : Closed 7 ⟨347123842547301,520925588613618,9,3⟩ := by
  apply closed_split (c:=86820931435603) (p:=617) (by decide +kernel) (by decide +kernel) htauPrime7_617 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=617) (r:=1) (E:=6) [1, 2, 3, 4, 5] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl|rfl
  · exact htau7_6
  · exact htau7_7
  · exact htau7_8
  · exact htau7_9
  · exact htau7_10

theorem htau7_12 : Closed 7 ⟨138356968286345779881,207631042036511423157,10,3⟩ := by
  exact closed_size (c:=23070115781834602573) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_13 : Closed 7 ⟨870899121,1306947099,8,2⟩ := by
  apply closed_split (c:=435649033) (p:=398581) (by decide +kernel) (by decide +kernel) htauPrime7_398581 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=398581) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau7_11
  · exact htau7_12

theorem htau7_14 : Closed 7 ⟨284814874619150877,428200830247187100,11,3⟩ := by
  exact closed_size (c:=1427336100823957) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_15 : Closed 7 ⟨85219173819921514756293,128121543000244867808300,13,3⟩ := by
  exact closed_size (c:=1281215430002448678083) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_16 : Closed 7 ⟨951892739253,1428493180300,9,2⟩ := by
  apply closed_split (c:=14284931803) (p:=547) (by decide +kernel) (by decide +kernel) htauPrime7_547 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=547) (r:=1) (E:=6) [2, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau7_14
  · exact htau7_15

theorem htau7_17 : Closed 7 ⟨1040418764003529,1561343046068993,10,2⟩ := by
  exact closed_size (c:=1561343046068993) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_18 : Closed 7 ⟨729,1093,6,1⟩ := by
  apply closed_split (c:=1093) (p:=1093) (by decide +kernel) (by decide +kernel) htauPrime7_1093 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=1093) (r:=1) (E:=5) [1, 2, 3, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl
  · exact htau7_5
  · exact htau7_13
  · exact htau7_16
  · exact htau7_17

theorem htau7_19 : Closed 7 ⟨47242400011222972401,70865717703335532900,22,3⟩ := by
  exact closed_size (c:=78739686337039481) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_20 : Closed 7 ⟨1738945502013106391108409,2608496204867253335578190,23,3⟩ := by
  exact closed_size (c:=260849620486725333557819) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_21 : Closed 7 ⟨64008844983600433150309426881,96016136804960653205002657800,24,3⟩ := by
  exact closed_size (c:=53342298224978140669445921) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_22 : Closed 7 ⟨1283446983379689,1925175705062090,21,2⟩ := by
  apply closed_split (c:=192517570506209) (p:=36809) (by decide +kernel) (by decide +kernel) htauPrime7_36809 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=36809) (r:=1) (E:=4) [1, 2, 3] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau7_19
  · exact htau7_20
  · exact htau7_21

theorem htau7_23 : Closed 7 ⟨472422716665246344321,708636000105829822611,22,2⟩ := by
  exact closed_size (c:=236212000035276607537) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_24 : Closed 7 ⟨3486784401,5230176601,20,1⟩ := by
  apply closed_split (c:=5230176601) (p:=368089) (by decide +kernel) (by decide +kernel) htauPrime7_368089 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=368089) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau7_22
  · exact htau7_23

theorem htauRoot7_3 : RootAt 7 3 := by
  intro e he hdiv
  have cases := allowed_list (p:=3) (r:=7) (E:=32) [6, 20] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau7_18
  · exact htau7_24

theorem htau7_26 : Closed 7 ⟨5960311890625,7450675977783,8,2⟩ := by
  exact closed_size (c:=2483558659261) [(127159831,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime7_127159831) (by decide +kernel)

theorem htau7_27 : Closed 7 ⟨15625,19531,6,1⟩ := by
  apply closed_split (c:=19531) (p:=19531) (by decide +kernel) (by decide +kernel) htauPrime7_19531 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=19531) (r:=1) (E:=4) [2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_26

theorem htau7_28 : Closed 7 ⟨465649366455078125,582091511440274658,15,2⟩ := by
  exact closed_size (c:=32338417302237481) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_29 : Closed 7 ⟨1220703125,1525878906,13,1⟩ := by
  apply closed_split (c:=254313151) (p:=19531) (by decide +kernel) (by decide +kernel) htauPrime7_19531 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=19531) (r:=1) (E:=4) [2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_28

end OddPerfect.HarmonicChain
