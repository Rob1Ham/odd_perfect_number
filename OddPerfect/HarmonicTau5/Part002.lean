module

public import OddPerfect.HarmonicTau5.Part001
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_30 : Closed 5 ⟨17363069361,28531167049,12,2⟩ := by
  apply closed_split (c:=28531167049) (p:=1772893) (by decide +kernel) (by decide +kernel) htauPrime5_1772893 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=1772893) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_28
  · exact htau5_29

theorem htau5_31 : Closed 5 ⟨3794519500429258953,6235195372090525434,15,3⟩ := by
  exact closed_size (c:=1039199228681754239) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_32 : Closed 5 ⟨6853330998478790175379689,11261467419075987434392423,16,3⟩ := by
  exact closed_size (c:=11261467419075987434392423) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_33 : Closed 5 ⟨2100931392681,3452271214381,14,2⟩ := by
  apply closed_split (c:=3452271214381) (p:=1806113) (by decide +kernel) (by decide +kernel) htauPrime5_1806113 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=1806113) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_31
  · exact htau5_32

theorem htau5_34 : Closed 5 ⟨254212698514401,417724816941553,16,2⟩ := by
  exact closed_size (c:=417724816941553) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_35 : Closed 5 ⟨30759736520242521,50544702849929365,18,2⟩ := by
  exact closed_size (c:=10108940569985873) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_36 : Closed 5 ⟨81,121,4,1⟩ := by
  apply closed_split (c:=121) (p:=11) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=11) (r:=1) (E:=15) [2, 4, 6, 8, 10, 12, 14] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htau5_15
  · exact htau5_25
  · exact htau5_27
  · exact htau5_30
  · exact htau5_33
  · exact htau5_34
  · exact htau5_35

theorem htau5_37 : Closed 5 ⟨1322081208513337401,1996675156441681716,18,4⟩ := by
  exact closed_size (c:=166389596370140143) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_38 : Closed 5 ⟨35126375628990861407169,53049674480581660613732,20,4⟩ := by
  exact closed_size (c:=13262418620145415153433) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_39 : Closed 5 ⟨933272674086658196727073161,1409476801286823223465346836,22,4⟩ := by
  exact closed_size (c:=352369200321705805866336709) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_40 : Closed 5 ⟨49760292390129,74689528165252,16,3⟩ := by
  apply closed_split (c:=18672382041313) (p:=163) (by decide +kernel) (by decide +kernel) htauPrime5_163 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=163) (r:=1) (E:=7) [2, 4, 6] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_37
  · exact htau5_38
  · exact htau5_39

theorem htau5_41 : Closed 5 ⟨113503226941884249,170366846474794398,17,3⟩ := by
  exact closed_size (c:=28394474412465733) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_42 : Closed 5 ⟨258900860654437971969,388606776841735876424,18,3⟩ := by
  exact closed_size (c:=48575847105216984553) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_43 : Closed 5 ⟨590552863152773014061289,886412057976032263977730,19,3⟩ := by
  exact closed_size (c:=88641205797603226397773) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_44 : Closed 5 ⟨21815121609,32729854586,15,2⟩ := by
  apply closed_split (c:=16364927293) (p:=2281) (by decide +kernel) (by decide +kernel) htauPrime5_2281 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=2281) (r:=1) (E:=5) [1, 2, 3, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl
  · exact htau5_40
  · exact htau5_41
  · exact htau5_42
  · exact htau5_43

theorem htau5_45 : Closed 5 ⟨99498769658649,149280873941199,16,2⟩ := by
  exact closed_size (c:=49760291313733) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_46 : Closed 5 ⟨453813888413098089,680870066052983092,17,2⟩ := by
  exact closed_size (c:=170217516513245773) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_47 : Closed 5 ⟨2069845145052140383929,3105448371267663057065,18,2⟩ := by
  exact closed_size (c:=621089674253532611413) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_48 : Closed 5 ⟨4782969,7174453,14,1⟩ := by
  apply closed_split (c:=7174453) (p:=4561) (by decide +kernel) (by decide +kernel) htauPrime5_4561 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=4561) (r:=1) (E:=5) [1, 2, 3, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl
  · exact htau5_44
  · exact htau5_45
  · exact htau5_46
  · exact htau5_47

theorem htau5_49 : Closed 5 ⟨282429536481,423644304721,24,1⟩ := by
  exact closed_size (c:=423644304721) [(391151,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_391151) (by decide +kernel)

theorem htauRoot5_3 : RootAt 5 3 := by
  intro e he hdiv
  have cases := allowed_list (p:=3) (r:=5) (E:=32) [4, 14, 24] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_36
  · exact htau5_48
  · exact htau5_49

theorem htau5_51 : Closed 5 ⟨67382066271499763125,85520231898149556156,10,5⟩ := by
  exact closed_size (c:=7126685991512463013) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_52 : Closed 5 ⟨110226346671636444010163125,139897501735365746637497276,12,5⟩ := by
  exact closed_size (c:=34974375433841436659374319) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_53 : Closed 5 ⟨41191085363125,52238186363836,8,4⟩ := by
  apply closed_split (c:=13059546590959) (p:=1279) (by decide +kernel) (by decide +kernel) htauPrime5_1279 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=1279) (r:=1) (E:=5) [2, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_51
  · exact htau5_52

theorem htau5_54 : Closed 5 ⟨105325605273510625,133573062953824494,9,4⟩ := by
  exact closed_size (c:=22262177158970749) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_55 : Closed 5 ⟨269317572684366668125,341546321993350727000,10,4⟩ := by
  exact closed_size (c:=341546321993350727) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_56 : Closed 5 ⟨688645033353925570395625,873333945337018230434842,11,4⟩ := by
  exact closed_size (c:=436666972668509115217421) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_57 : Closed 5 ⟨16109145625,20421495842,7,3⟩ := by
  apply closed_split (c:=10210747921) (p:=2557) (by decide +kernel) (by decide +kernel) htauPrime5_2557 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=2557) (r:=1) (E:=5) [1, 2, 3, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl
  · exact htau5_53
  · exact htau5_54
  · exact htau5_55
  · exact htau5_56

theorem htau5_58 : Closed 5 ⟨717899380460325855625,910078150452040814838,9,4⟩ := by
  exact closed_size (c:=151679691742006802473) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_59 : Closed 5 ⟨6257183002016362204919130625,7932205666292224527648462717,10,4⟩ := by
  exact closed_size (c:=881356185143580503072051413) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

end OddPerfect.HarmonicChain
