module

public import OddPerfect.HarmonicTau7.Part003
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htauRoot7_37 : RootAt 7 37 := by
  intro e he hdiv
  have cases := allowed_list (p:=37) (r:=7) (E:=10) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_89

theorem htau7_91 : Closed 7 ⟨537850640878060189,551296911766037810,7,2⟩ := by
  exact closed_size (c:=55129691176603781) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_92 : Closed 7 ⟨4750104241,4868856847,6,1⟩ := by
  apply closed_split (c:=4868856847) (p:=113229229) (by decide +kernel) (by decide +kernel) htauPrime7_113229229 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=113229229) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_91

theorem htauRoot7_41 : RootAt 7 41 := by
  intro e he hdiv
  have cases := allowed_list (p:=41) (r:=7) (E:=10) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_92

theorem htau7_94 : Closed 7 ⟨215520052404925129,220689277953965373,8,2⟩ := by
  exact closed_size (c:=10509013235903113) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_95 : Closed 7 ⟨6321363049,6471871693,6,1⟩ := by
  apply closed_split (c:=924553099) (p:=5839) (by decide +kernel) (by decide +kernel) htauPrime7_5839 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=5839) (r:=1) (E:=4) [2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_94

theorem htauRoot7_43 : RootAt 7 43 := by
  intro e he hdiv
  have cases := allowed_list (p:=43) (r:=7) (E:=10) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_95

theorem htau7_97 : Closed 7 ⟨10779215329,11013546097,6,1⟩ := by
  exact closed_size (c:=11013546097) [(256128979,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime7_256128979) (by decide +kernel)

theorem htauRoot7_47 : RootAt 7 47 := by
  intro e he hdiv
  have cases := allowed_list (p:=47) (r:=7) (E:=9) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_97

theorem htau7_99 : Closed 7 ⟨22164361129,22590598843,6,1⟩ := by
  exact closed_size (c:=22590598843) [(778986167,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime7_778986167) (by decide +kernel)

theorem htauRoot7_53 : RootAt 7 53 := by
  intro e he hdiv
  have cases := allowed_list (p:=53) (r:=7) (E:=9) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_99

theorem htau7_101 : Closed 7 ⟨42180533641,42907784221,6,1⟩ := by
  exact closed_size (c:=42907784221) [(4691,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime7_4691) (by decide +kernel)

theorem htauRoot7_59 : RootAt 7 59 := by
  intro e he hdiv
  have cases := allowed_list (p:=59) (r:=7) (E:=9) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_101

theorem htau7_103 : Closed 7 ⟨51520374361,52379047267,6,1⟩ := by
  exact closed_size (c:=52379047267) [(52379047267,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime7_52379047267) (by decide +kernel)

theorem htauRoot7_61 : RootAt 7 61 := by
  intro e he hdiv
  have cases := allowed_list (p:=61) (r:=7) (E:=9) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_103

theorem htau7_105 : Closed 7 ⟨47224793453530309,47940412456024454,7,2⟩ := by
  exact closed_size (c:=23970206228012227) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_106 : Closed 7 ⟨24654222895143486646849,25027819667296411443411,8,2⟩ := by
  exact closed_size (c:=8342606555765470481137) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_107 : Closed 7 ⟨90458382169,91828963717,6,1⟩ := by
  apply closed_split (c:=91828963717) (p:=522061) (by decide +kernel) (by decide +kernel) htauPrime7_522061 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=522061) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau7_105
  · exact htau7_106

theorem htauRoot7_67 : RootAt 7 67 := by
  intro e he hdiv
  have cases := allowed_list (p:=67) (r:=7) (E:=9) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_107

theorem htau7_109 : Closed 7 ⟨128100283921,129930287977,6,1⟩ := by
  exact closed_size (c:=18561469711) [(883,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime7_883) (by decide +kernel)

theorem htauRoot7_71 : RootAt 7 71 := by
  intro e he hdiv
  have cases := allowed_list (p:=71) (r:=7) (E:=9) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_109

theorem htau7_111 : Closed 7 ⟨151334226289,153436090543,6,1⟩ := by
  exact closed_size (c:=153436090543) [(153436090543,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime7_153436090543) (by decide +kernel)

theorem htauRoot7_73 : RootAt 7 73 := by
  intro e he hdiv
  have cases := allowed_list (p:=73) (r:=7) (E:=9) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_111

theorem htau7_113 : Closed 7 ⟨490307397785857,496839594026498,7,2⟩ := by
  exact closed_size (c:=248419797013249) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_114 : Closed 7 ⟨988950021334073569,1002125707355407827,8,2⟩ := by
  exact closed_size (c:=334041902451802609) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_115 : Closed 7 ⟨1994712193030826388673,2021287551982061548420,9,2⟩ := by
  exact closed_size (c:=101064377599103077421) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_116 : Closed 7 ⟨4023334493343176825953441,4076936992348064347124501,10,2⟩ := by
  exact closed_size (c:=4076936992348064347124501) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_117 : Closed 7 ⟨243087455521,246203961361,6,1⟩ := by
  apply closed_split (c:=246203961361) (p:=2017) (by decide +kernel) (by decide +kernel) htauPrime7_2017 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=2017) (r:=1) (E:=5) [1, 2, 3, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl
  · exact htau7_113
  · exact htau7_114
  · exact htau7_115
  · exact htau7_116

theorem htauRoot7_79 : RootAt 7 79 := by
  intro e he hdiv
  have cases := allowed_list (p:=79) (r:=7) (E:=8) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_117

theorem htau7_119 : Closed 7 ⟨3730811876496445073873,3776309582638165619874,7,2⟩ := by
  exact closed_size (c:=629384930439694269979) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

end OddPerfect.HarmonicChain
