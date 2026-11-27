module

public import OddPerfect.HarmonicTau5.Part022
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htauRoot5_1021 : RootAt 5 1021 := by
  intro e he hdiv
  have cases := allowed_list (p:=1021) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_659

theorem htau5_661 : Closed 5 ⟨1129886087521,1130983064305,4,1⟩ := by
  exact closed_size (c:=226196612861) [(7296664931,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_7296664931) (by decide +kernel)

theorem htauRoot5_1031 : RootAt 5 1031 := by
  intro e he hdiv
  have cases := allowed_list (p:=1031) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_661

theorem htau5_663 : Closed 5 ⟨1138678933921,1139782304981,4,1⟩ := by
  exact closed_size (c:=1139782304981) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1033 : RootAt 5 1033 := by
  intro e he hdiv
  have cases := allowed_list (p:=1033) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_663

theorem htau5_665 : Closed 5 ⟨1165365589441,1166488292321,4,1⟩ := by
  exact closed_size (c:=1166488292321) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1039 : RootAt 5 1039 := by
  intro e he hdiv
  have cases := allowed_list (p:=1039) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_665

theorem htau5_667 : Closed 5 ⟨1210882360801,1212037782901,4,1⟩ := by
  exact closed_size (c:=1212037782901) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1049 : RootAt 5 1049 := by
  intro e he hdiv
  have cases := allowed_list (p:=1049) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_667

theorem htau5_669 : Closed 5 ⟨1220143369201,1221305410505,4,1⟩ := by
  exact closed_size (c:=244261082101) [(14275091,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_14275091) (by decide +kernel)

theorem htauRoot5_1051 : RootAt 5 1051 := by
  intro e he hdiv
  have cases := allowed_list (p:=1051) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_669

theorem htau5_671 : Closed 5 ⟨1267247769841,1268443286605,4,1⟩ := by
  exact closed_size (c:=253688657321) [(398311,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_398311) (by decide +kernel)

theorem htauRoot5_1061 : RootAt 5 1061 := by
  intro e he hdiv
  have cases := allowed_list (p:=1061) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_671

theorem htau5_673 : Closed 5 ⟨1276829940961,1278032229041,4,1⟩ := by
  exact closed_size (c:=1278032229041) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1063 : RootAt 5 1063 := by
  intro e he hdiv
  have cases := allowed_list (p:=1063) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_673

theorem htau5_675 : Closed 5 ⟨1305902703121,1307125458461,4,1⟩ := by
  exact closed_size (c:=1307125458461) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1069 : RootAt 5 1069 := by
  intro e he hdiv
  have cases := allowed_list (p:=1069) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_675

theorem htau5_677 : Closed 5 ⟨1396105301761,1397390849921,4,1⟩ := by
  exact closed_size (c:=1397390849921) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1087 : RootAt 5 1087 := by
  intro e he hdiv
  have cases := allowed_list (p:=1087) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_677

theorem htau5_679 : Closed 5 ⟨1416768858961,1418068646905,4,1⟩ := by
  exact closed_size (c:=283613729381) [(5514451,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_5514451) (by decide +kernel)

theorem htauRoot5_1091 : RootAt 5 1091 := by
  intro e he hdiv
  have cases := allowed_list (p:=1091) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_679

theorem htau5_681 : Closed 5 ⟨1427186233201,1428493180301,4,1⟩ := by
  exact closed_size (c:=1428493180301) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1093 : RootAt 5 1093 := by
  intro e he hdiv
  have cases := allowed_list (p:=1093) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_681

theorem htau5_683 : Closed 5 ⟨1448193221281,1449514565461,4,1⟩ := by
  exact closed_size (c:=1449514565461) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1097 : RootAt 5 1097 := by
  intro e he hdiv
  have cases := allowed_list (p:=1097) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_683

theorem htau5_685 : Closed 5 ⟨1480137458881,1481480596321,4,1⟩ := by
  exact closed_size (c:=1481480596321) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1103 : RootAt 5 1103 := by
  intro e he hdiv
  have cases := allowed_list (p:=1103) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_685

theorem htau5_687 : Closed 5 ⟨1512607274161,1513972443181,4,1⟩ := by
  exact closed_size (c:=1513972443181) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1109 : RootAt 5 1109 := by
  intro e he hdiv
  have cases := allowed_list (p:=1109) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_687

theorem htau5_689 : Closed 5 ⟨1556727840721,1558122758141,4,1⟩ := by
  exact closed_size (c:=1558122758141) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

end OddPerfect.HarmonicChain
