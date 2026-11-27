module

public import OddPerfect.HarmonicTau7.Part004
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau7_120 : Closed 7 ⟨326940373369,330927451093,6,1⟩ := by
  apply closed_split (c:=330927451093) (p:=11411291417) (by decide +kernel) (by decide +kernel) htauPrime7_11411291417 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=11411291417) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_119

theorem htauRoot7_83 : RootAt 7 83 := by
  intro e he hdiv
  have cases := allowed_list (p:=83) (r:=7) (E:=8) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_120

theorem htau7_122 : Closed 7 ⟨496981290961,502628805631,6,1⟩ := by
  exact closed_size (c:=502628805631) [(502628805631,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime7_502628805631) (by decide +kernel)

theorem htauRoot7_89 : RootAt 7 89 := by
  intro e he hdiv
  have cases := allowed_list (p:=89) (r:=7) (E:=8) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_122

theorem htau7_124 : Closed 7 ⟨832972004929,841648796647,6,1⟩ := by
  exact closed_size (c:=841648796647) [(20241187,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime7_20241187) (by decide +kernel)

theorem htauRoot7_97 : RootAt 7 97 := by
  intro e he hdiv
  have cases := allowed_list (p:=97) (r:=7) (E:=8) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_124

theorem htau7_126 : Closed 7 ⟨1061520150601,1072135352107,6,1⟩ := by
  exact closed_size (c:=1072135352107) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_101 : RootAt 7 101 := by
  intro e he hdiv
  have cases := allowed_list (p:=101) (r:=7) (E:=8) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_126

theorem htau7_128 : Closed 7 ⟨1194052296529,1205758691593,6,1⟩ := by
  exact closed_size (c:=1205758691593) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_103 : RootAt 7 103 := by
  intro e he hdiv
  have cases := allowed_list (p:=103) (r:=7) (E:=8) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_128

theorem htau7_130 : Closed 7 ⟨1500730351849,1514888185357,6,1⟩ := by
  exact closed_size (c:=1514888185357) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_107 : RootAt 7 107 := by
  intro e he hdiv
  have cases := allowed_list (p:=107) (r:=7) (E:=8) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_130

theorem htau7_132 : Closed 7 ⟨1677100110841,1692628815571,6,1⟩ := by
  exact closed_size (c:=1692628815571) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_109 : RootAt 7 109 := by
  intro e he hdiv
  have cases := allowed_list (p:=109) (r:=7) (E:=8) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_132

theorem htau7_134 : Closed 7 ⟨2081951752609,2100540607543,6,1⟩ := by
  exact closed_size (c:=300077229649) [(6670903,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime7_6670903) (by decide +kernel)

theorem htauRoot7_113 : RootAt 7 113 := by
  intro e he hdiv
  have cases := allowed_list (p:=113) (r:=7) (E:=8) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_134

theorem htau7_136 : Closed 7 ⟨4195872914689,4229173493377,6,1⟩ := by
  exact closed_size (c:=604167641911) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_127 : RootAt 7 127 := by
  intro e he hdiv
  have cases := allowed_list (p:=127) (r:=7) (E:=8) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_136

theorem htau7_138 : Closed 7 ⟨5053913144281,5092789399237,6,1⟩ := by
  exact closed_size (c:=5092789399237) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_131 : RootAt 7 131 := by
  intro e he hdiv
  have cases := allowed_list (p:=131) (r:=7) (E:=8) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_138

theorem htau7_140 : Closed 7 ⟨6611856250609,6660472840687,6,1⟩ := by
  exact closed_size (c:=6660472840687) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_137 : RootAt 7 137 := by
  intro e he hdiv
  have cases := allowed_list (p:=137) (r:=7) (E:=8) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_140

theorem htau7_142 : Closed 7 ⟨7212549413161,7264814263981,6,1⟩ := by
  exact closed_size (c:=7264814263981) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_139 : RootAt 7 139 := by
  intro e he hdiv
  have cases := allowed_list (p:=139) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_142

theorem htau7_144 : Closed 7 ⟨10942526586601,11016462577051,6,1⟩ := by
  exact closed_size (c:=11016462577051) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_149 : RootAt 7 149 := by
  intro e he hdiv
  have cases := allowed_list (p:=149) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_144

theorem htau7_146 : Closed 7 ⟨11853911588401,11932937665657,6,1⟩ := by
  exact closed_size (c:=11932937665657) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_151 : RootAt 7 151 := by
  intro e he hdiv
  have cases := allowed_list (p:=151) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_146

theorem htau7_148 : Closed 7 ⟨14976071831449,15072072291907,6,1⟩ := by
  exact closed_size (c:=15072072291907) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_157 : RootAt 7 157 := by
  intro e he hdiv
  have cases := allowed_list (p:=157) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_148

end OddPerfect.HarmonicChain
