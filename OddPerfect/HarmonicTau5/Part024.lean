module

public import OddPerfect.HarmonicTau5.Part023
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htauRoot5_1117 : RootAt 5 1117 := by
  intro e he hdiv
  have cases := allowed_list (p:=1117) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_689

theorem htau5_691 : Closed 5 ⟨1590446354641,1591863864761,4,1⟩ := by
  exact closed_size (c:=1591863864761) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1123 : RootAt 5 1123 := by
  intro e he hdiv
  have cases := allowed_list (p:=1123) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_691

theorem htau5_693 : Closed 5 ⟨1624709678881,1626150024341,4,1⟩ := by
  exact closed_size (c:=1626150024341) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1129 : RootAt 5 1129 := by
  intro e he hdiv
  have cases := allowed_list (p:=1129) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_693

theorem htau5_695 : Closed 5 ⟨1755097689601,1756623861505,4,1⟩ := by
  exact closed_size (c:=351324772301) [(991,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_991) (by decide +kernel)

theorem htauRoot5_1151 : RootAt 5 1151 := by
  intro e he hdiv
  have cases := allowed_list (p:=1151) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_695

theorem htau5_697 : Closed 5 ⟨1767328289281,1768862428421,4,1⟩ := by
  exact closed_size (c:=1768862428421) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1153 : RootAt 5 1153 := by
  intro e he hdiv
  have cases := allowed_list (p:=1153) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_697

theorem htau5_699 : Closed 5 ⟨1829442899761,1831017291241,4,1⟩ := by
  exact closed_size (c:=1831017291241) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1163 : RootAt 5 1163 := by
  intro e he hdiv
  have cases := allowed_list (p:=1163) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_699

theorem htau5_701 : Closed 5 ⟨1880301880081,1881908975705,4,1⟩ := by
  exact closed_size (c:=376381795141) [(34216526831,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_34216526831) (by decide +kernel)

theorem htauRoot5_1171 : RootAt 5 1171 := by
  intro e he hdiv
  have cases := allowed_list (p:=1171) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_701

theorem htau5_703 : Closed 5 ⟨1945358247121,1947006855805,4,1⟩ := by
  exact closed_size (c:=389401371161) [(251491,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_251491) (by decide +kernel)

theorem htauRoot5_1181 : RootAt 5 1181 := by
  intro e he hdiv
  have cases := allowed_list (p:=1181) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_703

theorem htau5_705 : Closed 5 ⟨1985193642961,1986867499321,4,1⟩ := by
  exact closed_size (c:=1986867499321) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1187 : RootAt 5 1187 := by
  intro e he hdiv
  have cases := allowed_list (p:=1187) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_705

theorem htau5_707 : Closed 5 ⟨2025637716001,2027337076501,4,1⟩ := by
  exact closed_size (c:=2027337076501) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1193 : RootAt 5 1193 := by
  intro e he hdiv
  have cases := allowed_list (p:=1193) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_707

theorem htau5_709 : Closed 5 ⟨866434658380873943047201,867156687264939912036010,5,2⟩ := by
  exact closed_size (c:=86715668726493991203601) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_710 : Closed 5 ⟨2080520644801,2082254412005,4,1⟩ := by
  apply closed_split (c:=416450882401) (p:=416450882401) (by decide +kernel) (by decide +kernel) htauPrime5_416450882401 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=416450882401) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_709

theorem htauRoot5_1201 : RootAt 5 1201 := by
  intro e he hdiv
  have cases := allowed_list (p:=1201) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_710

theorem htau5_712 : Closed 5 ⟨2164926734161,2166712977341,4,1⟩ := by
  exact closed_size (c:=2166712977341) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1213 : RootAt 5 1213 := by
  intro e he hdiv
  have cases := allowed_list (p:=1213) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_712

theorem htau5_714 : Closed 5 ⟨2193624625921,2195428593541,4,1⟩ := by
  exact closed_size (c:=2195428593541) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1217 : RootAt 5 1217 := by
  intro e he hdiv
  have cases := allowed_list (p:=1217) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_714

theorem htau5_716 : Closed 5 ⟨2237205241441,2239036014961,4,1⟩ := by
  exact closed_size (c:=2239036014961) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1223 : RootAt 5 1223 := by
  intro e he hdiv
  have cases := allowed_list (p:=1223) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_716

theorem htau5_718 : Closed 5 ⟨2281432014481,2283289858141,4,1⟩ := by
  exact closed_size (c:=2283289858141) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1229 : RootAt 5 1229 := by
  intro e he hdiv
  have cases := allowed_list (p:=1229) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_718

end OddPerfect.HarmonicChain
