module

public import OddPerfect.HarmonicTau5.Part036
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1080 : Closed 5 ⟨48062176770721,48080437476181,4,1⟩ := by
  exact closed_size (c:=48080437476181) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2633 : RootAt 5 2633 := by
  intro e he hdiv
  have cases := allowed_list (p:=2633) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1080

theorem htau5_1082 : Closed 5 ⟨49092569678881,49111123182161,4,1⟩ := by
  exact closed_size (c:=49111123182161) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2647 : RootAt 5 2647 := by
  intro e he hdiv
  have cases := allowed_list (p:=2647) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1082

theorem htau5_1084 : Closed 5 ⟨49838644003201,49857408552901,4,1⟩ := by
  exact closed_size (c:=49857408552901) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2657 : RootAt 5 2657 := by
  intro e he hdiv
  have cases := allowed_list (p:=2657) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1084

theorem htau5_1086 : Closed 5 ⟨49988873418961,50007680369081,4,1⟩ := by
  exact closed_size (c:=50007680369081) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2659 : RootAt 5 2659 := by
  intro e he hdiv
  have cases := allowed_list (p:=2659) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1086

theorem htau5_1088 : Closed 5 ⟨50290350881761,50309242824241,4,1⟩ := by
  exact closed_size (c:=50309242824241) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2663 : RootAt 5 2663 := by
  intro e he hdiv
  have cases := allowed_list (p:=2663) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1088

theorem htau5_1090 : Closed 5 ⟨50897394646081,50916457340705,4,1⟩ := by
  exact closed_size (c:=10183291468141) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2671 : RootAt 5 2671 := by
  intro e he hdiv
  have cases := allowed_list (p:=2671) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1090

theorem htau5_1092 : Closed 5 ⟨51356271336241,51375462767981,4,1⟩ := by
  exact closed_size (c:=51375462767981) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2677 : RootAt 5 2677 := by
  intro e he hdiv
  have cases := allowed_list (p:=2677) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1092

theorem htau5_1094 : Closed 5 ⟨51818243883121,51837564630281,4,1⟩ := by
  exact closed_size (c:=51837564630281) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2683 : RootAt 5 2683 := by
  intro e he hdiv
  have cases := allowed_list (p:=2683) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1094

theorem htau5_1096 : Closed 5 ⟨52127952360961,52147359640321,4,1⟩ := by
  exact closed_size (c:=52147359640321) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2687 : RootAt 5 2687 := by
  intro e he hdiv
  have cases := allowed_list (p:=2687) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1096

theorem htau5_1098 : Closed 5 ⟨52283326179841,52302776822021,4,1⟩ := by
  exact closed_size (c:=52302776822021) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2689 : RootAt 5 2689 := by
  intro e he hdiv
  have cases := allowed_list (p:=2689) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1098

theorem htau5_1100 : Closed 5 ⟨52595115558001,52614653119501,4,1⟩ := by
  exact closed_size (c:=52614653119501) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2693 : RootAt 5 2693 := by
  intro e he hdiv
  have cases := allowed_list (p:=2693) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1100

theorem htau5_1102 : Closed 5 ⟨53065411729201,53085080154601,4,1⟩ := by
  exact closed_size (c:=53085080154601) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2699 : RootAt 5 2699 := by
  intro e he hdiv
  have cases := allowed_list (p:=2699) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1102

theorem htau5_1104 : Closed 5 ⟨53697370966801,53717214784601,4,1⟩ := by
  exact closed_size (c:=53717214784601) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2707 : RootAt 5 2707 := by
  intro e he hdiv
  have cases := allowed_list (p:=2707) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1104

theorem htau5_1106 : Closed 5 ⟨54015458929441,54035390833105,4,1⟩ := by
  exact closed_size (c:=10807078166621) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2711 : RootAt 5 2711 := by
  intro e he hdiv
  have cases := allowed_list (p:=2711) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1106

theorem htau5_1108 : Closed 5 ⟨54175031816161,54195007860341,4,1⟩ := by
  exact closed_size (c:=54195007860341) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2713 : RootAt 5 2713 := by
  intro e he hdiv
  have cases := allowed_list (p:=2713) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1108

end OddPerfect.HarmonicChain
