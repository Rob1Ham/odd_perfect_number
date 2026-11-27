module

public import OddPerfect.HarmonicTau5.Part037
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1110 : Closed 5 ⟨54655872347521,54675981204161,4,1⟩ := by
  exact closed_size (c:=54675981204161) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2719 : RootAt 5 2719 := by
  intro e he hdiv
  have cases := allowed_list (p:=2719) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1110

theorem htau5_1112 : Closed 5 ⟨55464377448481,55484708965141,4,1⟩ := by
  exact closed_size (c:=55484708965141) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2729 : RootAt 5 2729 := by
  intro e he hdiv
  have cases := allowed_list (p:=2729) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1112

theorem htau5_1114 : Closed 5 ⟨55627148806321,55647525051305,4,1⟩ := by
  exact closed_size (c:=11129505010261) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2731 : RootAt 5 2731 := by
  intro e he hdiv
  have cases := allowed_list (p:=2731) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1114

theorem htau5_1116 : Closed 5 ⟨56446386112561,56466986983405,4,1⟩ := by
  exact closed_size (c:=11293397396681) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2741 : RootAt 5 2741 := by
  intro e he hdiv
  have cases := allowed_list (p:=2741) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1116

theorem htau5_1118 : Closed 5 ⟨57108264114001,57129045869501,4,1⟩ := by
  exact closed_size (c:=57129045869501) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2749 : RootAt 5 2749 := by
  intro e he hdiv
  have cases := allowed_list (p:=2749) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1118

theorem htau5_1120 : Closed 5 ⟨57441377422081,57462250015621,4,1⟩ := by
  exact closed_size (c:=57462250015621) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2753 : RootAt 5 2753 := by
  intro e he hdiv
  have cases := allowed_list (p:=2753) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1120

theorem htau5_1122 : Closed 5 ⟨58618761251521,58639953862241,4,1⟩ := by
  exact closed_size (c:=58639953862241) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2767 : RootAt 5 2767 := by
  intro e he hdiv
  have cases := allowed_list (p:=2767) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1122

theorem htau5_1124 : Closed 5 ⟨59470764169441,59492187355381,4,1⟩ := by
  exact closed_size (c:=59492187355381) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2777 : RootAt 5 2777 := by
  intro e he hdiv
  have cases := allowed_list (p:=2777) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1124

theorem htau5_1126 : Closed 5 ⟨60505388947441,60527091023821,4,1⟩ := by
  exact closed_size (c:=60527091023821) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2789 : RootAt 5 2789 := by
  intro e he hdiv
  have cases := allowed_list (p:=2789) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1126

theorem htau5_1128 : Closed 5 ⟨60679130081761,60700878873905,4,1⟩ := by
  exact closed_size (c:=12140175774781) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2791 : RootAt 5 2791 := by
  intro e he hdiv
  have cases := allowed_list (p:=2791) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1128

theorem htau5_1130 : Closed 5 ⟨61202599057681,61224488399261,4,1⟩ := by
  exact closed_size (c:=61224488399261) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2797 : RootAt 5 2797 := by
  intro e he hdiv
  have cases := allowed_list (p:=2797) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1130

theorem htau5_1132 : Closed 5 ⟨61553455051201,61575438428005,4,1⟩ := by
  exact closed_size (c:=12315087685601) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2801 : RootAt 5 2801 := by
  intro e he hdiv
  have cases := allowed_list (p:=2801) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1132

theorem htau5_1134 : Closed 5 ⟨61729447662481,61751478157721,4,1⟩ := by
  exact closed_size (c:=61751478157721) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2803 : RootAt 5 2803 := by
  intro e he hdiv
  have cases := allowed_list (p:=2803) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1134

theorem htau5_1136 : Closed 5 ⟨63151010391121,63173420259961,4,1⟩ := by
  exact closed_size (c:=63173420259961) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2819 : RootAt 5 2819 := by
  intro e he hdiv
  have cases := allowed_list (p:=2819) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1136

theorem htau5_1138 : Closed 5 ⟨64414894240321,64437639612581,4,1⟩ := by
  exact closed_size (c:=64437639612581) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2833 : RootAt 5 2833 := by
  intro e he hdiv
  have cases := allowed_list (p:=2833) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1138

end OddPerfect.HarmonicChain
