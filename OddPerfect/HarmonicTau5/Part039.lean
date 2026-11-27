module

public import OddPerfect.HarmonicTau5.Part038
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1140 : Closed 5 ⟨64779462947761,64802304789421,4,1⟩ := by
  exact closed_size (c:=64802304789421) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2837 : RootAt 5 2837 := by
  intro e he hdiv
  have cases := allowed_list (p:=2837) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1140

theorem htau5_1142 : Closed 5 ⟨65329214857201,65352201913801,4,1⟩ := by
  exact closed_size (c:=65352201913801) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2843 : RootAt 5 2843 := by
  intro e he hdiv
  have cases := allowed_list (p:=2843) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1142

theorem htau5_1144 : Closed 5 ⟨66067651496401,66090833128505,4,1⟩ := by
  exact closed_size (c:=13218166625701) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2851 : RootAt 5 2851 := by
  intro e he hdiv
  have cases := allowed_list (p:=2851) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1144

theorem htau5_1146 : Closed 5 ⟨66625573677601,66648901959701,4,1⟩ := by
  exact closed_size (c:=66648901959701) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2857 : RootAt 5 2857 := by
  intro e he hdiv
  have cases := allowed_list (p:=2857) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1146

theorem htau5_1148 : Closed 5 ⟨66999479873041,67022906264605,4,1⟩ := by
  exact closed_size (c:=13404581252921) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2861 : RootAt 5 2861 := by
  intro e he hdiv
  have cases := allowed_list (p:=2861) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1148

theorem htau5_1150 : Closed 5 ⟨68701569626881,68725440915841,4,1⟩ := by
  exact closed_size (c:=68725440915841) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2879 : RootAt 5 2879 := by
  intro e he hdiv
  have cases := allowed_list (p:=2879) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1150

theorem htau5_1152 : Closed 5 ⟨69468374283361,69492445099121,4,1⟩ := by
  exact closed_size (c:=69492445099121) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2887 : RootAt 5 2887 := by
  intro e he hdiv
  have cases := allowed_list (p:=2887) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1152

theorem htau5_1154 : Closed 5 ⟨70435885826881,70460207610661,4,1⟩ := by
  exact closed_size (c:=70460207610661) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2897 : RootAt 5 2897 := by
  intro e he hdiv
  have cases := allowed_list (p:=2897) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1154

theorem htau5_1156 : Closed 5 ⟨71021222453281,71045695651921,4,1⟩ := by
  exact closed_size (c:=71045695651921) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2903 : RootAt 5 2903 := by
  intro e he hdiv
  have cases := allowed_list (p:=2903) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1156

theorem htau5_1158 : Closed 5 ⟨71610199722961,71634824963581,4,1⟩ := by
  exact closed_size (c:=71634824963581) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2909 : RootAt 5 2909 := by
  intro e he hdiv
  have cases := allowed_list (p:=2909) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1158

theorem htau5_1160 : Closed 5 ⟨72401192014321,72426020955341,4,1⟩ := by
  exact closed_size (c:=72426020955341) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2917 : RootAt 5 2917 := by
  intro e he hdiv
  have cases := allowed_list (p:=2917) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1160

theorem htau5_1162 : Closed 5 ⟨73399126194241,73424211336481,4,1⟩ := by
  exact closed_size (c:=73424211336481) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2927 : RootAt 5 2927 := by
  intro e he hdiv
  have cases := allowed_list (p:=2927) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1162

theorem htau5_1164 : Closed 5 ⟨74610224073841,74635618976521,4,1⟩ := by
  exact closed_size (c:=74635618976521) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2939 : RootAt 5 2939 := by
  intro e he hdiv
  have cases := allowed_list (p:=2939) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1164

theorem htau5_1166 : Closed 5 ⟨76042045003681,76067804504021,4,1⟩ := by
  exact closed_size (c:=76067804504021) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2953 : RootAt 5 2953 := by
  intro e he hdiv
  have cases := allowed_list (p:=2953) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1166

theorem htau5_1168 : Closed 5 ⟨76454895334801,76480759643101,4,1⟩ := by
  exact closed_size (c:=76480759643101) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2957 : RootAt 5 2957 := by
  intro e he hdiv
  have cases := allowed_list (p:=2957) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1168

end OddPerfect.HarmonicChain
