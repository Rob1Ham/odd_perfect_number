module

public import OddPerfect.HarmonicTau5.Part039
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1170 : Closed 5 ⟨77077320038161,77103342090841,4,1⟩ := by
  exact closed_size (c:=77103342090841) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2963 : RootAt 5 2963 := by
  intro e he hdiv
  have cases := allowed_list (p:=2963) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1170

theorem htau5_1172 : Closed 5 ⟨77703537431521,77729717868661,4,1⟩ := by
  exact closed_size (c:=77729717868661) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2969 : RootAt 5 2969 := by
  intro e he hdiv
  have cases := allowed_list (p:=2969) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1172

theorem htau5_1174 : Closed 5 ⟨77913122039281,77939355413705,4,1⟩ := by
  exact closed_size (c:=15587871082741) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2971 : RootAt 5 2971 := by
  intro e he hdiv
  have cases := allowed_list (p:=2971) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1174

theorem htau5_1176 : Closed 5 ⟨80892053988001,80919035994001,4,1⟩ := by
  exact closed_size (c:=80919035994001) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2999 : RootAt 5 2999 := by
  intro e he hdiv
  have cases := allowed_list (p:=2999) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1176

theorem htau5_1178 : Closed 5 ⟨81108054012001,81135090030005,4,1⟩ := by
  exact closed_size (c:=16227018006001) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3001 : RootAt 5 3001 := by
  intro e he hdiv
  have cases := allowed_list (p:=3001) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1178

theorem htau5_1180 : Closed 5 ⟨82194549986641,82221857146105,4,1⟩ := by
  exact closed_size (c:=16444371429221) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3011 : RootAt 5 3011 := by
  intro e he hdiv
  have cases := allowed_list (p:=3011) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1180

theorem htau5_1182 : Closed 5 ⟨83071576438321,83099101811561,4,1⟩ := by
  exact closed_size (c:=83099101811561) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3019 : RootAt 5 3019 := by
  intro e he hdiv
  have cases := allowed_list (p:=3019) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1182

theorem htau5_1184 : Closed 5 ⟨83512712283841,83540347198561,4,1⟩ := by
  exact closed_size (c:=83540347198561) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3023 : RootAt 5 3023 := by
  intro e he hdiv
  have cases := allowed_list (p:=3023) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1184

theorem htau5_1186 : Closed 5 ⟨85070535710161,85098556308221,4,1⟩ := by
  exact closed_size (c:=85098556308221) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3037 : RootAt 5 3037 := by
  intro e he hdiv
  have cases := allowed_list (p:=3037) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1186

theorem htau5_1188 : Closed 5 ⟨85519603877761,85547735326405,4,1⟩ := by
  exact closed_size (c:=17109547065281) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3041 : RootAt 5 3041 := by
  intro e he hdiv
  have cases := allowed_list (p:=3041) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1188

theorem htau5_1190 : Closed 5 ⟨86423071552801,86451425578901,4,1⟩ := by
  exact closed_size (c:=86451425578901) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3049 : RootAt 5 3049 := by
  intro e he hdiv
  have cases := allowed_list (p:=3049) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1190

theorem htau5_1192 : Closed 5 ⟨87791671617841,87820361706605,4,1⟩ := by
  exact closed_size (c:=17564072341321) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3061 : RootAt 5 3061 := by
  intro e he hdiv
  have cases := allowed_list (p:=3061) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1192

theorem htau5_1194 : Closed 5 ⟨88482035307121,88510894418441,4,1⟩ := by
  exact closed_size (c:=88510894418441) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3067 : RootAt 5 3067 := by
  intro e he hdiv
  have cases := allowed_list (p:=3067) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1194

theorem htau5_1196 : Closed 5 ⟨89874969418081,89904168563441,4,1⟩ := by
  exact closed_size (c:=89904168563441) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3079 : RootAt 5 3079 := by
  intro e he hdiv
  have cases := allowed_list (p:=3079) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1196

theorem htau5_1198 : Closed 5 ⟨90342914902321,90372227983081,4,1⟩ := by
  exact closed_size (c:=90372227983081) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3083 : RootAt 5 3083 := by
  intro e he hdiv
  have cases := allowed_list (p:=3083) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1198

end OddPerfect.HarmonicChain
