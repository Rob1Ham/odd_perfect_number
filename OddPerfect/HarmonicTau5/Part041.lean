module

public import OddPerfect.HarmonicTau5.Part040
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1200 : Closed 5 ⟨91048256370241,91077740909221,4,1⟩ := by
  exact closed_size (c:=91077740909221) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3089 : RootAt 5 3089 := by
  intro e he hdiv
  have cases := allowed_list (p:=3089) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1200

theorem htau5_1202 : Closed 5 ⟨93429255506161,93459316399181,4,1⟩ := by
  exact closed_size (c:=93459316399181) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3109 : RootAt 5 3109 := by
  intro e he hdiv
  have cases := allowed_list (p:=3109) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1202

theorem htau5_1204 : Closed 5 ⟨94637116441921,94667468307361,4,1⟩ := by
  exact closed_size (c:=94667468307361) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3119 : RootAt 5 3119 := by
  intro e he hdiv
  have cases := allowed_list (p:=3119) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1204

theorem htau5_1206 : Closed 5 ⟨94880087090881,94910497375205,4,1⟩ := by
  exact closed_size (c:=18982099475041) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3121 : RootAt 5 3121 := by
  intro e he hdiv
  have cases := allowed_list (p:=3121) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1206

theorem htau5_1208 : Closed 5 ⟨96840734511361,96871614847621,4,1⟩ := by
  exact closed_size (c:=96871614847621) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3137 : RootAt 5 3137 := by
  intro e he hdiv
  have cases := allowed_list (p:=3137) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1208

theorem htau5_1210 : Closed 5 ⟨100091400875761,100123055335241,4,1⟩ := by
  exact closed_size (c:=100123055335241) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3163 : RootAt 5 3163 := by
  intro e he hdiv
  have cases := allowed_list (p:=3163) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1210

theorem htau5_1212 : Closed 5 ⟨100598673352321,100630448043841,4,1⟩ := by
  exact closed_size (c:=100630448043841) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3167 : RootAt 5 3167 := by
  intro e he hdiv
  have cases := allowed_list (p:=3167) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1212

theorem htau5_1214 : Closed 5 ⟨100853031438721,100884866360261,4,1⟩ := by
  exact closed_size (c:=100884866360261) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3169 : RootAt 5 3169 := by
  intro e he hdiv
  have cases := allowed_list (p:=3169) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1214

theorem htau5_1216 : Closed 5 ⟨102389324175121,102421522075805,4,1⟩ := by
  exact closed_size (c:=20484304415161) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3181 : RootAt 5 3181 := by
  intro e he hdiv
  have cases := allowed_list (p:=3181) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1216

theorem htau5_1218 : Closed 5 ⟨103164019266961,103196399687321,4,1⟩ := by
  exact closed_size (c:=103196399687321) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3187 : RootAt 5 3187 := by
  intro e he hdiv
  have cases := allowed_list (p:=3187) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1218

theorem htau5_1220 : Closed 5 ⟨103682919315361,103715421797905,4,1⟩ := by
  exact closed_size (c:=20743084359581) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3191 : RootAt 5 3191 := by
  intro e he hdiv
  have cases := allowed_list (p:=3191) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1220

theorem htau5_1222 : Closed 5 ⟨105251369305681,105284239814521,4,1⟩ := by
  exact closed_size (c:=105284239814521) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3203 : RootAt 5 3203 := by
  intro e he hdiv
  have cases := allowed_list (p:=3203) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1222

theorem htau5_1224 : Closed 5 ⟨106042233977761,106075289536981,4,1⟩ := by
  exact closed_size (c:=106075289536981) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3209 : RootAt 5 3209 := by
  intro e he hdiv
  have cases := allowed_list (p:=3209) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1224

theorem htau5_1226 : Closed 5 ⟨107103643129921,107136946501541,4,1⟩ := by
  exact closed_size (c:=107136946501541) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3217 : RootAt 5 3217 := by
  intro e he hdiv
  have cases := allowed_list (p:=3217) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1226

theorem htau5_1228 : Closed 5 ⟨107637325775281,107670753516205,4,1⟩ := by
  exact closed_size (c:=21534150703241) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3221 : RootAt 5 3221 := by
  intro e he hdiv
  have cases := allowed_list (p:=3221) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1228

end OddPerfect.HarmonicChain
