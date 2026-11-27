module

public import OddPerfect.HarmonicTau5.Part042
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1260 : Closed 5 ⟨125493967403281,125531473071961,4,1⟩ := by
  exact closed_size (c:=125531473071961) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3347 : RootAt 5 3347 := by
  intro e he hdiv
  have cases := allowed_list (p:=3347) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1260

theorem htau5_1262 : Closed 5 ⟨127303403660161,127341314143681,4,1⟩ := by
  exact closed_size (c:=127341314143681) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3359 : RootAt 5 3359 := by
  intro e he hdiv
  have cases := allowed_list (p:=3359) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1262

theorem htau5_1264 : Closed 5 ⟨127606868135041,127644846369605,4,1⟩ := by
  exact closed_size (c:=25528969273921) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3361 : RootAt 5 3361 := by
  intro e he hdiv
  have cases := allowed_list (p:=3361) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1264

theorem htau5_1266 : Closed 5 ⟨129132336776881,129170654977705,4,1⟩ := by
  exact closed_size (c:=25834130995541) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3371 : RootAt 5 3371 := by
  intro e he hdiv
  have cases := allowed_list (p:=3371) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1266

theorem htau5_1268 : Closed 5 ⟨129439064282641,129477450719261,4,1⟩ := by
  exact closed_size (c:=129477450719261) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3373 : RootAt 5 3373 := by
  intro e he hdiv
  have cases := allowed_list (p:=3373) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1268

theorem htau5_1270 : Closed 5 ⟨131912598473041,131951533714621,4,1⟩ := by
  exact closed_size (c:=131951533714621) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3389 : RootAt 5 3389 := by
  intro e he hdiv
  have cases := allowed_list (p:=3389) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1270

theorem htau5_1272 : Closed 5 ⟨132224264252161,132263268459905,4,1⟩ := by
  exact closed_size (c:=26452653691981) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3391 : RootAt 5 3391 := by
  intro e he hdiv
  have cases := allowed_list (p:=3391) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1272

theorem htau5_1274 : Closed 5 ⟨134737515307201,134777074178401,4,1⟩ := by
  exact closed_size (c:=134777074178401) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3407 : RootAt 5 3407 := by
  intro e he hdiv
  have cases := allowed_list (p:=3407) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1274

theorem htau5_1276 : Closed 5 ⟨135689159747761,135728927965741,4,1⟩ := by
  exact closed_size (c:=135728927965741) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3413 : RootAt 5 3413 := by
  intro e he hdiv
  have cases := allowed_list (p:=3413) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1276

theorem htau5_1278 : Closed 5 ⟨138897750969121,138938222341781,4,1⟩ := by
  exact closed_size (c:=138938222341781) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3433 : RootAt 5 3433 := by
  intro e he hdiv
  have cases := allowed_list (p:=3433) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1278

theorem htau5_1280 : Closed 5 ⟨141505323151201,141546362978101,4,1⟩ := by
  exact closed_size (c:=141546362978101) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3449 : RootAt 5 3449 := by
  intro e he hdiv
  have cases := allowed_list (p:=3449) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1280

theorem htau5_1282 : Closed 5 ⟨142822791820801,142864117860101,4,1⟩ := by
  exact closed_size (c:=142864117860101) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3457 : RootAt 5 3457 := by
  intro e he hdiv
  have cases := allowed_list (p:=3457) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1282

theorem htau5_1284 : Closed 5 ⟨143484965347441,143526434990605,4,1⟩ := by
  exact closed_size (c:=28705286998121) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3461 : RootAt 5 3461 := by
  intro e he hdiv
  have cases := allowed_list (p:=3461) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1284

theorem htau5_1286 : Closed 5 ⟨143816914232161,143858455801841,4,1⟩ := by
  exact closed_size (c:=143858455801841) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3463 : RootAt 5 3463 := by
  intro e he hdiv
  have cases := allowed_list (p:=3463) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1286

theorem htau5_1288 : Closed 5 ⟨144482539567921,144524225240041,4,1⟩ := by
  exact closed_size (c:=144524225240041) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3467 : RootAt 5 3467 := by
  intro e he hdiv
  have cases := allowed_list (p:=3467) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1288

end OddPerfect.HarmonicChain
