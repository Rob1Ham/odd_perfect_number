module

public import OddPerfect.HarmonicTau5.Part049
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1470 : Closed 5 ⟨316238254381921,316313263455541,4,1⟩ := by
  exact closed_size (c:=316313263455541) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4217 : RootAt 5 4217 := by
  intro e he hdiv
  have cases := allowed_list (p:=4217) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1470

theorem htau5_1472 : Closed 5 ⟨316838611601521,316913727441161,4,1⟩ := by
  exact closed_size (c:=316913727441161) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4219 : RootAt 5 4219 := by
  intro e he hdiv
  have cases := allowed_list (p:=4219) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1472

theorem htau5_1474 : Closed 5 ⟨319853229882481,319928881072141,4,1⟩ := by
  exact closed_size (c:=319928881072141) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4229 : RootAt 5 4229 := by
  intro e he hdiv
  have cases := allowed_list (p:=4229) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1474

theorem htau5_1476 : Closed 5 ⟨320458725652321,320534484216305,4,1⟩ := by
  exact closed_size (c:=64106896843261) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4231 : RootAt 5 4231 := by
  intro e he hdiv
  have cases := allowed_list (p:=4231) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1476

theorem htau5_1478 : Closed 5 ⟨323499109738561,323575406698405,4,1⟩ := by
  exact closed_size (c:=64715081339681) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4241 : RootAt 5 4241 := by
  intro e he hdiv
  have cases := allowed_list (p:=4241) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1478

theorem htau5_1480 : Closed 5 ⟨324109773296401,324186178240601,4,1⟩ := by
  exact closed_size (c:=324186178240601) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4243 : RootAt 5 4243 := by
  intro e he hdiv
  have cases := allowed_list (p:=4243) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1480

theorem htau5_1482 : Closed 5 ⟨327176069584081,327253015978621,4,1⟩ := by
  exact closed_size (c:=327253015978621) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4253 : RootAt 5 4253 := by
  intro e he hdiv
  have cases := allowed_list (p:=4253) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1482

theorem htau5_1484 : Closed 5 ⟨329026259524561,329103532013881,4,1⟩ := by
  exact closed_size (c:=329103532013881) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4259 : RootAt 5 4259 := by
  intro e he hdiv
  have cases := allowed_list (p:=4259) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1484

theorem htau5_1486 : Closed 5 ⟨329644729766641,329722111158605,4,1⟩ := by
  exact closed_size (c:=65944422231721) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4261 : RootAt 5 4261 := by
  intro e he hdiv
  have cases := allowed_list (p:=4261) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1486

theorem htau5_1488 : Closed 5 ⟨332750169756481,332828097196705,4,1⟩ := by
  exact closed_size (c:=66565619439341) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4271 : RootAt 5 4271 := by
  intro e he hdiv
  have cases := allowed_list (p:=4271) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1488

theorem htau5_1490 : Closed 5 ⟨333373881243841,333451918201061,4,1⟩ := by
  exact closed_size (c:=333451918201061) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4273 : RootAt 5 4273 := by
  intro e he hdiv
  have cases := allowed_list (p:=4273) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1490

theorem htau5_1492 : Closed 5 ⟨336505601239921,336584187321481,4,1⟩ := by
  exact closed_size (c:=336584187321481) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4283 : RootAt 5 4283 := by
  intro e he hdiv
  have cases := allowed_list (p:=4283) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1492

theorem htau5_1494 : Closed 5 ⟨338395192861441,338474109650821,4,1⟩ := by
  exact closed_size (c:=338474109650821) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4289 : RootAt 5 4289 := by
  intro e he hdiv
  have cases := allowed_list (p:=4289) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1494

theorem htau5_1496 : Closed 5 ⟨340927013995681,341006373170261,4,1⟩ := by
  exact closed_size (c:=341006373170261) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4297 : RootAt 5 4297 := by
  intro e he hdiv
  have cases := allowed_list (p:=4297) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1496

theorem htau5_1498 : Closed 5 ⟨350548070339041,350629103180081,4,1⟩ := by
  exact closed_size (c:=350629103180081) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4327 : RootAt 5 4327 := by
  intro e he hdiv
  have cases := allowed_list (p:=4327) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1498

end OddPerfect.HarmonicChain
