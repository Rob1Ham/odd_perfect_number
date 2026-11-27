module

public import OddPerfect.HarmonicTau5.Part050
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1500 : Closed 5 ⟨353799885965761,353881481880421,4,1⟩ := by
  exact closed_size (c:=353881481880421) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4337 : RootAt 5 4337 := by
  intro e he hdiv
  have cases := allowed_list (p:=4337) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1500

theorem htau5_1502 : Closed 5 ⟨354452954340241,354534663181721,4,1⟩ := by
  exact closed_size (c:=354534663181721) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4339 : RootAt 5 4339 := by
  intro e he hdiv
  have cases := allowed_list (p:=4339) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1502

theorem htau5_1504 : Closed 5 ⟨357731868267601,357814143306301,4,1⟩ := by
  exact closed_size (c:=357814143306301) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4349 : RootAt 5 4349 := by
  intro e he hdiv
  have cases := allowed_list (p:=4349) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1504

theorem htau5_1506 : Closed 5 ⟨360371335935601,360454065810701,4,1⟩ := by
  exact closed_size (c:=360454065810701) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4357 : RootAt 5 4357 := by
  intro e he hdiv
  have cases := allowed_list (p:=4357) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1506

theorem htau5_1508 : Closed 5 ⟨362360501421361,362443573521641,4,1⟩ := by
  exact closed_size (c:=362443573521641) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4363 : RootAt 5 4363 := by
  intro e he hdiv
  have cases := allowed_list (p:=4363) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1508

theorem htau5_1510 : Closed 5 ⟨365694062750641,365777707321261,4,1⟩ := by
  exact closed_size (c:=365777707321261) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4373 : RootAt 5 4373 := by
  intro e he hdiv
  have cases := allowed_list (p:=4373) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1510

theorem htau5_1512 : Closed 5 ⟨371752372136161,371837053769905,4,1⟩ := by
  exact closed_size (c:=74367410753981) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4391 : RootAt 5 4391 := by
  intro e he hdiv
  have cases := allowed_list (p:=4391) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1512

theorem htau5_1514 : Closed 5 ⟨373788436964881,373873466181661,4,1⟩ := by
  exact closed_size (c:=373873466181661) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4397 : RootAt 5 4397 := by
  intro e he hdiv
  have cases := allowed_list (p:=4397) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1514

theorem htau5_1516 : Closed 5 ⟨377885645796961,377971373030581,4,1⟩ := by
  exact closed_size (c:=377971373030581) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4409 : RootAt 5 4409 := by
  intro e he hdiv
  have cases := allowed_list (p:=4409) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1516

theorem htau5_1518 : Closed 5 ⟨382016445748081,382102874808205,4,1⟩ := by
  exact closed_size (c:=76420574961641) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4421 : RootAt 5 4421 := by
  intro e he hdiv
  have cases := allowed_list (p:=4421) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1518

theorem htau5_1520 : Closed 5 ⟨382708191059041,382794737461361,4,1⟩ := by
  exact closed_size (c:=382794737461361) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4423 : RootAt 5 4423 := by
  intro e he hdiv
  have cases := allowed_list (p:=4423) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1520

theorem htau5_1522 : Closed 5 ⟨388976256795361,389063864060405,4,1⟩ := by
  exact closed_size (c:=77812772812081) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4441 : RootAt 5 4441 := by
  intro e he hdiv
  have cases := allowed_list (p:=4441) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1522

theorem htau5_1524 : Closed 5 ⟨391082621604481,391170584407361,4,1⟩ := by
  exact closed_size (c:=391170584407361) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4447 : RootAt 5 4447 := by
  intro e he hdiv
  have cases := allowed_list (p:=4447) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1524

theorem htau5_1526 : Closed 5 ⟨392491609582801,392579809944505,4,1⟩ := by
  exact closed_size (c:=78515961988901) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4451 : RootAt 5 4451 := by
  intro e he hdiv
  have cases := allowed_list (p:=4451) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1526

theorem htau5_1528 : Closed 5 ⟨394612225792801,394700783294101,4,1⟩ := by
  exact closed_size (c:=394700783294101) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4457 : RootAt 5 4457 := by
  intro e he hdiv
  have cases := allowed_list (p:=4457) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1528

end OddPerfect.HarmonicChain
