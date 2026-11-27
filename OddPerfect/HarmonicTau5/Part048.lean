module

public import OddPerfect.HarmonicTau5.Part047
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1410 : Closed 5 ⟨241716951468001,241778269822001,4,1⟩ := by
  exact closed_size (c:=241778269822001) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3943 : RootAt 5 3943 := by
  intro e he hdiv
  have cases := allowed_list (p:=3943) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1410

theorem htau5_1412 : Closed 5 ⟨242699289858481,242760795000361,4,1⟩ := by
  exact closed_size (c:=242760795000361) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3947 : RootAt 5 3947 := by
  intro e he hdiv
  have cases := allowed_list (p:=3947) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1412

theorem htau5_1414 : Closed 5 ⟨247655970193921,247718414967041,4,1⟩ := by
  exact closed_size (c:=247718414967041) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3967 : RootAt 5 3967 := by
  intro e he hdiv
  have cases := allowed_list (p:=3967) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1414

theorem htau5_1416 : Closed 5 ⟨253195594718641,253259084085421,4,1⟩ := by
  exact closed_size (c:=253259084085421) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3989 : RootAt 5 3989 := by
  intro e he hdiv
  have cases := allowed_list (p:=3989) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1416

theorem htau5_1418 : Closed 5 ⟨256256096016001,256320160040005,4,1⟩ := by
  exact closed_size (c:=51264032008001) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4001 : RootAt 5 4001 := by
  intro e he hdiv
  have cases := allowed_list (p:=4001) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1418

theorem htau5_1420 : Closed 5 ⟨256768864432081,256833024568121,4,1⟩ := by
  exact closed_size (c:=256833024568121) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4003 : RootAt 5 4003 := by
  intro e he hdiv
  have cases := allowed_list (p:=4003) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1420

theorem htau5_1422 : Closed 5 ⟨257796709490401,257861062138801,4,1⟩ := by
  exact closed_size (c:=257861062138801) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4007 : RootAt 5 4007 := by
  intro e he hdiv
  have cases := allowed_list (p:=4007) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1422

theorem htau5_1424 : Closed 5 ⟨259344259180561,259408901318941,4,1⟩ := by
  exact closed_size (c:=259408901318941) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4013 : RootAt 5 4013 := by
  intro e he hdiv
  have cases := allowed_list (p:=4013) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1424

theorem htau5_1426 : Closed 5 ⟨260898765874321,260963698369561,4,1⟩ := by
  exact closed_size (c:=260963698369561) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4019 : RootAt 5 4019 := by
  intro e he hdiv
  have cases := allowed_list (p:=4019) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1426

theorem htau5_1428 : Closed 5 ⟨261418484370481,261483513844205,4,1⟩ := by
  exact closed_size (c:=52296702768841) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4021 : RootAt 5 4021 := by
  intro e he hdiv
  have cases := allowed_list (p:=4021) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1428

theorem htau5_1430 : Closed 5 ⟨262982299459441,263047620447881,4,1⟩ := by
  exact closed_size (c:=263047620447881) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4027 : RootAt 5 4027 := by
  intro e he hdiv
  have cases := allowed_list (p:=4027) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1430

theorem htau5_1432 : Closed 5 ⟨268776384148801,268842781476901,4,1⟩ := by
  exact closed_size (c:=268842781476901) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4049 : RootAt 5 4049 := by
  intro e he hdiv
  have cases := allowed_list (p:=4049) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1432

theorem htau5_1434 : Closed 5 ⟨269307825181201,269374320940505,4,1⟩ := by
  exact closed_size (c:=53874864188101) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4051 : RootAt 5 4051 := by
  intro e he hdiv
  have cases := allowed_list (p:=4051) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1434

theorem htau5_1436 : Closed 5 ⟨270906877644001,270973669280501,4,1⟩ := by
  exact closed_size (c:=270973669280501) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4057 : RootAt 5 4057 := by
  intro e he hdiv
  have cases := allowed_list (p:=4057) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1436

theorem htau5_1438 : Closed 5 ⟨275205836670241,275273421600661,4,1⟩ := by
  exact closed_size (c:=275273421600661) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4073 : RootAt 5 4073 := by
  intro e he hdiv
  have cases := allowed_list (p:=4073) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1438

end OddPerfect.HarmonicChain
