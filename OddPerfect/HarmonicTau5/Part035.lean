module

public import OddPerfect.HarmonicTau5.Part034
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1020 : Closed 5 ⟨31923957716641,31937393725781,4,1⟩ := by
  exact closed_size (c:=31937393725781) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2377 : RootAt 5 2377 := by
  intro e he hdiv
  have cases := allowed_list (p:=2377) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1020

theorem htau5_1022 : Closed 5 ⟨32139386443921,32152890387805,4,1⟩ := by
  exact closed_size (c:=6430578077561) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2381 : RootAt 5 2381 := by
  intro e he hdiv
  have cases := allowed_list (p:=2381) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1022

theorem htau5_1024 : Closed 5 ⟨32247508758721,32261046755681,4,1⟩ := by
  exact closed_size (c:=32261046755681) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2383 : RootAt 5 2383 := by
  intro e he hdiv
  have cases := allowed_list (p:=2383) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1024

theorem htau5_1026 : Closed 5 ⟨32573512997041,32587153496621,4,1⟩ := by
  exact closed_size (c:=32587153496621) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2389 : RootAt 5 2389 := by
  intro e he hdiv
  have cases := allowed_list (p:=2389) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1026

theorem htau5_1028 : Closed 5 ⟨32792218149601,32805927270901,4,1⟩ := by
  exact closed_size (c:=32805927270901) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2393 : RootAt 5 2393 := by
  intro e he hdiv
  have cases := allowed_list (p:=2393) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1028

theorem htau5_1030 : Closed 5 ⟨33122338550401,33136151035201,4,1⟩ := by
  exact closed_size (c:=33136151035201) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2399 : RootAt 5 2399 := by
  intro e he hdiv
  have cases := allowed_list (p:=2399) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1030

theorem htau5_1032 : Closed 5 ⟨33790050552241,33804071320105,4,1⟩ := by
  exact closed_size (c:=6760814264021) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2411 : RootAt 5 2411 := by
  intro e he hdiv
  have cases := allowed_list (p:=2411) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1032

theorem htau5_1034 : Closed 5 ⟨34127667088321,34141792778341,4,1⟩ := by
  exact closed_size (c:=34141792778341) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2417 : RootAt 5 2417 := by
  intro e he hdiv
  have cases := allowed_list (p:=2417) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1034

theorem htau5_1036 : Closed 5 ⟨34467807323041,34482038457361,4,1⟩ := by
  exact closed_size (c:=34482038457361) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2423 : RootAt 5 2423 := by
  intro e he hdiv
  have cases := allowed_list (p:=2423) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1036

theorem htau5_1038 : Closed 5 ⟨35271352782961,35285831991821,4,1⟩ := by
  exact closed_size (c:=35285831991821) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2437 : RootAt 5 2437 := by
  intro e he hdiv
  have cases := allowed_list (p:=2437) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1038

theorem htau5_1040 : Closed 5 ⟨35503495827361,35518046440405,4,1⟩ := by
  exact closed_size (c:=7103609288081) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2441 : RootAt 5 2441 := by
  intro e he hdiv
  have cases := allowed_list (p:=2441) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1040

theorem htau5_1042 : Closed 5 ⟨35853856620481,35868514779361,4,1⟩ := by
  exact closed_size (c:=35868514779361) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2447 : RootAt 5 2447 := by
  intro e he hdiv
  have cases := allowed_list (p:=2447) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1042

theorem htau5_1044 : Closed 5 ⟨36562351115761,36577225953481,4,1⟩ := by
  exact closed_size (c:=36577225953481) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2459 : RootAt 5 2459 := by
  intro e he hdiv
  have cases := allowed_list (p:=2459) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1044

theorem htau5_1046 : Closed 5 ⟨37040479315921,37055499786041,4,1⟩ := by
  exact closed_size (c:=37055499786041) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2467 : RootAt 5 2467 := by
  intro e he hdiv
  have cases := allowed_list (p:=2467) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1046

theorem htau5_1048 : Closed 5 ⟨37402141201441,37417271517461,4,1⟩ := by
  exact closed_size (c:=37417271517461) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2473 : RootAt 5 2473 := by
  intro e he hdiv
  have cases := allowed_list (p:=2473) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1048

end OddPerfect.HarmonicChain
