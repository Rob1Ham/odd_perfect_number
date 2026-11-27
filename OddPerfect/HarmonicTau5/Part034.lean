module

public import OddPerfect.HarmonicTau5.Part033
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_990 : Closed 5 ⟨26505620986321,26517307768061,4,1⟩ := by
  exact closed_size (c:=26517307768061) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2269 : RootAt 5 2269 := by
  intro e he hdiv
  have cases := allowed_list (p:=2269) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_990

theorem htau5_992 : Closed 5 ⟨26693021907841,26704770597061,4,1⟩ := by
  exact closed_size (c:=26704770597061) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2273 : RootAt 5 2273 := by
  intro e he hdiv
  have cases := allowed_list (p:=2273) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_992

theorem htau5_994 : Closed 5 ⟨27070803167521,27082676326805,4,1⟩ := by
  exact closed_size (c:=5416535265361) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2281 : RootAt 5 2281 := by
  intro e he hdiv
  have cases := allowed_list (p:=2281) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_994

theorem htau5_996 : Closed 5 ⟨27356759876161,27368726962721,4,1⟩ := by
  exact closed_size (c:=27368726962721) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2287 : RootAt 5 2287 := by
  intro e he hdiv
  have cases := allowed_list (p:=2287) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_996

theorem htau5_998 : Closed 5 ⟨27644976106801,27657037614701,4,1⟩ := by
  exact closed_size (c:=27657037614701) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2293 : RootAt 5 2293 := by
  intro e he hdiv
  have cases := allowed_list (p:=2293) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_998

theorem htau5_1000 : Closed 5 ⟨27838381411681,27850506142261,4,1⟩ := by
  exact closed_size (c:=27850506142261) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2297 : RootAt 5 2297 := by
  intro e he hdiv
  have cases := allowed_list (p:=2297) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1000

theorem htau5_1002 : Closed 5 ⟨28424689653361,28437005376781,4,1⟩ := by
  exact closed_size (c:=28437005376781) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2309 : RootAt 5 2309 := by
  intro e he hdiv
  have cases := allowed_list (p:=2309) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1002

theorem htau5_1004 : Closed 5 ⟨28523300799841,28535648549105,4,1⟩ := by
  exact closed_size (c:=5707129709821) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2311 : RootAt 5 2311 := by
  intro e he hdiv
  have cases := allowed_list (p:=2311) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1004

theorem htau5_1006 : Closed 5 ⟨29625040666321,29637744371581,4,1⟩ := by
  exact closed_size (c:=29637744371581) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2333 : RootAt 5 2333 := by
  intro e he hdiv
  have cases := allowed_list (p:=2333) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1006

theorem htau5_1008 : Closed 5 ⟨29930976588241,29943778545721,4,1⟩ := by
  exact closed_size (c:=29943778545721) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2339 : RootAt 5 2339 := by
  intro e he hdiv
  have cases := allowed_list (p:=2339) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1008

theorem htau5_1010 : Closed 5 ⟨30033479838961,30046314659405,4,1⟩ := by
  exact closed_size (c:=6009262931881) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2341 : RootAt 5 2341 := by
  intro e he hdiv
  have cases := allowed_list (p:=2341) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1010

theorem htau5_1012 : Closed 5 ⟨30342569711281,30355503457961,4,1⟩ := by
  exact closed_size (c:=30355503457961) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2347 : RootAt 5 2347 := by
  intro e he hdiv
  have cases := allowed_list (p:=2347) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1012

theorem htau5_1014 : Closed 5 ⟨30549950894401,30562950873505,4,1⟩ := by
  exact closed_size (c:=6112590174701) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2351 : RootAt 5 2351 := by
  intro e he hdiv
  have cases := allowed_list (p:=2351) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1014

theorem htau5_1016 : Closed 5 ⟨30863013591601,30876113342701,4,1⟩ := by
  exact closed_size (c:=30876113342701) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2357 : RootAt 5 2357 := by
  intro e he hdiv
  have cases := allowed_list (p:=2357) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1016

theorem htau5_1018 : Closed 5 ⟨31602847532881,31616182067705,4,1⟩ := by
  exact closed_size (c:=6323236413541) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2371 : RootAt 5 2371 := by
  intro e he hdiv
  have cases := allowed_list (p:=2371) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1018

end OddPerfect.HarmonicChain
