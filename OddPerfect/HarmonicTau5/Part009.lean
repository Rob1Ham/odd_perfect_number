module

public import OddPerfect.HarmonicTau5.Part008
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_240 : Closed 5 ⟨38950081,39449441,4,1⟩ := by
  apply closed_split (c:=39449441) (p:=39449441) (by decide +kernel) (by decide +kernel) htauPrime5_39449441 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=39449441) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_239

theorem htauRoot5_79 : RootAt 5 79 := by
  intro e he hdiv
  have cases := allowed_list (p:=79) (r:=5) (E:=8) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_240

theorem htau5_242 : Closed 5 ⟨22881943190780047037,23163299315939850396,6,3⟩ := by
  exact closed_size (c:=1930274942994987533) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_243 : Closed 5 ⟨229666063805859332110369,232490037541649477462294,7,3⟩ := by
  exact closed_size (c:=116245018770824738731147) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_244 : Closed 5 ⟨2305158282419410116391773653,2333502506807843366488082520,8,3⟩ := by
  exact closed_size (c:=19445854223398694720734021) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_245 : Closed 5 ⟨2279759210001001,2307561199037642,5,2⟩ := by
  apply closed_split (c:=1153780599518821) (p:=10037) (by decide +kernel) (by decide +kernel) htauPrime5_10037 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=10037) (r:=1) (E:=4) [1, 2, 3] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_242
  · exact htau5_243
  · exact htau5_244

theorem htau5_246 : Closed 5 ⟨47458321,48037081,4,1⟩ := by
  apply closed_split (c:=48037081) (p:=48037081) (by decide +kernel) (by decide +kernel) htauPrime5_48037081 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=48037081) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_245

theorem htauRoot5_83 : RootAt 5 83 := by
  intro e he hdiv
  have cases := allowed_list (p:=83) (r:=5) (E:=8) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_246

theorem htau5_248 : Closed 5 ⟨29958227974921,30342573391233,6,2⟩ := by
  exact closed_size (c:=10114191130411) [(131,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_131) (by decide +kernel)

theorem htau5_249 : Closed 5 ⟨14304484651693254001,14488002329330337005,8,2⟩ := by
  exact closed_size (c:=2897600465866067401) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_250 : Closed 5 ⟨62742241,63455221,4,1⟩ := by
  apply closed_split (c:=63455221) (p:=691) (by decide +kernel) (by decide +kernel) htauPrime5_691 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=691) (r:=1) (E:=6) [2, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_248
  · exact htau5_249

theorem htauRoot5_89 : RootAt 5 89 := by
  intro e he hdiv
  have cases := allowed_list (p:=89) (r:=5) (E:=8) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_250

theorem htau5_252 : Closed 5 ⟨23223089521201,23465086152442,5,2⟩ := by
  exact closed_size (c:=11732543076221) [(4231,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_4231) (by decide +kernel)

theorem htau5_253 : Closed 5 ⟨6091904066290967521,6155384864684189343,6,2⟩ := by
  exact closed_size (c:=2051794954894729781) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_254 : Closed 5 ⟨88529281,89451461,4,1⟩ := by
  apply closed_split (c:=89451461) (p:=262321) (by decide +kernel) (by decide +kernel) htauPrime5_262321 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=262321) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_252
  · exact htau5_253

theorem htauRoot5_97 : RootAt 5 97 := by
  intro e he hdiv
  have cases := allowed_list (p:=97) (r:=5) (E:=8) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_254

theorem htau5_256 : Closed 5 ⟨25086985533481,25389565080865,6,2⟩ := by
  exact closed_size (c:=5077913016173) [(31,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact (by norm_num)) (by decide +kernel)

theorem htau5_257 : Closed 5 ⟨6047995559397132961,6120941790969709525,8,2⟩ := by
  exact closed_size (c:=244837671638788381) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_258 : Closed 5 ⟨104060401,105101005,4,1⟩ := by
  apply closed_split (c:=21020201) (p:=491) (by decide +kernel) (by decide +kernel) htauPrime5_491 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=491) (r:=1) (E:=6) [2, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_256
  · exact htau5_257

theorem htauRoot5_101 : RootAt 5 101 := by
  intro e he hdiv
  have cases := allowed_list (p:=101) (r:=5) (E:=8) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_258

theorem htau5_260 : Closed 5 ⟨112550881,113654321,4,1⟩ := by
  exact closed_size (c:=113654321) [(10332211,1),(11,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl
    · exact htauPrime5_10332211
    · exact (by norm_num)) (by decide +kernel)

theorem htauRoot5_103 : RootAt 5 103 := by
  intro e he hdiv
  have cases := allowed_list (p:=103) (r:=5) (E:=8) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_260

theorem htau5_262 : Closed 5 ⟨131079601,132316201,4,1⟩ := by
  exact closed_size (c:=132316201) [(627091,1),(211,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl
    · exact htauPrime5_627091
    · exact htauPrime5_211) (by decide +kernel)

theorem htauRoot5_107 : RootAt 5 107 := by
  intro e he hdiv
  have cases := allowed_list (p:=107) (r:=5) (E:=8) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_262

theorem htau5_264 : Closed 5 ⟨123904305957741901,125714940773646406,7,3⟩ := by
  exact closed_size (c:=62857470386823203) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_265 : Closed 5 ⟨2981261505649227879961,3024827195179331757579,8,3⟩ := by
  exact closed_size (c:=1008275731726443919193) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_266 : Closed 5 ⟨71732133087426072019741621,72780367143215126044691132,9,3⟩ := by
  exact closed_size (c:=18195091785803781511172783) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_267 : Closed 5 ⟨5149590871441,5224625582813,6,2⟩ := by
  apply closed_split (c:=5224625582813) (p:=24061) (by decide +kernel) (by decide +kernel) htauPrime5_24061 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=24061) (r:=1) (E:=4) [1, 2, 3] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_264
  · exact htau5_265
  · exact htau5_266

theorem htau5_268 : Closed 5 ⟨187862224581039121,190599593239915805,8,2⟩ := by
  exact closed_size (c:=38119918647983161) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_269 : Closed 5 ⟨6853401814940888173201,6953263761012721796957,10,2⟩ := by
  exact closed_size (c:=6953263761012721796957) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

end OddPerfect.HarmonicChain
