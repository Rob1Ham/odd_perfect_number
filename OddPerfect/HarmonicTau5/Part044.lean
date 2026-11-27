module

public import OddPerfect.HarmonicTau5.Part043
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1290 : Closed 5 ⟨144816217349521,144857975197661,4,1⟩ := by
  exact closed_size (c:=144857975197661) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3469 : RootAt 5 3469 := by
  intro e he hdiv
  have cases := allowed_list (p:=3469) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1290

theorem htau5_1292 : Closed 5 ⟨148524943300561,148567500590905,4,1⟩ := by
  exact closed_size (c:=29713500118181) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3491 : RootAt 5 3491 := by
  intro e he hdiv
  have cases := allowed_list (p:=3491) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1292

theorem htau5_1294 : Closed 5 ⟨149891073486001,149933923993001,4,1⟩ := by
  exact closed_size (c:=149933923993001) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3499 : RootAt 5 3499 := by
  intro e he hdiv
  have cases := allowed_list (p:=3499) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1294

theorem htau5_1296 : Closed 5 ⟨151957912148641,152001205001105,4,1⟩ := by
  exact closed_size (c:=30400241000221) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3511 : RootAt 5 3511 := by
  intro e he hdiv
  have cases := allowed_list (p:=3511) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1296

theorem htau5_1298 : Closed 5 ⟨152999310365521,153042825527741,4,1⟩ := by
  exact closed_size (c:=153042825527741) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3517 : RootAt 5 3517 := by
  intro e he hdiv
  have cases := allowed_list (p:=3517) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1298

theorem htau5_1300 : Closed 5 ⟨154746857593441,154790744960881,4,1⟩ := by
  exact closed_size (c:=154790744960881) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3527 : RootAt 5 3527 := by
  intro e he hdiv
  have cases := allowed_list (p:=3527) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1300

theorem htau5_1302 : Closed 5 ⟨155098155653281,155142117715541,4,1⟩ := by
  exact closed_size (c:=155142117715541) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3529 : RootAt 5 3529 := by
  intro e he hdiv
  have cases := allowed_list (p:=3529) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1302

theorem htau5_1304 : Closed 5 ⟨155802545803921,155846657509981,4,1⟩ := by
  exact closed_size (c:=155846657509981) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3533 : RootAt 5 3533 := by
  intro e he hdiv
  have cases := allowed_list (p:=3533) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1304

theorem htau5_1306 : Closed 5 ⟨156863626279441,156907963087321,4,1⟩ := by
  exact closed_size (c:=156907963087321) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3539 : RootAt 5 3539 := by
  intro e he hdiv
  have cases := allowed_list (p:=3539) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1306

theorem htau5_1308 : Closed 5 ⟨157218521219761,157262933231405,4,1⟩ := by
  exact closed_size (c:=31452586646281) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3541 : RootAt 5 3541 := by
  intro e he hdiv
  have cases := allowed_list (p:=3541) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1308

theorem htau5_1310 : Closed 5 ⟨158286819901681,158331458034761,4,1⟩ := by
  exact closed_size (c:=158331458034761) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3547 : RootAt 5 3547 := by
  intro e he hdiv
  have cases := allowed_list (p:=3547) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1310

theorem htau5_1312 : Closed 5 ⟨160079404758001,160124421463501,4,1⟩ := by
  exact closed_size (c:=160124421463501) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3557 : RootAt 5 3557 := by
  intro e he hdiv
  have cases := allowed_list (p:=3557) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1312

theorem htau5_1314 : Closed 5 ⟨160439740923361,160484833599281,4,1⟩ := by
  exact closed_size (c:=160484833599281) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3559 : RootAt 5 3559 := by
  intro e he hdiv
  have cases := allowed_list (p:=3559) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1314

theorem htau5_1316 : Closed 5 ⟨162614549665681,162660099959705,4,1⟩ := by
  exact closed_size (c:=32532019991941) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3571 : RootAt 5 3571 := by
  intro e he hdiv
  have cases := allowed_list (p:=3571) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1316

theorem htau5_1318 : Closed 5 ⟨164443716720721,164489650719805,4,1⟩ := by
  exact closed_size (c:=32897930143961) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3581 : RootAt 5 3581 := by
  intro e he hdiv
  have cases := allowed_list (p:=3581) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1318

end OddPerfect.HarmonicChain
