module

public import OddPerfect.HarmonicTau5.Part048
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1440 : Closed 5 ⟨276831063574081,276898947601441,4,1⟩ := by
  exact closed_size (c:=276898947601441) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4079 : RootAt 5 4079 := by
  intro e he hdiv
  have cases := allowed_list (p:=4079) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1440

theorem htau5_1442 : Closed 5 ⟨280103101710961,280171586576905,4,1⟩ := by
  exact closed_size (c:=56034317315381) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4091 : RootAt 5 4091 := by
  intro e he hdiv
  have cases := allowed_list (p:=4091) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1442

theorem htau5_1444 : Closed 5 ⟨280651248517201,280719833866301,4,1⟩ := by
  exact closed_size (c:=280719833866301) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4093 : RootAt 5 4093 := by
  intro e he hdiv
  have cases := allowed_list (p:=4093) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1444

theorem htau5_1446 : Closed 5 ⟨282300516843601,282369404231801,4,1⟩ := by
  exact closed_size (c:=282369404231801) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4099 : RootAt 5 4099 := by
  intro e he hdiv
  have cases := allowed_list (p:=4099) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1446

theorem htau5_1448 : Closed 5 ⟨285620849903041,285690344027105,4,1⟩ := by
  exact closed_size (c:=57138068805421) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4111 : RootAt 5 4111 := by
  intro e he hdiv
  have cases := allowed_list (p:=4111) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1448

theorem htau5_1450 : Closed 5 ⟨290093418272641,290163726905281,4,1⟩ := by
  exact closed_size (c:=290163726905281) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4127 : RootAt 5 4127 := by
  intro e he hdiv
  have cases := allowed_list (p:=4127) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1450

theorem htau5_1452 : Closed 5 ⟨290656159946881,290726570838341,4,1⟩ := by
  exact closed_size (c:=290726570838341) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4129 : RootAt 5 4129 := by
  intro e he hdiv
  have cases := allowed_list (p:=4129) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1452

theorem htau5_1454 : Closed 5 ⟨291784099092721,291854714799181,4,1⟩ := by
  exact closed_size (c:=291854714799181) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4133 : RootAt 5 4133 := by
  intro e he hdiv
  have cases := allowed_list (p:=4133) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1454

theorem htau5_1456 : Closed 5 ⟨293482159205041,293553082878121,4,1⟩ := by
  exact closed_size (c:=293553082878121) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4139 : RootAt 5 4139 := by
  intro e he hdiv
  have cases := allowed_list (p:=4139) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1456

theorem htau5_1458 : Closed 5 ⟨297473117213281,297544762954421,4,1⟩ := by
  exact closed_size (c:=297544762954421) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4153 : RootAt 5 4153 := by
  intro e he hdiv
  have cases := allowed_list (p:=4153) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1458

theorem htau5_1460 : Closed 5 ⟨298620829861201,298692682803901,4,1⟩ := by
  exact closed_size (c:=298692682803901) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4157 : RootAt 5 4157 := by
  intro e he hdiv
  have cases := allowed_list (p:=4157) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1460

theorem htau5_1462 : Closed 5 ⟨299195929992961,299267886686081,4,1⟩ := by
  exact closed_size (c:=299267886686081) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4159 : RootAt 5 4159 := by
  intro e he hdiv
  have cases := allowed_list (p:=4159) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1462

theorem htau5_1464 : Closed 5 ⟨304409289234241,304482184178981,4,1⟩ := by
  exact closed_size (c:=304482184178981) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4177 : RootAt 5 4177 := by
  intro e he hdiv
  have cases := allowed_list (p:=4177) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1464

theorem htau5_1466 : Closed 5 ⟨311466057856801,311540216442005,4,1⟩ := by
  exact closed_size (c:=62308043288401) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4201 : RootAt 5 4201 := by
  intro e he hdiv
  have cases := allowed_list (p:=4201) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1466

theorem htau5_1468 : Closed 5 ⟨314442301015441,314516990398105,4,1⟩ := by
  exact closed_size (c:=62903398079621) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4211 : RootAt 5 4211 := by
  intro e he hdiv
  have cases := allowed_list (p:=4211) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1468

end OddPerfect.HarmonicChain
