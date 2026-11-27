module

public import OddPerfect.HarmonicTau5.Part024
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_720 : Closed 5 ⟨2296318960321,2298185886305,4,1⟩ := by
  exact closed_size (c:=459637177261) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1231 : RootAt 5 1231 := by
  intro e he hdiv
  have cases := allowed_list (p:=1231) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_720

theorem htau5_722 : Closed 5 ⟨2341417168561,2343311519021,4,1⟩ := by
  exact closed_size (c:=2343311519021) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1237 : RootAt 5 1237 := by
  intro e he hdiv
  have cases := allowed_list (p:=1237) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_722

theorem htau5_724 : Closed 5 ⟨2433603120001,2435553122501,4,1⟩ := by
  exact closed_size (c:=2435553122501) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1249 : RootAt 5 1249 := by
  intro e he hdiv
  have cases := allowed_list (p:=1249) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_724

theorem htau5_726 : Closed 5 ⟨2512481776561,2514478979881,4,1⟩ := by
  exact closed_size (c:=2514478979881) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1259 : RootAt 5 1259 := by
  intro e he hdiv
  have cases := allowed_list (p:=1259) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_726

theorem htau5_728 : Closed 5 ⟨2659277071441,2661361144381,4,1⟩ := by
  exact closed_size (c:=2661361144381) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1277 : RootAt 5 1277 := by
  intro e he hdiv
  have cases := allowed_list (p:=1277) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_728

theorem htau5_730 : Closed 5 ⟨2675975777281,2678069655041,4,1⟩ := by
  exact closed_size (c:=2678069655041) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1279 : RootAt 5 1279 := by
  intro e he hdiv
  have cases := allowed_list (p:=1279) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_730

theorem htau5_732 : Closed 5 ⟨2709608995921,2711722575481,4,1⟩ := by
  exact closed_size (c:=2711722575481) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1283 : RootAt 5 1283 := by
  intro e he hdiv
  have cases := allowed_list (p:=1283) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_732

theorem htau5_734 : Closed 5 ⟨2760652033441,2762795396821,4,1⟩ := by
  exact closed_size (c:=2762795396821) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1289 : RootAt 5 1289 := by
  intro e he hdiv
  have cases := allowed_list (p:=1289) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_734

theorem htau5_736 : Closed 5 ⟨2777825555761,2779978908905,4,1⟩ := by
  exact closed_size (c:=555995781781) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1291 : RootAt 5 1291 := by
  intro e he hdiv
  have cases := allowed_list (p:=1291) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_736

theorem htau5_738 : Closed 5 ⟨2829827119681,2832010628261,4,1⟩ := by
  exact closed_size (c:=2832010628261) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1297 : RootAt 5 1297 := by
  intro e he hdiv
  have cases := allowed_list (p:=1297) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_738

theorem htau5_740 : Closed 5 ⟨2864898145201,2867101913005,4,1⟩ := by
  exact closed_size (c:=573420382601) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1301 : RootAt 5 1301 := by
  intro e he hdiv
  have cases := allowed_list (p:=1301) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_740

theorem htau5_742 : Closed 5 ⟨2882555400481,2884769344721,4,1⟩ := by
  exact closed_size (c:=2884769344721) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1303 : RootAt 5 1303 := by
  intro e he hdiv
  have cases := allowed_list (p:=1303) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_742

theorem htau5_744 : Closed 5 ⟨2918114646001,2920349037001,4,1⟩ := by
  exact closed_size (c:=2920349037001) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1307 : RootAt 5 1307 := by
  intro e he hdiv
  have cases := allowed_list (p:=1307) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_744

theorem htau5_746 : Closed 5 ⟨3026768337121,3029064822961,4,1⟩ := by
  exact closed_size (c:=3029064822961) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1319 : RootAt 5 1319 := by
  intro e he hdiv
  have cases := allowed_list (p:=1319) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_746

theorem htau5_748 : Closed 5 ⟨3045168091681,3047475037205,4,1⟩ := by
  exact closed_size (c:=609495007441) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1321 : RootAt 5 1321 := by
  intro e he hdiv
  have cases := allowed_list (p:=1321) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_748

end OddPerfect.HarmonicChain
