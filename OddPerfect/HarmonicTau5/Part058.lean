module

public import OddPerfect.HarmonicTau5.Part057
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1710 : Closed 5 ⟨752194746016561,752338404295021,4,1⟩ := by
  exact closed_size (c:=752338404295021) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5237 : RootAt 5 5237 := by
  intro e he hdiv
  have cases := allowed_list (p:=5237) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1710

theorem htau5_1712 : Closed 5 ⟨766078382090641,766224024368605,4,1⟩ := by
  exact closed_size (c:=153244804873721) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5261 : RootAt 5 5261 := by
  intro e he hdiv
  have cases := allowed_list (p:=5261) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1712

theorem htau5_1714 : Closed 5 ⟨773091832911841,773238474003061,4,1⟩ := by
  exact closed_size (c:=773238474003061) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5273 : RootAt 5 5273 := by
  intro e he hdiv
  have cases := allowed_list (p:=5273) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1714

theorem htau5_1716 : Closed 5 ⟨776616562001281,776763704207041,4,1⟩ := by
  exact closed_size (c:=776763704207041) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5279 : RootAt 5 5279 := by
  intro e he hdiv
  have cases := allowed_list (p:=5279) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1716

theorem htau5_1718 : Closed 5 ⟨777794145659521,777941455156805,4,1⟩ := by
  exact closed_size (c:=155588291031361) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5281 : RootAt 5 5281 := by
  intro e he hdiv
  have cases := allowed_list (p:=5281) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1718

theorem htau5_1720 : Closed 5 ⟨787263092287681,787411744684261,4,1⟩ := by
  exact closed_size (c:=787411744684261) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5297 : RootAt 5 5297 := by
  intro e he hdiv
  have cases := allowed_list (p:=5297) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1720

theorem htau5_1722 : Closed 5 ⟨790836141432481,790985299512721,4,1⟩ := by
  exact closed_size (c:=790985299512721) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5303 : RootAt 5 5303 := by
  intro e he hdiv
  have cases := allowed_list (p:=5303) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1722

theorem htau5_1724 : Closed 5 ⟨794421339201361,794571004110781,4,1⟩ := by
  exact closed_size (c:=794571004110781) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5309 : RootAt 5 5309 := by
  intro e he hdiv
  have cases := allowed_list (p:=5309) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1724

theorem htau5_1726 : Closed 5 ⟨802834199880241,802985051853161,4,1⟩ := by
  exact closed_size (c:=802985051853161) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5323 : RootAt 5 5323 := by
  intro e he hdiv
  have cases := allowed_list (p:=5323) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1726

theorem htau5_1728 : Closed 5 ⟨808884167110321,809035870817581,4,1⟩ := by
  exact closed_size (c:=809035870817581) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5333 : RootAt 5 5333 := by
  intro e he hdiv
  have cases := allowed_list (p:=5333) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1728

theorem htau5_1730 : Closed 5 ⟨817411486787281,817564388299961,4,1⟩ := by
  exact closed_size (c:=817564388299961) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5347 : RootAt 5 5347 := by
  intro e he hdiv
  have cases := allowed_list (p:=5347) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1730

theorem htau5_1732 : Closed 5 ⟨819860199506401,820013444403505,4,1⟩ := by
  exact closed_size (c:=164002688880701) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5351 : RootAt 5 5351 := by
  intro e he hdiv
  have cases := allowed_list (p:=5351) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1732

theorem htau5_1734 : Closed 5 ⟨838401348535921,838557185217805,4,1⟩ := by
  exact closed_size (c:=167711437043561) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5381 : RootAt 5 5381 := by
  intro e he hdiv
  have cases := allowed_list (p:=5381) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1734

theorem htau5_1736 : Closed 5 ⟨842146992813361,842303351334121,4,1⟩ := by
  exact closed_size (c:=842303351334121) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5387 : RootAt 5 5387 := by
  intro e he hdiv
  have cases := allowed_list (p:=5387) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1736

theorem htau5_1738 : Closed 5 ⟨845905173633601,846062055156901,4,1⟩ := by
  exact closed_size (c:=846062055156901) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5393 : RootAt 5 5393 := by
  intro e he hdiv
  have cases := allowed_list (p:=5393) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1738

end OddPerfect.HarmonicChain
