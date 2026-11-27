module

public import OddPerfect.HarmonicTau5.Part056
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1680 : Closed 5 ⟨677050860080401,677183615151005,4,1⟩ := by
  exact closed_size (c:=135436723030201) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5101 : RootAt 5 5101 := by
  intro e he hdiv
  have cases := allowed_list (p:=5101) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1680

theorem htau5_1682 : Closed 5 ⟨680241981939601,680375205986201,4,1⟩ := by
  exact closed_size (c:=680375205986201) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5107 : RootAt 5 5107 := by
  intro e he hdiv
  have cases := allowed_list (p:=5107) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1682

theorem htau5_1684 : Closed 5 ⟨683444370987361,683578065113141,4,1⟩ := by
  exact closed_size (c:=683578065113141) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5113 : RootAt 5 5113 := by
  intro e he hdiv
  have cases := allowed_list (p:=5113) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1684

theorem htau5_1686 : Closed 5 ⟨686658053713921,686792219023361,4,1⟩ := by
  exact closed_size (c:=686792219023361) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5119 : RootAt 5 5119 := by
  intro e he hdiv
  have cases := allowed_list (p:=5119) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1686

theorem htau5_1688 : Closed 5 ⟨701805347408881,701941726217161,4,1⟩ := by
  exact closed_size (c:=701941726217161) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5147 : RootAt 5 5147 := by
  intro e he hdiv
  have cases := allowed_list (p:=5147) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1688

theorem htau5_1690 : Closed 5 ⟨705083529521281,705220385796421,4,1⟩ := by
  exact closed_size (c:=705220385796421) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5153 : RootAt 5 5153 := by
  intro e he hdiv
  have cases := allowed_list (p:=5153) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1690

theorem htau5_1692 : Closed 5 ⟨712777277056321,712915251751841,4,1⟩ := by
  exact closed_size (c:=712915251751841) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5167 : RootAt 5 5167 := by
  intro e he hdiv
  have cases := allowed_list (p:=5167) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1692

theorem htau5_1694 : Closed 5 ⟨714987009256081,715125304615705,4,1⟩ := by
  exact closed_size (c:=143025060923141) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5171 : RootAt 5 5171 := by
  intro e he hdiv
  have cases := allowed_list (p:=5171) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1694

theorem htau5_1696 : Closed 5 ⟨719421883405681,719560821583241,4,1⟩ := by
  exact closed_size (c:=719560821583241) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5179 : RootAt 5 5179 := by
  intro e he hdiv
  have cases := allowed_list (p:=5179) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1696

theorem htau5_1698 : Closed 5 ⟨724994451369841,725134195867021,4,1⟩ := by
  exact closed_size (c:=725134195867021) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5189 : RootAt 5 5189 := by
  intro e he hdiv
  have cases := allowed_list (p:=5189) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1698

theorem htau5_1700 : Closed 5 ⟨729475763598481,729616155392861,4,1⟩ := by
  exact closed_size (c:=729616155392861) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5197 : RootAt 5 5197 := by
  intro e he hdiv
  have cases := allowed_list (p:=5197) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1700

theorem htau5_1702 : Closed 5 ⟨736236644609761,736378011092981,4,1⟩ := by
  exact closed_size (c:=736378011092981) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5209 : RootAt 5 5209 := by
  intro e he hdiv
  have cases := allowed_list (p:=5209) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1702

theorem htau5_1704 : Closed 5 ⟨746465946897841,746608783856681,4,1⟩ := by
  exact closed_size (c:=746608783856681) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5227 : RootAt 5 5227 := by
  intro e he hdiv
  have cases := allowed_list (p:=5227) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1704

theorem htau5_1706 : Closed 5 ⟨748753525216321,748896690326305,4,1⟩ := by
  exact closed_size (c:=149779338065261) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5231 : RootAt 5 5231 := by
  intro e he hdiv
  have cases := allowed_list (p:=5231) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1706

theorem htau5_1708 : Closed 5 ⟨749899284035521,750042613409381,4,1⟩ := by
  exact closed_size (c:=750042613409381) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5233 : RootAt 5 5233 := by
  intro e he hdiv
  have cases := allowed_list (p:=5233) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1708

end OddPerfect.HarmonicChain
