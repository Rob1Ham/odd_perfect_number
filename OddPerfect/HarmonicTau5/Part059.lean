module

public import OddPerfect.HarmonicTau5.Part058
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1740 : Closed 5 ⟨849675918938401,849833324629201,4,1⟩ := by
  exact closed_size (c:=849833324629201) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5399 : RootAt 5 5399 := by
  intro e he hdiv
  have cases := allowed_list (p:=5399) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1740

theorem htau5_1742 : Closed 5 ⟨854723172451201,854881278846401,4,1⟩ := by
  exact closed_size (c:=854881278846401) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5407 : RootAt 5 5407 := by
  intro e he hdiv
  have cases := allowed_list (p:=5407) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1742

theorem htau5_1744 : Closed 5 ⟨858523343723761,858681977009741,4,1⟩ := by
  exact closed_size (c:=858681977009741) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5413 : RootAt 5 5413 := by
  intro e he hdiv
  have cases := allowed_list (p:=5413) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1744

theorem htau5_1746 : Closed 5 ⟨861063821644321,861222806840341,4,1⟩ := by
  exact closed_size (c:=861222806840341) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5417 : RootAt 5 5417 := by
  intro e he hdiv
  have cases := allowed_list (p:=5417) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1746

theorem htau5_1748 : Closed 5 ⟨862336172844721,862495334190761,4,1⟩ := by
  exact closed_size (c:=862495334190761) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5419 : RootAt 5 5419 := by
  intro e he hdiv
  have cases := allowed_list (p:=5419) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1748

theorem htau5_1750 : Closed 5 ⟨869999916969121,870160137948305,4,1⟩ := by
  exact closed_size (c:=174032027589661) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5431 : RootAt 5 5431 := by
  intro e he hdiv
  have cases := allowed_list (p:=5431) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1750

theorem htau5_1752 : Closed 5 ⟨873850888218961,874011640773821,4,1⟩ := by
  exact closed_size (c:=874011640773821) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5437 : RootAt 5 5437 := by
  intro e he hdiv
  have cases := allowed_list (p:=5437) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1752

theorem htau5_1754 : Closed 5 ⟨876425295279361,876586402870405,4,1⟩ := by
  exact closed_size (c:=175317280574081) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5441 : RootAt 5 5441 := by
  intro e he hdiv
  have cases := allowed_list (p:=5441) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1754

theorem htau5_1756 : Closed 5 ⟨877714629810001,877875915115001,4,1⟩ := by
  exact closed_size (c:=877875915115001) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5443 : RootAt 5 5443 := by
  intro e he hdiv
  have cases := allowed_list (p:=5443) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1756

theorem htau5_1758 : Closed 5 ⟨881591169943201,881752989174101,4,1⟩ := by
  exact closed_size (c:=881752989174101) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5449 : RootAt 5 5449 := by
  intro e he hdiv
  have cases := allowed_list (p:=5449) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1758

theorem htau5_1760 : Closed 5 ⟨895915105649281,896078892688705,4,1⟩ := by
  exact closed_size (c:=179215778537741) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5471 : RootAt 5 5471 := by
  intro e he hdiv
  have cases := allowed_list (p:=5471) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1760

theorem htau5_1762 : Closed 5 ⟨899851746105841,900016072575181,4,1⟩ := by
  exact closed_size (c:=900016072575181) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5477 : RootAt 5 5477 := by
  intro e he hdiv
  have cases := allowed_list (p:=5477) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1762

theorem htau5_1764 : Closed 5 ⟨901166837952481,901331344494641,4,1⟩ := by
  exact closed_size (c:=901331344494641) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5479 : RootAt 5 5479 := by
  intro e he hdiv
  have cases := allowed_list (p:=5479) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1764

theorem htau5_1766 : Closed 5 ⟨903801345497521,903966212579881,4,1⟩ := by
  exact closed_size (c:=903966212579881) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5483 : RootAt 5 5483 := by
  intro e he hdiv
  have cases := allowed_list (p:=5483) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1766

theorem htau5_1768 : Closed 5 ⟨915728181522001,915894677555005,4,1⟩ := by
  exact closed_size (c:=183178935511001) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5501 : RootAt 5 5501 := by
  intro e he hdiv
  have cases := allowed_list (p:=5501) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1768

end OddPerfect.HarmonicChain
