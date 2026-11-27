module

public import OddPerfect.HarmonicTau5.Part027
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_810 : Closed 5 ⟨6029426229121,6033276437441,4,1⟩ := by
  exact closed_size (c:=6033276437441) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1567 : RootAt 5 1567 := by
  intro e he hdiv
  have cases := allowed_list (p:=1567) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_810

theorem htau5_812 : Closed 5 ⟨6091226377681,6095106139705,4,1⟩ := by
  exact closed_size (c:=1219021227941) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1571 : RootAt 5 1571 := by
  intro e he hdiv
  have cases := allowed_list (p:=1571) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_812

theorem htau5_814 : Closed 5 ⟨6216250684081,6220190006441,4,1⟩ := by
  exact closed_size (c:=6220190006441) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1579 : RootAt 5 1579 := by
  intro e he hdiv
  have cases := allowed_list (p:=1579) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_814

theorem htau5_816 : Closed 5 ⟨6279479680321,6283449010081,4,1⟩ := by
  exact closed_size (c:=6283449010081) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1583 : RootAt 5 1583 := by
  intro e he hdiv
  have cases := allowed_list (p:=1583) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_816

theorem htau5_818 : Closed 5 ⟨6504586067281,6508661622461,4,1⟩ := by
  exact closed_size (c:=6508661622461) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1597 : RootAt 5 1597 := by
  intro e he hdiv
  have cases := allowed_list (p:=1597) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_818

theorem htau5_820 : Closed 5 ⟨6569999366401,6574105616005,4,1⟩ := by
  exact closed_size (c:=1314821123201) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1601 : RootAt 5 1601 := by
  intro e he hdiv
  have cases := allowed_list (p:=1601) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_820

theorem htau5_822 : Closed 5 ⟨6669042837601,6673195417201,4,1⟩ := by
  exact closed_size (c:=6673195417201) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1607 : RootAt 5 1607 := by
  intro e he hdiv
  have cases := allowed_list (p:=1607) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_822

theorem htau5_824 : Closed 5 ⟨6702304832161,6706472932181,4,1⟩ := by
  exact closed_size (c:=6706472932181) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1609 : RootAt 5 1609 := by
  intro e he hdiv
  have cases := allowed_list (p:=1609) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_824

theorem htau5_826 : Closed 5 ⟨6769201929361,6773401186141,4,1⟩ := by
  exact closed_size (c:=6773401186141) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1613 : RootAt 5 1613 := by
  intro e he hdiv
  have cases := allowed_list (p:=1613) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_826

theorem htau5_828 : Closed 5 ⟨6870484987921,6874731270361,4,1⟩ := by
  exact closed_size (c:=6874731270361) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1619 : RootAt 5 1619 := by
  intro e he hdiv
  have cases := allowed_list (p:=1619) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_828

theorem htau5_830 : Closed 5 ⟨6904497224881,6908759260205,4,1⟩ := by
  exact closed_size (c:=1381751852041) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1621 : RootAt 5 1621 := by
  intro e he hdiv
  have cases := allowed_list (p:=1621) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_830

theorem htau5_832 : Closed 5 ⟨7007291942641,7011601470281,4,1⟩ := by
  exact closed_size (c:=7011601470281) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1627 : RootAt 5 1627 := by
  intro e he hdiv
  have cases := allowed_list (p:=1627) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_832

theorem htau5_834 : Closed 5 ⟨7181161893361,7185551356621,4,1⟩ := by
  exact closed_size (c:=7185551356621) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1637 : RootAt 5 1637 := by
  intro e he hdiv
  have cases := allowed_list (p:=1637) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_834

theorem htau5_836 : Closed 5 ⟨7538588431201,7543140718901,4,1⟩ := by
  exact closed_size (c:=7543140718901) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1657 : RootAt 5 1657 := by
  intro e he hdiv
  have cases := allowed_list (p:=1657) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_836

theorem htau5_838 : Closed 5 ⟨7648371893761,7652973802241,4,1⟩ := by
  exact closed_size (c:=7652973802241) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1663 : RootAt 5 1663 := by
  intro e he hdiv
  have cases := allowed_list (p:=1663) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_838

end OddPerfect.HarmonicChain
