module

public import OddPerfect.HarmonicTau5.Part028
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_840 : Closed 5 ⟨7722224074321,7726859262841,4,1⟩ := by
  exact closed_size (c:=7726859262841) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1667 : RootAt 5 1667 := by
  intro e he hdiv
  have cases := allowed_list (p:=1667) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_840

theorem htau5_842 : Closed 5 ⟨7759350084721,7764001973261,4,1⟩ := by
  exact closed_size (c:=7764001973261) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1669 : RootAt 5 1669 := by
  intro e he hdiv
  have cases := allowed_list (p:=1669) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_842

theorem htau5_844 : Closed 5 ⟨8215383330001,8220238757501,4,1⟩ := by
  exact closed_size (c:=8220238757501) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1693 : RootAt 5 1693 := by
  intro e he hdiv
  have cases := allowed_list (p:=1693) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_844

theorem htau5_846 : Closed 5 ⟨8293299876481,8298189793861,4,1⟩ := by
  exact closed_size (c:=8298189793861) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1697 : RootAt 5 1697 := by
  intro e he hdiv
  have cases := allowed_list (p:=1697) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_846

theorem htau5_848 : Closed 5 ⟨8332465333201,8337372556601,4,1⟩ := by
  exact closed_size (c:=8337372556601) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1699 : RootAt 5 1699 := by
  intro e he hdiv
  have cases := allowed_list (p:=1699) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_848

theorem htau5_850 : Closed 5 ⟨8530377503761,8535371869981,4,1⟩ := by
  exact closed_size (c:=8535371869981) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1709 : RootAt 5 1709 := by
  intro e he hdiv
  have cases := allowed_list (p:=1709) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_850

theorem htau5_852 : Closed 5 ⟨8772502109281,8777602401205,4,1⟩ := by
  exact closed_size (c:=1755520480241) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1721 : RootAt 5 1721 := by
  intro e he hdiv
  have cases := allowed_list (p:=1721) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_852

theorem htau5_854 : Closed 5 ⟨8813351875441,8818469965961,4,1⟩ := by
  exact closed_size (c:=8818469965961) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1723 : RootAt 5 1723 := by
  intro e he hdiv
  have cases := allowed_list (p:=1723) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_854

theorem htau5_856 : Closed 5 ⟨9019744817521,9024952522381,4,1⟩ := by
  exact closed_size (c:=9024952522381) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1733 : RootAt 5 1733 := by
  intro e he hdiv
  have cases := allowed_list (p:=1733) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_856

theorem htau5_858 : Closed 5 ⟨9187452028561,9192732173405,4,1⟩ := by
  exact closed_size (c:=1838546434681) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1741 : RootAt 5 1741 := by
  intro e he hdiv
  have cases := allowed_list (p:=1741) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_858

theorem htau5_860 : Closed 5 ⟨9314758936081,9320093849561,4,1⟩ := by
  exact closed_size (c:=9320093849561) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1747 : RootAt 5 1747 := by
  intro e he hdiv
  have cases := allowed_list (p:=1747) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_860

theorem htau5_862 : Closed 5 ⟨9443384314081,9448774373621,4,1⟩ := by
  exact closed_size (c:=9448774373621) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1753 : RootAt 5 1753 := by
  intro e he hdiv
  have cases := allowed_list (p:=1753) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_862

theorem htau5_864 : Closed 5 ⟨9573337234561,9578782818881,4,1⟩ := by
  exact closed_size (c:=9578782818881) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1759 : RootAt 5 1759 := by
  intro e he hdiv
  have cases := allowed_list (p:=1759) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_864

theorem htau5_866 : Closed 5 ⟨9971252437441,9976866881381,4,1⟩ := by
  exact closed_size (c:=9976866881381) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1777 : RootAt 5 1777 := by
  intro e he hdiv
  have cases := allowed_list (p:=1777) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_866

theorem htau5_868 : Closed 5 ⟨10106606869921,10112278366481,4,1⟩ := by
  exact closed_size (c:=10112278366481) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1783 : RootAt 5 1783 := by
  intro e he hdiv
  have cases := allowed_list (p:=1783) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_868

end OddPerfect.HarmonicChain
