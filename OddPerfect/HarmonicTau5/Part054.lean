module

public import OddPerfect.HarmonicTau5.Part053
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1590 : Closed 5 ⟨497590158679441,497695535671961,4,1⟩ := by
  exact closed_size (c:=497695535671961) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4723 : RootAt 5 4723 := by
  intro e he hdiv
  have cases := allowed_list (p:=4723) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1590

theorem htau5_1592 : Closed 5 ⟨500123493360481,500229272441141,4,1⟩ := by
  exact closed_size (c:=500229272441141) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4729 : RootAt 5 4729 := by
  intro e he hdiv
  have cases := allowed_list (p:=4729) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1592

theorem htau5_1594 : Closed 5 ⟨501817748861521,501923796568381,4,1⟩ := by
  exact closed_size (c:=501923796568381) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4733 : RootAt 5 4733 := by
  intro e he hdiv
  have cases := allowed_list (p:=4733) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1594

theorem htau5_1596 : Closed 5 ⟨509495229144001,509602491297505,4,1⟩ := by
  exact closed_size (c:=101920498259501) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4751 : RootAt 5 4751 := by
  intro e he hdiv
  have cases := allowed_list (p:=4751) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1596

theorem htau5_1598 : Closed 5 ⟨512935572982561,513043377852881,4,1⟩ := by
  exact closed_size (c:=513043377852881) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4759 : RootAt 5 4759 := by
  intro e he hdiv
  have cases := allowed_list (p:=4759) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1598

theorem htau5_1600 : Closed 5 ⟨523361201113921,523470645112481,4,1⟩ := by
  exact closed_size (c:=523470645112481) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4783 : RootAt 5 4783 := by
  intro e he hdiv
  have cases := allowed_list (p:=4783) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1600

theorem htau5_1602 : Closed 5 ⟨525114136406161,525223855197721,4,1⟩ := by
  exact closed_size (c:=525223855197721) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4787 : RootAt 5 4787 := by
  intro e he hdiv
  have cases := allowed_list (p:=4787) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1602

theorem htau5_1604 : Closed 5 ⟨525992253499441,526102109859821,4,1⟩ := by
  exact closed_size (c:=526102109859821) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4789 : RootAt 5 4789 := by
  intro e he hdiv
  have cases := allowed_list (p:=4789) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1604

theorem htau5_1606 : Closed 5 ⟨527751791176801,527861923019701,4,1⟩ := by
  exact closed_size (c:=527861923019701) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4793 : RootAt 5 4793 := by
  intro e he hdiv
  have cases := allowed_list (p:=4793) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1606

theorem htau5_1608 : Closed 5 ⟨530399370220801,530509916150401,4,1⟩ := by
  exact closed_size (c:=530509916150401) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4799 : RootAt 5 4799 := by
  intro e he hdiv
  have cases := allowed_list (p:=4799) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1608

theorem htau5_1610 : Closed 5 ⟨531284106259201,531394790448005,4,1⟩ := by
  exact closed_size (c:=106278958089601) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4801 : RootAt 5 4801 := by
  intro e he hdiv
  have cases := allowed_list (p:=4801) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1610

theorem htau5_1612 : Closed 5 ⟨536615788770961,536727304936541,4,1⟩ := by
  exact closed_size (c:=536727304936541) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4813 : RootAt 5 4813 := by
  intro e he hdiv
  have cases := allowed_list (p:=4813) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1612

theorem htau5_1614 : Closed 5 ⟨538401901773121,538513696187941,4,1⟩ := by
  exact closed_size (c:=538513696187941) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4817 : RootAt 5 4817 := by
  intro e he hdiv
  have cases := allowed_list (p:=4817) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1614

theorem htau5_1616 : Closed 5 ⟨544688429550721,544801201482305,4,1⟩ := by
  exact closed_size (c:=108960240296461) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4831 : RootAt 5 4831 := by
  intro e he hdiv
  have cases := allowed_list (p:=4831) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1616

theorem htau5_1618 : Closed 5 ⟨558344810921041,558459696684605,4,1⟩ := by
  exact closed_size (c:=111691939336921) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4861 : RootAt 5 4861 := by
  intro e he hdiv
  have cases := allowed_list (p:=4861) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1618

end OddPerfect.HarmonicChain
