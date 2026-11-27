module

public import OddPerfect.HarmonicTau5.Part054
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1620 : Closed 5 ⟨562953493142881,563069089342705,4,1⟩ := by
  exact closed_size (c:=112613817868541) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4871 : RootAt 5 4871 := by
  intro e he hdiv
  have cases := allowed_list (p:=4871) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1620

theorem htau5_1622 : Closed 5 ⟨565732361546641,565848385410781,4,1⟩ := by
  exact closed_size (c:=565848385410781) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4877 : RootAt 5 4877 := by
  intro e he hdiv
  have cases := allowed_list (p:=4877) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1622

theorem htau5_1624 : Closed 5 ⟨571320949187041,571437831541621,4,1⟩ := by
  exact closed_size (c:=571437831541621) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4889 : RootAt 5 4889 := by
  intro e he hdiv
  have cases := allowed_list (p:=4889) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1624

theorem htau5_1626 : Closed 5 ⟨577893185069281,578011074335921,4,1⟩ := by
  exact closed_size (c:=578011074335921) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4903 : RootAt 5 4903 := by
  intro e he hdiv
  have cases := allowed_list (p:=4903) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1626

theorem htau5_1628 : Closed 5 ⟨580727147154961,580845469719581,4,1⟩ := by
  exact closed_size (c:=580845469719581) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4909 : RootAt 5 4909 := by
  intro e he hdiv
  have cases := allowed_list (p:=4909) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1628

theorem htau5_1630 : Closed 5 ⟨585473564226721,585592611311761,4,1⟩ := by
  exact closed_size (c:=585592611311761) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4919 : RootAt 5 4919 := by
  intro e he hdiv
  have cases := allowed_list (p:=4919) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1630

theorem htau5_1632 : Closed 5 ⟨591207602487121,591327522893305,4,1⟩ := by
  exact closed_size (c:=118265504578661) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4931 : RootAt 5 4931 := by
  intro e he hdiv
  have cases := allowed_list (p:=4931) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1632

theorem htau5_1634 : Closed 5 ⟨592167354891121,592287421264781,4,1⟩ := by
  exact closed_size (c:=592287421264781) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4933 : RootAt 5 4933 := by
  intro e he hdiv
  have cases := allowed_list (p:=4933) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1634

theorem htau5_1636 : Closed 5 ⟨594090364812961,594210723476821,4,1⟩ := by
  exact closed_size (c:=594210723476821) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4937 : RootAt 5 4937 := by
  intro e he hdiv
  have cases := allowed_list (p:=4937) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1636

theorem htau5_1638 : Closed 5 ⟨596983656696001,597104454684001,4,1⟩ := by
  exact closed_size (c:=597104454684001) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4943 : RootAt 5 4943 := by
  intro e he hdiv
  have cases := allowed_list (p:=4943) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1638

theorem htau5_1640 : Closed 5 ⟨600857802784801,600979188199505,4,1⟩ := by
  exact closed_size (c:=120195837639901) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4951 : RootAt 5 4951 := by
  intro e he hdiv
  have cases := allowed_list (p:=4951) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1640

theorem htau5_1642 : Closed 5 ⟨603775763278801,603897590511101,4,1⟩ := by
  exact closed_size (c:=603897590511101) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4957 : RootAt 5 4957 := by
  intro e he hdiv
  have cases := allowed_list (p:=4957) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1642

theorem htau5_1644 : Closed 5 ⟨608662632445921,608785198421041,4,1⟩ := by
  exact closed_size (c:=608785198421041) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4967 : RootAt 5 4967 := by
  intro e he hdiv
  have cases := allowed_list (p:=4967) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1644

theorem htau5_1646 : Closed 5 ⟨609643555103521,609766269184661,4,1⟩ := by
  exact closed_size (c:=609766269184661) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4969 : RootAt 5 4969 := by
  intro e he hdiv
  have cases := allowed_list (p:=4969) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1646

theorem htau5_1648 : Closed 5 ⟨611608956871441,611731967522461,4,1⟩ := by
  exact closed_size (c:=611731967522461) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4973 : RootAt 5 4973 := by
  intro e he hdiv
  have cases := allowed_list (p:=4973) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1648

end OddPerfect.HarmonicChain
