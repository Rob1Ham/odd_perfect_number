module

public import OddPerfect.HarmonicTau5.Part052
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1560 : Closed 5 ⟨446578710143281,446675876964461,4,1⟩ := by
  exact closed_size (c:=446675876964461) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4597 : RootAt 5 4597 := by
  intro e he hdiv
  have cases := allowed_list (p:=4597) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1560

theorem htau5_1562 : Closed 5 ⟨448914775136881,449012322893321,4,1⟩ := by
  exact closed_size (c:=449012322893321) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4603 : RootAt 5 4603 := by
  intro e he hdiv
  have cases := allowed_list (p:=4603) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1562

theorem htau5_1564 : Closed 5 ⟨455977983956881,456076680490205,4,1⟩ := by
  exact closed_size (c:=91215336098041) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4621 : RootAt 5 4621 := by
  intro e he hdiv
  have cases := allowed_list (p:=4621) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1564

theorem htau5_1566 : Closed 5 ⟨462326070129361,462425795338621,4,1⟩ := by
  exact closed_size (c:=462425795338621) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4637 : RootAt 5 4637 := by
  intro e he hdiv
  have cases := allowed_list (p:=4637) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1566

theorem htau5_1568 : Closed 5 ⟨463124215943041,463224070237121,4,1⟩ := by
  exact closed_size (c:=463224070237121) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4639 : RootAt 5 4639 := by
  intro e he hdiv
  have cases := allowed_list (p:=4639) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1568

theorem htau5_1570 : Closed 5 ⟨464723607387601,464823720185401,4,1⟩ := by
  exact closed_size (c:=464823720185401) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4643 : RootAt 5 4643 := by
  intro e he hdiv
  have cases := allowed_list (p:=4643) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1570

theorem htau5_1572 : Closed 5 ⟨467130457466401,467230958855701,4,1⟩ := by
  exact closed_size (c:=467230958855701) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4649 : RootAt 5 4649 := by
  intro e he hdiv
  have cases := allowed_list (p:=4649) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1572

theorem htau5_1574 : Closed 5 ⟨467934814503601,468035445646505,4,1⟩ := by
  exact closed_size (c:=93607089129301) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4651 : RootAt 5 4651 := by
  intro e he hdiv
  have cases := allowed_list (p:=4651) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1574

theorem htau5_1576 : Closed 5 ⟨470354119147201,470455140220901,4,1⟩ := by
  exact closed_size (c:=470455140220901) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4657 : RootAt 5 4657 := by
  intro e he hdiv
  have cases := allowed_list (p:=4657) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1576

theorem htau5_1578 : Closed 5 ⟨472782792857761,472884204868241,4,1⟩ := by
  exact closed_size (c:=472884204868241) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4663 : RootAt 5 4663 := by
  intro e he hdiv
  have cases := allowed_list (p:=4663) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1578

theorem htau5_1580 : Closed 5 ⟨476851468151041,476953533961861,4,1⟩ := by
  exact closed_size (c:=476953533961861) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4673 : RootAt 5 4673 := by
  intro e he hdiv
  have cases := allowed_list (p:=4673) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1580

theorem htau5_1582 : Closed 5 ⟨479305244227681,479407703664241,4,1⟩ := by
  exact closed_size (c:=479407703664241) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4679 : RootAt 5 4679 := by
  intro e he hdiv
  have cases := allowed_list (p:=4679) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1582

theorem htau5_1584 : Closed 5 ⟨484241194041361,484344443762905,4,1⟩ := by
  exact closed_size (c:=96868888752581) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4691 : RootAt 5 4691 := by
  intro e he hdiv
  have cases := allowed_list (p:=4691) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1584

theorem htau5_1586 : Closed 5 ⟨489215169367681,489319213427521,4,1⟩ := by
  exact closed_size (c:=489319213427521) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4703 : RootAt 5 4703 := by
  intro e he hdiv
  have cases := allowed_list (p:=4703) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1586

theorem htau5_1588 : Closed 5 ⟨496747856441281,496853099631205,4,1⟩ := by
  exact closed_size (c:=99370619926241) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4721 : RootAt 5 4721 := by
  intro e he hdiv
  have cases := allowed_list (p:=4721) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1588

end OddPerfect.HarmonicChain
