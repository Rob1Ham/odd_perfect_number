module

public import OddPerfect.HarmonicTau5.Part026
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_780 : Closed 5 ⟨4531282799761,4534390675481,4,1⟩ := by
  exact closed_size (c:=4534390675481) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1459 : RootAt 5 1459 := by
  intro e he hdiv
  have cases := allowed_list (p:=1459) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_780

theorem htau5_782 : Closed 5 ⟨4682207873281,4685393048705,4,1⟩ := by
  exact closed_size (c:=937078609741) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1471 : RootAt 5 1471 := by
  intro e he hdiv
  have cases := allowed_list (p:=1471) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_782

theorem htau5_784 : Closed 5 ⟨4810832476321,4814083038805,4,1⟩ := by
  exact closed_size (c:=962816607761) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1481 : RootAt 5 1481 := by
  intro e he hdiv
  have cases := allowed_list (p:=1481) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_784

theorem htau5_786 : Closed 5 ⟨4836872105521,4840135851881,4,1⟩ := by
  exact closed_size (c:=4840135851881) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1483 : RootAt 5 1483 := by
  intro e he hdiv
  have cases := allowed_list (p:=1483) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_786

theorem htau5_788 : Closed 5 ⟨4889268346561,4892558567521,4,1⟩ := by
  exact closed_size (c:=4892558567521) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1487 : RootAt 5 1487 := by
  intro e he hdiv
  have cases := allowed_list (p:=1487) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_788

theorem htau5_790 : Closed 5 ⟨4915625528641,4918929040421,4,1⟩ := by
  exact closed_size (c:=4918929040421) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1489 : RootAt 5 1489 := by
  intro e he hdiv
  have cases := allowed_list (p:=1489) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_790

theorem htau5_792 : Closed 5 ⟨4968659444401,4971989645101,4,1⟩ := by
  exact closed_size (c:=4971989645101) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1493 : RootAt 5 1493 := by
  intro e he hdiv
  have cases := allowed_list (p:=1493) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_792

theorem htau5_794 : Closed 5 ⟨5049013494001,5052383997001,4,1⟩ := by
  exact closed_size (c:=5052383997001) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1499 : RootAt 5 1499 := by
  intro e he hdiv
  have cases := allowed_list (p:=1499) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_794

theorem htau5_796 : Closed 5 ⟨5212641500641,5216093581105,4,1⟩ := by
  exact closed_size (c:=1043218716221) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1511 : RootAt 5 1511 := by
  intro e he hdiv
  have cases := allowed_list (p:=1511) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_796

theorem htau5_798 : Closed 5 ⟨5380214781841,5383749745561,4,1⟩ := by
  exact closed_size (c:=5383749745561) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1523 : RootAt 5 1523 := by
  intro e he hdiv
  have cases := allowed_list (p:=1523) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_798

theorem htau5_800 : Closed 5 ⟨5494153169521,5497744119305,4,1⟩ := by
  exact closed_size (c:=1099548823861) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1531 : RootAt 5 1531 := by
  intro e he hdiv
  have cases := allowed_list (p:=1531) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_800

theorem htau5_802 : Closed 5 ⟨5668441960801,5672117993201,4,1⟩ := by
  exact closed_size (c:=5672117993201) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1543 : RootAt 5 1543 := by
  intro e he hdiv
  have cases := allowed_list (p:=1543) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_802

theorem htau5_804 : Closed 5 ⟨5757125158801,5760844231901,4,1⟩ := by
  exact closed_size (c:=5760844231901) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1549 : RootAt 5 1549 := by
  intro e he hdiv
  have cases := allowed_list (p:=1549) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_804

theorem htau5_806 : Closed 5 ⟨5816822652481,5820570605221,4,1⟩ := by
  exact closed_size (c:=5820570605221) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1553 : RootAt 5 1553 := by
  intro e he hdiv
  have cases := allowed_list (p:=1553) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_806

theorem htau5_808 : Closed 5 ⟨5907237891361,5911029443281,4,1⟩ := by
  exact closed_size (c:=5911029443281) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1559 : RootAt 5 1559 := by
  intro e he hdiv
  have cases := allowed_list (p:=1559) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_808

end OddPerfect.HarmonicChain
