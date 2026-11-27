module

public import OddPerfect.HarmonicTau5.Part025
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_750 : Closed 5 ⟨3100870943041,3103209458081,4,1⟩ := by
  exact closed_size (c:=3103209458081) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1327 : RootAt 5 1327 := by
  intro e he hdiv
  have cases := allowed_list (p:=1327) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_750

theorem htau5_752 : Closed 5 ⟨3431093087041,3433615949605,4,1⟩ := by
  exact closed_size (c:=686723189921) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1361 : RootAt 5 1361 := by
  intro e he hdiv
  have cases := allowed_list (p:=1361) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_752

theorem htau5_754 : Closed 5 ⟨3491998578721,3494554946641,4,1⟩ := by
  exact closed_size (c:=3494554946641) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1367 : RootAt 5 1367 := by
  intro e he hdiv
  have cases := allowed_list (p:=1367) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_754

theorem htau5_756 : Closed 5 ⟨3553711346641,3556301515261,4,1⟩ := by
  exact closed_size (c:=3556301515261) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1373 : RootAt 5 1373 := by
  intro e he hdiv
  have cases := allowed_list (p:=1373) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_756

theorem htau5_758 : Closed 5 ⟨3637263079921,3639898777805,4,1⟩ := by
  exact closed_size (c:=727979755561) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1381 : RootAt 5 1381 := by
  intro e he hdiv
  have cases := allowed_list (p:=1381) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_758

theorem htau5_760 : Closed 5 ⟨3830635754401,3833375837201,4,1⟩ := by
  exact closed_size (c:=3833375837201) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1399 : RootAt 5 1399 := by
  intro e he hdiv
  have cases := allowed_list (p:=1399) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_760

theorem htau5_762 : Closed 5 ⟨3941340648961,3944139896581,4,1⟩ := by
  exact closed_size (c:=3944139896581) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1409 : RootAt 5 1409 := by
  intro e he hdiv
  have cases := allowed_list (p:=1409) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_762

theorem htau5_764 : Closed 5 ⟨4100337455041,4103220955361,4,1⟩ := by
  exact closed_size (c:=4103220955361) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1423 : RootAt 5 1423 := by
  intro e he hdiv
  have cases := allowed_list (p:=1423) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_764

theorem htau5_766 : Closed 5 ⟨4146635796241,4149543675481,4,1⟩ := by
  exact closed_size (c:=4149543675481) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1427 : RootAt 5 1427 := by
  intro e he hdiv
  have cases := allowed_list (p:=1427) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_766

theorem htau5_768 : Closed 5 ⟨4169931445681,4172851565741,4,1⟩ := by
  exact closed_size (c:=4172851565741) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1429 : RootAt 5 1429 := by
  intro e he hdiv
  have cases := allowed_list (p:=1429) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_768

theorem htau5_770 : Closed 5 ⟨4216817073121,4219761777781,4,1⟩ := by
  exact closed_size (c:=4219761777781) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1433 : RootAt 5 1433 := by
  intro e he hdiv
  have cases := allowed_list (p:=1433) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_770

theorem htau5_772 : Closed 5 ⟨4287885459841,4290867299521,4,1⟩ := by
  exact closed_size (c:=4290867299521) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1439 : RootAt 5 1439 := by
  intro e he hdiv
  have cases := allowed_list (p:=1439) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_772

theorem htau5_774 : Closed 5 ⟨4384036128481,4387067965361,4,1⟩ := by
  exact closed_size (c:=4387067965361) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1447 : RootAt 5 1447 := by
  intro e he hdiv
  have cases := allowed_list (p:=1447) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_774

theorem htau5_776 : Closed 5 ⟨4432713370801,4435770414505,4,1⟩ := by
  exact closed_size (c:=887154082901) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1451 : RootAt 5 1451 := by
  intro e he hdiv
  have cases := allowed_list (p:=1451) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_776

theorem htau5_778 : Closed 5 ⟨4457203441681,4460273141021,4,1⟩ := by
  exact closed_size (c:=4460273141021) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1453 : RootAt 5 1453 := by
  intro e he hdiv
  have cases := allowed_list (p:=1453) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_778

end OddPerfect.HarmonicChain
