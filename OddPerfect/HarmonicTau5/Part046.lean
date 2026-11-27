module

public import OddPerfect.HarmonicTau5.Part045
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1350 : Closed 5 ⟨187618794154801,187669501937005,4,1⟩ := by
  exact closed_size (c:=37533900387401) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3701 : RootAt 5 3701 := by
  intro e he hdiv
  have cases := allowed_list (p:=3701) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1350

theorem htau5_1352 : Closed 5 ⟨189246272135761,189297309425981,4,1⟩ := by
  exact closed_size (c:=189297309425981) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3709 : RootAt 5 3709 := by
  intro e he hdiv
  have cases := allowed_list (p:=3709) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1352

theorem htau5_1354 : Closed 5 ⟨191295482183521,191346933362161,4,1⟩ := by
  exact closed_size (c:=191346933362161) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3719 : RootAt 5 3719 := by
  intro e he hdiv
  have cases := allowed_list (p:=3719) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1354

theorem htau5_1356 : Closed 5 ⟨192946795899841,192998579795681,4,1⟩ := by
  exact closed_size (c:=192998579795681) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3727 : RootAt 5 3727 := by
  intro e he hdiv
  have cases := allowed_list (p:=3727) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1356

theorem htau5_1358 : Closed 5 ⟨194192279513521,194244313886381,4,1⟩ := by
  exact closed_size (c:=194244313886381) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3733 : RootAt 5 3733 := by
  intro e he hdiv
  have cases := allowed_list (p:=3733) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1358

theorem htau5_1360 : Closed 5 ⟨195443783174641,195496068830921,4,1⟩ := by
  exact closed_size (c:=195496068830921) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3739 : RootAt 5 3739 := by
  intro e he hdiv
  have cases := allowed_list (p:=3739) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1360

theorem htau5_1362 : Closed 5 ⟨200084448104641,200137662053605,4,1⟩ := by
  exact closed_size (c:=40027532410721) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3761 : RootAt 5 3761 := by
  intro e he hdiv
  have cases := allowed_list (p:=3761) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1362

theorem htau5_1364 : Closed 5 ⟨201364301903521,201417770916241,4,1⟩ := by
  exact closed_size (c:=201417770916241) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3767 : RootAt 5 3767 := by
  intro e he hdiv
  have cases := allowed_list (p:=3767) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1364

theorem htau5_1366 : Closed 5 ⟨201792281140321,201845835355061,4,1⟩ := by
  exact closed_size (c:=201845835355061) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3769 : RootAt 5 3769 := by
  intro e he hdiv
  have cases := allowed_list (p:=3769) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1366

theorem htau5_1368 : Closed 5 ⟨203942419667281,203996401250041,4,1⟩ := by
  exact closed_size (c:=203996401250041) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3779 : RootAt 5 3779 := by
  intro e he hdiv
  have cases := allowed_list (p:=3779) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1368

theorem htau5_1370 : Closed 5 ⟨206981424148801,207036007857701,4,1⟩ := by
  exact closed_size (c:=207036007857701) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3793 : RootAt 5 3793 := by
  intro e he hdiv
  have cases := allowed_list (p:=3793) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1370

theorem htau5_1372 : Closed 5 ⟨207855915349681,207910671913261,4,1⟩ := by
  exact closed_size (c:=207910671913261) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3797 : RootAt 5 3797 := by
  intro e he hdiv
  have cases := allowed_list (p:=3797) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1372

theorem htau5_1374 : Closed 5 ⟨209172844170481,209227860699721,4,1⟩ := by
  exact closed_size (c:=209227860699721) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3803 : RootAt 5 3803 := by
  intro e he hdiv
  have cases := allowed_list (p:=3803) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1374

theorem htau5_1376 : Closed 5 ⟨213161197201681,213216998562205,4,1⟩ := by
  exact closed_size (c:=42643399712441) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3821 : RootAt 5 3821 := by
  intro e he hdiv
  have cases := allowed_list (p:=3821) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1376

theorem htau5_1378 : Closed 5 ⟨213607841778241,213663730800161,4,1⟩ := by
  exact closed_size (c:=213663730800161) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3823 : RootAt 5 3823 := by
  intro e he hdiv
  have cases := allowed_list (p:=3823) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1378

end OddPerfect.HarmonicChain
