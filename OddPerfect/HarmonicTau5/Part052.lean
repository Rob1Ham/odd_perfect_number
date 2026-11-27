module

public import OddPerfect.HarmonicTau5.Part051
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1530 : Closed 5 ⟨396741423620161,396830339223841,4,1⟩ := by
  exact closed_size (c:=396830339223841) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4463 : RootAt 5 4463 := by
  intro e he hdiv
  have cases := allowed_list (p:=4463) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1530

theorem htau5_1532 : Closed 5 ⟨403180738168321,403270733868805,4,1⟩ := by
  exact closed_size (c:=80654146773761) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4481 : RootAt 5 4481 := by
  intro e he hdiv
  have cases := allowed_list (p:=4481) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1532

theorem htau5_1534 : Closed 5 ⟨403901025149521,403991141397881,4,1⟩ := by
  exact closed_size (c:=403991141397881) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4483 : RootAt 5 4483 := by
  intro e he hdiv
  have cases := allowed_list (p:=4483) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1534

theorem htau5_1536 : Closed 5 ⟨407516947328401,407607667931101,4,1⟩ := by
  exact closed_size (c:=407607667931101) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4493 : RootAt 5 4493 := by
  intro e he hdiv
  have cases := allowed_list (p:=4493) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1536

theorem htau5_1538 : Closed 5 ⟨412619959676401,412711530905801,4,1⟩ := by
  exact closed_size (c:=412711530905801) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4507 : RootAt 5 4507 := by
  intro e he hdiv
  have cases := allowed_list (p:=4507) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1538

theorem htau5_1540 : Closed 5 ⟨414821573074561,414913510479941,4,1⟩ := by
  exact closed_size (c:=414913510479941) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4513 : RootAt 5 4513 := by
  intro e he hdiv
  have cases := allowed_list (p:=4513) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1540

theorem htau5_1542 : Closed 5 ⟨416294202017521,416386384081741,4,1⟩ := by
  exact closed_size (c:=416386384081741) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4517 : RootAt 5 4517 := by
  intro e he hdiv
  have cases := allowed_list (p:=4517) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1542

theorem htau5_1544 : Closed 5 ⟨417031985092321,417124289648561,4,1⟩ := by
  exact closed_size (c:=417124289648561) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4519 : RootAt 5 4519 := by
  intro e he hdiv
  have cases := allowed_list (p:=4519) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1544

theorem htau5_1546 : Closed 5 ⟨418510492785841,418603042651561,4,1⟩ := by
  exact closed_size (c:=418603042651561) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4523 : RootAt 5 4523 := by
  intro e he hdiv
  have cases := allowed_list (p:=4523) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1546

theorem htau5_1548 : Closed 5 ⟨427464267193681,427558298048761,4,1⟩ := by
  exact closed_size (c:=427558298048761) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4547 : RootAt 5 4547 := by
  intro e he hdiv
  have cases := allowed_list (p:=4547) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1548

theorem htau5_1550 : Closed 5 ⟨428216844946801,428310999925901,4,1⟩ := by
  exact closed_size (c:=428310999925901) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4549 : RootAt 5 4549 := by
  intro e he hdiv
  have cases := allowed_list (p:=4549) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1550

theorem htau5_1552 : Closed 5 ⟨432753201003841,432848103021605,4,1⟩ := by
  exact closed_size (c:=86569620604321) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4561 : RootAt 5 4561 := by
  intro e he hdiv
  have cases := allowed_list (p:=4561) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1552

theorem htau5_1554 : Closed 5 ⟨435034847385121,435130124399441,4,1⟩ := by
  exact closed_size (c:=435130124399441) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4567 : RootAt 5 4567 := by
  intro e he hdiv
  have cases := allowed_list (p:=4567) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1554

theorem htau5_1556 : Closed 5 ⟨441163353124321,441259634956081,4,1⟩ := by
  exact closed_size (c:=441259634956081) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4583 : RootAt 5 4583 := by
  intro e he hdiv
  have cases := allowed_list (p:=4583) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1556

theorem htau5_1558 : Closed 5 ⟨444251774352961,444348561231905,4,1⟩ := by
  exact closed_size (c:=88869712246381) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4591 : RootAt 5 4591 := by
  intro e he hdiv
  have cases := allowed_list (p:=4591) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1558

end OddPerfect.HarmonicChain
