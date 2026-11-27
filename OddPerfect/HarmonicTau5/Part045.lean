module

public import OddPerfect.HarmonicTau5.Part044
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1320 : Closed 5 ⟨164811393976321,164857404974081,4,1⟩ := by
  exact closed_size (c:=164857404974081) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3583 : RootAt 5 3583 := by
  intro e he hdiv
  have cases := allowed_list (p:=3583) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1320

theorem htau5_1322 : Closed 5 ⟨166659037303201,166705434585301,4,1⟩ := by
  exact closed_size (c:=166705434585301) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3593 : RootAt 5 3593 := by
  intro e he hdiv
  have cases := allowed_list (p:=3593) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1322

theorem htau5_1324 : Closed 5 ⟨169271783181601,169318724885201,4,1⟩ := by
  exact closed_size (c:=169318724885201) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3607 : RootAt 5 3607 := by
  intro e he hdiv
  have cases := allowed_list (p:=3607) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1324

theorem htau5_1326 : Closed 5 ⟨170400885105361,170448061430141,4,1⟩ := by
  exact closed_size (c:=170448061430141) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3613 : RootAt 5 3613 := by
  intro e he hdiv
  have cases := allowed_list (p:=3613) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1326

theorem htau5_1328 : Closed 5 ⟨171156751470721,171204084643141,4,1⟩ := by
  exact closed_size (c:=171204084643141) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3617 : RootAt 5 3617 := by
  intro e he hdiv
  have cases := allowed_list (p:=3617) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1328

theorem htau5_1330 : Closed 5 ⟨172295262524641,172342831619761,4,1⟩ := by
  exact closed_size (c:=172342831619761) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3623 : RootAt 5 3623 := by
  intro e he hdiv
  have cases := allowed_list (p:=3623) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1330

theorem htau5_1332 : Closed 5 ⟨173822101273921,173869986150305,4,1⟩ := by
  exact closed_size (c:=34773997230061) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3631 : RootAt 5 3631 := by
  intro e he hdiv
  have cases := allowed_list (p:=3631) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1332

theorem htau5_1334 : Closed 5 ⟨174973872717361,175021995344621,4,1⟩ := by
  exact closed_size (c:=175021995344621) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3637 : RootAt 5 3637 := by
  intro e he hdiv
  have cases := allowed_list (p:=3637) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1334

theorem htau5_1336 : Closed 5 ⟨176131358559601,176179719723401,4,1⟩ := by
  exact closed_size (c:=176179719723401) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3643 : RootAt 5 3643 := by
  intro e he hdiv
  have cases := allowed_list (p:=3643) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1336

theorem htau5_1338 : Closed 5 ⟨179246068134961,179295069247081,4,1⟩ := by
  exact closed_size (c:=179295069247081) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3659 : RootAt 5 3659 := by
  intro e he hdiv
  have cases := allowed_list (p:=3659) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1338

theorem htau5_1340 : Closed 5 ⟨181609071490081,181658556250705,4,1⟩ := by
  exact closed_size (c:=36331711250141) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3671 : RootAt 5 3671 := by
  intro e he hdiv
  have cases := allowed_list (p:=3671) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1340

theorem htau5_1342 : Closed 5 ⟨182005165283041,182054730959861,4,1⟩ := by
  exact closed_size (c:=182054730959861) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3673 : RootAt 5 3673 := by
  intro e he hdiv
  have cases := allowed_list (p:=3673) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1342

theorem htau5_1344 : Closed 5 ⟨182799296268241,182849024041981,4,1⟩ := by
  exact closed_size (c:=182849024041981) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3677 : RootAt 5 3677 := by
  intro e he hdiv
  have cases := allowed_list (p:=3677) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1344

theorem htau5_1346 : Closed 5 ⟨185599234557361,185649532452905,4,1⟩ := by
  exact closed_size (c:=37129906490581) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3691 : RootAt 5 3691 := by
  intro e he hdiv
  have cases := allowed_list (p:=3691) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1346

theorem htau5_1348 : Closed 5 ⟨186809002860481,186859546421861,4,1⟩ := by
  exact closed_size (c:=186859546421861) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3697 : RootAt 5 3697 := by
  intro e he hdiv
  have cases := allowed_list (p:=3697) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1348

end OddPerfect.HarmonicChain
