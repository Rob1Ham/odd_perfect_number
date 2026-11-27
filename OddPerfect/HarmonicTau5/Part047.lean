module

public import OddPerfect.HarmonicTau5.Part046
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1380 : Closed 5 ⟨215851602388321,215907931094581,4,1⟩ := by
  exact closed_size (c:=215907931094581) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3833 : RootAt 5 3833 := by
  intro e he hdiv
  have cases := allowed_list (p:=3833) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1380

theorem htau5_1382 : Closed 5 ⟨219022506749281,219079454878961,4,1⟩ := by
  exact closed_size (c:=219079454878961) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3847 : RootAt 5 3847 := by
  intro e he hdiv
  have cases := allowed_list (p:=3847) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1382

theorem htau5_1384 : Closed 5 ⟨219934861700401,219991987638505,4,1⟩ := by
  exact closed_size (c:=43998397527701) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3851 : RootAt 5 3851 := by
  intro e he hdiv
  have cases := allowed_list (p:=3851) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1384

theorem htau5_1386 : Closed 5 ⟨220392106580881,220449321561821,4,1⟩ := by
  exact closed_size (c:=220449321561821) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3853 : RootAt 5 3853 := by
  intro e he hdiv
  have cases := allowed_list (p:=3853) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1386

theorem htau5_1388 : Closed 5 ⟨222689034627361,222746696210641,4,1⟩ := by
  exact closed_size (c:=222746696210641) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3863 : RootAt 5 3863 := by
  intro e he hdiv
  have cases := allowed_list (p:=3863) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1388

theorem htau5_1390 : Closed 5 ⟨225934839014641,225993129736781,4,1⟩ := by
  exact closed_size (c:=225993129736781) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3877 : RootAt 5 3877 := by
  intro e he hdiv
  have cases := allowed_list (p:=3877) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1390

theorem htau5_1392 : Closed 5 ⟨226868693989921,226927165302805,4,1⟩ := by
  exact closed_size (c:=45385433060561) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3881 : RootAt 5 3881 := by
  intro e he hdiv
  have cases := allowed_list (p:=3881) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1392

theorem htau5_1394 : Closed 5 ⟨228745085711041,228803919323621,4,1⟩ := by
  exact closed_size (c:=228803919323621) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3889 : RootAt 5 3889 := by
  intro e he hdiv
  have cases := allowed_list (p:=3889) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1394

theorem htau5_1396 : Closed 5 ⟨233009509093201,233069163345401,4,1⟩ := by
  exact closed_size (c:=233069163345401) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3907 : RootAt 5 3907 := by
  intro e he hdiv
  have cases := allowed_list (p:=3907) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1396

theorem htau5_1398 : Closed 5 ⟨233965199238241,234025036885105,4,1⟩ := by
  exact closed_size (c:=46805007377021) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3911 : RootAt 5 3911 := by
  intro e he hdiv
  have cases := allowed_list (p:=3911) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1398

theorem htau5_1400 : Closed 5 ⟨235404242866321,235464356309341,4,1⟩ := by
  exact closed_size (c:=235464356309341) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3917 : RootAt 5 3917 := by
  intro e he hdiv
  have cases := allowed_list (p:=3917) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1400

theorem htau5_1402 : Closed 5 ⟨235885395990721,235945601553761,4,1⟩ := by
  exact closed_size (c:=235945601553761) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3919 : RootAt 5 3919 := by
  intro e he hdiv
  have cases := allowed_list (p:=3919) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1402

theorem htau5_1404 : Closed 5 ⟨236849914625041,236910304710361,4,1⟩ := by
  exact closed_size (c:=236910304710361) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3923 : RootAt 5 3923 := by
  intro e he hdiv
  have cases := allowed_list (p:=3923) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1404

theorem htau5_1406 : Closed 5 ⟨238302234835681,238362902410741,4,1⟩ := by
  exact closed_size (c:=238362902410741) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3929 : RootAt 5 3929 := by
  intro e he hdiv
  have cases := allowed_list (p:=3929) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1406

theorem htau5_1408 : Closed 5 ⟨238787822523121,238848582783305,4,1⟩ := by
  exact closed_size (c:=47769716556661) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3931 : RootAt 5 3931 := by
  intro e he hdiv
  have cases := allowed_list (p:=3931) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1408

end OddPerfect.HarmonicChain
