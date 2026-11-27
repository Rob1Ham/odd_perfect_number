module

public import OddPerfect.HarmonicTau5.Part035
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1050 : Closed 5 ⟨37644716109841,37659919953181,4,1⟩ := by
  exact closed_size (c:=37659919953181) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2477 : RootAt 5 2477 := by
  intro e he hdiv
  have cases := allowed_list (p:=2477) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1050

theorem htau5_1052 : Closed 5 ⟨39250337770081,39266025355121,4,1⟩ := by
  exact closed_size (c:=39266025355121) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2503 : RootAt 5 2503 := by
  intro e he hdiv
  have cases := allowed_list (p:=2503) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1052

theorem htau5_1054 : Closed 5 ⟨40391630304481,40407658729205,4,1⟩ := by
  exact closed_size (c:=8081531745841) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2521 : RootAt 5 2521 := by
  intro e he hdiv
  have cases := allowed_list (p:=2521) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1054

theorem htau5_1056 : Closed 5 ⟨41036336333521,41052556229305,4,1⟩ := by
  exact closed_size (c:=8210511245861) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2531 : RootAt 5 2531 := by
  intro e he hdiv
  have cases := allowed_list (p:=2531) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1056

theorem htau5_1058 : Closed 5 ⟨41557633003441,41574007169321,4,1⟩ := by
  exact closed_size (c:=41574007169321) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2539 : RootAt 5 2539 := by
  intro e he hdiv
  have cases := allowed_list (p:=2539) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1058

theorem htau5_1060 : Closed 5 ⟨41820135988801,41836587655201,4,1⟩ := by
  exact closed_size (c:=41836587655201) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2543 : RootAt 5 2543 := by
  intro e he hdiv
  have cases := allowed_list (p:=2543) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1060

theorem htau5_1062 : Closed 5 ⟨42216219754801,42232788129901,4,1⟩ := by
  exact closed_size (c:=42232788129901) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2549 : RootAt 5 2549 := by
  intro e he hdiv
  have cases := allowed_list (p:=2549) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1062

theorem htau5_1064 : Closed 5 ⟨42348870775201,42365478175505,4,1⟩ := by
  exact closed_size (c:=8473095635101) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2551 : RootAt 5 2551 := by
  intro e he hdiv
  have cases := allowed_list (p:=2551) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1064

theorem htau5_1066 : Closed 5 ⟨42748699986001,42765424829501,4,1⟩ := by
  exact closed_size (c:=42765424829501) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2557 : RootAt 5 2557 := by
  intro e he hdiv
  have cases := allowed_list (p:=2557) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1066

theorem htau5_1068 : Closed 5 ⟨44239006840081,44256167044441,4,1⟩ := by
  exact closed_size (c:=44256167044441) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2579 : RootAt 5 2579 := by
  intro e he hdiv
  have cases := allowed_list (p:=2579) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1068

theorem htau5_1070 : Closed 5 ⟨45068141784961,45085542611905,4,1⟩ := by
  exact closed_size (c:=9017108522381) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2591 : RootAt 5 2591 := by
  intro e he hdiv
  have cases := allowed_list (p:=2591) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1070

theorem htau5_1072 : Closed 5 ⟨45207455875201,45224897023301,4,1⟩ := by
  exact closed_size (c:=45224897023301) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2593 : RootAt 5 2593 := by
  intro e he hdiv
  have cases := allowed_list (p:=2593) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1072

theorem htau5_1074 : Closed 5 ⟨46333628948161,46351394910181,4,1⟩ := by
  exact closed_size (c:=46351394910181) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2609 : RootAt 5 2609 := by
  intro e he hdiv
  have cases := allowed_list (p:=2609) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1074

theorem htau5_1076 : Closed 5 ⟨46904541018721,46922470889141,4,1⟩ := by
  exact closed_size (c:=46922470889141) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2617 : RootAt 5 2617 := by
  intro e he hdiv
  have cases := allowed_list (p:=2617) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1076

theorem htau5_1078 : Closed 5 ⟨47191967468881,47209979670205,4,1⟩ := by
  exact closed_size (c:=9441995934041) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2621 : RootAt 5 2621 := by
  intro e he hdiv
  have cases := allowed_list (p:=2621) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1078

end OddPerfect.HarmonicChain
