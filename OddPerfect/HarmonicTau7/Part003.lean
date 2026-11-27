module

public import OddPerfect.HarmonicTau7.Part002
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau7_60 : Closed 7 ⟨3638452817128921,4002386209315077,8,2⟩ := by
  exact closed_size (c:=1334128736438359) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_61 : Closed 7 ⟨1771561,1948717,6,1⟩ := by
  apply closed_split (c:=1948717) (p:=45319) (by decide +kernel) (by decide +kernel) htauPrime7_45319 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=45319) (r:=1) (E:=4) [2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_60

theorem htauRoot7_11 : RootAt 7 11 := by
  intro e he hdiv
  have cases := allowed_list (p:=11) (r:=7) (E:=15) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_61

theorem htau7_63 : Closed 7 ⟨131978910896740215841,142977178535790267399,8,2⟩ := by
  exact closed_size (c:=47659059511930089133) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_64 : Closed 7 ⟨4826809,5229043,6,1⟩ := by
  apply closed_split (c:=5229043) (p:=5229043) (by decide +kernel) (by decide +kernel) htauPrime7_5229043 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=5229043) (r:=1) (E:=3) [2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_63

theorem htau7_65 : Closed 7 ⟨302875106592253,328114698808274,13,1⟩ := by
  exact closed_size (c:=3348109171513) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_13 : RootAt 7 13 := by
  intro e he hdiv
  have cases := allowed_list (p:=13) (r:=7) (E:=14) [6, 13] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau7_64
  · exact htau7_65

theorem htau7_67 : Closed 7 ⟨15875903854837564377841,16868148462382951977519,8,2⟩ := by
  exact closed_size (c:=5622716154127650659173) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_68 : Closed 7 ⟨24137569,25646167,6,1⟩ := by
  apply closed_split (c:=25646167) (p:=25646167) (by decide +kernel) (by decide +kernel) htauPrime7_25646167 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=25646167) (r:=1) (E:=3) [2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_67

theorem htauRoot7_17 : RootAt 7 17 := by
  intro e he hdiv
  have cases := allowed_list (p:=17) (r:=7) (E:=13) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_68

theorem htau7_70 : Closed 7 ⟨464606643223203729329,490466585976355274754,9,3⟩ := by
  exact closed_size (c:=81744430996059212459) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_71 : Closed 7 ⟨3332777255921,3517981203522,7,2⟩ := by
  apply closed_split (c:=586330200587) (p:=11807) (by decide +kernel) (by decide +kernel) htauPrime7_11807 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=11807) (r:=1) (E:=4) [2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_70

theorem htau7_72 : Closed 7 ⟨236097273586699561,249217306488361543,8,2⟩ := by
  exact closed_size (c:=249217306488361543) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_73 : Closed 7 ⟨16725366958155383600801,17654803208942069727204,9,2⟩ := by
  exact closed_size (c:=1471233600745172477267) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_74 : Closed 7 ⟨47045881,49659541,6,1⟩ := by
  apply closed_split (c:=49659541) (p:=70841) (by decide +kernel) (by decide +kernel) htauPrime7_70841 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=70841) (r:=1) (E:=4) [1, 2, 3] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau7_71
  · exact htau7_72
  · exact htau7_73

theorem htauRoot7_19 : RootAt 7 19 := by
  intro e he hdiv
  have cases := allowed_list (p:=19) (r:=7) (E:=12) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_74

theorem htau7_76 : Closed 7 ⟨702690680410353852089,734632129259855981796,8,3⟩ := by
  exact closed_size (c:=61219344104987998483) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_77 : Closed 7 ⟨625010333763030464802117317,653420751267392618632966962,9,3⟩ := by
  exact closed_size (c:=36301152848188478812942609) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_78 : Closed 7 ⟨790025645436413,825936056569374,7,2⟩ := by
  apply closed_split (c:=137656009428229) (p:=889453) (by decide +kernel) (by decide +kernel) htauPrime7_889453 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=889453) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau7_76
  · exact htau7_77

theorem htau7_79 : Closed 7 ⟨4216143292436477676121,4407786994006894669951,8,2⟩ := by
  exact closed_size (c:=4407786994006894669951) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_80 : Closed 7 ⟨148035889,154764793,6,1⟩ := by
  apply closed_split (c:=154764793) (p:=5336717) (by decide +kernel) (by decide +kernel) htauPrime7_5336717 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=5336717) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau7_78
  · exact htau7_79

theorem htauRoot7_23 : RootAt 7 23 := by
  intro e he hdiv
  have cases := allowed_list (p:=23) (r:=7) (E:=12) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_80

theorem htau7_82 : Closed 7 ⟨52350146491651933,54219795193563314,7,2⟩ := by
  exact closed_size (c:=3872842513825951) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_83 : Closed 7 ⟨594823321,616067011,6,1⟩ := by
  apply closed_split (c:=88009573) (p:=88009573) (by decide +kernel) (by decide +kernel) htauPrime7_88009573 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=88009573) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_82

theorem htauRoot7_29 : RootAt 7 29 := by
  intro e he hdiv
  have cases := allowed_list (p:=29) (r:=7) (E:=11) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_83

theorem htau7_85 : Closed 7 ⟨813918209885251297,841048817767943906,7,2⟩ := by
  exact closed_size (c:=420524408883971953) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_86 : Closed 7 ⟨887503681,917087137,6,1⟩ := by
  apply closed_split (c:=917087137) (p:=917087137) (by decide +kernel) (by decide +kernel) htauPrime7_917087137 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=917087137) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_85

theorem htauRoot7_31 : RootAt 7 31 := by
  intro e he hdiv
  have cases := allowed_list (p:=31) (r:=7) (E:=11) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_86

theorem htau7_88 : Closed 7 ⟨95293123714207973,97940157564456426,7,2⟩ := by
  exact closed_size (c:=16323359594076071) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_89 : Closed 7 ⟨2565726409,2636996587,6,1⟩ := by
  apply closed_split (c:=2636996587) (p:=37140797) (by decide +kernel) (by decide +kernel) htauPrime7_37140797 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=37140797) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_88

end OddPerfect.HarmonicChain
