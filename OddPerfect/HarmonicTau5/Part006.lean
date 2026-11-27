module

public import OddPerfect.HarmonicTau5.Part005
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_150 : Closed 5 ⟨8919167514983456477,9439661636653056876,8,4⟩ := by
  exact closed_size (c:=262212823240362691) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_151 : Closed 5 ⟨19702441040598455357693,20852413310244121179948,10,4⟩ := by
  exact closed_size (c:=579233703062336699443) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_152 : Closed 5 ⟨43522692258681987885143837,46062981203084141205045996,12,4⟩ := by
  exact closed_size (c:=1279527255641226144584611) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_153 : Closed 5 ⟨96141627199428511238282735933,101753125477813622799465146028,14,4⟩ := by
  exact closed_size (c:=2826475707717045077762920723) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_154 : Closed 5 ⟨4037649395646653,4182393281636268,6,3⟩ := by
  apply closed_split (c:=116177591156563) (p:=47) (by decide +kernel) (by decide +kernel) htauPrime5_47 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=47) (r:=1) (E:=9) [2, 4, 6, 8] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl
  · exact htau5_150
  · exact htau5_151
  · exact htau5_152
  · exact htau5_153

theorem htau5_155 : Closed 5 ⟨31465401740274366829,32593391380408485746,7,3⟩ := by
  exact closed_size (c:=16296695690204242873) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_156 : Closed 5 ⟨245209875761958140698397,254000299028059946467800,8,3⟩ := by
  exact closed_size (c:=141111277237811081371) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_157 : Closed 5 ⟨518112331021,536617049222,5,2⟩ := by
  apply closed_split (c:=268308524611) (p:=7793) (by decide +kernel) (by decide +kernel) htauPrime5_7793 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=7793) (r:=1) (E:=4) [1, 2, 3] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_154
  · exact htau5_155
  · exact htau5_156

theorem htau5_158 : Closed 5 ⟨379538525078454361,393093989854865643,6,2⟩ := by
  exact closed_size (c:=131031329951621881) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_159 : Closed 5 ⟨707281,732541,4,1⟩ := by
  apply closed_split (c:=732541) (p:=732541) (by decide +kernel) (by decide +kernel) htauPrime5_732541 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=732541) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_157
  · exact htau5_158

theorem htau5_160 : Closed 5 ⟨14507145975869,15025258332150,9,1⟩ := by
  exact closed_size (c:=100168388881) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_29 : RootAt 5 29 := by
  intro e he hdiv
  have cases := allowed_list (p:=29) (r:=5) (E:=11) [4, 9] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_159
  · exact htau5_160

theorem htau5_162 : Closed 5 ⟨278032647324721,287316951300665,6,2⟩ := by
  exact closed_size (c:=57463390260133) [(21787,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_21787) (by decide +kernel)

theorem htau5_163 : Closed 5 ⟨923521,954305,4,1⟩ := by
  apply closed_split (c:=190861) (p:=17351) (by decide +kernel) (by decide +kernel) htauPrime5_17351 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=17351) (r:=1) (E:=4) [2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_162

theorem htauRoot5_31 : RootAt 5 31 := by
  intro e he hdiv
  have cases := allowed_list (p:=31) (r:=5) (E:=11) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_163

theorem htau5_165 : Closed 5 ⟨34187397306001,35145275540573,6,2⟩ := by
  exact closed_size (c:=35145275540573) [(331,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_331) (by decide +kernel)

theorem htau5_166 : Closed 5 ⟨623627390900976187441,641100470210334301805,8,2⟩ := by
  exact closed_size (c:=128220094042066860361) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_167 : Closed 5 ⟨1874161,1926221,4,1⟩ := by
  apply closed_split (c:=1926221) (p:=4271) (by decide +kernel) (by decide +kernel) htauPrime5_4271 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=4271) (r:=1) (E:=5) [2, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_165
  · exact htau5_166

theorem htau5_168 : Closed 5 ⟨129961739795077,133571788122718,9,1⟩ := by
  exact closed_size (c:=66785894061359) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_37 : RootAt 5 37 := by
  intro e he hdiv
  have cases := allowed_list (p:=37) (r:=5) (E:=10) [4, 9] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_167
  · exact htau5_168

theorem htau5_170 : Closed 5 ⟨28091006638209401,29014805517964530,7,3⟩ := by
  exact closed_size (c:=967160183932151) [(67,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_67) (by decide +kernel)

theorem htau5_171 : Closed 5 ⟨482069764918311530561,497923298968046419050,9,3⟩ := by
  exact closed_size (c:=3319488659786976127) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_172 : Closed 5 ⟨8272799235763144175957321,8544861733812118854436770,11,3⟩ := by
  exact closed_size (c:=284828724460403961814559) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_173 : Closed 5 ⟨1636909657841,1677835281210,5,2⟩ := by
  apply closed_split (c:=55927842707) (p:=131) (by decide +kernel) (by decide +kernel) htauPrime5_131 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=131) (r:=1) (E:=8) [2, 4, 6] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_170
  · exact htau5_171
  · exact htau5_172

theorem htau5_174 : Closed 5 ⟨948230663503792321,971938099537506415,6,2⟩ := by
  exact closed_size (c:=194387619907501283) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_175 : Closed 5 ⟨2825761,2896405,4,1⟩ := by
  apply closed_split (c:=579281) (p:=579281) (by decide +kernel) (by decide +kernel) htauPrime5_579281 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=579281) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_173
  · exact htau5_174

theorem htau5_176 : Closed 5 ⟨327381934393961,335566482753810,9,1⟩ := by
  exact closed_size (c:=11185549425127) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_41 : RootAt 5 41 := by
  intro e he hdiv
  have cases := allowed_list (p:=41) (r:=5) (E:=10) [4, 9] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_175
  · exact htau5_176

theorem htau5_178 : Closed 5 ⟨11966490679001,12251410540602,5,2⟩ := by
  exact closed_size (c:=2041901756767) [(583367,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_583367) (by decide +kernel)

theorem htau5_179 : Closed 5 ⟨41885122641129979201,42882399425629161203,6,2⟩ := by
  exact closed_size (c:=42882399425629161203) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

end OddPerfect.HarmonicChain
