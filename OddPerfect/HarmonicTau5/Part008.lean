module

public import OddPerfect.HarmonicTau5.Part007
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_210 : Closed 5 ⟨143638125978738329761,147088742822372231617,10,2⟩ := by
  exact closed_size (c:=147088742822372231617) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_211 : Closed 5 ⟨12117361,12326281,4,1⟩ := by
  apply closed_split (c:=12326281) (p:=151) (by decide +kernel) (by decide +kernel) htauPrime5_151 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=151) (r:=1) (E:=7) [2, 4, 6] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_208
  · exact htau5_209
  · exact htau5_210

theorem htauRoot5_59 : RootAt 5 59 := by
  intro e he hdiv
  have cases := allowed_list (p:=59) (r:=5) (E:=9) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_211

theorem htau5_213 : Closed 5 ⟨6394882783296121,6501766689714665,6,2⟩ := by
  exact closed_size (c:=1300353337942933) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_214 : Closed 5 ⟨13845841,14076605,4,1⟩ := by
  apply closed_split (c:=2815321) (p:=21491) (by decide +kernel) (by decide +kernel) htauPrime5_21491 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=21491) (r:=1) (E:=4) [2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_213

theorem htauRoot5_61 : RootAt 5 61 := by
  intro e he hdiv
  have cases := allowed_list (p:=61) (r:=5) (E:=9) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_214

theorem htau5_216 : Closed 5 ⟨7280751573881041,7391890851263204,6,3⟩ := by
  exact closed_size (c:=1847972712815801) [(47,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_47) (by decide +kernel)

theorem htau5_217 : Closed 5 ⟨97860581904535072081,99354405481738771926,7,3⟩ := by
  exact closed_size (c:=16559067580289795321) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_218 : Closed 5 ⟨1315344081378855903840721,1335422564080600743504328,8,3⟩ := by
  exact closed_size (c:=166927820510075092938041) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_219 : Closed 5 ⟨541682283601,549910046962,5,2⟩ := by
  apply closed_split (c:=274955023481) (p:=13441) (by decide +kernel) (by decide +kernel) htauPrime5_13441 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=13441) (r:=1) (E:=4) [1, 2, 3] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_216
  · exact htau5_217
  · exact htau5_218

theorem htau5_220 : Closed 5 ⟨14560961465478481,14782131992841963,6,2⟩ := by
  exact closed_size (c:=4927377330947321) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_221 : Closed 5 ⟨391413205153527047761,397358490099605263844,7,2⟩ := by
  exact closed_size (c:=99339622524901315961) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_222 : Closed 5 ⟨20151121,20456441,4,1⟩ := by
  apply closed_split (c:=20456441) (p:=26881) (by decide +kernel) (by decide +kernel) htauPrime5_26881 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=26881) (r:=1) (E:=4) [1, 2, 3] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_219
  · exact htau5_220
  · exact htau5_221

theorem htauRoot5_67 : RootAt 5 67 := by
  intro e he hdiv
  have cases := allowed_list (p:=67) (r:=5) (E:=9) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_222

theorem htau5_224 : Closed 5 ⟨2512736012008021,2561921290615830,7,3⟩ := by
  exact closed_size (c:=85397376353861) [(31,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact (by norm_num)) (by decide +kernel)

theorem htau5_225 : Closed 5 ⟨5580786682669814641,5690028339437637195,8,3⟩ := by
  exact closed_size (c:=126445074209725271) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_226 : Closed 5 ⟨12394927222209658317661,12637552943043972088860,9,3⟩ := by
  exact closed_size (c:=210625882384066201481) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_227 : Closed 5 ⟨27529133360527651123525081,28068005086501814989236825,10,3⟩ := by
  exact closed_size (c:=374240067820024199856491) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_228 : Closed 5 ⟨1131353449801,1152979878765,6,2⟩ := by
  apply closed_split (c:=76865325251) (p:=2221) (by decide +kernel) (by decide +kernel) htauPrime5_2221 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=2221) (r:=1) (E:=5) [1, 2, 3, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl
  · exact htau5_224
  · exact htau5_225
  · exact htau5_226
  · exact htau5_227

theorem htau5_229 : Closed 5 ⟨50368986938590321,51331822646734025,8,2⟩ := by
  exact closed_size (c:=2053272905869361) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_230 : Closed 5 ⟨2242477667492979681241,2285344076060709764485,10,2⟩ := by
  exact closed_size (c:=457068815212141952897) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_231 : Closed 5 ⟨25411681,25774705,4,1⟩ := by
  apply closed_split (c:=5154941) (p:=211) (by decide +kernel) (by decide +kernel) htauPrime5_211 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=211) (r:=1) (E:=7) [2, 4, 6] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_228
  · exact htau5_229
  · exact htau5_230

theorem htauRoot5_71 : RootAt 5 71 := by
  intro e he hdiv
  have cases := allowed_list (p:=71) (r:=5) (E:=9) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_231

theorem htau5_233 : Closed 5 ⟨230810143883059595581,234016677357973634124,6,3⟩ := by
  exact closed_size (c:=6500463259943712059) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_234 : Closed 5 ⟨65153318225453945700200261,66058461702115172770410426,7,3⟩ := by
  exact closed_size (c:=11009743617019195461735071) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_235 : Closed 5 ⟨817660926109301,829017356253582,5,2⟩ := by
  apply closed_split (c:=138169559375597) (p:=282281) (by decide +kernel) (by decide +kernel) htauPrime5_282281 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=282281) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_233
  · exact htau5_234

theorem htau5_236 : Closed 5 ⟨23542633858411152639961,23869615701725645354363,6,2⟩ := by
  exact closed_size (c:=23869615701725645354363) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_237 : Closed 5 ⟨28398241,28792661,4,1⟩ := by
  apply closed_split (c:=28792661) (p:=28792661) (by decide +kernel) (by decide +kernel) htauPrime5_28792661 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=28792661) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_235
  · exact htau5_236

theorem htauRoot5_73 : RootAt 5 73 := by
  intro e he hdiv
  have cases := allowed_list (p:=73) (r:=5) (E:=9) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_237

theorem htau5_239 : Closed 5 ⟨1536558922354721,1556258434661922,5,2⟩ := by
  exact closed_size (c:=259376405776987) [(3299,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_3299) (by decide +kernel)

end OddPerfect.HarmonicChain
