module

public import OddPerfect.HarmonicTau5.Part009
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_270 : Closed 5 ⟨141158161,142465181,4,1⟩ := by
  apply closed_split (c:=142465181) (p:=191) (by decide +kernel) (by decide +kernel) htauPrime5_191 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=191) (r:=1) (E:=7) [2, 4, 6] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_267
  · exact htau5_268
  · exact htau5_269

theorem htauRoot5_109 : RootAt 5 109 := by
  intro e he hdiv
  have cases := allowed_list (p:=109) (r:=5) (E:=8) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_270

theorem htau5_272 : Closed 5 ⟨10272146790361,10405317177673,6,2⟩ := by
  exact closed_size (c:=10405317177673) [(1471,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_1471) (by decide +kernel)

theorem htau5_273 : Closed 5 ⟨647155519939533361,655545428965368205,8,2⟩ := by
  exact closed_size (c:=131109085793073641) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_274 : Closed 5 ⟨40771444911710541276361,41300017570288617074737,10,2⟩ := by
  exact closed_size (c:=41300017570288617074737) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_275 : Closed 5 ⟨163047361,164503141,4,1⟩ := by
  apply closed_split (c:=164503141) (p:=251) (by decide +kernel) (by decide +kernel) htauPrime5_251 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=251) (r:=1) (E:=7) [2, 4, 6] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_272
  · exact htau5_273
  · exact htau5_274

theorem htauRoot5_113 : RootAt 5 113 := by
  intro e he hdiv
  have cases := allowed_list (p:=113) (r:=5) (E:=8) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_275

theorem htau5_277 : Closed 5 ⟨68212339272613121,68753707304746242,5,2⟩ := by
  exact closed_size (c:=11458951217457707) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_278 : Closed 5 ⟨260144641,262209281,4,1⟩ := by
  apply closed_split (c:=262209281) (p:=262209281) (by decide +kernel) (by decide +kernel) htauPrime5_262209281 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=262209281) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_277

theorem htauRoot5_127 : RootAt 5 127 := by
  intro e he hdiv
  have cases := allowed_list (p:=127) (r:=5) (E:=8) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_278

theorem htau5_280 : Closed 5 ⟨286548717632921,288753235295610,5,2⟩ := by
  exact closed_size (c:=9625107843187) [(631,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_631) (by decide +kernel)

theorem htau5_281 : Closed 5 ⟨278812188805549765921,280957186696160590915,6,2⟩ := by
  exact closed_size (c:=56191437339232118183) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_282 : Closed 5 ⟨294499921,296765305,4,1⟩ := by
  apply closed_split (c:=59353061) (p:=973001) (by decide +kernel) (by decide +kernel) htauPrime5_973001 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=973001) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_280
  · exact htau5_281

theorem htauRoot5_131 : RootAt 5 131 := by
  intro e he hdiv
  have cases := allowed_list (p:=131) (r:=5) (E:=8) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_282

theorem htau5_284 : Closed 5 ⟨35940325458037953481,36204705904581677793,6,2⟩ := by
  exact closed_size (c:=12068235301527225931) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_285 : Closed 5 ⟨352275361,354865621,4,1⟩ := by
  apply closed_split (c:=354865621) (p:=319411) (by decide +kernel) (by decide +kernel) htauPrime5_319411 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=319411) (r:=1) (E:=3) [2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_284

theorem htauRoot5_137 : RootAt 5 137 := by
  intro e he hdiv
  have cases := allowed_list (p:=137) (r:=5) (E:=8) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_285

theorem htau5_287 : Closed 5 ⟨3423499424187121,3448307766968722,5,2⟩ := by
  exact closed_size (c:=1724153883484361) [(1499,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_1499) (by decide +kernel)

theorem htau5_288 : Closed 5 ⟨31396505822788608423601,31624020182246256190203,6,2⟩ := by
  exact closed_size (c:=10541340060748752063401) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_289 : Closed 5 ⟨373301041,376006121,4,1⟩ := by
  apply closed_split (c:=376006121) (p:=9170881) (by decide +kernel) (by decide +kernel) htauPrime5_9170881 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=9170881) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_287
  · exact htau5_288

theorem htauRoot5_139 : RootAt 5 139 := by
  intro e he hdiv
  have cases := allowed_list (p:=139) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_289

theorem htau5_291 : Closed 5 ⟨235342936673881,237276472221273,6,2⟩ := by
  exact closed_size (c:=79092157407091) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_292 : Closed 5 ⟨112371780745981373761,113295007576066226405,8,2⟩ := by
  exact closed_size (c:=22659001515213245281) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_293 : Closed 5 ⟨492884401,496214701,4,1⟩ := by
  apply closed_split (c:=496214701) (p:=691) (by decide +kernel) (by decide +kernel) htauPrime5_691 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=691) (r:=1) (E:=6) [2, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_291
  · exact htau5_292

theorem htauRoot5_149 : RootAt 5 149 := by
  intro e he hdiv
  have cases := allowed_list (p:=149) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_293

theorem htau5_295 : Closed 5 ⟨54416582342235901,54779360080504510,5,2⟩ := by
  exact closed_size (c:=5477936008050451) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_296 : Closed 5 ⟨519885601,523351505,4,1⟩ := by
  apply closed_split (c:=104670301) (p:=104670301) (by decide +kernel) (by decide +kernel) htauPrime5_104670301 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=104670301) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_295

theorem htauRoot5_151 : RootAt 5 151 := by
  intro e he hdiv
  have cases := allowed_list (p:=151) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_296

theorem htau5_298 : Closed 5 ⟨1089476568678361,1096461004292962,5,2⟩ := by
  exact closed_size (c:=548230502146481) [(367,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_367) (by decide +kernel)

theorem htau5_299 : Closed 5 ⟨1953606893367858489121,1966131110919583500783,6,2⟩ := by
  exact closed_size (c:=655377036973194500261) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

end OddPerfect.HarmonicChain
