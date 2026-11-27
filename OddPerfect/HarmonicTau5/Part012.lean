module

public import OddPerfect.HarmonicTau5.Part011
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htauRoot5_191 : RootAt 5 191 := by
  intro e he hdiv
  have cases := allowed_list (p:=191) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_329

theorem htau5_331 : Closed 5 ⟨1935149634958202501,1945228540694393502,5,2⟩ := by
  exact closed_size (c:=108068252260799639) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_332 : Closed 5 ⟨1387488001,1394714501,4,1⟩ := by
  apply closed_split (c:=1394714501) (p:=1394714501) (by decide +kernel) (by decide +kernel) htauPrime5_1394714501 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=1394714501) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_331

theorem htauRoot5_193 : RootAt 5 193 := by
  intro e he hdiv
  have cases := allowed_list (p:=193) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_332

theorem htau5_334 : Closed 5 ⟨1506138481,1513822861,4,1⟩ := by
  exact closed_size (c:=1513822861) [(2311,1),(991,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl
    · exact htauPrime5_2311
    · exact htauPrime5_991) (by decide +kernel)

theorem htauRoot5_197 : RootAt 5 197 := by
  intro e he hdiv
  have cases := allowed_list (p:=197) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_334

theorem htau5_336 : Closed 5 ⟨1568239201,1576159601,4,1⟩ := by
  exact closed_size (c:=1576159601) [(22199431,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_22199431) (by decide +kernel)

theorem htauRoot5_199 : RootAt 5 199 := by
  intro e he hdiv
  have cases := allowed_list (p:=199) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_336

theorem htau5_338 : Closed 5 ⟨2924228939979127541,2980129322355732630,7,3⟩ := by
  exact closed_size (c:=33112548026174807) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_339 : Closed 5 ⟨14741038086434781934181,15022873879438473224550,9,3⟩ := by
  exact closed_size (c:=33384164176529940499) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_340 : Closed 5 ⟨74309572993717735730206421,75730307268214786749993270,11,3⟩ := by
  exact closed_size (c:=841447858535719852777703) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_341 : Closed 5 ⟨374594557461331105815970568261,381756478939112705449941110790,13,3⟩ := by
  exact closed_size (c:=4241738654879030060554901231) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_342 : Closed 5 ⟨580089057722501,582853378125510,5,2⟩ := by
  apply closed_split (c:=6476148645839) (p:=71) (by decide +kernel) (by decide +kernel) htauPrime5_71 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=71) (r:=1) (E:=9) [2, 4, 6, 8] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl
  · exact htau5_338
  · exact htau5_339
  · exact htau5_340
  · exact htau5_341

theorem htau5_343 : Closed 5 ⟨169769443722124865161,170578452497581440215,6,2⟩ := by
  exact closed_size (c:=34115690499516288043) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_344 : Closed 5 ⟨1982119441,1991558105,4,1⟩ := by
  apply closed_split (c:=398311621) (p:=292661) (by decide +kernel) (by decide +kernel) htauPrime5_292661 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=292661) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_342
  · exact htau5_343

theorem htauRoot5_211 : RootAt 5 211 := by
  intro e he hdiv
  have cases := allowed_list (p:=211) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_344

theorem htau5_346 : Closed 5 ⟨2472973441,2484112961,4,1⟩ := by
  exact closed_size (c:=2484112961) [(30431,1),(11,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl
    · exact htauPrime5_30431
    · exact (by norm_num)) (by decide +kernel)

theorem htauRoot5_223 : RootAt 5 223 := by
  intro e he hdiv
  have cases := allowed_list (p:=223) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_346

theorem htau5_348 : Closed 5 ⟨7081483956834195721,7112817959298382442,5,2⟩ := by
  exact closed_size (c:=3556408979649191221) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_349 : Closed 5 ⟨2655237841,2666986681,4,1⟩ := by
  apply closed_split (c:=2666986681) (p:=2666986681) (by decide +kernel) (by decide +kernel) htauPrime5_2666986681 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=2666986681) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_348

theorem htauRoot5_227 : RootAt 5 227 := by
  intro e he hdiv
  have cases := allowed_list (p:=227) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_349

theorem htau5_351 : Closed 5 ⟨2750058481,2762120141,4,1⟩ := by
  exact closed_size (c:=2762120141) [(251101831,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_251101831) (by decide +kernel)

theorem htauRoot5_229 : RootAt 5 229 := by
  intro e he hdiv
  have cases := allowed_list (p:=229) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_351

theorem htau5_353 : Closed 5 ⟨2947295521,2959999381,4,1⟩ := by
  exact closed_size (c:=2959999381) [(95483851,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_95483851) (by decide +kernel)

theorem htauRoot5_233 : RootAt 5 233 := by
  intro e he hdiv
  have cases := allowed_list (p:=233) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_353

theorem htau5_355 : Closed 5 ⟨10690650985030155361,10735569689910680162,5,2⟩ := by
  exact closed_size (c:=5367784844955340081) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_356 : Closed 5 ⟨3262808641,3276517921,4,1⟩ := by
  apply closed_split (c:=3276517921) (p:=3276517921) (by decide +kernel) (by decide +kernel) htauPrime5_3276517921 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=3276517921) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_355

theorem htauRoot5_239 : RootAt 5 239 := by
  intro e he hdiv
  have cases := allowed_list (p:=239) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_356

theorem htau5_358 : Closed 5 ⟨37466429044944181,37622542553376910,5,2⟩ := by
  exact closed_size (c:=3762254255337691) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_359 : Closed 5 ⟨416117934339777995686201,417851796688222321597515,6,2⟩ := by
  exact closed_size (c:=27856786445881488106501) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

end OddPerfect.HarmonicChain
