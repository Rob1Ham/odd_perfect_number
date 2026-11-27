module

public import OddPerfect.HarmonicTau5.Part012
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_360 : Closed 5 ⟨3373402561,3387458405,4,1⟩ := by
  apply closed_split (c:=677491681) (p:=11106421) (by decide +kernel) (by decide +kernel) htauPrime5_11106421 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=11106421) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_358
  · exact htau5_359

theorem htauRoot5_241 : RootAt 5 241 := by
  intro e he hdiv
  have cases := allowed_list (p:=241) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_360

theorem htau5_362 : Closed 5 ⟨26143763729992781,26248342769888910,5,2⟩ := by
  exact closed_size (c:=874944758996297) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_363 : Closed 5 ⟨172203246205205580027961,172892085438195629501215,6,2⟩ := by
  exact closed_size (c:=34578417087639125900243) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_364 : Closed 5 ⟨3969126001,3985002505,4,1⟩ := by
  apply closed_split (c:=797000501) (p:=6586781) (by decide +kernel) (by decide +kernel) htauPrime5_6586781 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=6586781) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_362
  · exact htau5_363

theorem htauRoot5_251 : RootAt 5 251 := by
  intro e he hdiv
  have cases := allowed_list (p:=251) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_364

theorem htau5_366 : Closed 5 ⟨4362470401,4379511301,4,1⟩ := by
  exact closed_size (c:=4379511301) [(398137391,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_398137391) (by decide +kernel)

theorem htauRoot5_257 : RootAt 5 257 := by
  intro e he hdiv
  have cases := allowed_list (p:=257) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_366

theorem htau5_368 : Closed 5 ⟨22977376742013368401,23065076658026707922,5,2⟩ := by
  exact closed_size (c:=11532538329013353961) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_369 : Closed 5 ⟨4784350561,4802611441,4,1⟩ := by
  apply closed_split (c:=4802611441) (p:=4802611441) (by decide +kernel) (by decide +kernel) htauPrime5_4802611441 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=4802611441) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_368

theorem htauRoot5_263 : RootAt 5 263 := by
  intro e he hdiv
  have cases := allowed_list (p:=263) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_369

theorem htau5_371 : Closed 5 ⟨227431363824754261,228279993572127662,5,2⟩ := by
  exact closed_size (c:=114139996786063831) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_372 : Closed 5 ⟨5236114321,5255652061,4,1⟩ := by
  apply closed_split (c:=5255652061) (p:=43435141) (by decide +kernel) (by decide +kernel) htauPrime5_43435141 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=43435141) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_371

theorem htauRoot5_269 : RootAt 5 269 := by
  intro e he hdiv
  have cases := allowed_list (p:=269) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_372

theorem htau5_374 : Closed 5 ⟨5393580481,5413556705,4,1⟩ := by
  exact closed_size (c:=1082711341) [(4313591,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_4313591) (by decide +kernel)

theorem htauRoot5_271 : RootAt 5 271 := by
  intro e he hdiv
  have cases := allowed_list (p:=271) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_374

theorem htau5_376 : Closed 5 ⟨34786348177929797021,34912385677215355542,5,2⟩ := by
  exact closed_size (c:=5818730946202559257) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_377 : Closed 5 ⟨5887339441,5908670381,4,1⟩ := by
  apply closed_split (c:=5908670381) (p:=5908670381) (by decide +kernel) (by decide +kernel) htauPrime5_5908670381 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=5908670381) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_376

theorem htauRoot5_277 : RootAt 5 277 := by
  intro e he hdiv
  have cases := allowed_list (p:=277) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_377

theorem htau5_379 : Closed 5 ⟨928747929887681,932071143886410,5,2⟩ := by
  exact closed_size (c:=31069038129547) [(271,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_271) (by decide +kernel)

theorem htau5_380 : Closed 5 ⟨138347220383998849441,138842249670720626815,6,2⟩ := by
  exact closed_size (c:=27768449934144125363) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_381 : Closed 5 ⟨6234839521,6257106805,4,1⟩ := by
  apply closed_split (c:=1251421361) (p:=148961) (by decide +kernel) (by decide +kernel) htauPrime5_148961 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=148961) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_379
  · exact htau5_380

theorem htauRoot5_281 : RootAt 5 281 := by
  intro e he hdiv
  have cases := allowed_list (p:=281) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_381

theorem htau5_383 : Closed 5 ⟨6414247921,6436993481,4,1⟩ := by
  exact closed_size (c:=6436993481) [(5064511,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_5064511) (by decide +kernel)

theorem htauRoot5_283 : RootAt 5 283 := by
  intro e he hdiv
  have cases := allowed_list (p:=283) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_383

theorem htau5_385 : Closed 5 ⟨7370050801,7395290701,4,1⟩ := by
  exact closed_size (c:=7395290701) [(412891,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_412891) (by decide +kernel)

theorem htauRoot5_293 : RootAt 5 293 := by
  intro e he hdiv
  have cases := allowed_list (p:=293) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_385

theorem htau5_387 : Closed 5 ⟨8882874001,8911903001,4,1⟩ := by
  exact closed_size (c:=8911903001) [(5231,1),(1051,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl
    · exact htauPrime5_5231
    · exact htauPrime5_1051) (by decide +kernel)

theorem htauRoot5_307 : RootAt 5 307 := by
  intro e he hdiv
  have cases := allowed_list (p:=307) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_387

theorem htau5_389 : Closed 5 ⟨9354951841,9385129105,4,1⟩ := by
  exact closed_size (c:=1877025821) [(170638711,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_170638711) (by decide +kernel)

end OddPerfect.HarmonicChain
