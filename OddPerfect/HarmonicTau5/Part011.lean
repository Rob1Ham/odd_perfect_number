module

public import OddPerfect.HarmonicTau5.Part010
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_300 : Closed 5 ⟨607573201,611467901,4,1⟩ := by
  apply closed_split (c:=611467901) (p:=1793161) (by decide +kernel) (by decide +kernel) htauPrime5_1793161 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=1793161) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_298
  · exact htau5_299

theorem htauRoot5_157 : RootAt 5 157 := by
  intro e he hdiv
  have cases := allowed_list (p:=157) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_300

theorem htau5_302 : Closed 5 ⟨1413000884695613221,1471112046987080652,8,4⟩ := by
  exact closed_size (c:=4540469280824323) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_303 : Closed 5 ⟨1357893850192484305381,1413786084592151059020,10,4⟩ := by
  exact closed_size (c:=2618122378874353813) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_304 : Closed 5 ⟨1304935990034977417471141,1358648474700494734270668,12,4⟩ := by
  exact closed_size (c:=12580078469449025317321) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_305 : Closed 5 ⟨1254043486423613298189766501,1305661184234582877200664396,14,4⟩ := by
  exact closed_size (c:=1343272823286607898354593) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_306 : Closed 5 ⟨1205135790453092379560365607461,1254740398049481552427405037004,16,4⟩ := by
  exact closed_size (c:=11617966648606310670624120713) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_307 : Closed 5 ⟨1470344312898661,1481482423954764,6,3⟩ := by
  apply closed_split (c:=13717429851433) (p:=31) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=31) (r:=1) (E:=11) [2, 4, 6, 8, 10] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl|rfl
  · exact htau5_302
  · exact htau5_303
  · exact htau5_304
  · exact htau5_305
  · exact htau5_306

theorem htau5_308 : Closed 5 ⟨1912917951081157961,1927409771416472046,7,3⟩ := by
  exact closed_size (c:=107078320634248447) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_309 : Closed 5 ⟨2488706254356586507261,2507560113750681455928,8,3⟩ := by
  exact closed_size (c:=11609074600697599333) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_310 : Closed 5 ⟨3237806836917919045946561,3262335707990774425486410,9,3⟩ := by
  exact closed_size (c:=36248174533230826949849) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_311 : Closed 5 ⟨1130164729361,1137851324082,5,2⟩ := by
  apply closed_split (c:=63213962449) (p:=1301) (by decide +kernel) (by decide +kernel) htauPrime5_1301 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=1301) (r:=1) (E:=5) [1, 2, 3, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl
  · exact htau5_307
  · exact htau5_308
  · exact htau5_309
  · exact htau5_310

theorem htau5_312 : Closed 5 ⟨1809393731706961,1821700680124523,6,2⟩ := by
  exact closed_size (c:=1821700680124523) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_313 : Closed 5 ⟨2896839364462844561,2916542789589630564,7,2⟩ := by
  exact closed_size (c:=81015077488600849) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_314 : Closed 5 ⟨4637839822505014142161,4669385006133708802205,8,2⟩ := by
  exact closed_size (c:=933877001226741760441) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_315 : Closed 5 ⟨705911761,710269241,4,1⟩ := by
  apply closed_split (c:=710269241) (p:=1601) (by decide +kernel) (by decide +kernel) htauPrime5_1601 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=1601) (r:=1) (E:=5) [1, 2, 3, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl
  · exact htau5_311
  · exact htau5_312
  · exact htau5_313
  · exact htau5_314

theorem htauRoot5_163 : RootAt 5 163 := by
  intro e he hdiv
  have cases := allowed_list (p:=163) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_315

theorem htau5_317 : Closed 5 ⟨253593490295161,255568741534533,6,2⟩ := by
  exact closed_size (c:=85189580511511) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_318 : Closed 5 ⟨82681875169324587601,83325888506240286905,8,2⟩ := by
  exact closed_size (c:=16665177701248057381) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_319 : Closed 5 ⟨777796321,782481841,4,1⟩ := by
  apply closed_split (c:=782481841) (p:=571) (by decide +kernel) (by decide +kernel) htauPrime5_571 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=571) (r:=1) (E:=6) [2, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_317
  · exact htau5_318

theorem htauRoot5_167 : RootAt 5 167 := by
  intro e he hdiv
  have cases := allowed_list (p:=167) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_319

theorem htau5_321 : Closed 5 ⟨895745041,900952861,4,1⟩ := by
  exact closed_size (c:=900952861) [(95531,1),(9431,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl
    · exact htauPrime5_95531
    · exact htauPrime5_9431) (by decide +kernel)

theorem htauRoot5_173 : RootAt 5 173 := by
  intro e he hdiv
  have cases := allowed_list (p:=173) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_321

theorem htau5_323 : Closed 5 ⟨1026625681,1032393241,4,1⟩ := by
  exact closed_size (c:=1032393241) [(93853931,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_93853931) (by decide +kernel)

theorem htauRoot5_179 : RootAt 5 179 := by
  intro e he hdiv
  have cases := allowed_list (p:=179) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_323

theorem htau5_325 : Closed 5 ⟨1073283121,1079245805,4,1⟩ := by
  exact closed_size (c:=215849161) [(19622651,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_19622651) (by decide +kernel)

theorem htauRoot5_181 : RootAt 5 181 := by
  intro e he hdiv
  have cases := allowed_list (p:=181) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_325

theorem htau5_327 : Closed 5 ⟨4658874846914401,4685899729545265,6,2⟩ := by
  exact closed_size (c:=937179945909053) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_328 : Closed 5 ⟨16309048302977275631041,16403652717639554733025,8,2⟩ := by
  exact closed_size (c:=656146108705582189321) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_329 : Closed 5 ⟨1330863361,1337867905,4,1⟩ := by
  apply closed_split (c:=267573581) (p:=1871) (by decide +kernel) (by decide +kernel) htauPrime5_1871 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=1871) (r:=1) (E:=5) [2, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_327
  · exact htau5_328

end OddPerfect.HarmonicChain
