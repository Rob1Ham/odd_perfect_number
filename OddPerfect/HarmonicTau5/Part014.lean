module

public import OddPerfect.HarmonicTau5.Part013
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htauRoot5_311 : RootAt 5 311 := by
  intro e he hdiv
  have cases := allowed_list (p:=311) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_389

theorem htau5_391 : Closed 5 ⟨9597924961,9628687541,4,1⟩ := by
  exact closed_size (c:=9628687541) [(875335231,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_875335231) (by decide +kernel)

theorem htauRoot5_313 : RootAt 5 313 := by
  intro e he hdiv
  have cases := allowed_list (p:=313) (r:=5) (E:=7) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_391

theorem htau5_393 : Closed 5 ⟨29901515700014641,29996150879683802,5,2⟩ := by
  exact closed_size (c:=14998075439841901) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_394 : Closed 5 ⟨88542006071143053772561,88822232289010309456983,6,2⟩ := by
  exact closed_size (c:=29607410763003436485661) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_395 : Closed 5 ⟨10098039121,10129994941,4,1⟩ := by
  apply closed_split (c:=10129994941) (p:=2961121) (by decide +kernel) (by decide +kernel) htauPrime5_2961121 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=2961121) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_393
  · exact htau5_394

theorem htauRoot5_317 : RootAt 5 317 := by
  intro e he hdiv
  have cases := allowed_list (p:=317) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_395

theorem htau5_397 : Closed 5 ⟨763441772668321,765767272572610,5,2⟩ := by
  exact closed_size (c:=76576727257261) [(59,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_59) (by decide +kernel)

theorem htau5_398 : Closed 5 ⟨48555660183477883921,48703564314930555915,6,2⟩ := by
  exact closed_size (c:=3246904287662037061) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_399 : Closed 5 ⟨3088188543329376895259521,3097595393993910326737220,7,2⟩ := by
  exact closed_size (c:=154879769699695516336861) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_400 : Closed 5 ⟨12003612721,12039987305,4,1⟩ := by
  apply closed_split (c:=2407997461) (p:=63601) (by decide +kernel) (by decide +kernel) htauPrime5_63601 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=63601) (r:=1) (E:=4) [1, 2, 3] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_397
  · exact htau5_398
  · exact htau5_399

theorem htauRoot5_331 : RootAt 5 331 := by
  intro e he hdiv
  have cases := allowed_list (p:=331) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_400

theorem htau5_402 : Closed 5 ⟨166851390553318721381,167347972085720449662,5,2⟩ := by
  exact closed_size (c:=1033012173368644751) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_403 : Closed 5 ⟨12897917761,12936304421,4,1⟩ := by
  apply closed_split (c:=12936304421) (p:=12936304421) (by decide +kernel) (by decide +kernel) htauPrime5_12936304421 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=12936304421) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_402

theorem htauRoot5_337 : RootAt 5 337 := by
  intro e he hdiv
  have cases := allowed_list (p:=337) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_403

theorem htau5_405 : Closed 5 ⟨14498327281,14540229961,4,1⟩ := by
  exact closed_size (c:=14540229961) [(46753151,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_46753151) (by decide +kernel)

theorem htauRoot5_347 : RootAt 5 347 := by
  intro e he hdiv
  have cases := allowed_list (p:=347) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_405

theorem htau5_407 : Closed 5 ⟨14835483601,14878114301,4,1⟩ := by
  exact closed_size (c:=14878114301) [(510031,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_510031) (by decide +kernel)

theorem htauRoot5_349 : RootAt 5 349 := by
  intro e he hdiv
  have cases := allowed_list (p:=349) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_407

theorem htau5_409 : Closed 5 ⟨57554197594175101,57717719408844662,5,2⟩ := by
  exact closed_size (c:=28858859704422331) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_410 : Closed 5 ⟨213331597440718907043721,213937710832946781421923,6,2⟩ := by
  exact closed_size (c:=71312570277648927140641) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_411 : Closed 5 ⟨15527402881,15571514821,4,1⟩ := by
  apply closed_split (c:=15571514821) (p:=3706621) (by decide +kernel) (by decide +kernel) htauPrime5_3706621 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=3706621) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_409
  · exact htau5_410

theorem htauRoot5_353 : RootAt 5 353 := by
  intro e he hdiv
  have cases := allowed_list (p:=353) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_411

theorem htau5_413 : Closed 5 ⟨276673147376560730641,277445977413775831442,5,2⟩ := by
  exact closed_size (c:=138722988706887915721) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_414 : Closed 5 ⟨16610312161,16656709681,4,1⟩ := by
  apply closed_split (c:=16656709681) (p:=16656709681) (by decide +kernel) (by decide +kernel) htauPrime5_16656709681 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=16656709681) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_413

theorem htauRoot5_359 : RootAt 5 359 := by
  intro e he hdiv
  have cases := allowed_list (p:=359) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_414

theorem htau5_416 : Closed 5 ⟨18141126721,18190692641,4,1⟩ := by
  exact closed_size (c:=18190692641) [(5885051,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_5885051) (by decide +kernel)

theorem htauRoot5_367 : RootAt 5 367 := by
  intro e he hdiv
  have cases := allowed_list (p:=367) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_416

theorem htau5_418 : Closed 5 ⟨375695978546872558301,376705913992430567382,5,2⟩ := by
  exact closed_size (c:=20928106332912809299) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_419 : Closed 5 ⟨19356878641,19408913261,4,1⟩ := by
  apply closed_split (c:=19408913261) (p:=19408913261) (by decide +kernel) (by decide +kernel) htauPrime5_19408913261 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=19408913261) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_418

end OddPerfect.HarmonicChain
