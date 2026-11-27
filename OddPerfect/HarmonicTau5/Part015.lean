module

public import OddPerfect.HarmonicTau5.Part014
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htauRoot5_373 : RootAt 5 373 := by
  intro e he hdiv
  have cases := allowed_list (p:=373) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_419

theorem htau5_421 : Closed 5 ⟨20632736881,20687320841,4,1⟩ := by
  exact closed_size (c:=20687320841) [(45869891,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_45869891) (by decide +kernel)

theorem htauRoot5_379 : RootAt 5 379 := by
  intro e he hdiv
  have cases := allowed_list (p:=379) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_421

theorem htau5_423 : Closed 5 ⟨21517662721,21573991681,4,1⟩ := by
  exact closed_size (c:=21573991681) [(257351,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_257351) (by decide +kernel)

theorem htauRoot5_383 : RootAt 5 383 := by
  intro e he hdiv
  have cases := allowed_list (p:=383) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_423

theorem htau5_425 : Closed 5 ⟨22898045041,22957060621,4,1⟩ := by
  exact closed_size (c:=22957060621) [(126631,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_126631) (by decide +kernel)

theorem htauRoot5_389 : RootAt 5 389 := by
  intro e he hdiv
  have cases := allowed_list (p:=389) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_425

theorem htau5_427 : Closed 5 ⟨618613473741163863341,620175629002724412582,5,2⟩ := by
  exact closed_size (c:=103362604833787402097) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_428 : Closed 5 ⟨24840596881,24903325661,4,1⟩ := by
  apply closed_split (c:=24903325661) (p:=24903325661) (by decide +kernel) (by decide +kernel) htauPrime5_24903325661 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=24903325661) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_427

theorem htauRoot5_397 : RootAt 5 397 := by
  intro e he hdiv
  have cases := allowed_list (p:=397) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_428

theorem htau5_430 : Closed 5 ⟨25856961601,25921604005,4,1⟩ := by
  exact closed_size (c:=5184320801) [(1231,1),(11,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl
    · exact htauPrime5_1231
    · exact (by norm_num)) (by decide +kernel)

theorem htauRoot5_401 : RootAt 5 401 := by
  intro e he hdiv
  have cases := allowed_list (p:=401) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_430

theorem htau5_432 : Closed 5 ⟨27982932961,28051518581,4,1⟩ := by
  exact closed_size (c:=28051518581) [(8971,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_8971) (by decide +kernel)

theorem htauRoot5_409 : RootAt 5 409 := by
  intro e he hdiv
  have cases := allowed_list (p:=409) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_432

theorem htau5_434 : Closed 5 ⟨30821664721,30895400761,4,1⟩ := by
  exact closed_size (c:=30895400761) [(996625831,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_996625831) (by decide +kernel)

theorem htauRoot5_419 : RootAt 5 419 := by
  intro e he hdiv
  have cases := allowed_list (p:=419) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_434

theorem htau5_436 : Closed 5 ⟨1146027707886961,1154802265581965,6,2⟩ := by
  exact closed_size (c:=230960453116393) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_437 : Closed 5 ⟨41808236811424224241,42128347496615960525,8,2⟩ := by
  exact closed_size (c:=1685133899864638421) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_438 : Closed 5 ⟨1525206287117567124535921,1536884245030092776207885,10,2⟩ := by
  exact closed_size (c:=307376849006018555241577) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_439 : Closed 5 ⟨31414372081,31489168205,4,1⟩ := by
  apply closed_split (c:=6297833641) (p:=191) (by decide +kernel) (by decide +kernel) htauPrime5_191 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=191) (r:=1) (E:=7) [2, 4, 6] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_436
  · exact htau5_437
  · exact htau5_438

theorem htauRoot5_421 : RootAt 5 421 := by
  intro e he hdiv
  have cases := allowed_list (p:=421) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_439

theorem htau5_441 : Closed 5 ⟨34507149121,34587398305,4,1⟩ := by
  exact closed_size (c:=6917479661) [(191,1),(71,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl
    · exact htauPrime5_191
    · exact htauPrime5_71) (by decide +kernel)

theorem htauRoot5_431 : RootAt 5 431 := by
  intro e he hdiv
  have cases := allowed_list (p:=431) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_441

theorem htau5_443 : Closed 5 ⟨35152125121,35233495781,4,1⟩ := by
  exact closed_size (c:=35233495781) [(1811,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_1811) (by decide +kernel)

theorem htauRoot5_433 : RootAt 5 433 := by
  intro e he hdiv
  have cases := allowed_list (p:=433) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_443

theorem htau5_445 : Closed 5 ⟨1382631896806202202161,1385788590671668054962,5,2⟩ := by
  exact closed_size (c:=230964765111944675827) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_446 : Closed 5 ⟨37141383841,37226181521,4,1⟩ := by
  apply closed_split (c:=37226181521) (p:=37226181521) (by decide +kernel) (by decide +kernel) htauPrime5_37226181521 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=37226181521) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_445

theorem htauRoot5_439 : RootAt 5 439 := by
  intro e he hdiv
  have cases := allowed_list (p:=439) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_446

theorem htau5_448 : Closed 5 ⟨38513670001,38600805001,4,1⟩ := by
  exact closed_size (c:=38600805001) [(15971,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_15971) (by decide +kernel)

theorem htauRoot5_443 : RootAt 5 443 := by
  intro e he hdiv
  have cases := allowed_list (p:=443) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_448

end OddPerfect.HarmonicChain
