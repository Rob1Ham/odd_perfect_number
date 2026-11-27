module

public import OddPerfect.HarmonicTau5.Part015
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_450 : Closed 5 ⟨40642963201,40733684101,4,1⟩ := by
  exact closed_size (c:=40733684101) [(3703062191,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_3703062191) (by decide +kernel)

theorem htauRoot5_449 : RootAt 5 449 := by
  intro e he hdiv
  have cases := allowed_list (p:=449) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_450

theorem htau5_452 : Closed 5 ⟨1906693815762400342901,1910875161893216284302,5,2⟩ := by
  exact closed_size (c:=318479193648869380717) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_453 : Closed 5 ⟨43617904801,43713558101,4,1⟩ := by
  apply closed_split (c:=43713558101) (p:=43713558101) (by decide +kernel) (by decide +kernel) htauPrime5_43713558101 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=43713558101) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_452

theorem htauRoot5_457 : RootAt 5 457 := by
  intro e he hdiv
  have cases := allowed_list (p:=457) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_453

theorem htau5_455 : Closed 5 ⟨45165175441,45263360605,4,1⟩ := by
  exact closed_size (c:=9052672121) [(23971,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_23971) (by decide +kernel)

theorem htauRoot5_461 : RootAt 5 461 := by
  intro e he hdiv
  have cases := allowed_list (p:=461) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_455

theorem htau5_457 : Closed 5 ⟨2402210357653087921,2407409993225240242,5,2⟩ := by
  exact closed_size (c:=1203704996612620121) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_458 : Closed 5 ⟨45954068161,46053535841,4,1⟩ := by
  apply closed_split (c:=46053535841) (p:=52274161) (by decide +kernel) (by decide +kernel) htauPrime5_52274161 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=52274161) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_457

theorem htauRoot5_463 : RootAt 5 463 := by
  intro e he hdiv
  have cases := allowed_list (p:=463) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_458

theorem htau5_460 : Closed 5 ⟨162154039732600381,162502057439815742,5,2⟩ := by
  exact closed_size (c:=81251028719907871) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_461 : Closed 5 ⟨552825443652804907528441,554011926849371321264703,6,2⟩ := by
  exact closed_size (c:=184670642283123773754901) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_462 : Closed 5 ⟨47562811921,47664878041,4,1⟩ := by
  apply closed_split (c:=47664878041) (p:=3409261) (by decide +kernel) (by decide +kernel) htauPrime5_3409261 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=3409261) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_460
  · exact htau5_461

theorem htauRoot5_467 : RootAt 5 467 := by
  intro e he hdiv
  have cases := allowed_list (p:=467) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_462

theorem htau5_464 : Closed 5 ⟨2777101315158900784321,2782911150598905443522,5,2⟩ := by
  exact closed_size (c:=1391455575299452721761) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_465 : Closed 5 ⟨52643172481,52753304641,4,1⟩ := by
  apply closed_split (c:=52753304641) (p:=52753304641) (by decide +kernel) (by decide +kernel) htauPrime5_52753304641 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=52753304641) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_464

theorem htauRoot5_479 : RootAt 5 479 := by
  intro e he hdiv
  have cases := allowed_list (p:=479) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_465

theorem htau5_467 : Closed 5 ⟨144763953938015381,145061878520863062,5,2⟩ := by
  exact closed_size (c:=8058993251159059) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_468 : Closed 5 ⟨372567551897909082864601,373334296860798479361023,6,2⟩ := by
  exact closed_size (c:=373334296860798479361023) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_469 : Closed 5 ⟨56249134561,56364873521,4,1⟩ := by
  apply closed_split (c:=56364873521) (p:=2573621) (by decide +kernel) (by decide +kernel) htauPrime5_2573621 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=2573621) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_467
  · exact htau5_468

theorem htauRoot5_487 : RootAt 5 487 := by
  intro e he hdiv
  have cases := allowed_list (p:=487) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_469

theorem htau5_471 : Closed 5 ⟨58120048561,58238660905,4,1⟩ := by
  exact closed_size (c:=11647732181) [(603791,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_603791) (by decide +kernel)

theorem htauRoot5_491 : RootAt 5 491 := by
  intro e he hdiv
  have cases := allowed_list (p:=491) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_471

theorem htau5_473 : Closed 5 ⟨62001498001,62125999001,4,1⟩ := by
  exact closed_size (c:=62125999001) [(55918991,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_55918991) (by decide +kernel)

theorem htauRoot5_499 : RootAt 5 499 := by
  intro e he hdiv
  have cases := allowed_list (p:=499) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_473

theorem htau5_475 : Closed 5 ⟨4105897925017400794801,4114077004613321267762,5,2⟩ := by
  exact closed_size (c:=2057038502306660633881) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_476 : Closed 5 ⟨64013554081,64141071121,4,1⟩ := by
  apply closed_split (c:=64141071121) (p:=64141071121) (by decide +kernel) (by decide +kernel) htauPrime5_64141071121 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=64141071121) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_475

theorem htauRoot5_503 : RootAt 5 503 := by
  intro e he hdiv
  have cases := allowed_list (p:=503) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_476

theorem htau5_478 : Closed 5 ⟨67122964561,67255096381,4,1⟩ := by
  exact closed_size (c:=67255096381) [(6114099671,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_6114099671) (by decide +kernel)

theorem htauRoot5_509 : RootAt 5 509 := by
  intro e he hdiv
  have cases := allowed_list (p:=509) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_478

end OddPerfect.HarmonicChain
