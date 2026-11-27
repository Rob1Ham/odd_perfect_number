module

public import OddPerfect.HarmonicTau5.Part016
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_480 : Closed 5 ⟨73680216481,73821909205,4,1⟩ := by
  exact closed_size (c:=14764381841) [(75571,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_75571) (by decide +kernel)

theorem htauRoot5_521 : RootAt 5 521 := by
  intro e he hdiv
  have cases := allowed_list (p:=521) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_480

theorem htau5_482 : Closed 5 ⟨74818113841,74961443561,4,1⟩ := by
  exact closed_size (c:=74961443561) [(21472771,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_21472771) (by decide +kernel)

theorem htauRoot5_523 : RootAt 5 523 := by
  intro e he hdiv
  have cases := allowed_list (p:=523) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_482

theorem htau5_484 : Closed 5 ⟨14557615618492226741,14584574251754365710,5,2⟩ := by
  exact closed_size (c:=486152475058478857) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_485 : Closed 5 ⟨85662167761,85820801405,4,1⟩ := by
  apply closed_split (c:=17164160281) (p:=169942181) (by decide +kernel) (by decide +kernel) htauPrime5_169942181 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=169942181) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_484

theorem htauRoot5_541 : RootAt 5 541 := by
  intro e he hdiv
  have cases := allowed_list (p:=541) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_485

theorem htau5_487 : Closed 5 ⟨89526025681,89689992761,4,1⟩ := by
  exact closed_size (c:=89689992761) [(208097431,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_208097431) (by decide +kernel)

theorem htauRoot5_547 : RootAt 5 547 := by
  intro e he hdiv
  have cases := allowed_list (p:=547) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_487

theorem htau5_489 : Closed 5 ⟨9281581125795865003501,9298274617125564934502,5,2⟩ := by
  exact closed_size (c:=4649137308562782467251) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_490 : Closed 5 ⟨96254442001,96427561501,4,1⟩ := by
  apply closed_split (c:=96427561501) (p:=96427561501) (by decide +kernel) (by decide +kernel) htauPrime5_96427561501 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=96427561501) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_489

theorem htauRoot5_557 : RootAt 5 557 := by
  intro e he hdiv
  have cases := allowed_list (p:=557) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_490

theorem htau5_492 : Closed 5 ⟨10112050692432912623401,10130043665295717795722,5,2⟩ := by
  exact closed_size (c:=5065021832647858897861) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_493 : Closed 5 ⟨100469346961,100648118041,4,1⟩ := by
  apply closed_split (c:=100648118041) (p:=100648118041) (by decide +kernel) (by decide +kernel) htauPrime5_100648118041 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=100648118041) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_492

theorem htauRoot5_563 : RootAt 5 563 := by
  intro e he hdiv
  have cases := allowed_list (p:=563) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_493

theorem htau5_495 : Closed 5 ⟨104821185121,105005729461,4,1⟩ := by
  exact closed_size (c:=105005729461) [(9511,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_9511) (by decide +kernel)

theorem htauRoot5_569 : RootAt 5 569 := by
  intro e he hdiv
  have cases := allowed_list (p:=569) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_495

theorem htau5_497 : Closed 5 ⟨106302733681,106489229705,4,1⟩ := by
  exact closed_size (c:=21297845941) [(11631811,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_11631811) (by decide +kernel)

theorem htauRoot5_571 : RootAt 5 571 := by
  intro e he hdiv
  have cases := allowed_list (p:=571) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_497

theorem htau5_499 : Closed 5 ⟨110841719041,111034152581,4,1⟩ := by
  exact closed_size (c:=111034152581) [(131,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_131) (by decide +kernel)

theorem htauRoot5_577 : RootAt 5 577 := by
  intro e he hdiv
  have cases := allowed_list (p:=577) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_499

theorem htau5_501 : Closed 5 ⟨118727795761,118930402921,4,1⟩ := by
  exact closed_size (c:=118930402921) [(305411,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_305411) (by decide +kernel)

theorem htauRoot5_587 : RootAt 5 587 := by
  intro e he hdiv
  have cases := allowed_list (p:=587) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_501

theorem htau5_503 : Closed 5 ⟨123657019201,123865899301,4,1⟩ := by
  exact closed_size (c:=123865899301) [(71,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_71) (by decide +kernel)

theorem htauRoot5_593 : RootAt 5 593 := by
  intro e he hdiv
  have cases := allowed_list (p:=593) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_503

theorem htau5_505 : Closed 5 ⟨128738157601,128953438801,4,1⟩ := by
  exact closed_size (c:=128953438801) [(5278271,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_5278271) (by decide +kernel)

theorem htauRoot5_599 : RootAt 5 599 := by
  intro e he hdiv
  have cases := allowed_list (p:=599) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_505

theorem htau5_507 : Closed 5 ⟨3409957712839325763601,3415640975824698018010,5,2⟩ := by
  exact closed_size (c:=341564097582469801801) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_508 : Closed 5 ⟨130466162401,130683606005,4,1⟩ := by
  apply closed_split (c:=26136721201) (p:=26136721201) (by decide +kernel) (by decide +kernel) htauPrime5_26136721201 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=26136721201) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_507

theorem htauRoot5_601 : RootAt 5 601 := by
  intro e he hdiv
  have cases := allowed_list (p:=601) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_508

end OddPerfect.HarmonicChain
