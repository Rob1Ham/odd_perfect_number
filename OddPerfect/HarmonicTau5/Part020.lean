module

public import OddPerfect.HarmonicTau5.Part019
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_570 : Closed 5 ⟨349707832321,350163181061,4,1⟩ := by
  apply closed_split (c:=350163181061) (p:=647251721) (by decide +kernel) (by decide +kernel) htauPrime5_647251721 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=647251721) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_569

theorem htauRoot5_769 : RootAt 5 769 := by
  intro e he hdiv
  have cases := allowed_list (p:=769) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_570

theorem htau5_572 : Closed 5 ⟨357040905841,357503394061,4,1⟩ := by
  exact closed_size (c:=357503394061) [(251,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_251) (by decide +kernel)

theorem htauRoot5_773 : RootAt 5 773 := by
  intro e he hdiv
  have cases := allowed_list (p:=773) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_572

theorem htau5_574 : Closed 5 ⟨258136907664495061,258465710228104342,5,2⟩ := by
  exact closed_size (c:=129232855114052171) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_575 : Closed 5 ⟨173700583304346391041961,173921834878585745857863,6,2⟩ := by
  exact closed_size (c:=57973944959528581952621) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_576 : Closed 5 ⟨383617958161,384106021721,4,1⟩ := by
  apply closed_split (c:=384106021721) (p:=672901) (by decide +kernel) (by decide +kernel) htauPrime5_672901 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=672901) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_574
  · exact htau5_575

theorem htauRoot5_787 : RootAt 5 787 := by
  intro e he hdiv
  have cases := allowed_list (p:=787) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_576

theorem htau5_578 : Closed 5 ⟨403490473681,403997371261,4,1⟩ := by
  exact closed_size (c:=403997371261) [(895781311,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_895781311) (by decide +kernel)

theorem htauRoot5_797 : RootAt 5 797 := by
  intro e he hdiv
  have cases := allowed_list (p:=797) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_578

theorem htau5_580 : Closed 5 ⟨78473662082778603601,78570783380568216602,5,2⟩ := by
  exact closed_size (c:=39285391690284108301) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_581 : Closed 5 ⟨428345379361,428875509781,4,1⟩ := by
  apply closed_split (c:=428875509781) (p:=183201841) (by decide +kernel) (by decide +kernel) htauPrime5_183201841 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=183201841) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_580

theorem htauRoot5_809 : RootAt 5 809 := by
  intro e he hdiv
  have cases := allowed_list (p:=809) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_581

theorem htau5_583 : Closed 5 ⟨5526356791409474281,5533179887245886410,5,2⟩ := by
  exact closed_size (c:=553317988724588641) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_584 : Closed 5 ⟨70598329319526199833364321,70685493283964559922794915,6,2⟩ := by
  exact closed_size (c:=4712366218930970661519661) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_585 : Closed 5 ⟨432596913841,433130984105,4,1⟩ := by
  apply closed_split (c:=86626196821) (p:=12774841) (by decide +kernel) (by decide +kernel) htauPrime5_12774841 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=12774841) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_583
  · exact htau5_584

theorem htauRoot5_811 : RootAt 5 811 := by
  intro e he hdiv
  have cases := allowed_list (p:=811) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_585

theorem htau5_587 : Closed 5 ⟨454331269681,454885332205,4,1⟩ := by
  exact closed_size (c:=90977066441) [(1789091,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_1789091) (by decide +kernel)

theorem htauRoot5_821 : RootAt 5 821 := by
  intro e he hdiv
  have cases := allowed_list (p:=821) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_587

theorem htau5_589 : Closed 5 ⟨458774574241,459332694161,4,1⟩ := by
  exact closed_size (c:=459332694161) [(222991,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_222991) (by decide +kernel)

theorem htauRoot5_823 : RootAt 5 823 := by
  intro e he hdiv
  have cases := allowed_list (p:=823) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_589

theorem htau5_591 : Closed 5 ⟨3591200919916110951661,3595548621255995969582,5,2⟩ := by
  exact closed_size (c:=1797774310627997984791) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_592 : Closed 5 ⟨467758877041,468325171081,4,1⟩ := by
  apply closed_split (c:=468325171081) (p:=7677461821) (by decide +kernel) (by decide +kernel) htauPrime5_7677461821 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=7677461821) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_591

theorem htauRoot5_827 : RootAt 5 827 := by
  intro e he hdiv
  have cases := allowed_list (p:=827) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_592

theorem htau5_594 : Closed 5 ⟨472300192081,472870602941,4,1⟩ := by
  exact closed_size (c:=472870602941) [(93249971,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_93249971) (by decide +kernel)

theorem htauRoot5_829 : RootAt 5 829 := by
  intro e he hdiv
  have cases := allowed_list (p:=829) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_594

theorem htau5_596 : Closed 5 ⟨495504774241,496096068721,4,1⟩ := by
  exact closed_size (c:=496096068721) [(11105551,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_11105551) (by decide +kernel)

theorem htauRoot5_839 : RootAt 5 839 := by
  intro e he hdiv
  have cases := allowed_list (p:=839) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_596

theorem htau5_598 : Closed 5 ⟨529414856881,530036235821,4,1⟩ := by
  exact closed_size (c:=530036235821) [(17097943091,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_17097943091) (by decide +kernel)

theorem htauRoot5_853 : RootAt 5 853 := by
  intro e he hdiv
  have cases := allowed_list (p:=853) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_598

end OddPerfect.HarmonicChain
