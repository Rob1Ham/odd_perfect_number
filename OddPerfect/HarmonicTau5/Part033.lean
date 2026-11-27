module

public import OddPerfect.HarmonicTau5.Part032
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_960 : Closed 5 ⟨20855379099361,20865142853621,4,1⟩ := by
  exact closed_size (c:=20865142853621) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2137 : RootAt 5 2137 := by
  intro e he hdiv
  have cases := allowed_list (p:=2137) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_960

theorem htau5_962 : Closed 5 ⟨21011965022161,21021783697405,4,1⟩ := by
  exact closed_size (c:=4204356739481) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2141 : RootAt 5 2141 := by
  intro e he hdiv
  have cases := allowed_list (p:=2141) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_962

theorem htau5_964 : Closed 5 ⟨21090587817601,21100434030401,4,1⟩ := by
  exact closed_size (c:=21100434030401) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2143 : RootAt 5 2143 := by
  intro e he hdiv
  have cases := allowed_list (p:=2143) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_964

theorem htau5_966 : Closed 5 ⟨21487016597281,21497001270421,4,1⟩ := by
  exact closed_size (c:=21497001270421) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2153 : RootAt 5 2153 := by
  intro e he hdiv
  have cases := allowed_list (p:=2153) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_966

theorem htau5_968 : Closed 5 ⟨21808162146241,21818258517605,4,1⟩ := by
  exact closed_size (c:=4363651703521) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2161 : RootAt 5 2161 := by
  intro e he hdiv
  have cases := allowed_list (p:=2161) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_968

theorem htau5_970 : Closed 5 ⟨22543893337681,22554244069241,4,1⟩ := by
  exact closed_size (c:=22554244069241) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2179 : RootAt 5 2179 := by
  intro e he hdiv
  have cases := allowed_list (p:=2179) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_970

theorem htau5_972 : Closed 5 ⟨23553637597681,23564334072521,4,1⟩ := by
  exact closed_size (c:=23564334072521) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2203 : RootAt 5 2203 := by
  intro e he hdiv
  have cases := allowed_list (p:=2203) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_972

theorem htau5_974 : Closed 5 ⟨23725169980801,23735924817601,4,1⟩ := by
  exact closed_size (c:=23735924817601) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2207 : RootAt 5 2207 := by
  intro e he hdiv
  have cases := allowed_list (p:=2207) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_974

theorem htau5_976 : Closed 5 ⟨23984223122161,23995065899341,4,1⟩ := by
  exact closed_size (c:=23995065899341) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2213 : RootAt 5 2213 := by
  intro e he hdiv
  have cases := allowed_list (p:=2213) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_976

theorem htau5_978 : Closed 5 ⟨24332920331281,24343881106205,4,1⟩ := by
  exact closed_size (c:=4868776221241) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2221 : RootAt 5 2221 := by
  intro e he hdiv
  have cases := allowed_list (p:=2221) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_978

theorem htau5_980 : Closed 5 ⟨25041707380561,25052906713021,4,1⟩ := by
  exact closed_size (c:=25052906713021) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2237 : RootAt 5 2237 := by
  intro e he hdiv
  have cases := allowed_list (p:=2237) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_980

theorem htau5_982 : Closed 5 ⟨25131382160641,25142611553921,4,1⟩ := by
  exact closed_size (c:=25142611553921) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2239 : RootAt 5 2239 := by
  intro e he hdiv
  have cases := allowed_list (p:=2239) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_982

theorem htau5_984 : Closed 5 ⟨25311454040401,25322743716601,4,1⟩ := by
  exact closed_size (c:=25322743716601) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2243 : RootAt 5 2243 := by
  intro e he hdiv
  have cases := allowed_list (p:=2243) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_984

theorem htau5_986 : Closed 5 ⟨25674499134001,25685910022505,4,1⟩ := by
  exact closed_size (c:=5137182004501) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2251 : RootAt 5 2251 := by
  intro e he hdiv
  have cases := allowed_list (p:=2251) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_986

theorem htau5_988 : Closed 5 ⟨26412291425521,26423947335241,4,1⟩ := by
  exact closed_size (c:=26423947335241) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2267 : RootAt 5 2267 := by
  intro e he hdiv
  have cases := allowed_list (p:=2267) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_988

end OddPerfect.HarmonicChain
