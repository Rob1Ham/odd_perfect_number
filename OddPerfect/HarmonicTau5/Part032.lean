module

public import OddPerfect.HarmonicTau5.Part031
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_930 : Closed 5 ⟨16881653995441,16889986499881,4,1⟩ := by
  exact closed_size (c:=16889986499881) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2027 : RootAt 5 2027 := by
  intro e he hdiv
  have cases := allowed_list (p:=2027) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_930

theorem htau5_932 : Closed 5 ⟨16948379819281,16956737008541,4,1⟩ := by
  exact closed_size (c:=16956737008541) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2029 : RootAt 5 2029 := by
  intro e he hdiv
  have cases := allowed_list (p:=2029) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_932

theorem htau5_934 : Closed 5 ⟨17284980865441,17293462210321,4,1⟩ := by
  exact closed_size (c:=17293462210321) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2039 : RootAt 5 2039 := by
  intro e he hdiv
  have cases := allowed_list (p:=2039) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_934

theorem htau5_936 : Closed 5 ⟨17764614906481,17773272126221,4,1⟩ := by
  exact closed_size (c:=17773272126221) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2053 : RootAt 5 2053 := by
  intro e he hdiv
  have cases := allowed_list (p:=2053) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_936

theorem htau5_938 : Closed 5 ⟨18113272128961,18122056451041,4,1⟩ := by
  exact closed_size (c:=18122056451041) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2063 : RootAt 5 2063 := by
  intro e he hdiv
  have cases := allowed_list (p:=2063) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_938

theorem htau5_940 : Closed 5 ⟨18324914739121,18333775916461,4,1⟩ := by
  exact closed_size (c:=18333775916461) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2069 : RootAt 5 2069 := by
  intro e he hdiv
  have cases := allowed_list (p:=2069) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_940

theorem htau5_942 : Closed 5 ⟨18753758574721,18762774804805,4,1⟩ := by
  exact closed_size (c:=3752554960961) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2081 : RootAt 5 2081 := by
  intro e he hdiv
  have cases := allowed_list (p:=2081) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_942

theorem htau5_944 : Closed 5 ⟨18825957754321,18835000001081,4,1⟩ := by
  exact closed_size (c:=18835000001081) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2083 : RootAt 5 2083 := by
  intro e he hdiv
  have cases := allowed_list (p:=2083) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_944

theorem htau5_946 : Closed 5 ⟨18970981313761,18980075743921,4,1⟩ := by
  exact closed_size (c:=18980075743921) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2087 : RootAt 5 2087 := by
  intro e he hdiv
  have cases := allowed_list (p:=2087) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_946

theorem htau5_948 : Closed 5 ⟨19043806494241,19052927091221,4,1⟩ := by
  exact closed_size (c:=19052927091221) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2089 : RootAt 5 2089 := by
  intro e he hdiv
  have cases := allowed_list (p:=2089) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_948

theorem htau5_950 : Closed 5 ⟨19411082451601,19420334635801,4,1⟩ := by
  exact closed_size (c:=19420334635801) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2099 : RootAt 5 2099 := by
  intro e he hdiv
  have cases := allowed_list (p:=2099) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_950

theorem htau5_952 : Closed 5 ⟨19858796855041,19868208607105,4,1⟩ := by
  exact closed_size (c:=3973641721421) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2111 : RootAt 5 2111 := by
  intro e he hdiv
  have cases := allowed_list (p:=2111) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_952

theorem htau5_954 : Closed 5 ⟨19934162223361,19943600747141,4,1⟩ := by
  exact closed_size (c:=19943600747141) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2113 : RootAt 5 2113 := by
  intro e he hdiv
  have cases := allowed_list (p:=2113) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_954

theorem htau5_956 : Closed 5 ⟨20544834434881,20554488962341,4,1⟩ := by
  exact closed_size (c:=20554488962341) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2129 : RootAt 5 2129 := by
  intro e he hdiv
  have cases := allowed_list (p:=2129) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_956

theorem htau5_958 : Closed 5 ⟨20622143227921,20631824985305,4,1⟩ := by
  exact closed_size (c:=4126364997061) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2131 : RootAt 5 2131 := by
  intro e he hdiv
  have cases := allowed_list (p:=2131) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_958

end OddPerfect.HarmonicChain
