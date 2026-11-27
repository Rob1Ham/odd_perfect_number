module

public import OddPerfect.HarmonicTau13.Primes01
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau13_0 : Closed 13 ⟨104184438725488527477,156530433683134473432,15,4⟩ := by
  exact closed_size (c:=6522101403463936393) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau13_1 : Closed 13 ⟨64281798693626421453309,96579530867985366765268,16,4⟩ := by
  exact closed_size (c:=24144882716996341691317) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau13_2 : Closed 13 ⟨39661869793967502036691653,59589570798832462690828080,17,4⟩ := by
  exact closed_size (c:=248289878328468594545117) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau13_3 : Closed 13 ⟨24471373662877948756638749901,36766765183132914971637583084,18,4⟩ := by
  exact closed_size (c:=9191691295783228742909395771) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau13_4 : Closed 13 ⟨15098837549995694382846108688917,22685094117993261822991785420552,19,4⟩ := by
  exact closed_size (c:=315070751638795303097108130841) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau13_5 : Closed 13 ⟨168856464709057581,253285491396657724,14,3⟩ := by
  apply closed_split (c:=63321372849164431) (p:=617) (by decide +kernel) (by decide +kernel) htauPrime13_617 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=617) (r:=1) (E:=6) [1, 2, 3, 4, 5] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl|rfl
  · exact htau13_0
  · exact htau13_1
  · exact htau13_2
  · exact htau13_3
  · exact htau13_4

theorem htau13_6 : Closed 13 ⟨67302978560200879692561,100954784447006698746726,15,3⟩ := by
  exact closed_size (c:=16825797407834449791121) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau13_7 : Closed 13 ⟨423644039001,635466457082,13,2⟩ := by
  apply closed_split (c:=317733228541) (p:=398581) (by decide +kernel) (by decide +kernel) htauPrime13_398581 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=398581) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau13_5
  · exact htau13_6

theorem htau13_8 : Closed 13 ⟨337712505774076161,506569076394741363,14,2⟩ := by
  exact closed_size (c:=168856358798247121) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau13_9 : Closed 13 ⟨531441,797161,12,1⟩ := by
  apply closed_split (c:=797161) (p:=797161) (by decide +kernel) (by decide +kernel) htauPrime13_797161 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=797161) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau13_7
  · exact htau13_8

theorem htauRoot13_3 : RootAt 13 3 := by
  intro e he hdiv
  have cases := allowed_list (p:=3) (r:=13) (E:=32) [12] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau13_9

theorem htau13_11 : Closed 13 ⟨74505805908203125,93132257614135742,13,2⟩ := by
  exact closed_size (c:=46566128807067871) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau13_12 : Closed 13 ⟨244140625,305175781,12,1⟩ := by
  apply closed_split (c:=305175781) (p:=305175781) (by decide +kernel) (by decide +kernel) htauPrime13_305175781 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=305175781) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau13_11

theorem htauRoot13_5 : RootAt 13 5 := by
  intro e he hdiv
  have cases := allowed_list (p:=5) (r:=13) (E:=22) [12] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau13_12

theorem htau13_14 : Closed 13 ⟨223511436608353935601,260763342723203065202,13,2⟩ := by
  exact closed_size (c:=130381671361601532601) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau13_15 : Closed 13 ⟨13841287201,16148168401,12,1⟩ := by
  apply closed_split (c:=16148168401) (p:=16148168401) (by decide +kernel) (by decide +kernel) htauPrime13_16148168401 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=16148168401) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau13_14

theorem htauRoot13_7 : RootAt 13 7 := by
  intro e he hdiv
  have cases := allowed_list (p:=7) (r:=13) (E:=18) [12] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau13_15

theorem htau13_17 : Closed 13 ⟨3138428376721,3452271214393,12,1⟩ := by
  exact closed_size (c:=3452271214393) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot13_11 : RootAt 13 11 := by
  intro e he hdiv
  have cases := allowed_list (p:=11) (r:=13) (E:=15) [12] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau13_17

theorem htau13_19 : Closed 13 ⟨23298085122481,25239592216021,12,1⟩ := by
  exact closed_size (c:=25239592216021) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot13_13 : RootAt 13 13 := by
  intro e he hdiv
  have cases := allowed_list (p:=13) (r:=13) (E:=14) [12] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau13_19

theorem htau13_21 : Closed 13 ⟨582622237229761,619036127056621,12,1⟩ := by
  exact closed_size (c:=619036127056621) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot13_17 : RootAt 13 17 := by
  intro e he hdiv
  have cases := allowed_list (p:=17) (r:=13) (E:=13) [12] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau13_21

theorem htauRange13_3 : RootRange 13 3 18 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=3) [3, 5, 7, 11, 13, 17] [0, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot13_3
  · exact htauRoot13_5
  · exact htauRoot13_7
  · exact htauRoot13_11
  · exact htauRoot13_13
  · exact htauRoot13_17

theorem no_max_tau_13 : ∀ n, Small n 13 → ¬ 13∣n.divisors.card := by
  intro n H hd
  exact impossible_of_roots (M:=18) (by norm_num) (by decide +kernel) htauRange13_3 H hd

end OddPerfect.HarmonicChain
