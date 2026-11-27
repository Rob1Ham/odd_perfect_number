module

public import OddPerfect.HarmonicTau11.Primes01
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau11_0 : Closed 11 ⟨999254375218355769,1499263733156291258,13,3⟩ := by
  exact closed_size (c:=749631866578145629) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau11_1 : Closed 11 ⟨1140230181728536619246289,1710781359895027881546267,14,3⟩ := by
  exact closed_size (c:=11637968434660053615961) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau11_2 : Closed 11 ⟨875708538849,1313896576369,12,2⟩ := by
  apply closed_split (c:=1313896576369) (p:=1141081) (by decide +kernel) (by decide +kernel) htauPrime11_1141081 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=1141081) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau11_0
  · exact htau11_1

theorem htau11_3 : Closed 11 ⟨12986933648546978649,19485350321105303365,14,2⟩ := by
  exact closed_size (c:=3897070064221060673) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau11_4 : Closed 11 ⟨59049,88573,10,1⟩ := by
  apply closed_split (c:=88573) (p:=3851) (by decide +kernel) (by decide +kernel) htauPrime11_3851 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=3851) (r:=1) (E:=5) [2, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau11_2
  · exact htau11_3

theorem htauRoot11_3 : RootAt 11 3 := by
  intro e he hdiv
  have cases := allowed_list (p:=3) (r:=11) (E:=32) [10] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau11_4

theorem htau11_6 : Closed 11 ⟨1455191463232041015625,1818989440798767852783,12,2⟩ := by
  exact closed_size (c:=86618544799941326323) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau11_7 : Closed 11 ⟨9765625,12207031,10,1⟩ := by
  apply closed_split (c:=12207031) (p:=12207031) (by decide +kernel) (by decide +kernel) htauPrime11_12207031 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=12207031) (r:=1) (E:=3) [2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau11_6

theorem htau11_8 : Closed 11 ⟨476837158203125,596046447753906,21,1⟩ := by
  exact closed_size (c:=99341074625651) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot11_5 : RootAt 11 5 := by
  intro e he hdiv
  have cases := allowed_list (p:=5) (r:=11) (E:=22) [10, 21] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau11_7
  · exact htau11_8

theorem htau11_10 : Closed 11 ⟨282475249,329554457,10,1⟩ := by
  exact closed_size (c:=329554457) [(293459,1),(1123,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl
    · exact htauPrime11_293459
    · exact htauPrime11_1123) (by decide +kernel)

theorem htauRoot11_7 : RootAt 11 7 := by
  intro e he hdiv
  have cases := allowed_list (p:=7) (r:=11) (E:=18) [10] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau11_10

theorem htau11_12 : Closed 11 ⟨46845919758385913,51530540265210954,11,2⟩ := by
  exact closed_size (c:=8588423377535159) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau11_13 : Closed 11 ⟨84609024672577656486169,93069978670049482928863,12,2⟩ := by
  exact closed_size (c:=93069978670049482928863) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau11_14 : Closed 11 ⟨25937424601,28531167061,10,1⟩ := by
  apply closed_split (c:=28531167061) (p:=1806113) (by decide +kernel) (by decide +kernel) htauPrime11_1806113 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=1806113) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau11_12
  · exact htau11_13

theorem htauRoot11_11 : RootAt 11 11 := by
  intro e he hdiv
  have cases := allowed_list (p:=11) (r:=11) (E:=15) [10] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau11_14

theorem htau11_16 : Closed 11 ⟨137858491849,149346699503,10,1⟩ := by
  exact closed_size (c:=149346699503) [(859,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime11_859) (by decide +kernel)

theorem htauRoot11_13 : RootAt 11 13 := by
  intro e he hdiv
  have cases := allowed_list (p:=13) (r:=11) (E:=14) [10] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau11_16

theorem htau11_18 : Closed 11 ⟨2015993900449,2141993519227,10,1⟩ := by
  exact closed_size (c:=2141993519227) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot11_17 : RootAt 11 17 := by
  intro e he hdiv
  have cases := allowed_list (p:=17) (r:=11) (E:=13) [10] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau11_18

theorem htau11_20 : Closed 11 ⟨6131066257801,6471681049901,10,1⟩ := by
  exact closed_size (c:=6471681049901) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot11_19 : RootAt 11 19 := by
  intro e he hdiv
  have cases := allowed_list (p:=19) (r:=11) (E:=12) [10] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau11_20

theorem htau11_22 : Closed 11 ⟨41426511213649,43309534450633,10,1⟩ := by
  exact closed_size (c:=3937230404603) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot11_23 : RootAt 11 23 := by
  intro e he hdiv
  have cases := allowed_list (p:=23) (r:=11) (E:=12) [10] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau11_22

theorem htau11_24 : Closed 11 ⟨420707233300201,435732491632351,10,1⟩ := by
  exact closed_size (c:=435732491632351) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot11_29 : RootAt 11 29 := by
  intro e he hdiv
  have cases := allowed_list (p:=29) (r:=11) (E:=11) [10] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau11_24

theorem htau11_26 : Closed 11 ⟨819628286980801,846949229880161,10,1⟩ := by
  exact closed_size (c:=846949229880161) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot11_31 : RootAt 11 31 := by
  intro e he hdiv
  have cases := allowed_list (p:=31) (r:=11) (E:=11) [10] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau11_26

theorem htauRange11_3 : RootRange 11 3 32 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=3) [3, 5, 7, 11, 13, 17, 19, 23, 29, 31] [0, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot11_3
  · exact htauRoot11_5
  · exact htauRoot11_7
  · exact htauRoot11_11
  · exact htauRoot11_13
  · exact htauRoot11_17
  · exact htauRoot11_19
  · exact htauRoot11_23
  · exact htauRoot11_29
  · exact htauRoot11_31

theorem no_max_tau_11 : ∀ n, Small n 11 → ¬ 11∣n.divisors.card := by
  intro n H hd
  exact impossible_of_roots (M:=32) (by norm_num) (by decide +kernel) htauRange11_3 H hd

end OddPerfect.HarmonicChain
