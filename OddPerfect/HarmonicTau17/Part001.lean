module

public import OddPerfect.HarmonicTau17.Primes01
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau17_0 : Closed 17 ⟨51269037340142241,76905783857344273,18,2⟩ := by
  exact closed_size (c:=5915829527488021) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau17_1 : Closed 17 ⟨43046721,64570081,16,1⟩ := by
  apply closed_split (c:=64570081) (p:=34511) (by decide +kernel) (by decide +kernel) htauPrime17_34511 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=34511) (r:=1) (E:=4) [2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau17_0

theorem htauRoot17_3 : RootAt 17 3 := by
  intro e he hdiv
  have cases := allowed_list (p:=3) (r:=17) (E:=32) [16] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau17_1

theorem htau17_3 : Closed 17 ⟨71158509674072265625,88948137283208609210,17,2⟩ := by
  exact closed_size (c:=1270687675474408703) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau17_4 : Closed 17 ⟨152587890625,190734863281,16,1⟩ := by
  apply closed_split (c:=190734863281) (p:=466344409) (by decide +kernel) (by decide +kernel) htauPrime17_466344409 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=466344409) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau17_3

theorem htauRoot17_5 : RootAt 17 5 := by
  intro e he hdiv
  have cases := allowed_list (p:=5) (r:=17) (E:=22) [16] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau17_4

theorem htau17_6 : Closed 17 ⟨33232930569601,38771752331201,16,1⟩ := by
  exact closed_size (c:=38771752331201) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot17_7 : RootAt 17 7 := by
  intro e he hdiv
  have cases := allowed_list (p:=7) (r:=17) (E:=18) [16] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau17_6

theorem htauRange17_3 : RootRange 17 3 9 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=3) [3, 5, 7] [0, 2, 0, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl
  · exact htauRoot17_3
  · exact htauRoot17_5
  · exact htauRoot17_7

theorem no_max_tau_17 : ∀ n, Small n 17 → ¬ 17∣n.divisors.card := by
  intro n H hd
  exact impossible_of_roots (M:=9) (by norm_num) (by decide +kernel) htauRange17_3 H hd

end OddPerfect.HarmonicChain
