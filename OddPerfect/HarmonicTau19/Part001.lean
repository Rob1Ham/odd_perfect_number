module

public import OddPerfect.HarmonicTau19.Primes01
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau19_0 : Closed 19 ⟨5130050418713105469,7695308235877554300,20,3⟩ := by
  exact closed_size (c:=25651027452925181) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau19_1 : Closed 19 ⟨186677404686551194911441,280024571606815985854070,21,3⟩ := by
  exact closed_size (c:=28002457160681598585407) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau19_2 : Closed 19 ⟨6793004079138911431632426549,10189814136200638376906184600,22,3⟩ := by
  exact closed_size (c:=16983023560334397294843641) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau19_3 : Closed 19 ⟨140978054321721,211467662431370,19,2⟩ := by
  apply closed_split (c:=21146766243137) (p:=36389) (by decide +kernel) (by decide +kernel) htauPrime19_36389 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=36389) (r:=1) (E:=4) [1, 2, 3] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau19_0
  · exact htau19_1
  · exact htau19_2

theorem htau19_4 : Closed 19 ⟨51300363209076732969,76950756215069928663,20,2⟩ := by
  exact closed_size (c:=25650252071689976221) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau19_5 : Closed 19 ⟨387420489,581130733,18,1⟩ := by
  apply closed_split (c:=581130733) (p:=363889) (by decide +kernel) (by decide +kernel) htauPrime19_363889 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=363889) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau19_3
  · exact htau19_4

theorem htauRoot19_3 : RootAt 19 3 := by
  intro e he hdiv
  have cases := allowed_list (p:=3) (r:=19) (E:=32) [18] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau19_5

theorem htau19_7 : Closed 19 ⟨3814697265625,4768371582031,18,1⟩ := by
  exact closed_size (c:=4768371582031) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot19_5 : RootAt 19 5 := by
  intro e he hdiv
  have cases := allowed_list (p:=5) (r:=19) (E:=22) [18] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau19_7

theorem htauRange19_3 : RootRange 19 3 7 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=3) [3, 5] [0, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl
  · exact htauRoot19_3
  · exact htauRoot19_5

theorem no_max_tau_19 : ∀ n, Small n 19 → ¬ 19∣n.divisors.card := by
  intro n H hd
  exact impossible_of_roots (M:=7) (by norm_num) (by decide +kernel) htauRange19_3 H hd

end OddPerfect.HarmonicChain
