module

public import OddPerfect.HarmonicTau23.Primes01
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau23_0 : Closed 23 ⟨31381059609,47071589413,22,1⟩ := by
  exact closed_size (c:=47071589413) [(1001523179,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime23_1001523179) (by decide +kernel)

theorem htauRoot23_3 : RootAt 23 3 := by
  intro e he hdiv
  have cases := allowed_list (p:=3) (r:=23) (E:=32) [22] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau23_0

theorem htauRange23_3 : RootRange 23 3 5 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=3) [3] [0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl
  · exact htauRoot23_3

theorem no_max_tau_23 : ∀ n, Small n 23 → ¬ 23∣n.divisors.card := by
  intro n H hd
  exact impossible_of_roots (M:=5) (by norm_num) (by decide +kernel) htauRange23_3 H hd

end OddPerfect.HarmonicChain
