module

public import OddPerfect.HarmonicRoots
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau29_0 : Closed 29 ⟨22876792454961,34315188682441,28,1⟩ := by
  exact closed_size (c:=34315188682441) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot29_3 : RootAt 29 3 := by
  intro e he hdiv
  have cases := allowed_list (p:=3) (r:=29) (E:=32) [28] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau29_0

theorem htauRange29_3 : RootRange 29 3 4 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=3) [3] [0] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl
  · exact htauRoot29_3

theorem no_max_tau_29 : ∀ n, Small n 29 → ¬ 29∣n.divisors.card := by
  intro n H hd
  exact impossible_of_roots (M:=4) (by norm_num) (by decide +kernel) htauRange29_3 H hd

end OddPerfect.HarmonicChain
