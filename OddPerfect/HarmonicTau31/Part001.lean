module

public import OddPerfect.HarmonicRoots
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau31_0 : Closed 31 ⟨205891132094649,308836698141973,30,1⟩ := by
  exact closed_size (c:=308836698141973) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot31_3 : RootAt 31 3 := by
  intro e he hdiv
  have cases := allowed_list (p:=3) (r:=31) (E:=32) [30] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau31_0

theorem htauRange31_3 : RootRange 31 3 4 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=3) [3] [0] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl
  · exact htauRoot31_3

theorem no_max_tau_31 : ∀ n, Small n 31 → ¬ 31∣n.divisors.card := by
  intro n H hd
  exact impossible_of_roots (M:=4) (by norm_num) (by decide +kernel) htauRange31_3 H hd

end OddPerfect.HarmonicChain
