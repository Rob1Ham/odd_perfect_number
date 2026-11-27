module

public import OddPerfect.HarmonicTau7.Part007
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem no_max_tau_7 : ∀ n, Small n 7 → ¬ 7∣n.divisors.card := by
  intro n H hd
  exact impossible_of_roots (M:=317) (by norm_num) (by decide +kernel) (root_join (root_join htauRange7_3 htauRange7_83) (root_join htauRange7_163 htauRange7_243)) H hd

end OddPerfect.HarmonicChain
