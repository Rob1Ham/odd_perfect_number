module

public import OddPerfect.DivisorCountBounds

public section

namespace OddPerfect.DivisorCountSearch

theorem bound2_5_2_1 : ResidualBound 5 2 1 (1/1 : ℚ) :=
  residual_envelope (C:=4) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bound2_7_2_1 : ResidualBound 7 2 1 (1/1 : ℚ) :=
  residual_envelope (C:=4) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end OddPerfect.DivisorCountSearch
