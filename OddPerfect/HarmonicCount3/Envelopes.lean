module

public import OddPerfect.HarmonicSearch

public section

namespace OddPerfect.HarmonicSearch

open DivisorCountSearch

theorem envH3_5 : ResidualBound 5 3 1 (64/35 : ℚ) :=
  residual_envelope (C:=8) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem envH3_7 : ResidualBound 7 3 1 (8/7 : ℚ) :=
  residual_envelope (C:=8) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem envH3_11 : ResidualBound 11 3 1 (1/1 : ℚ) :=
  residual_envelope (C:=8) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem envH3_13 : ResidualBound 13 3 1 (1/1 : ℚ) :=
  residual_envelope (C:=8) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem envH3_17 : ResidualBound 17 3 1 (1/1 : ℚ) :=
  residual_envelope (C:=8) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end OddPerfect.HarmonicSearch
