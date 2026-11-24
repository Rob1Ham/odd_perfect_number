module

public import OddPerfect.DivisorCountBounds

public section

namespace OddPerfect.DivisorCountSearch

theorem bound3_5_3_1 : ResidualBound 5 3 1 (64/35 : ℚ) :=
  residual_envelope (C:=8) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bound3_5_4_1 : ResidualBound 5 4 1 (331776/25025 : ℚ) :=
  residual_envelope (C:=16) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bound3_7_3_1 : ResidualBound 7 3 1 (8/7 : ℚ) :=
  residual_envelope (C:=8) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bound3_7_4_1 : ResidualBound 7 4 1 (4096/1001 : ℚ) :=
  residual_envelope (C:=16) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bound3_11_3_1 : ResidualBound 11 3 1 (1/1 : ℚ) :=
  residual_envelope (C:=8) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bound3_11_4_1 : ResidualBound 11 4 1 (256/143 : ℚ) :=
  residual_envelope (C:=16) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bound3_13_3_1 : ResidualBound 13 3 1 (1/1 : ℚ) :=
  residual_envelope (C:=8) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bound3_13_4_1 : ResidualBound 13 4 1 (16/13 : ℚ) :=
  residual_envelope (C:=16) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bound3_17_3_1 : ResidualBound 17 3 1 (1/1 : ℚ) :=
  residual_envelope (C:=8) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bound3_17_4_1 : ResidualBound 17 4 1 (1/1 : ℚ) :=
  residual_envelope (C:=16) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bound3_19_3_1 : ResidualBound 19 3 1 (1/1 : ℚ) :=
  residual_envelope (C:=8) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bound3_23_3_1 : ResidualBound 23 3 1 (1/1 : ℚ) :=
  residual_envelope (C:=8) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end OddPerfect.DivisorCountSearch
