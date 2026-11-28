module

public import OddPerfect.IndexSieveRanges

public section

namespace OddPerfect.IndexSieve

private def rows : List Row := [
  ⟨343,3,3⟩, ⟨345,5,5⟩, ⟨351,3,13⟩, ⟨357,3,17⟩, ⟨363,11,11⟩, ⟨369,41,41⟩,
  ⟨375,3,5⟩, ⟨385,5,7⟩, ⟨387,3,3⟩, ⟨399,3,19⟩, ⟨405,5,5⟩, ⟨423,47,47⟩,
  ⟨425,17,17⟩, ⟨429,11,11⟩, ⟨435,3,5⟩, ⟨455,5,5⟩, ⟨459,3,17⟩, ⟨465,3,31⟩,
  ⟨475,19,19⟩, ⟨477,53,53⟩, ⟨483,7,23⟩, ⟨495,3,5⟩, ⟨507,3,13⟩]

set_option maxRecDepth 20000 in
private theorem rows_valid : ∀ z : Fin rows.length, (rows.get z).exactValid := by decide +kernel

set_option maxRecDepth 20000 in
theorem covers_343_511 : Covers 343 511 := covers_of_table rows rows_valid (by decide +kernel)

end OddPerfect.IndexSieve
