module

public import OddPerfect.HarmonicTau5.Part062
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htauRange5_5123 : RootRange 5 5123 5203 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=5123) [5147, 5153, 5167, 5171, 5179, 5189, 5197] [47, 2, 5, 2, 3, 2, 23, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 53, 2, 37, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 31, 2, 0, 2, 3, 2, 71, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_5147
  · exact htauRoot5_5153
  · exact htauRoot5_5167
  · exact htauRoot5_5171
  · exact htauRoot5_5179
  · exact htauRoot5_5189
  · exact htauRoot5_5197

theorem htauRange5_5203 : RootRange 5 5203 5283 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=5203) [5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281] [11, 2, 3, 2, 41, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 17, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 29, 2, 59, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 19, 2, 3, 2, 23, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_5209
  · exact htauRoot5_5227
  · exact htauRoot5_5231
  · exact htauRoot5_5233
  · exact htauRoot5_5237
  · exact htauRoot5_5261
  · exact htauRoot5_5273
  · exact htauRoot5_5279
  · exact htauRoot5_5281

theorem htauRange5_5283 : RootRange 5 5283 5363 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=5283) [5297, 5303, 5309, 5323, 5333, 5347, 5351] [3, 2, 5, 2, 17, 2, 3, 2, 11, 2, 67, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 47, 2, 3, 2, 5, 2, 13, 2, 3, 2, 17, 2, 0, 2, 3, 2, 7, 2, 73, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 53, 2, 3, 2, 11, 2, 23, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_5297
  · exact htauRoot5_5303
  · exact htauRoot5_5309
  · exact htauRoot5_5323
  · exact htauRoot5_5333
  · exact htauRoot5_5347
  · exact htauRoot5_5351

theorem htauRange5_5363 : RootRange 5 5363 5443 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=5363) [5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441] [31, 2, 5, 2, 3, 2, 7, 2, 41, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 61, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_5381
  · exact htauRoot5_5387
  · exact htauRoot5_5393
  · exact htauRoot5_5399
  · exact htauRoot5_5407
  · exact htauRoot5_5413
  · exact htauRoot5_5417
  · exact htauRoot5_5419
  · exact htauRoot5_5431
  · exact htauRoot5_5437
  · exact htauRoot5_5441

theorem htauRange5_5443 : RootRange 5 5443 5523 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=5443) [5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521] [0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 53, 2, 43, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 17, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 37, 2, 5, 2, 3, 2, 0, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_5443
  · exact htauRoot5_5449
  · exact htauRoot5_5471
  · exact htauRoot5_5477
  · exact htauRoot5_5479
  · exact htauRoot5_5483
  · exact htauRoot5_5501
  · exact htauRoot5_5503
  · exact htauRoot5_5507
  · exact htauRoot5_5519
  · exact htauRoot5_5521

theorem htauRange5_5523 : RootRange 5 5523 5603 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=5523) [5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591] [3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 29, 2, 3, 2, 23, 2, 5, 2, 3, 2, 31, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 67, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 37, 2, 3, 2, 0, 2, 7, 2, 3, 2, 29, 2, 11, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_5527
  · exact htauRoot5_5531
  · exact htauRoot5_5557
  · exact htauRoot5_5563
  · exact htauRoot5_5569
  · exact htauRoot5_5573
  · exact htauRoot5_5581
  · exact htauRoot5_5591

theorem htauRange5_5603 : RootRange 5 5603 5624 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=5603) [5623] [13, 2, 5, 2, 3, 2, 71, 2, 31, 2, 3, 2, 5, 2, 41, 2, 3, 2, 7, 2, 0] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl
  · exact htauRoot5_5623

theorem no_max_tau_5 : ∀ n, Small n 5 → ¬ 5∣n.divisors.card := by
  intro n H hd
  exact impossible_of_roots (M:=5624) (by norm_num) (by decide +kernel) (root_join (root_join (root_join (root_join (root_join (root_join (root_join htauRange5_3 htauRange5_83) (root_join htauRange5_163 htauRange5_243)) (root_join (root_join htauRange5_323 htauRange5_403) (root_join htauRange5_483 htauRange5_563))) (root_join (root_join (root_join htauRange5_643 htauRange5_723) (root_join htauRange5_803 htauRange5_883)) (root_join (root_join htauRange5_963 htauRange5_1043) (root_join htauRange5_1123 htauRange5_1203)))) (root_join (root_join (root_join (root_join htauRange5_1283 htauRange5_1363) (root_join htauRange5_1443 htauRange5_1523)) (root_join (root_join htauRange5_1603 htauRange5_1683) (root_join htauRange5_1763 htauRange5_1843))) (root_join (root_join (root_join htauRange5_1923 htauRange5_2003) (root_join htauRange5_2083 htauRange5_2163)) (root_join (root_join htauRange5_2243 htauRange5_2323) (root_join htauRange5_2403 htauRange5_2483))))) (root_join (root_join (root_join (root_join (root_join htauRange5_2563 htauRange5_2643) (root_join htauRange5_2723 htauRange5_2803)) (root_join (root_join htauRange5_2883 htauRange5_2963) (root_join htauRange5_3043 htauRange5_3123))) (root_join (root_join (root_join htauRange5_3203 htauRange5_3283) (root_join htauRange5_3363 htauRange5_3443)) (root_join (root_join htauRange5_3523 htauRange5_3603) (root_join htauRange5_3683 htauRange5_3763)))) (root_join (root_join (root_join (root_join htauRange5_3843 htauRange5_3923) (root_join htauRange5_4003 htauRange5_4083)) (root_join (root_join htauRange5_4163 htauRange5_4243) (root_join htauRange5_4323 htauRange5_4403))) (root_join (root_join (root_join htauRange5_4483 htauRange5_4563) (root_join htauRange5_4643 htauRange5_4723)) (root_join (root_join htauRange5_4803 htauRange5_4883) (root_join htauRange5_4963 htauRange5_5043)))))) (root_join (root_join (root_join htauRange5_5123 htauRange5_5203) (root_join htauRange5_5283 htauRange5_5363)) (root_join (root_join htauRange5_5443 htauRange5_5523) htauRange5_5603))) H hd

end OddPerfect.HarmonicChain
