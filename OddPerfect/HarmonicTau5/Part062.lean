module

public import OddPerfect.HarmonicTau5.Part061
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htauRange5_2723 : RootRange 5 2723 2803 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=2723) [2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801] [7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2, 41, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 47, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_2729
  · exact htauRoot5_2731
  · exact htauRoot5_2741
  · exact htauRoot5_2749
  · exact htauRoot5_2753
  · exact htauRoot5_2767
  · exact htauRoot5_2777
  · exact htauRoot5_2789
  · exact htauRoot5_2791
  · exact htauRoot5_2797
  · exact htauRoot5_2801

theorem htauRange5_2803 : RootRange 5 2803 2883 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=2803) [2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879] [0, 2, 3, 2, 7, 2, 53, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 47, 2, 19, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 43, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_2803
  · exact htauRoot5_2819
  · exact htauRoot5_2833
  · exact htauRoot5_2837
  · exact htauRoot5_2843
  · exact htauRoot5_2851
  · exact htauRoot5_2857
  · exact htauRoot5_2861
  · exact htauRoot5_2879

theorem htauRange5_2883 : RootRange 5 2883 2963 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=2883) [2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957] [3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 41, 2, 3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 37, 2, 3, 2, 0, 2, 29, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_2887
  · exact htauRoot5_2897
  · exact htauRoot5_2903
  · exact htauRoot5_2909
  · exact htauRoot5_2917
  · exact htauRoot5_2927
  · exact htauRoot5_2939
  · exact htauRoot5_2953
  · exact htauRoot5_2957

theorem htauRange5_2963 : RootRange 5 2963 3043 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=2963) [2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041] [0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 19, 2, 3, 2, 29, 2, 7, 2, 3, 2, 41, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2, 23, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_2963
  · exact htauRoot5_2969
  · exact htauRoot5_2971
  · exact htauRoot5_2999
  · exact htauRoot5_3001
  · exact htauRoot5_3011
  · exact htauRoot5_3019
  · exact htauRoot5_3023
  · exact htauRoot5_3037
  · exact htauRoot5_3041

theorem htauRange5_3043 : RootRange 5 3043 3123 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=3043) [3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121] [17, 2, 3, 2, 11, 2, 0, 2, 3, 2, 43, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 37, 2, 7, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 29, 2, 3, 2, 13, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_3049
  · exact htauRoot5_3061
  · exact htauRoot5_3067
  · exact htauRoot5_3079
  · exact htauRoot5_3083
  · exact htauRoot5_3089
  · exact htauRoot5_3109
  · exact htauRoot5_3119
  · exact htauRoot5_3121

theorem htauRange5_3123 : RootRange 5 3123 3203 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=3123) [3137, 3163, 3167, 3169, 3181, 3187, 3191] [3, 2, 5, 2, 53, 2, 3, 2, 31, 2, 13, 2, 3, 2, 0, 2, 43, 2, 3, 2, 7, 2, 5, 2, 3, 2, 47, 2, 23, 2, 3, 2, 5, 2, 7, 2, 3, 2, 29, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 31, 2, 3, 2, 23, 2, 7, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_3137
  · exact htauRoot5_3163
  · exact htauRoot5_3167
  · exact htauRoot5_3169
  · exact htauRoot5_3181
  · exact htauRoot5_3187
  · exact htauRoot5_3191

theorem htauRange5_3203 : RootRange 5 3203 3283 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=3203) [3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271] [0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 53, 2, 5, 2, 3, 2, 41, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 17, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_3203
  · exact htauRoot5_3209
  · exact htauRoot5_3217
  · exact htauRoot5_3221
  · exact htauRoot5_3229
  · exact htauRoot5_3251
  · exact htauRoot5_3253
  · exact htauRoot5_3257
  · exact htauRoot5_3259
  · exact htauRoot5_3271

theorem htauRange5_3283 : RootRange 5 3283 3363 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=3283) [3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361] [7, 2, 3, 2, 19, 2, 11, 2, 3, 2, 37, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 31, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 47, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_3299
  · exact htauRoot5_3301
  · exact htauRoot5_3307
  · exact htauRoot5_3313
  · exact htauRoot5_3319
  · exact htauRoot5_3323
  · exact htauRoot5_3329
  · exact htauRoot5_3331
  · exact htauRoot5_3343
  · exact htauRoot5_3347
  · exact htauRoot5_3359
  · exact htauRoot5_3361

theorem htauRange5_3363 : RootRange 5 3363 3443 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=3363) [3371, 3373, 3389, 3391, 3407, 3413, 3433] [3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 31, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 43, 2, 3, 2, 19, 2, 41, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2, 23, 2, 3, 2, 47, 2, 0, 2, 3, 2, 7, 2, 19, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_3371
  · exact htauRoot5_3373
  · exact htauRoot5_3389
  · exact htauRoot5_3391
  · exact htauRoot5_3407
  · exact htauRoot5_3413
  · exact htauRoot5_3433

theorem htauRange5_3443 : RootRange 5 3443 3523 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=3443) [3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517] [11, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 7, 2, 59, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 31, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_3449
  · exact htauRoot5_3457
  · exact htauRoot5_3461
  · exact htauRoot5_3463
  · exact htauRoot5_3467
  · exact htauRoot5_3469
  · exact htauRoot5_3491
  · exact htauRoot5_3499
  · exact htauRoot5_3511
  · exact htauRoot5_3517

theorem htauRange5_3523 : RootRange 5 3523 3603 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=3523) [3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593] [13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 53, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 43, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 59, 2, 13, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_3527
  · exact htauRoot5_3529
  · exact htauRoot5_3533
  · exact htauRoot5_3539
  · exact htauRoot5_3541
  · exact htauRoot5_3547
  · exact htauRoot5_3557
  · exact htauRoot5_3559
  · exact htauRoot5_3571
  · exact htauRoot5_3581
  · exact htauRoot5_3583
  · exact htauRoot5_3593

theorem htauRange5_3603 : RootRange 5 3603 3683 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=3603) [3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677] [3, 2, 5, 2, 0, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 41, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_3607
  · exact htauRoot5_3613
  · exact htauRoot5_3617
  · exact htauRoot5_3623
  · exact htauRoot5_3631
  · exact htauRoot5_3637
  · exact htauRoot5_3643
  · exact htauRoot5_3659
  · exact htauRoot5_3671
  · exact htauRoot5_3673
  · exact htauRoot5_3677

theorem htauRange5_3683 : RootRange 5 3683 3763 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=3683) [3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761] [29, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 47, 2, 5, 2, 3, 2, 0, 2, 61, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 37, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 23, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_3691
  · exact htauRoot5_3697
  · exact htauRoot5_3701
  · exact htauRoot5_3709
  · exact htauRoot5_3719
  · exact htauRoot5_3727
  · exact htauRoot5_3733
  · exact htauRoot5_3739
  · exact htauRoot5_3761

theorem htauRange5_3763 : RootRange 5 3763 3843 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=3763) [3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833] [53, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 37, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 43, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 23, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_3767
  · exact htauRoot5_3769
  · exact htauRoot5_3779
  · exact htauRoot5_3793
  · exact htauRoot5_3797
  · exact htauRoot5_3803
  · exact htauRoot5_3821
  · exact htauRoot5_3823
  · exact htauRoot5_3833

theorem htauRange5_3843 : RootRange 5 3843 3923 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=3843) [3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919] [3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 53, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 13, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 47, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_3847
  · exact htauRoot5_3851
  · exact htauRoot5_3853
  · exact htauRoot5_3863
  · exact htauRoot5_3877
  · exact htauRoot5_3881
  · exact htauRoot5_3889
  · exact htauRoot5_3907
  · exact htauRoot5_3911
  · exact htauRoot5_3917
  · exact htauRoot5_3919

theorem htauRange5_3923 : RootRange 5 3923 4003 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=3923) [3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001] [0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 59, 2, 5, 2, 3, 2, 37, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 29, 2, 3, 2, 41, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_3923
  · exact htauRoot5_3929
  · exact htauRoot5_3931
  · exact htauRoot5_3943
  · exact htauRoot5_3947
  · exact htauRoot5_3967
  · exact htauRoot5_3989
  · exact htauRoot5_4001

theorem htauRange5_4003 : RootRange 5 4003 4083 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=4003) [4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079] [0, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 37, 2, 3, 2, 11, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 31, 2, 17, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_4003
  · exact htauRoot5_4007
  · exact htauRoot5_4013
  · exact htauRoot5_4019
  · exact htauRoot5_4021
  · exact htauRoot5_4027
  · exact htauRoot5_4049
  · exact htauRoot5_4051
  · exact htauRoot5_4057
  · exact htauRoot5_4073
  · exact htauRoot5_4079

theorem htauRange5_4083 : RootRange 5 4083 4163 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=4083) [4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159] [3, 2, 5, 2, 61, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 41, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_4091
  · exact htauRoot5_4093
  · exact htauRoot5_4099
  · exact htauRoot5_4111
  · exact htauRoot5_4127
  · exact htauRoot5_4129
  · exact htauRoot5_4133
  · exact htauRoot5_4139
  · exact htauRoot5_4153
  · exact htauRoot5_4157
  · exact htauRoot5_4159

theorem htauRange5_4163 : RootRange 5 4163 4243 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=4163) [4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241] [23, 2, 5, 2, 3, 2, 11, 2, 43, 2, 3, 2, 5, 2, 0, 2, 3, 2, 37, 2, 47, 2, 3, 2, 53, 2, 59, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 41, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_4177
  · exact htauRoot5_4201
  · exact htauRoot5_4211
  · exact htauRoot5_4217
  · exact htauRoot5_4219
  · exact htauRoot5_4229
  · exact htauRoot5_4231
  · exact htauRoot5_4241

theorem htauRange5_4243 : RootRange 5 4243 4323 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=4243) [4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297] [0, 2, 3, 2, 31, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 13, 2, 3, 2, 59, 2, 31, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2, 29, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_4243
  · exact htauRoot5_4253
  · exact htauRoot5_4259
  · exact htauRoot5_4261
  · exact htauRoot5_4271
  · exact htauRoot5_4273
  · exact htauRoot5_4283
  · exact htauRoot5_4289
  · exact htauRoot5_4297

theorem htauRange5_4323 : RootRange 5 4323 4403 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=4323) [4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397] [3, 2, 5, 2, 0, 2, 3, 2, 61, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 43, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 29, 2, 13, 2, 3, 2, 5, 2, 41, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 53, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_4327
  · exact htauRoot5_4337
  · exact htauRoot5_4339
  · exact htauRoot5_4349
  · exact htauRoot5_4357
  · exact htauRoot5_4363
  · exact htauRoot5_4373
  · exact htauRoot5_4391
  · exact htauRoot5_4397

theorem htauRange5_4403 : RootRange 5 4403 4483 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=4403) [4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481] [7, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 43, 2, 3, 2, 11, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 61, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 41, 2, 17, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_4409
  · exact htauRoot5_4421
  · exact htauRoot5_4423
  · exact htauRoot5_4441
  · exact htauRoot5_4447
  · exact htauRoot5_4451
  · exact htauRoot5_4457
  · exact htauRoot5_4463
  · exact htauRoot5_4481

theorem htauRange5_4483 : RootRange 5 4483 4563 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=4483) [4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561] [0, 2, 3, 2, 7, 2, 67, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 13, 2, 3, 2, 19, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 47, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_4483
  · exact htauRoot5_4493
  · exact htauRoot5_4507
  · exact htauRoot5_4513
  · exact htauRoot5_4517
  · exact htauRoot5_4519
  · exact htauRoot5_4523
  · exact htauRoot5_4547
  · exact htauRoot5_4549
  · exact htauRoot5_4561

theorem htauRange5_4563 : RootRange 5 4563 4643 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=4563) [4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639] [3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 23, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 43, 2, 0, 2, 3, 2, 17, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 31, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 41, 2, 3, 2, 0, 2, 0, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_4567
  · exact htauRoot5_4583
  · exact htauRoot5_4591
  · exact htauRoot5_4597
  · exact htauRoot5_4603
  · exact htauRoot5_4621
  · exact htauRoot5_4637
  · exact htauRoot5_4639

theorem htauRange5_4643 : RootRange 5 4643 4723 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=4643) [4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721] [0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 59, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 31, 2, 3, 2, 5, 2, 43, 2, 3, 2, 0, 2, 13, 2, 3, 2, 7, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 53, 2, 3, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_4643
  · exact htauRoot5_4649
  · exact htauRoot5_4651
  · exact htauRoot5_4657
  · exact htauRoot5_4663
  · exact htauRoot5_4673
  · exact htauRoot5_4679
  · exact htauRoot5_4691
  · exact htauRoot5_4703
  · exact htauRoot5_4721

theorem htauRange5_4723 : RootRange 5 4723 4803 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=4723) [4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801] [0, 2, 3, 2, 29, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 47, 2, 3, 2, 0, 2, 7, 2, 3, 2, 67, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 19, 2, 13, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_4723
  · exact htauRoot5_4729
  · exact htauRoot5_4733
  · exact htauRoot5_4751
  · exact htauRoot5_4759
  · exact htauRoot5_4783
  · exact htauRoot5_4787
  · exact htauRoot5_4789
  · exact htauRoot5_4793
  · exact htauRoot5_4799
  · exact htauRoot5_4801

theorem htauRange5_4803 : RootRange 5 4803 4883 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=4803) [4813, 4817, 4831, 4861, 4871, 4877] [3, 2, 5, 2, 11, 2, 3, 2, 17, 2, 0, 2, 3, 2, 0, 2, 61, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 47, 2, 29, 2, 3, 2, 37, 2, 13, 2, 3, 2, 23, 2, 5, 2, 3, 2, 43, 2, 0, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_4813
  · exact htauRoot5_4817
  · exact htauRoot5_4831
  · exact htauRoot5_4861
  · exact htauRoot5_4871
  · exact htauRoot5_4877

theorem htauRange5_4883 : RootRange 5 4883 4963 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=4883) [4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957] [19, 2, 5, 2, 3, 2, 0, 2, 67, 2, 3, 2, 5, 2, 59, 2, 3, 2, 13, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_4889
  · exact htauRoot5_4903
  · exact htauRoot5_4909
  · exact htauRoot5_4919
  · exact htauRoot5_4931
  · exact htauRoot5_4933
  · exact htauRoot5_4937
  · exact htauRoot5_4943
  · exact htauRoot5_4951
  · exact htauRoot5_4957

theorem htauRange5_4963 : RootRange 5 4963 5043 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=4963) [4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039] [7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 47, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 71, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_4967
  · exact htauRoot5_4969
  · exact htauRoot5_4973
  · exact htauRoot5_4987
  · exact htauRoot5_4993
  · exact htauRoot5_4999
  · exact htauRoot5_5003
  · exact htauRoot5_5009
  · exact htauRoot5_5011
  · exact htauRoot5_5021
  · exact htauRoot5_5023
  · exact htauRoot5_5039

theorem htauRange5_5043 : RootRange 5 5043 5123 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=5043) [5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119] [3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 31, 2, 3, 2, 13, 2, 0, 2, 3, 2, 61, 2, 5, 2, 3, 2, 37, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_5051
  · exact htauRoot5_5059
  · exact htauRoot5_5077
  · exact htauRoot5_5081
  · exact htauRoot5_5087
  · exact htauRoot5_5099
  · exact htauRoot5_5101
  · exact htauRoot5_5107
  · exact htauRoot5_5113
  · exact htauRoot5_5119

end OddPerfect.HarmonicChain
