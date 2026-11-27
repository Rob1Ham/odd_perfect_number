module

public import OddPerfect.CountChain45.PrimePart03
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.FactorBudget.Count45

set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] noncomputable def splitPrimes : List ℕ :=
  primes1 ++ (primes2 ++ (primes3 ++ (primes4 ++ (primes5 ++ (primes6 ++ (primes7 ++ (primes8 ++ (primes9 ++ (primes10 ++ (primes11 ++ (primes12 ++ (primes13 ++ (primes14 ++ (primes15 ++ (primes16 ++ (primes17 ++ (primes18 ++ (primes19 ++ (primes20 ++ (primes21 ++ (primes22 ++ (primes23 ++ (primes24 ++ (primes25 ++ (primes26 ++ (primes27 ++ (primes28 ++ (primes29 ++ (primes30 ++ (primes31 ++ (primes32 ++ (primes33 ++ (primes34 ++ (primes35 ++ (primes36 ++ (primes37 ++ (primes38 ++ (primes39 ++ (primes40 ++ (primes41 ++ (primes42 ++ (primes43 ++ (primes44 ++ (primes45 ++ (primes46 ++ (primes47 ++ (primes48 ++ (primes49 ++ (primes50 ++ (primes51 ++ (primes52 ++ (primes53 ++ (primes54 ++ (primes55 ++ (primes56 ++ (primes57))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem prime_proofs : ∀ p ∈ splitPrimes, p.Prime := by
  simp only [splitPrimes, List.forall_mem_append]
  exact ⟨primes1_valid, primes2_valid, primes3_valid, primes4_valid, primes5_valid, primes6_valid, primes7_valid, primes8_valid, primes9_valid, primes10_valid, primes11_valid, primes12_valid, primes13_valid, primes14_valid, primes15_valid, primes16_valid, primes17_valid, primes18_valid, primes19_valid, primes20_valid, primes21_valid, primes22_valid, primes23_valid, primes24_valid, primes25_valid, primes26_valid, primes27_valid, primes28_valid, primes29_valid, primes30_valid, primes31_valid, primes32_valid, primes33_valid, primes34_valid, primes35_valid, primes36_valid, primes37_valid, primes38_valid, primes39_valid, primes40_valid, primes41_valid, primes42_valid, primes43_valid, primes44_valid, primes45_valid, primes46_valid, primes47_valid, primes48_valid, primes49_valid, primes50_valid, primes51_valid, primes52_valid, primes53_valid, primes54_valid, primes55_valid, primes56_valid, primes57_valid⟩

end OddPerfect.FactorBudget.Count45
