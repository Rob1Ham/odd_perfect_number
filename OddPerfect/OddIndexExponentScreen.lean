module

public import OddPerfect.OddIndexLocal

public section
namespace OddPerfect.IndexObstruction
open ArithmeticFunction

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option exponentiation.threshold 200000

private def good (c : LocalTest) : Bool := decide c.r.Prime && c.ok

private def tests0 : List LocalTest := [
  ⟨97,193,5,0xa,0x16⟩,
  ⟨17,577,3,0x2,0x6⟩,
  ⟨337,673,5,0xa,0x16⟩,
  ⟨577,1153,5,0xa,0x16⟩,
  ⟨601,1201,7,0x12,0x4b⟩,
  ⟨89,1601,41,0x6,0x1d9c15a839b⟩,
  ⟨937,1873,5,0xa,0x16⟩,
  ⟨1009,2017,13,0x6,0x14f2⟩,
  ⟨1297,2593,5,0xa,0x16⟩,
  ⟨17,2753,5,0xa,0x16⟩,
  ⟨1609,3217,7,0x12,0x4b⟩,
  ⟨1657,3313,5,0xa,0x16⟩,
  ⟨41,3361,3,0x2,0x6⟩,
  ⟨2089,4177,7,0x22,0x4b⟩,
  ⟨2137,4273,5,0xa,0x16⟩,
  ⟨241,4337,7,0x3e,0x4b⟩,
  ⟨2281,4561,7,0x12,0x4b⟩,
  ⟨17,4657,3,0x2,0x6⟩,
  ⟨137,4657,3,0x2,0x6⟩,
  ⟨41,4673,17,0x8002,0x1d18b⟩]

private theorem good0 : tests0.all good=true := by decide +kernel

private def tests1 : List LocalTest := [
  ⟨73,4817,5,0x6,0x16⟩,
  ⟨2617,5233,5,0xa,0x16⟩,
  ⟨3169,6337,7,0x6,0x4b⟩,
  ⟨353,6353,5,0xa,0x16⟩,
  ⟨17,6833,5,0xa,0x16⟩,
  ⟨3529,7057,13,0x802,0x14f2⟩,
  ⟨41,7297,3,0x2,0x6⟩,
  ⟨89,7297,3,0x2,0x6⟩,
  ⟨3697,7393,5,0xa,0x16⟩,
  ⟨113,7457,5,0x6,0x16⟩,
  ⟨3769,7537,7,0x22,0x4b⟩,
  ⟨17,7649,479,0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002,0x4002281293a88e392c159b8b8350b78cb342a66f851d293d88be64a19e5f81619eb660bb90dad1d78266af4cb384bd4f8b8995f2d8e3ba8dadfaefff⟩,
  ⟨433,7793,5,0xa,0x16⟩,
  ⟨449,8081,17,0x42,0x1d18b⟩,
  ⟨4177,8353,5,0xa,0x16⟩,
  ⟨41,8609,11,0x3fe,0x6e2⟩,
  ⟨17,8737,3,0x2,0x6⟩,
  ⟨257,8737,3,0x2,0x6⟩,
  ⟨137,9041,5,0x2,0x16⟩,
  ⟨17,9281,5,0x2,0x16⟩]

private theorem good1 : tests1.all good=true := by decide +kernel

private def tests2 : List LocalTest := [
  ⟨521,9377,17,0x402,0x1d18b⟩,
  ⟨4801,9601,7,0x12,0x4b⟩,
  ⟨193,9649,13,0xa,0x14f2⟩,
  ⟨17,10369,3,0x2,0x6⟩,
  ⟨73,10657,5,0x6,0x16⟩,
  ⟨97,11057,5,0x6,0x16⟩,
  ⟨241,12049,7,0x6,0x4b⟩,
  ⟨673,12113,5,0xa,0x16⟩,
  ⟨6121,12241,7,0x22,0x4b⟩,
  ⟨6217,12433,5,0xa,0x16⟩,
  ⟨6361,12721,7,0x6,0x4b⟩,
  ⟨17,13633,3,0x2,0x6⟩,
  ⟨401,13633,3,0x2,0x6⟩,
  ⟨6841,13681,11,0x102,0x6e2⟩,
  ⟨761,13697,857,0x4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002,0x1d18b4acfb0e4fadd478afc12df6e5bd11a1d484457d0a9acf3d7b456b165d1012b6683d19ae0123839b7718044c1ced87d85f33dcd18b3bccfa1be1b738322018eed9c1c4807598bc166d4808ba68d6a2debcf35950bea2212b8588bda76fb483f51e2bb5f270df352d18b⟩,
  ⟨769,13841,7,0x3e,0x4b⟩,
  ⟨6961,13921,7,0x22,0x4b⟩,
  ⟨17,14177,5,0x6,0x16⟩,
  ⟨17,14449,3,0x2,0x6⟩,
  ⟨809,14561,11,0x102,0x6e2⟩]

private theorem good2 : tests2.all good=true := by decide +kernel

private def tests3 : List LocalTest := [
  ⟨7297,14593,5,0xa,0x16⟩,
  ⟨7369,14737,7,0x6,0x4b⟩,
  ⟨7537,15073,5,0xa,0x16⟩,
  ⟨7561,15121,13,0x6,0x14f2⟩,
  ⟨73,15329,13,0xf7e,0x14f2⟩,
  ⟨7681,15361,13,0x102,0x14f2⟩,
  ⟨233,15377,5,0x6,0x16⟩,
  ⟨313,15649,7,0x12,0x4b⟩,
  ⟨17,15809,1217,0x20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002,0x1d183688fbe62e25dcfde9c24dc24b3f372d75b5ec3f88438d3d80418e587d58d9da4533f93e519fc522fd56240902762730fd1caaa10a1e87439e835519340596179cc9abb2525dd4bafd691896bf5d2bba4a4dd59339e869a02c98aac179c2e17850855538bf0ce46e4090246abf44a3f98a7c9fcca25b9b1abe1a718201bcb1c211fc37adaeb4ecfcd243b24397bf3ba47467df116c18b⟩,
  ⟨8017,16033,5,0xa,0x16⟩,
  ⟨8209,16417,7,0x6,0x4b⟩,
  ⟨41,16481,11,0xa,0x6e2⟩,
  ⟨8329,16657,7,0x12,0x4b⟩,
  ⟨8521,17041,11,0x6,0x6e2⟩,
  ⟨41,17137,3,0x2,0x6⟩,
  ⟨8689,17377,13,0x202,0x14f2⟩,
  ⟨17,17713,3,0x2,0x6⟩,
  ⟨521,17713,3,0x2,0x6⟩,
  ⟨9049,18097,7,0x6,0x4b⟩,
  ⟨17,18257,5,0x6,0x16⟩]

private theorem good3 : tests3.all good=true := by decide +kernel

private def tests4 : List LocalTest := [
  ⟨9241,18481,13,0x102,0x14f2⟩,
  ⟨1033,18593,5,0xa,0x16⟩,
  ⟨193,18913,5,0xa,0x16⟩,
  ⟨17,19073,5,0xa,0x16⟩,
  ⟨9721,19441,7,0x6,0x4b⟩,
  ⟨17,19889,227,0x100000000000000000000000000000000002,0x6cbc4abf344ce229e3bfb6b42fc764702f4a4808e1aee3374c0ab70b2⟩,
  ⟨89,20113,3,0x2,0x6⟩,
  ⟨113,20113,3,0x2,0x6⟩,
  ⟨17,20161,3,0x2,0x6⟩,
  ⟨593,20161,3,0x2,0x6⟩,
  ⟨10177,20353,5,0xa,0x16⟩,
  ⟨97,20369,13,0xf7a,0x14f2⟩,
  ⟨10321,20641,7,0x22,0x4b⟩,
  ⟨1153,20753,5,0xa,0x16⟩,
  ⟨73,21169,7,0x2,0x4b⟩,
  ⟨10657,21313,5,0xa,0x16⟩,
  ⟨17,21521,5,0x2,0x16⟩,
  ⟨1201,21617,13,0xf7a,0x14f2⟩,
  ⟨433,21649,7,0x22,0x4b⟩,
  ⟨137,22193,5,0xa,0x16⟩]

private theorem good4 : tests4.all good=true := by decide +kernel

private def tests5 : List LocalTest := [
  ⟨1249,22481,7,0x3e,0x4b⟩,
  ⟨89,22961,29,0x400002,0x16176e86⟩,
  ⟨11497,22993,5,0xa,0x16⟩,
  ⟨41,23041,3,0x2,0x6⟩,
  ⟨281,23041,3,0x2,0x6⟩,
  ⟨1289,23201,11,0x6,0x6e2⟩,
  ⟨353,23297,5,0x6,0x16⟩,
  ⟨97,23473,5,0xa,0x16⟩,
  ⟨12049,24097,13,0x102,0x14f2⟩,
  ⟨12241,24481,7,0x6,0x4b⟩,
  ⟨17,25057,3,0x2,0x6⟩,
  ⟨12577,25153,5,0xa,0x16⟩,
  ⟨113,25537,3,0x2,0x6⟩,
  ⟨17,25601,5,0x2,0x16⟩,
  ⟨1433,25793,5,0xa,0x16⟩,
  ⟨73,25841,5,0x2,0x16⟩,
  ⟨17,25873,3,0x2,0x6⟩,
  ⟨761,25873,3,0x2,0x6⟩,
  ⟨13009,26017,7,0x22,0x4b⟩,
  ⟨41,26321,11,0x202,0x6e2⟩]

private theorem good5 : tests5.all good=true := by decide +kernel

private def tests6 : List LocalTest := [
  ⟨17,26417,5,0x6,0x16⟩,
  ⟨13249,26497,7,0x6,0x4b⟩,
  ⟨233,26561,5,0x2,0x16⟩,
  ⟨1489,26801,7,0x3e,0x4b⟩,
  ⟨13417,26833,5,0xa,0x16⟩,
  ⟨13441,26881,11,0x102,0x6e2⟩,
  ⟨409,26993,7,0x3e,0x4b⟩,
  ⟨13537,27073,5,0xa,0x16⟩,
  ⟨13681,27361,7,0x22,0x4b⟩,
  ⟨13729,27457,17,0x6,0x1d18b⟩,
  ⟨1553,27953,5,0xa,0x16⟩,
  ⟨41,28289,11,0x3fe,0x6e2⟩,
  ⟨89,28657,3,0x2,0x6⟩,
  ⟨1601,28817,17,0x6,0x1d18b⟩,
  ⟨1609,28961,7,0x3e,0x4b⟩,
  ⟨17,29137,3,0x2,0x6⟩,
  ⟨857,29137,3,0x2,0x6⟩,
  ⟨113,29153,5,0xa,0x16⟩,
  ⟨257,29297,5,0x6,0x16⟩,
  ⟨14737,29473,5,0xa,0x16⟩]

private theorem good6 : tests6.all good=true := by decide +kernel

private def tests7 : List LocalTest := [
  ⟨449,29633,17,0x6,0x1d18b⟩,
  ⟨457,30161,5,0x2,0x16⟩,
  ⟨15121,30241,11,0x6,0x6e2⟩,
  ⟨17,30497,5,0x6,0x16⟩,
  ⟨15289,30577,17,0x802,0x1d18b⟩,
  ⟨1721,30977,23,0x80002,0x4299af⟩,
  ⟨15937,31873,5,0xa,0x16⟩,
  ⟨17,32401,3,0x2,0x6⟩,
  ⟨953,32401,3,0x2,0x6⟩,
  ⟨16249,32497,17,0x402,0x1d18b⟩,
  ⟨16417,32833,5,0xa,0x16⟩,
  ⟨257,33409,3,0x2,0x6⟩,
  ⟨16729,33457,7,0x12,0x4b⟩,
  ⟨1873,33713,5,0xa,0x16⟩,
  ⟨17,34033,3,0x2,0x6⟩,
  ⟨17137,34273,5,0xa,0x16⟩,
  ⟨97,34337,5,0x6,0x16⟩,
  ⟨17257,34513,5,0xa,0x16⟩,
  ⟨17,34849,3,0x2,0x6⟩,
  ⟨41,34849,3,0x2,0x6⟩]

private theorem good7 : tests7.all good=true := by decide +kernel

private def tests8 : List LocalTest := [
  ⟨17449,34897,7,0x6,0x4b⟩,
  ⟨17,35393,5,0xa,0x16⟩,
  ⟨17761,35521,11,0x6,0x6e2⟩,
  ⟨18049,36097,7,0x22,0x4b⟩,
  ⟨41,36161,11,0x12,0x6e2⟩]

private theorem good8 : tests8.all good=true := by decide +kernel

private def tests : List LocalTest := tests0 ++ tests1 ++ tests2 ++ tests3 ++ tests4 ++ tests5 ++ tests6 ++ tests7 ++ tests8

private theorem tests_ok : ∀ c∈tests, c.r.Prime ∧ c.ok=true := by
  have hall : tests.all good=true := by simp only [tests,List.all_append,good0,good1,good2,good3,good4,good5,good6,good7,good8,Bool.and_self]
  intro c hc
  simpa [good] using List.all_eq_true.mp hall c hc

private def smallBases : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191]

private def properFactor (n : ℕ) : Bool :=
  smallBases.any fun r => decide (1<r ∧ r<n ∧ r∣n)

private def quickCover (K : ℕ) (ts : List LocalTest) : Bool :=
  (List.range K).all fun k =>
    let n := 16*k+17
    properFactor n || (n+1).primeFactorsList.all fun d =>
      d%8 != 1 || ts.any fun c => c.d==d && c.n==n

private theorem cover_of_quick {K : ℕ} {ts : List LocalTest} (h : quickCover K ts=true) :
    cover K ts=true := by
  apply List.all_eq_true.mpr
  intro k hk
  have hv := List.all_eq_true.mp h k hk
  let n := 16*k+17
  change (!(decide n.Prime) || _) = true
  by_cases hn : n.Prime
  · rw [decide_eq_true hn,Bool.not_true,Bool.false_or]
    have hnot : properFactor n=false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      obtain ⟨r,_,hr⟩ := List.any_eq_true.mp (show (smallBases.any fun r => decide (1<r ∧ r<n ∧ r∣n))=true from ht)
      obtain ⟨hr1,hrn,hrd⟩ := of_decide_eq_true hr
      rcases (Nat.dvd_prime hn).mp hrd with h|h <;> omega
    change (properFactor n || _)=true at hv
    rwa [hnot,Bool.false_or] at hv
  · simp [hn]

private theorem tests_cover : cover 2262 tests=true := cover_of_quick (by decide +kernel)

/-- Every odd prime-power index at an Euler component has exponent at
least 36207. The index prime and the odd perfect number are unbounded
in the finite residue checks. -/
theorem odd_prime_power_index_exponent_at_least_36207 {N q a m p j : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1)
    (hqm : ¬q∣m) (hform : N=q^a*m^2) (hp : p.Prime) (hj : Odd j)
    (hi : sigma 1 (m^2)/q^a=p^j) : 36207≤j :=
  exponent_bound_of_cover tests_cover tests_ok hN ho hq hq4 ha4 hqm hform hp hj hi

/-- The same exclusion holds at every exact prime-power component. -/
theorem component_index_ne_odd_prime_power_below_36207 {N q a b i p j : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0<a)
    (hform : N=q^a*b) (hqb : ¬q∣b) (hl : sigma 1 b=q^a*i) (hr : sigma 1 (q^a)*i=2*b)
    (hp : p.Prime) (hj : Odd j) (hlim : j<36207) : i≠p^j :=
  component_index_ne_of_cover tests_cover tests_ok hN ho hq ha hform hqb hl hr hp hj hlim

end OddPerfect.IndexObstruction
