import ParityFiniteness
import Lean.Util.CollectAxioms

open Lean Elab Command

#check ParityFiniteness.even_pow_two_deficientPerfect
#check ParityFiniteness.even_thabit_deficientPerfect
#check ParityFiniteness.even_mersenne_nearPerfect_families
#check ParityFiniteness.not_deficientPerfect_of_perfect_dvd
#check ParityFiniteness.deficientPerfect_le_of_bounded_rank_two_val
#check ParityFiniteness.nearPerfect_le_of_bounded_rank_two_val
#check ParityFiniteness.finite_deficient_and_nearPerfect_of_bounded_rank_two_val
#check ParityFiniteness.odd_deficientPerfect_explicit_bound_and_finiteness
#check ParityFiniteness.odd_nearPerfect_finiteness

run_cmd
  let env ← getEnv
  let prefixes := #[`OddPerfect, `ParityFiniteness]
  let projectConstants := env.constants.fold (init := #[]) fun acc n info =>
    match env.getModuleIdxFor? n with
    | some i =>
      let modName := env.header.moduleNames[i]!
      if prefixes.any (fun p => p.isPrefixOf modName) then acc.push (n, info) else acc
    | none => acc
  let mut checked : Nat := 0
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for (n, info) in projectConstants.qsort (fun a b => Name.quickLt a.1 b.1) do
    if info.isAxiom then throwError "Project axiom: {n}"
    let axioms ← collectAxioms n
    for a in axioms do
      unless allowed.contains a do throwError "{n} depends on unexpected axiom {a}"
    if info.isTheorem && !n.isInternalDetail then
      checked := checked + 1
  if checked == 0 then throwError "No project theorems found"
  logInfo m!"ParityFiniteness audit passed: {checked} named theorems and {projectConstants.size} declarations verified on [propext, Classical.choice, Quot.sound]."
