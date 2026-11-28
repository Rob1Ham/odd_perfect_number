import RestrainedOPN
import Lean.Util.CollectAxioms

open Lean Elab Command

#check RestrainedOPN.smooth_quadratic_three_step_growth
#check RestrainedOPN.three_free_restrained_excluded
#check RestrainedOPN.three_free_two_large_sources_congruence
#check RestrainedOPN.restrained_three_divisibility_and_exponent_profile
#check RestrainedOPN.finite_of_bounded_nonSquare_exponents

run_cmd
  let env ← getEnv
  let prefixes := #[`OddPerfect, `RestrainedOPN]
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
  logInfo m!"RestrainedOPN audit passed: {checked} named theorems and {projectConstants.size} declarations verified on [propext, Classical.choice, Quot.sound]."
