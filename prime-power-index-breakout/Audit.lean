import PrimePowerIndex
import Lean.Util.CollectAxioms

open Lean Elab Command

#check PrimePowerIndex.prime_power_index_euler_only_and_nonfermat
#check PrimePowerIndex.even_prime_power_tridecuple_repunit_and_size_bounds
#check PrimePowerIndex.even_prime_power_primorial_padic_and_gauss_reciprocity

run_cmd
  let env ← getEnv
  let prefixes := #[`OddPerfect, `PrimePowerIndex]
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
  logInfo m!"PrimePowerIndex audit passed: {checked} named theorems and {projectConstants.size} declarations verified on [propext, Classical.choice, Quot.sound]."
