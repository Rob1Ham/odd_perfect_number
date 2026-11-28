import EulerIndexBounds
import Lean.Util.CollectAxioms

open Lean Elab Command

#check EulerIndexBounds.euler_index_ge_2379
#check EulerIndexBounds.odd_component_index_has_nonfermat_prime
#check EulerIndexBounds.euler_index_odd_valuation_escape
#check EulerIndexBounds.hirakawa_second_block_pell_fundamental
#check EulerIndexBounds.hirakawa_exceptional_branch_size_and_sieve
#check EulerIndexBounds.hirakawa_zsqrtTwo_frobenius_descent

run_cmd
  let env ← getEnv
  let prefixes := #[`OddPerfect, `EulerIndexBounds]
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
  logInfo m!"EulerIndexBounds audit passed: {checked} named theorems and {projectConstants.size} declarations verified on [propext, Classical.choice, Quot.sound]."
