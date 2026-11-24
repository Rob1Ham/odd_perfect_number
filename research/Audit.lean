import OddPerfect
import Lean.Util.CollectAxioms

open Lean Elab Command

#print OddPerfect.existsOddPerfect

/- Inspect the declarations imported by the project's public entry point.
An unexpected axiom fails this command, including when it occurs in a helper. -/
run_cmd
  let env ← getEnv
  let projectConstants := env.constants.fold (init := #[]) fun acc n info =>
    match env.getModuleIdxFor? n with
    | some i =>
      if `OddPerfect |>.isPrefixOf env.header.moduleNames[i]! then acc.push (n, info) else acc
    | none => acc
  let mut checked : Nat := 0
  for (n, info) in projectConstants.qsort (fun a b => Name.quickLt a.1 b.1) do
    if info.isAxiom then throwError "Project axiom: {n}"
    let allowed := #[`propext, `Classical.choice, `Quot.sound]
    let axioms ← collectAxioms n
    for a in axioms do
      unless allowed.contains a do throwError "{n} depends on unexpected axiom {a}"
    if info.isTheorem && !n.isInternalDetail then
      elabCommand (← `(#check $(mkIdent n)))
      elabCommand (← `(#print axioms $(mkIdent n)))
      checked := checked + 1
  if checked == 0 then throwError "No project theorems found"
  logInfo m!"Audited {checked} named theorems and checked axioms of {projectConstants.size} project declarations."
