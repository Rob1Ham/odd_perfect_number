import TothAnalytic
import TothTheorem
import Lean.Util.CollectAxioms

open Lean Elab Command

#check TothBreakout.Analytic.odd_toth_square_and_deficient_iff
#check TothBreakout.Analytic.suffix_abundancy_strict_ceiling
#check TothBreakout.Analytic.analytic_interval_cut
#check TothBreakout.Analytic.unbounded_toth_radical_size_upper
#check TothBreakout.Analytic.finite_odd_toth_pairs_of_bounded_prime_count
#check TothBreakout.Analytic.finite_deficientPerfect_of_bounded_rank_and_two_val
#check TothBreakout.Analytic.proper_factor_and_unsplit_characterization
#check TothBreakout.Analytic.linear_euler_toth_unique_source
#check TothBreakout.Theorem.toth_unique_odd_pair_below_trillion
#check TothBreakout.Theorem.toth_odd_pair_set_below_trillion
#check TothBreakout.Theorem.descartes_non_example_factor_gt_ten_pow_twelve
#check TothBreakout.Theorem.deficientPerfect_below_trillion_iff

/- Audit every declaration in `OddPerfect`, `TothAnalytic`, and `TothTheorem`
to ensure zero `sorry`, zero custom `axiom`, and only standard Lean foundations
(`propext`, `Classical.choice`, `Quot.sound`). -/
run_cmd
  let env ← getEnv
  let prefixes := #[`OddPerfect, `TothBreakout, `TothAnalytic, `TothTheorem]
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
  logInfo m!"Breakout audit passed: {checked} named theorems and {projectConstants.size} declarations verified on [propext, Classical.choice, Quot.sound]."
