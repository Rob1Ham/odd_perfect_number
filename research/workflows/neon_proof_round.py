# Dynamic workflow for a 3-stage Neon (`model="flash"`) proof round orchestrated by Carbon.
#
# Run from Carbon via `run_workflow`:
#   run_workflow(
#       ScriptPath="/Users/roberthamilton/Desktop/perfect_number/odd_perfect_number/research/workflows/neon_proof_round.py",
#       Description="Execute parallel Neon scout -> prover -> auditor round",
#       Args={
#           "tasks": [
#               {
#                   "id": "second_prime_fifth_pow",
#                   "target_module": "OddPerfect/SecondPrimeBound.lean",
#                   "goal": "Prove b^5 < 2*N for the second-largest prime divisor b of an odd perfect number N (Zelinsky / Bibby-Vyncke-Zelinsky).",
#                   "mathlib_queries": ["primeFactors", "abundancyIndex", "ordProj", "geom_sum"],
#               }
#           ]
#       },
#   )

tasks = args.get("tasks", [])
if not tasks:
    raise ValueError("Pass non-empty `Args={'tasks': [...]}` to neon_proof_round.py")

SCOUT_SCHEMA = {
    "type": "object",
    "properties": {
        "task_id": {"type": "string"},
        "recommended_imports": {"type": "array", "items": {"type": "string"}},
        "mathlib_lemmas": {"type": "array", "items": {"type": "string"}},
        "project_lemmas": {"type": "array", "items": {"type": "string"}},
        "proof_sketch": {"type": "string"},
    },
    "required": ["task_id", "recommended_imports", "mathlib_lemmas", "project_lemmas", "proof_sketch"],
}

PROVER_SCHEMA = {
    "type": "object",
    "properties": {
        "task_id": {"type": "string"},
        "status": {"type": "string", "enum": ["PROVED", "PARTIAL_BLOCKER", "REFUTED_HYPOTHESIS"]},
        "module_path": {"type": "string"},
        "declarations": {"type": "array", "items": {"type": "string"}},
        "mathlib_used": {"type": "array", "items": {"type": "string"}},
        "blocker_or_notes": {"type": "string"},
    },
    "required": ["task_id", "status", "module_path", "declarations", "mathlib_used", "blocker_or_notes"],
}

AUDIT_SCHEMA = {
    "type": "object",
    "properties": {
        "task_id": {"type": "string"},
        "verdict": {"type": "string", "enum": ["PASS", "CONDITIONAL_PASS", "REJECT", "SKIPPED_UNPROVED"]},
        "hypothesis_check": {"type": "string"},
        "coverage_check": {"type": "string"},
        "axiom_check": {"type": "string"},
        "issues": {"type": "array", "items": {"type": "string"}},
    },
    "required": ["task_id", "verdict", "hypothesis_check", "coverage_check", "axiom_check", "issues"],
}

phase("1. Mathlib & Corpus Scouting (Neon)")
scout_briefs = await parallel(
    tasks,
    lambda t: agent(
        prompt=(
            f"Task `{t['id']}`: Scout Mathlib and `OddPerfect/` for reusable lemmas to prove:\n"
            f"Goal: {t['goal']}\n"
            f"Target file: `{t['target_module']}`\n"
            f"Suggested queries: {t.get('mathlib_queries', [])}\n\n"
            "Run `python3 research/tools/mathlib_kb.py search ...` (`--scope mathlib` and `--scope project`) "
            "and inspect relevant files with `read_file`. Do NOT edit any files."
        ),
        schema=SCOUT_SCHEMA,
        role=f"Neon Scout: {t['id']}",
        type_name="neon-mathlib-scout",
        model="flash",
    ),
)
log(f"Completed {len(scout_briefs)} Mathlib scout brief(s).")

paired = list(zip(tasks, scout_briefs))

phase("2. Isolated Proof Execution (Neon)")
prover_results = await parallel(
    paired,
    lambda pair: agent(
        prompt=(
            f"Task `{pair[0]['id']}`: Formalize in `{pair[0]['target_module']}` (and ONLY that file).\n"
            f"Goal: {pair[0]['goal']}\n\n"
            f"Mathlib & Project Scout Brief:\n{pair[1]}\n\n"
            "Rules: Zero `sorry`/`admit`/`axiom`. Do NOT edit `OddPerfect.lean`. "
            f"Verify with `lake env lean {pair[0]['target_module']}`."
        ),
        schema=PROVER_SCHEMA,
        role=f"Neon Prover: {pair[0]['id']}",
        type_name="neon-prover",
        model="flash",
    ),
)
log(f"Completed {len(prover_results)} Neon prover run(s).")

audit_inputs = list(zip(tasks, prover_results))


async def audit_one(item):
    t, res = item
    if res["status"] != "PROVED":
        return {
            "task_id": t["id"],
            "verdict": "SKIPPED_UNPROVED",
            "hypothesis_check": "N/A",
            "coverage_check": "N/A",
            "axiom_check": "N/A",
            "issues": [res["blocker_or_notes"]],
        }
    return await agent(
        prompt=(
            f"Adversarially audit `{res['module_path']}` for task `{t['id']}`.\n"
            f"Intended mathematical goal: {t['goal']}\n"
            f"Claimed declarations: {res['declarations']}\n\n"
            "Check hypothesis fidelity (no extra assumptions), edge cases, branch coverage, "
            "and verify zero `sorry`/custom axioms via `lake env lean` + `#print axioms` in scratch."
        ),
        schema=AUDIT_SCHEMA,
        role=f"Neon Auditor: {t['id']}",
        type_name="neon-auditor",
        model="flash",
    )


phase("3. Adversarial Verification (Neon)")
audit_results = await parallel(audit_inputs, audit_one)

summary = {
    "scouts": scout_briefs,
    "provers": prover_results,
    "audits": audit_results,
}
import json
print(json.dumps(summary, indent=2))
