---
name: carbon-reevaluation-loop
description: >-
  Runbook for the Carbon Strategist session on odd_perfect_number. Each round reviews the
  BRANCH_MAP frontier, generates informal ideas, runs the four pre-dispatch gates and a
  Skeptic review, dispatches Neon (`Model="flash"`) provers only for surviving ideas, then
  integrates, audits, commits, and records branch impact.
---

# Carbon research loop

Use this skill whenever you coordinate a research round from a Carbon (`pro`) session. The aim is to change the status of [BRANCH_MAP.md](../../../research/BRANCH_MAP.md) nodes. Producing declarations is not the aim. Read [AGENTS.md](../../../AGENTS.md) §0 first.

## Phase 0: Hygiene (blocking)

```sh
git status --short
python3 research/tools/evaluate_progress.py --strict --dashboard research/PROGRESS_DASHBOARD.md
```

If `OddPerfect.lean` imports untracked files, or the last audited state is uncommitted, commit and tag (`audit-YYYYMMDD`) before anything else.

## Phase 1: Frontier review

1. Read section 0 of `research/PROGRESS_DASHBOARD.md`, then [FLOOR_CEILING.md](../../../research/FLOOR_CEILING.md) and [NO_GO.md](../../../research/NO_GO.md).
2. For each active node (at most 3), write one line naming its single missing ingredient: a ceiling, a cut of the count-LP ray, a descent step, or an arithmetic reuse bound.
3. Run `python3 research/tools/count_lp.py --branch <id>` for every node that has count constraints. Record the current recession ray.

## Phase 2: Idea generation (informal, no Lean)

Add 1–3 entries to [IDEAS.md](../../../research/IDEAS.md). Each entry needs:
- the target node;
- an informal proof sketch;
- a closure argument;
- which non-spoofable property it uses (primality of bases / closure of σ-factorizations / exact valuations);
- a kill criterion.

Read the relevant literature before inventing. Start with the closest results in [CORPUS.md](../../../research/CORPUS.md).

## Phase 3: Gates and Skeptic

Run gates G1–G4 from [GATES.md](../../../research/GATES.md) and paste the gate record into the idea entry.

- Test new count inequalities with `count_lp.py --add "<expr>"`. They pass G2 only if the ray changes or the LP becomes bounded.
- Invoke the Skeptic (`.agents/agents/skeptic.md`, a separate `pro` session) on every idea that passes the gates.
- Any gate FAIL or Skeptic `KILL` → set the status to `KILLED` and add a NO_GO entry if the reason generalizes. **This counts as a successful round.**

## Phase 4: Formalization (Neon)

Only ideas with status `SURVIVES` are formalized. Pipeline: `neon-mathlib-scout` → `neon-prover` → `neon-auditor`.

- Run at most 3 concurrent provers on disjoint files.
- The prompt must contain the closure argument and the BRANCH_MAP node id. The prover copies both into the module docstring.
- `neon-harvester` gets at most one slot, and only for modules on an active node's critical path.
- Terminating deliverables from ROADMAP §3 (literature replays, Mathlib upstreaming) may use one further background slot.

## Phase 5: Integration and audit

1. Wire `PASS`-audited modules into `OddPerfect.lean`.
2. Run the authoritative gate:
   ```sh
   lake build && lake lean research/Audit.lean
   ```
3. Add the headline theorems to `research/claims_registry.json` and run `python3 research/tools/claims.py`.
4. Add newly proven count inequalities to `research/count_constraints.json` (set `verified: true` only after reading the Lean statement).
5. Regenerate the dashboard: `python3 research/tools/evaluate_progress.py --record --strict`.
6. Append a LEDGER entry with **Branch impact**, **Gate record**, and **Classification** (REPLAY / CANDIDATE-NEW / REDUCTION / LIBRARY).
7. Commit and tag.

## Phase 6: Pivot check

- **Advancing** means one of:
  - a node changed status;
  - a ceiling was added to FLOOR_CEILING;
  - a count-LP ray was cut;
  - a descent step or reduction shrank a node to a strictly smaller, precisely stated family;
  - an idea was killed with a documented, generalizable reason.
- **Not advancing**: new declarations with none of the above.
- After **two consecutive non-advancing rounds** on a node, freeze it (`active: false`), write a NO_GO entry explaining the stall, and promote another node, or spend the slot on a terminating deliverable.
- Keep [WHITEBOARD.md](../../../research/WHITEBOARD.md) current. Clear finished sketches every round and move history to LEDGER.
