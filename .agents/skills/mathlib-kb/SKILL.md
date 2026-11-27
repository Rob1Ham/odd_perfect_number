---
name: mathlib-kb
description: >-
  Search and cross-reference the pinned Mathlib 4 checkout and OddPerfect theorem library
  using the local SQLite/FTS5 index (`research/tools/mathlib_kb.py`) and `research/MATHLIB_KB.md`.
---

# Mathlib & OddPerfect Knowledge Base Skill

Always consult the local theorem index before writing new helper lemmas on divisors, arithmetic functions, valuations, cyclotomic polynomials, multiplicative orders, quadratic reciprocity, Pell equations, or logarithmic bounds.

## Commands

```sh
# 1. Rebuild index after adding or editing Lean modules (~2s)
python3 research/tools/mathlib_kb.py index

# 2. Full-text BM25 search across Mathlib declarations, signatures, and docstrings
python3 research/tools/mathlib_kb.py search "cyclotomic isRoot orderOf" --scope mathlib

# 3. Filter to a Mathlib namespace/directory
python3 research/tools/mathlib_kb.py search "log_one_add" --module Mathlib.Analysis.SpecialFunctions.Log

# 4. Search existing OddPerfect structural lemmas to avoid duplicating project theorems
python3 research/tools/mathlib_kb.py search "euler_form" --scope project

# 5. Audit underutilized Mathlib modules and overlapping short names
python3 research/tools/mathlib_kb.py overlap

# 6. Regenerate research/MATHLIB_KB.md
python3 research/tools/mathlib_kb.py domain-map --out research/MATHLIB_KB.md
```

Read [research/MATHLIB_KB.md](../../../research/MATHLIB_KB.md) for the 7-domain map of Mathlib modules relevant to odd perfect numbers.
