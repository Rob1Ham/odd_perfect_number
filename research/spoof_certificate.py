"""Emit independently checkable subtrees for Dittmer's positive odd spoof problem."""

import argparse
from pathlib import Path

from spoof_boxes import Slot, branches, certificate


def offsets(code):
    """Record lengths and depths for all subtrees of the preorder encoding."""
    sizes = [0] * len(code)
    depths = [0] * len(code)
    for n in reversed(range(len(code))):
        if code[n] == "A" or code[n].islower():
            sizes[n] = depths[n] = 1
        else:
            right = n + 1 + sizes[n + 1]
            sizes[n] = 1 + sizes[n + 1] + sizes[right]
            depths[n] = 1 + max(depths[n + 1], depths[right])
    if sizes[0] != len(code):
        raise ValueError("preorder certificate has trailing data")
    return sizes, depths


def jump_table(code, sizes, start, end):
    result = []
    for j in range(start, end):
        jump = 0 if code[j] == "A" or code[j].islower() else 1 + sizes[j + 1]
        digits = []
        for _ in range(5):
            jump, digit = divmod(jump, 26)
            digits.append(chr(65 + digit))
        if jump:
            raise ValueError("subtree too large for jump table")
        result.extend(reversed(digits))
    return "".join(result)


def lean_rows(slots):
    return "#v[" + ", ".join(
        f"⟨{str(s.special).lower()},{s.base_lo},{s.base_hi},{s.exp_lo},{s.exp_hi}⟩"
        for s in slots
    ) + "]"


def lean_rank(k, special, chunk, saved_code=None):
    if saved_code is None:
        code, _, solutions = certificate(k, special, True)
        if solutions and (k != 5 or any(
                s != [(3, 2), (7, 2), (11, 2), (13, 2), (22021, 1)] for s in solutions)):
            raise ValueError(f"unexpected solutions: {solutions}")
    else:
        code = saved_code.read_text().strip()
    sizes, depths = offsets(code)
    rows = [Slot(i == special, 5 if i == special else 3, 0, 1 if i == special else 2, 0) for i in range(k)]
    prefix = f"r{k}_{special}"
    definitions = []
    allowed = f"({('descartesTuple :: []' if k == 5 else '[]')} : List (Fin {k} → ℕ × ℕ))"

    def emit(n, state):
        name = f"{prefix}_{n}"
        children = []
        if sizes[n] > chunk:
            axis, parity = divmod(ord(code[n]) - 66, 2)
            left, right = branches(state, axis, bool(parity))
            children = [emit(n + 1, left), emit(n + 1 + sizes[n + 1], right)]
        definitions.append(f"private def {name}_rows : Vector Slot {k} := {lean_rows(state)}")
        definitions.append(f"private theorem {name} : Covered (· ∈ {allowed}) {name}_rows := by")
        if children:
            definitions.extend([
                f"  exact covered_split (keep := (· ∈ {allowed})) {name}_rows ({axis} : Fin {k})",
                f"    Axis.{('exponent' if parity else 'base')} {children[0]} {children[1]}",
            ])
        else:
            end = n + sizes[n]
            table = jump_table(code, sizes, n, end)
            definitions.extend([
                f'  apply verifyCover_sound "{code[n:end]}".toUTF8 "{table}".toUTF8',
                f"    (spoofRule {allowed}) _ (spoofRule_sound _) {depths[n]} 0 {name}_rows",
                "  decide +kernel",
            ])
        definitions.append("")
        return name

    root = emit(0, rows)
    definitions.extend([
        f"theorem covered_{k}_{special} : Covered (· ∈ {allowed}) (initial ({special} : Fin {k})) := {root}",
        "",
    ])
    return definitions


def emit_four_project(directory, chunk):
    """Four serial modules bound memory during a clean parallel Lake build."""
    directory.mkdir(parents=True, exist_ok=True)
    groups = [[(k, i) for k in range(1, 4) for i in range(k)] + [(4, 0)], [(4, 1)], [(4, 2)], [(4, 3)]]
    for part, ranks in enumerate(groups, 1):
        dependency = "OddPerfect.SpoofCover" if part == 1 else f"OddPerfect.SpoofBelowFive.Part{part-1}"
        content = ["module", "", f"public import {dependency}", "", "public section", "",
                   "namespace OddPerfect.SpoofBox", ""]
        for k, i in ranks:
            content.extend(lean_rank(k, i, chunk))
        (directory / f"Part{part}.lean").write_text("\n".join(content + ["end OddPerfect.SpoofBox", ""]))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("slots", type=int, nargs="?")
    p.add_argument("special", type=int, nargs="?")
    p.add_argument("--four-project", action="store_true", help="emit all ranks through four slots into the output directory")
    p.add_argument("--chunk", type=int, default=63)
    p.add_argument("--input", type=Path)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    if args.chunk < 1:
        p.error("chunk size must be positive")
    if args.four_project:
        emit_four_project(args.output, args.chunk)
        return
    if args.slots is None or args.special is None:
        p.error("supply the length and special rank")
    content = ["module", "", "public import OddPerfect.SpoofCover", "", "public section",
               "", "namespace OddPerfect.SpoofBox", ""]
    if args.slots == 5:
        content.extend([
            "private def descartesTuple : Fin 5 → ℕ × ℕ := ![(3,2),(7,2),(11,2),(13,2),(22021,1)]", "",
        ])
    content.extend(lean_rank(args.slots, args.special, args.chunk, args.input))
    args.output.write_text("\n".join(content + ["end OddPerfect.SpoofBox", ""]))


if __name__ == "__main__":
    main()
