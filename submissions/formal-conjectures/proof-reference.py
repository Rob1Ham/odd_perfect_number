#!/usr/bin/env python3
"""Emit a declaration-local formal_proof patch for a published Palomar entry."""

import argparse
import difflib
import re
from pathlib import Path

TARGETS = {
    "toth": "descartes_non_example_factor_gt_ten_pow_twelve",
    "cube-free": "descartes_cubeFree_lt_seven_primeFactors_unique",
}
SOURCE = "FormalConjectures/Wikipedia/DescartesNumber.lean"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path, help="Google DeepMind formal-conjectures checkout")
    parser.add_argument("target", choices=TARGETS)
    parser.add_argument("entry", help="published Palomar entry URL for this theorem")
    args = parser.parse_args()
    if not re.fullmatch(r"https://palomar-registry\.org/entry\.html\?id=PALOMAR-\d{4}-\d{2}-\d{2}-\d{6}", args.entry):
        parser.error("supply a canonical published Palomar URL")
    original = (args.checkout / SOURCE).read_text()
    declaration = "theorem " + TARGETS[args.target] + " "
    tag = "@[category research solved, AMS 11]"
    before = tag + "\n" + declaration
    if original.count(before) != 1:
        parser.error("the expected unannotated declaration has changed; review the upstream source")
    after = '@[category research solved, AMS 11, formal_proof using lean4 at\n  "' + args.entry + '"]\n' + declaration
    edited = original.replace(before, after)
    print("".join(difflib.unified_diff(original.splitlines(True), edited.splitlines(True),
                                       "a/" + SOURCE, "b/" + SOURCE)), end="")


if __name__ == "__main__":
    main()
