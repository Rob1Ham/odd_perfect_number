"""Independently check the odd-index exponent rows stored in the Lean certificate."""

from argparse import ArgumentParser
from math import isqrt
from pathlib import Path
import re


ROW = re.compile(
    r"⟨(\d+),(\d+),(\d+),(0x[0-9a-f]+),(0x[0-9a-f]+)⟩"
)


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def putative_pairs(limit):
    for j in range(15, limit, 16):
        length = j + 2
        if not prime(length):
            continue
        total = length + 1
        divisors = set()
        for d in range(1, isqrt(total) + 1):
            if total % d == 0:
                divisors.update((d, total // d))
        for half in divisors:
            if half % 8 == 1 and prime(half):
                yield half, length


def verify_row(half, length, modulus, sums, squares):
    if not prime(modulus):
        raise ValueError(f"nonprime modulus {modulus}")
    for b in range(modulus):
        if b == 1:
            geometric = length % modulus
        else:
            geometric = ((pow(b, length, modulus) - 1) *
                         pow(b - 1, -1, modulus)) % modulus
        possible_square = (2 * b * b - 1) % modulus
        if not ((sums >> geometric) & 1 and (squares >> possible_square) & 1):
            raise ValueError(f"incomplete masks for {half=}, {length=}, {modulus=}")
        root_base = (2 * half * b * b - 1) % modulus
        value = pow(root_base, half, modulus)
        if (sums & squares) >> value & 1:
            raise ValueError(f"overlapping residues for {half=}, {length=}, {b=}")


def main():
    project = Path(__file__).resolve().parents[1]
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path,
                        default=project / "OddPerfect/OddIndexExponentScreen.lean")
    parser.add_argument("--limit", type=int, default=36207)
    args = parser.parse_args()

    rows = [tuple(int(field, 0) for field in group)
            for group in ROW.findall(args.certificate.read_text())]
    actual = {(half, length) for half, length, _, _, _ in rows}
    required = set(putative_pairs(args.limit))
    if len(actual) != len(rows) or actual != required:
        raise ValueError(f"length coverage differs at {actual ^ required}")
    for row in rows:
        verify_row(*row)
    print(f"Checked {len(rows)} candidate pairs and {sum(r[2] for r in rows)} "
          f"field residues below exponent {args.limit}.")


if __name__ == "__main__":
    main()
