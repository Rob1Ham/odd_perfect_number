"""Discover candidate-support certificates for OddPerfect.SupportSieve (standard Python)."""

import argparse
from math import gcd, isqrt, prod


def odd_primes(bound):
    return [
        p for p in range(3, bound + 1, 2)
        if all(p % q for q in range(3, isqrt(p) + 1, 2))
    ]


def may_be_smooth(n, mask):
    for _ in range(12):
        if n == 1:
            return True
        common = gcd(n, mask)
        if common == 1:
            return False
        n //= common
    return True


def certificate(bound):
    support = odd_primes(bound)
    primes = [2, *support]
    rows = []
    while support:
        mask = 2 * prod(support)
        lengths = [l for l in primes if any((r - 1) % l == 0 for r in support)]
        next_support = [
            p for p in support if any(
                (l != 2 or p % 4 == 1) and may_be_smooth((p ** l - 1) // (p - 1), mask)
                for l in lengths
            )
        ]
        if next_support == support:
            raise ValueError(f"nonempty fixed point at {support}")
        rows.append((lengths, next_support))
        support = next_support
    return rows


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("bound", type=int)
    args = parser.parse_args()
    rows = certificate(args.bound)
    print("[" + ",\n ".join(map(str, rows)) + "]")
