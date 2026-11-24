"""Generate preorder interval certificates for positive odd spoof factorizations."""

import argparse
from dataclasses import dataclass, replace
from fractions import Fraction
from functools import cache
from math import gcd
from pathlib import Path


@cache
def abundancy(base, exponent):
    """Zero base denotes its limit at infinity; zero exponent denotes an unbounded exponent."""
    if base == 0:
        return Fraction(1)
    if exponent == 0:
        return Fraction(base, base - 1)
    return Fraction(base ** (exponent + 1) - 1, (base - 1) * base**exponent)


@dataclass(frozen=True)
class Slot:
    special: bool
    base_lo: int
    base_hi: int
    exp_lo: int
    exp_hi: int

    @property
    def stride(self):
        return 4 if self.special else 2

    def round_up(self, value, residue):
        return value + (residue - value) % self.stride

    def round_down(self, value, residue):
        return max(0, value - (value - residue) % self.stride)

    def base_cut(self):
        lo, hi = self.base_lo, self.base_hi
        middle = 2 * lo * hi // (lo + hi) if hi else 2 * lo
        cut = lo + self.stride * ((middle - lo) // self.stride)
        return min(cut, hi - self.stride) if hi else cut


def cap(old, new):
    return min(old, new) if old else new


def branches(slots, index, split_exponent):
    chosen = slots[index]
    left, right = slots.copy(), slots.copy()
    if split_exponent:
        cut = chosen.exp_lo
        left[index] = replace(chosen, exp_hi=cut)
        right[index] = replace(chosen, exp_lo=cut + chosen.stride)
    else:
        cut = chosen.base_cut()
        lower = chosen.round_up(cut + 1, 1)
        for j, slot in enumerate(slots):
            if j <= index:
                left[j] = replace(slot, base_hi=cap(slot.base_hi, slot.round_down(cut, 1)))
            if j >= index:
                right[j] = replace(slot, base_lo=max(slot.base_lo, slot.round_up(lower, 1)))
    return left, right


def last_solution(slots, index):
    """Recover a possible final slot from the exact geometric sums of the others."""
    total, twice = 1, 2
    for j, slot in enumerate(slots):
        if j == index:
            continue
        b, e = slot.base_lo, slot.exp_lo
        total *= (b ** (e + 1) - 1) // (b - 1)
        twice *= b**e
    common = gcd(total, twice)
    power, divisor_sum = total // common, twice // common
    if divisor_sum <= power:
        return None
    b = (power - 1) // (divisor_sum - power) + 1
    slot = slots[index]
    if (b < slot.base_lo or (slot.base_hi and b > slot.base_hi)
            or b % slot.stride != 1):
        return None
    e, remaining = 0, power
    while remaining % b == 0:
        remaining //= b
        e += 1
    if (remaining != 1 or e < slot.exp_lo or (slot.exp_hi and e > slot.exp_hi)
            or e % slot.stride != int(slot.special)
            or (b ** (e + 1) - 1) // (b - 1) != divisor_sum):
        return None
    return [(b, e) if j == index else (s.base_lo, s.exp_lo) for j, s in enumerate(slots)]


def certificate(k, special, use_last=False):
    if not 0 <= special < k <= 31:
        raise ValueError("Choose a special slot among 1–31 slots")
    code = []
    solutions = []
    depth = 0

    def visit(slots, level):
        nonlocal depth
        depth = max(depth, level)
        lower = upper = Fraction(1)
        choices = []
        for i, slot in enumerate(slots):
            if (slot.base_hi and slot.base_hi < slot.base_lo) or (
                slot.exp_hi and slot.exp_hi < slot.exp_lo
            ):
                code.append("A")
                return
            low = abundancy(slot.base_hi, slot.exp_lo)
            high = abundancy(slot.base_lo, slot.exp_hi)
            middle = abundancy(slot.base_lo, slot.exp_lo)
            lower *= low
            upper *= high
            if slot.base_lo != slot.base_hi:
                choices.append(((middle - low) / low, i, False))
            if slot.exp_lo != slot.exp_hi:
                choices.append(((high - middle) / high, i, True))
        if lower > 2 or upper < 2 or (lower == 2 and any(not s.base_hi for s in slots)) or (
            upper == 2 and any(not s.exp_hi for s in slots)
        ):
            code.append("A")
            return
        if use_last:
            free = [i for i, s in enumerate(slots) if s.base_lo != s.base_hi or s.exp_lo != s.exp_hi]
            if len(free) == 1:
                i = free[0]
                solution = last_solution(slots, i)
                if solution:
                    solutions.append(solution)
                code.append(chr(97 + i))
                return
        if not choices:
            solutions.append([(s.base_lo, s.exp_lo) for s in slots])
            code.append("A")
            return
        _, i, split_exponent = max(choices)
        code.append(chr(66 + 2 * i + int(split_exponent)))
        left, right = branches(slots, i, split_exponent)
        visit(left, level + 1)
        visit(right, level + 1)

    start = [
        Slot(i == special, 5 if i == special else 3, 0, 1 if i == special else 2, 0)
        for i in range(k)
    ]
    visit(start, 1)
    return "".join(code), depth, solutions


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("slots", type=int)
    parser.add_argument("special", type=int, nargs="?", help="zero-based position in nondecreasing base order")
    parser.add_argument("--output", type=Path, help="write the ASCII certificate")
    parser.add_argument("--last", action="store_true", help="use the one-missing-component rule")
    args = parser.parse_args()
    if args.special is None:
        parser.error("supply the position of the special slot")
    code, depth, solutions = certificate(args.slots, args.special, args.last)
    print(f"{len(code)} nodes, depth {depth}, solutions {solutions}")
    if args.output:
        args.output.write_text(code, encoding="ascii")


if __name__ == "__main__":
    main()
