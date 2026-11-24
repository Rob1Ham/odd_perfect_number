#!/usr/bin/env python3
"""Generate the low-bit-first affine inverse transcript consumed by EllipticPrime.lean."""

import argparse
from math import gcd


def add_point(n, a, first, second):
    if first is None:
        return second, 0
    if second is None:
        return first, 0
    x, y = first
    z, w = second
    if x == z:
        if (y+w) % n == 0:
            return None, 0
        if y != w:
            raise ValueError('incompatible ordinates for equal abscissas')
        numerator, denominator = 3*x*x+a, 2*y
    else:
        numerator, denominator = y-w, x-z
    if gcd(denominator, n) != 1:
        raise ValueError('a denominator has a nontrivial common factor with the subject')
    inverse = pow(denominator, -1, n)
    slope = numerator*inverse % n
    new_x = (slope*slope-x-z) % n
    return (new_x, (slope*(x-new_x)-y) % n), inverse


def scalar_trace(n, a, x, y, q):
    if n < 2 or q < 1:
        raise ValueError('the modulus must exceed one and the scalar must be positive')
    start = x % n, y % n
    point, trace = None, []
    for bit in bin(q)[2:]:
        point, double = add_point(n, a, point, point)
        addition = 0
        if bit == '1':
            point, addition = add_point(n, a, point, start)
        trace.append((double, addition))
    return point, trace[::-1]


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for field in ('n', 'a', 'x', 'y', 'q'):
        parser.add_argument(field, type=int)
    args = parser.parse_args()
    result, transcript = scalar_trace(args.n, args.a, args.x, args.y, args.q)
    if result is not None:
        parser.error('the scalar multiple of the supplied point is nonzero')
    print('[' + ',\n '.join(map(str, transcript)) + ']')
