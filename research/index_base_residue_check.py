"""Independently replay the finite prime-base tables with Python integers."""

from argparse import ArgumentParser
from math import isqrt
from pathlib import Path
import re


def primes_to(limit):
    sieve = bytearray(b'\x01') * (limit + 1)
    sieve[0:2] = b'\x00\x00'
    for prime in range(2, isqrt(limit) + 1):
        if sieve[prime]:
            multiples = range(prime * prime, limit + 1, prime)
            sieve[multiples.start:limit + 1:prime] = bytes(len(multiples))
    return [n for n, flag in enumerate(sieve) if flag]


def geometric(base, length, modulus):
    if base % modulus == 1:
        return length % modulus
    return (pow(base, length, modulus) - 1) * pow(base - 1, -1, modulus) % modulus


def verify(source, cutoff, use_return):
    rows = [tuple(map(int, row)) for row in re.findall(r'⟨(\d+),(\d+),(\d+)⟩', source.read_text())]
    primes = primes_to(cutoff)
    half_lengths = [d for d in primes if d % 8 == 1 and d <= (cutoff - 1) // 8]
    expected = {(p, d) for p in primes if p < cutoff and p % 8 == 1
                for d in half_lengths if d <= (p - 1) // 8 and (p - 1) % d == 0}
    assert len(rows) == len(expected) and {(p, d) for p, d, _ in rows} == expected
    for p, d, r in rows:
        assert r in primes and r % 2 == 1 and r < 2*d - 1
        squares = {u*u % r for u in range(r)}
        return_values = {geometric(p, 16*k + 1, r) for k in range(r-1)}
        for q in range(1, r):
            power = pow(q, d, r)
            required = [2*d*(q+1), 2*(power+1), p*geometric(q, d, r)]
            if any(z % r not in squares for z in required):
                continue
            assert use_return and p % r != 1 and power not in return_values, (p, d, r, q)
    print(f'{source.name}: {len(rows)} pairs, {sum(r-1 for _,_,r in rows)} nonzero residues, '
          f'moduli {sorted({r for _,_,r in rows})}')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--source-dir', type=Path, default=Path(__file__).resolve().parents[1] / 'OddPerfect')
    directory = parser.parse_args().source_dir
    verify(directory / 'IndexSquarefreePrime33049.lean', 33049, False)
    verify(directory / 'IndexPrime100001.lean', 100001, True)
