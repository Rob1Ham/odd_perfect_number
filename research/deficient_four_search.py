"""Generate proof trees for odd deficient-perfect integers with four prime divisors.

The first four rows are distinct increasing prime bases with positive even
exponents. The fifth row has a positive formal base congruent to one modulo four.
For deficient-perfect numbers its exponent is one. The higher-exponent replay
allows every exponent congruent to one modulo four and at least five. The
value and position of the formal base are independent of the true bases.
Every row keeps inclusive bounds, with zero as an infinite upper bound.
State g is an odd divisor of the formal base. The five deficient-perfect
roots fix the two smallest primes. The higher-exponent root leaves all
prime bases and all exponents unbounded above.
"""

import argparse
from collections import Counter
from dataclasses import dataclass, replace
from fractions import Fraction
from functools import lru_cache
import json
from math import isqrt, lcm, prod
from pathlib import Path

from spoof_boxes import Slot, last_solution


@lru_cache(4096)
def ratio(base, exponent):
    if base == 0:
        return Fraction(1)
    if exponent == 0:
        return Fraction(base, base - 1)
    value = base**exponent
    return Fraction((base*value - 1)//(base - 1), value)


@lru_cache(4096)
def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


@lru_cache(2048)
def deliveries(base, exponent, prime_limit):
    """Small odd prime witnesses suffice. No full sigma factorization is assumed."""
    sigma = (base**(exponent + 1) - 1)//(base - 1)
    return tuple(p for p in primes_below(prime_limit) if sigma % p == 0)


@lru_cache(8)
def primes_below(limit):
    return tuple(p for p in range(3, limit + 1, 2) if is_prime(p))


def first_multiplier(lower, g):
    k = (lower + g - 1)//g
    return g*(k + (pow(g, -1, 4) - k) % 4)


def last_multiplier(upper, g):
    k = upper//g
    return g*(k - (k - pow(g, -1, 4)) % 4)


def prime_lower(lower):
    # Avoid long primality computations at remote endpoints. Skipping only
    # even integers there is itself a certified lower-bound step.
    candidate = max(lower, 3) | 1
    while candidate < 1000000 and not is_prime(candidate):
        candidate += 2
    return candidate


def prime_upper(upper):
    candidate = (upper - 1) | 1
    while 3 <= candidate < 1000000 and not is_prime(candidate):
        candidate -= 2
    return max(1, candidate)


def bound(slot, lower=0, upper=0):
    return replace(slot, base_lo=max(lower, slot.base_lo),
                   base_hi=min(slot.base_hi, upper) if slot.base_hi and upper else slot.base_hi or upper)


def initial_rows(first, second, higher):
    normal = [Slot(False,first or 3,first,2,0), Slot(False,second or 3,second,2,0),
              Slot(False,3,0,2,0), Slot(False,3,0,2,0)]
    return normal + [Slot(True,5,0,5 if higher else 1,0 if higher else 1)]


def ordinary_leaf(rows):
    if any(s.base_hi and s.base_lo > s.base_hi for s in rows):
        return True
    low = prod(ratio(s.base_hi, s.exp_lo) for s in rows)
    high = prod(ratio(s.base_lo, s.exp_hi) for s in rows)
    return (low > 2 or high < 2 or (low == 2 and any(not s.base_hi for s in rows))
            or (high == 2 and any(not s.exp_hi for s in rows)))


@dataclass
class Node:
    rows: tuple
    modulus: int
    steps: list
    end: tuple


class Search:
    def __init__(self, prime_limit=1999, arithmetic=True, exponent_weight=4, cap=100000, higher=False):
        self.higher = higher
        self.prime_limit = prime_limit
        self.arithmetic = arithmetic
        self.exponent_weight = exponent_weight
        self.cap = cap
        self.nodes = []
        self.solutions = set()
        self.steps = Counter()
        self.terminals = Counter()
        self.max_depth = 0
        self.max_prime = 0
        self.max_g = 1
        self.max_base = 0
        self.max_exponent = 0

    def root(self, second, first=3):
        return self.visit(initial_rows(first, second, self.higher), 1, 0)

    def visit(self, rows, g, depth):
        self.max_depth = max(self.max_depth, depth)
        if len(self.nodes) >= self.cap:
            raise RuntimeError(f"node limit {self.cap} reached")
        if depth > 200:
            raise RuntimeError(f"excessive depth at {rows}, modulus {g}")
        start_rows, start_g = tuple(rows), g
        steps = []

        def step(tag, *args):
            steps.append((tag, *args))
            self.steps[tag] += 1

        def finish(tag, *args):
            number = len(self.nodes)
            self.nodes.append(Node(start_rows, start_g, steps, (tag, *args)))
            self.terminals[tag] += 1
            return number

        for _ in range(32):
            old, old_g = rows.copy(), g
            for i in range(4):
                s = rows[i]
                start = max(s.base_lo, rows[i-1].base_lo + 1 if i else 3)
                lower = prime_lower(start)
                if lower != s.base_lo:
                    step('primeLo', i, lower)
                    rows[i] = bound(s, lower=lower)
                if s.base_hi and s.base_hi < lower:
                    return finish('reject')
            for i in reversed(range(4)):
                s = rows[i]
                after = rows[i+1].base_hi if i < 3 else 0
                stop = min(s.base_hi or after-1, after-1) if after else s.base_hi
                if stop:
                    upper = prime_upper(stop)
                    if upper != s.base_hi:
                        step('primeHi', i, upper)
                        rows[i] = bound(s, upper=upper)
                    if upper < s.base_lo:
                        return finish('reject')
            x = rows[4]
            lower = first_multiplier(x.base_lo, g)
            if lower != x.base_lo:
                step('xLo', lower)
                rows[4] = bound(rows[4], lower=lower)
            if x.base_hi:
                if lower > x.base_hi:
                    return finish('reject')
                upper = last_multiplier(x.base_hi, g)
                if upper != x.base_hi:
                    step('xHi', upper)
                    rows[4] = bound(rows[4], upper=upper)
            required = {}
            for i, s in enumerate(rows):
                if s.base_lo == s.base_hi and (s.exp_lo == s.exp_hi or s.special):
                    e = s.exp_lo if s.exp_lo == s.exp_hi else 1
                    for r in deliveries(s.base_lo, e, self.prime_limit):
                        required.setdefault(r, i)
            for r, src in sorted(required.items()):
                options = [i for i, s in enumerate(rows[:4]) if s.base_lo <= r and
                           (not s.base_hi or r <= s.base_hi)]
                new_g = lcm(g, r)
                x = rows[4]
                x_ok = not x.base_hi or first_multiplier(x.base_lo, new_g) <= x.base_hi
                if not options and not x_ok:
                    self.max_prime = max(self.max_prime, r)
                    return finish('missing', src, r)
                if not options and new_g != g:
                    step('grow', src, r)
                    self.max_prime = max(self.max_prime, r)
                    g = new_g
                elif not x_ok and len(options) == 1:
                    j = options[0]
                    if (rows[j].base_lo, rows[j].base_hi) != (r, r):
                        step('fix', src, r, j)
                        self.max_prime = max(self.max_prime, r)
                        rows[j] = bound(rows[j], lower=r, upper=r)
            if ordinary_leaf(rows):
                return finish('reject')
            if self.arithmetic:
                lows = [ratio(s.base_hi, s.exp_lo) for s in rows]
                highs = [ratio(s.base_lo, s.exp_hi) for s in rows]
                low, high = prod(lows), prod(highs)
                for i, s in enumerate(rows):
                    if s.base_lo == s.base_hi:
                        continue
                    min_ratio = 2*highs[i]/high
                    max_ratio = 2*lows[i]/low
                    if max_ratio <= 1:
                        # The full interval comparison will deal with an endpoint
                        # equality. No tightening is needed here.
                        continue
                    min_base = 1/(max_ratio-1)
                    lo = (min_base.numerator+min_base.denominator-1)//min_base.denominator
                    if lo > rows[i].base_lo:
                        discarded = rows.copy()
                        discarded[i] = bound(discarded[i], upper=lo-1)
                        if ordinary_leaf(discarded):
                            step('dropLo', i, lo)
                            rows[i] = bound(rows[i], lower=lo)
                            if ordinary_leaf(rows):
                                return finish('reject')
                    if min_ratio > 1:
                        max_base = (1 if s.exp_hi == 1 else min_ratio)/(min_ratio - 1)
                        hi = max_base.numerator//max_base.denominator
                        if hi > 0 and (not rows[i].base_hi or hi < rows[i].base_hi):
                            discarded = rows.copy()
                            discarded[i] = bound(discarded[i], lower=hi+1)
                            if ordinary_leaf(discarded):
                                step('dropHi', i, hi)
                                rows[i] = bound(rows[i], upper=hi)
                                if ordinary_leaf(rows):
                                    return finish('reject')
            if old == rows and old_g == g:
                break
        self.max_g = max(self.max_g, g)
        self.max_base = max(self.max_base, *(max(s.base_lo, s.base_hi) for s in rows))
        self.max_exponent = max(self.max_exponent, *(max(s.exp_lo, s.exp_hi) for s in rows))
        free = [i for i, s in enumerate(rows) if s.base_lo != s.base_hi or s.exp_lo != s.exp_hi]
        if len(free) <= 1:
            i = free[0] if free else 4
            sol = last_solution(rows, i)
            if sol:
                table = tuple(sol)
                if table != ((3,2),(7,2),(11,2),(13,2),(22021,1)):
                    raise RuntimeError(f"additional positive balanced tuple at {rows}: {table}")
                self.solutions.add(table)
            return finish('last', i)
        choices = []
        for i in free:
            s = rows[i]
            mid = ratio(s.base_lo, s.exp_lo)
            if s.base_lo != s.base_hi:
                low = ratio(s.base_hi, s.exp_lo)
                choices.append(((mid-low)/mid*(3 if i<4 else 1), i, False))
            if s.exp_lo != s.exp_hi:
                high = ratio(s.base_lo, s.exp_hi)
                choices.append(((high-mid)/mid*(self.exponent_weight if s.base_lo==s.base_hi else 1), i, True))
        _, i, exponent = max(choices)
        s = rows[i]
        left, right = rows.copy(), rows.copy()
        if exponent:
            cut = s.exp_lo
            left[i], right[i] = replace(s,exp_hi=cut), replace(s,exp_lo=cut+s.stride)
        else:
            cut = s.base_cut()
            # A raw integer cut has complementary branches even when a bound
            # has just changed via a rational comparison.
            left[i], right[i] = bound(s, upper=cut), bound(s, lower=cut+1)
        a = self.visit(left, g, depth+1)
        b = self.visit(right, g, depth+1)
        if exponent and i == 4:
            return finish('splitSpecial', cut, a, b)
        return finish('splitExp' if exponent else 'splitBase', i, cut, a, b)




def replay(nodes, roots, higher):
    """Check the emitted operation stream from root states, independently of search choices."""
    known = ((3,2), (7,2), (11,2), (13,2), (22021,1))

    def visit(index, rows, g):
        node = nodes[index]
        assert node.rows == tuple(rows) and node.modulus == g

        def recipients(src, r):
            s = rows[src]
            assert s.base_lo == s.base_hi
            assert is_prime(r) and r % 2 == 1
            assert ((s.exp_lo == s.exp_hi and sum(s.base_lo**e for e in range(s.exp_lo+1)) % r == 0)
                    or (s.special and (s.base_lo+1) % r == 0))
            matches = [i for i, slot in enumerate(rows[:4]) if slot.base_lo <= r and
                       (not slot.base_hi or r <= slot.base_hi)]
            modulus = lcm(g,r)
            x = rows[4]
            return matches, not x.base_hi or first_multiplier(x.base_lo,modulus) <= x.base_hi

        for tag,*xs in node.steps:
            if tag == 'primeLo':
                i,b = xs
                bottom = max(rows[i].base_lo, rows[i-1].base_lo+1 if i else 3)
                assert not any(is_prime(q) for q in range(bottom,b))
                rows[i] = bound(rows[i], lower=b)
            elif tag == 'primeHi':
                i,b = xs
                tops = [v for v in (rows[i].base_hi, rows[i+1].base_hi-1 if i<3 and rows[i+1].base_hi else 0) if v]
                assert tops and not any(is_prime(q) for q in range(b+1,min(tops)+1))
                rows[i] = bound(rows[i], upper=b)
            elif tag == 'xLo':
                assert first_multiplier(rows[4].base_lo,g) >= xs[0]
                rows[4] = bound(rows[4], lower=xs[0])
            elif tag == 'xHi':
                assert rows[4].base_hi and first_multiplier(xs[0]+1,g) > rows[4].base_hi
                rows[4] = bound(rows[4], upper=xs[0])
            elif tag in ('dropLo','dropHi'):
                i,b = xs
                discarded = rows.copy()
                if tag == 'dropLo':
                    discarded[i] = bound(rows[i], upper=b-1)
                    rows[i] = bound(rows[i], lower=b)
                else:
                    discarded[i] = bound(rows[i], lower=b+1)
                    rows[i] = bound(rows[i], upper=b)
                assert ordinary_leaf(discarded)
            elif tag == 'grow':
                src,r = xs
                js,x_ok = recipients(src,r)
                assert not js
                g = lcm(g,r)
            elif tag == 'fix':
                src,r,j = xs
                js,x_ok = recipients(src,r)
                assert js == [j] and not x_ok
                rows[j] = bound(rows[j],lower=r,upper=r)
            else:
                raise ValueError(tag)
        tag,*args = node.end
        if tag == 'reject':
            assert ordinary_leaf(rows)
        elif tag == 'last':
            i, = args
            assert all(j == i or (s.base_lo == s.base_hi and s.exp_lo == s.exp_hi) for j,s in enumerate(rows))
            result = last_solution(rows,i)
            assert result is None or tuple(result) == known
        elif tag == 'missing':
            js,x_ok = recipients(*args)
            assert not js and not x_ok
        elif tag in ('splitBase','splitExp','splitSpecial'):
            i,cut,a,b = args if tag != 'splitSpecial' else [4,*args]
            left,right = rows.copy(),rows.copy()
            if tag == 'splitBase':
                assert cut >= 1
                left[i] = bound(rows[i],upper=cut)
                right[i] = bound(rows[i],lower=cut+1)
            else:
                assert cut % rows[i].stride == int(rows[i].special) and cut == rows[i].exp_lo and not rows[i].exp_hi
                left[i] = replace(rows[i],exp_hi=cut)
                right[i] = replace(rows[i],exp_lo=cut+rows[i].stride)
            visit(a,left,g)
            visit(b,right,g)
        else:
            raise ValueError(tag)

    for (first,second),root in roots.items():
        visit(root, initial_rows(first, second, higher), 1)


def partition(nodes, root, limit):
    """Each named proof covers at most limit search nodes other than its holes."""
    boundaries = {root}

    def size(index):
        end = nodes[index].end
        if end[0] not in ('splitBase', 'splitExp', 'splitSpecial'):
            return 1
        left, right = end[-2:]
        parts = [(size(left), left), (size(right), right)]
        total = 1 + sum(cost for cost, child in parts)
        for cost, child in sorted(parts, reverse=True):
            if total <= limit:
                break
            boundaries.add(child)
            total -= cost
        return total

    size(root)
    return sorted(boundaries)


def lean_rows(rows):
    return '#v[' + ', '.join(f'⟨{str(s.special).lower()},{s.base_lo},{s.base_hi},{s.exp_lo},{s.exp_hi}⟩'
                             for s in rows) + ']'


def lean_tree(nodes, root, boundaries):
    refs = []

    def build(index, indent):
        pad = ' ' * indent
        if index != root and index in boundaries:
            ref = len(refs)
            refs.append(index)
            return [f'{pad}.use {ref}']
        node = nodes[index]
        lines = [pad + '.step (.' + ' '.join(map(str, op)) + ') <|' for op in node.steps]
        end = node.end
        if end[0] in ('splitBase', 'splitExp', 'splitSpecial'):
            lines.append(pad + '.' + ' '.join(map(str, end[:-2])))
            for child in end[-2:]:
                sub = build(child, indent+2)
                sub[0] = ' '*(indent+2) + '(' + sub[0].lstrip()
                sub[-1] += ')'
                lines.extend(sub)
        else:
            lines.append(pad + '.' + ' '.join(map(str, end)))
        return lines

    return build(root, 2), refs


def emit_lean(nodes, roots, output, chunk, per_file, higher):
    for (first,second), root in roots.items():
        suffix = 'General' if not first and not second else 'FiveSeven' if first==5 else str(second)
        profile = 'Power' if higher else ''
        module = f'Deficient{profile}Replay{suffix}'
        directory = output / module
        directory.mkdir(parents=True, exist_ok=True)
        # Keep the smallest primary root intact for a one-module benchmark.
        cuts = partition(nodes, root, 100 if second == 17 and not higher else chunk)
        boundaries = set(cuts)
        root_name = f'closed{profile}' + (f'Second{second}' if first==3 else suffix)
        names = {node: (root_name if node == root else f'deficientFour{profile}{suffix}Part{n:03}')
                 for n,node in enumerate(cuts)}
        previous = 'OddPerfect.DeficientTree'
        for part in range(0, len(cuts), per_file):
            lines = ['module', '', f'public import {previous}', '', 'public section', '',
                     'namespace OddPerfect.DeficientSlots', 'open OddPerfect.SpoofBox (Slot)', '',
                     'set_option maxRecDepth 16000', 'set_option maxHeartbeats 0', '']
            for index in cuts[part:part+per_file]:
                node = nodes[index]
                name = names[index]
                code, refs = lean_tree(nodes, index, boundaries)
                lines.append(f'private def {name}Tree : Tree :=')
                lines.extend(code)
                lines.append('')
                if refs:
                    lines.append(f'private def {name}Refs : List Known := [')
                    for n,ref in enumerate(refs):
                        target = nodes[ref]
                        suffix = ',' if n+1 < len(refs) else ']'
                        lines.append(f'  ⟨{lean_rows(target.rows)}, {target.modulus}, {names[ref]}⟩{suffix}')
                    lines.append('')
                ref_name = f'{name}Refs' if refs else '[]'
                lines.extend([f'theorem {name} : Closed ({lean_rows(node.rows)} : Vector Slot 5) {node.modulus} :=',
                              f'  Tree.sound {name}Tree {ref_name} _ _ (by decide +kernel)', ''])
            lines.extend(['end OddPerfect.DeficientSlots', ''])
            filename = f'Part{part//per_file+1:03}'
            (directory / f'{filename}.lean').write_text(''.join(line+'\n' for line in lines[:-1]))
            previous = f'OddPerfect.{module}.{filename}'
        print(f'{first},{second}: {len(cuts)} certified subtrees, public import {previous}')

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--second', nargs='+', type=int)
    parser.add_argument('--higher', action='store_true', help='use special exponents congruent to one modulo four and at least five')
    parser.add_argument('--unrestricted', action='store_true', help='leave all four true bases initially unbounded')
    parser.add_argument('--prime-limit', type=int, default=1999)
    parser.add_argument('--no-arithmetic', action='store_true')
    parser.add_argument('--exponent-weight', type=int, default=4)
    parser.add_argument('--cap', type=int, default=100000)
    parser.add_argument('--json', type=Path, help='write replay records in postorder')
    parser.add_argument('--lean', type=Path, help='Lean module root, normally OddPerfect')
    parser.add_argument('--chunk', type=int, default=45, help='maximum search nodes per checked subtree')
    parser.add_argument('--per-file', type=int, default=5, help='checked subtrees per Lean module')
    args = parser.parse_args()
    if args.chunk < 2 or args.per_file < 1:
        parser.error('choose --chunk ≥ 2 and --per-file ≥ 1')
    tree = Search(args.prime_limit, not args.no_arithmetic, args.exponent_weight, args.cap, args.higher)
    roots = {}
    params = [(3,p) for p in args.second or [5,7,11,13,17]]
    if args.unrestricted or (args.higher and args.second is None):
        params = [(0,0)]
    for first,second in params:
        start = len(tree.nodes)
        roots[first,second] = tree.root(second, first)
        print(f'second {second}, {len(tree.nodes)-start} nodes', flush=True)
    replay(tree.nodes, roots, args.higher)
    print('total',len(tree.nodes),'max depth',tree.max_depth,'max g',tree.max_g,'max delivered prime',tree.max_prime,
          'max base bound',tree.max_base,'max exponent bound',tree.max_exponent)
    print('steps',dict(sorted(tree.steps.items())),'terminals',dict(sorted(tree.terminals.items())))
    print('solutions',sorted(tree.solutions))
    if args.lean:
        emit_lean(tree.nodes, roots, args.lean, args.chunk, args.per_file, args.higher)
    if args.json:
        root_keys = {(str(q) if p==3 else f'{p}_{q}'):i for (p,q),i in roots.items()}
        record = {'schema':1, 'roots':root_keys, 'nodes':[[n.steps,n.end] for n in tree.nodes]}
        args.json.write_text(json.dumps(record,separators=(',',':'))+'\n')


if __name__ == '__main__':
    main()
