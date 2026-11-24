#!/usr/bin/env python3
"""Search exact-exponent chains and emit hints for the Lean kernel replay."""

import argparse
from collections import Counter
from dataclasses import dataclass, field
from functools import cache
from itertools import count
from math import factorial, gcd, isqrt, prod
from pathlib import Path
from shutil import which
from subprocess import check_output, TimeoutExpired


# Incomplete factorizations that arise on the two seed paths. Lean accepts a
# proposed factor only after divisibility, and proves primality for every split.
KNOWN_FACTORS = (
    10303, 18457, 21613, 73774717787791, 31747594185191, 22280841470107301759731,
    297134095231, 25332490598403837286469216576711, 88009573,
    304018940824561, 829007553280001, 12601, 14421466756460791, 97298466526008161,
)


def prime_candidates(bound):
    return [p for p in range(2, bound) if all(p % q for q in range(2, isqrt(p)+1))]


TRIAL_PRIMES = prime_candidates(10001)


class Factorer:
    def __init__(self, timeout):
        self.command = which('gfactor') or which('factor')
        if not self.command:
            raise SystemExit('Install GNU coreutils for the factor command.')
        self.timeout = timeout

    def full(self, n, timeout=None):
        reply = check_output([self.command, str(n)], text=True, timeout=timeout)
        return list(map(int, reply.partition(':')[2].split()))

    @cache
    def partial(self, n):
        factors = []
        for p in KNOWN_FACTORS:
            while n % p == 0:
                factors.append(p)
                n //= p
        if n == 1:
            return factors, 1
        try:
            return factors + self.full(n, self.timeout), 1
        except TimeoutExpired:
            for p in TRIAL_PRIMES:
                if p*p > n:
                    if n > 1:
                        factors.append(n)
                    return factors, 1
                while n % p == 0:
                    factors.append(p)
                    n //= p
            return factors, n

    def residual_groups(self, n, path):
        # Distinct component sums often reveal coprime blocks of a large K long
        # before a general-purpose factorer can split K in the aggregate.
        blocks = [n] if n > 1 else []
        for p, e in path:
            geom = (p**(e+1) - 1) // (p-1)
            new_blocks = []
            for block in blocks:
                outside = block
                while (common := gcd(outside, geom)) > 1:
                    outside //= common
                if outside > 1:
                    new_blocks.append(outside)
                if outside < block:
                    new_blocks.append(block // outside)
            blocks = new_blocks
        primes = []
        groups = []
        for block in blocks:
            known, rest = self.partial(block)
            primes.extend(known)
            groups.extend(set(known))
            if rest > 1:
                groups.append(rest)
        return primes, sorted(groups)

    def prime_proof(self, p):
        if p < 1024:
            return 'by norm_num'
        witnesses = []
        seen = set()

        def visit(n):
            if n < 1024 or n in seen:
                return
            seen.add(n)
            factors = sorted(set(self.full(n - 1)))
            root = next(a for a in range(2, n)
                        if all(pow(a, (n - 1) // q, n) != 1 for q in factors))
            witnesses.append(f'.lucas {{ root := {root}, primeFactors := {factors} }}')
            for q in factors:
                visit(q)

        visit(p)
        return 'by primality (cert := .witnesses [' + ', '.join(witnesses) + '])'


@dataclass
class Tree:
    seed: int
    budget: int
    min_distinct: int
    factors: Factorer
    cutoffs: bool = False
    hints: dict = field(default_factory=dict)
    primes: set = field(default_factory=set)
    unresolved: list = field(default_factory=list)
    counts: Counter = field(default_factory=Counter)

    @property
    def avoid(self):
        return 3 if self.cutoffs and self.seed == 5 else 1

    def possible_small_primes(self, bound, component):
        return [p for p in range(3, bound, 2) if self.avoid % p and component % p
                and all(p % d for d in range(2, isqrt(p) + 1))]

    def abundancy_cut(self, path, component, divisor_sum, spent, residual, bypass):
        k = (self.budget + 1 - spent - spent % 2) // 2
        if k < 1 or divisor_sum >= 2 * component:
            return False

        def use_cut(a, large, witness):
            if divisor_sum * large * a**(k-1) > 2*component*(large-1)*(a-1)**(k-1):
                return False
            candidates = self.possible_small_primes(a, component)
            self.hints[component] = path, f'.cut {a} {large} {witness}'
            self.counts['cut'] += 1
            for p in candidates:
                self.descend(path, component, divisor_sum, spent, p)
            return True

        # A prime dividing this witness is at least `large`. The subgroup of
        # small primes already removed from D can be tested without factoring K.
        smallest = next(p for p in count(3, 2) if self.avoid % p and component % p
                        and all(p % q for q in range(2, isqrt(p)+1)))
        for large in ((257,) if bypass else (7, 13, 31, 101, 257)):
            witness = residual
            mask = factorial(large - 1)
            while (common := gcd(witness, mask)) > 1:
                witness //= common
            for a in (range(3, 501) if bypass else (smallest,)):
                threshold = large if witness > 1 else a
                if use_cut(a, threshold, witness):
                    return True
        return False

    def descend(self, path, component, divisor_sum, spent, p):
        for e in range(1, self.budget - spent + 1):
            geom = (p**(e+1)-1) // (p-1)
            self.visit((*path, (p,e)), component * p**e, divisor_sum * geom, spent + e)

    def visit(self, path=(), component=1, divisor_sum=1, spent=0):
        self.counts['nodes'] += 1
        residual = divisor_sum // gcd(divisor_sum, 2 * component)
        gap = 2 * component - divisor_sum
        missing = max(0, self.min_distinct - len(path))

        def over_budget(k):
            return spent + 2 * max(k, missing) + spent % 2 > self.budget + 1

        if (divisor_sum % 4 == 0 or gap < 0 or gcd(component, residual) > 1
                or (spent + 1 >= self.budget and gap > 0 and divisor_sum % gap != 0)
                or over_budget(0)):
            self.counts['automatic'] += 1
            return

        if gcd(self.avoid, component * residual) > 1:
            self.counts['forbidden'] += 1
            return
        if self.cutoffs and self.abundancy_cut(path, component, divisor_sum, spent, residual, False):
            return
        if self.cutoffs:
            primes, groups = self.factors.residual_groups(residual, path)
        else:
            primes, remainder = self.factors.partial(residual)
            groups = sorted(set(primes)) + ([remainder] if remainder > 1 else [])
        if over_budget(len(groups)):
            while over_budget(len(groups) - 1):
                groups.pop()
            if residual % prod(groups) != 0 or any(
                    q <= 1 or gcd(q, prod(groups[:i])) != 1 for i, q in enumerate(groups)):
                raise ValueError(f'Invalid group proposal at {path}')
            self.hints[component] = path, f'.groups {groups}'
            self.counts['groups'] += 1
            return

        if not path:
            p = self.seed
        elif primes:
            p = min(primes)
        else:
            if self.cutoffs and self.abundancy_cut(path, component, divisor_sum, spent, residual, True):
                return
            self.unresolved.append((path, residual))
            return
        self.hints[component] = path, f'.split {p}'
        self.primes.add(p)
        self.counts['split'] += 1
        self.descend(path, component, divisor_sum, spent, p)

    def table(self):
        def balanced(items, indent):
            if not items:
                return '.empty'
            i = len(items) // 2
            component, (path, action) = items[i]
            if self.cutoffs and not action.startswith('.cut '):
                action = f'.basic ({action})'
            head = f'(.node {component} ({action})'
            if len(items) == 1:
                return head + ' .empty .empty)'
            desc = ' * '.join(str(p) if e == 1 else f'{p}^{e}' for p, e in path) or '1'
            sep = '\n' + ' ' * (indent + 2)
            return (head + ' -- ' + desc + sep + balanced(items[:i], indent + 2)
                    + sep + balanced(items[i+1:], indent + 2) + ')')

        typ = 'ChoiceTree' if self.cutoffs else 'HintTree'
        return (f'private def seed{self.seed}Tree : {typ} :=\n  '
                + balanced(sorted(self.hints.items()), 2) + '\n')

    def replay(self):
        p, b, w = self.seed, self.budget, self.min_distinct
        lookup = f'(fun n => seed{p}Tree.lookup n)'
        if self.cutoffs:
            goal = f'replayPlan (prepareChoices splitPrimes {lookup} {p} {self.avoid} {b} {w}) {b} {w} {b+1} root'
            assumption = ' (h3 : ¬ 3 ∣ N)' if self.avoid == 3 else ''
            coprime = '(Nat.prime_three.coprime_iff_not_dvd.mpr h3)' if self.avoid == 3 else '(Nat.coprime_one_left N)'
            return f'''private theorem seed{p}Check : {goal} = true := by
  decide +kernel

theorem exclude_{p}_budget_{b} {{N : ℕ}} (H : Conditions N {b} {w}){assumption} (hseed : {p} ∣ N) : False :=
  exclude_of_choice_certificate H hseed {coprime} splitPrimes prime_proofs {lookup} seed{p}Check
'''
        return f'''private theorem seed{p}Check : certify splitPrimes {lookup} {p} {b} {w} {b+1} root = true := by
  decide +kernel

theorem exclude_{p}_budget_{b} {{N : ℕ}} (H : Conditions N {b} {w}) (hseed : {p} ∣ N) : False :=
  certify_correct H hseed splitPrimes prime_proofs {lookup} {b+1} (root_realizes N) seed{p}Check
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('budget', type=int)
    parser.add_argument('--output', type=Path, help='write a Lean module if every path closes')
    parser.add_argument('--cutoffs', action='store_true', help='use conditional small-prime branches')
    parser.add_argument('--factor-seconds', type=float, default=0.4)
    args = parser.parse_args()
    if args.budget < 1 or args.factor_seconds <= 0:
        parser.error('budget and factor-seconds must be positive')
    factorer = Factorer(args.factor_seconds)
    trees = [Tree(seed, args.budget, w, factorer, args.cutoffs) for seed, w in [(3, 5), (5, 8)]]
    for tree in trees:
        tree.visit()
        print(f'seed {tree.seed}, {dict(tree.counts)}, open {len(tree.unresolved)}', flush=True)
        for path, k in tree.unresolved:
            print(f'  {path}, residual divisor {k}', flush=True)
    if any(t.unresolved for t in trees):
        raise SystemExit(1)
    if not args.output:
        return
    primes = sorted(set.union(*(t.primes for t in trees)))
    proofs = ',\n    '.join(factorer.prime_proof(p) for p in primes)
    sections = ['''module

public import OddPerfect.CountChain
import Mathlib.Tactic.Primality

/-! Replay data for the exact-exponent factor-count certificates. -/

public section

namespace OddPerfect.FactorBudget

set_option maxHeartbeats 0
set_option maxRecDepth 100000''',
                f'private def splitPrimes : List ℕ := {primes}',
                'private theorem prime_proofs : ∀ p ∈ splitPrimes, p.Prime := by\n'
                f'  simp only [splitPrimes, List.forall_mem_cons]\n  exact ⟨{proofs}, by simp⟩',
                *(t.table().rstrip() for t in trees),
                *(t.replay().rstrip() for t in trees), 'end OddPerfect.FactorBudget\n']
    if args.cutoffs:
        sections[0] = sections[0].replace('import OddPerfect.CountChain', 'import OddPerfect.ChainPlan')
    args.output.write_text('\n\n'.join(sections))


if __name__ == '__main__':
    main()
