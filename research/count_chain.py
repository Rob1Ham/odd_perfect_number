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
    # Divisors recovered from the numeric literals in Brent–Cohen–te Riele’s
    # published 1991 proof tree. The generator checks division at each use.
    18013, 37871, 54151, 55829, 130873, 331937, 375707, 504527, 1489303,
    308804117, 911193301, 30982393921, 45712301287, 687183137093, 17342847747419,
    496833428679257, 46434088032473231, 94355327820089003, 10736056226838183421,
    73080068123622666931553, 3772162179805889112204931, 12614694253451600922931463,
    # Three small prime divisors of Φ₅(1247451159302262598804596798564656994853573).
    # FactorDB entry 1100000000293441960 gives the complete factorization.
    32831761, 66613372141, 16551583277371,
)


def prime_candidates(bound):
    return [p for p in range(2, bound) if all(p % q for q in range(2, isqrt(p)+1))]


TRIAL_PRIMES = prime_candidates(10001)


@cache
def probable_prime(n):
    """Propose a prime for the later certificate, independently of the factor subprocess timeout."""
    if n < 2:
        return False
    d = n - 1
    twos = 0
    while d % 2 == 0:
        d //= 2
        twos += 1
    for a in (2, 3, 5, 7, 11, 13, 17):
        if n == a:
            return True
        if n % a == 0:
            return False
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(twos - 1):
            x = x*x % n
            if x == n - 1:
                break
        else:
            return False
    return True


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
        if probable_prime(n):
            return factors + [n], 1
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
            if probable_prime(n):
                return factors + [n], 1
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
    tight: bool = False
    compact: bool = False
    hints: dict = field(default_factory=dict)
    primes: set = field(default_factory=set)
    unresolved: list = field(default_factory=list)
    counts: Counter = field(default_factory=Counter)

    @property
    def avoid(self):
        return {3: 1, 5: 3, 7: 15, 11: 105}[self.seed] if self.cutoffs else 1

    @property
    def count_constant(self):
        return 15 if self.avoid % 3 == 0 else 31

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
            for a in (range(3, 4001) if bypass else (smallest,)):
                threshold = max(large, a) if witness > 1 else a
                if use_cut(a, threshold, witness if threshold > a else 1):
                    return True
        return False

    def exponents(self, component, spent, p):
        return range(1, self.budget - spent + 1)

    def descend(self, path, component, divisor_sum, spent, p):
        for e in self.exponents(component, spent, p):
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
        def closes(subset):
            if over_budget(len(subset)):
                return True
            if not self.tight:
                return False
            global_count = 18*(len(path) + len(subset)) > 7*self.budget + self.count_constant
            abundant = divisor_sum*prod(q+1 for q in subset) > 2*component*prod(subset)
            return global_count or abundant

        if closes(groups):
            while groups and closes(groups[:-1]):
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
        sections = []

        def emit(items, name):
            if len(items) <= 512:
                value = balanced(items, 2)
            else:
                middle = len(items) // 2
                component, (_, action) = items[middle]
                left_name = name + 'L'
                right_name = name + 'R'
                emit(items[:middle], left_name)
                emit(items[middle+1:], right_name)
                if self.cutoffs and not action.startswith('.cut '):
                    action = f'.basic ({action})'
                value = f'.node {component} ({action}) {left_name} {right_name}'
            sections.append(f'private def {name} : {typ} :=\n  {value}')

        emit(sorted(self.hints.items()), f'seed{self.seed}Tree')
        return '\n\n'.join(sections) + '\n'


    def script(self, root=1, blocked=frozenset(), label=None):
        label = label or f'seed{self.seed}Script'
        # Local indices identify children without repeatedly storing D in the
        # witness text. The independent verifier recomputes every omitted case.
        data = {}

        def collect(d, spent):
            if d in data:
                return data[d][2]
            _, action = self.hints[d]
            if action.startswith('.split '):
                ps = [int(action.split()[1])]
            elif action.startswith('.cut '):
                ps = self.possible_small_primes(int(action.split()[1]), d)
            else:
                ps = []
            children = []
            size = 1
            for i, p in enumerate(ps):
                for e in self.exponents(d, spent, p):
                    child = d*p**e
                    if child in self.hints and child not in blocked:
                        children.append((i*(self.budget+1)+e, child))
                        size += collect(child, spent+e)
            data[d] = action, children, size
            return size

        if root not in self.hints:
            return f'private noncomputable def {label} : Script := .automatic\n'
        collect(root, sum(e for _, e in self.hints[root][0]))
        sections = []
        declared = {}

        def render(d, indent, allowance):
            action, children, size = data[d]
            if size > allowance and d != root:
                if d not in declared:
                    name = f'{label}Part{len(declared)+1}'
                    declared[d] = name
                    path, _ = self.hints[d]
                    desc = ' * '.join(str(p) if e == 1 else f'{p}^{e}' for p, e in path)
                    block = render_body(d, 2)
                    sections.append(f'-- Exact component {desc}.\nprivate noncomputable def {name} : Script :=\n  {block}')
                return declared[d]
            return render_body(d, indent)

        def render_body(d, indent):
            action, children, _ = data[d]
            if action.startswith('.groups '):
                return action
            if not children:
                return action + ' []'
            quota = max(1, 256 // len(children))
            chunks = [f'({key}, {render(child, indent+2, quota)})' for key, child in children]
            sep = ',\n' + ' '*(indent+2)
            return action + ' [\n' + ' '*(indent+2) + sep.join(chunks) + ']'

        body = render_body(root, 2)
        sections.append(f'private noncomputable def {label} : Script :=\n  {body}')
        return '\n\n'.join(sections) + '\n'

    def replay(self):
        p, b, w = self.seed, self.budget, self.min_distinct
        lookup = f'(fun n => seed{p}Tree.lookup n)'
        if self.cutoffs:
            prepare = 'prepareTightChoices' if self.tight else 'prepareChoices'
            const = f' {self.count_constant}' if self.tight else ''
            goal = f'replayPlan ({prepare} splitPrimes {lookup} {p} {self.avoid} {b} {w}{const}) {b} {w} {b+1} root'
            excluded = [q for q in [3, 5, 7] if self.avoid % q == 0]
            assumptions = ''.join(f' (h{q} : ¬ {q} ∣ N)' for q in excluded)
            coprime = '(Nat.coprime_one_left N)'
            if excluded:
                proofs = [f'((by decide : Nat.Prime {q}).coprime_iff_not_dvd.mpr h{q})' for q in excluded]
                coprime = proofs[0]
                for proof in proofs[1:]:
                    coprime = f'({coprime}.mul_left {proof})'
            if self.tight:
                if self.compact:
                    goal = f'replayScript splitPrimes {p} {self.avoid} {b} {w} {self.count_constant} {b+1} root seed{p}Script'
                bound = '(ochem_rao_count_cases H.odd H.perfect).2 h3' if excluded else 'ochem_rao_prime_factor_count H.odd H.perfect'
                apply = (f'replayScript_correct H hseed {coprime} ?_ splitPrimes prime_proofs {b+1} (root_realizes N) seed{p}Script seed{p}Check'
                         if self.compact else f'exclude_of_tight_choice_certificate H hseed {coprime} ?_ splitPrimes prime_proofs {lookup} seed{p}Check')
                body = (f'by\n  apply {apply}\n'
                        f'  have := {bound}\n  have hu : N.primeFactorsList.length ≤ {b} := H.count\n  omega')
            else:
                body = f'\n  exclude_of_choice_certificate H hseed {coprime} splitPrimes prime_proofs {lookup} seed{p}Check'
            return f'''private theorem seed{p}Check : {goal} = true := by
  decide +kernel

theorem exclude_{p}_budget_{b} {{N : ℕ}} (H : Conditions N {b} {w}){assumptions} (hseed : {p} ∣ N) : False := {body}
'''

        return f'''private theorem seed{p}Check : certify splitPrimes {lookup} {p} {b} {w} {b+1} root = true := by
  decide +kernel

theorem exclude_{p}_budget_{b} {{N : ℕ}} (H : Conditions N {b} {w}) (hseed : {p} ∣ N) : False :=
  certify_correct H hseed splitPrimes prime_proofs {lookup} {b+1} (root_realizes N) seed{p}Check
'''


def floor_log(base, n):
    e = 0
    while n >= base:
        n //= base
        e += 1
    return e


@dataclass
class SizeTree(Tree):
    limit: int = 1
    min_count: int = 37

    def exponents(self, component, spent, p):
        return range(1, min(self.budget-spent, floor_log(p, self.limit//component))+1)

    def visit(self, path=(), component=1, divisor_sum=1, spent=0):
        forced = divisor_sum // gcd(divisor_sum, 2*component)
        floor = next(iter(self.possible_small_primes(43, component)), 43)
        if (component*forced > self.limit or
                component*floor**max(0, self.min_count-spent) > self.limit):
            self.counts['size'] += 1
            return
        parent_budget = self.budget
        self.budget = spent + floor_log(floor, self.limit//component)
        try:
            super().visit(path, component, divisor_sum, spent)
        finally:
            self.budget = parent_budget

    def replay(self):
        p, w, c = self.seed, self.min_distinct, self.count_constant
        exponent = len(str(self.limit))-1
        fuel = self.budget+1
        modulus = self.avoid
        excluded = [q for q in [3, 5, 7] if modulus % q == 0]
        assumptions = ''.join(f' (h{q} : ¬ {q} ∣ N)' for q in excluded)
        coprime = '(Nat.coprime_one_left N)'
        if excluded:
            proofs = [f'((by decide : Nat.Prime {q}).coprime_iff_not_dvd.mpr h{q})' for q in excluded]
            coprime = proofs[0]
            for proof in proofs[1:]:
                coprime = f'({coprime}.mul_left {proof})'
        count = '(ochem_rao_count_cases ho hN).2 h3' if excluded else 'ochem_rao_prime_factor_count ho hN'
        return f'''private theorem seed{p}Check :
    replaySize splitPrimes {p} {modulus} (10^{exponent}) {w} {c} {self.min_count} {fuel} {fuel} root seed{p}Script = true := by
  decide +kernel

theorem exclude_{p}_size_{exponent} {{N : ℕ}} (ho : Odd N) (hN : N.Perfect) (hw : {w} ≤ N.primeFactors.card)
    (hsize : N ≤ 10^{exponent}) (hlow : {self.min_count} ≤ N.primeFactorsList.length){assumptions} (hseed : {p} ∣ N) : False :=
  replaySize_correct ho hN hw hseed {coprime} hsize ({count}) hlow splitPrimes prime_proofs {fuel}
    (root_realizes N) seed{p}Script seed{p}Check
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('budget', type=int)
    parser.add_argument('--size', action='store_true', help='interpret the number as a decimal exponent for an absolute size bound')
    parser.add_argument('--min-count', type=int, default=37, help='minimum total factor count for size searches')
    parser.add_argument('--output', type=Path, help='write a Lean module if every path closes')
    parser.add_argument('--partition', action='store_true', help='emit bounded independent exact-exponent modules')
    parser.add_argument('--compact', action='store_true', help='key each child by its local branch number')
    parser.add_argument('--tight', action='store_true', help='use sharper residual group and count cutoffs')
    parser.add_argument('--cutoffs', action='store_true', help='use conditional small-prime branches')
    parser.add_argument('--factor-seconds', type=float, default=0.4)
    args = parser.parse_args()
    if args.budget < 1 or args.factor_seconds <= 0:
        parser.error('budget and factor-seconds must be positive')
    factorer = Factorer(args.factor_seconds)
    args.compact = args.compact or args.size or args.partition
    args.tight = args.tight or args.compact
    args.cutoffs = args.cutoffs or args.tight
    seeds = [(3, 5), (5, 8)]
    if args.cutoffs and args.budget >= 37:
        seeds.append((7, 15))
    if args.cutoffs and args.budget >= 69:
        seeds.append((11, 27))
    trees = [Tree(seed, args.budget, w, factorer, args.cutoffs, args.tight, args.compact) for seed, w in seeds]
    if args.size:
        if args.budget > 180:
            parser.error('the proved four-seed size complement suffices up to 180 decimal powers')
        seeds = [(3,5), (5,8)]
        if args.budget > 47:
            seeds.append((7,15))
        if args.budget > 106:
            seeds.append((11,27))
        limit = 10**args.budget
        trees = [SizeTree(p, floor_log(p, limit), w, factorer, True, True, True,
                          limit=limit, min_count=args.min_count) for p, w in seeds]
    for tree in trees:
        tree.visit()
        print(f'seed {tree.seed}, {dict(tree.counts)}, open {len(tree.unresolved)}', flush=True)
        for path, k in tree.unresolved:
            print(f'  {path}, residual divisor {k}', flush=True)
    if any(t.unresolved for t in trees):
        raise SystemExit(1)
    if not args.output:
        return
    if args.partition:
        if args.size:
            parser.error('partitioned replay currently applies to count budgets')
        from partition_chain import emit_partition
        emit_partition(trees, factorer, args.output)
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
                f'private {"noncomputable " if args.compact else ""}def splitPrimes : List ℕ := {primes}',
                'private theorem prime_proofs : ∀ p ∈ splitPrimes, p.Prime := by\n'
                f'  simp only [splitPrimes, List.forall_mem_cons]\n  exact ⟨{proofs}, by simp⟩',
                *((t.script() if args.compact else t.table()).rstrip() for t in trees),
                *(t.replay().rstrip() for t in trees), 'end OddPerfect.FactorBudget\n']
    if args.cutoffs:
        module = 'SizeChain' if args.size else 'ChainScript' if args.compact else 'ChainGroupBounds' if args.tight else 'ChainPlan'
        sections[0] = sections[0].replace('import OddPerfect.CountChain', 'import OddPerfect.' + module)
    args.output.write_text('\n\n'.join(sections))


if __name__ == '__main__':
    main()
