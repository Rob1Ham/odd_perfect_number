#!/usr/bin/env python3
"""Generate prime-index size certificates using a local copy of Brent's factor-tree supplement."""

import argparse
from bisect import bisect_left, bisect_right
from collections import Counter, defaultdict
from functools import cache
import gzip
from math import gcd, lcm, prod
from pathlib import Path
import re

from count_chain import Factorer, TRIAL_PRIMES, probable_prime


SEEDS = (127, 19, 7, 11, 31, 13, 3, 5)


class FactorTable:
    def __init__(self, path, timeout, extra_tables=(), power_table=None):
        candidates = set()
        for table in (path, *extra_tables):
            source = gzip.decompress(table.read_bytes()) if table.suffix == '.gz' else table.read_bytes()
            candidates.update(n for v in re.findall(rb'\d{5,}', source) if (n := int(v)) > 1)
        self.table = self.product_tree(sorted(candidates))
        self.factorer = Factorer(timeout)
        self.power_factors = defaultdict(list)
        if power_table:
            prime_lengths = set(TRIAL_PRIMES)
            opener = gzip.open if power_table.suffix == '.gz' else open
            with opener(power_table, 'rt') as table:
                for line in table:
                    base, power, value = line.split()
                    length = 2 if power == '1+' else int(power[:-1])
                    if (power.endswith('-') or power == '1+') and length in prime_lengths:
                        self.power_factors[int(base), length].append(int(value))

    @cache
    def geom_factors(self, base, length, geom):
        result = set()
        for factor in self.power_factors.get((base, length), ()):
            if geom % factor == 0:
                result.update(self.factors(factor))
                while geom % factor == 0:
                    geom //= factor
        return result | self.factors(geom)

    @classmethod
    def product_tree(cls, values):
        if not values:
            raise ValueError('empty list of candidate divisors')
        if len(values) == 1:
            return values[0], None
        mid = len(values)//2
        left, right = cls.product_tree(values[:mid]), cls.product_tree(values[mid:])
        return left[0]*right[0], (left, right)

    @classmethod
    def matching_divisors(cls, node, n):
        value, children = node
        common = gcd(value, n)
        if common == 1:
            return
        if children is None:
            if n % value == 0:
                yield value
        else:
            for child in children:
                yield from cls.matching_divisors(child, common)

    @cache
    def factors(self, n):
        found, rem = self.factorer.partial(n)
        primes = set(found)
        if rem > 1:
            for p in sorted(set(self.matching_divisors(self.table, rem))):
                if p < rem and rem % p == 0:
                    factors, _ = self.factorer.partial(p)
                    primes.update(factors)
                    while rem % p == 0:
                        rem //= p
            if rem > 1:
                factors, leftover = self.factorer.partial(rem)
                primes.update(factors)
                # This only proposes a prime for the later Lucas proof.
                if probable_prime(leftover):
                    primes.add(leftover)
        primes.discard(2)
        return primes


def valuation(n, p):
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def allowance_for(pairs, special):
    if special:
        return 1
    return max((p for p, _ in pairs if p % 4 == 1), default=1)


def automatic(d, a, avoid, bound):
    u = lcm(d, a//gcd(a, 2))
    return u > bound or gcd(avoid, u) != 1 or a % 4 == 0 or a > 2*d


def rounded_factors(u, candidates, special, bound):
    pairs = [(p, v) for p in sorted(candidates) if p != special and (v := valuation(u, p)) % 2]

    def enough(subset):
        return bound*allowance_for(subset, special) < u*prod(p for p, _ in subset)

    if not enough(pairs):
        return None
    for pair in pairs[:]:
        trial = [x for x in pairs if x != pair]
        if enough(trial):
            pairs = trial
    return pairs


def exponent_cases(d, p, special, bound):
    for ell in TRIAL_PRIMES:
        e = ell-1
        if d*p**e > bound or (e > 1 and p**(2*e) >= bound):
            return
        if e != 1 or (p % 4 == 1 and not special):
            yield e, (p**ell-1)//(p-1)
    raise ValueError('prime-length enumeration does not cover the requested size')


def abundant_factors(u, special, primes):
    pairs = []
    d, a = 1, 1
    for p in primes:
        if u % p:
            continue
        e = valuation(u, p)
        if e % 2 and p != special and (special or p % 4 == 3):
            e += 1
        pairs.append((p, e))
        d *= p**e
        a *= (p**(e+1)-1)//(p-1)
        if a > 2*d:
            break
    else:
        return None
    # Retain only the factors needed by the strict abundancy inequality.
    for p, e in reversed(pairs[:]):
        geom = (p**(e+1)-1)//(p-1)
        if a//geom > 2*(d//p**e):
            pairs.remove((p, e))
            d //= p**e
            a //= geom
    return pairs


def prune_abundant(tree, primes, d=1, a=1, special=0):
    """Add a partial-abundancy proof wherever it replaces an existing subtree."""
    pairs = abundant_factors(lcm(d, a//gcd(a, 2)), special, primes)
    if pairs:
        return 'abundant', pairs
    if tree[0] != 'split':
        return tree
    _, p, cases = tree
    return 'split', p, [(e, prune_abundant(child, primes, d*p**e, a*((p**(e+1)-1)//(p-1)),
                                           p if e == 1 else special)) for e, child in cases]


def discover(seed, avoid, bound, factors, small_primes=()):
    stats, primes, missing = Counter(), set(), []

    def visit(d, a, must, special):
        stats['nodes'] += 1
        u = lcm(d, a//gcd(a, 2))
        if automatic(d, a, avoid, bound):
            stats['automatic'] += 1
            return None
        abundant = abundant_factors(u, special, small_primes)
        if abundant:
            primes.update(p for p, _ in abundant)
            stats['abundant'] += 1
            return 'abundant', abundant
        pairs = rounded_factors(u, must, special, bound)
        if pairs is not None:
            primes.update(p for p, _ in pairs)
            stats['round'] += 1
            return 'round', pairs
        available = [p for p in must if d % p != 0]
        if not available:
            missing.append((d, a, u))
            return None
        p = max(available)
        primes.add(p)
        stats['split'] += 1
        children = []
        for e, geom in exponent_cases(d, p, special, bound):
            next_d, next_a = d*p**e, a*geom
            if automatic(next_d, next_a, avoid, bound):
                continue
            child = visit(next_d, next_a, must | factors.geom_factors(p, e+1, geom), p if e == 1 else special)
            if child:
                children.append((e, child))
        return 'split', p, children

    tree = visit(1, 1, {seed}, None)
    return tree, primes, missing, stats


def primes_used(tree):
    if tree is None:
        return set()
    if tree[0] in ('round', 'abundant'):
        return {p for p, _ in tree[1]}
    return {tree[1]}.union(*(primes_used(child) for _, child in tree[2]))


def load_prime_leaves(directory):
    """Read exactly the leaf groups named by this bank, including named leaves from an earlier bank."""
    bank = (directory/'Bank.lean').read_text()
    namespace = re.search(r'^namespace ([\w.]+)$', bank, re.M).group(1)
    definition = bank.split('def bank : PrimeBank :=', 1)[1].split('theorem bank_valid', 1)[0]
    names = re.findall(r'\b(?:[\w.]+\.)?bankLeaf\d+\b', definition)
    leaves, imports = {}, set()
    leaf_block = re.compile(r'def (bankLeaf\d+) : PrimeBank := \.leaf \[([0-9, ]+)\].*?'
                            r'  exact ⟨(.*?), by simp⟩$', re.S | re.M)
    for file in sorted(directory.glob('Primes*.lean')):
        source = file.read_text()
        imports.update(re.findall(r'^public import OddPerfect\.(\w+)\.Bank$', source, re.M))
        for name, values, witnesses in leaf_block.findall(source):
            leaves[namespace+'.'+name] = dict(zip(map(int, values.split(',')),
                                                  witnesses.split(',\n    '), strict=True))
    imports.update(re.findall(r'^public import OddPerfect\.(\w+)\.Bank$', bank, re.M))
    if any('.' in name for name in names):
        for imported in imports:
            leaves.update(load_prime_leaves(directory.parent/imported))
    if not names:
        raise ValueError(f'no prime witness blocks in {directory}')
    qualified = [name if '.' in name else namespace+'.'+name for name in names]
    return {name: leaves[name] for name in qualified}


def load_prime_witnesses(directory):
    """Read the separate prime witnesses already shipped with a Lean certificate."""
    proofs = {p: proof for group in load_prime_leaves(directory).values() for p, proof in group.items()}
    references = {p for p, proof in proofs.items() if re.match(r'^[\w.]+\.bank\.prime_of_contains ', proof)}
    if references:
        imports = set()
        for source in [directory/'Bank.lean', *directory.glob('Primes*.lean')]:
            imports.update(re.findall(r'^public import OddPerfect\.(\w+)\.Bank$', source.read_text(), re.M))
        for package in imports:
            previous = load_prime_witnesses(directory.parent/package)
            recovered = references.intersection(previous)
            proofs.update((p, previous[p]) for p in recovered)
            references.difference_update(recovered)
        if references:
            raise ValueError(f'missing source for {len(references)} imported prime witnesses in {directory}')
    return proofs


def bank_groups(primes, reference_leaves):
    """Use a whole verified leaf whenever no required new number falls within its numeric interval."""
    groups, pending, cursor = [], [], 0

    def flush():
        groups.extend((pending[i:i+16], None) for i in range(0, len(pending), 16))
        pending.clear()

    for name, entries in reference_leaves.items():
        values = sorted(entries)
        left, right = bisect_left(primes, values[0]), bisect_right(primes, values[-1])
        pending.extend(primes[cursor:left])
        inside = primes[left:right]
        if inside and all(p in entries for p in inside):
            flush()
            groups.append((values, name))
        else:
            pending.extend(inside)
        cursor = right
    pending.extend(primes[cursor:])
    flush()
    return groups


def repair_witnesses(tree, avoid, bound, available, small_primes=()):
    """Replace an unavailable primality witness by a finite subtree on other forced primes."""
    bank = FactorTable.product_tree(sorted(available))
    failed = object()
    small_primes = tuple(p for p in small_primes if p in available)

    @cache
    def rebuild(d, a, special, depth):
        if automatic(d, a, avoid, bound):
            return None
        u = lcm(d, a//gcd(a, 2))
        abundant = abundant_factors(u, special, small_primes)
        if abundant:
            return 'abundant', abundant
        candidates = sorted(FactorTable.matching_divisors(bank, u), reverse=True)
        pairs = rounded_factors(u, candidates, special, bound)
        if pairs is not None:
            return 'round', pairs
        if depth == 0:
            return failed
        for p in candidates:
            if d % p == 0:
                continue
            children = []
            for e, geom in exponent_cases(d, p, special, bound):
                result = rebuild(d*p**e, a*geom, p if e == 1 else special, depth-1)
                if result is failed:
                    break
                if result is not None:
                    children.append((e, result))
            else:
                return 'split', p, children
        return failed

    def visit(t, d, a, special):
        if t is None:
            return None
        if t[0] in ('round', 'abundant') and all(p in available for p, _ in t[1]):
            return t
        if t[0] == 'split' and t[1] in available:
            _, p, cases = t
            children = []
            for e, child in cases:
                geom = (p**(e+1)-1)//(p-1)
                result = visit(child, d*p**e, a*geom, p if e == 1 else special)
                if result is failed:
                    break
                if result is not None:
                    children.append((e, result))
            else:
                return 'split', p, children
        for depth in range(1, 6):
            result = rebuild(d, a, special, depth)
            if result is not failed:
                return result
        return failed

    result = visit(tree, 1, 1, 0)
    if result is failed:
        raise ValueError('the available prime witnesses leave an open subtree')
    return result


def tree_depth(tree):
    if tree is None or tree[0] != 'split':
        return 1
    return 1 + max((tree_depth(child) for _, child in tree[2]), default=0)


def render_tree(tree, special=0, indent=2):
    if tree is None:
        return '.automatic'
    if tree[0] == 'abundant':
        return f'.abundant {tree[1]}'
    if tree[0] == 'round':
        pairs = tree[1]
        return f'.round {allowance_for(pairs, special)} {pairs}'
    _, p, children = tree
    if not children:
        return f'.split {p} []'
    sep = ',\n' + ' '*(indent+2)
    cases = [f'({e}, {render_tree(child, p if e == 1 else special, indent+2)})' for e, child in children]
    return f'.split {p} [\n' + ' '*(indent+2) + sep.join(cases) + ']'


def partition_blocks(tree, seed, avoid, exponent, node_limit, abundance=False):
    """Join small replay theorems by the three numeric state fields at their root."""
    number = 0
    blocks = []
    context = (f'{{N : ℕ}} (ho : Odd N) (hN : N.Perfect) (hs : {seed} ∣ N)\n'
               f'    (hav : Nat.Coprime {avoid} N) (hx : N ≤ 10^{exponent})')

    replay = 'replayAbundance' if abundance else 'replay'
    tree_type = 'AbundanceTree' if abundance else 'ProofTree'

    def weight(t):
        return 1 if t[0] != 'split' else 1+sum(weight(child) for _, child in t[2])

    def add(t, d, a, special):
        nonlocal number
        large = weight(t) > node_limit
        children = []
        if large:
            _, p, cases = t
            for e, child in cases:
                geom = (p**(e+1)-1)//(p-1)
                children.append(add(child, d*p**e, a*geom, p if e == 1 else special))
        number += 1
        label = f'{seed}_{number}'
        state = 'state'+label
        head = f'@[expose] noncomputable def {state} : State := ⟨{d}, {a}, {special}⟩'
        theorem = f'theorem reject{label} {context} (h : Valid {state} N) : False :='
        if large:
            states = '[' + ', '.join('state'+i for i in children) + ']'
            test = f'checkChildren bank {seed} {avoid} (10^{exponent}) {state} {t[1]} {states}'
            check = f'private theorem checked{label} : {test} = true := by\n  decide +kernel'
            cases = ' | '.join('rfl' for _ in children)
            body = (f' by\n  apply checkChildren_correct ho hN hs hav hx bank bank_valid h {states} ?_ checked{label}\n'
                    '  intro t ht hvalid\n  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht\n'
                    f'  rcases ht with {cases}\n' +
                    '\n'.join(f'  · exact reject{i} ho hN hs hav hx hvalid' for i in children))
            block = '\n\n'.join((head,check,theorem+body))
        else:
            fuel = tree_depth(t)+2
            witness = f'private noncomputable def tree{label} : {tree_type} :=\n  {render_tree(t,special)}'
            test = f'{replay} bank {seed} {avoid} (10^{exponent}) {fuel} {state} tree{label}'
            check = f'private theorem checked{label} : {test} = true := by\n  decide +kernel'
            body = (f'\n  {replay}_correct ho hN hs hav hx bank bank_valid {fuel} h tree{label} checked{label}')
            block = '\n\n'.join((head,witness,check,theorem+body))
        blocks.append(block)
        return label

    root = add(tree, 1, 1, 0)
    wrapper = (f'theorem exclude_{seed} {context} : False :=\n'
               f'  reject{root} ho hN hs hav hx (root_valid N)')
    return blocks, wrapper


def write_certificate(data, exponent, prime_proof, output, chunk_nodes=None, abundance=False,
                      reference_bank=None, bank_only=False, reuse_leaves=False, prime_imports=()):
    package = output.stem
    directory = output.parent/package
    directory.mkdir(exist_ok=True)
    ns = f'OddPerfect.IndexComponent.{package}' if bank_only else f'OddPerfect.IndexComponent.Size{exponent}'
    previous = 'OddPerfect.PrimeBank' if bank_only else (
        'OddPerfect.IndexAbundantReplay' if abundance else 'OddPerfect.IndexReplay')
    replay = 'replayAbundance' if abundance else 'replay'
    tree_type = 'AbundanceTree' if abundance else 'ProofTree'
    reference_primes = set()
    reference_import = ''
    reference_name = ''
    reference_leaves = {}
    if reference_bank:
        source = (reference_bank/'Bank.lean').read_text()
        reference_name = re.search(r'^namespace ([\w.]+)$', source, re.M).group(1)
        reference_import = f'public import OddPerfect.{reference_bank.name}.Bank\n'
        reference_leaves = load_prime_leaves(reference_bank)
        reference_primes = {p for group in reference_leaves.values() for p in group}

    def write(name, blocks, imports=''):
        nonlocal previous
        src = (f'module\n\npublic import {previous}\n{imports}\npublic section\n\nnamespace {ns}\n\n'
               'set_option maxRecDepth 20000\nset_option maxHeartbeats 0\n\n' + '\n\n'.join(blocks)
               + f'\n\nend {ns}\n')
        (directory/f'{name}.lean').write_text(src)
        previous = f'OddPerfect.{package}.{name}'

    primes = sorted(set.union(*(ds[1] for ds in data.values())))
    leaves, blocks, bank_files = [], [], 0
    order_modules = {
        'OddPerfect.LargeOrderPrime': ('prime_of_largeOrderCheck',),
        'OddPerfect.LargeOrderCube': ('prime_of_largeOrderCubeCheck',),
        'OddPerfect.LargeOrderQuadratic': ('prime_of_largeOrderPlusCheck', 'prime_of_mixedOrderCheck'),
        'OddPerfect.EllipticPrime': ('prime_of_ellipticCheck', 'prime_of_ellipticTraceCheck'),
    }
    pending_prime_imports = list(prime_imports)
    groups = bank_groups(primes, reference_leaves if reuse_leaves else {})
    last_explicit = max((i for i, (_, named) in enumerate(groups) if named is None), default=-1)
    for i, (group, named) in enumerate(groups):
        if named:
            leaves.append((group[0], named))
            continue
        name = f'bankLeaf{i+1}'
        leaves.append((group[0], name))
        witnesses = ',\n    '.join(
            f'{reference_name}.bank.prime_of_contains {reference_name}.bank_valid (by decide +kernel)'
            if p in reference_primes else prime_proof(p) for p in group)
        blocks.append(f'@[expose] noncomputable def {name} : PrimeBank := .leaf {group}\n\n'
                      f'theorem {name}_valid : {name}.Certified := by\n'
                      f'  simp only [{name}, PrimeBank.Certified, List.forall_mem_cons]\n'
                      f'  exact ⟨{witnesses}, by simp⟩')
        if sum(map(len, blocks)) > 45000 or i == last_explicit:
            bank_files += 1
            imports = (reference_import if bank_files == 1 else '') + 'import Mathlib.Tactic.Primality\n'
            for module in list(pending_prime_imports):
                if any(module+'.' in block for block in blocks):
                    imports += f'public import {module}\n'
                    pending_prime_imports.remove(module)
            for mod, checkers in list(order_modules.items()):
                if any(checker in block for block in blocks for checker in checkers):
                    imports += f'public import {mod}\n'
                    del order_modules[mod]
            write(f'Primes{bank_files:02d}', blocks, imports)
            blocks = []

    def balanced(groups):
        if len(groups) == 1:
            return groups[0][1], groups[0][1]+'_valid'
        mid = len(groups)//2
        l, lp = balanced(groups[:mid])
        r, rp = balanced(groups[mid:])
        return f'(.branch {groups[mid][0]} {l} {r})', f'⟨{lp}, {rp}⟩'

    bank, valid = balanced(leaves)
    write('Bank', [f'@[expose] noncomputable def bank : PrimeBank :=\n  {bank}',
                   f'theorem bank_valid : bank.Certified :=\n  {valid}'],
          (reference_import if not bank_files else '') +
          ('public import OddPerfect.IndexCheckpoint\n' if chunk_nodes and not abundance else ''))
    if bank_only:
        output.write_text(f'module\n\npublic import {previous}\n')
        return
    avoid = 1
    for seed in SEEDS:
        tree = data[seed][0]
        if chunk_nodes:
            blocks, wrapper = partition_blocks(tree, seed, avoid, exponent, chunk_nodes, abundance)
            pending, part = [], 0
            for block in blocks:
                if pending and sum(map(len, pending))+len(block) > 65000:
                    part += 1
                    write(f'Seed{seed}Part{part:02d}', pending)
                    pending = []
                pending.append(block)
            write(f'Seed{seed}', [*pending, wrapper])
            avoid *= seed
            continue
        fuel = max(32, tree_depth(tree)+2)
        write(f'Seed{seed}', [f'private noncomputable def witness : {tree_type} :=\n  {render_tree(tree)}',
            f'private theorem checked : {replay} bank {seed} {avoid} (10^{exponent}) {fuel} root witness = true := by\n'
            '  decide +kernel',
            f'theorem exclude_{seed} {{N : ℕ}} (ho : Odd N) (hN : N.Perfect) (hs : {seed} ∣ N)\n'
            f'    (hav : Nat.Coprime {avoid} N) (hx : N ≤ 10^{exponent}) : False :=\n'
            f'  {replay}_correct ho hN hs hav hx bank bank_valid {fuel} (root_valid N) witness checked'])
        avoid *= seed
    output.write_text(f'module\n\npublic import {previous}\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('exponent', type=int)
    parser.add_argument('--table', type=Path, required=True, help='Brent–Cohen–te Riele TeX appendix, plain or gzipped')
    parser.add_argument('--extra-table', type=Path, action='append', default=[], help='additional factor tables, plain or gzipped')
    parser.add_argument('--power-table', type=Path, help='Brent’s tabulated factors of powers plus or minus one')
    parser.add_argument('--factor-seconds', type=float, default=0.05)
    parser.add_argument('--reuse-primes', type=Path, help='reuse the primality witnesses in this certificate directory')
    parser.add_argument('--prime-import', action='append', default=[], help='import a separate Lean module supplying named prime proofs')
    parser.add_argument('--reference-bank', type=Path, help='refer directly to prime proofs in this earlier certificate')
    parser.add_argument('--reuse-leaves', action='store_true', help='share entire ordered leaf groups from the reference bank')
    parser.add_argument('--small-abundance', type=int, default=0, help='use forced primes up to this bound for abundant-divisor leaves')
    parser.add_argument('--chunk-nodes', type=int, help='maximum explicit nodes per serial subtree proof')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.chunk_nodes is not None and args.chunk_nodes < 1:
        parser.error('--chunk-nodes must be positive')
    if args.reuse_leaves and not args.reference_bank:
        parser.error('--reuse-leaves needs --reference-bank')
    if args.exponent < 1 or args.factor_seconds <= 0:
        parser.error('use a positive decimal exponent and a positive factoring timeout')
    bank = FactorTable(args.table, args.factor_seconds, args.extra_table, args.power_table)
    small_primes = tuple(p for p in TRIAL_PRIMES if 2 < p <= args.small_abundance)
    witnesses = load_prime_witnesses(args.reuse_primes) if args.reuse_primes else None
    avoid, data = 1, {}
    for seed in SEEDS:
        data[seed] = discover(seed, avoid, 10**args.exponent, bank, small_primes)
        tree, primes, missing, stats = data[seed]
        if witnesses and not missing and not primes.issubset(witnesses):
            tree = repair_witnesses(tree, avoid, 10**args.exponent, witnesses, small_primes)
            primes = primes_used(tree)
            data[seed] = (tree, primes, missing, stats)
        print(f'{seed}: {dict(stats)}, {len(primes)} proposed primes, {len(missing)} open', flush=True)
        avoid *= seed
    if any(ds[2] for ds in data.values()):
        raise SystemExit('The proposed case tree has open branches.')
    if args.output:
        prime_proof = witnesses.__getitem__ if witnesses else bank.factorer.prime_proof
        write_certificate(data, args.exponent, prime_proof, args.output, args.chunk_nodes,
                          bool(small_primes), args.reference_bank, reuse_leaves=args.reuse_leaves,
                          prime_imports=args.prime_import)


if __name__ == '__main__':
    main()
