"""Emit independently checked exact-component subtrees for a factor-count proof."""

from collections import Counter, defaultdict
from functools import cache
from math import prod
from pathlib import Path


def emit_partition(trees, factorer, output, chunk_limit=450, module_bytes=90000,
                   frequent_primes_first=False, arithmetic_after=None, lanes=1, excess=None):
    budget = trees[0].budget
    package = output.stem
    prefix = f'OddPerfect.{package}'
    topic = f'Count{budget}' if excess is None else f'Excess{excess}'
    namespace = f'OddPerfect.FactorBudget.{topic}'
    if excess is not None and arithmetic_after != 0:
        raise ValueError('an excess certificate needs the arithmetic verifier at every node')
    directory = output.parent/package
    directory.mkdir(exist_ok=True)
    options = 'set_option maxHeartbeats 0\nset_option maxRecDepth 100000'

    def module(imports, blocks, ns=namespace):
        return (f'module\n\n{imports}\n\npublic section\n\nnamespace {ns}\n\n{options}\n\n'
                + '\n\n'.join(blocks) + f'\n\nend {ns}\n')

    def identifier(t, d):
        return f'S{t.seed}_{indices[t.seed, d]}'

    # Small independent primality theorems prevent a single long conjunction
    # from retaining every tactic invocation in one elaboration command.
    primes = sorted(set.union(*(t.primes for t in trees)))
    if frequent_primes_first:
        frequency = Counter(int(action.split()[1]) for t in trees for _, action in t.hints.values()
                            if action.startswith('.split '))
        primes.sort(key=lambda p: (-frequency[p], p))
    prime_blocks = []
    names = []
    for i in range(0, len(primes), 24):
        block = primes[i:i+24]
        name = f'primes{i//24+1}'
        names.append(name)
        proofs = ',\n    '.join(factorer.prime_proof(p) for p in block)
        prime_blocks.append(f'@[expose] noncomputable def {name} : List ℕ := {block}\n\n'
                            f'private theorem {name}_valid : ∀ p ∈ {name}, p.Prime := by\n'
                            f'  simp only [{name}, List.forall_mem_cons]\n  exact ⟨{proofs}, by simp⟩')
    prime_blocks.append('@[expose] noncomputable def splitPrimes : List ℕ :=\n  ' + ' ++ ('.join(names) + ')'*(len(names)-1))
    prime_blocks.append('theorem prime_proofs : ∀ p ∈ splitPrimes, p.Prime := by\n'
                        '  simp only [splitPrimes, List.forall_mem_append]\n  exact ⟨' +
                        ', '.join(f'{n}_valid' for n in names) + '⟩')
    imports = 'public import OddPerfect.ChainCheckpoint\nimport Mathlib.Tactic.Primality'
    for checker, name in [('prime_of_largeOrderCheck', 'LargeOrderPrime'),
                          ('prime_of_largeOrderCubeCheck', 'LargeOrderCube'),
                          ('prime_of_largeOrderPlusCheck', 'LargeOrderQuadratic'),
                          ('prime_of_mixedOrderCheck', 'LargeOrderQuadratic')]:
        if any(checker in block for block in prime_blocks) and f'OddPerfect.{name}' not in imports:
            imports += f'\npublic import OddPerfect.{name}'
    if sum(map(len, prime_blocks)) > module_bytes:
        groups, current, size = [], [], 0
        for block in prime_blocks[:-2]:
            if current and size+len(block) > module_bytes:
                groups.append(current)
                current, size = [], 0
            current.append(block.replace('private theorem ', 'theorem ', 1))
            size += len(block)
        groups.append(current)
        for i, group in enumerate(groups, 1):
            name = f'PrimePart{i:02d}'
            (directory/f'{name}.lean').write_text(module(imports, group))
            imports = f'public import {prefix}.{name}\nimport Mathlib.Tactic.Primality'
        prime_blocks = prime_blocks[-2:]
    (directory/'Primes.lean').write_text(module(imports, prime_blocks))
    previous = 'Primes'
    lane_tips = [previous] * lanes
    published = {}
    current_names, required = set(), set()
    power_groups = defaultdict(list)
    root_blocks = []
    active_lane = 0
    indices = {}
    sections = []
    sizes = []

    def is_arithmetic():
        return arithmetic_after is not None and len(sizes) >= arithmetic_after

    def flush():
        nonlocal previous, sections
        if not sections:
            return
        name = f'Part{len(sizes)+1:02d}'
        if is_arithmetic():
            lane = active_lane
            parents = {published[dep] for dep in required-current_names}
            parents.add(lane_tips[lane])
            imports = '\n'.join(f'public import {prefix}.{part}' for part in sorted(parents))
            if lane_tips[lane] == 'Primes' or lane_tips[lane] == f'Part{arithmetic_after:02d}':
                imports += '\npublic import OddPerfect.ChainWitness'
            lane_tips[lane] = name
        else:
            imports = f'public import {prefix}.{previous}'
            lane_tips[:] = [name] * lanes
        src = module(imports, sections)
        (directory/f'{name}.lean').write_text(src)
        sizes.append(len(src.encode()))
        published.update((item, name) for item in current_names)
        current_names.clear()
        required.clear()
        previous, sections = name, []

    wrappers = []
    for t in trees:
        B, w, seed, avoid, c = t.budget, t.min_distinct, t.seed, t.avoid, t.count_constant

        @cache
        def children(d):
            path, action = t.hints[d]
            spent = sum(e for _, e in path)
            if action.startswith('.split '):
                ps = [int(action.split()[1])]
            elif action.startswith('.cut '):
                ps = t.possible_small_primes(int(action.split()[1]), d)
            else:
                ps = []
            return tuple({d*p**e: None for p in ps for e in t.exponents(d, spent, p) if d*p**e in t.hints})

        @cache
        def weight(d):
            return 1+sum(weight(x) for x in children(d))

        starts = set()

        def partition(d):
            if d in starts:
                return
            starts.add(d)
            remaining = weight(d)
            for x in sorted(children(d), key=weight, reverse=True):
                if d != 1 and remaining <= chunk_limit:
                    break
                partition(x)
                remaining -= weight(x)

        partition(1)
        order = sorted(starts, reverse=True)
        for i, d in enumerate(order, 1):
            indices[t.seed, d] = i

        @cache
        def external(d):
            return frozenset().union(*(frozenset([x]) if x in starts else external(x) for x in children(d)))

        for d in order:
            name = identifier(t, d)
            path = t.hints[d][0]
            earlier = sorted(external(d), reverse=True)
            blocked = set(earlier)
            state = f'state{name}'
            geom = prod((p**(e+1)-1)//(p-1) for p, e in path)
            desc = ' * '.join(str(p) if e == 1 else f'{p}^{e}' for p, e in path) or '1'
            head = (f'-- Exact component {desc}.\n@[expose] def {state} : Node := '
                    f'⟨{d}, {geom}, {sum(e for _, e in path)}, {len(path)}⟩')
            dependencies = [identifier(t, x) for x in earlier]
            deps = '[' + ', '.join('state'+key for key in dependencies) + ']'

            def make_block(arithmetic):
                witness = t.script(d, blocked, f'tree{name}', arithmetic=arithmetic).rstrip()
                if arithmetic:
                    ver = f'replayArithmetic {deps}'
                    correct = 'replayArithmetic_correct' if excess is None else 'replayArithmetic_correct_of_offset'
                    start_path = f'{list(path)} '
                else:
                    ver = f'replayChunk {deps}' if earlier else 'replayScript'
                    correct = 'replayChunk_correct' if earlier else 'replayScript_correct'
                    start_path = ''
                args = f'splitPrimes {seed} {avoid} {B} {w} {c} {B+1} {start_path}{state} tree{name}'
                check = f'private theorem checked{name} : {ver} {args} = true := by\n  decide +kernel'
                actual = w if excess is None else 0
                offset = '' if excess is None else f' (hoff : 2*{w}+N.primeFactorsList.length ≤ {B}+2*N.primeFactors.card)'
                context = 'H' if excess is None else 'H hoff'
                theorem = (f'theorem reject{name} {{N m : ℕ}} (H : Conditions N {B} {actual}){offset} (hs : {seed} ∣ N)\n'
                           f'    (hav : Nat.Coprime {avoid} N) (hc : 18*N.primeFactors.card ≤ 7*{B}+{c})\n'
                           f'    (h : Realizes {state} N m) : False :=')
                rest = f'splitPrimes prime_proofs {B+1} {start_path}h tree{name} checked{name}'
                if earlier:
                    prior = ' | '.join('rfl' for _ in earlier)
                    branches = '\n'.join(f'  · exact reject{key} {context} hs hav hc hreal' for key in dependencies)
                    theorem += (f' by\n  apply {correct} {context} hs hav hc {deps} ?_ {rest}\n'
                                '  intro t ht m hreal\n  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht\n'
                                f'  rcases ht with {prior}\n' + branches)
                else:
                    arguments = '[] (by simp) ' if arithmetic else ''
                    theorem += f'\n  {correct} {context} hs hav hc {arguments}{rest}'
                return '\n\n'.join([head, witness, check, theorem])

            arithmetic = is_arithmetic()
            block = make_block(arithmetic)
            if not arithmetic and sections and sum(len(item.encode()) for item in sections)+len(block.encode()) > module_bytes:
                flush()
                if is_arithmetic() != arithmetic:
                    block = make_block(is_arithmetic())
            if is_arithmetic():
                entry = (name, dependencies, block)
                if path:
                    power_groups[seed, path[0][1]].append(entry)
                else:
                    root_blocks.append(entry)
            else:
                sections.append(block)
                current_names.add(name)
                required.update(dependencies)
        root = f'{topic}.reject{identifier(t,1)}'
        excluded = [p for p in (3,5,7) if avoid%p == 0]
        extra = ''.join(f' (h{p} : ¬ {p} ∣ N)' for p in excluded)
        coprime = '(Nat.coprime_one_left N)'
        if excluded:
            hs = [f'((by decide : Nat.Prime {p}).coprime_iff_not_dvd.mpr h{p})' for p in excluded]
            coprime = hs[0]
            for part in hs[1:]:
                coprime = f'({coprime}.mul_left {part})'
        bound = '(ochem_rao_count_cases H.odd H.perfect).2 h3' if excluded else 'ochem_rao_prime_factor_count H.odd H.perfect'
        if excess is None:
            wrappers.append(f'theorem exclude_{seed}_budget_{B} {{N : ℕ}} (H : Conditions N {B} {w}){extra}\n'
                            f'    (hs : {seed} ∣ N) : False := by\n  apply {root} H hs {coprime} ?_ (root_realizes N)\n'
                            f'  have := {bound}\n  have hu : N.primeFactorsList.length ≤ {B} := H.count\n  omega')
        else:
            relation = bound.replace('H.odd H.perfect', 'ho hN')
            wrappers.append(f'theorem exclude_{seed}_excess_{excess} {{N : ℕ}} (ho : Odd N) (hN : N.Perfect)\n'
                            f'    (hx : N.primeFactorsList.length ≤ 2*N.primeFactors.card+{excess}){extra}\n'
                            f'    (hs : {seed} ∣ N) : False := by\n  have hlin := {relation}\n'
                            f'  have hcap : N.primeFactors.card ≤ {w} := by omega\n'
                            f'  have htotal : N.primeFactorsList.length ≤ {B} := by omega\n'
                            f'  have H : Conditions N {B} 0 := ⟨ho,hN,htotal,Nat.zero_le _⟩\n'
                            f'  apply {root} H (by omega) hs {coprime} (by omega) (root_realizes N)')
        children.cache_clear()
        weight.cache_clear()
        external.cache_clear()
    flush()
    if power_groups or root_blocks:
        # Different first prime powers cannot lead to the same exact component.
        # Assign whole groups by source size and join their roots only at the end.
        assignments = [[] for _ in range(lanes)]
        loads = [0] * lanes
        weights = {key: sum(len(block.encode()) for _, _, block in group)
                   for key, group in power_groups.items()}
        for key in sorted(power_groups, key=lambda k: (-weights[k], k)):
            lane = min(range(lanes), key=loads.__getitem__)
            assignments[lane].append(key)
            loads[lane] += weights[key]

        def append_group(group):
            for name, dependencies, block in group:
                if sections and sum(len(item.encode()) for item in sections)+len(block.encode()) > 4*module_bytes:
                    flush()
                sections.append(block)
                current_names.add(name)
                required.update(dependencies)

        for active_lane, keys in enumerate(assignments):
            for key in keys:
                append_group(power_groups[key])
            flush()
        active_lane = 0
        append_group(root_blocks)
        flush()
    imports = '\n'.join(f'public import {prefix}.{part}' for part in sorted(set(lane_tips)))
    output.write_text(module(imports, wrappers, 'OddPerfect.FactorBudget'))
    print(f'{len(indices)} subtree theorems in {len(sizes)} modules, largest {max(sizes):,} bytes', flush=True)
