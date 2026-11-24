"""Emit independently checked exact-component subtrees for a factor-count proof."""

from functools import cache
from math import prod
from pathlib import Path


def emit_partition(trees, factorer, output, chunk_limit=450, module_bytes=90000):
    budget = trees[0].budget
    package = output.stem
    prefix = f'OddPerfect.{package}'
    namespace = f'OddPerfect.FactorBudget.Count{budget}'
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
    (directory/'Primes.lean').write_text(module('public import OddPerfect.ChainCheckpoint\nimport Mathlib.Tactic.Primality', prime_blocks))
    previous = 'Primes'
    indices = {}
    sections = []
    sizes = []

    def flush():
        nonlocal previous, sections
        if sections:
            name = f'Part{len(sizes)+1:02d}'
            src = module(f'public import {prefix}.{previous}', sections)
            (directory/f'{name}.lean').write_text(src)
            sizes.append(len(src.encode()))
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
            witness = t.script(d, blocked, f'tree{name}').rstrip()
            state = f'state{name}'
            geom = prod((p**(e+1)-1)//(p-1) for p, e in path)
            desc = ' * '.join(str(p) if e == 1 else f'{p}^{e}' for p, e in path) or '1'
            head = (f'-- Exact component {desc}.\n@[expose] def {state} : Node := '
                    f'⟨{d}, {geom}, {sum(e for _, e in path)}, {len(path)}⟩')
            deps = '[' + ', '.join(f'state{identifier(t, x)}' for x in earlier) + ']'
            ver = f'replayChunk {deps}' if earlier else 'replayScript'
            args = f'splitPrimes {seed} {avoid} {B} {w} {c} {B+1} {state} tree{name}'
            check = f'private theorem checked{name} : {ver} {args} = true := by\n  decide +kernel'
            theorem = (f'theorem reject{name} {{N m : ℕ}} (H : Conditions N {B} {w}) (hs : {seed} ∣ N)\n'
                       f'    (hav : Nat.Coprime {avoid} N) (hc : 18*N.primeFactors.card ≤ 7*{B}+{c})\n'
                       f'    (h : Realizes {state} N m) : False := ')
            rest = f'splitPrimes prime_proofs {B+1} h tree{name} checked{name}'
            if earlier:
                prior = ' | '.join('rfl' for _ in earlier)
                branches = '\n'.join(f'  · exact reject{identifier(t,x)} H hs hav hc ht' for x in earlier)
                theorem += (f'by\n  apply replayChunk_correct H hs hav hc {deps} ?_ {rest}\n'
                            '  intro t ht m hreal\n  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht\n'
                            f'  rcases ht with {prior}\n' + branches.replace(' hc ht', ' hc hreal'))
            else:
                theorem += f'\n  replayScript_correct H hs hav hc {rest}'
            block = '\n\n'.join([head, witness, check, theorem])
            if sections and sum(len(s.encode()) for s in sections)+len(block.encode()) > module_bytes:
                flush()
            sections.append(block)
        root = f'Count{B}.reject{identifier(t,1)}'
        excluded = [p for p in (3,5,7) if avoid%p == 0]
        extra = ''.join(f' (h{p} : ¬ {p} ∣ N)' for p in excluded)
        coprime = '(Nat.coprime_one_left N)'
        if excluded:
            hs = [f'((by decide : Nat.Prime {p}).coprime_iff_not_dvd.mpr h{p})' for p in excluded]
            coprime = hs[0]
            for part in hs[1:]:
                coprime = f'({coprime}.mul_left {part})'
        bound = '(ochem_rao_count_cases H.odd H.perfect).2 h3' if excluded else 'ochem_rao_prime_factor_count H.odd H.perfect'
        wrappers.append(f'theorem exclude_{seed}_budget_{B} {{N : ℕ}} (H : Conditions N {B} {w}){extra}\n'
                        f'    (hs : {seed} ∣ N) : False := by\n  apply {root} H hs {coprime} ?_ (root_realizes N)\n'
                        f'  have := {bound}\n  have hu : N.primeFactorsList.length ≤ {B} := H.count\n  omega')
        children.cache_clear()
        weight.cache_clear()
        external.cache_clear()
    flush()
    output.write_text(module(f'public import {prefix}.{previous}', wrappers, 'OddPerfect.FactorBudget'))
    print(f'{len(indices)} subtree theorems in {len(sizes)} sequential modules, largest {max(sizes):,} bytes', flush=True)
